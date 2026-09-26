#!/usr/bin/env node
/**
 * Holds the TEI export to the schema it names, and fails the deploy if it
 * does not.
 *
 *   npm run tei:validate          after npm run tei
 *
 * `npm run tei` used to check well-formedness with xmllint, where xmllint was
 * installed, and nothing else ran on the deploy. Well-formed says the bytes
 * parse; it does not say the file is TEI, and still less *which* TEI. The last
 * validation against tei_all was run by hand, on 2026-09-05, over 53 files. So
 * this script asks three questions, on every file, on every deploy:
 *
 * 1. **Is it TEI?** Every exported file, and the ODD itself, against the
 *    Consortium's own `tei_all.rng` for unmodified TEI P5, with jing.
 *
 * 2. **Is it this customisation's TEI?** Every exported file against the
 *    RELAX NG derived here from `tei/grothendieck.odd` — the schema each file
 *    names in its `<?xml-model?>`, published beside the ODD under /tei/. The
 *    derivation is the Consortium's own: `odd2odd.xsl` then `odd2relax.xsl`
 *    from TEI Stylesheets, on Saxon, against the `p5subset.xml` the ODD's
 *    `schemaSpec/@source` names.
 *
 * 3. **Does the ODD still describe the export?** Read directly off the ODD,
 *    in both directions, as hopper-project's tei-validate does: an element
 *    used and not declared fails; an element declared and used nowhere fails
 *    too, because a subset that can only grow is the full schema again,
 *    reached politely; a value outside a closed list fails. The RELAX NG
 *    already enforces the first and third; they are restated here because
 *    the message says which file, which value and what the list is, where
 *    jing says only that the attribute is wrong. The second the RELAX NG
 *    cannot say at all.
 *
 * Beyond the grammar, two things no schema checks across a file: every
 * `#pointer` the export writes (`resp="#pass"`, `who="#rev-…"`) lands on an
 * `xml:id` in the same file, and every file names the schema and the ODD it
 * is to be read against.
 *
 * ## Pins
 *
 * Everything fetched is fetched at a pinned version from a URL that does not
 * move — the Vault for TEI P5, a tagged release for the Stylesheets, Maven
 * Central for the jars — and checked against a SHA-256 recorded below, cached
 * or not, because a cache is a place a file can be replaced. A schema that
 * changed under the corpus would be a check that could not fail the same way
 * twice. Java is the one thing assumed on the machine; the deploy runner has
 * it, and so does `npm run article-tei`.
 */
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { copyFileSync, existsSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const root = resolve(import.meta.dirname, '..');
const cacheDir = resolve(root, 'node_modules/.cache/tei');
const oddPath = resolve(root, 'tei/grothendieck.odd');
const publicTei = resolve(root, 'public/tei');
const exportDir = resolve(root, 'public/transcripts');

/** Where the export says the schema and the ODD are. scripts/tei.mjs writes the same two URLs. */
export const RNG_URL = 'https://grothendieck.commutator.io/tei/grothendieck.rng';
export const ODD_URL = 'https://grothendieck.commutator.io/tei/grothendieck.odd';

const TEI_VERSION = '4.12.0';
const XSL_VERSION = '7.61.0';
const PINS = {
  'tei_all.rng': {
    url: `https://www.tei-c.org/Vault/P5/${TEI_VERSION}/xml/tei/custom/schema/relaxng/tei_all.rng`,
    sha256: 'b0f115095ead2ccc6933aa3365c6f4a82cba3b2ec7eee7f76bb616d7a63b7e48',
  },
  'p5subset.xml': {
    url: `https://www.tei-c.org/Vault/P5/${TEI_VERSION}/xml/tei/odd/p5subset.xml`,
    sha256: '5b89720edc6f3821ab3d0aa242aa5dc922bfbafabfb103d2de9d211001c33e26',
  },
  'tei-xsl.zip': {
    url: `https://github.com/TEIC/Stylesheets/releases/download/v${XSL_VERSION}/tei-xsl-${XSL_VERSION}.zip`,
    sha256: '1a6cd1043af5adb3c5a8c1b2ec0b6abb7d0f241cd8725e233d691b3ca2f312bf',
  },
  'jing.jar': {
    url: 'https://repo1.maven.org/maven2/org/relaxng/jing/20220510/jing-20220510.jar',
    sha256: 'a60eb8a56d523bce08d07b08229dde9bab1f6b07b4b9eaa853c6fe8490a76d8c',
  },
  'saxon.jar': {
    url: 'https://repo1.maven.org/maven2/net/sf/saxon/Saxon-HE/12.5/Saxon-HE-12.5.jar',
    sha256: '98c3a91e6e5aaf9b3e2b37601e04b214a6e67098493cdd8232fcb705fddcb674',
  },
  'xmlresolver.jar': {
    url: 'https://repo1.maven.org/maven2/org/xmlresolver/xmlresolver/5.2.2/xmlresolver-5.2.2.jar',
    sha256: 'efc92bd7ed32b3e57095e0b3e872051ccfbbdcc980831ef33e89e38161a85222',
  },
};

const digest = (buf) => createHash('sha256').update(buf).digest('hex');
const rel = (p) => p.slice(root.length + 1);

/** A pinned file: from the cache when its digest matches, from the net otherwise. */
function pinned(name) {
  const { url, sha256 } = PINS[name];
  const path = resolve(cacheDir, name);
  if (existsSync(path)) {
    if (digest(readFileSync(path)) === sha256) return path;
    process.stdout.write(`tei: cached ${name} does not match its digest, refetching\n`);
  }
  mkdirSync(cacheDir, { recursive: true });
  process.stdout.write(`tei: fetching ${name}\n`);
  const body = execFileSync('curl', ['-fsSL', '--proto', '=https', '--tlsv1.2', url], {
    maxBuffer: 64 * 1024 * 1024,
  });
  const got = digest(body);
  if (got !== sha256) {
    throw new Error(
      `tei: ${name} digest mismatch\n  expected ${sha256}\n  got      ${got}\n  from ${url}\n` +
        'Either the pinned copy changed, which it should not, or the download was tampered with.',
    );
  }
  writeFileSync(path, body);
  return path;
}

const java = (args) =>
  execFileSync('java', args, { stdio: ['ignore', 'pipe', 'pipe'], encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 });

/* ------------------------------------------------------ the derivation */

/**
 * The RELAX NG for the customisation, derived from the ODD.
 *
 * The ODD names the Vault's p5subset.xml as its source, which is right for
 * anyone opening it in Roma; here the same file is substituted from the cache,
 * after its digest is checked, so that the derivation needs no network once
 * the pins are cached. The result is cached on the digest of everything it
 * depends on, since it takes Saxon a dozen seconds and changes only when the
 * ODD or a pin does.
 */
function derive() {
  const odd = readFileSync(oddPath, 'utf8');
  const source = PINS['p5subset.xml'].url;
  if (!odd.includes(`source="${source}"`)) {
    throw new Error(`tei: tei/grothendieck.odd must name ${source} as its schemaSpec/@source`);
  }
  const key = digest(odd + JSON.stringify(PINS)).slice(0, 16);
  const cached = resolve(cacheDir, `grothendieck-${key}.rng`);
  if (existsSync(cached)) return cached;

  const subset = pinned('p5subset.xml');
  const xslDir = resolve(cacheDir, `tei-xsl-${XSL_VERSION}`);
  if (!existsSync(resolve(xslDir, 'xml/tei/stylesheet/odds/odd2relax.xsl'))) {
    rmSync(xslDir, { recursive: true, force: true });
    execFileSync('unzip', ['-q', pinned('tei-xsl.zip'), '-d', xslDir]);
  }
  const odds = resolve(xslDir, 'xml/tei/stylesheet/odds');
  const cp = `${pinned('saxon.jar')}:${pinned('xmlresolver.jar')}`;
  const local = resolve(cacheDir, 'grothendieck.local.odd');
  const compiled = resolve(cacheDir, 'grothendieck.compiled.odd');
  writeFileSync(local, odd.replace(`source="${source}"`, `source="${pathToFileURL(subset).href}"`));
  process.stdout.write(`tei: deriving the schema from tei/grothendieck.odd (TEI Stylesheets ${XSL_VERSION})\n`);
  java(['-cp', cp, 'net.sf.saxon.Transform', `-s:${local}`, `-xsl:${odds}/odd2odd.xsl`, `-o:${compiled}`]);
  java(['-cp', cp, 'net.sf.saxon.Transform', `-s:${compiled}`, `-xsl:${odds}/odd2relax.xsl`, `-o:${cached}`]);
  return cached;
}

/* -------------------------------------------------------------- jing */

/**
 * Runs jing over a set of files and returns the error lines. jing compiles the
 * schema once per run, so 363 files take seconds; it exits non-zero on any
 * error and prints one line per error on stdout.
 */
function jing(schema, files) {
  try {
    java(['-jar', pinned('jing.jar'), schema, ...files]);
    return [];
  } catch (e) {
    if (e.status == null) throw e;
    return String(e.stdout || e.stderr).split('\n').filter(Boolean);
  }
}

/** The files named in a list of jing error lines, and the lines themselves, shortened. */
function report(label, errors) {
  const byFile = new Map();
  for (const line of errors) {
    const m = /^(.+?):\d+:\d+: /.exec(line);
    const f = m ? m[1] : '?';
    if (!byFile.has(f)) byFile.set(f, []);
    byFile.get(f).push(line.replace(`${root}/`, ''));
  }
  process.stderr.write(`tei: ${byFile.size} file(s) NOT valid against ${label}\n`);
  for (const [, lines] of [...byFile].slice(0, 20)) {
    for (const l of lines.slice(0, 3)) process.stderr.write(`       ${l.slice(0, 300)}\n`);
    if (lines.length > 3) process.stderr.write(`       … ${lines.length - 3} more in this file\n`);
  }
  if (byFile.size > 20) process.stderr.write(`       … and ${byFile.size - 20} more file(s)\n`);
  return byFile.size;
}

/* ------------------------------------------------------------ the ODD */

/** The elements the ODD includes, and its closed value lists keyed `element/@attribute`. */
function declared(odd) {
  const elements = new Set();
  for (const m of odd.matchAll(/<moduleRef\b([^>]*)\/>/g)) {
    const include = /\binclude="([^"]*)"/.exec(m[1]);
    // A bare moduleRef brings in a whole module. The one here is `tei`, the
    // infrastructure, which declares no element the export emits; any other
    // bare one would widen the subset silently, so it is refused.
    if (!include) {
      if (!/\bkey="tei"/.test(m[1])) throw new Error(`tei: bare <moduleRef${m[1]}/> in the ODD — list its elements with @include`);
      continue;
    }
    for (const e of include[1].trim().split(/\s+/)) elements.add(e);
  }
  const closed = new Map();
  for (const el of odd.matchAll(/<elementSpec\b([^>]*)>([\s\S]*?)<\/elementSpec>/g)) {
    const ident = /\bident="([^"]+)"/.exec(el[1])?.[1];
    for (const at of el[2].matchAll(/<attDef\b([^>]*)>([\s\S]*?)<\/attDef>/g)) {
      const name = /\bident="([^"]+)"/.exec(at[1])?.[1];
      const list = /<valList\b[^>]*type="closed"[^>]*>([\s\S]*?)<\/valList>/.exec(at[2]);
      if (!ident || !name || !list) continue;
      closed.set(`${ident}/@${name}`, new Set([...list[1].matchAll(/<valItem\b[^>]*\bident="([^"]+)"/g)].map((v) => v[1])));
    }
  }
  return { elements, closed };
}

/**
 * The start-tags of an exported file. A regular expression is safe here for a
 * reason that is checked, not assumed: scripts/tei.mjs escapes every `<` and
 * `&` it writes in text and attributes, it writes no CDATA and no comments,
 * and jing has parsed every file before this runs.
 */
function usedIn(text) {
  const elements = new Map();
  const values = new Map();
  for (const m of text.matchAll(/<([A-Za-z][\w.]*)((?:\s+[\w:.]+="[^"]*")*)\s*\/?>/g)) {
    elements.set(m[1], (elements.get(m[1]) ?? 0) + 1);
    for (const a of m[2].matchAll(/([\w:.]+)="([^"]*)"/g)) {
      const key = `${m[1]}/@${a[1]}`;
      if (!values.has(key)) values.set(key, new Set());
      values.get(key).add(a[2]);
    }
  }
  return { elements, values };
}

/* ----------------------------------------------------------------- go */

function main() {
  const files = [];
  if (existsSync(exportDir)) {
    for (const d of readdirSync(exportDir, { withFileTypes: true })) {
      if (!d.isDirectory()) continue;
      for (const f of readdirSync(resolve(exportDir, d.name))) {
        if (/^batch-\d+\.fr\.xml$/.test(f)) files.push(resolve(exportDir, d.name, f));
      }
    }
  }
  if (!files.length) {
    process.stderr.write('tei: nothing exported — run npm run tei first\n');
    process.exit(1);
  }

  try {
    execFileSync('java', ['-version'], { stdio: 'ignore' });
  } catch {
    // CI has Java; a contributor without it is told, not silently passed.
    process.stderr.write('tei: java not found — install a JRE to validate the TEI\n');
    process.exit(process.env.CI ? 1 : 0);
  }

  let failed = false;
  const odd = readFileSync(oddPath, 'utf8');

  // 1. TEI P5, unmodified: the ODD and every file.
  const teiAll = jing(pinned('tei_all.rng'), [oddPath, ...files]);
  if (teiAll.length) failed = report(`TEI P5 ${TEI_VERSION} (tei_all)`, teiAll) > 0 || failed;
  else process.stdout.write(`tei: ${files.length} file(s) and the ODD valid against TEI P5 ${TEI_VERSION} (tei_all)\n`);

  // 2. The customisation, as the schema derived from the ODD. Published
  //    beside the ODD, which is where each file's <?xml-model?> points.
  const rng = derive();
  mkdirSync(publicTei, { recursive: true });
  copyFileSync(rng, resolve(publicTei, 'grothendieck.rng'));
  copyFileSync(oddPath, resolve(publicTei, 'grothendieck.odd'));
  const custom = jing(rng, files);
  if (custom.length) failed = report('tei/grothendieck.odd (the derived RELAX NG)', custom) > 0 || failed;
  else process.stdout.write(`tei: ${files.length} file(s) valid against tei/grothendieck.odd (derived RELAX NG, sha256 ${digest(readFileSync(rng)).slice(0, 12)}…)\n`);

  // 3. The ODD against the export, both ways, and what no schema checks.
  const { elements: declaredElements, closed } = declared(odd);
  const seen = new Map();
  const seenValues = new Map();
  const dangling = [];
  const unnamed = [];
  const untyped = [];
  for (const f of files) {
    const text = readFileSync(f, 'utf8');
    const { elements, values } = usedIn(text);
    for (const [el, n] of elements) seen.set(el, (seen.get(el) ?? 0) + n);
    for (const [key, set] of values) {
      if (!seenValues.has(key)) seenValues.set(key, new Map());
      for (const v of set) if (!seenValues.get(key).has(v)) seenValues.get(key).set(v, f);
    }
    const ids = new Set([...text.matchAll(/\sxml:id="([^"]+)"/g)].map((m) => m[1]));
    for (const m of text.matchAll(/\s(?:resp|who)="([^"]+)"/g)) {
      for (const p of m[1].split(/\s+/)) {
        if (!p.startsWith('#') || !ids.has(p.slice(1))) dangling.push(`${rel(f)}: ${p}`);
      }
    }
    if (!text.includes(`<?xml-model href="${RNG_URL}"`) || !text.includes(`url="${ODD_URL}"`)) unnamed.push(rel(f));
    const body = text.slice(text.indexOf('<text>'));
    const bare = (body.match(/<note(?![^>]*\stype=")[\s>]/g) ?? []).length;
    if (bare) untyped.push(`${rel(f)}: ${bare}`);
  }

  const fail = (head, lines, tail) => {
    failed = true;
    process.stderr.write(`tei: ${head}\n${lines.slice(0, 30).map((l) => `       ${l}`).join('\n')}\n`);
    if (lines.length > 30) process.stderr.write(`       … ${lines.length - 30} more\n`);
    if (tail) process.stderr.write(`     ${tail}\n`);
  };

  const undeclared = [...seen.keys()].filter((e) => !declaredElements.has(e)).sort();
  if (undeclared.length) {
    fail('the export uses elements tei/grothendieck.odd does not declare —',
      undeclared.map((e) => `<${e}> (${seen.get(e)}×)`),
      'Either the export should not emit them, or the customisation grows and says why.');
  }
  const unused = [...declaredElements].filter((e) => !seen.has(e)).sort();
  if (unused.length) {
    fail('tei/grothendieck.odd declares elements no file uses —', unused.map((e) => `<${e}>`),
      'A declaration nobody reads is a claim about the corpus that is not true. Remove it.');
  }
  for (const [key, allowed] of closed) {
    for (const [v, where] of seenValues.get(key) ?? []) {
      if (allowed.has(v)) continue;
      fail(`${key}="${v}" is outside the closed list in tei/grothendieck.odd`,
        [`first in ${rel(where)}`, `declared: ${[...allowed].join(', ')}`]);
    }
  }
  if (dangling.length) fail('a pointer lands on no xml:id in its own file —', dangling);
  if (unnamed.length) fail(`files that do not name ${RNG_URL} and ${ODD_URL} —`, unnamed);
  if (untyped.length) fail('notes in the text without @type (editorial or authorial) —', untyped);

  if (!failed) {
    process.stdout.write(
      `     ${declaredElements.size} element(s) declared, all used, none undeclared; ` +
        `${closed.size} closed value list(s) held; every pointer resolves\n`,
    );
  }
  process.exit(failed ? 1 : 0);
}

if (process.argv[1] && resolve(process.argv[1]) === resolve(import.meta.filename)) main();
