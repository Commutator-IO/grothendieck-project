import { useMemo, useState } from 'react';
import { BY_ID } from '../content/catalogue.ts';
import { evidence, useManifest } from '../lib/batches.ts';
import lineageRaw from '../content/lineage.json';
import publicationsRaw from '../content/publications.json';

/**
 * Two figures for the Maps page, both bipartite, both drawn by hand.
 *
 * A force layout would have been one dependency and a different picture on
 * every load; a figure whose whole point is "which folder touches which text"
 * has to put the same folder in the same place each time, so it can be pointed
 * at. Folders sit in one column, in shelfmark order, and whatever they connect
 * to sits in the other. The edges are the content, and the data behind every
 * edge carries its own evidence — hover or focus one to read it.
 */

type LinkKind = 'draft' | 'partial' | 'open' | 'edition';
interface Text {
  id: string;
  title: string;
  year: string;
  url: string;
}
interface Link {
  folder: string;
  text: string;
  kind: LinkKind;
  where: string;
  pages: string;
  note: string;
}
const PUB = publicationsRaw as unknown as { texts: Text[]; links: Link[] };

type PersonKind = 'letter' | 'typescript' | 'named' | 'literature';
interface Person {
  id: number;
  name: string;
  generation: number;
  parent: number | null;
  year: number | null;
  school: string | null;
  thesis: string | null;
  students: number | null;
  descendants: number | null;
}
interface Evidence {
  folder: string;
  person: number;
  kind: PersonKind;
  detail: string;
  where: string;
}
interface ArchiveRole {
  role: string;
  what: string;
  year: string | null;
  cotes: string[];
  source: string;
}
interface ArchivePerson {
  name: string;
  mgp: number | null;
  roles: ArchiveRole[];
}
const LIN = lineageRaw as unknown as {
  source: string;
  root: Person & { advisors: { id: number; name: string }[] };
  people: Person[];
  secondGenerationTotal: number;
  edges: Evidence[];
  archive: { source: string; people: ArchivePerson[] };
};

/**
 * The folders an edition covers come as runs — 134-1 to 134-8 for Pursuing
 * Stacks — and drawn one by one they would fill the column with eight rows
 * saying the same thing. A run is one node; the lines into it still say, in
 * the panel below, which folder of the run each one means.
 */
const RUNS = ['134', '140', '157'];
const RUN: Record<string, { span: string; title: string }> = {
  '134': { span: '134-1–8', title: 'Pursuing Stacks' },
  '140': { span: '140-1–4', title: 'La Longue Marche' },
  '157': { span: '157-1–5', title: 'Les Dérivateurs' },
};
const runOf = (cote: string) => RUNS.find((r) => cote.startsWith(`${r}-`)) ?? cote;

const mgp = (id: number) => `https://www.mathgenealogy.org/id.php?id=${id}`;
const folderHref = (id: string) => `/#${id}/1`;

/** Shelfmark order: 1 < 2 < … < 134-1 < 161-3, not string order. */
function byShelfmark(a: string, b: string) {
  const [a0, a1 = '0'] = a.split('-');
  const [b0, b1 = '0'] = b.split('-');
  return Number(a0) - Number(b0) || Number(a1) - Number(b1);
}

function shortTitle(id: string, max = 34) {
  const t = (BY_ID.get(id)?.title ?? '').replace(/\s*:\s*notes manuscrites.*$/i, '').replace(/\s*:.*$/, '');
  return t.length > max ? `${t.slice(0, max - 1).trimEnd()}…` : t;
}

/** A horizontal S between two columns. */
const curve = (x1: number, y1: number, x2: number, y2: number) => {
  const m = (x1 + x2) / 2;
  return `M${x1},${y1} C${m},${y1} ${m},${y2} ${x2},${y2}`;
};

const ROW = 26;
const TOP = 14;

const LINK_STYLE: Record<LinkKind, { stroke: string; width: number; dash?: string; label: string; help: string }> = {
  draft: {
    stroke: 'var(--color-brand-700)',
    width: 2.6,
    label: 'draft',
    help: 'the folder holds a draft of the published passage',
  },
  partial: {
    stroke: 'var(--color-brand-400)',
    width: 1.8,
    label: 'shared statements',
    help: 'specific statements in both, the rest of the folder not in print',
  },
  open: {
    stroke: 'var(--color-encours-500)',
    width: 1.8,
    dash: '5 3',
    label: 'print announces or leaves open',
    help: 'the folder works out what the published text only states, announces or leaves to the reader',
  },
  edition: {
    stroke: 'var(--color-relu-500)',
    width: 1.8,
    label: 'edited by others',
    help: 'a scholarly edition covers the folder',
  },
};

const PERSON_STYLE: Record<PersonKind, { stroke: string; dash?: string; label: string; help: string }> = {
  letter: { stroke: 'var(--color-relu-500)', label: 'letter', help: 'a letter to or from them is in the folder' },
  typescript: {
    stroke: 'var(--color-encours-500)',
    label: 'their text',
    help: 'a typescript or offprint of theirs is in the folder',
  },
  named: { stroke: 'var(--color-brand-400)', label: 'named by him', help: 'he names them, or a result of theirs, on the leaves' },
  literature: {
    stroke: 'var(--color-ink-400)',
    dash: '4 3',
    label: 'their work settles a finding',
    help: 'a finding below names their published work as what would settle it',
  },
};

function Key<K extends string>({
  kinds,
  style,
}: {
  kinds: K[];
  style: Record<K, { stroke: string; dash?: string; label: string; help: string }>;
}) {
  return (
    <ul className="mt-3 flex flex-wrap items-center gap-x-5 gap-y-1.5 text-[12px] text-ink-500">
      {kinds.map((k) => (
        <li key={k} className="flex items-center gap-1.5" title={style[k].help}>
          <svg width="26" height="8" aria-hidden="true">
            <line x1="1" y1="4" x2="25" y2="4" stroke={style[k].stroke} strokeWidth="2.2" strokeDasharray={style[k].dash} />
          </svg>
          {style[k].label}
        </li>
      ))}
    </ul>
  );
}

/** Folder node: a shelfmark and a short title, linking to the reading view. */
function FolderLabel({
  id,
  x,
  y,
  anchor,
  dim,
  onFocus,
}: {
  id: string;
  x: number;
  y: number;
  anchor: 'start' | 'end';
  dim: boolean;
  onFocus: () => void;
}) {
  return (
    <a href={folderHref(id)} onMouseEnter={onFocus} onFocus={onFocus}>
      <text
        x={x}
        y={y}
        textAnchor={anchor}
        dominantBaseline="middle"
        className="tabular"
        style={{ fontSize: 12, fill: dim ? 'var(--color-ink-300)' : 'var(--color-ink-800)' }}
      >
        {anchor === 'end' ? (
          <>
            <tspan style={{ fill: dim ? 'var(--color-ink-300)' : 'var(--color-ink-500)' }}>{shortTitle(id)}</tspan>
            <tspan dx="6" style={{ fontWeight: 600 }}>
              {id}
            </tspan>
          </>
        ) : (
          <>
            <tspan style={{ fontWeight: 600 }}>{id}</tspan>
            <tspan dx="6" style={{ fill: dim ? 'var(--color-ink-300)' : 'var(--color-ink-500)' }}>
              {shortTitle(id)}
            </tspan>
          </>
        )}
        <title>{`n° ${id} — ${BY_ID.get(id)?.title ?? ''}`}</title>
      </text>
    </a>
  );
}

/* ------------------------------------------------------------------------ */

export function FoldersToPrint() {
  type Sel = { folder: string } | { text: string } | { link: number } | null;
  const [sel, setSel] = useState<Sel>(null);

  const folders = useMemo(() => [...new Set(PUB.links.map((l) => l.folder))].sort(byShelfmark), []);
  const texts = PUB.texts.filter((t) => PUB.links.some((l) => l.text === t.id));
  const rows = Math.max(folders.length, texts.length);
  const H = TOP * 2 + (rows - 1) * ROW;
  const W = 800;
  const XF = 300; // right edge of folder labels
  const XT = 540; // left edge of text labels
  const yF = (i: number) => TOP + i * ((rows - 1) / Math.max(folders.length - 1, 1)) * ROW;
  const yT = (i: number) => TOP + i * ((rows - 1) / Math.max(texts.length - 1, 1)) * ROW;
  const fi = new Map(folders.map((f, i) => [f, i]));
  const ti = new Map(texts.map((t, i) => [t.id, i]));

  const on = (l: Link, i: number) =>
    sel === null ||
    ('folder' in sel && sel.folder === l.folder) ||
    ('text' in sel && sel.text === l.text) ||
    ('link' in sel && sel.link === i);

  // Links sharing a folder and a text are drawn once, as parallel strands
  // offset a little, so a folder with two kinds of link to SGA 3 shows both.
  const strand = new Map<string, number>();
  const offsets = PUB.links.map((l) => {
    const k = `${l.folder}|${l.text}`;
    const n = strand.get(k) ?? 0;
    strand.set(k, n + 1);
    return n;
  });

  const shown: Link[] =
    sel === null
      ? []
      : 'link' in sel
        ? [PUB.links[sel.link]]
        : PUB.links.filter((l) => ('folder' in sel ? l.folder === sel.folder : l.text === sel.text));

  return (
    <section id="folders-and-print" className="mt-12 scroll-mt-16">
      <h2 className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
        Where these folders meet the published texts
      </h2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        Each transcribed folder that shares something concrete with a text already in print — his
        own published writings as the Grothendieck Circle gives them, and the editions others have
        made. A shared subject is not an edge. No folder so far is a draft of a published text as a
        whole; what the lines show is how local the overlaps are, and where the notes go past what
        was printed. These are leads from reading the texts side by side, not a specialist's
        verdict.
      </p>
      <Key kinds={['draft', 'partial', 'open', 'edition'] as LinkKind[]} style={LINK_STYLE} />

      <div className="mt-3 overflow-x-auto" onMouseLeave={() => setSel(null)}>
        <svg
          viewBox={`0 0 ${W} ${H}`}
          className="w-full min-w-[640px]"
          role="img"
          aria-label="Folders on the left, published texts on the right, joined where they share material"
        >
          {PUB.links.map((l, i) => {
            const s = LINK_STYLE[l.kind];
            const d = (offsets[i] - 0.5 * ((strand.get(`${l.folder}|${l.text}`) ?? 1) - 1)) * 4;
            const lit = on(l, i);
            return (
              <path
                key={i}
                d={curve(XF + 8, yF(fi.get(l.folder)!) + d, XT - 8, yT(ti.get(l.text)!) + d)}
                fill="none"
                stroke={s.stroke}
                strokeWidth={lit && sel !== null ? s.width + 1 : s.width}
                strokeDasharray={s.dash}
                strokeLinecap="round"
                opacity={lit ? 1 : 0.12}
                tabIndex={0}
                onMouseEnter={() => setSel({ link: i })}
                onFocus={() => setSel({ link: i })}
                style={{ cursor: 'pointer', outline: 'none' }}
              >
                <title>{`${l.folder} → ${texts[ti.get(l.text)!].title}, ${l.where}`}</title>
              </path>
            );
          })}

          {folders.map((f, i) => (
            <FolderLabel
              key={f}
              id={f}
              x={XF}
              y={yF(i)}
              anchor="end"
              dim={sel !== null && !PUB.links.some((l, k) => l.folder === f && on(l, k))}
              onFocus={() => setSel({ folder: f })}
            />
          ))}

          {texts.map((t, i) => (
            <a key={t.id} href={t.url} target="_blank" rel="noopener noreferrer" onMouseEnter={() => setSel({ text: t.id })} onFocus={() => setSel({ text: t.id })}>
              <text x={XT} y={yT(i)} dominantBaseline="middle" style={{ fontSize: 12.5, fill: 'var(--color-ink-800)', fontWeight: 600 }}>
                {t.title}
                <tspan dx="6" className="tabular" style={{ fontWeight: 400, fill: 'var(--color-ink-400)' }}>
                  {t.year} ↗
                </tspan>
              </text>
            </a>
          ))}
        </svg>
      </div>

      {/* The evidence, under the figure rather than in a floating tooltip —
          the same choice as the mosaic on the archive page. */}
      <div className="mt-2 min-h-[4.5em] text-[12.5px] leading-relaxed text-ink-600">
        {shown.length === 0 ? (
          <p className="text-ink-400">
            Hover a folder, a text or a line for what joins them. A folder opens its reading view; a
            text opens where it is published.
          </p>
        ) : (
          <ul className="space-y-1.5">
            {shown.map((l, i) => (
              <li key={i}>
                <span className="tabular font-semibold text-ink-900">n° {l.folder}</span>
                <span className="text-ink-400"> ({l.pages})</span> →{' '}
                <span className="font-semibold text-ink-800">
                  {PUB.texts.find((t) => t.id === l.text)?.title}, {l.where}
                </span>{' '}
                <span style={{ color: LINK_STYLE[l.kind].stroke }}>· {LINK_STYLE[l.kind].label}</span>
                <br />
                {l.note}
              </li>
            ))}
          </ul>
        )}
      </div>
    </section>
  );
}

/* ------------------------------------------------------------------------ */

export function LineageToFolders() {
  type Sel = { key: string } | { folder: string } | null;
  const [sel, setSel] = useState<Sel>(null);
  const manifest = useManifest();

  // Students in the order of their first degree, each second-generation
  // person directly under the student they descend through; then, under a
  // rule, everyone who has worked on the archives without being in the line —
  // those whose work covers folders first, the rest after.
  const rows = useMemo(() => {
    const gen1 = LIN.people
      .filter((p) => p.generation === 1)
      .sort((a, b) => (a.year ?? 0) - (b.year ?? 0) || a.name.localeCompare(b.name));
    const out: { key: string; kind: 'student' | 'grandstudent' | 'archive'; name: string; year: string; p?: Person; a?: ArchivePerson }[] = [];
    for (const s of gen1) {
      out.push({ key: `m${s.id}`, kind: 'student', name: s.name, year: String(s.year ?? ''), p: s });
      for (const g of LIN.people.filter((p) => p.generation === 2 && p.parent === s.id))
        out.push({ key: `m${g.id}`, kind: 'grandstudent', name: g.name, year: String(g.year ?? ''), p: g });
    }
    const covers = (a: ArchivePerson) => a.roles.some((r) => r.cotes.length > 0);
    const first = (a: ArchivePerson) => Math.min(...a.roles.map((r) => Number.parseInt(r.year ?? '9999', 10) || 9999));
    for (const a of [...LIN.archive.people].sort(
      (x, y) => Number(covers(y)) - Number(covers(x)) || first(x) - first(y) || x.name.localeCompare(y.name),
    ))
      out.push({ key: `a${a.name}`, kind: 'archive', name: a.name, year: '', a });
    return out;
  }, []);

  type Line = { key: string; folder: string; cote: string; kind: PersonKind | 'archive'; detail: string; source?: string };
  const lines = useMemo(() => {
    const out: Line[] = LIN.edges.map((e) => ({
      key: `m${e.person}`,
      folder: runOf(e.folder),
      cote: e.folder,
      kind: e.kind,
      detail: e.detail,
    }));
    for (const a of LIN.archive.people)
      for (const r of a.roles) {
        // One line per person and run, whatever the number of folders in it.
        for (const run of new Set(r.cotes.map(runOf)))
          out.push({
            key: `a${a.name}`,
            folder: run,
            cote: r.cotes.filter((c) => runOf(c) === run).join(', '),
            kind: 'archive',
            detail: `${r.role}${r.year ? `, ${r.year}` : ''}: ${r.what}`,
            source: r.source,
          });
      }
    return out;
  }, []);

  const folders = useMemo(() => [...new Set(lines.map((l) => l.folder))].sort(byShelfmark), [lines]);
  const firstCote = (f: string) => (RUNS.includes(f) ? `${f}-1` : f);
  const transcribed = (f: string) =>
    manifest !== null && (RUNS.includes(f) ? [1, 2, 3, 4, 5, 6, 7, 8].some((k) => evidence(manifest, `${f}-${k}`, 1).transcribed) : evidence(manifest, f, 1).transcribed);

  const GAP = 2; // blank rows between the line and the others, one of them the heading
  const firstArchive = rows.findIndex((r) => r.kind === 'archive');
  const slot = (i: number) => (i >= firstArchive ? i + GAP : i);
  const n = Math.max(rows.length + GAP, folders.length);
  const STEP = 21;
  const H = TOP * 2 + (n - 1) * STEP;
  const W = 800;
  const XR = 58; // Grothendieck
  const XP = 130; // students' dot
  const XE = 372; // where a person's lines leave
  const XF = 540; // folders
  const yP = (i: number) => TOP + slot(i) * STEP;
  const yF = (i: number) => TOP + i * ((H - 2 * TOP) / Math.max(folders.length - 1, 1));
  const ri = new Map(rows.map((r, i) => [r.key, i]));
  const fi = new Map(folders.map((f, i) => [f, i]));
  const lastStudent = firstArchive - 1;
  const yRoot = (TOP + yP(lastStudent)) / 2;

  const on = (l: Line) => sel === null || ('key' in sel ? sel.key === l.key : sel.folder === l.folder);
  const style = (k: Line['kind']) =>
    k === 'archive'
      ? { stroke: 'var(--color-relu-600)', dash: undefined as string | undefined }
      : PERSON_STYLE[k];
  const row = sel && 'key' in sel ? rows[ri.get(sel.key)!] : null;
  const shown = sel === null ? [] : lines.filter(on);

  return (
    <section id="lineage" className="mt-12 scroll-mt-16">
      <h2 className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
        His students, the people who have worked on the archives, and the folders they meet
      </h2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        Above the rule, Grothendieck's {LIN.root.students} doctoral students as the Mathematics
        Genealogy Project records them, with those of their own students who turn up in these
        folders — {LIN.root.descendants} descendants in all, most of whom do not. Below it, the
        people who have worked on the archives without being in that line: who kept the fonds,
        catalogued it, edited or transcribed what came out of it. A line to a folder means
        something on the leaves or in a finding below — a letter, a text of theirs, his naming
        them, their published work as what would settle a finding — or, for the second group, a
        documented piece of work covering that folder. It says nothing about influence, and
        nothing about who has been or will be asked to read anything.
      </p>
      <Key
        kinds={['letter', 'typescript', 'named', 'literature', 'archive'] as (PersonKind | 'archive')[]}
        style={{
          ...PERSON_STYLE,
          archive: {
            stroke: 'var(--color-relu-600)',
            label: 'worked on it',
            help: 'an edition, transcription or translation of theirs covers the folder',
          },
        }}
      />

      <div className="mt-3 overflow-x-auto" onMouseLeave={() => setSel(null)}>
        <svg viewBox={`0 0 ${W} ${H}`} className="w-full min-w-[640px]" role="img" aria-label="Grothendieck, his students, the people who have worked on the archives, and the folders each meets">
          {rows.map((r, i) => {
            if (r.kind === 'archive') return null;
            const p = r.p!;
            const fromY = p.generation === 1 ? yRoot : yP(ri.get(`m${p.parent}`)!);
            return (
              <path
                key={`t${r.key}`}
                d={p.generation === 1 ? curve(XR + 8, fromY, XP - 5, yP(i)) : `M${XP},${fromY} V${yP(i)} H${XP + 10}`}
                fill="none"
                stroke="var(--color-ink-200)"
                strokeWidth="1.2"
              />
            );
          })}

          {/* The rule, and the second group's heading. */}
          <line x1={XR - 40} x2={XE} y1={yP(firstArchive) - STEP * 1.5} y2={yP(firstArchive) - STEP * 1.5} stroke="var(--color-ink-200)" />
          <text x={XR - 40} y={yP(firstArchive) - STEP * 0.7} style={{ fontSize: 10.5, fontWeight: 700, letterSpacing: '0.08em', fill: 'var(--color-ink-400)' }}>
            WORKED ON THE ARCHIVES
          </text>

          {lines.map((l, i) => {
            const s = style(l.kind);
            return (
              <path
                key={i}
                d={curve(XE, yP(ri.get(l.key)!), XF - 8, yF(fi.get(l.folder)!))}
                fill="none"
                stroke={s.stroke}
                strokeWidth={on(l) && sel !== null ? 2.4 : 1.4}
                strokeDasharray={s.dash}
                opacity={on(l) ? 0.95 : 0.1}
              />
            );
          })}

          <a href={mgp(LIN.root.id)} target="_blank" rel="noopener noreferrer">
            <circle cx={XR} cy={yRoot} r="6" fill="var(--color-ink-900)" />
            <text x={XR} y={yRoot - 14} textAnchor="middle" style={{ fontSize: 12.5, fontWeight: 600, fill: 'var(--color-ink-900)' }}>
              Grothendieck
            </text>
            <text x={XR} y={yRoot + 20} textAnchor="middle" className="tabular" style={{ fontSize: 10.5, fill: 'var(--color-ink-400)' }}>
              Nancy {LIN.root.year}
            </text>
            <title>{`${LIN.root.name} — thesis ${LIN.root.year}, advisors ${LIN.root.advisors.map((a) => a.name).join(' and ')} (MGP)`}</title>
          </a>

          {rows.map((r, i) => {
            const has = lines.some((l) => l.key === r.key);
            const lit = sel === null || ('key' in sel ? sel.key === r.key : lines.some((l) => l.key === r.key && on(l)));
            const x = r.kind === 'grandstudent' ? XP + 14 : XP;
            const href =
              r.kind === 'archive'
                ? r.a!.mgp
                  ? mgp(r.a!.mgp)
                  : r.a!.roles[0].source
                : mgp(r.p!.id);
            const dot = !has ? 'var(--color-ink-300)' : r.kind === 'archive' ? 'var(--color-relu-600)' : 'var(--color-brand-600)';
            return (
              <a key={r.key} href={href} target="_blank" rel="noopener noreferrer" onMouseEnter={() => setSel({ key: r.key })} onFocus={() => setSel({ key: r.key })}>
                <circle cx={x} cy={yP(i)} r={r.kind === 'grandstudent' ? 3 : 4} fill={dot} />
                <text
                  x={x + 9}
                  y={yP(i)}
                  dominantBaseline="middle"
                  style={{
                    fontSize: r.kind === 'grandstudent' ? 11 : 12,
                    fontStyle: r.kind === 'grandstudent' ? 'italic' : 'normal',
                    fill: !lit ? 'var(--color-ink-300)' : has ? 'var(--color-ink-800)' : 'var(--color-ink-400)',
                  }}
                >
                  {r.name}
                  <tspan dx="5" className="tabular" style={{ fontSize: 10.5, fill: 'var(--color-ink-400)' }}>
                    {r.year}
                  </tspan>
                </text>
              </a>
            );
          })}

          {folders.map((f, i) => {
            const dim = sel !== null && !lines.some((l) => l.folder === f && on(l));
            const here = transcribed(f);
            return (
              <a key={f} href={folderHref(firstCote(f))} onMouseEnter={() => setSel({ folder: f })} onFocus={() => setSel({ folder: f })}>
                <text x={XF} y={yF(i)} dominantBaseline="middle" className="tabular" style={{ fontSize: 12, fill: dim ? 'var(--color-ink-300)' : 'var(--color-ink-800)' }}>
                  <tspan style={{ fontWeight: 600, fill: dim ? 'var(--color-ink-300)' : here ? 'var(--color-ink-800)' : 'var(--color-ink-400)' }}>
                    {RUN[f]?.span ?? f}
                  </tspan>
                  <tspan dx="6" style={{ fill: dim || !here ? 'var(--color-ink-300)' : 'var(--color-ink-500)' }}>
                    {RUN[f]?.title ?? shortTitle(firstCote(f))}
                  </tspan>
                  <title>{`n° ${RUN[f]?.span ?? f} — ${RUN[f]?.title ?? BY_ID.get(firstCote(f))?.title ?? ''}${here ? '' : ' (not transcribed here yet)'}`}</title>
                </text>
              </a>
            );
          })}
        </svg>
      </div>

      <div className="mt-2 min-h-[4.5em] text-[12.5px] leading-relaxed text-ink-600">
        {sel === null ? (
          <p className="text-ink-400">
            Hover a name for what ties them to the folders, or a folder for everyone it meets.
            Students' names open their page on the Mathematics Genealogy Project; the others open
            it where they have one, or the source of their work. Grey names have no line to a
            folder; grey folders are not transcribed here yet.
          </p>
        ) : (
          <>
            {row?.p && (
              <p>
                <span className="font-semibold text-ink-900">{row.p.name}</span>
                {row.p.year && <span className="tabular"> · {row.p.year}</span>}
                {row.p.school && <span> · {row.p.school}</span>}
                {row.p.thesis && <span className="italic"> · {row.p.thesis}</span>}
                {row.p.students ? (
                  <span className="tabular text-ink-400">
                    {' '}
                    · {row.p.students} {row.p.students === 1 ? 'student' : 'students'} of their own on MGP
                  </span>
                ) : null}
              </p>
            )}
            {row?.a && (
              <>
                <p className="font-semibold text-ink-900">{row.a.name}</p>
                <ul className="mt-0.5 space-y-0.5">
                  {row.a.roles.map((r, i) => (
                    <li key={i}>
                      <span style={{ color: 'var(--color-relu-700)' }}>{r.role}</span>
                      {r.year && <span className="tabular"> · {r.year}</span>} — {r.what}
                      {r.cotes.length > 0 && <span className="tabular text-ink-400"> (n° {r.cotes.join(', ')})</span>}{' '}
                      <a href={r.source} target="_blank" rel="noopener noreferrer" className="text-brand-700 underline underline-offset-2">
                        source ↗
                      </a>
                    </li>
                  ))}
                </ul>
              </>
            )}
            {!row?.a && shown.length > 0 && (
              <ul className="mt-1 space-y-0.5">
                {shown.map((l, i) => (
                  <li key={i}>
                    <span className="tabular font-semibold text-ink-900">n° {l.cote}</span>
                    {!row && <> · {rows[ri.get(l.key)!].name}</>} ·{' '}
                    <span style={{ color: style(l.kind).stroke }}>{l.kind === 'archive' ? 'worked on it' : PERSON_STYLE[l.kind].label}</span> —{' '}
                    {l.detail}
                  </li>
                ))}
              </ul>
            )}
          </>
        )}
      </div>

      <p className="mt-3 max-w-[44em] text-[12px] leading-relaxed text-ink-400">
        Lineage from the Mathematics Genealogy Project, read {LIN.source.slice(-10)}, every name
        linked to the page it was read from; {LIN.secondGenerationTotal} second-generation students
        were read, and only those with a line here are drawn. {LIN.archive.source} The lines come
        from the transcriptions, the findings and those sources, each traceable to a line of a file
        in the repository or to a cited page.
      </p>
    </section>
  );
}
