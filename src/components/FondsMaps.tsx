import { useMemo, useState } from 'react';
import citationRaw from '../content/citation-map.json';
import mathRaw from '../content/math-map.json';

/**
 * Two maps of the fonds, drawn like the people network: positions and
 * communities computed once by `npm run fonds-maps`, the evidence under the
 * figure on hover. Both are knowingly incomplete — the first covers only the
 * folders with a modernised reading, the second only references written in the
 * usual forms — and say so above the figure.
 */

/* The six categorical slots of the people network, checked there. */
const SLOTS = ['#38539d', '#c9900c', '#128557', '#d55181', '#4a3aa7', '#eb6834'];
const OTHER = 'var(--color-ink-400)';
const colour = (c: number) => SLOTS[c] ?? OTHER;

/* One hue, light to dark, for the dating: checked as an ordinal ramp. */
const DATING = [
  { upTo: 1966, label: 'to 1966', fill: '#97afe1' },
  { upTo: 1968, label: '1967–68', fill: '#6b8ad0' },
  { upTo: 1970, label: '1969–70', fill: '#4a6bbd' },
  { upTo: 1972, label: '1971–72', fill: '#2e447f' },
  { upTo: 9999, label: '1973 on', fill: '#223154' },
];
const dating = (y: number | null) => (y === null ? OTHER : DATING.find((d) => y <= d.upTo)!.fill);

interface Drawn {
  key: string;
  x: number;
  y: number;
  r: number;
  fill: string;
  label: string;
  bold?: boolean;
  always?: boolean;
  square?: boolean;
}

/** The shared drawing: links, then nodes, labels haloed so lines never cut them. */
function Canvas({
  width,
  height,
  nodes,
  links,
  sel,
  onSel,
  label,
}: {
  width: number;
  height: number;
  nodes: Drawn[];
  links: { s: number; t: number; width: number; stroke: string }[];
  sel: number | null;
  onSel: (i: number | null) => void;
  label: string;
}) {
  const nb = useMemo(() => {
    const m = nodes.map(() => new Set<number>());
    for (const l of links) {
      m[l.s].add(l.t);
      m[l.t].add(l.s);
    }
    return m;
  }, [nodes, links]);
  const lit = (i: number) => sel === null || sel === i || nb[sel].has(i);
  return (
    <div className="mt-3 overflow-x-auto" onMouseLeave={() => onSel(null)}>
      <svg
        viewBox={`0 0 ${width} ${height}`}
        className="w-full min-w-[640px] rounded-[var(--radius-card)] border border-ink-200 bg-white"
        role="img"
        aria-label={label}
      >
        {links.map((l, i) => {
          const on = sel === null || l.s === sel || l.t === sel;
          return (
            <line
              key={i}
              x1={nodes[l.s].x}
              y1={nodes[l.s].y}
              x2={nodes[l.t].x}
              y2={nodes[l.t].y}
              stroke={l.stroke}
              strokeWidth={l.width}
              opacity={on ? (sel === null ? 0.3 : 0.8) : 0.05}
            />
          );
        })}
        {nodes.map((n, i) => (
          <g
            key={n.key}
            tabIndex={0}
            onMouseEnter={() => onSel(i)}
            onFocus={() => onSel(i)}
            style={{ cursor: 'pointer', outline: 'none' }}
            opacity={lit(i) ? 1 : 0.2}
          >
            <circle cx={n.x} cy={n.y} r={n.r + 6} fill="#fff" fillOpacity={0} />
            {n.square ? (
              <rect x={n.x - n.r} y={n.y - n.r} width={2 * n.r} height={2 * n.r} rx={3} fill={n.fill} stroke="#fff" strokeWidth="2" />
            ) : (
              <circle cx={n.x} cy={n.y} r={n.r} fill={n.fill} stroke="#fff" strokeWidth="2" />
            )}
            {(n.always || sel === i || (sel !== null && nb[sel].has(i))) && (
              <text
                x={n.x < 130 ? n.x - n.r : n.x > width - 130 ? n.x + n.r : n.x}
                y={n.y - n.r - 5}
                textAnchor={n.x < 130 ? 'start' : n.x > width - 130 ? 'end' : 'middle'}
                style={{
                  fontSize: n.bold ? 13.5 : 11.5,
                  fontWeight: n.bold ? 600 : 400,
                  fill: 'var(--color-ink-800)',
                  paintOrder: 'stroke',
                  stroke: '#fff',
                  strokeWidth: 4,
                  strokeLinejoin: 'round',
                }}
              >
                {n.label}
              </text>
            )}
            <title>{n.label}</title>
          </g>
        ))}
      </svg>
    </div>
  );
}

function Swatches({ items }: { items: { label: string; fill: string }[] }) {
  return (
    <ul className="mt-3 flex flex-wrap items-center gap-x-5 gap-y-1.5 text-[12px] text-ink-500">
      {items.map((it) => (
        <li key={it.label} className="flex items-center gap-1.5">
          <span aria-hidden="true" className="inline-block h-2.5 w-2.5 rounded-full" style={{ background: it.fill }} />
          {it.label}
        </li>
      ))}
    </ul>
  );
}

/* ------------------------------------------------------------------------ */

interface Term {
  term: string;
  short: string;
  x: number;
  y: number;
  cluster: number;
  folders: { id: string; title: string; keywords: string[]; year: number | null }[];
  year: number | null;
  dated: number;
}
const MATH = mathRaw as unknown as {
  built: string;
  width: number;
  height: number;
  coverage: { folders: number; keywords: number; mapped: number };
  nodes: Term[];
  links: { s: number; t: number; w: number; folders: string[] }[];
};

export function MathMap() {
  const [sel, setSel] = useState<number | null>(null);
  const [mode, setMode] = useState<'community' | 'dating'>('community');
  const { nodes, links, coverage } = MATH;
  const maxW = Math.max(...links.map((l) => l.w));
  const maxF = Math.max(...nodes.map((n) => n.folders.length));

  // A community is named by its two largest subjects.
  const names = useMemo(() => {
    const out = new Map<number, string>();
    for (const c of [...new Set(nodes.map((n) => n.cluster))].sort((a, b) => a - b))
      out.set(
        c,
        nodes
          .filter((n) => n.cluster === c)
          .sort((a, b) => b.folders.length - a.folders.length)
          .slice(0, 2)
          .map((n) => n.term.split(/,| and /)[0])
          .join(' · '),
      );
    return out;
  }, [nodes]);

  const drawn: Drawn[] = nodes.map((n) => ({
    key: n.term,
    x: n.x,
    y: n.y,
    r: 5 + 13 * Math.sqrt(n.folders.length / maxF),
    fill: mode === 'community' ? colour(n.cluster) : dating(n.year),
    label: n.short,
    bold: n.folders.length >= 15,
    always: true,
  }));
  const lines = links.map((l) => ({
    s: l.s,
    t: l.t,
    width: 0.5 + (3 * l.w) / maxW,
    stroke: mode === 'community' && nodes[l.s].cluster === nodes[l.t].cluster ? colour(nodes[l.s].cluster) : 'var(--color-ink-300)',
  }));
  const n = sel === null ? null : nodes[sel];

  return (
    <section id="math-map" className="mt-12 scroll-mt-16">
      <h2 className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">A map of the mathematics in the fonds</h2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        The subjects of the {coverage.folders} folders that have a modernised reading, drawn close to those they share
        folders with more often than their sizes alone would give; a larger dot, more folders. Each reading closes on a list of modern keywords, and each keyword is
        filed under the coarse subjects of a vocabulary kept with the site — {coverage.mapped} of {coverage.keywords}{' '}
        keywords find a subject so far, and the rest are listed with the data. Folders without a modernised reading are
        not on this map yet.
      </p>

      <div role="group" aria-label="Colour" className="mt-3 flex items-center gap-1 text-[12px]">
        <span className="mr-1 text-ink-400">Colour</span>
        {(
          [
            ['community', 'by community'],
            ['dating', "by the inventory's dating"],
          ] as const
        ).map(([k, l]) => (
          <button
            key={k}
            type="button"
            aria-pressed={mode === k}
            onClick={() => setMode(k)}
            className={`rounded-full px-2.5 py-1 transition-colors ${mode === k ? 'bg-ink-800 text-white' : 'bg-ink-100 text-ink-600 hover:bg-ink-200'}`}
          >
            {l}
          </button>
        ))}
      </div>
      {mode === 'community' ? (
        <Swatches items={[...names].map(([c, name]) => ({ label: name, fill: colour(c) }))} />
      ) : (
        <>
          <Swatches items={[...DATING.map((d) => ({ label: d.label, fill: d.fill })), { label: 'undated', fill: OTHER }]} />
          <p className="mt-1.5 max-w-[44em] text-[12px] leading-relaxed text-ink-400">
            The mean, over a subject's folders, of the midpoint of each folder's dating in the inventory — which nearly
            always infers it from a verso or a letterhead, and brackets it to say so. A shade here is a tendency, not a
            date.
          </p>
        </>
      )}

      <Canvas
        width={MATH.width}
        height={MATH.height}
        nodes={drawn}
        links={lines}
        sel={sel}
        onSel={setSel}
        label="Subjects of the folders, linked when a folder carries both"
      />

      <div className="mt-2 min-h-[4.5em] text-[12.5px] leading-relaxed text-ink-600">
        {n ? (
          <>
            <p>
              <span className="font-semibold text-ink-900">{n.term}</span>
              <span className="tabular text-ink-400">
                {' '}
                · {n.folders.length} {n.folders.length === 1 ? 'folder' : 'folders'}
                {n.year !== null && ` · mean dating ${n.year} (${n.dated} dated)`}
              </span>
            </p>
            <ul className="mt-1 space-y-0.5">
              {n.folders.map((f) => (
                <li key={f.id}>
                  <a href={`/#${f.id}/1`} className="tabular font-semibold text-ink-900 hover:text-brand-700">
                    n° {f.id}
                  </a>{' '}
                  <span className="text-ink-500">{f.title}</span> — <span className="italic">{f.keywords.join(', ')}</span>
                </li>
              ))}
            </ul>
          </>
        ) : (
          <p className="text-ink-400">Hover or focus a subject for its folders and the keywords that put them there.</p>
        )}
      </div>

      <p className="mt-3 max-w-[44em] text-[12px] leading-relaxed text-ink-400">
        Built on {MATH.built}. Subjects and their patterns are in src/content/math-vocabulary.json; `npm run fonds-maps`
        rebuilds the map. Co-occurrence is counted fractionally, the communities are found by modularity and the
        positions by a force layout, as for the people network.
      </p>
    </section>
  );
}

/* ------------------------------------------------------------------------ */

interface CNode {
  id: string;
  kind: 'folder' | 'text';
  x: number;
  y: number;
  cluster: number;
  title?: string;
  cites?: Record<string, string[]>;
  n: number;
  by?: string[];
}
const CIT = citationRaw as unknown as {
  built: string;
  width: number;
  height: number;
  nodes: CNode[];
  links: { s: number; t: number; n: number }[];
};

export function CitationMap() {
  const [sel, setSel] = useState<number | null>(null);
  const { nodes, links } = CIT;
  const maxN = Math.max(...links.map((l) => l.n));
  const maxT = Math.max(...nodes.filter((x) => x.kind === 'text').map((x) => x.n));
  const maxF = Math.max(...nodes.filter((x) => x.kind === 'folder').map((x) => x.n));
  const folders = nodes.filter((x) => x.kind === 'folder').length;
  const texts = nodes.length - folders;

  const drawn: Drawn[] = nodes.map((n) => ({
    key: `${n.kind}:${n.id}`,
    x: n.x,
    y: n.y,
    r: n.kind === 'text' ? 7 + 9 * Math.sqrt(n.n / maxT) : 4 + 5 * Math.sqrt(n.n / maxF),
    fill: colour(n.cluster),
    label: n.kind === 'text' ? n.id : `n° ${n.id}`,
    bold: n.kind === 'text',
    always: n.kind === 'text' || n.n >= 6,
    square: n.kind === 'text',
  }));
  const lines = links.map((l) => ({
    s: l.s,
    t: l.t,
    width: 0.6 + (2.6 * Math.log2(1 + l.n)) / Math.log2(1 + maxN),
    stroke: nodes[l.s].cluster === nodes[l.t].cluster ? colour(nodes[l.s].cluster) : 'var(--color-ink-300)',
  }));
  const n = sel === null ? null : nodes[sel];

  return (
    <section id="citation-map" className="mt-12 scroll-mt-16">
      <h2 className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">Folders linked by what they cite</h2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        {folders} folders (dots) and the {texts} volumes of his published work they refer to (squares) — SGA, EGA, FGA —
        joined by how often the folder cites the volume, so that folders working on the same part of his corpus fall
        together. Read from the leaves alone: the transcriber's notes and the header comments are cut out first, so what
        counts is what is on the page, his text and the letters to him in the folder. Only references in the usual
        forms are caught — « SGA 4 VIII », « SGA A », « EGA IV 16.9 », « TDTE » — and a volume given only by a year, or an
        exposé without its seminar, is not. Folder 162-1, a register of papers lent, is left out.
      </p>

      <Canvas
        width={CIT.width}
        height={CIT.height}
        nodes={drawn}
        links={lines}
        sel={sel}
        onSel={setSel}
        label="Folders and the volumes of SGA, EGA and FGA they cite"
      />

      <div className="mt-2 min-h-[4.5em] text-[12.5px] leading-relaxed text-ink-600">
        {n?.kind === 'folder' ? (
          <>
            <p>
              <a href={`/#${n.id}/1`} className="font-semibold text-ink-900 hover:text-brand-700">
                n° {n.id}
              </a>{' '}
              <span className="text-ink-500">{n.title}</span>
              <span className="tabular text-ink-400"> · {n.n} references</span>
            </p>
            <ul className="mt-1 space-y-0.5">
              {Object.entries(n.cites ?? {}).map(([u, refs]) => (
                <li key={u}>
                  <span className="font-semibold text-ink-800">{u}</span> — {refs.join(', ')}
                </li>
              ))}
            </ul>
          </>
        ) : n?.kind === 'text' ? (
          <p>
            <span className="font-semibold text-ink-900">{n.id}</span>
            <span className="tabular text-ink-400"> · cited {n.n} times, by </span>
            {(n.by ?? []).map((f, i) => (
              <span key={f}>
                {i > 0 && ', '}
                <a href={`/#${f}/1`} className="tabular text-ink-800 hover:text-brand-700">
                  n° {f}
                </a>
              </span>
            ))}
          </p>
        ) : (
          <p className="text-ink-400">Hover or focus a volume for the folders citing it, or a folder for its references.</p>
        )}
      </div>

      <p className="mt-3 max-w-[44em] text-[12px] leading-relaxed text-ink-400">
        Built on {CIT.built} from every transcribed batch; `npm run fonds-maps` rebuilds it. Colours are communities found
        by modularity over folders and volumes together.
      </p>
    </section>
  );
}
