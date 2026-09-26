import { useMemo, useState } from 'react';
import evidenceRaw from '../content/people-evidence.json';
import networkRaw from '../content/people-network.json';

/**
 * Who is named together in the same folder — a co-occurrence map in the
 * manner of VOSviewer (as scanR draws its communities), with the layout and
 * the clusters computed once by `npm run people-network`, not in the browser.
 *
 * Every node rests on records in people-evidence.json, each with a file and a
 * line; the panel under the figure prints them. A link says only that two
 * people are named in the same folder, weighted so that a folder naming many
 * people counts for less per pair.
 */

interface Node {
  name: string;
  x: number;
  y: number;
  cluster: number;
  folders: string[];
}
interface Link {
  s: number;
  t: number;
  w: number;
  folders: string[];
}
interface EvidenceRecord {
  folder: string;
  person: string;
  kind: 'letter' | 'typescript' | 'named';
  detail: string;
  where: string;
}
const NET = networkRaw as unknown as { width: number; height: number; built: string; nodes: Node[]; links: Link[] };
const EVIDENCE = (evidenceRaw as unknown as { records: EvidenceRecord[] }).records;

/**
 * Six categorical slots in a fixed order, the largest cluster first; checked
 * with the dataviz validator against white (all checks pass; the amber is
 * under 3:1 against the surface, which the visible labels and the list view
 * relieve). Clusters past the sixth are small and share the neutral.
 */
const SLOTS = ['#38539d', '#c9900c', '#128557', '#d55181', '#4a3aa7', '#eb6834'];
const OTHER = 'var(--color-ink-400)';
const colour = (c: number) => SLOTS[c] ?? OTHER;

const KIND: Record<EvidenceRecord['kind'], string> = {
  letter: 'letter',
  typescript: 'their text',
  named: 'named by him',
};

const byShelfmark = (a: string, b: string) => {
  const [a0, a1 = '0'] = a.split('-');
  const [b0, b1 = '0'] = b.split('-');
  return Number(a0) - Number(b0) || Number(a1) - Number(b1);
};

export function PeopleNetwork() {
  const [sel, setSel] = useState<number | null>(null);
  const { nodes, links, width: W, height: H } = NET;

  const neighbours = useMemo(() => {
    const m = nodes.map(() => new Set<number>());
    for (const l of links) {
      m[l.s].add(l.t);
      m[l.t].add(l.s);
    }
    return m;
  }, [nodes, links]);

  // Clusters named by their two most-recurring people, as a key and a list.
  const clusters = useMemo(() => {
    const out = new Map<number, Node[]>();
    for (const n of nodes) out.set(n.cluster, [...(out.get(n.cluster) ?? []), n]);
    return [...out]
      .sort((a, b) => a[0] - b[0])
      .map(([c, ms]) => ({
        c,
        members: [...ms].sort((a, b) => b.folders.length - a.folders.length || a.name.localeCompare(b.name)),
      }));
  }, [nodes]);
  const surname = (n: string) => n.split(' ').slice(-1)[0];

  const maxW = Math.max(...links.map((l) => l.w));
  const radius = (n: Node) => 4 + 3.2 * Math.sqrt(n.folders.length);
  const lit = (i: number) => sel === null || sel === i || neighbours[sel].has(i);
  const node = sel === null ? null : nodes[sel];
  const records = node
    ? EVIDENCE.filter((r) => r.person === node.name).sort((a, b) => byShelfmark(a.folder, b.folder))
    : [];
  const together = node
    ? links
        .filter((l) => l.s === sel || l.t === sel)
        .map((l) => ({ other: nodes[l.s === sel ? l.t : l.s], folders: l.folders, w: l.w }))
        .sort((a, b) => b.w - a.w)
    : [];

  return (
    <section id="people-network" className="mt-12 scroll-mt-16">
      <h2 className="text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
        Who is named together in the folders
      </h2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        {nodes.length} people, each named in a folder with at least one other, drawn close to those
        they share folders with; a larger dot, more folders. The colours are communities found by
        the layout, not a classification of anyone's work. A person counts here when the folder
        holds a letter to or from them, a text of theirs, or his naming them where the words make
        it an attribution — « th. de Hodge », « d'après Deligne », « lettre à Verdier » — and not an
        object that merely bears a name, « groupe de Galois » or « espace de Hilbert ». Folder
        162-1, a register of papers he lent, is left out.
      </p>

      <ul className="mt-3 flex flex-wrap items-center gap-x-5 gap-y-1.5 text-[12px] text-ink-500">
        {clusters
          .filter(({ c }) => c < SLOTS.length)
          .map(({ c, members }) => (
            <li key={c} className="flex items-center gap-1.5">
              <span aria-hidden="true" className="inline-block h-2.5 w-2.5 rounded-full" style={{ background: colour(c) }} />
              {members
                .slice(0, 2)
                .map((m) => surname(m.name))
                .join(' · ')}
            </li>
          ))}
        {clusters.some(({ c }) => c >= SLOTS.length) && (
          <li className="flex items-center gap-1.5">
            <span aria-hidden="true" className="inline-block h-2.5 w-2.5 rounded-full" style={{ background: OTHER }} />
            smaller groups
          </li>
        )}
      </ul>

      <div className="mt-3 overflow-x-auto" onMouseLeave={() => setSel(null)}>
        <svg
          viewBox={`0 0 ${W} ${H}`}
          className="w-full min-w-[640px] rounded-[var(--radius-card)] border border-ink-200 bg-white"
          role="img"
          aria-label="People named together in the same folders, grouped into communities"
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
                stroke={nodes[l.s].cluster === nodes[l.t].cluster ? colour(nodes[l.s].cluster) : 'var(--color-ink-300)'}
                strokeWidth={0.6 + (2.4 * l.w) / maxW}
                opacity={on ? (sel === null ? 0.35 : 0.8) : 0.06}
              />
            );
          })}
          {nodes.map((n, i) => (
            <g
              key={n.name}
              tabIndex={0}
              onMouseEnter={() => setSel(i)}
              onFocus={() => setSel(i)}
              style={{ cursor: 'pointer', outline: 'none' }}
              opacity={lit(i) ? 1 : 0.2}
            >
              {/* a hit area larger than the mark */}
              <circle cx={n.x} cy={n.y} r={radius(n) + 6} fill="#fff" fillOpacity={0} />
              <circle cx={n.x} cy={n.y} r={radius(n)} fill={colour(n.cluster)} stroke="#fff" strokeWidth="2" />
              {(n.folders.length >= 2 || sel === i || (sel !== null && neighbours[sel].has(i))) && (
                <text
                  x={n.x}
                  y={n.y - radius(n) - 5}
                  textAnchor="middle"
                  style={{
                    fontSize: n.folders.length >= 4 ? 14 : 12,
                    fontWeight: n.folders.length >= 4 ? 600 : 400,
                    fill: 'var(--color-ink-800)',
                    paintOrder: 'stroke',
                    stroke: '#fff',
                    strokeWidth: 4,
                    strokeLinejoin: 'round',
                  }}
                >
                  {surname(n.name)}
                </text>
              )}
              <title>{`${n.name} — ${n.folders.length} ${n.folders.length === 1 ? 'folder' : 'folders'}`}</title>
            </g>
          ))}
        </svg>
      </div>

      <div className="mt-2 min-h-[4.5em] text-[12.5px] leading-relaxed text-ink-600">
        {node ? (
          <>
            <p>
              <span className="font-semibold text-ink-900">{node.name}</span>
              <span className="tabular text-ink-400">
                {' '}
                · {node.folders.length} {node.folders.length === 1 ? 'folder' : 'folders'}: {[...node.folders].sort(byShelfmark).join(', ')}
              </span>
            </p>
            <ul className="mt-1 space-y-0.5">
              {records.map((r, i) => (
                <li key={i}>
                  <a href={`/#${r.folder}/1`} className="tabular font-semibold text-ink-900 hover:text-brand-700">
                    n° {r.folder}
                  </a>{' '}
                  · {KIND[r.kind]} — {r.detail}
                </li>
              ))}
            </ul>
            {together.length > 0 && (
              <p className="mt-1.5 text-ink-500">
                Named with:{' '}
                {together.map((t, i) => (
                  <span key={t.other.name}>
                    {i > 0 && '; '}
                    {t.other.name} <span className="tabular text-ink-400">({t.folders.join(', ')})</span>
                  </span>
                ))}
              </p>
            )}
          </>
        ) : (
          <p className="text-ink-400">
            Hover or focus a dot for the folders, the evidence line by line, and who else each folder
            names. Only people in two folders or more are labelled; the others are named on hover.
          </p>
        )}
      </div>

      {/* The same content without the picture: each community and its members. */}
      <details className="mt-3 text-[12.5px] text-ink-600">
        <summary className="cursor-pointer text-ink-500">The communities as a list</summary>
        <ul className="mt-2 space-y-1.5">
          {clusters.map(({ c, members }) => (
            <li key={c}>
              <span aria-hidden="true" className="mr-1.5 inline-block h-2 w-2 rounded-full" style={{ background: colour(c) }} />
              {members.map((m, i) => (
                <span key={m.name}>
                  {i > 0 && ', '}
                  {m.name} <span className="tabular text-ink-400">({m.folders.join(', ')})</span>
                </span>
              ))}
            </li>
          ))}
        </ul>
      </details>

      <p className="mt-3 max-w-[44em] text-[12px] leading-relaxed text-ink-400">
        Built on {NET.built} from the folders transcribed that morning; `npm run people-network`
        rebuilds it from src/content/people-evidence.json. Co-occurrence is counted fractionally —
        a folder naming n people gives each pair 1/(n−1) — the communities are found by modularity
        and the positions by a force layout, both computed once.
      </p>
    </section>
  );
}
