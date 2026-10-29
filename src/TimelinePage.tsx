import { useMemo, useState } from 'react';
import { Footer, Header } from './components/Frame.tsx';
import { BNF_BOXES, type BnfBox } from './content/bnf-boxes.ts';
import { BOURBAKI_FONDS } from './content/bourbaki-boxes.ts';
import { COTES, GROUPS } from './content/catalogue.ts';
import datedRaw from './content/dated-leaves.json';
import handRaw from './content/hand.json';
import proposedRaw from './content/proposed-datings.json';
import { CommentButton, commentData, useComments } from './components/Comments.tsx';
import type { CommentContext } from './lib/report.ts';
import { openEnd, parseDating, type Dating } from './lib/dating.ts';
import { REDISCOVERIES, type Rediscovery } from './content/rediscoveries.ts';

/**
 * When the folders were written — and how anyone knows.
 *
 * Two kinds of date meet here and are never merged. The inventory's datings
 * are the archivists', mostly deduced (their square brackets), often decades
 * wide. The dates written on the leaves are his, or a typist's, or a machine's,
 * and exact — but rare, and only as many as the folders read so far. The page
 * draws the first as ranges and the second as dots over them, so that a reader
 * sees at once where the two agree, where they do not, and how little of the
 * fonds either covers.
 */

interface Leaf {
  folder: string;
  batch: number;
  page: string;
  written: string;
  iso: string | null;
  kind: string;
  hand: string;
  context: string;
  where: string;
}
const LEAVES = ((datedRaw as unknown as { records: Leaf[] }).records ?? []).filter((l) => l.iso && l.kind !== 'paper' && l.kind !== 'label');
/**
 * A machine stamp — the banner of a computer listing he wrote on the back of,
 * a postmark — dates the paper, not the writing: the leaf can be no older, and
 * may be years younger. Drawn hollow, and kept off the calendar of his days.
 */
const isStamp = (l: Leaf) => l.kind === 'stamp' || l.hand === 'machine';
/**
 * The project's own proposed datings, from the evidence of the leaves. They
 * are drawn beside the inventory's bars and never in their place: the
 * inventory's dating stays what the archivists wrote.
 */
interface Proposal {
  folder: string;
  inventory: string;
  from: string | null;
  to: string | null;
  confidence: 'high' | 'medium' | 'low';
  summary: string;
  evidence: { kind: 'tpq' | 'taq' | 'date'; text: string; where: string }[];
}
const PROPOSALS = (proposedRaw as unknown as { records: Proposal[] }).records ?? [];
const PROPOSED = new Map(PROPOSALS.map((p) => [p.folder, p]));
const BEGUN = new Set((handRaw as unknown as { folders: { id: string }[] }).folders.map((f) => f.id));

const Y0 = 1949;
const Y1 = 1992;
const DARK = '#38539d';
const LIGHT = '#97afe1';
const DOT = '#c9900c';
const PROP = '#1f8a70';
const OPEN_YEARS = 4; // how far an unbounded end of a proposal fades

/** A date as a fractional year: « 1983-12-31 » → 1983.997. */
function frac(iso: string): number {
  const [y, m, d] = iso.split('-').map(Number);
  if (!m) return y + 0.5;
  if (!d) return y + (m - 0.5) / 12;
  return y + (m - 1) / 12 + (d - 0.5) / 365;
}
/** The first and the last instant an ISO date or year names: « 1966-12 » → 1966.917 and 1967. */
function startOf(iso: string): number {
  const [y, m, d] = iso.split('-').map(Number);
  if (!m) return y;
  if (!d) return y + (m - 1) / 12;
  return y + (m - 1) / 12 + (d - 1) / 365;
}
function endOf(iso: string): number {
  const [y, m, d] = iso.split('-').map(Number);
  if (!m) return y + 1;
  if (!d) return y + m / 12;
  return y + (m - 1) / 12 + d / 365;
}
/** A proposal's span in fractional years, an open end faded over a few years. */
function span(p: Proposal): { from: number; to: number } {
  const from = p.from ? startOf(p.from) : endOf(p.to as string) - OPEN_YEARS;
  const to = p.to ? endOf(p.to) : startOf(p.from as string) + OPEN_YEARS;
  return { from, to };
}
const interval = (p: Proposal) =>
  p.from && p.to ? `${p.from} – ${p.to}` : p.from ? `from ${p.from}, no end proposed` : `until ${p.to}, no start proposed`;
const shortTitle = (t: string) => t.replace(/\s*:\s*notes manuscrites.*$/i, '').replace(/\s*:.*$/, '');
const byShelfmark = (a: string, b: string) => {
  const [a0, a1 = '0'] = a.split('-');
  const [b0, b1 = '0'] = b.split('-');
  return Number(a0) - Number(b0) || Number(a1) - Number(b1);
};

interface Row {
  id: string;
  title: string;
  dating: Dating;
  from: number;
  to: number;
  open: boolean;
  openStart: boolean;
  read: boolean;
  leaves: Leaf[];
  proposal: Proposal | undefined;
}

const ROWS: Row[] = COTES.flatMap((c) => {
  const d = parseDating(c.date);
  if (!d) return [];
  const from = d.start?.year ?? (d.end ? d.end.year - 4 : Y0);
  const to = d.end ? d.end.year + 1 : from + 1;
  return [
    {
      id: c.id,
      title: c.title,
      dating: d,
      from,
      to,
      open: openEnd(d),
      openStart: d.start === null,
      read: !(d.start?.inferred ?? true) && !(d.end?.inferred ?? true),
      leaves: LEAVES.filter((l) => l.folder === c.id),
      proposal: PROPOSED.get(c.id),
    },
  ];
}).sort((a, b) => a.from - b.from || a.to - b.to || byShelfmark(a.id, b.id));
const UNDATED = COTES.filter((c) => !parseDating(c.date));

/**
 * Lanes: a folder goes in the first lane whose last bar, fade included, ends
 * before its own starts. One row per folder made the figure 150 rows tall
 * for a chart whose busiest year has about fifty; packed, it is as tall as
 * the overlap actually is, and still read left to right in order of start.
 */
const GAP = 0.8; // years of white between two bars in a lane
const LANE: number[] = [];
{
  const ends: number[] = [];
  for (const r of ROWS) {
    // A leaf dated outside its folder's range widens the folder's claim on the
    // lane, so its dot never lands on a neighbour's bar.
    // So does a proposed dating, drawn under the bar.
    const ls = r.leaves.map((l) => frac(l.iso as string));
    const ps = r.proposal ? [span(r.proposal)] : [];
    const start = Math.min(r.from, ...ls, ...ps.map((p) => p.from));
    const end = Math.max(r.open ? r.to + 5 : r.to, ...ls.map((v) => v + 0.3), ...ps.map((p) => p.to));
    let k = ends.findIndex((e) => e + GAP <= start);
    if (k < 0) k = ends.push(-Infinity) - 1;
    ends[k] = end;
    LANE.push(k);
  }
}
const LANES = Math.max(...LANE) + 1;

function H2({ id, children }: { id: string; children: React.ReactNode }) {
  return (
    <h2 id={id} className="scroll-mt-16 text-[11px] font-bold uppercase tracking-[0.12em] text-ink-400">
      {children}
    </h2>
  );
}

/* ---------- the life, sourced ---------- */

const MACTUTOR = 'https://mathshistory.st-andrews.ac.uk/Biographies/Grothendieck/';
const FONDS = 'https://grothendieck.umontpellier.fr/';
const LIFE: { year: number; what: string; source: string }[] = [
  { year: 1953, what: 'Thesis at Nancy, on topological tensor products and nuclear spaces', source: MACTUTOR },
  { year: 1958, what: 'Joins the new Institut des Hautes Études Scientifiques', source: MACTUTOR },
  { year: 1960, what: 'First volume of the Éléments de géométrie algébrique, with Dieudonné', source: MACTUTOR },
  { year: 1966, what: 'Fields Medal', source: MACTUTOR },
  { year: 1970, what: 'Leaves the IHÉS', source: MACTUTOR },
  { year: 1973, what: 'Professor at the University of Montpellier', source: MACTUTOR },
  { year: 1988, what: 'Retires', source: MACTUTOR },
  { year: 1990, what: 'Hands his mathematical papers to Jean Malgoire (a second part follows on 28 July 1995); they later form this fonds', source: FONDS },
];

/* ---------- the works, sourced ---------- */

const CIRCLE_BIBLIO = 'https://webusers.imj-prg.fr/~leila.schneps/grothendieckcircle/GrothBiblio.pdf';
const CIRCLE_UNPUB = 'https://webusers.imj-prg.fr/~leila.schneps/grothendieckcircle/unpubtexts.php';
const NUMDAM = 'https://www.numdam.org/search?Publications%20math%C3%A9matiques%20de%20l%27IH%C3%89S-%22Grothendieck%2C%20Alexander%22-qn';
const BNF = 'https://archivesetmanuscrits.bnf.fr/ark:/12148/cc126317b';
const BOREL_SERRE = 'https://www.numdam.org/item/BSMF_1958__86__97_0/';
const DE_RHAM = 'https://www.numdam.org/item/PMIHES_1966__29__95_0/';
const SOURCE_NAME: Record<string, string> = {
  [BNF]: 'BnF, NAF 29093',
  [CIRCLE_BIBLIO]: 'bibliography, Grothendieck Circle',
  [CIRCLE_UNPUB]: 'Grothendieck Circle',
  [NUMDAM]: 'Numdam',
  [BOREL_SERRE]: 'Borel–Serre, Numdam',
  [DE_RHAM]: 'Numdam',
  [MACTUTOR]: 'MacTutor',
};

/**
 * The book-length works, placed on the folders' own axis so that a reader can
 * see which folders stand beside which treatise. Seminars and runs of talks
 * are drawn as the years they were held, volumes as the year they appeared;
 * each carries the reference it is taken from, and where two references
 * disagree the row says so rather than choosing.
 */
interface Work {
  row: string;
  label: string;
  from: number;
  to?: number;
  detail: string;
  source: string[];
  /** Which of the row's two tracks, and on which side the label goes; above the mark by default. */
  track?: number;
  side?: 'left' | 'right';
}
const WORKS: Work[] = [
  { row: 'EGA', label: 'I', from: 1960, detail: 'EGA I, Le langage des schémas — Publ. Math. IHÉS 4 (1960), with Dieudonné', source: [NUMDAM, CIRCLE_BIBLIO] },
  { row: 'EGA', label: 'II, III₁', from: 1961, detail: 'EGA II, Étude globale élémentaire — IHÉS 8; EGA III, première partie — IHÉS 11 (1961)', source: [NUMDAM, CIRCLE_BIBLIO] },
  { row: 'EGA', label: 'III₂', from: 1963, detail: 'EGA III, seconde partie — IHÉS 17 (1963)', source: [NUMDAM, CIRCLE_BIBLIO] },
  { row: 'EGA', label: 'IV₁', from: 1964, detail: 'EGA IV, première partie — IHÉS 20 (1964)', source: [NUMDAM, CIRCLE_BIBLIO] },
  { row: 'EGA', label: 'IV₂', from: 1965, detail: 'EGA IV, seconde partie — IHÉS 24 (1965)', source: [NUMDAM, CIRCLE_BIBLIO] },
  { row: 'EGA', label: 'IV₃', from: 1966, detail: 'EGA IV, troisième partie — IHÉS 28 (1966)', source: [NUMDAM, CIRCLE_BIBLIO] },
  { row: 'EGA', label: 'IV₄', from: 1967, detail: 'EGA IV, quatrième partie — IHÉS 32 (1967)', source: [NUMDAM, CIRCLE_BIBLIO] },
  { row: 'FGA', label: 'FGA', from: 1957, to: 1962, detail: 'Fondements de la géométrie algébrique: his talks at the Séminaire Bourbaki, 1956/57 to 1961/62, with the « Commentaires » of 1961/62', source: [CIRCLE_BIBLIO] },
  { row: 'SGA', label: '1', from: 1960, to: 1961, detail: 'SGA 1, Revêtements étales et groupe fondamental — seminar 1960–61; LNM 224 (1971)', source: [CIRCLE_BIBLIO] },
  { row: 'SGA', label: '2', from: 1961, to: 1962, detail: 'SGA 2, Cohomologie locale des faisceaux cohérents et théorèmes de Lefschetz locaux et globaux — seminar 1961–62; North-Holland (1968)', source: [CIRCLE_BIBLIO] },
  { row: 'SGA', label: '3', from: 1962, to: 1964, detail: 'SGA 3, Schémas en groupes, with Demazure — seminar 1962–64; LNM 151–153 (1970)', source: [CIRCLE_BIBLIO] },
  { row: 'SGA', label: '4', from: 1963, to: 1964, detail: 'SGA 4, Théorie des topos et cohomologie étale, with Artin and Verdier — seminar 1963–64; LNM 269, 270, 305 (1972–73)', source: [CIRCLE_BIBLIO] },
  { row: 'SGA', label: '5', from: 1965, to: 1966, detail: 'SGA 5, Cohomologie ℓ-adique et fonctions L — seminar 1965–66; LNM 589 (1977)', source: [CIRCLE_BIBLIO] },
  { row: 'SGA', label: '6', from: 1966, to: 1967, detail: 'SGA 6, Théorie des intersections et théorème de Riemann–Roch, with Berthelot and Illusie — seminar 1966–67; LNM 225 (1971)', source: [CIRCLE_BIBLIO] },
  { row: 'SGA', label: '7', from: 1967, to: 1969, detail: 'SGA 7, Groupes de monodromie en géométrie algébrique — seminar 1967–69; LNM 288 (1972), 340 (1973, Deligne and Katz)', source: [CIRCLE_BIBLIO] },
  { row: 'Manuscripts', label: 'Longue Marche', from: 1981, track: 0, side: 'left', detail: 'La Longue Marche à travers la théorie de Galois — nearly 800 handwritten double pages; folders 140-1 to 140-4', source: [MACTUTOR, CIRCLE_UNPUB] },
  { row: 'Manuscripts', label: 'À la poursuite des champs', from: 1983, track: 1, side: 'left', detail: 'À la poursuite des champs (Pursuing Stacks) — folders 134-1 to 134-8', source: [CIRCLE_BIBLIO, MACTUTOR] },
  { row: 'Manuscripts', label: 'Esquisse', from: 1984, track: 0, side: 'right', detail: "Esquisse d'un programme — folder 119; the bibliography dates it 1984, MacTutor 1983", source: [CIRCLE_BIBLIO, MACTUTOR] },
  { row: 'Manuscripts', label: 'Dérivateurs', from: 1987, to: 1991, track: 1, detail: 'Les Dérivateurs — folders 157-1 to 157-5; MacTutor gives 1987, the Grothendieck Circle calls it his 1991 manuscript', source: [MACTUTOR, CIRCLE_UNPUB] },
  { row: 'Other writings', label: 'Récoltes et semailles', from: 1983, to: 1985, side: 'left', detail: 'Récoltes et semailles — written 1983–85; issued by the Université des Sciences et Techniques du Languedoc and the CNRS (1985)', source: [MACTUTOR, CIRCLE_BIBLIO] },
  { row: 'Other writings', label: 'La Clef des songes', from: 1987, to: 1988, side: 'right', detail: 'La Clef des songes — ou Dialogue avec le bon Dieu, April 1987 to April 1988: the corrected typescript is NAF 29093 (1–2) at the BnF (MacTutor gives 1986)', source: [BNF, MACTUTOR] },
  // The theorems, at the year of the paper or talk that proves them, as his
  // bibliography dates it — not the year the idea came, which nobody can date.
  // Numbered on the figure, since a dozen names would not fit its decade.
  { row: 'Theorems', label: '1', from: 1955, detail: '① Nuclear spaces and the approximation property: every nuclear space has it — Produits tensoriels topologiques et espaces nucléaires, his thesis (defended 1953), Mem. AMS 16 (1955)', source: [CIRCLE_BIBLIO, MACTUTOR] },
  { row: 'Theorems', label: '2', from: 1956, detail: "② Grothendieck's inequality, the « théorème fondamental de la théorie métrique des produits tensoriels » — Résumé de la théorie métrique des produits tensoriels topologiques, Bol. Soc. Mat. São Paulo 8 (1956)", source: [CIRCLE_BIBLIO] },
  { row: 'Theorems', label: '3', from: 1957, detail: '③ Every holomorphic vector bundle on the Riemann sphere is a sum of line bundles — Sur la classification des fibrés holomorphes sur la sphère de Riemann, Amer. J. Math. 79 (1957)', source: [CIRCLE_BIBLIO] },
  { row: 'Theorems', label: '4', from: 1957, track: 1, detail: '④ Tôhoku: abelian categories with enough injectives, sheaf cohomology as a derived functor, its vanishing above the dimension, the spectral sequence of a composite functor — Sur quelques points d\'algèbre homologique, Tôhoku Math. J. 9 (1957)', source: [CIRCLE_BIBLIO] },
  { row: 'Theorems', label: '5', from: 1958, track: 1, detail: "⑤ Grothendieck–Riemann–Roch, for a projective morphism of smooth quasi-projective varieties — his theorem of 1957, first written up by Borel and Serre, Bull. SMF 86 (1958); in full generality SGA 6 (1966–67)", source: [BOREL_SERRE, MACTUTOR] },
  { row: 'Theorems', label: '6', from: 1959, track: 0, detail: '⑥ Coherent duality, then the existence theorem in formal geometry — Séminaire Bourbaki n° 149 (1956/57) and n° 195 (1959/60); the theorem on formal functions, EGA III₁ (1961)', source: [CIRCLE_BIBLIO] },
  { row: 'Theorems', label: '7', from: 1961, track: 1, detail: '⑦ Hilbert and Quot schemes exist — Séminaire Bourbaki n° 221 (1960/61); the Picard scheme, n° 232 and 236 (1961/62)', source: [CIRCLE_BIBLIO] },
  { row: 'Theorems', label: '8', from: 1960, track: 0, detail: '⑧ The étale fundamental group, and the prime-to-p fundamental group of a curve, known from its lift to characteristic 0 — SGA 1 (1960–61)', source: [CIRCLE_BIBLIO, MACTUTOR] },
  { row: 'Theorems', label: '9', from: 1962, track: 1, detail: '⑨ Lefschetz theorems, local and global, for the Picard group and the fundamental group — SGA 2 (1961–62)', source: [CIRCLE_BIBLIO] },
  { row: 'Theorems', label: '10', from: 1965, track: 0, detail: '⑩ The Lefschetz trace formula in ℓ-adic cohomology and the rationality of L-functions — Formule de Lefschetz et rationalité des fonctions L, Séminaire Bourbaki n° 279 (1964/65); SGA 5 (1965–66)', source: [CIRCLE_BIBLIO] },
  { row: 'Theorems', label: '11', from: 1966, track: 1, detail: '⑪ Algebraic de Rham cohomology computes the cohomology of the complex variety — On the de Rham cohomology of algebraic varieties, Publ. Math. IHÉS 29 (1966)', source: [DE_RHAM] },
  { row: 'Theorems', label: '12', from: 1968, track: 0, detail: "⑫ The ℓ-adic local monodromy theorem: monodromy is quasi-unipotent — SGA 7 (1967–69), exposé I", source: [CIRCLE_BIBLIO] },
];
const WORK_ROWS = ['EGA', 'FGA', 'SGA', 'Theorems', 'Manuscripts', 'Other writings'];

function Works() {
  const [sel, setSel] = useState<Work | null>(null);
  const W = 900;
  const L = 110;
  const R = 16;
  const ROWH = 34;
  const TOP = 22;
  const H = TOP + WORK_ROWS.length * ROWH + 8;
  const x = (y: number) => L + ((y - Y0) / (Y1 - Y0)) * (W - L - R);
  const decades = [1950, 1955, 1960, 1965, 1970, 1975, 1980, 1985, 1990];
  // The seminars overlap; they alternate on two tracks of their row. The
  // manuscripts say which track they take.
  const track = (w: Work) =>
    w.track ?? (w.row === 'SGA' ? WORKS.filter((v) => v.row === 'SGA').indexOf(w) % 2 : 0);
  return (
    <section className="mt-12">
      <H2 id="works">The works, on the same years</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        His treatises, seminars and long manuscripts, on the axis of the folders above: a volume
        at the year it appeared, a seminar or a run of talks over the years it was held, a
        manuscript at the date its reference gives. The numbered row of theorems places each main
        result at the paper or talk that proves it. Hover a mark for its reference; the list under
        the figure gives every work with the source of its date.
      </p>
      <div className="mt-3 overflow-x-auto" onMouseLeave={() => setSel(null)}>
        <svg
          viewBox={`0 0 ${W} ${H}`}
          className="w-full min-w-[640px] rounded-[var(--radius-card)] border border-ink-200 bg-white"
          role="img"
          aria-label="EGA, FGA, SGA, his main theorems, and his later manuscripts and writings, by year"
        >
          {decades.map((d) => (
            <g key={d}>
              <line x1={x(d)} x2={x(d)} y1={TOP - 6} y2={H - 6} stroke="var(--color-ink-200)" />
              <text x={x(d)} y={TOP - 10} textAnchor="middle" className="tabular" style={{ fontSize: 11, fill: 'var(--color-ink-400)' }}>
                {d}
              </text>
            </g>
          ))}
          {WORK_ROWS.map((row, i) => (
            <text key={row} x={10} y={TOP + i * ROWH + ROWH / 2 + 4} style={{ fontSize: 11.5, fill: 'var(--color-ink-600)', fontWeight: 600 }}>
              {row}
            </text>
          ))}
          {WORKS.map((w) => {
            const i = WORK_ROWS.indexOf(w.row);
            const y = TOP + i * ROWH + 8 + track(w) * 13;
            const on = sel === null || sel === w;
            const x0 = x(w.from);
            const x1 = w.to ? x(w.to + 1) : x0;
            return (
              <g key={w.row + w.label} opacity={on ? 1 : 0.3} onMouseEnter={() => setSel(w)} style={{ cursor: 'pointer' }}>
                <rect x={x0 - 4} y={y - 6} width={Math.max(8, x1 - x0) + 8} height={16} fill="#fff" fillOpacity={0} />
                {w.row === 'Theorems' && !w.to ? (
                  <rect x={x(w.from + 0.5) - 3.2} y={y - 0.7} width={6.4} height={6.4} transform={`rotate(45 ${x(w.from + 0.5)} ${y + 2.5})`} fill="var(--color-brand-600)" />
                ) : w.to ? (
                  <rect x={x0} y={y} width={x1 - x0} height={5} rx={2} fill={w.row === 'Theorems' ? 'var(--color-brand-600)' : 'var(--color-ink-700)'} />
                ) : (
                  <circle cx={x(w.from + 0.5)} cy={y + 2.5} r={3.6} fill="var(--color-ink-700)" />
                )}
                <text
                  x={
                    w.side === 'left'
                      ? (w.to ? x0 : x(w.from + 0.5)) - 7
                      : w.side === 'right'
                        ? (w.to ? x1 : x(w.from + 0.5)) + 7
                        : w.to
                          ? x0 + (x1 - x0) / 2
                          : x(w.from + 0.5)
                  }
                  // The theorems' second track labels below its marks, clear of the first track's.
                  y={w.side ? y + 6 : w.row === 'Theorems' && track(w) === 1 ? y + 15 : y - 2}
                  textAnchor={w.side === 'left' ? 'end' : w.side === 'right' ? 'start' : 'middle'}
                  style={{ fontSize: 10, fill: 'var(--color-ink-500)' }}
                >
                  {w.label}
                </text>
              </g>
            );
          })}
        </svg>
      </div>
      <p className="mt-2 min-h-[2.5em] text-[12.5px] leading-relaxed text-ink-600">
        {sel ? sel.detail : <span className="text-ink-400">Hover a mark for the work and its dates.</span>}
      </p>
      <ul className="mt-3 space-y-1.5 text-[13px] text-ink-700">
        {WORKS.map((w) => (
          <li key={w.row + w.label} className="flex gap-3">
            <span className="tabular w-[5.5rem] shrink-0 font-semibold text-ink-900">
              {w.to ? `${w.from}–${w.to}` : w.from}
            </span>
            <span>
              {w.detail}{' '}
              {w.source.map((src, k) => (
                <span key={src}>
                  {k > 0 && ' · '}
                  <a href={src} target="_blank" rel="noopener noreferrer" className="text-[12px] text-brand-600 hover:text-brand-700">
                    {SOURCE_NAME[src]} ↗
                  </a>
                </span>
              ))}
            </span>
          </li>
        ))}
      </ul>
    </section>
  );
}


/* ---------- the works as volumes ---------- */

// Words per page, so that a typed or printed page weighs more than a handwritten
// one. Handwritten and typed are measured on the transcriptions (median over
// 107 handwritten folders, mean over the 3 typescript folders transcribed);
// printed is an estimate for the IHÉS Publications and the Lecture Notes, not
// a measurement.
// clean: the BnF fair copies (1992–1996), written out as courses, denser than the working notes; an estimate, to count on a page at the BnF.
const WPP = { hand: 140, clean: 250, typed: 200, printed: 450 } as const;
type VolumeKind = keyof typeof WPP;
type VolumeStatus = 'printed' | 'edited' | 'unedited' | 'bnf';
type Volume = { title: string; short?: string; years: string; kind: VolumeKind; status: VolumeStatus; pages: number; cotes?: string[]; note?: string; edition?: string };

const pagesOf = (cotes: string[]) => cotes.reduce((a, c) => a + (COTES.find((k) => k.id === c)?.pages ?? 0), 0);
const range = (p: string, a: number, b: number) => Array.from({ length: b - a + 1 }, (_, i) => `${p}${a + i}`);

const VOLUMES: Volume[] = ([
  { title: 'EGA I', years: '1960', kind: 'printed', status: 'printed', pages: 228, note: 'Publ. Math. IHÉS 4' , edition: '2nd edition, Springer, Grundlehren 166 (1971)' },
  { title: 'SGA 1', years: '1960–61', kind: 'printed', status: 'printed', pages: 447, note: 'LNM 224 (1971)' , edition: 're-edited, SMF, Documents mathématiques 3 (2003)' },
  { title: 'EGA II', years: '1961', kind: 'printed', status: 'printed', pages: 222, note: 'Publ. Math. IHÉS 8' },
  { title: 'EGA III', years: '1961–63', kind: 'printed', status: 'printed', pages: 258, note: 'Publ. Math. IHÉS 11, 17' },
  { title: 'SGA 2', years: '1962', kind: 'printed', status: 'printed', pages: 290, note: 'approximate' , edition: 're-edited, SMF, Documents mathématiques 4 (2005)' },
  { title: 'SGA 3', years: '1962–64', kind: 'printed', status: 'printed', pages: 1750, note: 'LNM 151–153, approximate' , edition: 're-edited by Gille and Polo, SMF, Documents mathématiques 7–8 (2011)' },
  { title: 'SGA 4', years: '1963–64', kind: 'printed', status: 'printed', pages: 1580, note: 'LNM 269, 270, 305, approximate' },
  { title: 'EGA IV', years: '1964–67', kind: 'printed', status: 'printed', pages: 1106, note: 'Publ. Math. IHÉS 20, 24, 28, 32' },
  { title: 'SGA 5', years: '1965–66', kind: 'printed', status: 'printed', pages: 480, note: 'LNM 589, approximate' },
  { title: 'SGA 6', years: '1966–67', kind: 'printed', status: 'printed', pages: 700, note: 'LNM 225, approximate' },
  { title: 'SGA 7', years: '1967–69', kind: 'printed', status: 'printed', pages: 960, note: 'LNM 288, 340, approximate' },
  { title: 'La Longue Marche', short: 'Longue Marche', years: '1981', kind: 'hand', status: 'unedited', pages: 0, cotes: range('140-', 1, 4), note: '§ 1–37 edited by Malgoire (1995), the rest unedited' , edition: '§ 1–37 only, ed. Malgoire, Université Montpellier II (1995)' },
  { title: 'Teichmülleries', years: '1981–83', kind: 'hand', status: 'unedited', pages: 0, cotes: ['144'] },
  { title: "Structure à l'infini des M_{g,ν}", short: 'Structure à l’infini', years: '1982–83', kind: 'hand', status: 'unedited', pages: 0, cotes: ['147'], note: 'dated by the edition to the winter of 1982–83' },
  { title: 'À la poursuite des champs', short: 'Poursuite des champs', years: '1983', kind: 'typed', status: 'edited', pages: 0, cotes: range('134-', 2, 8), note: 'volume I edited by Maltsiniotis (2022)' , edition: 'vol. I, ed. Maltsiniotis, SMF, Documents mathématiques 20 (2022)' },
  { title: "Esquisse d'un programme", short: 'Esquisse', years: '1984', kind: 'printed', status: 'edited', pages: 44, note: 'as printed in Geometric Galois Actions 1 (1997)' , edition: 'in Geometric Galois Actions 1, Cambridge (1997)' },
  { title: 'Vers une géométrie des formes', short: 'Géométrie des formes', years: '1986', kind: 'hand', status: 'unedited', pages: 0, cotes: range('156-', 1, 9) },
  { title: 'Les Dérivateurs', short: 'Dérivateurs', years: '1990–91', kind: 'hand', status: 'edited', pages: 0, cotes: range('157-', 1, 5), note: 'edited by Künzer, Malgoire and Maltsiniotis' , edition: 'ed. Künzer, Malgoire and Maltsiniotis (online)' },
  { title: 'Géométrie élémentaire schématique', short: 'Géom. élém. schématique', years: '1992', kind: 'clean', status: 'bnf', pages: 1098, note: 'BnF, box 3: 549 leaves written on both sides' },
  { title: 'Trialité', years: '1995', kind: 'clean', status: 'bnf', pages: 89, note: 'BnF, box 43: 89 leaves (counted as pages)' },
  { title: 'Notions de « géographie combinatoire »', short: 'Géographie combinatoire', years: '1996', kind: 'clean', status: 'bnf', pages: 32, note: 'BnF, box 43, pochette 1: 32 leaves of text (28–30 June 1996) and 4 of figures, from the BnF notice' },
] as Volume[]).map((v) => (v.cotes ? { ...v, pages: pagesOf(v.cotes) } : v));

const VOLUME_STYLE: Record<VolumeStatus, { fill: string; stroke: string; dash?: string; label: string }> = {
  printed: { fill: 'var(--color-ink-300)', stroke: 'var(--color-ink-500)', label: 'Printed by him (EGA, SGA)' },
  edited: { fill: 'var(--color-brand-600)', stroke: 'var(--color-brand-700)', label: 'Manuscript, edited (in whole or part)' },
  unedited: { fill: '#fff', stroke: 'var(--color-brand-600)', label: 'Manuscript, unedited (Montpellier)' },
  bnf: { fill: '#fff', stroke: 'var(--color-brand-600)', dash: '3 2', label: 'Manuscript, unedited and not transcribed (BnF)' },
};

const RIBBON = '#eb6834';

function Volumes() {
  const [sel, setSel] = useState<Volume | null>(null);
  const W = 900;
  const PAD = 12;
  const SHELF = 150;
  const BOOK = 118;
  const GAP = 2;
  const PER_PX = 2000; // words per pixel of thickness
  const words = (v: Volume) => v.pages * WPP[v.kind];
  // Fill shelves left to right in reading order; a book never splits.
  const placed: { v: Volume; x: number; w: number; row: number }[] = [];
  let x = PAD;
  let row = 0;
  for (const v of VOLUMES) {
    const w = Math.max(3, words(v) / PER_PX);
    if (x + w > W - PAD) {
      row += 1;
      x = PAD;
    }
    placed.push({ v, x, w, row });
    x += w + GAP;
  }
  const H = (row + 1) * SHELF + 8;
  const fmt = (n: number) => n.toLocaleString('en-US');
  return (
    <section className="mt-12">
      <H2 id="volumes">The works as volumes</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        EGA, SGA and the long manuscripts as books on a shelf, in the order they were written. Each
        spine's thickness is proportional to an estimate of its length in words, not in pages: a
        handwritten page of his carries about {WPP.hand} words, a typed page about {WPP.typed}, a
        printed page of EGA or SGA about {WPP.printed}. The first two figures are measured on the
        transcriptions; the printed one is an estimate, and the SGA page counts are approximate. The three
        BnF texts are fair copies written out as courses, much denser than the working notes: they are
        counted at about {WPP.clean} words a page, an estimate not yet measured.
        Hover a spine for its pages and words.
      </p>
      <div className="mt-3 flex flex-wrap gap-x-5 gap-y-1 text-[12px] text-ink-600">
        {(Object.keys(VOLUME_STYLE) as VolumeStatus[]).map((k) => (
          <span key={k} className="inline-flex items-center gap-1.5">
            <svg width="12" height="14" aria-hidden="true">
              <rect x="1" y="1" width="10" height="12" rx="1.5" fill={VOLUME_STYLE[k].fill} stroke={VOLUME_STYLE[k].stroke} strokeWidth="1.5" strokeDasharray={VOLUME_STYLE[k].dash} />
            </svg>
            {VOLUME_STYLE[k].label}
          </span>
        ))}
        <span className="inline-flex items-center gap-1.5">
          <svg width="10" height="14" aria-hidden="true">
            <path d="M1 0 h8 v13 l-4 -4 l-4 4 z" fill={RIBBON} />
          </svg>
          Published since: a later edition, or the first edition of a manuscript
        </span>
      </div>
      <div className="mt-3 overflow-x-auto" onMouseLeave={() => setSel(null)}>
        <svg
          viewBox={`0 0 ${W} ${H}`}
          className="w-full min-w-[640px] rounded-[var(--radius-card)] border border-ink-200 bg-white"
          role="img"
          aria-label="EGA, SGA and the long manuscripts as book spines whose thickness is proportional to their length in words"
        >
          {Array.from({ length: row + 1 }, (_, r) => (
            <line key={r} x1={PAD - 4} x2={W - PAD + 4} y1={r * SHELF + 14 + BOOK + 1} y2={r * SHELF + 14 + BOOK + 1} stroke="var(--color-ink-400)" strokeWidth={2} />
          ))}
          {placed.map(({ v, x: bx, w, row: r }) => {
            const st = VOLUME_STYLE[v.status];
            const y0 = r * SHELF + 14;
            const on = sel === null || sel === v;
            return (
              <g key={v.title} opacity={on ? 1 : 0.35} onMouseEnter={() => setSel(v)} style={{ cursor: 'pointer' }}>
                <rect x={bx} y={y0} width={w} height={BOOK} rx={2} fill={st.fill} stroke={st.stroke} strokeWidth={1.5} strokeDasharray={st.dash} />
                {v.edition && <path d={`M${bx + w / 2 - Math.min(4, w / 2 - 1)} ${y0 - 1} h${2 * Math.min(4, w / 2 - 1)} v14 l-${Math.min(4, w / 2 - 1)} -4 l-${Math.min(4, w / 2 - 1)} 4 z`} fill={RIBBON} />}
                {w >= 13 && (
                  <text
                    transform={`translate(${bx + w / 2 + 3.5} ${y0 + BOOK - 6}) rotate(-90)`}
                    style={{ fontSize: 10, fill: v.status === 'edited' ? '#fff' : 'var(--color-ink-800)', fontWeight: 600 }}
                  >
                    {(() => { const t = v.short ?? v.title; return t.length > 20 ? t.slice(0, 19) + '…' : t; })()}
                  </text>
                )}
                <text x={bx + w / 2} y={y0 + BOOK + 14} textAnchor="middle" className="tabular" style={{ fontSize: 9, fill: 'var(--color-ink-500)' }}>
                  {w >= 22 ? v.years.slice(0, 4) : ''}
                </text>
              </g>
            );
          })}
        </svg>
      </div>
      <p className="mt-2 min-h-[2.5em] text-[12.5px] leading-relaxed text-ink-600">
        {sel ? (
          <>
            <span className="font-semibold text-ink-900">{sel.title}</span> ({sel.years}) · {fmt(sel.pages)} {sel.kind === 'printed' ? 'printed' : sel.kind === 'typed' ? 'typed' : sel.kind === 'clean' ? 'handwritten (fair copy)' : 'handwritten'} pages · about {fmt(Math.round(words(sel) / 1000) * 1000)} words
            {sel.cotes && <> · folders {sel.cotes[0]}–{sel.cotes[sel.cotes.length - 1].split('-').pop()}</>}
            {sel.note && <> · {sel.note}</>}
            {sel.edition && <> · <span className="text-ink-800">published since: {sel.edition}</span></>}
          </>
        ) : (
          <span className="text-ink-400">Hover a spine for the work, its pages and its estimated length.</span>
        )}
      </p>
      <details className="mt-2 text-[12.5px] text-ink-600">
        <summary className="cursor-pointer text-ink-500 hover:text-brand-700">The figures as a table</summary>
        <table className="mt-2 w-full max-w-[52em] border-collapse">
          <thead>
            <tr className="text-left text-ink-500">
              <th className="py-1 pr-3 font-semibold">Work</th>
              <th className="py-1 pr-3 font-semibold">Years</th>
              <th className="py-1 pr-3 text-right font-semibold">Pages</th>
              <th className="py-1 pr-3 font-semibold">Kind</th>
              <th className="py-1 pr-3 text-right font-semibold">Words (est.)</th>
              <th className="py-1 font-semibold">Note</th>
            </tr>
          </thead>
          <tbody>
            {VOLUMES.map((v) => (
              <tr key={v.title} className="border-t border-ink-100">
                <td className="py-1 pr-3 text-ink-800">{v.title}</td>
                <td className="tabular py-1 pr-3">{v.years}</td>
                <td className="tabular py-1 pr-3 text-right">{fmt(v.pages)}</td>
                <td className="py-1 pr-3">{v.kind}</td>
                <td className="tabular py-1 pr-3 text-right">{fmt(Math.round(words(v) / 1000) * 1000)}</td>
                <td className="py-1 text-ink-500">{[VOLUME_STYLE[v.status].label, v.note, v.edition && `published since: ${v.edition}`].filter(Boolean).join(' · ')}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </details>
    </section>
  );
}

/* ---------- figure: the boxes of the two fonds ---------- */

const PAGES_OF = new Map(COTES.map((c) => [c.id, c.pages ?? 0]));
const MTP_BOXES = GROUPS.map((g) => ({
  id: g.id,
  title: g.title.replace(/\s*\(.*$/, '').replace(/^MATHÉMATIQUES \/ RECHERCHE \/ /, ''),
  folders: g.cotes.length,
  pages: g.cotes.reduce((a, c) => a + (PAGES_OF.get(c) ?? 0), 0),
}));
const SHEET_CM = 0.01; // a sheet of 80 g paper is about a tenth of a millimetre thick
const A4 = { w: 21, d: 29.7 }; // cm

interface RoomBox {
  key: string;
  label: string;
  sheets: number;
  fill: string;
  detail: string;
}

/** Shade a hex colour: f < 1 darkens, f > 1 lightens. */
function shade(hex: string, f: number): string {
  const n = parseInt(hex.slice(1), 16);
  const c = [(n >> 16) & 255, (n >> 8) & 255, n & 255].map((v) =>
    Math.round(f < 1 ? v * f : v + (255 - v) * (f - 1)),
  );
  return `rgb(${c.join(',')})`;
}

/**
 * Library shelving seen in perspective, from the front, by a person standing in the aisle. The boxes
 * have an A4 footprint and lie flat, as tall as their stack of paper; they are stacked tallest first
 * into piles that fit between two shelves, and fill first the shelves within easy reach. Faces are
 * painted far to near, so a shelf hides what lies behind it.
 */
const SHELF = { w: 100, d: 32, gap: 37, levels: 5, board: 2 }; // cm: bays 1 m wide, shelves 37 cm apart, about 1.85 m tall
// Shelves filled first: those within easy reach of a person of average height (about 0.75 m to 1.5 m), then the others.
const REACH_ORDER = [2, 3, 1, 4, 0];
const EYE = { z: 160, dist: 240 }; // cm: eye height, and distance from the front of the shelving

type V3 = [number, number, number];

function Room({ title, sets, sel, onSel }: { title: string; sets: { label: string; boxes: RoomBox[] }[]; sel: string | null; onSel: (k: string | null) => void }) {
  const bays = sets.length;
  const width = bays * SHELF.w;
  const shelfH = SHELF.levels * SHELF.gap;
  const pileMax = SHELF.gap - SHELF.board - 3;
  const perShelf = Math.floor(SHELF.w / (A4.w + 3));
  const eyeX = width / 2; // standing in front of the middle of the shelving
  const F = 330; // focal length, px
  // x: along the shelving, y: depth away from the viewer, z: up.
  const proj = ([x, y, z]: V3): [number, number] => {
    const k = F / (EYE.dist + y);
    return [(x - eyeX) * k, (EYE.z - z) * k];
  };
  // Piles per set, in its own bay.
  const placed = sets.flatMap((set, bay) => {
    const piles: { boxes: { b: RoomBox; z: number; h: number }[]; top: number }[] = [];
    for (const b of [...set.boxes].sort((p, q) => q.sheets - p.sheets)) {
      const h = Math.max(0.4, b.sheets * SHEET_CM);
      const pile = piles.find((p) => p.top + h <= pileMax);
      if (pile) {
        pile.boxes.push({ b, z: pile.top, h });
        pile.top += h;
      } else piles.push({ boxes: [{ b, z: 0, h }], top: h });
    }
    return piles.flatMap((p, i) => {
      const level = REACH_ORDER[Math.floor(i / perShelf) % SHELF.levels];
      const x0 = bay * SHELF.w + 3 + (i % perShelf) * (A4.w + 3);
      return p.boxes.map((x) => ({ ...x, level, x0, z: x.z + level * SHELF.gap + SHELF.board }));
    });
  });
  type Face = { pts: V3[]; fill: string; stroke?: string; key?: string; detail?: string; depth: number };
  const depthOf = (pts: V3[]) => {
    const c = pts.reduce((a, q) => [a[0] + q[0] / pts.length, a[1] + q[1] / pts.length, a[2] + q[2] / pts.length], [0, 0, 0]);
    return Math.hypot(c[0] - eyeX, c[1] + EYE.dist, c[2] - EYE.z);
  };
  // A box (or board) as its visible faces, painted far to near.
  const cuboid = (x0: number, x1: number, y0: number, y1: number, z0: number, z1: number, base: string, extra: Partial<Face> = {}): Face[] => {
    const out: Face[] = [];
    const add = (pts: V3[], fill: string) => out.push({ pts, fill, depth: depthOf(pts), ...extra });
    add([[x0, y0, z0], [x1, y0, z0], [x1, y0, z1], [x0, y0, z1]], shade(base, 0.9)); // front
    if (EYE.z > z1) add([[x0, y0, z1], [x1, y0, z1], [x1, y1, z1], [x0, y1, z1]], shade(base, 1.2)); // top
    if (EYE.z < z0) add([[x0, y0, z0], [x1, y0, z0], [x1, y1, z0], [x0, y1, z0]], shade(base, 0.6)); // underside
    if (eyeX < x0) add([[x0, y0, z0], [x0, y1, z0], [x0, y1, z1], [x0, y0, z1]], shade(base, 0.75)); // left side
    if (eyeX > x1) add([[x1, y0, z0], [x1, y1, z0], [x1, y1, z1], [x1, y0, z1]], shade(base, 0.75)); // right side
    return out.sort((a, b) => b.depth - a.depth);
  };
  const WOOD = '#d9d1c3';
  const board = (l: number) => cuboid(0, width, 0, SHELF.d, l * SHELF.gap, l * SHELF.gap + SHELF.board, WOOD);
  const boxesOn = (l: number) =>
    placed
      .filter((p) => p.level === l)
      .flatMap((p) => cuboid(p.x0, p.x0 + A4.w, 1, 1 + A4.d, p.z, p.z + p.h, p.b.fill, { key: p.b.key, detail: p.b.detail, stroke: shade(p.b.fill, 0.6) }))
      .sort((a, b) => b.depth - a.depth);
  // Order by shelf, so no box crosses a shelf. Below eye level a shelf is seen from above and covers the
  // boxes beneath it: draw bottom-up, board then its boxes. Above eye level a shelf is seen from below and
  // covers the boxes standing on it: draw top-down, the board over a level, its boxes, then the board under.
  const below = Array.from({ length: SHELF.levels }, (_, l) => l).filter((l) => (l + 1) * SHELF.gap <= EYE.z);
  const above = Array.from({ length: SHELF.levels }, (_, l) => l).filter((l) => (l + 1) * SHELF.gap > EYE.z);
  const faces: Face[] = [];
  for (const l of below) faces.push(...board(l), ...boxesOn(l));
  for (const l of [...above].reverse()) faces.push(...board(l + 1), ...boxesOn(l));
  faces.push(...board(above.length ? above[0] : SHELF.levels));
  // The uprights: back posts behind everything, front posts in front of everything.
  const post = (x: number, y: number): V3[] => [[x - 1.5, y, 0], [x + 1.5, y, 0], [x + 1.5, y, shelfH + SHELF.board], [x - 1.5, y, shelfH + SHELF.board]];
  const backPosts = Array.from({ length: bays + 1 }, (_, k) => post(k * SHELF.w, SHELF.d));
  const frontPosts = Array.from({ length: bays + 1 }, (_, k) => post(k * SHELF.w, 0));
  // Frame: the back wall and the floor.
  const wall: V3[] = [[-40, SHELF.d + 2, 0], [width + 40, SHELF.d + 2, 0], [width + 40, SHELF.d + 2, 210], [-40, SHELF.d + 2, 210]];
  const floor: V3[] = [[-40, -60, 0], [width + 40, -60, 0], [width + 40, SHELF.d + 2, 0], [-40, SHELF.d + 2, 0]];
  const all = [...wall, ...floor, ...faces.flatMap((f) => f.pts)].map(proj);
  const minX = Math.min(...all.map((q) => q[0])) - 6;
  const minY = Math.min(...all.map((q) => q[1])) - 18;
  const W = Math.max(...all.map((q) => q[0])) - minX + 6;
  const H = Math.max(...all.map((q) => q[1])) - minY + 6;
  const pts = (q: V3[]) => q.map((v) => proj(v)).map(([a, b]) => `${(a - minX).toFixed(1)},${(b - minY).toFixed(1)}`).join(' ');
  return (
    <figure className="w-full max-w-[560px]">
      {title && <figcaption className="text-[12.5px] font-semibold text-ink-800">{title}</figcaption>}
      <svg viewBox={`0 0 ${W.toFixed(0)} ${H.toFixed(0)}`} className="mt-1 w-full rounded-[var(--radius-card)] border border-ink-200 bg-white" role="img" aria-label={title || sets.map((x) => x.label).join(', ')} onMouseLeave={() => onSel(null)}>
        <polygon points={pts(floor)} fill="#f2eee6" />
        <polygon points={pts(wall)} fill="#faf8f4" stroke="#e4dfd5" />
        {backPosts.map((q, k) => <polygon key={'bp' + k} points={pts(q)} fill="#b9b0a2" />)}
        {faces.map((f, n) => {
          const on = !f.key || sel === null || sel === f.key;
          return (
            <polygon
              key={n}
              points={pts(f.pts)}
              fill={f.fill}
              stroke={f.stroke ?? '#b3aa9c'}
              strokeWidth={0.4}
              opacity={on ? 1 : 0.3}
              onMouseEnter={f.key ? () => onSel(f.key!) : undefined}
              style={f.key ? { cursor: 'pointer' } : undefined}
            >
              {f.detail && <title>{f.detail}</title>}
            </polygon>
          );
        })}
        {frontPosts.map((q, k) => <polygon key={'fp' + k} points={pts(q)} fill="#8f8678" />)}
        {sets.map((set, k) => {
          const [lx, ly] = proj([k * SHELF.w + SHELF.w / 2, 0, shelfH + 14]);
          return (
            <text key={'lab' + k} x={lx - minX} y={ly - minY} textAnchor="middle" style={{ fontSize: 11, fontWeight: 600, fill: 'var(--color-ink-700)' }}>
              {set.label}
            </text>
          );
        })}
      </svg>
    </figure>
  );
}

function Boxes() {
  const [sel, setSel] = useState<string | null>(null);
  const fmt = (n: number) => n.toLocaleString('en-US');
  const mtpTotal = MTP_BOXES.reduce((a, b) => a + b.pages, 0);
  const bnfTotal = BNF_BOXES.reduce((a, b) => a + b.leaves, 0);
  const CARD = '#b89b72';
  // Bourbaki collections in which no document names Grothendieck.
  const PLAIN = '#cfd3dc';
  const bnfFill = (b: BnfBox) => (b.maths === 'whole' ? DARK : b.maths === 'part' ? LIGHT : CARD);
  const mtp: RoomBox[] = MTP_BOXES.map((b) => ({ key: 'm:' + b.id, label: b.title, sheets: b.pages, fill: DARK, detail: `${b.title}: ${b.folders} folder${b.folders > 1 ? 's' : ''}, ${fmt(b.pages)} pages, a stack of about ${Math.round(b.pages * SHEET_CM)} cm` }));
  const bnf: RoomBox[] = BNF_BOXES.map((b) => ({ key: 'b:' + b.box, label: `(${b.box}) ${b.title}`, sheets: b.leaves, fill: bnfFill(b), detail: `NAF 29093 (${b.box}), ${b.title}${b.years ? `, ${b.years}` : ''}: ${fmt(b.leaves)} leaves, a stack of about ${Math.round(b.leaves * SHEET_CM)} cm` }));
  // The Bourbaki archive by source collection, cut into boxes of at most 3,000 pages (30 cm) so they fit between two shelves.
  const BOX_MAX = 3000;
  const bkTotal = BOURBAKI_FONDS.reduce((a, f) => a + f.pages, 0);
  const bk: RoomBox[] = BOURBAKI_FONDS.flatMap((f) => {
    const n = Math.ceil(f.pages / BOX_MAX);
    return Array.from({ length: n }, (_, i) => {
      const pages = i < n - 1 ? BOX_MAX : f.pages - BOX_MAX * (n - 1);
      const names = f.grothendieck ? `, ${f.grothendieck} document${f.grothendieck > 1 ? 's' : ''} naming Grothendieck` : ', no document naming Grothendieck';
      return { key: `k:${f.collection}:${i}`, label: f.collection, sheets: pages, fill: f.grothendieck ? DARK : PLAIN, detail: `Bourbaki, ${f.collection}${n > 1 ? ` (box ${i + 1} of ${n})` : ''}: ${fmt(pages)} pages, a stack of about ${Math.round(pages * SHEET_CM)} cm${names}` };
    });
  });
  const all = [...mtp, ...bnf, ...bk];
  const cur = all.find((b) => b.key === sel);
  return (
    <section className="mt-12">
      <H2 id="boxes">Three archives on the shelves</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        Each box has the footprint of an A4 sheet and is as tall as its stack of paper, at a tenth of a millimetre a sheet; the boxes lie flat on the shelves of a 1 m bay (shelves 37 cm apart, about 1.85 m in all, typical figures rather than the archives' own), stacked tallest first between two shelves, and placed first on the shelves within easy reach, between about 0.75 m and 1.5 m. On
        the left, Montpellier's {GROUPS.length} thematic groups ({COTES.length} folders, {fmt(mtpTotal)} pages by its
        inventory); on the right, the{' '}
        <a href={BNF} target="_blank" rel="noopener noreferrer" className="text-brand-600 hover:text-brand-700">
          BnF
        </a>
        's {BNF_BOXES.length} boxes of later writings, 1987 to 1999 ({fmt(bnfTotal)} leaves by its notices). All the bays
        are drawn to the same scale. Montpellier counts pages and the BnF counts leaves, and a leaf written on both sides
        is two pages, so a Montpellier stack may be up to twice too tall. Montpellier is mathematics throughout; at the
        BnF only box (3) is a mathematical text, and boxes (40), (42) and (43) hold some mathematics among other notes.
        For comparison, the third bay holds the{' '}
        <a href="https://archives-bourbaki.ahp-numerique.fr" target="_blank" rel="noopener noreferrer" className="text-brand-600 hover:text-brand-700">
          Bourbaki archive
        </a>{' '}
        put online by the Archives Henri Poincaré: {fmt(bkTotal)} pages of drafts, reports and circulars from{' '}
        {BOURBAKI_FONDS.length} source collections, the larger ones cut into boxes of at most 3,000 pages; only the {BOURBAKI_FONDS.filter((f) => f.grothendieck).length} collections with a document that names Grothendieck are in blue.
      </p>
      <div className="mt-3 flex flex-wrap gap-x-5 gap-y-1 text-[12px] text-ink-600">
        {[
          [DARK, 'Mathematics'],
          [LIGHT, 'Partly mathematics (BnF)'],
          [CARD, 'Other writings (BnF)'],
          [PLAIN, 'Bourbaki, Grothendieck not named'],
        ].map(([c, l]) => (
          <span key={l} className="inline-flex items-center gap-1.5">
            <svg width="12" height="10" aria-hidden="true">
              <rect x="0" y="1" width="12" height="8" rx="1.5" fill={c} />
            </svg>
            {l}
          </span>
        ))}
      </div>
      <div className="mt-3 flex flex-wrap gap-8">
        <Room
          title=""
          sets={[
            { label: `Montpellier · ${GROUPS.length} groups`, boxes: mtp },
            { label: `BnF · ${BNF_BOXES.length} boxes`, boxes: bnf },
            { label: `Bourbaki · ${BOURBAKI_FONDS.length} collections`, boxes: bk },
          ]}
          sel={sel}
          onSel={setSel}
        />
      </div>
      <p className="mt-2 min-h-[1.5em] text-[12.5px] text-ink-600">
        {cur ? cur.detail : <span className="text-ink-400">Hover a box for the group or box, and the height of its stack.</span>}
      </p>
    </section>
  );
}

/* ---------- figure: statements of the notes found in print ---------- */

type RediscoveryGroup = 'later' | 'concurrent' | 'own' | 'earlier' | 'unclear';
const RD_GROUPS: { key: RediscoveryGroup; label: string; color: string; shape: 'circle' | 'square' | 'diamond' | 'ring' }[] = [
  { key: 'later', label: 'Printed after the folder’s dating', color: '#38539d', shape: 'circle' },
  { key: 'concurrent', label: 'Printed within the folder’s dating', color: 'var(--color-ink-500)', shape: 'circle' },
  { key: 'own', label: 'His own printed work, or his circle’s', color: '#128557', shape: 'diamond' },
  { key: 'earlier', label: 'Printed before the folder’s dating', color: '#eb6834', shape: 'square' },
  { key: 'unclear', label: 'A textbook statement, no single source', color: 'var(--color-ink-400)', shape: 'ring' },
];
const rdGroup = (r: Rediscovery): RediscoveryGroup => (r.kind === 'circle' ? 'own' : r.kind);

function RdMark({ shape, color, x, y, r = 3.4 }: { shape: string; color: string; x: number; y: number; r?: number }) {
  if (shape === 'square') return <rect x={x - r} y={y - r} width={2 * r} height={2 * r} fill={color} />;
  if (shape === 'diamond') return <rect x={x - r} y={y - r} width={2 * r} height={2 * r} fill={color} transform={`rotate(45 ${x} ${y})`} />;
  if (shape === 'ring') return <circle cx={x} cy={y} r={r - 0.6} fill="#fff" stroke={color} strokeWidth={1.4} />;
  return <circle cx={x} cy={y} r={r} fill={color} />;
}

function Rediscoveries() {
  const [sel, setSel] = useState<Rediscovery | null>(null);
  const W = 900;
  const L = 74;
  const R = 16;
  const Y0 = 1950;
  const Y1 = 2026;
  const ROW = 9;
  const HEAD = 18;
  const x = (y: number) => L + ((Math.max(Y0, Math.min(Y1, y)) - Y0) / (Y1 - Y0)) * (W - L - R);
  const lag = (r: Rediscovery) => (r.pub > r.to ? r.pub - r.to : r.pub < r.from ? r.pub - r.from : 0);
  const groups = RD_GROUPS.map((g) => ({
    ...g,
    rows: REDISCOVERIES.filter((r) => rdGroup(r) === g.key).sort((a, b) => lag(b) - lag(a) || a.from - b.from),
  }));
  let yy = 26;
  const layout = groups.map((g) => {
    const top = yy;
    yy += HEAD + g.rows.length * ROW + 6;
    return { ...g, top };
  });
  const H = yy + 4;
  const ticks = [1950, 1960, 1970, 1980, 1990, 2000, 2010, 2020];
  const count = (k: RediscoveryGroup) => REDISCOVERIES.filter((r) => rdGroup(r) === k).length;
  return (
    <section className="mt-12">
      <H2 id="found-in-print">Statements of the notes found in print</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        The {REDISCOVERIES.length} mathematical findings that the edition later found in the literature. Each row sets the
        folder’s dating, as a grey bar, against the year of the printed source that matches it. {count('later')} were printed
        after the end of the folder’s dating, often decades later; {count('earlier')} before it, results he redid in his own
        notation without citing them; {count('own')} are his own printed work or his students’ and colleagues’; {count('concurrent')}{' '}
        appeared within the dating. The datings are the inventory’s, often inferred, so none of this is a claim of priority.
        Sources before 1950 are pinned to the left edge. Hover a row for the folder and the source.
      </p>
      <div className="mt-3 flex flex-wrap gap-x-5 gap-y-1 text-[12px] text-ink-600">
        {RD_GROUPS.map((g) => (
          <span key={g.key} className="inline-flex items-center gap-1.5">
            <svg width="12" height="12" aria-hidden="true">
              <RdMark shape={g.shape} color={g.color} x={6} y={6} />
            </svg>
            {g.label} ({count(g.key)})
          </span>
        ))}
        <span className="inline-flex items-center gap-1.5">
          <svg width="18" height="8" aria-hidden="true">
            <rect x="1" y="2" width="16" height="4" fill="var(--color-ink-200)" />
          </svg>
          Folder’s dating (inventory)
        </span>
      </div>
      <div className="mt-3 overflow-x-auto" onMouseLeave={() => setSel(null)}>
        <svg
          viewBox={`0 0 ${W} ${H}`}
          className="w-full min-w-[640px] rounded-[var(--radius-card)] border border-ink-200 bg-white"
          role="img"
          aria-label="For each statement of the notes found in print, the folder's dating and the year of the matching source"
        >
          {ticks.map((t) => (
            <g key={t}>
              <line x1={x(t)} x2={x(t)} y1={18} y2={H - 4} stroke="var(--color-ink-100)" strokeWidth={1} />
              <text x={x(t)} y={13} textAnchor="middle" className="tabular" style={{ fontSize: 10, fill: 'var(--color-ink-500)' }}>
                {t}
              </text>
            </g>
          ))}
          {layout.map((g) => (
            <g key={g.key}>
              <text x={8} y={g.top + 12} style={{ fontSize: 10.5, fontWeight: 600, fill: 'var(--color-ink-700)' }}>
                {g.label}
              </text>
              {g.rows.map((r, i) => {
                const y = g.top + HEAD + i * ROW + ROW / 2;
                const on = sel === null || sel === r;
                const x0 = x(r.from);
                const x1 = Math.max(x(r.to), x0 + 2);
                const xp = x(r.pub);
                return (
                  <g key={r.id} opacity={on ? 1 : 0.3} onMouseEnter={() => setSel(r)} style={{ cursor: 'pointer' }}>
                    <rect x={0} y={y - ROW / 2} width={W} height={ROW} fill="transparent" />
                    <text x={L - 8} y={y + 3} textAnchor="end" className="tabular" style={{ fontSize: 8.5, fill: 'var(--color-ink-500)' }}>
                      {r.cote}
                    </text>
                    <line x1={Math.min(xp, x0)} x2={Math.max(xp, x1)} y1={y} y2={y} stroke={g.color} strokeWidth={0.8} opacity={0.5} />
                    <rect x={x0} y={y - 2} width={x1 - x0} height={4} fill={r.open ? 'var(--color-ink-100)' : 'var(--color-ink-200)'} />
                    {r.pub < Y0 && (
                      <text x={xp + 6} y={y + 3} style={{ fontSize: 8, fill: 'var(--color-ink-500)' }}>
                        {r.pub}
                      </text>
                    )}
                    <RdMark shape={g.shape} color={g.color} x={xp} y={y} />
                  </g>
                );
              })}
            </g>
          ))}
        </svg>
      </div>
      <p className="mt-2 min-h-[2.5em] text-[12.5px] leading-relaxed text-ink-600">
        {sel ? (
          <>
            <span className="font-semibold text-ink-900">Folder {sel.cote}</span>, dated {sel.from}
            {sel.to !== sel.from ? `–${sel.to}` : ''}
            {sel.open ? ' (lower bound only)' : ''} · <span className="text-ink-800">{sel.source}</span> ({sel.pub}) ·{' '}
            <a href={`/findings/#${sel.id}`} className="text-brand-700 hover:underline">
              the finding
            </a>
          </>
        ) : (
          <span className="text-ink-400">Hover a row for the folder, its dating and the printed source.</span>
        )}
      </p>
      <details className="mt-2 text-[12.5px] text-ink-600">
        <summary className="cursor-pointer text-ink-500 hover:text-brand-700">The rows as a table</summary>
        <table className="mt-2 w-full max-w-[56em] border-collapse">
          <thead>
            <tr className="text-left text-ink-500">
              <th className="py-1 pr-3 font-semibold">Folder</th>
              <th className="py-1 pr-3 font-semibold">Dating</th>
              <th className="py-1 pr-3 font-semibold">Source</th>
              <th className="py-1 pr-3 text-right font-semibold">Year</th>
              <th className="py-1 font-semibold">Relation</th>
            </tr>
          </thead>
          <tbody>
            {groups.flatMap((g) =>
              g.rows.map((r) => (
                <tr key={r.id} className="border-t border-ink-100">
                  <td className="tabular py-1 pr-3">
                    <a href={`/findings/#${r.id}`} className="hover:text-brand-700">
                      {r.cote}
                    </a>
                  </td>
                  <td className="tabular py-1 pr-3">
                    {r.from}
                    {r.to !== r.from ? `–${r.to}` : ''}
                    {r.open ? '+' : ''}
                  </td>
                  <td className="py-1 pr-3 text-ink-800">{r.source}</td>
                  <td className="tabular py-1 pr-3 text-right">{r.pub}</td>
                  <td className="py-1 text-ink-500">{g.label}</td>
                </tr>
              )),
            )}
          </tbody>
        </table>
      </details>
    </section>
  );
}

/* ---------- figure 1: the ranges and the dots ---------- */

/**
 * A proposed dating, as a thin bar under the folder's own: solid for high
 * confidence, faded for medium, outlined for low; an end with no bound fades
 * out over a few years. A distinct colour, so it never reads as the inventory's.
 */
function ProposalMark({ p, x, y }: { p: Proposal; x: (year: number) => number; y: number }) {
  const h = 3;
  const s = span(p);
  const from = p.from ? startOf(p.from) : null;
  const to = p.to ? endOf(p.to) : null;
  // The bounded part: the whole interval, or a short stub at the one end given.
  const b0 = from ?? (to as number);
  const b1 = to ?? b0;
  const bx = from === null ? x(b1) - 3 : x(b0);
  const bw = from !== null && to !== null ? Math.max(3, x(b1) - x(b0)) : 3;
  const style =
    p.confidence === 'high'
      ? { fill: PROP }
      : p.confidence === 'medium'
        ? { fill: PROP, fillOpacity: 0.5 }
        : { fill: '#fff', stroke: PROP, strokeWidth: 0.9 };
  const fade = p.confidence === 'high' ? 1 : p.confidence === 'medium' ? 0.5 : 0.35;
  return (
    <g>
      {to === null && <rect x={x(b1)} y={y} width={x(s.to) - x(b1)} height={h} fill="url(#prop-fade)" opacity={fade} />}
      {from === null && <rect x={x(s.from)} y={y} width={x(b0) - x(s.from)} height={h} fill="url(#prop-fade-in)" opacity={fade} />}
      <rect x={bx} y={y} width={bw} height={h} rx={1} {...style} />
    </g>
  );
}

function Ranges() {
  const [sel, setSel] = useState<Row | null>(null);
  const W = 900;
  const L = 16;
  const R = 16;
  const TOP = 26;
  // A lane holds the folder's bar and, under it, room for a proposed dating.
  const BAR = 7;
  const ROW = 13;
  const H = TOP + LANES * ROW + 24;
  const x = (y: number) => L + ((y - Y0) / (Y1 - Y0)) * (W - L - R);
  const decades = [1950, 1955, 1960, 1965, 1970, 1975, 1980, 1985, 1990];

  return (
    <section className="mt-10">
      <H2 id="ranges">Every dated folder: the inventory's range, and the dates on the leaves</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        One bar per folder, placed by where its dating starts; folders that do not overlap share
        a row. A dark bar is a dating the archivists read on the pages, a light one a dating they
        deduced (their square brackets). A bar that fades is open-ended, as in « à partir de
        1982 », from 1982 with no end given. The dots are dates written on the leaves themselves,
        found by the transcriptions. A hollow dot is a stamp printed on the paper, most often the
        banner of a computer listing whose back he wrote on; it dates the paper, not the writing.
        Folders not yet begun are drawn fainter, since they can have no dots. The thin green bar
        under some folders is the project's own proposed dating, argued from those leaves. It is
        drawn beside the inventory's dating and never replaces it.
      </p>
      <ul className="mt-3 flex flex-wrap items-center gap-x-5 gap-y-1 text-[12px] text-ink-500">
        <li className="flex items-center gap-1.5">
          <span className="inline-block h-2 w-5 rounded-sm" style={{ background: DARK }} /> dating read on the pages
        </li>
        <li className="flex items-center gap-1.5">
          <span className="inline-block h-2 w-5 rounded-sm" style={{ background: LIGHT }} /> dating deduced [in brackets]
        </li>
        <li className="flex items-center gap-1.5">
          <span className="inline-block h-2 w-5 rounded-sm" style={{ background: `linear-gradient(90deg, ${LIGHT}, transparent)` }} /> open-ended
        </li>
        <li className="flex items-center gap-1.5">
          <span className="inline-block h-2.5 w-2.5 rounded-full" style={{ background: DOT }} /> a date written on a leaf
        </li>
        <li className="flex items-center gap-1.5">
          <span className="inline-block h-2.5 w-2.5 rounded-full border-[1.5px] bg-white" style={{ borderColor: DOT }} /> a machine stamp on the paper (the leaf is no older)
        </li>
        <li className="flex items-center gap-1.5">
          <span className="inline-flex gap-0.5">
            <span className="inline-block h-[3px] w-3 rounded-sm" style={{ background: PROP }} />
            <span className="inline-block h-[3px] w-3 rounded-sm" style={{ background: PROP, opacity: 0.5 }} />
            <span className="inline-block h-[3px] w-3 rounded-sm border-[0.9px] bg-white" style={{ borderColor: PROP }} />
          </span>{' '}
          proposed dating (project): high, medium, low confidence
        </li>
      </ul>
      <div className="mt-3 overflow-x-auto" onMouseLeave={() => setSel(null)}>
        <svg
          viewBox={`0 0 ${W} ${H}`}
          className="w-full min-w-[640px] rounded-[var(--radius-card)] border border-ink-200 bg-white"
          role="img"
          aria-label="Each folder's inventory dating as a range, with dates written on its leaves as dots"
        >
          <defs>
            <linearGradient id="fade" x1="0" x2="1">
              <stop offset="0" stopColor={LIGHT} />
              <stop offset="1" stopColor={LIGHT} stopOpacity="0" />
            </linearGradient>
            <linearGradient id="fade-in" x1="0" x2="1">
              <stop offset="0" stopColor={LIGHT} stopOpacity="0" />
              <stop offset="1" stopColor={LIGHT} />
            </linearGradient>
            <linearGradient id="prop-fade" x1="0" x2="1">
              <stop offset="0" stopColor={PROP} />
              <stop offset="1" stopColor={PROP} stopOpacity="0" />
            </linearGradient>
            <linearGradient id="prop-fade-in" x1="0" x2="1">
              <stop offset="0" stopColor={PROP} stopOpacity="0" />
              <stop offset="1" stopColor={PROP} />
            </linearGradient>
          </defs>
          {decades.map((d) => (
            <g key={d}>
              <line x1={x(d)} x2={x(d)} y1={TOP - 6} y2={H - 20} stroke="var(--color-ink-200)" />
              <text x={x(d)} y={TOP - 12} textAnchor="middle" className="tabular" style={{ fontSize: 11, fill: 'var(--color-ink-400)' }}>
                {d}
              </text>
            </g>
          ))}
          {LIFE.map((e) => (
            <line key={e.year} x1={x(e.year + 0.5)} x2={x(e.year + 0.5)} y1={H - 18} y2={H - 8} stroke="var(--color-ink-500)" strokeWidth="1.5">
              <title>{`${e.year}: ${e.what}`}</title>
            </line>
          ))}
          {ROWS.map((r, i) => {
            const y = TOP + LANE[i] * ROW;
            const on = sel === null || sel === r;
            const fill = r.read ? DARK : LIGHT;
            return (
              <g
                key={r.id}
                opacity={on ? (BEGUN.has(r.id) ? 1 : 0.45) : 0.15}
                onMouseEnter={() => setSel(r)}
                style={{ cursor: 'pointer' }}
              >
                <rect x={x(r.from)} y={y} width={x(r.open ? r.to + 5 : r.to) - x(r.from)} height={ROW} fill="#fff" fillOpacity={0} />
                {r.openStart && <rect x={x(r.from)} y={y + 1} width={x(r.from + 4) - x(r.from)} height={BAR} fill="url(#fade-in)" />}
                <rect
                  x={x(r.openStart ? r.from + 4 : r.from)}
                  y={y + 1}
                  width={Math.max(3, x(r.to) - x(r.openStart ? r.from + 4 : r.from))}
                  height={BAR}
                  rx={1.5}
                  fill={fill}
                />
                {r.open && <rect x={x(r.to)} y={y + 1} width={x(r.to + 5) - x(r.to)} height={BAR} fill="url(#fade)" />}
                {r.proposal && <ProposalMark p={r.proposal} x={x} y={y + BAR + 2} />}
                {r.leaves.map((l, j) =>
                  isStamp(l) ? (
                    <circle key={j} cx={x(frac(l.iso as string))} cy={y + 1 + BAR / 2} r={3} fill="#fff" stroke={DOT} strokeWidth="1.6" />
                  ) : (
                    <circle key={j} cx={x(frac(l.iso as string))} cy={y + 1 + BAR / 2} r={3.4} fill={DOT} stroke="#fff" strokeWidth="1" />
                  ),
                )}
              </g>
            );
          })}
        </svg>
      </div>
      <div className="mt-2 min-h-[6em] text-[12.5px] leading-relaxed text-ink-600">
        {sel ? (
          <>
            <p>
              <a href={`/#${sel.id}/1`} className="tabular font-semibold text-ink-900 hover:text-brand-700">
                n° {sel.id}
              </a>{' '}
              {shortTitle(sel.title)} <span className="text-ink-500">· inventory: « {sel.dating.raw} »</span>
              {!BEGUN.has(sel.id) && <span className="text-ink-400"> · not yet transcribed</span>}
            </p>
            {sel.leaves.length > 0 ? (
              <p className="text-ink-500">
                On the leaves:{' '}
                {sel.leaves.slice(0, 12).map((l, i) => (
                  <span key={i}>
                    {i > 0 && '; '}« {l.written} » <span className="text-ink-400">(p. {l.page})</span>
                  </span>
                ))}
                {sel.leaves.length > 12 && `; and ${sel.leaves.length - 12} more`}
              </p>
            ) : (
              <p className="text-ink-400">No date found written on its leaves{BEGUN.has(sel.id) ? ' so far' : ''}.</p>
            )}
            {sel.proposal && (
              <p className="text-ink-500">
                <span className="font-semibold" style={{ color: PROP }}>
                  Proposed dating (project):
                </span>{' '}
                <span className="tabular text-ink-900">{interval(sel.proposal)}</span> · {sel.proposal.confidence} confidence.{' '}
                {sel.proposal.summary} <span className="text-ink-400">Shown beside the inventory's dating, not in its place.</span>
              </p>
            )}
          </>
        ) : (
          <p className="text-ink-400">
            Hover a bar for the folder, its dating as the inventory writes it, and the dates on its
            leaves. The ticks along the foot are the events listed below. {UNDATED.length} folders are
            « s.d. », undated, and are not drawn.
          </p>
        )}
      </div>
      <Proposals />
    </section>
  );
}

/** Every proposed dating beside the inventory's, each piece of evidence with the line it rests on. */
const SITE = 'https://grothendieck.commutator.io';
const proposalCtx = (p: Proposal): CommentContext => ({
  kind: 'dating',
  label: `n° ${p.folder}: ${interval(p)} (${p.confidence} confidence)`,
  cote: p.folder,
  ref: p.folder,
  details: [
    `**Inventory** « ${p.inventory} »`,
    `**Proposed** ${interval(p)}, ${p.confidence} confidence`,
    ...p.evidence.map((e) => `- ${e.kind}: ${e.text} (${e.where})`),
  ],
  link: `${SITE}/timeline/#dating-${p.folder}`,
});
const leafCtx = (l: Leaf): CommentContext => ({
  kind: 'leaf',
  label: `n° ${l.folder}, p. ${l.page}: « ${l.written} »`,
  cote: l.folder,
  batch: l.batch,
  page: Number.parseInt(l.page, 10) || undefined,
  ref: `${l.folder}/p${l.page}`,
  details: [`**Written** « ${l.written} »${l.iso ? ` → ${l.iso}` : ''}`, `**Kind** ${l.kind}, ${l.context}`, `**Source** ${l.where}`],
  link: `${SITE}/#${l.folder}/${l.batch}/p${l.page}`,
});

function Proposals() {
  const drawn = new Set(ROWS.map((r) => r.id));
  const list = [...PROPOSALS].sort((a, b) => byShelfmark(a.folder, b.folder));
  return (
    <details className="mt-3 text-[12.5px] text-ink-600">
      <summary className="cursor-pointer text-ink-500">
        All {list.length} proposed datings, each beside the inventory's, with its evidence
      </summary>
      <ul className="mt-2 space-y-2">
        {list.map((p) => (
          <li key={p.folder} id={`dating-${p.folder}`} className="scroll-mt-16" {...commentData(proposalCtx(p))}>
            <a href={`/#${p.folder}/1`} className="tabular font-semibold text-ink-900 hover:text-brand-700">
              n° {p.folder}
            </a>{' '}
            <span className="text-ink-500">inventory « {p.inventory} »</span> →{' '}
            <span className="tabular" style={{ color: PROP }}>
              {interval(p)}
            </span>{' '}
            <span className="text-ink-400">· {p.confidence} confidence{drawn.has(p.folder) ? '' : ' · not drawn: the inventory gives no dating'}</span>{' '}
            <CommentButton scope="timeline" ctx={proposalCtx(p)} text={p.summary} />
            <p>{p.summary}</p>
            <ul className="pl-4 text-ink-500">
              {p.evidence.map((e, i) => (
                <li key={i}>
                  <span className="font-semibold uppercase tracking-wide text-[10.5px] text-ink-400">{e.kind}</span> {e.text}{' '}
                  <span className="text-ink-400">· {e.where}</span>
                </li>
              ))}
            </ul>
          </li>
        ))}
      </ul>
    </details>
  );
}

/* ---------- figure 2: two strips on one year axis ---------- */

function Strips() {
  const W = 900;
  const L = 130;
  const R = 16;
  const h = 56;
  const years = Array.from({ length: Y1 - Y0 }, (_, i) => Y0 + i);
  const x = (y: number) => L + ((y - Y0) / (Y1 - Y0)) * (W - L - R);
  const bw = (W - L - R) / years.length;
  const covering = years.map((y) => ROWS.filter((r) => r.from <= y && y < (r.open ? r.to + 5 : r.to)).length);
  const leaves = years.map((y) => LEAVES.filter((l) => !isStamp(l) && Math.floor(frac(l.iso as string)) === y).length);
  const strips = [
    { label: 'Folders the inventory dates to the year', data: covering, colour: LIGHT },
    { label: 'Dates written on leaves, stamps left out', data: leaves, colour: DOT },
  ];
  return (
    <section className="mt-12">
      <H2 id="by-year">Year by year</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        Two counts on the same years, each on its own scale: how many folders the inventory's
        ranges cover in a year (an open end counted five years on), and how many dates the
        transcriptions have found written on the leaves of that year.
      </p>
      <div className="mt-3 overflow-x-auto">
        <svg
          viewBox={`0 0 ${W} ${strips.length * (h + 22) + 22}`}
          className="w-full min-w-[640px] rounded-[var(--radius-card)] border border-ink-200 bg-white"
          role="img"
          aria-label="Folders dated to each year, and dates written on leaves per year"
        >
          {strips.map((s, j) => {
            const top = 14 + j * (h + 22);
            const mx = Math.max(1, ...s.data);
            return (
              <g key={s.label}>
                <text x={10} y={top + h / 2} style={{ fontSize: 11, fill: 'var(--color-ink-600)' }}>
                  {s.label.split(' ').slice(0, 3).join(' ')}
                </text>
                <text x={10} y={top + h / 2 + 14} style={{ fontSize: 11, fill: 'var(--color-ink-600)' }}>
                  {s.label.split(' ').slice(3).join(' ')}
                </text>
                <text x={W - R} y={top + 8} textAnchor="end" className="tabular" style={{ fontSize: 10.5, fill: 'var(--color-ink-400)' }}>
                  max {mx}
                </text>
                <line x1={L} x2={W - R} y1={top + h} y2={top + h} stroke="var(--color-ink-200)" />
                {s.data.map((v, i) => (
                  <rect key={i} x={x(years[i]) + 1} y={top + h - (v / mx) * h} width={bw - 2} height={(v / mx) * h} rx={1} fill={s.colour}>
                    <title>{`${years[i]}: ${v}`}</title>
                  </rect>
                ))}
              </g>
            );
          })}
          {[1950, 1960, 1970, 1980, 1990].map((d) => (
            <text key={d} x={x(d) + bw / 2} y={strips.length * (h + 22) + 14} textAnchor="middle" className="tabular" style={{ fontSize: 11, fill: 'var(--color-ink-400)' }}>
              {d}
            </text>
          ))}
        </svg>
      </div>
    </section>
  );
}

/* ---------- figure 3: the days ---------- */

function Calendar() {
  const days = useMemo(() => {
    const m = new Map<string, Leaf[]>();
    for (const l of LEAVES) if (!isStamp(l) && /^\d{4}-\d\d-\d\d$/.test(l.iso as string)) m.set(l.iso as string, [...(m.get(l.iso as string) ?? []), l]);
    return m;
  }, []);
  // A year with a leaf or two dated to the day is a row of empty cells; those
  // are named under the calendar instead, and the register lists them.
  const perYear = new Map<number, number>();
  for (const [d, ls] of days) perYear.set(Number(d.slice(0, 4)), (perYear.get(Number(d.slice(0, 4))) ?? 0) + ls.length);
  const years = [...perYear].filter(([, k]) => k >= 5).map(([y]) => y).sort();
  const sparse = [...perYear].filter(([, k]) => k < 5).sort((a, b) => a[0] - b[0]);
  const [sel, setSel] = useState<string | null>(null);
  if (!years.length) return null;
  const C = 10;
  const max = Math.max(...[...days.values()].map((v) => v.length));
  const shade = (n: number) => (n === 0 ? 'var(--color-ink-100)' : ['#dfe6f6', '#97afe1', '#6b8ad0', '#4a6bbd', '#38539d', '#223154'][Math.min(5, Math.ceil((5 * n) / max))]);

  return (
    <section className="mt-12">
      <H2 id="days">The days he dated</H2>
      <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
        Every year with five leaves or more dated to the day, a week to a column, stamps left out.
        The darker the cell, the more leaves dated that day. Some runs of the late notebooks are
        dated day by day, and the calendar shows the rhythm of that work, which the ranges above
        cannot.
      </p>
      <div className="mt-3 space-y-1.5 overflow-x-auto">
        {years.map((y) => {
          const jan1 = new Date(Date.UTC(y, 0, 1));
          const offset = (jan1.getUTCDay() + 6) % 7; // Monday first
          const n = (Date.UTC(y + 1, 0, 1) - jan1.getTime()) / 864e5;
          const cells = Array.from({ length: n }, (_, i) => {
            const d = new Date(jan1.getTime() + i * 864e5);
            const iso = d.toISOString().slice(0, 10);
            return { iso, col: Math.floor((i + offset) / 7), row: (i + offset) % 7, n: days.get(iso)?.length ?? 0 };
          });
          const total = cells.reduce((a, c) => a + c.n, 0);
          return (
            <div key={y} className="flex items-start gap-3">
              <p className="tabular w-16 shrink-0 pt-1 text-[12px] text-ink-500">
                {y}
                <br />
                <span className="text-ink-400">{total} dated</span>
              </p>
              <svg width={54 * C + 2} height={7 * C + 2} role="img" aria-label={`Leaves dated to the day in ${y}`}>
                {cells.map((c) => (
                  <rect
                    key={c.iso}
                    x={1 + c.col * C}
                    y={1 + c.row * C}
                    width={C - 2}
                    height={C - 2}
                    rx={2}
                    fill={shade(c.n)}
                    stroke={sel === c.iso ? 'var(--color-ink-900)' : 'none'}
                    onMouseEnter={() => c.n && setSel(c.iso)}
                    style={{ cursor: c.n ? 'pointer' : 'default' }}
                  >
                    <title>{`${c.iso}${c.n ? `: ${c.n}` : ''}`}</title>
                  </rect>
                ))}
              </svg>
            </div>
          );
        })}
      </div>
      <div className="mt-2 min-h-[3em] text-[12.5px] leading-relaxed text-ink-600">
        {sel ? (
          <ul>
            {(days.get(sel) ?? []).map((l, i) => (
              <li key={i}>
                <span className="tabular text-ink-900">{sel}</span> ·{' '}
                <a href={`/#${l.folder}/${l.batch}`} className="tabular font-semibold text-ink-900 hover:text-brand-700">
                  n° {l.folder}
                </a>{' '}
                p. {l.page}: « {l.written} », {l.context}
              </li>
            ))}
          </ul>
        ) : (
          <p className="text-ink-400">
            Hover a coloured day for the leaves dated to it. Fewer than five in{' '}
            {sparse.map(([y, k]) => `${y} (${k})`).join(', ')}: they are in the register below.
          </p>
        )}
      </div>
    </section>
  );
}

/* ---------- the register of dated leaves ---------- */

function Register() {
  const byFolder = useMemo(() => {
    const m = new Map<string, Leaf[]>();
    for (const l of LEAVES) m.set(l.folder, [...(m.get(l.folder) ?? []), l]);
    return [...m].sort((a, b) => byShelfmark(a[0], b[0]));
  }, []);
  return (
    <details className="mt-6 text-[12.5px] text-ink-600">
      <summary className="cursor-pointer text-ink-500">
        All {LEAVES.length} dates written on leaves, by folder, each with the line it rests on
      </summary>
      <ul className="mt-2 space-y-2">
        {byFolder.map(([f, ls]) => (
          <li key={f}>
            <span className="tabular font-semibold text-ink-900">n° {f}</span>
            <ul className="pl-4">
              {ls.map((l, i) => (
                <li key={i} {...commentData(leafCtx(l))}>
                  <a href={`/#${l.folder}/${l.batch}`} className="tabular hover:text-brand-700">
                    p. {l.page}
                  </a>{' '}
                  « {l.written} » <span className="text-ink-400">· {l.kind}, {l.context} · {l.where}</span>{' '}
                  <CommentButton scope="timeline" ctx={leafCtx(l)} text={`« ${l.written} », ${l.context}`} />
                </li>
              ))}
            </ul>
          </li>
        ))}
      </ul>
    </details>
  );
}

export function TimelinePage() {
  const commentRoot = useComments<HTMLElement>('timeline', 'Timeline');
  const inferred = ROWS.filter((r) => !r.read).length;
  const foldersWithLeaves = new Set(LEAVES.map((l) => l.folder)).size;
  return (
    <>
      <Header path="/timeline/" />

      <main ref={commentRoot} className="mx-auto max-w-5xl px-5 py-12">
        <header className="max-w-[44em]">
          <p className="text-[11px] font-bold uppercase tracking-[0.14em] text-ink-400">Timeline</p>
          <h1 className="titre mt-2 text-[30px] leading-tight text-ink-900">
            When the folders were written, and how anyone knows
          </h1>
          <p className="mt-4 text-[15.5px] leading-relaxed text-ink-600">
            Almost nothing in the fonds is dated. The inventory proposes a dating for most folders,
            but of the {ROWS.length} it dates, {inferred} rest at least in part on the archivists'
            deduction from a verso, a letter or a neighbouring folder, and {UNDATED.length} more
            carry no dating at all. The transcriptions have so far found {LEAVES.length} dates on
            the leaves themselves, in {foldersWithLeaves} folders; {LEAVES.filter(isStamp).length} of
            them are machine stamps on reused paper, which date the paper rather than the writing.
            The figures below keep each kind of date apart.
          </p>
        </header>

        <Ranges />
        <Works />
        <Volumes />
        <Boxes />
        <Rediscoveries />
        <Strips />
        <Calendar />
        <Register />

        <section className="mt-12">
          <H2 id="life">The life, where it is sourced</H2>
          <p className="mt-2 max-w-[44em] text-[13.5px] leading-relaxed text-ink-600">
            Events a reference work states, given as landmarks for the ranges above; this is not a
            biography.
          </p>
          <ul className="mt-3 space-y-1.5 text-[13px] text-ink-700">
            {LIFE.map((e) => (
              <li key={e.year} className="flex gap-3">
                <span className="tabular w-10 shrink-0 font-semibold text-ink-900">{e.year}</span>
                <span>
                  {e.what}{' '}
                  <a href={e.source} target="_blank" rel="noopener noreferrer" className="text-[12px] text-brand-600 hover:text-brand-700">
                    {e.source === MACTUTOR ? 'MacTutor' : 'the fonds'} ↗
                  </a>
                </span>
              </li>
            ))}
          </ul>
        </section>

        <p className="mt-12 max-w-[44em] text-[12px] leading-relaxed text-ink-400">
          The ranges are read from the inventory's datings as src/content/catalogue.ts carries them,
          brackets included. The dates on the leaves are src/content/dated-leaves.json, each with
          the file and line of the transcription that records it. The proposed datings are
          src/content/proposed-datings.json: the project's reading of that evidence, kept beside
          the inventory's datings and never substituted for them.
        </p>
      </main>

      <Footer />
    </>
  );
}
