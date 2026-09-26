/**
 * Statements of the modernised readings proved in Lean (lean/, issue #26).
 *
 * One entry per proof file. Written by hand when a proof lands, alongside its
 * section of docs/lean/article.tex, which gives the same statement with its
 * proof written out. The notation is the findings' hybrid (Unicode operators,
 * TeX indices), rendered by lib/notation.tsx.
 */
export interface Proof {
  folder: string;
  /** Where the reading's statement is, as the reader addresses it. */
  batch: number;
  page: string;
  /** The reading's name for it. */
  name: string;
  statement: string;
  /** What the formalisation turned up — the point of doing it. */
  found: string;
  /** The verdict in one word, for the badge. */
  verdict: 'holds' | 'holds, more generally' | 'needs a hypothesis' | 'false as stated' | 'already in mathlib';
  lean: string;
  theorems: string[];
}

export const PROOFS: Proof[] = [
  {
    folder: '42',
    batch: 1,
    page: '4',
    name: 'Lemme 2',
    statement:
      'Let A be a Noetherian ring and 𝔭 a prime ideal. (1) Some f ∉ 𝔭 makes A_f → A_𝔭 injective. (2) If moreover A → A_𝔭 is injective, then A_𝔮 → A_𝔭 is injective for every prime 𝔮 ⊇ 𝔭.',
    found:
      'Both parts hold as the reading states them; no hypothesis is missing. Part (2) does not need the Noetherian hypothesis: it holds over any commutative ring. Part (1) uses it only to make the kernel of A → A_𝔭 finitely generated, and needs that kernel described exactly — the elements killed by some element outside 𝔭 — which is the correction the reading’s footnote makes to the page’s « l’annulateur de A − 𝔭 ».',
    verdict: 'holds, more generally',
    lean: 'lean/Grothendieck/Folder42.lean',
    theorems: ['lemme2_1', 'lemme2_2'],
  },
];
