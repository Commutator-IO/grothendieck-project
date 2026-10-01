/**
 * Folders with a statement proved in the Lean appendix that bears on one of the
 * numbered theorems of the Timeline (the « Theorems » row), as the appendix's
 * blue lozenges mark them. The link is of subject, not of proof: none of these
 * statements is itself one of the theorems.
 */
export const THEOREM_LINKS: Record<string, number[]> = {
  '19': [4], // pp. 14–15, a Grothendieck category with a generator: Tôhoku
  '21': [4], // proposition 2.15, Baer's criterion cited as « Tohoku »
  '125': [6, 9], // leaf 2: local cohomology, formal completion, duality; SGA 2
};
