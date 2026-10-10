/**
 * The open findings the mosaic marks with a red lozenge.
 *
 * Not every open finding: only those whose statement is of the weight of his
 * main theorems, or a conjecture he stated and did not prove — the standard
 * conjectures and their variants, weights and levels, p-adic cohomology,
 * étale duality, the Galois action on Teichmüller and anabelian statements.
 * Chosen by hand from FINDINGS; a finding marked here is still only a
 * candidate, and its status is read from FINDINGS at render time.
 */
export const MAJOR_FINDINGS = new Set<string>([
  '16-algebraic-iso-suffices',
  '16-weak-variants-imply-strong',
  '36-griffiths-conditional-l-adic',
  '4-vanishing-unit-root-bound',
  '7-noninfinitesimal-site',
  '5-deligne-letter-ringed-duality',
  '12-immersion-level-bound',
  '18-archimedean-lattice-cocycle',
  '31-imperfection-bound-conjectures',
  '29-formal-tame-pi1-self-intersection',
  '142-galois-image-conditions-single-curve',
  '142-teichmuller-galois-category-etale',
  '149-dominant-faithfulness-curves',
]);
