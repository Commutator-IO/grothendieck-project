# Folder 147, pp. 62–64: the stratified class of M₁,₁ over ℤ

Check for issue #91 (« Calculatoires »), appendix row « D'après les pages 62 à 64, forme
complétée par l'édition, classe stratifiée de $M_{1,1}$ sur $\mathbf Z$ »
(`docs/lean/sections/autres/topologie-combinatoire-surfaces-et-carte.tex`, `\nonverifie`
example `147-m11-stratified-class-over-z`; formulas (79), (80) of `transcripts/147/147.modern.tex`).
It is not in Lean and not settled.

## What is tested

The invariant reconstructed by the reading counts each locally closed piece with constant
geometric automorphism group H as [coarse space]/card H. Its F_q-realisation sends L ↦ q and
ζ_p ↦ 1 if char F_q = p, otherwise 0. On M₁,₁ it gives

  N(q) = Σ_{j ∈ F_q} 1 / card Aut_{F̄_q}(E_j).

The script computes N(q) from scratch and compares it with the page's formulas:
- for each j ∈ F_q it searches the Weierstrass equations over F_q for one with that j
  (and checks that every j occurs);
- it counts that curve's automorphisms by enumerating all changes of variables (u, r, s, t)
  over K = F_{q²} that fix the five coefficients, using Silverman III.1 in any characteristic.
  For q = 2 and 3 it repeats the count over F_{q⁴}, to show that F_{q²} already gives all of them;
- it sums 1/card Aut with exact fractions and compares the result with
  - (80): ½(q−1) − 1/12 + ⅛[p=2] + ⅙[p=3],
  - (79): ½(q−1) − 1/12, which the reading claims over ℤ[1/6],
  - the compactified forms, which add ½ for the cusp;
- it checks the strata of p. 63: generic Aut = 2, j = 1728 ↦ 4, j = 0 ↦ 6, with the two
  points merging in characteristics 2 and 3 into Aut of order 24 and 12. It also checks
  that the generic stratum has q − 2 + [p=2] + [p=3] points, matching
  [U] = L − 2 + ζ₂ + ζ₃.

## Run

    python3 computations/m11-stratified-class/check.py    # about 7 s, writes results.txt

## Result

Everything agrees, for q = 2, 3, 4, 5, 7, 8, 9, 11, 13, 17, 25.
- N(q) equals (80) in every case, for example 13/24 for q = 2, 13/12 for q = 3 and
  71/12 for q = 13.
- N(q) equals (79) exactly when p ≥ 5. In characteristics 2 and 3 (79) is off by ⅛ and ⅙.
  This bears out the reading's correction that (79) holds over ℤ[1/6], not ℤ[1/2] as the
  page says: at q = 3, (79) gives 11/12 against the true 13/12.
- The automorphism orders are as on p. 63.

## Limits

- The invariant itself is the reading's reconstruction. The page says only « dans un groupe
  de Grothendieck convenable ». The script tests the formulas under that rule, through point
  counts only. It does not test that the rule defines an additive invariant on Deligne–Mumford
  stacks, or anything beyond the F_q-realisation.
- Aut(cusp) = ℤ/2 for the compactification is taken as input, not computed.
- q ≤ 25 (q = 16 left out for time).
- It does not compute the stacky (Behrend) point count, which equals q.
