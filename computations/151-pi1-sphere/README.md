# Π₁ too coarse for the sphere (folder 151)

Tests the example « Π₁ trop grossier pour la sphère » (appendix of
`docs/lean/article.tex`, folder 151, given there as pp. 61–63; Findings piste
`151-pi1-too-coarse-for-the-sphere`). Run `python3 check.py` (about 10 s); the
output is `results.txt`.

**Page reference.** In the transcription the computation is at pp. 38–41
(`transcripts/151/batch-02.fr.tex`, `\page{38}` to `\page{40}`, continued in
`batch-03.fr.tex`, diagram (23) and formula (25)). In the modern reading it is
in `\pagerange{37}{40}` and `\pagerange{41}{43}`. Pages 61–63 of the folder are
the « diagramme fondamental » and the census of inclusions. The appendix row
and the `\lot{151}{4}{61}` link should be checked.

`lean/Grothendieck/Folder151.lean` proves the colimit-in-Top statements of
pp. 62–68 (the depth-2 counterexample and depth one). It proves nothing about
this example.

## What is tested

1. **Groupoid level.** Take S² stratified by k points (k = 1 is the page's
   case: {∞}, ℂ, D*_∞). The pieces are X* = S² minus k points (π₁ = F_{k−1}),
   k discs (π₁ = 1) and k punctured discs (π₁ = ℤ). The amalgamated group is
   computed by sympy's coset enumeration.
2. **The category C and its nerve.** Three categories are compared. G = ℤ/m,
   m = 2 to 5, stands in for ℤ so that every chain group is finite.
   * (a) the page's C = · → ·;
   * (c) End(a) = G with one arrow a → b. This is the first case of p. 38
     (X = ℂ), where the page says b is final;
   * (b) End(a) = G with one arrow a → b and one arrow a → c. This is what the
     definition on p. 37 (objects of the three groupoids Π₁V*, Π₁V, Π₁X*,
     arrows a → b given by p*(a) → b) gives for the sphere data
     ℤ → 1, ℤ → 1.

   For each, the dimensions of H₀ to H₄ of the normalised nerve are computed,
   over ℚ (via the prime 1000003) and over F_p for p | m.
3. **The homotopy pushout of the pieces**, ∗ ← S¹ → ∗, as a simplicial
   suspension of a 3-cycle, with integral homology computed by Smith normal
   form.
4. **The gerbe level.** Count the gluing data by brute force: trivial
   extensions on the pieces, one element of Hom(ℤ, A) per boundary circle,
   modulo the image of Hom(F_{k−1}, A) through the boundary loops c₁, …, c_k
   (with c₁⋯c_k = 1). Compare with |H²(S²; A)|, computed from the
   simplicial cochains of the boundary of a tetrahedron. A runs over ℤ/2 to
   ℤ/8, ℤ/2×ℤ/2, ℤ/2×ℤ/4 and ℤ/3×ℤ/3, and k = 1, 2, 3.

## Result

* 1: the amalgamated group is trivial for k = 1 to 4. Gluing at the level of
  groupoids gives a contractible 1-type. π₁(S²) = 1 is right, and π₂ is lost.
  **Agrees** with the page.
* 2: (a) and (c) are acyclic, as a category with a final object must be. (b)
  is not acyclic: over F_p it has H₂ = H₃ = H₄ = F_p, which is the homology of
  ΣB(ℤ/m). By Thomason's theorem the nerve of (b) is the homotopy pushout
  ∗ ← BG → ∗. For G = ℤ this is ΣS¹ = S², which item 3 computes ([ℤ, 0, ℤ]).

  So the triviality holds for the category the page writes (· → ·) and for
  the groupoid pushout. It does **not** hold for the three-object category
  that the definition of p. 37 produces from the sphere data. That category
  keeps the ℤ, and its nerve is S². The page's « C est la catégorie · → · »
  drops either the object of Π₁(X*) or the endomorphisms ℤ of a. This matches
  the modern reading's diagnosis: what loses the information is the
  truncation of the link S¹ to its π₀. The amalgamated pieces themselves keep
  it.
* 4: the number of gluing classes equals |A| = |H²(S²; A)| in every case
  (k = 1, 2, 3), as formula (25) says. **Agrees.**

## Limits

* The nerve computations use ℤ/m in place of ℤ, and degrees ≤ 4 only. The
  ℤ case rests on Thomason's theorem together with item 3.
* The ℚ ranks are computed modulo one large prime, which gives a lower bound
  that is exact here.
* Item 4 takes as input that extensions of F_{k−1} and of 1 by A are trivial
  (H² = 0) and that A is abelian with trivial action. It counts isomorphism
  classes of gluing data. It does not construct the gerbes.
* The general claim (that the gerbe level recovers the homotopy type of any
  stratified space whose pieces are K(π,1)'s) is not a finite check and is not
  tested.
