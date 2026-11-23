# Test categories on finite decks (issue #187, folders 108, 118, 134-2)

Machine checks for § « Test categories and the De Morgan arch » of the companion
note (`docs/bridges/en/n5d-test.tex`). Grothendieck's criterion (Cisinski,
Astérisque 308, Th. 4.1.19; Maltsiniotis, *La théorie de l'homotopie de
Grothendieck*, Th. 6.6): `A` is a local test category iff the category of
elements `A/(a × L)` of the Lawvere object `L` (the presheaf of sieves) is
aspherical for every object `a`; a weak test category needs `A/L` aspherical.

* `finite_test.py [N]` — for every monoid of order ≤ N (from
  `docs/bridges/atlas/monoids-6.json`) and every poset on ≤ 4 points, the
  homology in degrees 0–2, over Q (mod a large prime) and F₂, of the nerves of
  `A`, `A/L` and `A/(a × L)`, from the normalised chains (strings of
  non-identity arrows). A nerve whose homology in these degrees differs from a
  point's is not aspherical; vanishing proves nothing. Prints every non-Ore
  monoid with the homology of `A/(a × L)` over Q, then a tally.
  `python3 finite_test.py 5` takes about 10 s → `results-5.txt`; order 6
  (2237 monoids) takes much longer → `results-6.txt`.
* `posets_euler.py [N]` — the Euler characteristic of the finite poset `A/L`
  for every poset on ≤ N points, by χ(A/L) = Σₓ |D(↓x)| c(x), with c(x) =
  1 − χ(A_{<x}). `python3 posets_euler.py 6` → `results-posets-6.txt`.

## Results

* Monoids of order ≤ 6 (2510): `A/L` and `A/(a × L)` are never aspherical, so
  none is a weak test category or a local test category (usual weak
  equivalences). The 2015 Ore monoids are covered by the theorem of the note;
  for the 495 others H₁(A/(a × L); Q) has rank 4 to 743. Order ≤ 5 alone:
  50 non-Ore monoids, rank 4 to 224 (`results-5.txt`); order 6 took 13 min.
* Posets on ≤ 6 points: χ(A/L) ≠ 1 whenever χ(A) = 1, so none is a weak test
  category. (No finite poset is a local test category, by the theorem: the
  slice over a minimal element is the point.)

The homology code was checked on BZ/2 (F₂-homology of RP^∞), BZ/3, a
monoid with an idempotent (contractible) and a four-point poset circle.
