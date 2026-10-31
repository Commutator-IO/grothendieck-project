# Operations on maps (folder 138, pp. 122–124 and 127)

Concerns « opérations sur les cartes » (appendix of `docs/lean/article.tex`;
Findings piste `138-operations-belyi-extending`). Run `python3 check.py`
(about 1 s); the output is `results.txt`.

## Why the statement is not a finite check

The statement says: outside an exceptional case, every operation given by a
subset A of the reference sphere is composition with a clean φ, ramified
only over 0, 1, ∞, with φ({0, 1, ∞}) ⊂ {0, 1, ∞} and A = φ⁻¹([0, 1]). This
is an existence statement.

As the edition fixes it (Findings entry), its proof is the clean-dessin
correspondence applied to A. The ingredients are Riemann existence, a Möbius
normalisation sending the three distinguished elements to 0, 1, ∞, and the
triviality of the pure mapping class group of the sphere with three marked
points. A computation on small A would only re-find Belyi functions that
Riemann existence guarantees. It would not test the converse, and the
exceptional case is an open question on the page. So no finite check of
the statement itself is possible.

## What is checked (forward direction, small cases)

The script checks only the easy direction and its bookkeeping, exactly with
sympy:

* Three operations are tested: `sub` = 4z(1−z) (A = [0, 1], the subdivision
  of every edge), `med` = −(z−1)²/(4z) (A = a loop at 1 round 0, the medial
  map), and `sub∘sub`. Each is clean and branched over {0, 1, ∞} only (by
  Riemann–Hurwitz on the three fibres), with φ({0, 1, ∞}) ⊂ {0, 1, ∞} and
  1 ∉ φ⁻¹(1).
* These are composed with seven small clean maps f: 4b(1−b) for
  b = z, z², z³, z²(3−2z), z²/(2z−1), 1−(1−z)³, and f = `med`. In 21 of 21
  cases φ∘f is again clean and branched over 0, 1, ∞ only. Its passport
  (vertex and face degrees) is the one the operation predicts from f's
  passport (subdivision: degree-2 vertices at edge midpoints and doubled
  faces; medial: degree-4 vertices at edge midpoints, and faces given by the
  vertices and faces of f).
* A clean φ with φ(1) = 1, namely z(2−z), is composed with 4z(1−z). It gives
  index 4 over 1, which is not a map. This is why the cell rules of p. 124
  forbid 1 as an edge midpoint of A.

These cases illustrate the exceptional case. Duality, for instance, needs
the edge midpoints of X to stay edge midpoints, so 1 would have to be an edge
midpoint of A, and the construction above cannot produce it. Likewise
A = [0, 1], with 1 an end of A, gives subdivision under the rules (1 becomes
a vertex), not the identity: the identity φ = z is not clean.

## Result

The forward direction agrees on every case tested (21 of 21). The converse
is not checkable by finite computation.

## Limits

* Genus 0 only, f of degree ≤ 12, three operations.
* Passports are compared, not the maps up to isomorphism.
* The converse and the exceptional case are not tested.
