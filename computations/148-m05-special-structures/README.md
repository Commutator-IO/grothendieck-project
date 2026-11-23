# Special structures on five points (folder 148, pp. 30–35)

Tests the vertex set of the chart of page 30 (Findings row
`148-m05-special-structures-chart`): 542 « special » structures on a set K of
five points of the sphere, in nine 𝔖₅-orbits on three levels, 12 + 20 + 30,
60 + 60 + 120, 60 + 120 + 60. Run `python3 -I check.py` (under a second,
standard library only); the output is `results.txt`.

## The definition tested

The page gives the types, their groups and their counts, not a definition.
The script uses the edition's, read from pages 30 and 33–35 (the three
graphs of p. 35 are the dual graphs of the strata of M̄₀,₅; the
« sommets-repères » are read as tangential base points; the NB « sauf I₄,
toutes ces structures sont réelles » as the condition on the rays):

* **level 2**: a point of M₀,₅(ℂ) that is an isolated fixed point of its
  stabiliser in 𝔖₅, i.e. whose stabiliser has order > 2;
* **level 1**: a point of a boundary divisor D_ab ≅ M₀,₃ × M₀,₄ at which a
  non-trivial permutation of the three points of the four-holed piece is an
  automorphism (an isolated fixed point in D_ab), with a ray in the normal
  line T_n(triangle) ⊗ T_n(piece) at the node;
* **level 0**: one of the 15 points of the 0-dimensional strata (three
  triangles), with a pair of rays in the normal lines at the two nodes;

the rays being **real**: fixed, as an isolated point, by an antiholomorphic
automorphism of the marked stable curve fixing each node (the labels may be
permuted). For each structure, G is its group of holomorphic automorphisms
(relabellings), G̃ the group with the antiholomorphic ones, and its
𝔖₅-orbit has 120/|G| elements.

Everything is computed from Möbius maps in complex floating point: the
level-2 points as the fixed points of z ↦ ζz realising an element of order
≥ 3 of 𝔖₅, the level-1 points as fixed points of the anharmonic action on
λ (fitted from three values), the stabilisers by testing the 240 pairs
(relabelling, holomorphic or not), the rays from the derivatives at the
nodes in fixed charts.

## Result

| level | type (page 30) | orbit size | G | G̃ |
|---|---|---|---|---|
| 2 | I₁₀ pentagonal | 12 | 𝔻₅ | order 20 |
| 2 | I₆ bitetrahedral | 20 | 𝔖₃ | order 12 |
| 2 | I₄ square pyramid | 30 | ℤ/4 | order 8 (see below) |
| 1 | II₂ square–triangle, right | 60 | ℤ/2 | order 4 |
| 1 | II′₂ = Tw₁/₄ II₂, left | 60 | ℤ/2 | order 4 |
| 1 | II₁ tetrahedron–triangle | 120 | 1 | order 2 |
| 1 | **not on the chart**: Tw₁/₄ II₁ | **120** | 1 | order 2 |
| 0 | III₂ triple triangle, right | 60 | ℤ/2 | order 4 |
| 0 | III′₁ semi-left | 120 | 1 | order 2 |
| 0 | III′₂ left | 60 | ℤ/2 | order 4 |

* The nine types of the chart come out with exactly the page's sizes 120/|G|
  and groups G; G̃ = G × {1, σ} for all of them but I₄, as the page says.
* With this definition there are **662 structures in ten orbits**, not 542 in
  nine. The extra orbit is at the tetrahedral node: the four-holed piece has
  three mirrors through the node and the triangle two, so the real rays are
  the 12 rays at multiples of π/6, which the stabiliser of the point (order 6,
  rotations by π/3) splits into two orbits of 6 rays each, a quarter turn
  apart. Page 35 counts 10 × 2 × 6 = 120, i.e. one of them. For the square
  (4 real rays, two orbits of 2) and at the level-0 nodes (4 real rays each)
  the page takes both, as II₂/II′₂ and III₂/III′₁/III′₂.
* II₂ and III₂ are the structures fixed by an antiholomorphic map fixing all
  five labels (all points on one real circle); the primed types are their
  quarter-twists. II₁ has no such label-fixing real structure; its two real
  orbits differ by Tw₁/₄, and the chart keeps one.
* I₄: as a set of five points {∞} ∪ μ₄ the configuration has the
  antiholomorphic symmetry z ↦ z̄, so |G̃| = 8 for the point; the page's
  G̃ = G ≅ ℤ/4 is for the structure « point + **oriented** square », whose
  orientation that symmetry reverses. The count, 30, is unaffected.

So 542 = 662 − 120: the chart is this set minus the orbit Tw₁/₄ II₁. Either
the page's notion of special structure is narrower at the tetrahedral node,
in a way the leaves do not state, or the chart leaves one type out. The
arrows (1620 in fourteen orbits) are not tested: their definition is not on
the leaves.
