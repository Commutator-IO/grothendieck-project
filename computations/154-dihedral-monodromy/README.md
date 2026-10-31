# Dihedral monodromy (folder 154, pp. 55–63)

Tests the arithmetic of the statement « monodromie diédrale » (appendix of
`docs/lean/article.tex`, folder 154, pp. 55–63, 85–86; Findings piste
`154-dihedral-monodromy-half-turn`). Run `python3 check.py` (about 10 s); the
output is `results.txt`.

## What is tested

Pseudoline arrangements are replaced by **realisable** ones: random lines of
RP² with integer coefficients in [−9, 9]. Some lines are forced through
existing vertices, so that points of multiplicity ≥ 3 occur. There are 214
arrangements with n = 3 to 10 lines, 145 of them with a multiple point, and
1373 (arrangement, line D_i) pairs.

* **A.** On every line D_i, Σ_{s ∈ D_i} (ν(s) − 1) = n − 1. This is the
  value the page gives χ_{2n}.
* **B.** Compose the page's reflections σ(t) = l − t of ℤ/2n along the chain
  s₁, a₁, s₂, …, s_m, a_m of vertices and arcs of D_i. The page's values are
  l_s = n − ν_s and l_a = (n−1) − (ν_s−1) − (ν_t−1). The result is the
  rotation t ↦ t − (n−1), as the box of p. 57 says. Each line is tried with
  five random orders of its vertices.
* **C.** The geometric half-turn in the realisable model the Findings entry
  proposes. Positions D are points p of the dual plane. Pol(D) is the doubled
  cyclic order of the directions from p to the dual points δ_j. Move p half-way
  round δ_i on a small circle and count how many of the 2n − 2 other
  directions the direction p → δ_i passes. The count is recorded, and so is
  the length 2m_i of the chain of cells that the half-turn crosses, where m_i
  is the number of vertices on D_i.
* **D.** In 𝔻_{2n}, of order 4n, n = 2 to 20: the index of ⟨rot(n−1)⟩ and of
  ⟨rot(2(n−1))⟩ among the rotations; whether rot(n−1) and a reflection
  through a vertex generate 𝔻_{2n}; and whether adding a reflection through
  an edge midpoint does.

## Result

* A and B hold in all 1373 cases. The rotation t ↦ t − (n−1) comes out
  exactly, and it does not depend on the order of the vertices along D_i
  (the l_a telescope).
* C: the label passes exactly n − 1 others in 334 of 334 half-turns tested.
  The "n − 1 steps" are therefore realised geometrically.

  **Remark.** In the dual model the half-turn crosses only m_i ≤ n − 1 walls,
  so the chain has 2m_i cells and never the page's p = 2n (0 of 1373). The
  composite in B does not depend on p, so the boxed value is unaffected. The
  edition says it did not redo this chain identification.
* D: ⟨rot(n−1)⟩ has index gcd(n−1, 2) and ⟨rot(2(n−1))⟩ has index 2, as the
  reading says. rot(n−1) and a vertex reflection generate 𝔻_{2n} exactly when
  n is even (index 2 when n is odd), and adding an edge reflection always gives
  𝔻_{2n}. This confirms the edition's remark that for odd n a side reflection
  is needed.

## Limits

* Only the arithmetic and the realisable step count are checked.
  Grothendieck's transport isomorphism (which reflection is attached to each
  cell of the surface 𝒳) is not modelled. The naive identification of the
  labelled points before and after a half-turn is not even dihedral: it fixes
  the two labels of D_i and shifts the others by n. So the local-system
  structure itself is not tested.
* Surjectivity on π₁(𝒳) is checked only at the level "these generators
  generate 𝔻_{2n}". That the loops which realise them exist on 𝒳 is not
  checked.
* Pages 85–86 (surjectivity without crossing the D_i) are not tested.
* Non-realisable pseudoline arrangements (n ≥ 9) are not covered.
