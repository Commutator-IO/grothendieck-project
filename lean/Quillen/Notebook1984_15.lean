import Mathlib

/-!
# Quillen, notebook 1984-15, p. 55: pair symmetry of a curvature tensor

Daniel Quillen's research notebook 1984-15 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201984/1984-15.pdf>) derives, on
p. 55, the pair symmetry `R_{ijkl} = R_{klij}` of a four-index tensor skew in `(i, j)` and in
`(k, l)` and satisfying the cyclic (first Bianchi) identity `R_{ijkl} + R_{jkil} + R_{kijl} = 0`,
by adding four cyclic identities.

The sum of the four identities gives `2 R_{ijkl} = 2 R_{klij}`, so the conclusion needs `2` to be
cancellable in the target. This file proves

* `two_smul_pair_symm`: `2 • R i j k l = 2 • R k l i j` in any additive commutative group;
* `pair_symm`: `R i j k l = R k l i j` when the target has no `2`-torsion (for instance a vector
  space over `ℝ`, the case of the page);
* `not_pair_symm_zmod_two`: the factor `2` cannot be removed in general: over `ZMod 2`, on four
  indices, the tensor equal to `1` exactly when `i, j, k, l` are distinct and `0 ∈ {i, j}` is
  alternating in both pairs and satisfies the cyclic identity, but `R 0 1 2 3 = 1 ≠ 0 = R 2 3 0 1`.
  (A computation over `GF(2)` shows that on three indices pair symmetry still holds.)
-/

namespace Quillen.Notebook1984_15

variable {ι G : Type*} [AddCommGroup G]

/-- The hypotheses: skew in each pair and the cyclic identity. -/
structure IsCurvature (R : ι → ι → ι → ι → G) : Prop where
  skew₁ : ∀ i j k l, R i j k l = -R j i k l
  skew₂ : ∀ i j k l, R i j k l = -R i j l k
  bianchi : ∀ i j k l, R i j k l + R j k i l + R k i j l = 0

variable {R : ι → ι → ι → ι → G}

/-- The sum of four cyclic identities: `2 R_{ijkl} = 2 R_{klij}`. -/
theorem two_smul_pair_symm (hR : IsCurvature R) (i j k l : ι) :
    (2 : ℤ) • R i j k l = (2 : ℤ) • R k l i j := by
  have h1 := hR.bianchi i j k l
  have h2 := hR.bianchi j k l i
  have h3 := hR.bianchi k l i j
  have h4 := hR.bianchi l i j k
  rw [hR.skew₁ k i j l] at h1
  rw [hR.skew₂ j k l i, hR.skew₂ k l j i, hR.skew₁ l j k i, hR.skew₂ j l k i] at h2
  rw [hR.skew₁ l i k j, hR.skew₂ i l k j, hR.skew₁ i k l j, hR.skew₂ k i l j,
    hR.skew₁ k i j l] at h3
  rw [hR.skew₁ l i j k, hR.skew₂ i j l k] at h4
  linear_combination (norm := abel) h1 + h2 - h3 - h4

/-- **p. 55**: pair symmetry, when the target has no `2`-torsion. -/
theorem pair_symm (hR : IsCurvature R) (h2 : ∀ x : G, (2 : ℤ) • x = 0 → x = 0)
    (i j k l : ι) : R i j k l = R k l i j := by
  exact sub_eq_zero.1 (h2 _ (by rw [smul_sub, two_smul_pair_symm hR, sub_self]))

/-- The counterexample in characteristic `2`. -/
def R₂ (i j k l : Fin 4) : ZMod 2 :=
  if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧ (i = 0 ∨ j = 0) then 1 else 0

theorem isCurvature_R₂ : IsCurvature R₂ where
  skew₁ := by unfold R₂; decide
  skew₂ := by unfold R₂; decide
  bianchi := by unfold R₂; decide

/-- Pair symmetry fails for `R₂`: the factor `2` is needed. -/
theorem not_pair_symm_zmod_two : R₂ 0 1 2 3 ≠ R₂ 2 3 0 1 := by
  unfold R₂; decide

end Quillen.Notebook1984_15
