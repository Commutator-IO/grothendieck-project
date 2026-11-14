import Mathlib

/-!
# Quillen, notebook 1971-14: the functional equation of the zeta function of a curve

Daniel Quillen's research notebook 1971-14 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201971/1971-14.pdf>).

* pp. 24-25: for a curve of genus `g ≥ 1` over `𝔽_q`, write `μ Z(z)` as the finite sum over the
  classes `L` of degree `0 ≤ deg L ≤ 2g − 2` of `z^{deg L}(q^{h⁰(L)} − 1)` plus the geometric
  tail `h(q^g z^{2g−1}/(1 − qz) − z^{2g−1}/(1 − z))` (`Z`). Given Riemann–Roch
  `h⁰(L) = deg L + 1 − g + h⁰(K − L)` for an involution `L ↦ K − L` with `deg K = 2g − 2`, and
  `h` classes in each degree, `Z(z) = q^{g−1} z^{2g−2} Z(1/(qz))` in any field
  (`functional_equation`). The page's route (an infinite sum continued analytically) is replaced by
  the finite split `Z = Σ z^{deg L} q^{h⁰(L)} + h(q^g z^{2g−1}/(1 − qz) − 1/(1 − z))`, both parts
  invariant.
-/

namespace Quillen.Notebook1971_14

open Finset

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- The zeta function of p. 24 in the variable `w`, times `μ`: the polynomial part over the classes
`L` of degree `0 ≤ deg L ≤ 2g − 2`, plus `h` times the geometric tail. -/
noncomputable def Z (q : K) (g h : ℕ) (deg h0 : ι → ℕ) (w : K) : K :=
  ∑ i, w ^ deg i * (q ^ h0 i - 1) + h * (q ^ g * w ^ (2 * g - 1) / (1 - q * w)
    - w ^ (2 * g - 1) / (1 - w))

/-- **pp. 24-25.** The functional equation `Z(z) = q^{g−1} z^{2g−2} Z(1/(qz))`, from Riemann–Roch
`h⁰(L) = deg L + 1 − g + h⁰(K − L)` for the involution `σ : L ↦ K − L` (`deg K = 2g − 2`) and `h`
classes in each degree `0, …, 2g − 2`. -/
theorem functional_equation {q z : K} (hq : q ≠ 0) (hz : z ≠ 0) (hz1 : z ≠ 1) (hqz : q * z ≠ 1)
    {g h : ℕ} (hg : 1 ≤ g) (deg h0 : ι → ℕ) (σ : ι → ι) (hσ : Function.Involutive σ)
    (hdeg : ∀ i, deg i + deg (σ i) + 2 = 2 * g)
    (hRR : ∀ i, (h0 i : ℤ) = deg i + 1 - g + h0 (σ i))
    (hcard : ∀ d < 2 * g - 1, #{i | deg i = d} = h) :
    Z q g h deg h0 z = q ^ (g - 1) * z ^ (2 * g - 2) * Z q g h deg h0 (q * z)⁻¹ := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le' hg
  have hN : 2 * (N + 1) - 1 = 2 * N + 1 := by omega
  have hN' : 2 * (N + 1) - 2 = 2 * N := by omega
  rw [hN', Nat.add_sub_cancel]
  have hdeg' : ∀ i, deg i < 2 * N + 1 := fun i => by have := hdeg i; omega
  -- `Z = B + h · S` with `B(w) = Σ w^{deg} q^{h⁰}` and `S(w) = q^g w^{2g−1}/(1 − qw) − 1/(1 − w)`
  have split : ∀ w : K, w ≠ 1 → q * w ≠ 1 → Z q (N + 1) h deg h0 w =
      ∑ i, w ^ deg i * q ^ h0 i + h * (q ^ (N + 1) * w ^ (2 * N + 1) / (1 - q * w) - 1 / (1 - w)) :=
    fun w hw hqw => by
    have hC : ∑ i, w ^ deg i = h * ∑ d ∈ range (2 * N + 1), w ^ d := by
      rw [← sum_fiberwise_of_maps_to (g := deg) (t := range (2 * N + 1))
        (fun i _ => mem_range.2 (hdeg' i)), mul_sum]
      refine sum_congr rfl fun d hd => ?_
      rw [sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2], sum_const, hcard d (mem_range.1 hd),
        nsmul_eq_mul]
    have hw' : 1 - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
    have hqw' : 1 - q * w ≠ 0 := sub_ne_zero.2 (Ne.symm hqw)
    have key : ∑ d ∈ range (2 * N + 1), w ^ d + w ^ (2 * N + 1) / (1 - w) = 1 / (1 - w) := by
      field_simp; linear_combination geom_sum_mul_neg w (2 * N + 1)
    simp only [Z, mul_sub, sum_sub_distrib, mul_one, hC]
    rw [hN]
    linear_combination (-(h : K)) * key
  have hw : q * (q * z)⁻¹ = z⁻¹ := by rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
  rw [split z hz1 hqz, split _ (by rwa [Ne, inv_eq_one]) (by rw [hw]; exact inv_ne_one.2 hz1),
    hw, mul_add, mul_sum]
  congr 1
  · refine Fintype.sum_equiv (hσ.toPerm σ) _ _ fun i => ?_
    have h1 := hdeg i
    have h2 := hRR i
    have e1 : z ^ (2 * N) = z ^ deg i * z ^ deg (σ i) := by rw [← pow_add]; congr 1; omega
    have e2 : q ^ N * q ^ h0 (σ i) = q ^ h0 i * q ^ deg (σ i) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    simp only [Function.Involutive.coe_toPerm, inv_pow, mul_pow]
    rw [e1]
    field_simp
    linear_combination -e2
  · have : 1 - (q * z)⁻¹ ≠ 0 := sub_ne_zero.2 (by rwa [ne_comm, Ne, inv_eq_one])
    have : 1 - z⁻¹ ≠ 0 := sub_ne_zero.2 (by rwa [ne_comm, Ne, inv_eq_one])
    have : 1 - q * z ≠ 0 := sub_ne_zero.2 (Ne.symm hqz)
    have : 1 - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
    simp only [inv_pow, mul_pow]
    field_simp
    ring

end Quillen.Notebook1971_14
