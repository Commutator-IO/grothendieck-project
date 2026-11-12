import Mathlib

/-!
# Quillen, notebook 1982-3, p. 18: `∏ (1 + a_n)` converges iff `∑ a_n` does, for `a_n ≥ 0`

Daniel Quillen's research notebook 1982-3 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201982/1982-3.pdf>) uses, on
p. 18 (and again p. 35), the classical criterion: for `a_n ≥ 0`, the infinite product
`∏ (1 + a_n)` converges if and only if `∑ a_n < ∞`.

Mathlib has one direction (`Real.multipliable_one_add_of_summable`, through the logarithm).
This file adds the converse, from `1 + ∑_{i ∈ s} a_i ≤ ∏_{i ∈ s} (1 + a_i)`, and states the
criterion both for unconditional products (`Multipliable`) and for the sequence of partial
products:

* `one_add_sum_le_prod`: `1 + ∑_{i ∈ s} a_i ≤ ∏_{i ∈ s} (1 + a_i)` for `a_i ≥ 0`;
* `multipliable_one_add_iff`: **the criterion**, `Multipliable (1 + a) ↔ Summable a`;
* `tendsto_prod_range_iff`: the partial products `∏_{i < N} (1 + a_i)` converge iff
  `Summable a`.

The limits are then `≥ 1`, so the product converges in the classical sense (to a nonzero limit).
-/

namespace Quillen.Notebook1982_3

open Finset Filter Topology

theorem one_add_sum_le_prod {ι : Type*} (s : Finset ι) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    have h1 : 1 ≤ ∏ i ∈ s, (1 + a i) := by
      have := sum_nonneg fun i (_ : i ∈ s) => ha i
      linarith
    nlinarith [ha j]

/-- **The criterion of notebook 1982-3, p. 18**, for unconditional products. -/
theorem multipliable_one_add_iff {ι : Type*} {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    Multipliable (fun i => 1 + a i) ↔ Summable a := by
  classical
  refine ⟨fun h => ?_, Real.multipliable_one_add_of_summable⟩
  obtain ⟨r, -, s₁, hs₁⟩ := h.eventually_bounded_finsetProd
  refine summable_of_sum_le (c := r) (fun i => ha i) fun t => ?_
  calc ∑ i ∈ t, a i ≤ ∑ i ∈ t ∪ s₁, a i :=
        sum_le_sum_of_subset_of_nonneg subset_union_left fun i _ _ => ha i
    _ ≤ ∏ i ∈ t ∪ s₁, (1 + a i) := by linarith [one_add_sum_le_prod (t ∪ s₁) ha]
    _ ≤ r := hs₁ _ subset_union_right

/-- The criterion for the sequence of partial products `∏_{i < N} (1 + a_i)`. -/
theorem tendsto_prod_range_iff {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) :
    (∃ P, Tendsto (fun N => ∏ i ∈ range N, (1 + a i)) atTop (𝓝 P)) ↔ Summable a := by
  refine ⟨fun ⟨P, hP⟩ => ?_, fun h =>
    ⟨_, (Real.multipliable_one_add_of_summable h).hasProd.tendsto_prod_nat⟩⟩
  have hmono : Monotone (fun N => ∏ i ∈ range N, (1 + a i)) := by
    refine monotone_nat_of_le_succ fun N => ?_
    rw [prod_range_succ]
    have h1 : 1 ≤ ∏ i ∈ range N, (1 + a i) := by
      have := one_add_sum_le_prod (range N) ha
      have := sum_nonneg fun i (_ : i ∈ range N) => ha i
      linarith
    nlinarith [ha N]
  refine summable_of_sum_range_le (c := P) ha fun N => ?_
  have := hmono.ge_of_tendsto hP N
  linarith [one_add_sum_le_prod (range N) ha]

end Quillen.Notebook1982_3
