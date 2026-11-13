import Mathlib

/-!
# Quillen, notebook 1972-1, p. 25: a transposition acts on `A_n` by an outer automorphism

Daniel Quillen's research notebook 1972-1 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201972/1972-1.pdf>) asks, on
p. 25, whether a transposition `σ` acts on `A_n ⊂ Σ_n` by an outer automorphism, and answers
yes: if `σ x σ⁻¹ = y x y⁻¹` for all `x ∈ A_n`, then `y⁻¹ σ` commutes with `A_n`, so it is the
identity. The page says « center of `A_n` »; since `y⁻¹ σ` is odd, what is used is that the
centralizer of `A_n` in `Σ_n` is trivial, which holds for `n ≥ 4`.

* `eq_one_of_commute_alternating`: for `|α| ≥ 4`, a permutation commuting with every even
  permutation is the identity (the argument of mathlib's `alternatingGroup.center_eq_bot`, for
  a permutation that need not be even);
* `not_inner_swap`: **the answer of the page**: for `|α| ≥ 4` and `a ≠ b`, conjugation by the
  transposition `(a b)` on `A_n` is not conjugation by any element of `A_n`;
* `not_inner_swap_three`: the same for `n = 3`, by computation (`A_3` is abelian and the
  transposition inverts it).
-/

namespace Quillen.Notebook1972_1

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- For `|α| ≥ 4`, the centralizer of the alternating group in the symmetric group is trivial. -/
theorem eq_one_of_commute_alternating (hα4 : 4 ≤ Fintype.card α) {g : Perm α}
    (hg : ∀ k ∈ alternatingGroup α, k * g = g * k) : g = 1 := by
  rw [← support_eq_empty_iff, Finset.eq_empty_iff_forall_notMem]
  intro a ha
  have hab : g a ≠ a := mem_support.1 ha
  have : 2 ≤ (({a, g a} : Finset α)ᶜ).card := by
    rw [← Nat.add_le_add_iff_left, Finset.card_add_card_compl, Finset.card_pair hab.symm]
    exact hα4
  rw [← Nat.lt_iff_add_one_le, Finset.one_lt_card_iff] at this
  obtain ⟨c, d, hc, hd, hcd⟩ := this
  simp only [Finset.compl_insert, Finset.mem_erase, ← ne_eq, Finset.mem_compl,
    Finset.mem_singleton] at hc hd
  let k := swap (g a) d * swap (g a) c
  have hka : k a = a := by
    simp only [coe_mul, Function.comp_apply, k, swap_apply_of_ne_of_ne hab.symm hc.1.symm,
      swap_apply_of_ne_of_ne hab.symm hd.1.symm]
  have hkga : k (g a) = c := by
    simp only [coe_mul, Function.comp_apply, swap_apply_left, k, swap_apply_of_ne_of_ne hc.2 hcd]
  have hk : k ∈ alternatingGroup α := by simp [k, hc.2.symm, hd.2.symm]
  exact hc.2 (by simpa [hka, hkga] using congrArg (fun f : Perm α => f a) (hg k hk))

/-- **Quillen, notebook 1972-1, p. 25.** For `|α| ≥ 4` and `a ≠ b`, there is no `y ∈ A_n` with
`(a b) x (a b)⁻¹ = y x y⁻¹` for every `x ∈ A_n`: the transposition acts on `A_n` by an outer
automorphism. -/
theorem not_inner_swap (hα4 : 4 ≤ Fintype.card α) {a b : α} (hab : a ≠ b) :
    ¬ ∃ y ∈ alternatingGroup α,
      ∀ x ∈ alternatingGroup α, swap a b * x * (swap a b)⁻¹ = y * x * y⁻¹ := by
  rintro ⟨y, hy, h⟩
  have hc : y⁻¹ * swap a b = 1 := by
    refine eq_one_of_commute_alternating hα4 fun k hk => ?_
    have := h k hk
    calc k * (y⁻¹ * swap a b) = y⁻¹ * (y * k * y⁻¹) * swap a b := by group
      _ = y⁻¹ * (swap a b * k * (swap a b)⁻¹) * swap a b := by rw [this]
      _ = y⁻¹ * swap a b * k := by group
  have hs : swap a b = y := by
    rw [← mul_left_cancel_iff (a := y⁻¹), hc, inv_mul_cancel]
  have := mem_alternatingGroup.mp hy
  rw [← hs, sign_swap hab] at this
  exact absurd this (by decide)

/-- **The case `n = 3`**, by computation: conjugation by `(0 1)` on `A_3` is not inner. -/
theorem not_inner_swap_three :
    ¬ ∃ y ∈ alternatingGroup (Fin 3),
      ∀ x ∈ alternatingGroup (Fin 3), swap 0 1 * x * (swap 0 1)⁻¹ = y * x * y⁻¹ := by
  rintro ⟨y, hy, h⟩
  have hc : finRotate 3 ∈ alternatingGroup (Fin 3) := by
    rw [mem_alternatingGroup]; decide
  have hcomm : ∀ z : Perm (Fin 3), sign z = 1 → z * finRotate 3 = finRotate 3 * z := by decide
  have h1 := h _ hc
  rw [hcomm y (mem_alternatingGroup.mp hy), mul_inv_cancel_right] at h1
  revert h1; decide

end Quillen.Notebook1972_1
