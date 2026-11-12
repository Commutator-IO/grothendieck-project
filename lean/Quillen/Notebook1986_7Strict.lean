import Mathlib

/-!
# Quillen, notebook 1986-7, p. 56: the strict-sum lemma

Daniel Quillen's research notebook 1986-7 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201986/1986-7.pdf>), p. 56,
on the way to the Durfee and Jacobi identities:
`Σ_{0 < i₁ < ⋯ < i_s} q^{i₁ + ⋯ + i_s} = q^{s(s+1)/2} / ((1 − q)(1 − q²)⋯(1 − q^s))`.

The left side is the power series `D s` whose `N`-th coefficient counts the `s`-element sets of
positive integers with sum `N` (`card_filter`, `D`). The statement is proved in the
denominator-free form `(1 − q)⋯(1 − q^s) · D s = q^{s(s+1)/2}` (`prod_mul_D`), over any
commutative ring; the product is a unit of `R⟦q⟧`. The proof is the recursion
`(1 − q^s) D_s = q^s D_{s−1}` (`one_sub_mul_D`): removing `0` from a set of naturals, and
shifting every element by one (`count_succ`, `count_shift`).
-/

namespace Quillen.Notebook1986_7Strict

open Finset PowerSeries

/-- The number of `s`-element sets of natural numbers with sum `N`; `pos` asks for `0 ∉ S`. -/
def count (pos : Bool) (s N : ℕ) : ℕ :=
  (((range (N + 1)).powersetCard s).filter
    (fun S => (pos → 0 ∉ S) ∧ S.sum id = N)).card

theorem subset_range_of_sum {S : Finset ℕ} {N : ℕ} (h : S.sum id = N) : S ⊆ range (N + 1) := by
  intro x hx
  rw [mem_range, Nat.lt_succ_iff, ← h]
  exact single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hx

theorem mem_filter_iff (pos : Bool) (s N : ℕ) (S : Finset ℕ) :
    S ∈ ((range (N + 1)).powersetCard s).filter (fun S => (pos → 0 ∉ S) ∧ S.sum id = N) ↔
      S.card = s ∧ (pos → 0 ∉ S) ∧ S.sum id = N := by
  simp only [mem_filter, mem_powersetCard]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨subset_range_of_sum h2.2, h1⟩, h2⟩

/-- Sets containing `0` or not: `e_{s+1}(N) = d_{s+1}(N) + d_s(N)`. -/
theorem count_succ (s N : ℕ) : count false (s + 1) N = count true (s + 1) N + count true s N := by
  unfold count
  rw [← card_filter_add_card_filter_not (fun S : Finset ℕ => 0 ∉ S), filter_filter,
    filter_filter]
  congr 1
  · congr 1; ext S
    simp only [mem_filter, mem_powersetCard]
    tauto
  · symm
    apply card_nbij' (fun S => insert 0 S) (fun S => S.erase 0)
    · intro S hS
      rw [mem_coe, mem_filter_iff] at hS
      simp only [mem_coe, mem_filter]
      have h0 : 0 ∉ S := hS.2.1 rfl
      have hsum : (insert 0 S).sum id = N := by rw [sum_insert h0]; simpa using hS.2.2
      exact ⟨mem_powersetCard.mpr ⟨subset_range_of_sum hsum, by
        rw [card_insert_of_notMem h0, hS.1]⟩, ⟨fun h => by simp at h, hsum⟩, by simp⟩
    · intro S hS
      simp only [mem_coe, mem_filter] at hS
      rw [mem_coe, mem_filter_iff]
      have h0 : 0 ∈ S := not_not.mp hS.2.2
      refine ⟨?_, fun _ => notMem_erase 0 S, ?_⟩
      · rw [card_erase_of_mem h0, (mem_powersetCard.mp hS.1).2]; rfl
      · rw [← hS.2.1.2, ← sum_erase_add _ _ h0]; simp
    · intro S hS
      rw [mem_coe, mem_filter_iff] at hS
      exact erase_insert (hS.2.1 rfl)
    · intro S hS
      simp only [mem_coe, mem_filter] at hS
      exact insert_erase (not_not.mp hS.2.2)

/-- Shifting by one: `d_s(M + s) = e_s(M)`. -/
theorem count_shift (s M : ℕ) : count true s (M + s) = count false s M := by
  unfold count
  symm
  apply card_nbij' (fun S => S.map (addRightEmbedding 1)) (fun S => S.image (· - 1))
  · intro S hS
    rw [mem_coe, mem_filter_iff] at hS
    rw [mem_coe, mem_filter_iff]
    refine ⟨by simp [hS.1], fun _ => by simp, ?_⟩
    rw [sum_map, ← hS.2.2, ← hS.1]
    simp [sum_add_distrib]
  · intro S hS
    rw [mem_coe, mem_filter_iff] at hS
    rw [mem_coe, mem_filter_iff]
    have h0 : ∀ x ∈ S, 1 ≤ x := fun x hx =>
      Nat.one_le_iff_ne_zero.mpr fun h => hS.2.1 rfl (h ▸ hx)
    have hinj : Set.InjOn (· - 1) (S : Set ℕ) := fun x hx y hy h => by
      have := h0 x hx; have := h0 y hy; simp only at h; omega
    refine ⟨by rw [card_image_of_injOn hinj, hS.1], fun h => by simp at h, ?_⟩
    rw [sum_image hinj]
    have : ∑ x ∈ S, (x - 1) + ∑ x ∈ S, 1 = ∑ x ∈ S, x := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun x hx => by have := h0 x hx; omega
    simp only [sum_const, smul_eq_mul, mul_one, hS.1] at this
    simp only [id] at hS ⊢
    omega
  · intro S _
    ext x; simp
  · intro S hS
    rw [mem_coe, mem_filter_iff] at hS
    ext x
    simp only [mem_map, mem_image, addRightEmbedding_apply]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have : y ≠ 0 := fun h => hS.2.1 rfl (h ▸ hy)
      rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr this)]
    · intro hx
      have : x ≠ 0 := fun h => hS.2.1 rfl (h ▸ hx)
      exact ⟨x - 1, ⟨x, hx, rfl⟩, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr this)⟩

/-- Below `s`, no set of `s` positive integers has sum `N`. -/
theorem count_true_of_lt {s N : ℕ} (h : N < s) : count true s N = 0 := by
  unfold count
  rw [card_eq_zero, filter_eq_empty_iff]
  intro S hS ⟨h0, hsum⟩
  rw [mem_powersetCard] at hS
  have : ∑ x ∈ S, 1 ≤ ∑ x ∈ S, id x := sum_le_sum fun x hx =>
    Nat.one_le_iff_ne_zero.mpr fun h => h0 rfl (h ▸ hx)
  have hs : ∑ x ∈ S, id x = N := hsum
  simp only [sum_const, smul_eq_mul, mul_one, hS.2] at this
  omega

variable (R : Type*) [CommRing R]

/-- `D s = Σ_{0 < i₁ < ⋯ < i_s} q^{i₁ + ⋯ + i_s}`. -/
noncomputable def D (s : ℕ) : R⟦X⟧ := PowerSeries.mk fun N => (count true s N : R)

theorem coeff_D (s N : ℕ) : coeff N (D R s) =
    (((range (N + 1)).powersetCard s).filter (fun S => 0 ∉ S ∧ S.sum id = N)).card := by
  simp [D, count]

/-- The coefficients of `D s` count the `s`-element sets of positive integers with sum `N`. -/
theorem card_filter (s N : ℕ) (S : Finset ℕ) :
    S ∈ ((range (N + 1)).powersetCard s).filter (fun S => 0 ∉ S ∧ S.sum id = N) ↔
      S.card = s ∧ 0 ∉ S ∧ S.sum id = N := by
  simpa using mem_filter_iff true s N S

theorem D_zero : D R 0 = 1 := by
  ext N
  rw [D, coeff_mk, coeff_one]
  have : count true 0 N = if N = 0 then 1 else 0 := by
    unfold count
    rcases N with _ | N
    · decide
    · simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [card_eq_zero, filter_eq_empty_iff]
      intro S hS h
      rw [powersetCard_zero, mem_singleton] at hS
      subst hS; simp at h
  rw [this]; split_ifs <;> simp

/-- **The recursion**: `D_{s+1} = q^{s+1} (D_{s+1} + D_s)`, i.e.
`(1 − q^{s+1}) D_{s+1} = q^{s+1} D_s`. -/
theorem one_sub_mul_D (s : ℕ) : (1 - X ^ (s + 1)) * D R (s + 1) = X ^ (s + 1) * D R s := by
  have key : D R (s + 1) = X ^ (s + 1) * (D R (s + 1) + D R s) := by
    ext N
    simp only [D, coeff_X_pow_mul', coeff_mk, map_add]
    split_ifs with h
    · rw [← Nat.cast_add, ← count_succ, ← count_shift, Nat.sub_add_cancel h]
    · rw [count_true_of_lt (not_le.mp h), Nat.cast_zero]
  rw [sub_mul, one_mul]
  nth_rewrite 1 [key]
  ring

/-- **Notebook 1986-7, p. 56** (strict-sum lemma), denominator-free:
`(1 − q)(1 − q²)⋯(1 − q^s) · Σ_{0<i₁<⋯<i_s} q^{i₁+⋯+i_s} = q^{s(s+1)/2}`. -/
theorem prod_mul_D (s : ℕ) :
    (∏ i ∈ range s, (1 - X ^ (i + 1) : R⟦X⟧)) * D R s = X ^ (s * (s + 1) / 2) := by
  induction s with
  | zero => simp [D_zero]
  | succ s ih =>
    rw [prod_range_succ, mul_assoc, one_sub_mul_D, mul_left_comm, ih, ← pow_add]
    congr 1
    have : (s + 1) * (s + 1 + 1) = s * (s + 1) + 2 * (s + 1) := by ring
    rw [this, Nat.add_mul_div_left _ _ two_pos, add_comm]

/-- The product `(1 − q)⋯(1 − q^s)` is a unit, so `D s = q^{s(s+1)/2} / ((1 − q)⋯(1 − q^s))`. -/
theorem isUnit_prod (s : ℕ) : IsUnit (∏ i ∈ range s, (1 - X ^ (i + 1) : R⟦X⟧)) := by
  rw [isUnit_iff_constantCoeff, map_prod]
  simp

end Quillen.Notebook1986_7Strict
