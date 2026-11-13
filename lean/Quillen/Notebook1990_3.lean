import Mathlib

/-!
# Quillen, notebooks 1990-2 and 1990-3: the rigid triple in `Sₙ`; the Green operator of `ℤ/n`

Daniel Quillen's research notebooks 1990-2 and 1990-3 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201990/1990-3.pdf>).

* p. 2: for an `n`-cycle `γ` and a transposition `s = (x y)`, the product `γ s` is an
  `(n − 1)`-cycle (a cycle moving all points but one) if and only if `s` swaps two
  `γ`-adjacent points, `γ x = y` or `γ y = x` (`isCycle_mul_swap_iff`, for `n ≥ 3`). The
  direction « if » is mathlib's `Equiv.Perm.IsCycle.swap_mul` after conjugating the swap past
  `γ`; « only if » comes from the fixed point of `γ s`, which must be `x` or `y`.
* p. 18: in a `ℚ`-algebra where `κⁿ = 1`, the element
  `G = (1/n) Σ_{j<n} ((n−1)/2 − j) κʲ` satisfies `G (1 − κ) = 1 − P` with
  `P = (1/n) Σ_{j<n} κʲ` (`green_mul_one_sub`), and `P (1 − κ) = 0`, `P² = P`
  (`proj_mul_one_sub`, `proj_idem`): `G` inverts `1 − κ` on the complement of the invariants.
  The same operator is the « canonical Green operator » of 1990-2, p. 11, where it is also
  checked that `G` commutes with `1 − κ` and `P G = G P = 0` (`green_commute`,
  `proj_mul_green`, `green_mul_proj`; the last uses `Σ_{j<n} ((n − 1)/2 − j) = 0`).
-/

namespace Quillen.Notebook1990_3

open Equiv Equiv.Perm Finset

section Rigid

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- For a cycle `γ` moving every point of a set with at least three elements, `γ² x ≠ x`. -/
lemma sq_apply_ne {γ : Perm α} (hγ : γ.IsCycle) (hs : γ.support = univ) (hn : 3 ≤ Fintype.card α)
    (x : α) : γ (γ x) ≠ x := by
  intro h
  have hx : γ x ≠ x := mem_support.mp (hs ▸ mem_univ x)
  have h2 : γ ^ 2 = 1 := (hγ.pow_eq_one_iff' hx).mpr (by rw [pow_two, mul_apply, h])
  have := orderOf_le_of_pow_eq_one two_pos h2
  rw [hγ.orderOf, hs, card_univ] at this
  omega

/-- **Notebook 1990-3, p. 2**: for `γ` an `n`-cycle (`n ≥ 3`) and `x ≠ y`, `γ (x y)` is a cycle
moving `n − 1` points iff `x` and `y` are adjacent for `γ`. -/
theorem isCycle_mul_swap_iff {γ : Perm α} (hγ : γ.IsCycle) (hs : γ.support = univ)
    (hn : 3 ≤ Fintype.card α) {x y : α} (hxy : x ≠ y) :
    ((γ * swap x y).IsCycle ∧ #(γ * swap x y).support = Fintype.card α - 1) ↔
      (γ x = y ∨ γ y = x) := by
  have hmove : ∀ z, γ z ≠ z := fun z => mem_support.mp (hs ▸ mem_univ z)
  constructor
  · rintro ⟨-, hcard⟩
    obtain ⟨z, hz⟩ : ∃ z, z ∉ (γ * swap x y).support := by
      by_contra! h
      rw [eq_univ_of_forall h, card_univ] at hcard
      omega
    rw [notMem_support, mul_apply] at hz
    by_cases hzx : z = x
    · subst hzx; exact Or.inr (by rwa [swap_apply_left] at hz)
    by_cases hzy : z = y
    · subst hzy; exact Or.inl (by rwa [swap_apply_right] at hz)
    exact absurd (by rwa [swap_apply_of_ne_of_ne hzx hzy] at hz) (hmove z)
  · -- reduce to `γ x = y`
    have key : ∀ a, (γ * swap a (γ a)).IsCycle ∧
        #(γ * swap a (γ a)).support = Fintype.card α - 1 := fun a => by
      rw [mul_swap_eq_swap_mul]
      have h1 : γ (γ a) ≠ γ a := hmove (γ a)
      have h2 : γ (γ (γ a)) ≠ γ a := fun h => sq_apply_ne hγ hs hn a (γ.injective h)
      refine ⟨hγ.swap_mul h1 h2, ?_⟩
      rw [support_swap_mul_eq γ (γ a) h2, hs, card_sdiff, card_univ]
      simp
    rintro (h | h)
    · subst h; exact key x
    · subst h; rw [swap_comm]; exact key y

end Rigid

section Green

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- `P = (1/n) Σ_{j<n} κʲ`. -/
noncomputable def proj (n : ℕ) (κ : A) : A := (1 / (n : ℚ)) • ∑ j ∈ range n, κ ^ j

/-- `G = (1/n) Σ_{j<n} ((n − 1)/2 − j) κʲ`. -/
noncomputable def green (n : ℕ) (κ : A) : A :=
  (1 / (n : ℚ)) • ∑ j ∈ range n, (((n : ℚ) - 1) / 2 - j) • κ ^ j

lemma proj_mul_one_sub (n : ℕ) {κ : A} (hκ : κ ^ n = 1) : proj n κ * (1 - κ) = 0 := by
  rw [proj, smul_mul_assoc, geom_sum_mul_neg, hκ, sub_self, smul_zero]

/-- **Notebook 1990-3, p. 18**: `G (1 − κ) = 1 − P` when `κⁿ = 1`, `n ≥ 1`. -/
theorem green_mul_one_sub {n : ℕ} (hn : 0 < n) {κ : A} (hκ : κ ^ n = 1) :
    green n κ * (1 - κ) = 1 - proj n κ := by
  -- the sum `Σ_{j<n} (c − j) κʲ (1 − κ)` telescopes
  have hsum : ∀ (m : ℕ) (c : ℚ), (∑ j ∈ range m, (c - j) • κ ^ j) * (1 - κ) =
      c • 1 - (c - m) • κ ^ m - ∑ j ∈ range m, κ ^ (j + 1) := by
    intro m c
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, add_mul, ih, sum_range_succ, smul_mul_assoc, mul_sub, mul_one,
        ← pow_succ]
      push_cast
      module
  have hshift : ∑ j ∈ range n, κ ^ (j + 1) = ∑ j ∈ range n, κ ^ j := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [sum_range_succ, sum_range_succ', hκ, pow_zero]
  rw [green, smul_mul_assoc, hsum, hshift, hκ, proj]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  match_scalars <;> field_simp
  ring

lemma proj_idem {n : ℕ} (hn : 0 < n) {κ : A} (hκ : κ ^ n = 1) : proj n κ * proj n κ = proj n κ := by
  have h : proj n κ * κ = proj n κ :=
    (sub_eq_zero.mp (by simpa [mul_sub] using proj_mul_one_sub n hκ)).symm
  have hpow : ∀ j, proj n κ * κ ^ j = proj n κ := fun j => by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, h]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  calc proj n κ * proj n κ = (1 / (n : ℚ)) • ∑ j ∈ range n, proj n κ * κ ^ j := by
        nth_rewrite 2 [proj]
        rw [mul_smul_comm, mul_sum]
    _ = (1 / (n : ℚ)) • ((n : ℚ) • proj n κ) := by
        simp only [hpow, sum_const, card_range]
        rw [Nat.cast_smul_eq_nsmul]
    _ = proj n κ := by rw [smul_smul, one_div_mul_cancel hn', one_smul]

lemma commute_pow_green (n j : ℕ) (κ : A) : Commute (κ ^ j) (green n κ) := by
  rw [green]
  exact (Commute.sum_right _ _ _ fun i _ =>
    ((Commute.refl κ).pow_pow j i).smul_right _).smul_right _

/-- **Notebook 1990-2, p. 11**: `(1 − κ) G = G (1 − κ)`. -/
theorem green_commute (n : ℕ) (κ : A) : Commute (1 - κ) (green n κ) :=
  (Commute.one_left _).sub_left (by simpa using commute_pow_green n 1 κ)

/-- **Notebook 1990-2, p. 11**: `P G = 0`, because `Σ_{j<n} ((n − 1)/2 − j) = 0`. -/
theorem proj_mul_green {n : ℕ} (hn : 0 < n) {κ : A} (hκ : κ ^ n = 1) : proj n κ * green n κ = 0 := by
  have h : proj n κ * κ = proj n κ :=
    (sub_eq_zero.mp (by simpa [mul_sub] using proj_mul_one_sub n hκ)).symm
  have hpow : ∀ j, proj n κ * κ ^ j = proj n κ := fun j => by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, h]
  have hsum : ∑ j ∈ range n, (((n : ℚ) - 1) / 2 - j) = 0 := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    have h2 := congrArg (Nat.cast : ℕ → ℚ) (Finset.sum_range_id_mul_two n)
    push_cast [Nat.cast_sub (show 1 ≤ n by omega)] at h2
    linarith
  simp only [green, mul_smul_comm, mul_sum, hpow, ← sum_smul, hsum, zero_smul, smul_zero]

/-- **Notebook 1990-2, p. 11**: `G P = 0`. -/
theorem green_mul_proj {n : ℕ} (hn : 0 < n) {κ : A} (hκ : κ ^ n = 1) : green n κ * proj n κ = 0 := by
  have hc : Commute (proj n κ) (green n κ) := by
    rw [proj]
    exact (Commute.sum_left _ _ _ fun j _ => commute_pow_green n j κ).smul_left _
  rw [← hc.eq, proj_mul_green hn hκ]

end Green

end Quillen.Notebook1990_3
