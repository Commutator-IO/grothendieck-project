import Buffalo.AG.Part03

/-!
# Buffalo, algebraic geometry, part 03: blackboard items

The board items of `public/buffalo-boards/` in the time range of part 03 that no index entry
formalises (`docs/buffalo-ag/lean/Part03-boards.json`).
-/

open CategoryTheory TensorProduct PrimeSpectrum

universe u

namespace Buffalo.AG.Part03

noncomputable section

/-- Board `51wmmpHand0-32167`, t = 32499: in `Spec A_f`, `X_{h/f^n} = φ⁻¹(Y_h)`, since `f^n` is a
unit of `A_f`. -/
theorem board_32499 {A : Type*} [CommRing A] (f h : A) (n : ℕ) :
    basicOpen (IsLocalization.mk' (Localization.Away f) h (pw f n)) =
      basicOpen (algebraMap A (Localization.Away f) h) := by
  have hu : IsUnit (IsLocalization.mk' (Localization.Away f) (1 : A) (pw f n)) :=
    IsUnit.of_mul_eq_one (algebraMap A _ (pw f n)) (by rw [IsLocalization.mk'_spec, map_one])
  have hU : basicOpen (IsLocalization.mk' (Localization.Away f) (1 : A) (pw f n)) = ⊤ :=
    top_unique fun p _ => (mem_basicOpen _ _).2 fun hp =>
      p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
  rw [IsLocalization.mk'_eq_mul_mk'_one, basicOpen_mul, hU, inf_top_eq]

/-- Board `51wmmpHand0-35114`, t = 36406: the Čech complex of the trivial covering has the constant
terms with differentials `∑_{j=0}^{i+1} (-1)^j`, alternately `0` and `1`. -/
theorem board_36406 (i : ℕ) :
    ∑ j ∈ Finset.range (i + 2), (-1 : ℤ) ^ j = if Even i then 0 else 1 := by
  induction i with
  | zero => simp [Finset.sum_range_succ]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with h | h
    · have h1 : ¬ Even (k + 1) := Nat.not_even_iff_odd.2 h.add_one
      have h2 : Even (k + 2) := by simpa [Nat.even_add] using h
      simp [h, h1, h2.neg_one_pow]
    · have h1 : Even (k + 1) := h.add_one
      have h2 : Odd (k + 2) := by simpa [Nat.odd_add] using h
      simp [Nat.not_even_iff_odd.2 h, h1, h2.neg_one_pow]

/-- Board `thSz9ZHDK9o-2870`, t = 2938: `φ⁻¹V(𝔎) = V(𝔎B)` and `V(J) ⊂ V(𝔎B) ⟺ 𝔎 ⊂ u⁻¹(√J)`. -/
theorem board_2938 {A B : Type*} [CommRing A] [CommRing B] (u : A →+* B) (K : Ideal A)
    (J : Ideal B) :
    comap u ⁻¹' zeroLocus (K : Set A) = zeroLocus (K.map u : Set B) ∧
      (zeroLocus (J : Set B) ⊆ zeroLocus (K.map u : Set B) ↔ K ≤ J.radical.comap u) := by
  refine ⟨(prop_31557 u K).1, ?_⟩
  rw [zeroLocus_subset_zeroLocus_iff, Ideal.map_le_iff_le_comap]

/-- Board `thSz9ZHDK9o-0000`, t = 1836: if `Y → S` is a monomorphism (`A → C` an epimorphism of
rings), so is its base change, hence `Spec(B ⊗_A C) → Spec B` is injective (`prop_1836`); its
image is the preimage of `Spec C` (`prop_1899`), so `Spec Z → Spec X ×_{Spec S} Spec Y` is
bijective. -/
theorem board_1836 {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C]
    (hu : ∀ (T : Type u) [CommRing T] (g h : C →+* T),
      g.comp (algebraMap A C) = h.comp (algebraMap A C) → g = h) :
    Function.Injective (comap (algebraMap B (B ⊗[A] C))) := by
  refine prop_1836 _ fun T _ g h hgh => ?_
  have hC : g.comp Algebra.TensorProduct.includeRight.toRingHom =
      h.comp Algebra.TensorProduct.includeRight.toRingHom := by
    refine hu T _ _ (RingHom.ext fun a => ?_)
    have := congrArg (fun φ : B →+* T => φ (algebraMap A B a)) hgh
    change g (Algebra.TensorProduct.includeRight (algebraMap A C a)) =
      h (Algebra.TensorProduct.includeRight (algebraMap A C a))
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A B (B ⊗[A] C)]
    exact this
  refine RingHom.ext fun x => ?_
  induction x with
  | tmul b c =>
    have h1 := congrArg (fun φ : B →+* T => φ b) hgh
    have h2 := congrArg (fun φ : C →+* T => φ c) hC
    rw [← mul_one b, ← one_mul c, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, map_mul]
    rw [show b ⊗ₜ[A] (1 : C) = algebraMap B (B ⊗[A] C) b from rfl]
    exact congrArg₂ (· * ·) h1 h2
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end

end Buffalo.AG.Part03
