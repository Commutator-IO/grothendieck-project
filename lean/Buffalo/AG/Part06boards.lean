import Buffalo.AG.Part06

/-!
# Buffalo, algebraic geometry, part 06: blackboard items

The board items of `public/buffalo-boards/` in the time range of part 06 (`Oqhr-Gt66es`,
3486–19492 s) that no index entry formalises (`docs/buffalo-ag/lean/Part06-boards.json`).
-/

open CategoryTheory TensorProduct

universe u

namespace Buffalo.AG.Part06

noncomputable section

/-- Board `Oqhr-Gt66es-5839`, t = 6161: `A ⊂ ∏_𝔭 A_𝔭` (an element vanishing in every local ring
is zero). -/
theorem board_6161 {A : Type u} [CommRing A] (a : A)
    (h : ∀ (p : Ideal A) [p.IsPrime], algebraMap A (Localization.AtPrime p) a = 0) : a = 0 := by
  by_contra ha
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Submodule.span A {a}).annihilator
    (by
      rw [Ne, Ideal.eq_top_iff_one, Submodule.mem_annihilator_span_singleton, one_smul]
      exact ha)
  obtain ⟨⟨s, hs⟩, hsa⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl
    (Localization.AtPrime m) a).1 (@h m hm.isPrime)
  exact hs (hle (Submodule.mem_annihilator_span_singleton _ _ |>.2 (by
    rw [smul_eq_mul]; exact hsa)))

/-- Board `Oqhr-Gt66es-5839`, t = 6430: `Spec A` is irreducible iff `A/nil(A)` is a domain (the
nilradical is prime; mathlib: `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`). -/
theorem board_6430 (A : Type u) [CommRing A] :
    IrreducibleSpace (PrimeSpectrum A) ↔ (nilradical A).IsPrime :=
  PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical

/-- Board `Oqhr-Gt66es-8803`, t = 11246: epimorphisms of affine schemes (injective ring maps) are
not stable under base change: `ℤ → ℚ` is injective, but `𝔽₂ ⊗_ℤ ℚ = 0`, so
`𝔽₂ → 𝔽₂ ⊗_ℤ ℚ` is not. -/
theorem board_11246 : Function.Injective (algebraMap ℤ ℚ) ∧
    ¬ Function.Injective (algebraMap (ZMod 2) (ZMod 2 ⊗[ℤ] ℚ)) := by
  refine ⟨fun a b h => by exact_mod_cast h, fun h => ?_⟩
  have hsub : Subsingleton (ZMod 2 ⊗[ℤ] ℚ) := by
    refine subsingleton_of_zero_eq_one ?_
    rw [Algebra.TensorProduct.one_def]
    have : (1 : ℚ) = (2 : ℤ) • ((1 : ℚ) / 2) := by norm_num
    rw [this, ← TensorProduct.smul_tmul, show (2 : ℤ) • (1 : ZMod 2) = 0 by decide,
      TensorProduct.zero_tmul]
  have := h (Subsingleton.elim (algebraMap (ZMod 2) _ 0) (algebraMap (ZMod 2) _ 1))
  exact absurd this (by decide)

/-- Board `Oqhr-Gt66es-8803`, t = 11441: for `A` local with residue field `k`, the map
`𝔪 ⊗_A k → A ⊗_A k` induced by the injection `𝔪 ↪ A` is zero. -/
theorem board_11441 (A : Type u) [CommRing A] [IsLocalRing A] :
    LinearMap.rTensor (A ⧸ IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal A).subtype = 0 := by
  apply TensorProduct.ext'
  intro x c
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  simp only [LinearMap.rTensor_tmul, Submodule.coe_subtype, LinearMap.zero_apply]
  rw [show (x : A) = (x : A) • (1 : A) by rw [smul_eq_mul, mul_one], TensorProduct.smul_tmul,
    Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mul_mem_right _ _ x.2), TensorProduct.tmul_zero]

/-- Board `Oqhr-Gt66es-11767`, t = 12804: two homomorphisms `B ⇉ C` agreeing on generators
coincide (mathlib: `AlgHom.ext_of_adjoin_eq_top`). -/
theorem board_12804 {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] {s : Set B} (hs : Algebra.adjoin A s = ⊤) {φ ψ : B →ₐ[A] C}
    (h : Set.EqOn φ ψ s) : φ = ψ :=
  AlgHom.ext_of_adjoin_eq_top hs h

/-- Board `Oqhr-Gt66es-16594`, t = 18815: `A ⊗_k B ⊂ A ⊗_k Frac(B)` (tensoring over a field
preserves injections). -/
theorem board_18815 (k A B : Type u) [Field k] [CommRing A] [CommRing B] [IsDomain B]
    [Algebra k A] [Algebra k B] :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id k A)
      (IsScalarTower.toAlgHom k B (FractionRing B))) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective B (FractionRing B))

end

end Buffalo.AG.Part06
