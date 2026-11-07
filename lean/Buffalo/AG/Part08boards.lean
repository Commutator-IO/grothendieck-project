import Buffalo.AG.Part08

/-!
# Buffalo, algebraic geometry, part 08: blackboards

Counterexamples for the board items of `public/buffalo-boards/` (videos `Oqhr-Gt66es` from 37143 s
and `vuys5SNs2eQ` to 15735 s) that misstate mathematics; the status of every checked item is in
`docs/buffalo-ag/lean/Part08-boards.json`.
-/

open PrimeSpectrum

namespace Buffalo.AG.Part08

noncomputable section

/-- `ℤ/2²`, a local ring. -/
abbrev A4 := ZMod (2 ^ 2)

instance : Algebra A4 (ZMod 2) := (ZMod.castHom (by norm_num) (ZMod 2)).toAlgebra

/-- Board `vuys5SNs2eQ-0000`, item at 2099 s: for a local homomorphism of local rings, surjectivity of
`Spec B → Spec A` does not imply flatness: `ℤ/4 → ℤ/2` is local, surjective on spectra, and not flat
(a finite flat module over a local ring is free, and `4ⁿ ≠ 2`). -/
theorem board_cex_2099 :
    IsLocalHom (algebraMap A4 (ZMod 2)) ∧ Function.Surjective (comap (algebraMap A4 (ZMod 2))) ∧
      ¬ Module.Flat A4 (ZMod 2) := by
  refine ⟨inferInstance, fun y => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩, ?_⟩
  intro h
  have : Module.Finite A4 (ZMod 2) :=
    Module.Finite.of_surjective (Algebra.linearMap A4 (ZMod 2)) (ZMod.ringHom_surjective _)
  have : Module.Free A4 (ZMod 2) := Module.free_of_flat_of_isLocalRing
  have h1 := Module.card_fintype (Module.Free.chooseBasis A4 (ZMod 2))
  simp only [ZMod.card] at h1
  rcases Nat.eq_zero_or_pos (Fintype.card (Module.Free.ChooseBasisIndex A4 (ZMod 2))) with h0 | h0
  · rw [h0] at h1; simp at h1
  · have : 4 ≤ (2 ^ 2) ^ Fintype.card (Module.Free.ChooseBasisIndex A4 (ZMod 2)) :=
      le_self_pow₀ (by norm_num) h0.ne'
    omega

/-- Board `vuys5SNs2eQ-0000`, item at 712 s: equality of fibre dimensions alone does not give
flatness: the line `V(y) ⊂ 𝔸²` (all of whose nonempty fibres are points) is not flat over `𝔸²`,
since `y` kills `1` in `k[x,y]/(y)`. -/
theorem board_cex_712 (k : Type*) [Field k] :
    ¬ Module.Flat (MvPolynomial (Fin 2) k)
      (MvPolynomial (Fin 2) k ⧸ (Ideal.span {MvPolynomial.X (1 : Fin 2)} : Ideal (MvPolynomial (Fin 2) k))) := by
  intro h
  have := (Module.isTorsionFree_iff_smul_eq_zero.1 (inferInstance :
    Module.IsTorsionFree (MvPolynomial (Fin 2) k)
      (MvPolynomial (Fin 2) k ⧸ (Ideal.span {MvPolynomial.X (1 : Fin 2)} : Ideal (MvPolynomial (Fin 2) k)))))
    (MvPolynomial.X 1) 1 (by
      rw [← map_one (Ideal.Quotient.mk _), ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
        smul_eq_mul, mul_one, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_span_singleton_self _)
  rcases this with h0 | h0
  · exact MvPolynomial.X_ne_zero _ h0
  · have hne : Ideal.span {MvPolynomial.X (1 : Fin 2)} ≠ (⊤ : Ideal (MvPolynomial (Fin 2) k)) := by
      rw [Ne, Ideal.span_singleton_eq_top]
      intro hu
      have := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
      simp [MvPolynomial.totalDegree_X] at this
    have := Ideal.Quotient.nontrivial_iff.2 hne
    exact one_ne_zero h0

end

end Buffalo.AG.Part08
