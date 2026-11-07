import Buffalo.Groupes.Part01

/-!
# Buffalo, algebraic groups, Part 01: board items not covered by the index

Items of the reconstructed blackboards `public/buffalo-boards/_lTf_L0yvrU-*.json` in the time
range of Part 01 that no index entry formalises. Statuses in
`docs/buffalo-groupes/lean/Part01-boards.json`.
-/

namespace Buffalo.Groupes.Part01

open TensorProduct Polynomial

universe u

variable (k : Type u) [CommRing k]

/-- Board `_lTf_L0yvrU-5096`, t = 5486 (exercise): `Hom_𝒪(W(M), V(N))` is representable without
conditions: at each `A`, `Hom_A(A ⊗ M, Hom_k(N, A)) ≃ Hom_k(M ⊗ N, A) = V(M ⊗ N)(A)`. -/
noncomputable def homWV (M N A : Type u) [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k N] [CommRing A] [Algebra k A] :
    (A ⊗[k] M →ₗ[A] (N →ₗ[k] A)) ≃ₗ[k] (M ⊗[k] N →ₗ[k] A) :=
  ((LinearMap.liftBaseChangeEquiv A).symm.restrictScalars k).trans
    (TensorProduct.lift.equiv (RingHom.id k) M N A)

/-- Board `_lTf_L0yvrU-3729`, t = 4450: in characteristic `p` an additive endomorphism of `𝔾_a`
need not be linear: `X^p` is additive but (for `k ≠ 0`) not of the form `c X`. -/
theorem frobenius_additive_not_linear [Nontrivial k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    IsAdditivePoly k (X ^ p) ∧ ∀ c : k, (X ^ p : k[X]) ≠ C c * X := by
  refine ⟨(isAdditivePoly_iff k p _).mpr fun n hn ↦ ⟨1, ?_⟩, fun c h ↦ ?_⟩
  · rw [coeff_X_pow] at hn
    split_ifs at hn with h
    · rw [h, pow_one]
    · exact absurd rfl hn
  · have := congrArg (fun q : k[X] ↦ q.coeff p) h
    have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
    simp [coeff_X_pow, coeff_C_mul, coeff_X, Ne.symm hp1] at this

end Buffalo.Groupes.Part01
