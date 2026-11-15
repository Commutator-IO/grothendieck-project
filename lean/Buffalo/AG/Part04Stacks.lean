import Buffalo.AG.Part04d
import StacksFrontier.Algebra.Module.Projective.Invertible

/-!
# Buffalo, algebraic geometry, part 04: invertible modules are the locally free modules of rank one

Entry `thSz9ZHDK9o-23907` of `docs/buffalo-ag/index.tex`, of which `Part04d.lean` proves only the
direction « invertible ⇒ finite projective and free of rank one at every prime »: the converse was
a Mathlib TODO at `715a03a`. It is completed here with the vendored AxiomMath/Stacks file
`StacksFrontier/Algebra/Module/Projective/Invertible.lean` (Apache-2.0, see
`lean/Stacks/NOTICE.md`), whose `Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse`
(Stacks tag 0B8I) states the equivalence with the rank read through Mathlib's `Module.rankAtStalk`.
-/

open Module

universe u

namespace Buffalo.AG.Part04

/-- thSz9ZHDK9o-23907 (6:38:27) [prop] An `A`-module `L` is invertible if and only if it is
finitely generated projective and `L_𝔭` is free of rank `1` over `A_𝔭` for every prime `𝔭`.
Stacks tag 0B8I for the converse. -/
theorem prop_23907_iff (A L : Type u) [CommRing A] [AddCommGroup L] [Module A L] :
    Module.Invertible A L ↔
      Module.Finite A L ∧ Projective A L ∧ ∀ (p : Ideal A) [p.IsPrime],
        Nonempty (LocalizedModule p.primeCompl L ≃ₗ[Localization.AtPrime p]
          Localization.AtPrime p) := by
  have h := (Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse.{u, u, u}
    A L).1
  constructor
  · intro hL
    exact ⟨inferInstance, inferInstance, fun p _ => (prop_23907 A L p).2.2⟩
  · rintro ⟨hf, hp, hloc⟩
    have h12 : (Module.Finite A L ∧ Projective A L ∧
        rankAtStalk L = Function.const (PrimeSpectrum A) 1) ↔ Module.Invertible A L := h.out 1 2
    refine h12.1 ⟨hf, hp, funext fun p => ?_⟩
    obtain ⟨e⟩ := hloc p.asIdeal
    simp only [Function.const_apply, Module.rankAtStalk, e.finrank_eq, Module.finrank_self]

end Buffalo.AG.Part04
