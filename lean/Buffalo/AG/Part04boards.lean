import Buffalo.AG.Part04

/-!
# Buffalo, algebraic geometry, part 04: board items not covered by the index

Claims on the reconstructed blackboards `public/buffalo-boards/thSz9ZHDK9o-*.json`
(1:39:49–6:59:05) that no index entry of part 04 formalises, and the counterexamples behind the
corrections of the boards. Status in `docs/buffalo-ag/lean/Part04-boards.json`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace Buffalo.AG.Part04

/-- Board thSz9ZHDK9o-5786, t = 7027 [m] (corrected) The criterion "`f` or `1 - f` invertible for
every `f`" characterises local rings only among nonzero rings: the zero ring satisfies it and is
not local. -/
theorem board_7027 :
    (∀ f : PUnit.{u + 1}, IsUnit f ∨ IsUnit (1 - f)) ∧ ¬ IsLocalRing PUnit.{u + 1} :=
  ⟨fun f => Or.inl (isUnit_of_subsingleton f), fun h => not_nontrivial PUnit h.toNontrivial⟩

/-- Board thSz9ZHDK9o-5786, t = 7502 [p] If `f̄ ≠ 0` in `κ(𝔭)`, i.e. `f ∉ 𝔭`, then `g/f` is the
inverse of `f/g` in `A_𝔭`. -/
theorem board_7502 {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] (f g : p.primeCompl) :
    IsLocalization.mk' (Localization.AtPrime p) (f : A) g *
      IsLocalization.mk' (Localization.AtPrime p) (g : A) f = 1 :=
  IsLocalization.mk'_mul_mk'_eq_one f g

/-- Board thSz9ZHDK9o-5786, t = 7772 [p] `M ↦ M^~` is fully faithful (mathlib); exactness and the
compatibilities with colimits, `⊗` and `𝓗om` are not formalised. -/
noncomputable def board_7772 (A : CommRingCat.{u}) : (tilde.functor A).FullyFaithful :=
  tilde.fullyFaithfulFunctor

end Buffalo.AG.Part04
