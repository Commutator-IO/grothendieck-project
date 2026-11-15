import Buffalo.AG.Part05b
import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability

/-!
# Buffalo, algebraic geometry, part 05: the relative spectrum of a quasi-coherent algebra

Entries `thSz9ZHDK9o-33684` and `thSz9ZHDK9o-33941` of `docs/buffalo-ag/index.tex`, which
`Part05b.lean` treats over an affine base only, Mathlib (at `715a03a`) having no quasi-coherent
algebras and no relative spectrum. They are completed here with the vendored AxiomMath/Stacks
files of `StacksFrontier/AlgebraicGeometry/RelativeSpec/` and their imports (Apache-2.0, see
`lean/Stacks/NOTICE.md`):

* a *relative spectrum situation* `s` (`Stacks.RelativeSpec.RelativeSpecSituation`, tag 01LM) is
  a scheme `S = s.base` with a quasi-coherent sheaf `𝒜 = s.algebra` of commutative
  `𝒪_S`-algebras;
* `Stacks.RelativeSpec.relativeSpecFunctor s` sends `T` to the pairs `(f : T ⟶ S, 𝒜 ⟶ f_*𝒪_T)`
  of a morphism and a map of `𝒪_S`-algebras, which by adjunction are the `𝒪_T`-algebra maps
  `f^*𝒜 ⟶ 𝒪_T` of the lecture;
* the scheme `(gluedSpectrum s).scheme`, glued from the `Spec Γ(U, 𝒜)` over the affine opens
  `U ⊆ S`, represents it (tags 01LU, 01LV), and its restriction over every affine open `U` is
  `Spec Γ(U, 𝒜)` (the cartesian squares of the gluing, tag 01LP).
-/

open AlgebraicGeometry CategoryTheory Limits Stacks.RelativeSpec

universe u

namespace Buffalo.AG.Part05

/-- thSz9ZHDK9o-33684 (9:21:24) [def] For a quasi-coherent `𝒪_S`-algebra `𝒜`, the functor
`Spec(𝒜) : S' ↦ {(f : S' ⟶ S, 𝒜 ⟶ f_*𝒪_{S'})}` (Stacks' `relativeSpecFunctor`); over an affine
base it is the functor of points of `Spec A` (`def_33684`). -/
noncomputable abbrev def_33684_relative (s : RelativeSpecSituation.{u}) :
    Scheme.{u}ᵒᵖ ⥤ Type u :=
  relativeSpecFunctor s

/-- thSz9ZHDK9o-33941 (9:25:41) [prop] The functor `Spec(𝒜)` of a quasi-coherent
`𝒪_S`-algebra is representable by an `S`-scheme `π : X ⟶ S`, and over every affine open
`U ⊆ S` the inverse image `π⁻¹(U)` is `Spec Γ(U, 𝒜)`: the chart `Spec Γ(U, 𝒜) ⟶ X` and the
inclusion `U ⟶ S` form a cartesian square over `π`. Stacks tags 01LP, 01LU. (That the functor
is a Zariski sheaf, which follows from representability, is not restated.) -/
theorem prop_33941_relative (s : RelativeSpecSituation.{u}) :
    (def_33684_relative s).IsRepresentable ∧
      Nonempty ((def_33684_relative s).RepresentableBy (gluedSpectrum s).scheme) ∧
      ∀ U : s.base.affineOpens,
        IsPullback ((gluedSpectrum s).chart U) (specSectionsToOpen s U) (gluedSpectrum s).toBase
          U.1.ι :=
  ⟨relativeSpecFunctor_isRepresentable s, ⟨relativeSpecRepresentableBy s⟩,
    (gluedSpectrum s).chart_isPullback⟩

end Buffalo.AG.Part05
