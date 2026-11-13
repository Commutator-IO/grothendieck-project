import Mathlib

/-!
# The Grothendieck group of a commutative monoid: elements as fractions, flatness of `M → G(M)`

Declarations a proof of this repository (`Quillen.Notebook1971_4`, a monoid and its group
completion) needed and that Mathlib does not have at the pinned revision. Mathlib defines
`Algebra.GrothendieckGroup M` as `Localization ⊤` and has its universal property, but no API
stating what its elements and equalities look like in terms of `GrothendieckGroup.of`; these
follow from `Submonoid.LocalizationMap.surj` and `Submonoid.LocalizationMap.eq_iff_exists`. The
additive versions (`Algebra.GrothendieckAddGroup`) come from `to_additive`.

* `Algebra.GrothendieckGroup.exists_of_mul_eq_of`: every `x` satisfies `of b * x = of a`;
* `Algebra.GrothendieckGroup.exists_of_mul_eq_and_of_mul_eq`: two elements are translates
  `of m₁ * g`, `of m₂ * g` of a common one (a common denominator);
* `Algebra.GrothendieckGroup.of_eq_of_iff`: `of m₁ = of m₂ ↔ ∃ c, c * m₁ = c * m₂`;
* `Algebra.GrothendieckGroup.representablyFlat_toFunctor_of`: the functor
  `SingleObj M ⥤ SingleObj (GrothendieckGroup M)` induced by `of` is representably flat, and
  `Algebra.GrothendieckGroup.final_toFunctor_of`: hence final.

Drop a declaration once Mathlib has it.
-/

open CategoryTheory

namespace Algebra.GrothendieckGroup

universe u

variable {M : Type u} [CommMonoid M]

/-- Every element of the Grothendieck group becomes an element of `M` after multiplication by an
element of `M`. -/
@[to_additive /-- Every element of the Grothendieck group becomes an element of `M` after adding
an element of `M`. -/]
theorem exists_of_mul_eq_of (x : GrothendieckGroup M) :
    ∃ b a : M, of b * x = of a := by
  obtain ⟨⟨a, b⟩, h⟩ := (Localization.monoidOf (⊤ : Submonoid M)).surj x
  exact ⟨b, a, (mul_comm _ _).trans h⟩

/-- Any two elements of the Grothendieck group are translates of a common element by elements
of `M`. -/
@[to_additive /-- Any two elements of the Grothendieck group are translates of a common element
by elements of `M`. -/]
theorem exists_of_mul_eq_and_of_mul_eq (g₁ g₂ : GrothendieckGroup M) :
    ∃ (g : GrothendieckGroup M) (m₁ m₂ : M), of m₁ * g = g₁ ∧ of m₂ * g = g₂ := by
  obtain ⟨b₁, a₁, h₁⟩ := exists_of_mul_eq_of g₁
  obtain ⟨b₂, a₂, h₂⟩ := exists_of_mul_eq_of g₂
  refine ⟨(of (b₁ * b₂))⁻¹, b₂ * a₁, b₁ * a₂, ?_, ?_⟩ <;>
    simp only [map_mul, ← h₁, ← h₂, mul_inv_eq_iff_eq_mul] <;> ac_rfl

/-- Two elements of `M` have the same image in the Grothendieck group iff they become equal after
multiplication by an element of `M`. -/
@[to_additive /-- Two elements of `M` have the same image in the Grothendieck group iff they
become equal after adding an element of `M`. -/]
theorem of_eq_of_iff {m₁ m₂ : M} : of m₁ = of m₂ ↔ ∃ c : M, c * m₁ = c * m₂ :=
  (Localization.monoidOf (⊤ : Submonoid M)).eq_iff_exists.trans
    ⟨fun ⟨c, hc⟩ ↦ ⟨c, hc⟩, fun ⟨c, hc⟩ ↦ ⟨⟨c, Submonoid.mem_top c⟩, hc⟩⟩

/-- **The map from a commutative monoid to its Grothendieck group is representably flat**: for
the unique object `X`, the category `X / of` of elements of `G(M)` with arrows given by `M`
acting by translation is cofiltered. -/
theorem representablyFlat_toFunctor_of : RepresentablyFlat (of (M := M)).toFunctor where
  cofiltered X :=
    { cone_objs Y₁ Y₂ := by
        obtain ⟨g, m₁, m₂, h₁, h₂⟩ := exists_of_mul_eq_and_of_mul_eq (M := M) Y₁.hom Y₂.hom
        exact ⟨StructuredArrow.mk (Y := SingleObj.star M) g, StructuredArrow.homMk m₁ h₁,
          StructuredArrow.homMk m₂ h₂, trivial⟩
      cone_maps Y Y' φ ψ := by
        have hφ := StructuredArrow.w φ
        have hψ := StructuredArrow.w ψ
        obtain ⟨c, hc⟩ := (of_eq_of_iff (M := M) (m₁ := φ.right) (m₂ := ψ.right)).1
          (mul_right_cancel (hφ.trans hψ.symm))
        refine ⟨StructuredArrow.mk (Y := SingleObj.star M) ((of c)⁻¹ * Y.hom),
          StructuredArrow.homMk c (mul_inv_cancel_left (of c) Y.hom),
          StructuredArrow.hom_ext _ _ ?_⟩
        change φ.right * c = ψ.right * c
        rw [mul_comm, hc, mul_comm]
      nonempty := ⟨StructuredArrow.mk (Y := SingleObj.star M) (1 : GrothendieckGroup M)⟩ }

/-- The functor `SingleObj M ⥤ SingleObj (GrothendieckGroup M)` induced by `of` is final
(`CategoryTheory.final_of_representablyFlat`). -/
theorem final_toFunctor_of : (of (M := M)).toFunctor.Final :=
  have := representablyFlat_toFunctor_of (M := M)
  final_of_representablyFlat _

end Algebra.GrothendieckGroup
