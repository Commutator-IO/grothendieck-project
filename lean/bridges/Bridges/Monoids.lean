/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.Boolean
public import LeanPool.ToposTheoreticBridges.DeMorgan
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.CategoryTheory.SingleObj

/-!
# Topoi of `M`-sets: Boolean and De Morgan monoids

For a monoid `M`, the presheaf topos `(SingleObj M)ᵒᵖ ⥤ Type` is the topos of *right* `M`-sets:
composition in `SingleObj M` is `f ≫ g = g * f` (`SingleObj.comp_as_mul`), so a presheaf `F`
gives the action `x • m := F.map (op m) x`, which satisfies `x • (m * n) = (x • m) • n`.

Reading the two bridges `isBooleanTopos_presheaf_iff_isGroupoid` and
`isDeMorganTopos_presheaf_iff_rightOreCondition` on the one-object category `SingleObj M` gives:

* `isBooleanTopos_singleObj_iff`: the topos of right `M`-sets is Boolean iff every element of
  `M` is invertible;
* `isDeMorganTopos_singleObj_iff`: it is De Morgan iff any two elements of `M` have a common
  right multiple, `a * c = b * d` (`M` is right reversible);
* the topos is De Morgan for commutative monoids and for monoids with zero, and for the free
  monoid on one letter, but not for the free monoid on two letters, whose presheaves are the
  deterministic automata on a two-letter alphabet (`not_isDeMorganTopos_freeMonoid_two`).

The universe of `M` is `0`: `SingleObj M` has objects in `Type`, and the bridges are stated for
small categories.
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory

section Monoid

variable {M : Type} [Monoid M]

/-- A morphism of `SingleObj M` is an isomorphism iff it is a unit of `M`. -/
theorem singleObj_isIso_iff_isUnit {x y : SingleObj M} (m : x ⟶ y) :
    IsIso m ↔ IsUnit (show M from m) := by
  constructor
  · intro h
    refine isUnit_iff_exists.2 ⟨show M from inv m, ?_, ?_⟩
    · have h' := IsIso.inv_hom_id m
      rwa [SingleObj.comp_as_mul] at h'
    · have h' := IsIso.hom_inv_id m
      rwa [SingleObj.comp_as_mul] at h'
  · rintro ⟨u, hu⟩
    exact ⟨show y ⟶ x from (u⁻¹ : Mˣ), by
      simp [SingleObj.comp_as_mul, ← hu, SingleObj.id_as_one], by
      simp [SingleObj.comp_as_mul, ← hu, SingleObj.id_as_one]⟩

/-- `SingleObj M` is a groupoid iff every element of `M` is a unit. -/
theorem isGroupoid_singleObj_iff : IsGroupoid (SingleObj M) ↔ ∀ m : M, IsUnit m := by
  constructor
  · intro h m
    exact (singleObj_isIso_iff_isUnit (x := SingleObj.star M) (y := SingleObj.star M) m).1
      (h.all_isIso _)
  · intro h
    exact ⟨fun m => (singleObj_isIso_iff_isUnit m).2 (h _)⟩

/-- **Boolean `M`-sets.** The topos of right `M`-sets is Boolean iff every element of `M` is
invertible. -/
theorem isBooleanTopos_singleObj_iff :
    IsBooleanTopos ((SingleObj M)ᵒᵖ ⥤ Type) ↔ ∀ m : M, IsUnit m := by
  rw [isBooleanTopos_presheaf_iff_isGroupoid, isGroupoid_singleObj_iff]

/-- The right Ore condition on `SingleObj M`: any two elements have a common right multiple. -/
theorem rightOreCondition_singleObj_iff :
    GrothendieckTopology.RightOreCondition (SingleObj M) ↔
      ∀ a b : M, ∃ c d : M, a * c = b * d := by
  constructor
  · intro h a b
    obtain ⟨_, c, d, hcd⟩ := h (X := SingleObj.star M) (Y := SingleObj.star M)
      (Z := SingleObj.star M) a b
    exact ⟨c, d, by simpa [SingleObj.comp_as_mul] using hcd⟩
  · intro h X Y Z a b
    obtain ⟨c, d, hcd⟩ := h a b
    exact ⟨SingleObj.star M, c, d, by simpa [SingleObj.comp_as_mul] using hcd⟩

/-- **De Morgan `M`-sets.** The topos of right `M`-sets is De Morgan iff any two elements of
`M` have a common right multiple. -/
theorem isDeMorganTopos_singleObj_iff :
    IsDeMorganTopos ((SingleObj M)ᵒᵖ ⥤ Type) ↔ ∀ a b : M, ∃ c d : M, a * c = b * d := by
  rw [isDeMorganTopos_presheaf_iff_rightOreCondition, rightOreCondition_singleObj_iff]

end Monoid

/-- For a group `G`, the topos of right `G`-sets is Boolean. -/
theorem isBooleanTopos_singleObj_of_group (G : Type) [Group G] :
    IsBooleanTopos ((SingleObj G)ᵒᵖ ⥤ Type) :=
  isBooleanTopos_singleObj_iff.2 Group.isUnit

/-- For a commutative monoid `M`, the topos of `M`-sets is De Morgan. -/
theorem isDeMorganTopos_singleObj_of_commMonoid (M : Type) [CommMonoid M] :
    IsDeMorganTopos ((SingleObj M)ᵒᵖ ⥤ Type) :=
  isDeMorganTopos_singleObj_iff.2 fun a b => ⟨b, a, mul_comm a b⟩

/-- For a monoid with zero `M`, the topos of right `M`-sets is De Morgan. -/
theorem isDeMorganTopos_singleObj_of_monoidWithZero (M : Type) [MonoidWithZero M] :
    IsDeMorganTopos ((SingleObj M)ᵒᵖ ⥤ Type) :=
  isDeMorganTopos_singleObj_iff.2 fun a b => ⟨0, 0, by rw [mul_zero, mul_zero]⟩

/-- The topos of `(ℕ, +)`-sets (sets with an endomorphism) is De Morgan. -/
theorem isDeMorganTopos_singleObj_multiplicative_nat :
    IsDeMorganTopos ((SingleObj (Multiplicative ℕ))ᵒᵖ ⥤ Type) :=
  isDeMorganTopos_singleObj_of_commMonoid _

/-- The free monoid on one letter is commutative. -/
theorem freeMonoid_unit_mul_comm (a b : FreeMonoid Unit) : a * b = b * a := by
  apply FreeMonoid.ext
  rw [FreeMonoid.toList_mul, FreeMonoid.toList_mul]
  exact List.ext_getElem (by simp [Nat.add_comm]) fun _ _ _ => Subsingleton.elim _ _

/-- The topos of automata on a one-letter alphabet, presheaves on the free monoid on one
letter, is De Morgan. -/
theorem isDeMorganTopos_singleObj_freeMonoid_unit :
    IsDeMorganTopos ((SingleObj (FreeMonoid Unit))ᵒᵖ ⥤ Type) :=
  isDeMorganTopos_singleObj_iff.2 fun a b => ⟨b, a, freeMonoid_unit_mul_comm a b⟩

/-- In the free monoid on two letters, the two letters have no common right multiple. -/
theorem freeMonoid_two_of_mul_ne (c d : FreeMonoid (Fin 2)) :
    FreeMonoid.of 0 * c ≠ FreeMonoid.of 1 * d := by
  intro h
  have := congrArg FreeMonoid.toList h
  simp [FreeMonoid.toList_mul, FreeMonoid.toList_of] at this

/-- The topos of deterministic automata on a two-letter alphabet, the right `M`-sets for the
free monoid `M` on two letters, is not De Morgan. -/
theorem not_isDeMorganTopos_freeMonoid_two :
    ¬ IsDeMorganTopos ((SingleObj (FreeMonoid (Fin 2)))ᵒᵖ ⥤ Type) := by
  rw [isDeMorganTopos_singleObj_iff]
  intro h
  obtain ⟨c, d, hcd⟩ := h (FreeMonoid.of 0) (FreeMonoid.of 1)
  exact freeMonoid_two_of_mul_ne c d hcd

end LeanPool.ToposTheoreticBridges.Examples
