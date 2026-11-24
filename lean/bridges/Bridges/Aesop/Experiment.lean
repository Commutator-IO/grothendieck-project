/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Bridges.Aesop.Registry

/-!
# How far `aesop` runs the generator

Each statement below was proved by hand in `Bridges.Monoids` or `Bridges.QuiversDeMorgan`; here
it is given to `aesop` with the rule set `Bridges` of `Bridges.Aesop.Registry` and nothing
else. A statement `aesop` does not prove is kept under `fail_if_success`, so that the file
records the boundary and the build breaks if it moves.

1. **Join and specialise** (stages 1–2): the four readings of the Boolean and De Morgan arches
   on the decks `SingleObj M` and `Paths Q`.
2. **Specialise, then close**: a corollary whose deck condition is a known fact
   (`Group.isUnit`), proved only once that fact is given as a rule.
3. **Witnesses**: corollaries whose deck condition is an existential (`a * c = b * d` with
   `c = b`, `d = a`, or `c = d = 0`): the witness has to be found.
4. **Transfer along a deck equivalence** (Morita): this rewrites in the other direction, from
   the category to the topos, then uses the invariance of the property under equivalence.
-/

public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory

universe u

/-! ## 1. Join and specialise -/

example {M : Type} [Monoid M] :
    IsBooleanTopos ((SingleObj M)ᵒᵖ ⥤ Type) ↔ ∀ m : M, IsUnit m := by
  aesop (rule_sets := [Bridges])

example {M : Type} [Monoid M] :
    IsDeMorganTopos ((SingleObj M)ᵒᵖ ⥤ Type) ↔ ∀ a b : M, ∃ c d : M, a * c = b * d := by
  aesop (rule_sets := [Bridges])

example (Q : Type (u + 1)) [Quiver.{u + 1} Q] :
    IsBooleanTopos ((Paths Q)ᵒᵖ ⥤ Type (u + 1)) ↔ ∀ v w : Q, IsEmpty (v ⟶ w) := by
  aesop (rule_sets := [Bridges])

example (Q : Type (u + 1)) [Quiver.{u + 1} Q] :
    IsDeMorganTopos ((Paths Q)ᵒᵖ ⥤ Type (u + 1)) ↔ ∀ v : Q, Subsingleton (Σ w : Q, w ⟶ v) := by
  aesop (rule_sets := [Bridges])

/-! ## 2. Specialise, then close -/

-- The deck condition `∀ m : G, IsUnit m` is not closed: `Group.isUnit` is not a `simp` lemma.
example (G : Type) [Group G] : IsBooleanTopos ((SingleObj G)ᵒᵖ ⥤ Type) := by
  fail_if_success aesop (config := { terminal := true }) (rule_sets := [Bridges])
  exact isBooleanTopos_singleObj_of_group G

-- With `Group.isUnit` added as a rule, it is.
example (G : Type) [Group G] : IsBooleanTopos ((SingleObj G)ᵒᵖ ⥤ Type) := by
  aesop (rule_sets := [Bridges]) (add safe apply Group.isUnit)

/-! ## 3. Witnesses -/

example (M : Type) [CommMonoid M] : IsDeMorganTopos ((SingleObj M)ᵒᵖ ⥤ Type) := by
  fail_if_success aesop (config := { terminal := true }) (rule_sets := [Bridges])
  exact isDeMorganTopos_singleObj_of_commMonoid M

example (M : Type) [MonoidWithZero M] : IsDeMorganTopos ((SingleObj M)ᵒᵖ ⥤ Type) := by
  fail_if_success aesop (config := { terminal := true }) (rule_sets := [Bridges])
  exact isDeMorganTopos_singleObj_of_monoidWithZero M

example : ¬ IsDeMorganTopos ((SingleObj (FreeMonoid (Fin 2)))ᵒᵖ ⥤ Type) := by
  fail_if_success aesop (config := { terminal := true }) (rule_sets := [Bridges])
  exact not_isDeMorganTopos_freeMonoid_two

/-! ## 4. Transfer along a deck equivalence -/

-- With the registry alone, `aesop` does not see that a Morita equivalence transfers the
-- condition: the arch would have to be used from right to left.
example {C D : Type u} [SmallCategory C] [SmallCategory D] (h : MoritaEquivalentCat C D) :
    IsGroupoid C ↔ IsGroupoid D := by
  fail_if_success aesop (config := { terminal := true }) (rule_sets := [Bridges])
  exact isGroupoid_iff_of_moritaEquivalentCat h

/-- The arch read from right to left, as a lemma of its own: Aesop's `simp` rules take no `←`
(Aesop issue 234), and both directions in one `simp` set would loop. -/
theorem isGroupoid_iff_isBooleanTopos_presheaf (C : Type u) [SmallCategory C] :
    IsGroupoid C ↔ IsBooleanTopos (Cᵒᵖ ⥤ Type u) :=
  (isBooleanTopos_presheaf_iff_isGroupoid C).symm

-- With the reversed arch, the unfolding of `MoritaEquivalentCat` and the invariance of
-- Booleanness under equivalence as a forward rule, `aesop` does the transfer.
example {C D : Type u} [SmallCategory C] [SmallCategory D] (h : MoritaEquivalentCat C D) :
    IsGroupoid C ↔ IsGroupoid D := by
  aesop (add norm simp isGroupoid_iff_isBooleanTopos_presheaf,
    norm unfold MoritaEquivalentCat, safe cases Nonempty, safe forward isBooleanTopos_congr)

end LeanPool.ToposTheoreticBridges.Examples
