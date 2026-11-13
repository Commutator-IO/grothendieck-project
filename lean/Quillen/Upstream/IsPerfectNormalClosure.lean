import Mathlib.GroupTheory.IsPerfect

/-!
# The normal closure of a perfect subgroup is perfect

Declarations a proof of this repository (`Quillen.Notebook1968_15`, killing a perfect subgroup
of the fundamental group) needed and that Mathlib does not have at the pinned revision: the
normal closure of a perfect subgroup is perfect. It extends `Mathlib/GroupTheory/IsPerfect.lean`;
drop the declaration once Mathlib has it.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- The normal closure of a perfect subgroup is perfect: each conjugate of `H` is perfect, hence
lies in the commutator subgroup of the normal closure, which is normal. -/
theorem isPerfect_normalClosure (H : Subgroup G) [Group.IsPerfect H] :
    Group.IsPerfect (normalClosure (H : Set G)) := by
  rw [isPerfect_iff]
  refine le_antisymm (commutator_le_left _ _) (normalClosure_le_normal fun h hh => ?_)
  rw [← (commutator_eq_self : ⁅H, H⁆ = H)] at hh
  exact commutator_mono le_normalClosure le_normalClosure hh

end Subgroup
