/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Bridges.Preorders
public import Mathlib.CategoryTheory.Skeletal

import LeanPool.ToposTheoreticBridges.Morita

/-!
# When is a presheaf topos the presheaf topos of a preorder?

Grothendieck, in an undated manuscript note on topoi (Montpellier, folder 161-3, p. 26), lists
equivalent conditions on a topos `E` (to be equivalent both to the topos of a space and to a
presheaf topos; to be equivalent to the presheaf topos of an ordered set; ...) and asks to prove
that the presheaf topos of a small category `C` satisfies them iff `C` is preordered.

* `exists_preorder_moritaEquivalentCat_iff_isThin`: the presheaf topos of `C` is equivalent to
  the presheaf topos of some preorder iff `C` is thin.

The proof reads the Morita bridge `moritaEquivalentCat_iff_karoubi` on the deck of preorders: a
preorder is its own Karoubi envelope (`karoubiEquivPreorder`), and `C` embeds fully faithfully in
its Karoubi envelope, so it is thin when the envelope is. Conversely a thin category is
equivalent to its thin skeleton, a partial order.
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory Idempotents

universe u

variable (C : Type u) [SmallCategory C]

/-- A thin category has the presheaf topos of its thin skeleton. -/
theorem moritaEquivalentCat_thinSkeleton [Quiver.IsThin C] :
    MoritaEquivalentCat C (ThinSkeleton C) :=
  ⟨(ThinSkeleton.equivalence C).symm.op.congrLeft⟩

/-- **Grothendieck, folder 161-3, p. 26.** The presheaf topos of a small category is the
presheaf topos of a preorder iff the category is thin. -/
theorem exists_preorder_moritaEquivalentCat_iff_isThin :
    (∃ (P : Type u) (_ : Preorder P), MoritaEquivalentCat C P) ↔ Quiver.IsThin C := by
  constructor
  · rintro ⟨P, _, h⟩
    obtain ⟨e⟩ := karoubi_of_moritaEquivalentCat h
    intro X Y
    exact ⟨fun f g => (toKaroubi C ⋙ (e.trans karoubiEquivPreorder).functor).map_injective
      (Subsingleton.elim _ _)⟩
  · intro h
    exact ⟨ThinSkeleton C, inferInstance, @moritaEquivalentCat_thinSkeleton C _ h⟩

end LeanPool.ToposTheoreticBridges.Examples
