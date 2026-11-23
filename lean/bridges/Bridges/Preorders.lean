/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.Boolean
public import LeanPool.ToposTheoreticBridges.DeMorgan
public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.Topology.ExtremallyDisconnected
public import Mathlib.Topology.Order.UpperLowerSetTopology

import LeanPool.ToposTheoreticBridges.Morita

/-!
# Presheaves on a preorder: confluence and extremal disconnectedness

A preorder `P` is a category with a morphism `x ⟶ y` iff `x ≤ y`. The functor category
`P ⥤ Type u` is the presheaf topos on `Pᵒᵖ`; it is equivalent to the topos of sheaves on the
Alexandrov space of `P` (open sets: the upper sets), an equivalence we do not formalise.

Reading the bridges of `Boolean.lean` and `DeMorgan.lean` on `Pᵒᵖ` and on `P`:

* `isDeMorganTopos_functor_preorder_iff`: `P ⥤ Type u` is De Morgan iff `P` is *confluent*:
  whenever `x ≤ y` and `x ≤ z`, there is `w` with `y ≤ w` and `z ≤ w`;
* `isDeMorganTopos_presheaf_preorder_iff`: dually, `Pᵒᵖ ⥤ Type u` is De Morgan iff any two
  elements with a common upper bound have a common lower bound;
* `isBooleanTopos_functor_preorder_iff`, `isBooleanTopos_presheaf_preorder_iff`: either topos is
  Boolean iff the preorder is symmetric;
* `extremallyDisconnected_iff_confluent`: a direct, topos-free proof that the Alexandrov space of
  `P` is extremally disconnected (the closure of an open set is open) iff `P` is confluent;
* `extremallyDisconnected_withUpperSet_iff_isDeMorganTopos`: the resulting bridge between the
  topology of the Alexandrov space and the logic of the topos `P ⥤ Type u`;
* `moritaEquivalentCat_preorder_iff`, `moritaEquivalentCat_preorder_iff_antisymmetrization`: two
  preorders have equivalent presheaf topoi iff they are equivalent as categories, iff their
  posetal quotients (`ThinSkeleton`, or `Antisymmetrization`) are order isomorphic. The proof
  reads `moritaEquivalentCat_iff_karoubi` on preorders, which are idempotent complete since an
  idempotent of a thin category is an identity.
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory Opposite

universe u

variable (P : Type u) [Preorder P]

/-- A preorder is confluent when any two elements above a common element have a common upper
bound. -/
def IsConfluent : Prop :=
  ∀ x y z : P, x ≤ y → x ≤ z → ∃ w, y ≤ w ∧ z ≤ w

/-- The right Ore condition on the category `P`: any two elements below a common element have
a common lower bound. -/
theorem rightOreCondition_preorder_iff :
    GrothendieckTopology.RightOreCondition P ↔
      ∀ x y z : P, y ≤ x → z ≤ x → ∃ w, w ≤ y ∧ w ≤ z := by
  constructor
  · intro h x y z hy hz
    obtain ⟨w, f, g, -⟩ := h (homOfLE hy) (homOfLE hz)
    exact ⟨w, f.le, g.le⟩
  · intro h X Y Z f g
    obtain ⟨w, hy, hz⟩ := h X Y Z f.le g.le
    exact ⟨w, homOfLE hy, homOfLE hz, Subsingleton.elim _ _⟩

/-- The right Ore condition on `Pᵒᵖ` is the confluence of `P`. -/
theorem rightOreCondition_op_preorder_iff :
    GrothendieckTopology.RightOreCondition Pᵒᵖ ↔ IsConfluent P := by
  constructor
  · intro h x y z hy hz
    obtain ⟨w, f, g, -⟩ := h (homOfLE hy).op (homOfLE hz).op
    exact ⟨w.unop, f.unop.le, g.unop.le⟩
  · intro h X Y Z f g
    obtain ⟨w, hy, hz⟩ := h X.unop Y.unop Z.unop f.unop.le g.unop.le
    exact ⟨op w, (homOfLE hy).op, (homOfLE hz).op, Subsingleton.elim _ _⟩

/-- **Confluence.** The topos `P ⥤ Type u` (the sheaves on the Alexandrov space of `P`) is
De Morgan iff `P` is confluent. -/
theorem isDeMorganTopos_functor_preorder_iff :
    IsDeMorganTopos (P ⥤ Type u) ↔ IsConfluent P := by
  rw [← isDeMorganTopos_congr ((opOpEquivalence P).congrLeft (E := Type u)),
    isDeMorganTopos_presheaf_iff_rightOreCondition, rightOreCondition_op_preorder_iff]

/-- The presheaf topos `Pᵒᵖ ⥤ Type u` is De Morgan iff any two elements below a common element
have a common lower bound. -/
theorem isDeMorganTopos_presheaf_preorder_iff :
    IsDeMorganTopos (Pᵒᵖ ⥤ Type u) ↔ ∀ x y z : P, y ≤ x → z ≤ x → ∃ w, w ≤ y ∧ w ≤ z := by
  rw [isDeMorganTopos_presheaf_iff_rightOreCondition, rightOreCondition_preorder_iff]

/-- A preorder is a groupoid, as a category, iff it is symmetric. -/
theorem isGroupoid_preorder_iff : IsGroupoid P ↔ ∀ x y : P, x ≤ y → y ≤ x := by
  constructor
  · intro h x y hxy
    exact (inv (homOfLE hxy)).le
  · intro h
    exact ⟨fun f => ⟨homOfLE (h _ _ f.le), Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

/-- `Pᵒᵖ` is a groupoid iff `P` is symmetric. -/
theorem isGroupoid_op_preorder_iff : IsGroupoid Pᵒᵖ ↔ ∀ x y : P, x ≤ y → y ≤ x := by
  rw [← isGroupoid_preorder_iff]
  constructor
  · intro h
    exact ⟨fun f => ⟨(inv f.op).unop, Quiver.Hom.op_inj (by simp),
      Quiver.Hom.op_inj (by simp)⟩⟩
  · intro h
    exact ⟨fun f => ⟨(inv f.unop).op, Quiver.Hom.unop_inj (by simp),
      Quiver.Hom.unop_inj (by simp)⟩⟩

/-- The presheaf topos `Pᵒᵖ ⥤ Type u` is Boolean iff `P` is symmetric. -/
theorem isBooleanTopos_presheaf_preorder_iff :
    IsBooleanTopos (Pᵒᵖ ⥤ Type u) ↔ ∀ x y : P, x ≤ y → y ≤ x := by
  rw [isBooleanTopos_presheaf_iff_isGroupoid, isGroupoid_preorder_iff]

/-- The topos `P ⥤ Type u` is Boolean iff `P` is symmetric. -/
theorem isBooleanTopos_functor_preorder_iff :
    IsBooleanTopos (P ⥤ Type u) ↔ ∀ x y : P, x ≤ y → y ≤ x := by
  rw [← isBooleanTopos_congr ((opOpEquivalence P).congrLeft (E := Type u)),
    isBooleanTopos_presheaf_iff_isGroupoid, isGroupoid_op_preorder_iff]

/-- **Alexandrov spaces.** For the topology whose open sets are the upper sets, the closure of
every open set is open iff the preorder is confluent. -/
theorem extremallyDisconnected_iff_confluent [TopologicalSpace P] [Topology.IsUpperSet P] :
    ExtremallyDisconnected P ↔ IsConfluent P := by
  have key : (∀ U : Set P, IsOpen U → IsOpen (closure U)) ↔ IsConfluent P := by
    simp_rw [Topology.IsUpperSet.isOpen_iff_isUpperSet,
      Topology.IsUpperSet.closure_eq_lowerClosure]
    constructor
    · intro h x y z hy hz
      have hx : x ∈ (lowerClosure (Set.Ici y) : Set P) := ⟨y, le_rfl, hy⟩
      obtain ⟨w, hw, hzw⟩ := h _ (IsUpperSet.Ici y) hz hx
      exact ⟨w, hw, hzw⟩
    · rintro h U hU x y hxy ⟨u, hu, hxu⟩
      obtain ⟨w, huw, hyw⟩ := h x u y hxu hxy
      exact ⟨w, hU huw hu, hyw⟩
  exact ⟨fun h => key.1 h.open_closure, fun h => ⟨key.2 h⟩⟩

/-- **A bridge through the Alexandrov space.** The Alexandrov space of `P` is extremally
disconnected iff the topos `P ⥤ Type u` is De Morgan. -/
theorem extremallyDisconnected_withUpperSet_iff_isDeMorganTopos :
    ExtremallyDisconnected (Topology.WithUpperSet P) ↔ IsDeMorganTopos (P ⥤ Type u) := by
  rw [extremallyDisconnected_iff_confluent, isDeMorganTopos_functor_preorder_iff]
  exact ⟨fun h x y z hy hz => h (Topology.WithUpperSet.toUpperSet x)
      (Topology.WithUpperSet.toUpperSet y) (Topology.WithUpperSet.toUpperSet z) hy hz,
    fun h x y z hy hz => h x y z hy hz⟩

section Morita

open Idempotents

variable {P} {Q : Type u} [Preorder Q]

/-- A preorder is idempotent complete: every idempotent of a thin category is an identity. -/
instance isIdempotentComplete_preorder : IsIdempotentComplete P :=
  ⟨fun X _ _ => ⟨X, 𝟙 X, 𝟙 X, Category.comp_id _, Subsingleton.elim _ _⟩⟩

/-- The Karoubi envelope of a preorder is equivalent to the preorder itself. -/
noncomputable def karoubiEquivPreorder : Karoubi P ≌ P :=
  (toKaroubiEquivalence P).symm

/-- **Morita equivalence of preorders.** Two preorders have equivalent presheaf topoi iff they
are equivalent as categories. -/
theorem moritaEquivalentCat_preorder_iff : MoritaEquivalentCat P Q ↔ Nonempty (P ≌ Q) := by
  rw [moritaEquivalentCat_iff_karoubi]
  constructor
  · rintro ⟨e⟩
    exact ⟨karoubiEquivPreorder.symm.trans (e.trans karoubiEquivPreorder)⟩
  · rintro ⟨e⟩
    exact ⟨karoubiEquivPreorder.trans (e.trans karoubiEquivPreorder.symm)⟩

/-- Two preorders are equivalent as categories iff their posetal quotients are isomorphic. -/
theorem nonempty_equivalence_preorder_iff :
    Nonempty (P ≌ Q) ↔ Nonempty (ThinSkeleton P ≃o ThinSkeleton Q) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨(e.trans (ThinSkeleton.equivalence Q).symm).thinSkeletonOrderIso⟩
  · rintro ⟨φ⟩
    exact ⟨(ThinSkeleton.equivalence P).symm.trans
      (φ.equivalence.trans (ThinSkeleton.equivalence Q))⟩

/-- The thin skeleton of a preorder is its antisymmetrization. -/
noncomputable def thinSkeletonOrderIsoAntisymmetrization :
    ThinSkeleton P ≃o Antisymmetrization P (· ≤ ·) where
  toEquiv := Quotient.congr (Equiv.refl P) fun a b =>
    ⟨fun ⟨i⟩ => ⟨i.hom.le, i.inv.le⟩, fun h => ⟨⟨homOfLE h.1, homOfLE h.2,
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩⟩
  map_rel_iff' {a b} := by
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    exact ⟨fun h => ⟨homOfLE h⟩, fun ⟨f⟩ => f.le⟩

/-- **Morita equivalence of preorders.** Two preorders have equivalent presheaf topoi iff their
antisymmetrizations (posetal quotients) are order isomorphic. -/
theorem moritaEquivalentCat_preorder_iff_antisymmetrization :
    MoritaEquivalentCat P Q ↔
      Nonempty (Antisymmetrization P (· ≤ ·) ≃o Antisymmetrization Q (· ≤ ·)) := by
  rw [moritaEquivalentCat_preorder_iff, nonempty_equivalence_preorder_iff]
  exact ⟨fun ⟨φ⟩ => ⟨thinSkeletonOrderIsoAntisymmetrization.symm.trans
      (φ.trans thinSkeletonOrderIsoAntisymmetrization)⟩,
    fun ⟨φ⟩ => ⟨thinSkeletonOrderIsoAntisymmetrization.trans
      (φ.trans thinSkeletonOrderIsoAntisymmetrization.symm)⟩⟩

/-- Two partial orders have equivalent presheaf topoi iff they are order isomorphic. -/
theorem moritaEquivalentCat_partialOrder_iff {R S : Type u} [PartialOrder R] [PartialOrder S] :
    MoritaEquivalentCat R S ↔ Nonempty (R ≃o S) := by
  rw [moritaEquivalentCat_preorder_iff]
  exact ⟨fun ⟨e⟩ => ⟨e.toOrderIso⟩, fun ⟨φ⟩ => ⟨φ.equivalence⟩⟩

end Morita

end LeanPool.ToposTheoreticBridges.Examples
