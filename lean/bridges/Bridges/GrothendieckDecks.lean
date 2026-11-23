/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Bridges.PreorderPresheaves
public import Bridges.SubterminalArches
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.SingleObj

/-!
# The decks of Grothendieck's notes, read with the subterminal and spatial arches

Three decks that Grothendieck's working notes (Montpellier) use, read with the arches of
`SubterminalArches.lean` (two-valued, connected) and `PreorderPresheaves.lean` (spatial):

* the simplex category `Δ`, the first test category of *Pursuing Stacks* (folders 108, 118):
  simplicial sets form a two-valued, connected topos that is not the presheaf topos of a
  preorder (`simplexCategory_twoValued`, `simplexCategory_isConnected`,
  `simplexCategory_not_spatial`);
* a group `G` as a one-object groupoid, whose presheaf topos is `B G` (folder 161-6, p. 22): two
  valued and connected, and the presheaf topos of a preorder iff `G` is trivial
  (`singleObj_twoValued`, `singleObj_isConnected`, `singleObj_spatial_iff`);
* an ordered set `I`, whose presheaf topos `I^∧` is `Top(I)` (folder 37, p. 48; folder 161-3,
  p. 26): two-valued iff any two elements are comparable both ways (`preorder_twoValued_iff`).
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory

/-- A category with an arrow between any two objects is connected as soon as it is nonempty. -/
theorem isConnected_of_forall_nonempty_hom (C : Type*) [Category C] [Nonempty C]
    (h : ∀ a b : C, Nonempty (a ⟶ b)) : IsConnected C :=
  zigzag_isConnected fun a b => (h a b).elim fun f => Zigzag.of_hom f

section Simplex

/-- There is a (constant) map between any two objects of `Δ`. -/
theorem simplexCategory_nonempty_hom (a b : SimplexCategory) : Nonempty (a ⟶ b) :=
  ⟨SimplexCategory.const a b 0⟩

/-- **Simplicial sets form a two-valued topos.** -/
theorem simplexCategory_twoValued (S : Subfunctor (terminalPresheaf SimplexCategory)) :
    S = ⊥ ∨ S = ⊤ :=
  (forall_subfunctor_terminal_eq_bot_or_eq_top_iff SimplexCategory).2
    simplexCategory_nonempty_hom S

/-- **Simplicial sets form a connected topos.** -/
theorem simplexCategory_isConnected : IsConnected SimplexCategory :=
  haveI : Nonempty SimplexCategory := ⟨SimplexCategory.mk 0⟩
  isConnected_of_forall_nonempty_hom SimplexCategory simplexCategory_nonempty_hom

/-- `Δ` is not thin: the two vertices of `[1]` are two maps `[0] ⟶ [1]`. -/
theorem simplexCategory_not_isThin : ¬ Quiver.IsThin SimplexCategory := by
  intro h
  have h01 := congrArg (fun f : SimplexCategory.mk 0 ⟶ SimplexCategory.mk 1 =>
    (SimplexCategory.Hom.toOrderHom f) 0)
    (@Subsingleton.elim _ (h _ _) (SimplexCategory.const _ _ 0) (SimplexCategory.const _ _ 1))
  simp [SimplexCategory.const] at h01

/-- **Simplicial sets are not the presheaves on a preorder**, so not the sheaves on an
Alexandrov space. -/
theorem simplexCategory_not_spatial :
    ¬ ∃ (P : Type) (_ : Preorder P), MoritaEquivalentCat SimplexCategory P :=
  fun h => simplexCategory_not_isThin
    ((exists_preorder_moritaEquivalentCat_iff_isThin SimplexCategory).1 h)

end Simplex

section Group

variable (G : Type) [Group G]

/-- **`B G` is two-valued** (SGA 4 IV 8.4.3). -/
theorem singleObj_twoValued (S : Subfunctor (terminalPresheaf (SingleObj G))) :
    S = ⊥ ∨ S = ⊤ :=
  (forall_subfunctor_terminal_eq_bot_or_eq_top_iff (SingleObj G)).2
    (fun _ _ => ⟨(1 : G)⟩) S

/-- **`B G` is connected.** -/
theorem singleObj_isConnected : IsConnected (SingleObj G) :=
  isConnected_of_forall_nonempty_hom (SingleObj G) fun _ _ => ⟨(1 : G)⟩

/-- **`B G` is the presheaf topos of a preorder iff `G` is trivial.** -/
theorem singleObj_spatial_iff :
    (∃ (P : Type) (_ : Preorder P), MoritaEquivalentCat (SingleObj G) P) ↔ Subsingleton G := by
  rw [exists_preorder_moritaEquivalentCat_iff_isThin]
  exact ⟨fun h => h (SingleObj.star G) (SingleObj.star G), fun h _ _ => h⟩

end Group

section Order

variable (I : Type) [Preorder I]

/-- **`I^∧` is two-valued iff any two elements of `I` are comparable both ways**, i.e. iff the
posetal quotient of `I` has at most one point. -/
theorem preorder_twoValued_iff :
    (∀ S : Subfunctor (terminalPresheaf I), S = ⊥ ∨ S = ⊤) ↔ ∀ a b : I, a ≤ b := by
  rw [forall_subfunctor_terminal_eq_bot_or_eq_top_iff]
  exact ⟨fun h a b => (h a b).elim fun f => f.le, fun h a b => ⟨homOfLE (h a b)⟩⟩

end Order

end LeanPool.ToposTheoreticBridges.Examples
