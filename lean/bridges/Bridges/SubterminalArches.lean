/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.Subpresheaf
public import Mathlib.CategoryTheory.IsConnected

/-!
# Two arches read on the subterminal objects of a presheaf topos

The subterminal objects (the « ouverts ») of the presheaf topos `Cᵒᵖ ⥤ Type u` are the
subfunctors of the terminal presheaf; SGA 4 IV 8.4.4 identifies them with the sieves of `C`. Two
invariants of the topos read on them give two arches:

* `forall_subfunctor_terminal_eq_bot_or_eq_top_iff` (**two-valued**): the only subterminal
  objects are `⊥` and `⊤` iff there is an arrow `a ⟶ b` between any two objects of `C`;
* `isConnected_iff_forall_isCompl` (**connected**, after SGA 4 IV 8.7): `C` is nonempty and
  every complemented subterminal object is `⊥` or `⊤` iff `C` is connected.
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory Opposite

universe u

variable (C : Type u) [SmallCategory C]

/-- The terminal presheaf on `C`. -/
abbrev terminalPresheaf : Cᵒᵖ ⥤ Type u := (Functor.const Cᵒᵖ).obj PUnit

/-- The subterminal object of the objects that map to `b`. -/
def subterminalBelow (b : C) : Subfunctor (terminalPresheaf C) where
  obj U := {_x | Nonempty (U.unop ⟶ b)}
  map i := fun _ hx => hx.elim fun f => ⟨i.unop ≫ f⟩

/-- The subterminal object of a set of objects closed under precomposition. -/
def subterminalOfSet (p : Set C) (hp : ∀ {a b : C} (_ : a ⟶ b), b ∈ p → a ∈ p) :
    Subfunctor (terminalPresheaf C) where
  obj U := {_x | U.unop ∈ p}
  map i := fun _ hx => hp i.unop hx

variable {C}

theorem mem_of_mem_obj {S : Subfunctor (terminalPresheaf C)} {a b : C} (f : a ⟶ b)
    (h : PUnit.unit ∈ S.obj (op b)) : PUnit.unit ∈ S.obj (op a) :=
  S.map f.op h

theorem eq_top_of_mem {S : Subfunctor (terminalPresheaf C)}
    (h : ∀ a : C, PUnit.unit ∈ S.obj (op a)) : S = ⊤ := by
  ext U x
  cases x
  exact iff_of_true (h U.unop) (by simp)

theorem eq_bot_of_not_mem {S : Subfunctor (terminalPresheaf C)}
    (h : ∀ a : C, PUnit.unit ∉ S.obj (op a)) : S = ⊥ := by
  ext U x
  cases x
  exact iff_of_false (h U.unop) (by simp)

variable (C)

/-- **Two-valued arch.** The presheaf topos on `C` has no subterminal objects besides `⊥` and
`⊤` iff any two objects of `C` are joined by an arrow `a ⟶ b`. -/
theorem forall_subfunctor_terminal_eq_bot_or_eq_top_iff :
    (∀ S : Subfunctor (terminalPresheaf C), S = ⊥ ∨ S = ⊤) ↔ ∀ a b : C, Nonempty (a ⟶ b) := by
  constructor
  · intro h a b
    rcases h (subterminalBelow C b) with hS | hS
    · have hb : PUnit.unit ∈ (subterminalBelow C b).obj (op b) := ⟨𝟙 b⟩
      rw [hS] at hb
      simp at hb
    · have ha : PUnit.unit ∈ (subterminalBelow C b).obj (op a) := by
        rw [hS]
        simp
      exact ha
  · intro h S
    by_cases hS : ∃ x : C, PUnit.unit ∈ S.obj (op x)
    · obtain ⟨x, hx⟩ := hS
      exact Or.inr (eq_top_of_mem fun a => (h a x).elim fun f => mem_of_mem_obj f hx)
    · exact Or.inl (eq_bot_of_not_mem fun a ha => hS ⟨a, ha⟩)

/-- **Connected arch** (SGA 4 IV 8.7). The presheaf topos on `C` is connected and nonempty
(`C` is nonempty, and its only complemented subterminal objects are `⊥` and `⊤`) iff `C` is
connected. -/
theorem isConnected_iff_forall_isCompl :
    (Nonempty C ∧ ∀ S T : Subfunctor (terminalPresheaf C), IsCompl S T → S = ⊥ ∨ S = ⊤) ↔
      IsConnected C := by
  constructor
  · rintro ⟨⟨j₀⟩, h⟩
    refine IsConnected.of_induct (j₀ := j₀) fun p h0 h1 j => ?_
    have hdown : ∀ {a b : C} (_ : a ⟶ b), b ∈ p → a ∈ p := fun f hb => (h1 f).2 hb
    have hdown' : ∀ {a b : C} (_ : a ⟶ b), b ∈ pᶜ → a ∈ pᶜ := fun f hb ha => hb ((h1 f).1 ha)
    have hc : IsCompl (subterminalOfSet C p hdown) (subterminalOfSet C pᶜ hdown') := by
      rw [Subfunctor.isCompl_iff_forall]
      intro U
      exact isCompl_compl
    rcases h _ _ hc with hS | hS
    · have h0' : PUnit.unit ∈ (subterminalOfSet C p hdown).obj (op j₀) := h0
      rw [hS] at h0'
      simp at h0'
    · have hj : PUnit.unit ∈ (subterminalOfSet C p hdown).obj (op j) := by
        rw [hS]
        simp
      exact hj
  · intro hC
    refine ⟨inferInstance, fun S T hST => ?_⟩
    have hcompl := Subfunctor.isCompl_iff_forall.1 hST
    by_cases hS : ∃ x : C, PUnit.unit ∈ S.obj (op x)
    · obtain ⟨x, hx⟩ := hS
      refine Or.inr (eq_top_of_mem fun a => ?_)
      refine induct_on_objects {y : C | PUnit.unit ∈ S.obj (op y)} hx (fun {j₁ j₂} f => ?_) a
      constructor
      · intro h₁
        by_contra h₂
        have hT : PUnit.unit ∈ T.obj (op j₂) := by
          have := (hcompl (op j₂)).2
          rw [codisjoint_iff] at this
          have hu : PUnit.unit ∈ (S.obj (op j₂) ⊔ T.obj (op j₂)) := by rw [this]; trivial
          exact hu.resolve_left h₂
        have hT₁ : PUnit.unit ∈ T.obj (op j₁) := mem_of_mem_obj f hT
        exact Set.disjoint_left.1 (hcompl (op j₁)).1 h₁ hT₁
      · exact fun h₂ => mem_of_mem_obj f h₂
    · exact Or.inl (eq_bot_of_not_mem fun a ha => hS ⟨a, ha⟩)

end LeanPool.ToposTheoreticBridges.Examples
