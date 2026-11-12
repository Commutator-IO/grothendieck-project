import Mathlib

/-!
# Quillen, notebook 1975-21, pp. 41-48: Birkhoff duality on morphisms

Daniel Quillen's research notebook 1975-21 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201975/1975-21.pdf>) uses, on
pp. 41-48, that a lattice homomorphism between lattices of order ideals of finite posets comes
from a unique monotone map between the posets, in the opposite direction: Birkhoff's
duality between finite posets and finite distributive lattices, on morphisms.

Mathlib has Birkhoff's representation on objects (`Mathlib/Order/Birkhoff.lean`, with a « TODO:
extend to morphisms »). This file proves the statement on morphisms. For a finite partial order
`α` and any preorder `β`:

* `comap f`: the preimage `Z ↦ f⁻¹(Z)` along a monotone `f : β → α`, a bounded lattice
  homomorphism `LowerSet α → LowerSet β`;
* `exists_unique_comap`: **the statement**: every bounded lattice homomorphism
  `u : LowerSet α → LowerSet β` is `comap f` for a unique monotone `f : β → α`;
* `comap_injective`: `comap` is injective on monotone maps.

Only `β`'s preorder is used, and `α` need only be finite; the functoriality and the categorical
equivalence `FinPartOrdᵒᵖ ≌ FinBddDistLat` are not formalised.
-/

namespace Quillen.Notebook1975_21

variable {α β : Type*}

section comap

variable [Preorder α] [Preorder β]

/-- The preimage of a lower set along a monotone map, as a bounded lattice homomorphism. -/
def comap (f : β →o α) : BoundedLatticeHom (LowerSet α) (LowerSet β) where
  toFun Z := ⟨f ⁻¹' Z, fun _ _ h hb => Z.lower (f.mono h) hb⟩
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl

@[simp]
theorem mem_comap (f : β →o α) (Z : LowerSet α) (b : β) : b ∈ comap f Z ↔ f b ∈ Z :=
  Iff.rfl

end comap

section main

variable [PartialOrder α] [Fintype α] [Preorder β]

omit [PartialOrder α] [Fintype α] [Preorder β] in
theorem mem_finset_sup {γ ι : Type*} [Preorder γ] (s : Finset ι) (g : ι → LowerSet γ) (b : γ) :
    b ∈ s.sup g ↔ ∃ i ∈ s, b ∈ g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sup_insert, ih]

open Classical in
omit [Preorder β] in
theorem eq_sup_Iic (Z : LowerSet α) :
    Z = (Finset.univ.filter (· ∈ Z)).sup LowerSet.Iic := by
  ext a
  simp only [SetLike.mem_coe, mem_finset_sup, Finset.mem_filter, Finset.mem_univ, true_and,
    LowerSet.mem_Iic_iff]
  exact ⟨fun h => ⟨a, h, le_rfl⟩, fun ⟨c, hc, hac⟩ => Z.lower hac hc⟩

variable (u : BoundedLatticeHom (LowerSet α) (LowerSet β))

open Classical in
theorem mem_iff_exists (Z : LowerSet α) (b : β) :
    b ∈ u Z ↔ ∃ a ∈ Z, b ∈ u (LowerSet.Iic a) := by
  conv_lhs => rw [eq_sup_Iic Z, map_finset_sup]
  simp [mem_finset_sup]

theorem exists_mem (b : β) : ∃ a, b ∈ u (LowerSet.Iic a) := by
  have : b ∈ u ⊤ := by rw [map_top]; trivial
  obtain ⟨a, -, ha⟩ := (mem_iff_exists u ⊤ b).mp this
  exact ⟨a, ha⟩

theorem exists_le_le (b : β) {a a' : α} (h : b ∈ u (LowerSet.Iic a))
    (h' : b ∈ u (LowerSet.Iic a')) : ∃ c, c ≤ a ∧ c ≤ a' ∧ b ∈ u (LowerSet.Iic c) := by
  have : b ∈ u (LowerSet.Iic a ⊓ LowerSet.Iic a') := by
    rw [map_inf]; exact ⟨h, h'⟩
  obtain ⟨c, ⟨hc, hc'⟩, hb⟩ := (mem_iff_exists u _ b).mp this
  exact ⟨c, hc, hc', hb⟩

/-- `f b` is the least `a` with `b ∈ u(↓a)`. -/
noncomputable def least (b : β) : α :=
  (wellFounded_lt.has_min {a | b ∈ u (LowerSet.Iic a)} (exists_mem u b)).choose

theorem least_mem (b : β) : b ∈ u (LowerSet.Iic (least u b)) :=
  (wellFounded_lt.has_min {a | b ∈ u (LowerSet.Iic a)} (exists_mem u b)).choose_spec.1

theorem least_le (b : β) {a : α} (h : b ∈ u (LowerSet.Iic a)) : least u b ≤ a := by
  obtain ⟨c, hc, hca, hb⟩ := exists_le_le u b (least_mem u b) h
  have hmin := (wellFounded_lt.has_min {a | b ∈ u (LowerSet.Iic a)}
    (exists_mem u b)).choose_spec.2 c hb
  have : c = least u b := by
    by_contra hne
    exact hmin (lt_of_le_of_ne hc hne)
  exact this ▸ hca

theorem least_mono : Monotone (least u) := fun b' b h =>
  least_le u b' ((u (LowerSet.Iic (least u b))).lower h (least_mem u b))

/-- The monotone map `β → α` attached to `u`. -/
noncomputable def dual : β →o α := ⟨least u, least_mono u⟩

theorem comap_dual : comap (dual u) = u := by
  ext Z b
  simp only [SetLike.mem_coe, mem_comap]
  rw [mem_iff_exists]
  exact ⟨fun h => ⟨_, h, least_mem u b⟩,
    fun ⟨a, ha, hb⟩ => Z.lower (least_le u b hb) ha⟩

omit [Fintype α] in
theorem comap_injective : Function.Injective (comap : (β →o α) → _) := by
  intro f g h
  ext b
  have h1 : b ∈ comap f (LowerSet.Iic (f b)) := by simp
  have h2 : b ∈ comap g (LowerSet.Iic (g b)) := by simp
  rw [h] at h1
  rw [← h] at h2
  exact le_antisymm (by simpa using h2) (by simpa using h1)

/-- **Birkhoff duality on morphisms** (notebook 1975-21, pp. 41-48): a bounded lattice
homomorphism between lattices of lower sets, the source over a finite poset, is the preimage
along a unique monotone map. -/
theorem exists_unique_comap : ∃! f : β →o α, comap f = u :=
  ⟨dual u, comap_dual u, fun _ hf => comap_injective (hf.trans (comap_dual u).symm)⟩

end main

end Quillen.Notebook1975_21
