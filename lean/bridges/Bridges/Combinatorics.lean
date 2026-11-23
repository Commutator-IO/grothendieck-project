/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.Boolean
public import LeanPool.ToposTheoreticBridges.DeMorgan
public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic

import Bridges.Preorders

/-!
# De Morgan presheaf topoi in combinatorics

We read the bridge `isDeMorganTopos_presheaf_iff_rightOreCondition` (the presheaf topos
`Cᵒᵖ ⥤ Type u` is De Morgan iff every cospan `Y ⟶ X ⟵ Z` of `C` is completed to a commutative
square) on a few categories of combinatorial structures.

* *Directed graphs.* A presheaf on `WalkingParallelPair` (objects `zero`, `one`, arrows
  `left right : zero ⟶ one`) is a directed graph: edges `F.obj (op one)`, vertices
  `F.obj (op zero)`, source `F.map left.op` and target `F.map right.op`. The cospan
  `left, right` has no completion (`not_rightOreCondition_walkingParallelPair`), so the topos of
  graphs is not De Morgan (`not_isDeMorganTopos_graphs`). Explicitly, in the graph with one
  edge `yoneda.obj one`, with source vertex `left` and target vertex `right`, take for `A` the
  source vertex: `¬A` is the target vertex, `¬¬A` the source vertex, and the edge lies in
  neither (`graphs_pseudocompl_counterexample`).
* *Simplicial sets.* The two vertices `δ 0, δ 1 : ⦋0⦌ ⟶ ⦋1⦌` have no completion, so simplicial
  sets do not form a De Morgan topos (`not_isDeMorganTopos_simplicialSets`).
* *Categories with an initial object* satisfy the Ore condition
  (`rightOreCondition_of_hasInitial`): augmented simplicial sets, and presheaves on finite sets
  (`FintypeCat.Skeleton`), form De Morgan topoi.
* *The topos of trees* `ℕᵒᵖ ⥤ Type` is De Morgan but not Boolean.
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory Limits Opposite

universe u

section Initial

variable {C : Type u} [SmallCategory C]

/-- A category with an initial object satisfies the right Ore condition. -/
theorem rightOreCondition_of_isInitial {I : C} (hI : IsInitial I) :
    GrothendieckTopology.RightOreCondition C :=
  fun _ _ => ⟨I, hI.to _, hI.to _, hI.hom_ext _ _⟩

/-- A category with an initial object satisfies the right Ore condition. -/
theorem rightOreCondition_of_hasInitial [HasInitial C] :
    GrothendieckTopology.RightOreCondition C :=
  rightOreCondition_of_isInitial initialIsInitial

/-- The presheaf topos of a small category with an initial object is De Morgan. -/
theorem isDeMorganTopos_presheaf_of_hasInitial [HasInitial C] :
    IsDeMorganTopos (Cᵒᵖ ⥤ Type u) :=
  (isDeMorganTopos_presheaf_iff_rightOreCondition C).2 rightOreCondition_of_hasInitial

end Initial

/-- Augmented simplicial sets form a De Morgan topos. -/
theorem isDeMorganTopos_augmentedSimplicialSets :
    IsDeMorganTopos (AugmentedSimplexCategoryᵒᵖ ⥤ Type) :=
  isDeMorganTopos_presheaf_of_hasInitial

/-- The empty set is initial in the skeleton of the category of finite sets. -/
def FintypeCat.Skeleton.isInitialZero : IsInitial (FintypeCat.Skeleton.mk.{u} 0) :=
  IsInitial.ofUniqueHom (fun _ x => x.down.elim0) fun _ _ => funext fun x => x.down.elim0

/-- Presheaves on (a skeleton of) the category of finite sets form a De Morgan topos. -/
theorem isDeMorganTopos_presheaf_fintypeCatSkeleton :
    IsDeMorganTopos (FintypeCat.Skeleton.{u}ᵒᵖ ⥤ Type u) :=
  (isDeMorganTopos_presheaf_iff_rightOreCondition _).2
    (rightOreCondition_of_isInitial FintypeCat.Skeleton.isInitialZero)

section Graphs

open WalkingParallelPair WalkingParallelPairHom

/-- The source and target arrows `left, right : zero ⟶ one` of `WalkingParallelPair` cannot be
completed to a commutative square. -/
theorem not_rightOreCondition_walkingParallelPair :
    ¬ GrothendieckTopology.RightOreCondition WalkingParallelPair := by
  intro h
  obtain ⟨W, f, g, hfg⟩ := h (left : zero ⟶ one) (right : zero ⟶ one)
  cases f
  cases g
  change (left : WalkingParallelPairHom zero one) = right at hfg
  exact absurd hfg (by decide)

/-- The topos of directed graphs (presheaves on `WalkingParallelPair`) is not De Morgan. -/
theorem not_isDeMorganTopos_graphs : ¬ IsDeMorganTopos (WalkingParallelPairᵒᵖ ⥤ Type) := by
  rw [isDeMorganTopos_presheaf_iff_rightOreCondition]
  exact not_rightOreCondition_walkingParallelPair

/-- The source vertex of the graph `yoneda.obj one` with one edge, as a subgraph: the maps
`zero ⟶ one` factoring through `left`. -/
abbrev sourceVertex : Subfunctor (yoneda.obj one) :=
  Subfunctor.range (yoneda.map (left : zero ⟶ one))

/-- In the graph with one edge, `¬A` for `A` the source vertex is the target vertex, `¬¬A` is the
source vertex, and the edge `𝟙 one` lies in neither, so `¬A ⊔ ¬¬A ≠ ⊤`. -/
theorem graphs_pseudocompl_counterexample :
    (∀ x : zero ⟶ one,
      x ∈ (Subfunctor.pseudocompl sourceVertex).obj (op zero) ↔ x = right) ∧
    (∀ x : zero ⟶ one,
      x ∈ (Subfunctor.pseudocompl (Subfunctor.pseudocompl sourceVertex)).obj (op zero) ↔
        x = left) ∧
    (𝟙 one ∉ (Subfunctor.pseudocompl sourceVertex).obj (op one)) ∧
    (𝟙 one ∉ (Subfunctor.pseudocompl (Subfunctor.pseudocompl sourceVertex)).obj (op one)) ∧
    Subfunctor.pseudocompl sourceVertex ⊔
      Subfunctor.pseudocompl (Subfunctor.pseudocompl sourceVertex) ≠ ⊤ := by
  have hA : ∀ x : zero ⟶ one, x ∈ sourceVertex.obj (op zero) ↔ x = left := by
    intro x
    constructor
    · rintro ⟨g, rfl⟩
      cases g
      rfl
    · rintro rfl
      exact ⟨𝟙 zero, rfl⟩
  have hA1 : ∀ x : one ⟶ one, x ∉ sourceVertex.obj (op one) := by
    rintro x ⟨g, -⟩
    cases g
  have hN : ∀ x : zero ⟶ one,
      x ∈ (Subfunctor.pseudocompl sourceVertex).obj (op zero) ↔ x = right := by
    intro x
    rw [Subfunctor.mem_pseudocompl_iff]
    constructor
    · intro h
      cases x
      · exact absurd ((hA _).2 rfl) (by simpa using h (𝟙 _))
      · rfl
    · rintro rfl ⟨V⟩ ⟨g⟩
      cases g
      change ¬ (right ∈ sourceVertex.obj (op zero))
      rw [hA]
      exact fun h => by cases h
  have hN1 : 𝟙 one ∉ (Subfunctor.pseudocompl sourceVertex).obj (op one) := fun h =>
    h (Quiver.Hom.op (left : zero ⟶ one)) ((hA _).2 rfl)
  have hNN : ∀ x : zero ⟶ one,
      x ∈ (Subfunctor.pseudocompl (Subfunctor.pseudocompl sourceVertex)).obj (op zero) ↔
        x = left := by
    intro x
    rw [Subfunctor.mem_pseudocompl_iff]
    constructor
    · intro h
      cases x
      · rfl
      · exact absurd ((hN _).2 rfl) (by simpa using h (𝟙 _))
    · rintro rfl ⟨V⟩ ⟨g⟩
      cases g
      change ¬ (left ∈ (Subfunctor.pseudocompl sourceVertex).obj (op zero))
      rw [hN]
      exact fun h => by cases h
  have hNN1 : 𝟙 one ∉ (Subfunctor.pseudocompl (Subfunctor.pseudocompl sourceVertex)).obj
      (op one) := fun h => h (Quiver.Hom.op (right : zero ⟶ one)) ((hN _).2 rfl)
  refine ⟨hN, hNN, hN1, hNN1, fun h => ?_⟩
  have : 𝟙 one ∈ (Subfunctor.pseudocompl sourceVertex ⊔
      Subfunctor.pseudocompl (Subfunctor.pseudocompl sourceVertex)).obj (op one) := by
    rw [h]
    exact Set.mem_univ _
  rcases this with h1 | h1
  · exact hN1 h1
  · exact hNN1 h1

end Graphs

section Simplicial

/-- The two vertices `δ 0, δ 1 : ⦋0⦌ ⟶ ⦋1⦌` of the `1`-simplex cannot be completed to a
commutative square in the simplex category. -/
theorem not_rightOreCondition_simplexCategory :
    ¬ GrothendieckTopology.RightOreCondition SimplexCategory := by
  intro h
  obtain ⟨W, f, g, hfg⟩ := h (SimplexCategory.δ (n := 0) 0) (SimplexCategory.δ (n := 0) 1)
  have := congrArg (fun k : W ⟶ SimplexCategory.mk 1 => k.toOrderHom 0) hfg
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply] at this
  rw [Fin.fin_one_eq_zero (f.toOrderHom 0), Fin.fin_one_eq_zero (g.toOrderHom 0)] at this
  exact absurd this (by decide)

/-- Simplicial sets do not form a De Morgan topos. -/
theorem not_isDeMorganTopos_simplicialSets :
    ¬ IsDeMorganTopos (SimplexCategoryᵒᵖ ⥤ Type) := by
  rw [isDeMorganTopos_presheaf_iff_rightOreCondition]
  exact not_rightOreCondition_simplexCategory

end Simplicial

/-- The topos of trees `ℕᵒᵖ ⥤ Type` is De Morgan. -/
theorem isDeMorganTopos_treeTopos : IsDeMorganTopos (ℕᵒᵖ ⥤ Type) :=
  (isDeMorganTopos_presheaf_preorder_iff ℕ).2 fun _ _ _ _ _ =>
    ⟨0, Nat.zero_le _, Nat.zero_le _⟩

/-- The topos of trees `ℕᵒᵖ ⥤ Type` is not Boolean. -/
theorem not_isBooleanTopos_treeTopos : ¬ IsBooleanTopos (ℕᵒᵖ ⥤ Type) := by
  rw [isBooleanTopos_presheaf_preorder_iff]
  intro h
  exact absurd (h 0 1 (Nat.zero_le 1)) (by decide)

end LeanPool.ToposTheoreticBridges.Examples
