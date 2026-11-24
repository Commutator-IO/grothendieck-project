/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Bridges.CubeTest

/-!
# Joyal's category `Θ₂`

Neither Mathlib nor AxiomMath's Stacks library has Joyal's category `Θ`. This file defines `Θ₂`,
Berger's wreath product `Δ ≀ Δ`, in a form fit for computation:

* `Theta2`, `Theta2.Hom`: the object `[m](a₁, …, a_m)`; a morphism is a map `φ` of `Δ` on the
  vertices with, for each cell `j` of the target lying over a cell `i` of the source
  (`Theta2.Cover`, unique by `cover_unique`), a map `[aᵢ] ⟶ [b_j]` of `Δ`. The components are
  indexed by the cells of the target, so composition is a `bind` (`compC`); that a cell covered
  by a composite is covered along the way is a discrete intermediate value theorem
  (`exists_cover`);
* `Theta2.ptIsTerminal`, `Theta2.isAspherical`: the point is terminal, so `Θ₂` is aspherical for
  every fundamental localizer;
* `Theta2.proj`: the projection `Θ₂ ⥤ Δ`;
* `Theta2.not_rightOreCondition`: `Θ₂` does not satisfy the right Ore condition, so the De Morgan
  obstruction of `Bridges.FundamentalLocalizers` does not apply to it.

That `Θ₂` (and `Θ`) is a test category (Cisinski–Maltsiniotis, Berger) is **not** formalised.
The cone method of `Bridges.SimplexTest` and the cylinder method of `Bridges.CubeTest` do not
apply. A final one-cell `[m + 1](a, 0)` would need, for a map `φ`, a vertex of each `[b_j]` with
`φ(m) < j`, and no choice of vertex is natural. Thickening the two-cells,
`[m](a) ↦ [m](a₁ + 1, …, a_m + 1)`, is a functor with two natural ends. But a map that collapses
a cell forgets the components over it, so factoring through the first end is not reflected and
the contraction `(a, F) ↦ (T a, F⁺)` is not natural. The known proofs go through Grothendieck's
criterion (Cisinski, Th. 4.1.19), or through the stability of test categories under `Δ ≀ -`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace LeanPool.ToposTheoreticBridges.Examples

/-- Joyal's `Θ₂ = Δ ≀ Δ`: the object `[m](a₁, …, a_m)`, `m` cells of dimension one, the `i`-th
carrying the simplex `[aᵢ]` of two-cells. -/
structure Theta2 where
  /-- The number of one-cells. -/
  m : ℕ
  /-- The two-cells over each one-cell. -/
  a : Fin m → ℕ

namespace Theta2

/-- The cell `j` of the target lies over the cell `i` of the source along `φ`. -/
def Cover {m n : ℕ} (φ : Fin (m + 1) →o Fin (n + 1)) (i : Fin m) (j : Fin n) : Prop :=
  φ i.castSucc ≤ j.castSucc ∧ j.succ ≤ φ i.succ

theorem cover_unique {m n : ℕ} {φ : Fin (m + 1) →o Fin (n + 1)} {i i' : Fin m} {j : Fin n}
    (h : Cover φ i j) (h' : Cover φ i' j) : i = i' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : φ i.succ ≤ φ i'.castSucc := φ.monotone (Fin.succ_le_castSucc_iff.2 hlt)
    have := h.2.trans (this.trans h'.1)
    exact absurd this (not_le.2 Fin.castSucc_lt_succ)
  · have : φ i'.succ ≤ φ i.castSucc := φ.monotone (Fin.succ_le_castSucc_iff.2 hlt)
    have := h'.2.trans (this.trans h.1)
    exact absurd this (not_le.2 Fin.castSucc_lt_succ)

/-- A discrete intermediate value theorem: between two vertices `v`, `w` whose images straddle
the cell `k`, some cell `j` is sent across `k`. -/
theorem exists_cover {n p : ℕ} (g : Fin (n + 1) →o Fin (p + 1)) (k : Fin p) {v w : Fin (n + 1)}
    (hv : g v ≤ k.castSucc) (hw : k.succ ≤ g w) :
    ∃ j : Fin n, v ≤ j.castSucc ∧ j.succ ≤ w ∧ Cover g j k := by
  classical
  have hvw : v < w := by
    by_contra h
    have := (g.monotone (not_lt.1 h)).trans hv
    exact absurd (hw.trans this) (not_le.2 Fin.castSucc_lt_succ)
  let S := Finset.univ.filter fun u : Fin (n + 1) => u ≤ w ∧ g u ≤ k.castSucc
  have hS : S.Nonempty := ⟨v, by simp [S, hvw.le, hv]⟩
  set u := S.max' hS with hu
  have huS : u ∈ S := S.max'_mem hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at huS
  have huw : u < w := lt_of_le_of_ne huS.1 fun h => by
    rw [h] at huS; exact absurd (hw.trans huS.2) (not_le.2 Fin.castSucc_lt_succ)
  have hul : u ≠ Fin.last n := fun h => by
    rw [h] at huw; exact absurd huw (not_lt.2 (Fin.le_last _))
  refine ⟨u.castPred hul, ?_, ?_, ?_, ?_⟩
  · rw [Fin.castSucc_castPred]; exact S.le_max' v (by simp [S, hvw.le, hv])
  · rw [Fin.le_iff_val_le_val]
    have := Fin.lt_def.1 huw
    simp only [Fin.val_succ, Fin.coe_castPred]
    omega
  · rw [Fin.castSucc_castPred]; exact huS.2
  · by_contra hc
    have hlt : g (u.castPred hul).succ < k.succ := not_le.1 hc
    have hle : g (u.castPred hul).succ ≤ k.castSucc := by
      rw [Fin.lt_def] at hlt
      rw [Fin.le_iff_val_le_val]
      simp only [Fin.val_succ, Fin.val_castSucc] at hlt ⊢
      omega
    have hmem : (u.castPred hul).succ ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, hle⟩
      rw [Fin.le_iff_val_le_val]
      have := Fin.lt_def.1 huw
      simp only [Fin.val_succ, Fin.coe_castPred]
      omega
    have := S.le_max' _ hmem
    rw [← hu, Fin.le_iff_val_le_val] at this
    simp only [Fin.val_succ, Fin.coe_castPred] at this
    omega

/-- A morphism of `Θ₂`: a map `φ` of `Δ` on the vertices, and for each cell `j` of the target
lying over a cell `i` of the source, a map `[aᵢ] ⟶ [b_j]` of `Δ` (Berger's wreath product). -/
@[ext]
structure Hom (x y : Theta2) where
  /-- The map on vertices. -/
  φ : Fin (x.m + 1) →o Fin (y.m + 1)
  /-- The two-cell components, indexed by the cells of the target. -/
  c : (j : Fin y.m) → Option (Σ i : Fin x.m, Fin (x.a i + 1) →o Fin (y.a j + 1))
  /-- A component sits over its cell. -/
  cover_of : ∀ j s, s ∈ c j → Cover φ s.1 j
  /-- Every covered cell has a component. -/
  isSome_of : ∀ j i, Cover φ i j → (c j).isSome

/-- The components of a composite. -/
def compC {x y z : Theta2} (f : Hom x y) (g : Hom y z) (k : Fin z.m) :
    Option (Σ i : Fin x.m, Fin (x.a i + 1) →o Fin (z.a k + 1)) :=
  (g.c k).bind fun s => (f.c s.1).map fun t => ⟨t.1, s.2.comp t.2⟩

theorem mem_compC {x y z : Theta2} {f : Hom x y} {g : Hom y z} {k : Fin z.m} {r}
    (h : r ∈ compC f g k) : ∃ s ∈ g.c k, ∃ t ∈ f.c s.1, r = ⟨t.1, s.2.comp t.2⟩ := by
  unfold compC at h
  obtain ⟨s, hs, h⟩ := Option.mem_bind_iff.1 h
  obtain ⟨t, ht, rfl⟩ := Option.mem_map.1 h
  exact ⟨s, hs, t, ht, rfl⟩

instance : SmallCategory Theta2 where
  Hom := Hom
  id x := ⟨OrderHom.id, fun j => some ⟨j, OrderHom.id⟩,
    fun j s hs => by cases hs; exact ⟨le_rfl, le_rfl⟩,
    fun _ _ _ => rfl⟩
  comp f g := ⟨g.φ.comp f.φ, compC f g, fun k r hr => by
      obtain ⟨s, hs, t, ht, rfl⟩ := mem_compC hr
      have hg := g.cover_of k s hs
      have hf := f.cover_of s.1 t ht
      exact ⟨(g.φ.monotone hf.1).trans hg.1, hg.2.trans (g.φ.monotone hf.2)⟩,
    fun k i hcov => by
      obtain ⟨j, h1, h2, hj⟩ := exists_cover g.φ k hcov.1 hcov.2
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 (g.isSome_of k j hj)
      have hsj : s.1 = j := cover_unique (g.cover_of k s hs) hj
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (f.isSome_of s.1 i (hsj ▸ ⟨h1, h2⟩))
      simp [compC, hs, ht]⟩
  id_comp f := Hom.ext rfl (funext fun k => by
    change compC _ f k = f.c k
    unfold compC
    cases f.c k <;> rfl)
  comp_id f := Hom.ext rfl (funext fun k => by
    dsimp only
    simp only [compC]
    change (f.c k).map _ = _
    cases f.c k <;> rfl)
  assoc f g h := Hom.ext rfl (funext fun k => by
    change compC (Hom.mk _ (compC f g) _ _) h k = compC f (Hom.mk _ (compC g h) _ _) k
    simp only [compC, Option.bind_map, Option.map_bind, Option.bind_assoc]
    congr 1; funext s; congr 1; funext t
    simp only [Function.comp_apply]
    cases f.c t.1 <;> rfl)

theorem hom_ext {x y : Theta2} {f g : x ⟶ y} (hφ : Hom.φ f = Hom.φ g) (hc : Hom.c f = Hom.c g) :
    f = g := Hom.ext hφ hc

/-- The point `[0]`, with no cell. -/
abbrev pt : Theta2 := ⟨0, Fin.elim0⟩

/-- The unique map to the point. -/
def toPt (x : Theta2) : x ⟶ pt :=
  (⟨⟨fun _ => 0, fun _ _ _ => le_rfl⟩, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
    fun j => Fin.elim0 j⟩ : Hom _ _)

/-- The point is terminal. -/
def ptIsTerminal : IsTerminal pt :=
  IsTerminal.ofUniqueHom toPt fun _ _ =>
    hom_ext (OrderHom.ext _ _ (funext fun _ => Subsingleton.elim (α := Fin 1) _ _))
      (funext fun j => Fin.elim0 j)

instance : HasTerminal Theta2 := ptIsTerminal.hasTerminal

/-- **`Θ₂` is aspherical**, for every fundamental localizer. -/
theorem isAspherical (L : FundamentalLocalizer.{0}) : L.IsAspherical Theta2 :=
  L.star_mem_of_hasTerminal _

/-- The projection `Θ₂ ⥤ Δ`, `[m](a) ↦ [m]`. -/
def proj : Theta2 ⥤ SimplexCategory where
  obj x := SimplexCategory.mk x.m
  map f := SimplexCategory.Hom.mk (Hom.φ f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The one-cell `[1](0)`. -/
abbrev arrow : Theta2 := ⟨1, fun _ => 0⟩

/-- The vertex `e` of the one-cell. -/
def vertex (e : Fin 2) : pt ⟶ arrow :=
  (⟨⟨fun _ => e, fun _ _ _ => le_rfl⟩, fun _ => none, fun _ s hs => (by cases hs),
    fun _ i _ => Fin.elim0 i⟩ : Hom _ _)

/-- **`Θ₂` does not satisfy the right Ore condition**: the two vertices of the one-cell admit no
common precomposition. So the De Morgan obstruction does not apply, and its presheaf topos is not
De Morgan. -/
theorem not_rightOreCondition : ¬ GrothendieckTopology.RightOreCondition Theta2 := by
  intro h
  obtain ⟨w, k, l, hkl⟩ := h (vertex 0) (vertex 1)
  have h01 : (0 : Fin 2) = 1 := congrArg (fun φ : _ ⟶ _ => (Hom.φ φ) 0) hkl
  exact absurd h01 (by decide)

end Theta2
end LeanPool.ToposTheoreticBridges.Examples
