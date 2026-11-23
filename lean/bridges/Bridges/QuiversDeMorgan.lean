/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.Boolean
public import LeanPool.ToposTheoreticBridges.DeMorgan
public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Presheaf topoi on free categories

For a quiver `Q`, the free category `Paths Q` has the paths of `Q` as morphisms, and composition
`p ≫ q` is the path `p` followed by `q` (`Quiver.Path.comp`). A presheaf on `Paths Q` is the
same as a representation of the opposite quiver in sets.

* `rightOreCondition_paths_iff`: `Paths Q` satisfies the right Ore condition iff every vertex
  of `Q` has at most one incoming arrow. Indeed `w ≫ p = w' ≫ q` is an equality of paths, so of
  two paths with the same target one is a final segment of the other
  (`exists_comp_eq_or_exists_comp_eq`), as soon as no vertex has two incoming arrows;
* `isDeMorganTopos_paths_iff`: hence the presheaf topos on `Paths Q` is De Morgan iff every
  vertex of `Q` has at most one incoming arrow (for instance, `Q` is a forest of rooted trees
  oriented away from the roots, or the quiver `ℕ` with one arrow `n ⟶ n + 1`);
* `isGroupoid_paths_iff`, `isBooleanTopos_paths_iff`: `Paths Q` is a groupoid, and its presheaf
  topos is Boolean, iff `Q` has no arrows, since a non-empty path is never invertible.
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory Quiver

universe v u

section Path

variable {Q : Type u} [Quiver.{v + 1} Q]

/-- If no vertex of `Q` has two incoming arrows, then of two paths with the same target, one is
a final segment of the other. -/
theorem exists_comp_eq_or_exists_comp_eq (hQ : ∀ v : Q, Subsingleton (Σ w : Q, w ⟶ v))
    {x y z : Q} (p : Path y x) (q : Path z x) :
    (∃ r : Path z y, r.comp p = q) ∨ ∃ r : Path y z, r.comp q = p := by
  induction p generalizing z with
  | nil => exact Or.inl ⟨q, Path.comp_nil q⟩
  | @cons x' x p a ih =>
    cases q with
    | nil => exact Or.inr ⟨p.cons a, Path.comp_nil _⟩
    | @cons x'' _ q b =>
      obtain ⟨rfl, hab⟩ := Sigma.mk.inj_iff.1 ((hQ x).elim ⟨x', a⟩ ⟨x'', b⟩)
      obtain rfl := eq_of_heq hab
      rcases ih q with ⟨r, hr⟩ | ⟨r, hr⟩
      · exact Or.inl ⟨r, by rw [Path.comp_cons, hr]⟩
      · exact Or.inr ⟨r, by rw [Path.comp_cons, hr]⟩

/-- Two arrows with the same target and distinct sources or values are not both the last arrow
of a path. -/
theorem sigma_eq_of_cons_eq_cons {x y z w : Q} {p : Path w y} {q : Path w z} {a : y ⟶ x}
    {b : z ⟶ x} (h : p.cons a = q.cons b) : (⟨y, a⟩ : Σ v : Q, v ⟶ x) = ⟨z, b⟩ := by
  obtain rfl := Path.obj_eq_of_cons_eq_cons h
  rw [eq_of_heq (Path.hom_heq_of_cons_eq_cons h)]

/-- A path whose composite with another path is the empty path is empty. -/
theorem Path.length_eq_zero_of_comp_eq_nil {x y : Q} {p : Path x y} {q : Path y x}
    (h : p.comp q = Path.nil) : p.length = 0 := by
  have := congrArg Path.length h
  rw [Path.length_comp, Path.length_nil] at this
  omega

end Path

section Paths

variable (Q : Type u) [Quiver.{v + 1} Q]

/-- **Ore condition for free categories.** The free category on a quiver `Q` satisfies the right
Ore condition iff every vertex of `Q` has at most one incoming arrow. -/
theorem rightOreCondition_paths_iff :
    GrothendieckTopology.RightOreCondition (Paths Q) ↔
      ∀ v : Q, Subsingleton (Σ w : Q, w ⟶ v) := by
  constructor
  · intro h v
    refine ⟨fun ⟨y, a⟩ ⟨z, b⟩ => ?_⟩
    obtain ⟨w, p, q, hpq⟩ := h (X := (v : Paths Q)) (Y := (y : Paths Q)) (Z := (z : Paths Q))
      a.toPath b.toPath
    exact sigma_eq_of_cons_eq_cons (p := p) (q := q) hpq
  · intro hQ x y z p q
    rcases exists_comp_eq_or_exists_comp_eq hQ p q with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨z, r, 𝟙 z, hr.trans (Path.nil_comp q).symm⟩
    · exact ⟨y, 𝟙 y, r, (Path.nil_comp p).trans hr.symm⟩

/-- The free category on a quiver is a groupoid iff the quiver has no arrows. -/
theorem isGroupoid_paths_iff : IsGroupoid (Paths Q) ↔ ∀ v w : Q, IsEmpty (v ⟶ w) := by
  constructor
  · intro h v w
    refine ⟨fun a => ?_⟩
    have := Path.length_eq_zero_of_comp_eq_nil (IsIso.hom_inv_id ((Paths.of Q).map a))
    exact Nat.one_ne_zero this
  · intro h
    refine ⟨fun {x y} p => ?_⟩
    cases p with
    | nil => exact inferInstanceAs (IsIso (𝟙 x))
    | cons _ a => exact (h _ _).elim a

end Paths

section Topos

/-! Mathlib's paths of a quiver with vertices in `Type u` and arrows in `Sort v` live in
`Type (max u v)`. For `Paths Q` to be a small category, to which the bridges apply, we take the
vertices in `Type (u + 1)` and the arrows in `Type u`. -/

variable (Q : Type (u + 1)) [Quiver.{u + 1} Q]

/-- The free category on a quiver with vertices in `Type (u + 1)` and arrows in `Type u` is a
small category. -/
instance Paths.smallCategory : SmallCategory (Paths Q) :=
  Paths.categoryPaths Q

/-- **De Morgan topoi of quiver representations.** The presheaf topos on the free category of a
quiver `Q` is De Morgan iff every vertex of `Q` has at most one incoming arrow. -/
theorem isDeMorganTopos_paths_iff :
    IsDeMorganTopos ((Paths Q)ᵒᵖ ⥤ Type (u + 1)) ↔ ∀ v : Q, Subsingleton (Σ w : Q, w ⟶ v) :=
  (isDeMorganTopos_presheaf_iff_rightOreCondition (Paths Q)).trans
    (rightOreCondition_paths_iff Q)

/-- **Boolean topoi of quiver representations.** The presheaf topos on the free category of a
quiver `Q` is Boolean iff `Q` has no arrows. -/
theorem isBooleanTopos_paths_iff :
    IsBooleanTopos ((Paths Q)ᵒᵖ ⥤ Type (u + 1)) ↔ ∀ v w : Q, IsEmpty (v ⟶ w) :=
  (isBooleanTopos_presheaf_iff_isGroupoid (Paths Q)).trans (isGroupoid_paths_iff Q)

end Topos

end LeanPool.ToposTheoreticBridges.Examples
