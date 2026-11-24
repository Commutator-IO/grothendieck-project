/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Bridges.SimplexTest

/-!
# The cube category is a test category, from the axioms of a fundamental localizer

In the axiomatic setting of `Bridges.FundamentalLocalizers`, this file proves that the cube
category `□` (faces and degeneracies, no connections) is a weak and a local test category for
every fundamental localizer, with no hypothesis on `W`:

* `CylData`, `CylData.isWeakTest`: a category with a terminal object and a cylinder (an
  endofunctor `T` with two ends `ι, ι₁ : 𝟭 ⟶ T`, `ι` mono with factorisation through it reflected
  by `T`, nothing on the end `ι₁` factoring through `ι`) is a weak test category. With the
  contraction `(a, F) ↦ (T a, F⁺)` of `Bridges.SimplexTest`, `ι` and `ι₁` give
  `𝟭 ⟶ cone ⟵ proj ⋙ sec`, where `proj : A/i_A^*(C) ⥤ A` and `sec a = (a, const ⋆)`; so `proj`,
  a retraction of `sec`, is a `W`-equivalence, and `A/i_A^*(C)` is aspherical since `A` is;
* `Cube`, `Cube.Hom`: the cube category, a morphism `[1]^m ⟶ [1]^n` being given by its
  coordinates, each a constant or a coordinate of the source, the latter in increasing order;
* `Cube.cylData`, `Cube.cylDataOver`: the cylinder `[1]^n ↦ [1]^{n+1}` on `□` and on every slice
  `□/b` (over `b` through the projection);
* `Cube.isWeakTest_cube`, `Cube.isLocalTest_cube`, `Cube.isTest_cube`: `□` is a test category
  (Cisinski, Astérisque 308, Cor. 8.4.13, for the usual weak equivalences).

As for `Δ`, the usual weak equivalences are not shown to form a fundamental localizer.
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace LeanPool.ToposTheoreticBridges.Examples

/-- A cylinder structure on `A`: an endofunctor `T` with two ends `ι, ι₁ : 𝟭 ⟶ T`, nothing on the
end `ι₁` factoring through the end `ι`. -/
structure CylData (A : Type) [SmallCategory A] extends FacData A where
  ι₁ : 𝟭 A ⟶ T
  not_fac₁ : ∀ {z a : A} (h : z ⟶ a) (g : z ⟶ a), g ≫ ι.app a ≠ h ≫ ι₁.app a

namespace CylData
open FacData
variable {A : Type} [SmallCategory A] (D : CylData A)

/-- The projection `A/i_A^*(C) ⥤ A`. -/
def proj (C : Type) [SmallCategory C] : E A C ⥤ A where
  obj X := X.unop.obj.unop
  map φ := φ.unop.hom.unop

/-- The section `a ↦ (a, const ⋆)`. -/
noncomputable def sec (C : Type) [SmallCategory C] [HasTerminal C] : A ⥤ E A C where
  obj a := op ((iStar A C).elementsMk (op a) ((Functor.const _).obj (⊤_ C)))
  map f := Quiver.Hom.op ⟨f.op, rfl⟩

theorem sec_proj (C : Type) [SmallCategory C] [HasTerminal C] : sec C ⋙ proj C = 𝟭 A := rfl

/-- `proj ⋙ sec ⟶ cone`, by the other end `ι₁`. -/
noncomputable def cylι₁ (C : Type) [SmallCategory C] [HasTerminal C] :
    proj C ⋙ sec C ⟶ D.toFacData.cone C where
  app X := Quiver.Hom.op ⟨(D.ι₁.app X.unop.obj.unop).op,
    map_comp_plus_of D.toFacData D.not_fac₁ (valF X)⟩
  naturality X Y φ := Quiver.Hom.unop_inj (Functor.Elements.Hom.ext (by
    change (φ.unop.hom.unop ≫ D.ι₁.app _).op = (D.ι₁.app _ ≫ D.T.map φ.unop.hom.unop).op
    exact congrArg Quiver.Hom.op (D.ι₁.naturality φ.unop.hom.unop)))

include D in
/-- **A category with a terminal object and cylinder data is a weak test category**, for every
fundamental localizer: `𝟭 ⟶ cone ⟵ proj ⋙ sec` makes `proj` a `W`-equivalence. -/
theorem isWeakTest [HasTerminal A] (L : FundamentalLocalizer.{0}) : IsWeakTest A L :=
  fun C _ _ => by
    have ht : L.W (D.toFacData.cone C) :=
      (mem_iff_of_natTrans L (D.toFacData.coneι C)).1 (L.id_mem _)
    have hu : L.W (proj C ⋙ sec C) := (mem_iff_of_natTrans L (D.cylι₁ C)).2 ht
    have hq : L.W (proj (A := A) C) := L.of_retract (sec C) (proj C) (sec_proj C) hu
    unfold FundamentalLocalizer.IsAspherical
    rw [Functor.punit_ext' (Functor.star (E A C)) (proj C ⋙ Functor.star A)]
    exact L.comp_mem _ _ hq (L.star_mem_of_hasTerminal A)

end CylData
/-- The cube category `□`: one object `[1]^n` for each `n`. -/
structure Cube where
  /-- The dimension. -/
  dim : ℕ

namespace Cube

/-- A morphism `[1]^m ⟶ [1]^n` of `□`, as the list of its coordinates: each coordinate of the
target is a constant (`Sum.inl`) or a coordinate of the source (`Sum.inr`), the coordinates of
the source appearing in increasing order. These are the composites of faces (inserting a
constant coordinate) and degeneracies (forgetting one). -/
@[ext]
structure Hom (m n : Cube) where
  /-- The coordinates. -/
  c : Fin n.dim → Bool ⊕ Fin m.dim
  /-- The coordinates of the source are used in increasing order. -/
  mono : ∀ k k' i i', k < k' → c k = .inr i → c k' = .inr i' → i < i'

theorem comp_inr {m n p : Cube} (f : Hom m n) (g : Hom n p) {k : Fin p.dim}
    {i : Fin m.dim} (h : Sum.elim .inl f.c (g.c k) = .inr i) :
    ∃ j, g.c k = .inr j ∧ f.c j = .inr i := by
  cases hg : g.c k with
  | inl b => rw [hg] at h; cases h
  | inr j => rw [hg] at h; exact ⟨j, rfl, h⟩

instance : SmallCategory Cube where
  Hom := Hom
  id n := ⟨.inr, fun _ _ _ _ hk h h' => by cases h; cases h'; exact hk⟩
  comp f g := ⟨fun k => Sum.elim .inl f.c (g.c k), fun k k' i i' hk h h' => by
    obtain ⟨j, hj, hfj⟩ := comp_inr f g h
    obtain ⟨j', hj', hfj'⟩ := comp_inr f g h'
    exact f.mono _ _ _ _ (g.mono _ _ _ _ hk hj hj') hfj hfj'⟩
  id_comp f := Hom.ext (funext fun k => by
    change Sum.elim _ _ (Hom.c f k) = _
    cases Hom.c f k <;> rfl)
  comp_id _ := rfl
  assoc f g h := Hom.ext (funext fun k => by
    change Sum.elim _ _ (Hom.c h k) = Sum.elim _ _ (Sum.elim _ _ (Hom.c h k))
    cases Hom.c h k <;> rfl)

/-- The coordinates of a morphism. -/
abbrev co {m n : Cube} (f : m ⟶ n) : Fin n.dim → Bool ⊕ Fin m.dim := Hom.c f

theorem hom_ext {m n : Cube} {f g : m ⟶ n} (h : ∀ k, co f k = co g k) : f = g :=
  Hom.ext (funext h)

theorem co_mk {m n : Cube} (c : Fin n.dim → Bool ⊕ Fin m.dim) (h) :
    co (⟨c, h⟩ : Hom m n) = c := rfl

theorem co_comp {m n p : Cube} (f : m ⟶ n) (g : n ⟶ p) (k : Fin p.dim) :
    co (f ≫ g) k = Sum.elim .inl (co f) (co g k) := rfl

/-- `[1]^0` is terminal. -/
instance : HasTerminal Cube :=
  (IsTerminal.ofUniqueHom (X := ⟨0⟩)
    (fun _ => (⟨Fin.elim0, fun k => k.elim0⟩ : Hom _ _))
    fun _ _ => hom_ext fun k => k.elim0).hasTerminal

/-- The coordinates of `T f = f × [1]`. -/
def Tc {m n : Cube} (f : m ⟶ n) : Fin (n.dim + 1) → Bool ⊕ Fin (m.dim + 1) :=
  Fin.lastCases (.inr (Fin.last _)) fun k => (co f k).map id Fin.castSucc

theorem Tc_last {m n : Cube} (f : m ⟶ n) : Tc f (Fin.last _) = .inr (Fin.last _) :=
  Fin.lastCases_last

theorem Tc_castSucc {m n : Cube} (f : m ⟶ n) (k : Fin n.dim) :
    Tc f k.castSucc = (co f k).map id Fin.castSucc :=
  Fin.lastCases_castSucc _

theorem Tc_mono {m n : Cube} (f : m ⟶ n) (k k' : Fin (n.dim + 1)) (i i' : Fin (m.dim + 1))
    (hk : k < k') (h : Tc f k = .inr i) (h' : Tc f k' = .inr i') : i < i' := by
  induction k' using Fin.lastCases with
  | last =>
    induction k using Fin.lastCases with
    | last => exact absurd hk (lt_irrefl _)
    | cast k =>
      rw [Tc_last] at h'
      cases h'
      rw [Tc_castSucc] at h
      cases hf : co f k with
      | inl b => rw [hf] at h; cases h
      | inr j => rw [hf] at h; cases h; exact Fin.castSucc_lt_last _
  | cast k' =>
    induction k using Fin.lastCases with
    | last => exact absurd hk (not_lt.2 (Fin.le_last _))
    | cast k =>
      rw [Tc_castSucc] at h h'
      cases hf : co f k with
      | inl b => rw [hf] at h; cases h
      | inr j =>
        cases hf' : co f k' with
        | inl b => rw [hf'] at h'; cases h'
        | inr j' =>
          rw [hf] at h; rw [hf'] at h'; cases h; cases h'
          exact Fin.castSucc_lt_castSucc_iff.2
            (f.mono _ _ _ _ (Fin.castSucc_lt_castSucc_iff.1 hk) hf hf')

/-- `T [1]^n = [1]^{n+1}`, the cylinder. -/
@[reducible] def T : Cube ⥤ Cube where
  obj n := ⟨n.dim + 1⟩
  map f := (⟨Tc f, Tc_mono f⟩ : Hom _ _)
  map_id n := hom_ext fun k => by
    induction k using Fin.lastCases with
    | last => exact Tc_last _
    | cast k => exact Tc_castSucc _ _
  map_comp f g := hom_ext fun k => by
    induction k using Fin.lastCases with
    | last =>
      change Tc _ _ = Sum.elim _ _ (Tc _ _)
      rw [Tc_last, Tc_last]; exact (Tc_last _).symm
    | cast k =>
      change Tc _ _ = Sum.elim _ _ (Tc _ _)
      rw [Tc_castSucc, Tc_castSucc, co_comp]
      cases co g k with
      | inl b => rfl
      | inr j => exact (Tc_castSucc _ _).symm

theorem co_T {m n : Cube} (f : m ⟶ n) : co (T.map f) = Tc f := rfl

/-- The coordinates of the end `ε` of the cylinder, `x ↦ (x, ε)`. -/
def endc (ε : Bool) (n : Cube) : Fin (n.dim + 1) → Bool ⊕ Fin n.dim :=
  Fin.lastCases (.inl ε) fun k => .inr k

theorem endc_last (ε : Bool) (n : Cube) : endc ε n (Fin.last _) = .inl ε := Fin.lastCases_last

theorem endc_castSucc (ε : Bool) (n : Cube) (k : Fin n.dim) : endc ε n k.castSucc = .inr k :=
  Fin.lastCases_castSucc _

theorem endc_mono (ε : Bool) (n : Cube) (k k' : Fin (n.dim + 1)) (i i' : Fin n.dim) (hk : k < k')
    (h : endc ε n k = .inr i) (h' : endc ε n k' = .inr i') : i < i' := by
  induction k' using Fin.lastCases with
  | last => rw [endc_last] at h'; cases h'
  | cast k' =>
    induction k using Fin.lastCases with
    | last => rw [endc_last] at h; cases h
    | cast k =>
      rw [endc_castSucc] at h h'
      cases h; cases h'
      exact Fin.castSucc_lt_castSucc_iff.1 hk

/-- The end `ε` of the cylinder. -/
def endι (ε : Bool) : 𝟭 Cube ⟶ T where
  app n := (⟨endc ε n, endc_mono ε n⟩ : Hom _ _)
  naturality m n f := hom_ext fun k => by
    change Sum.elim _ (co f) (endc ε n k) = Sum.elim _ (endc ε m) (Tc f k)
    induction k using Fin.lastCases with
    | last => rw [endc_last, Tc_last]; exact (endc_last ε m).symm
    | cast k =>
      rw [endc_castSucc, Tc_castSucc, Sum.elim_inr]
      cases co f k with
      | inl b => rfl
      | inr j => exact (endc_castSucc ε m j).symm

theorem co_endι (ε : Bool) (n : Cube) : co ((endι ε).app n) = endc ε n := rfl

instance (n : Cube) : Mono ((endι false).app n) where
  right_cancellation f g e := hom_ext fun k => by
    have := congrArg (fun φ : _ ⟶ _ => co φ k.castSucc) e
    simpa only [co_comp, co_endι, endc_castSucc, Sum.elim_inr] using this

theorem not_fac₁ {z a : Cube} (h : z ⟶ a) (g : z ⟶ a) :
    g ≫ (endι false).app a ≠ h ≫ (endι true).app a := by
  intro e
  have := congrArg (fun φ : _ ⟶ _ => co φ (Fin.last _)) e
  simp only [co_comp, co_endι, endc_last, Sum.elim_inl] at this
  cases this

theorem fac_of {z a b : Cube} (f : a ⟶ b) (k : z ⟶ T.obj a) (g : z ⟶ b)
    (e : g ≫ (endι false).app b = k ≫ T.map f) :
    ∃ g' : z ⟶ a, g' ≫ (endι false).app a = k := by
  have hl : co k (Fin.last _) = .inl false := by
    have := congrArg (fun φ : _ ⟶ _ => co φ (Fin.last _)) e
    simp only [co_comp, co_endι, co_mk, endc_last, Tc_last, Sum.elim_inl, Sum.elim_inr] at this
    exact this.symm
  refine ⟨(⟨fun j => co k j.castSucc, fun j j' i i' hj h h' =>
    k.mono _ _ _ _ (Fin.castSucc_lt_castSucc_iff.2 hj) h h'⟩ : Hom _ _), hom_ext fun j => ?_⟩
  induction j using Fin.lastCases with
  | last => rw [co_comp, co_endι, endc_last, hl]; rfl
  | cast j => rw [co_comp, co_endι, endc_castSucc]; rfl

/-- The cylinder data of `□`. -/
def cylData : CylData Cube where
  T := T
  ι := endι false
  mono := inferInstance
  fac_of := fac_of
  ι₁ := endι true
  not_fac₁ := not_fac₁

/-- **`□` is a weak test category**, for every fundamental localizer. -/
theorem isWeakTest_cube (L : FundamentalLocalizer.{0}) : IsWeakTest Cube L :=
  cylData.isWeakTest L

/-- The projection `[1]^{n+1} ⟶ [1]^n` forgetting the last coordinate. -/
def pr (n : Cube) : T.obj n ⟶ n :=
  (⟨fun k => .inr k.castSucc, fun _ _ _ _ hk h h' => by
    cases h; cases h'; exact Fin.castSucc_lt_castSucc_iff.2 hk⟩ : Hom _ _)

theorem endι_pr (ε : Bool) (n : Cube) : (endι ε).app n ≫ pr n = 𝟙 n :=
  hom_ext fun k => endc_castSucc ε n k

theorem T_map_pr {m n : Cube} (f : m ⟶ n) : T.map f ≫ pr n = pr m ≫ f :=
  hom_ext fun k => by
    change Tc f k.castSucc = Sum.elim _ _ (co f k)
    rw [Tc_castSucc]
    cases co f k <;> rfl

section Slice
variable (b : Cube)

/-- The cylinder on `□/b`: `Y × [1]` over `b` through the projection. -/
def Tb : Over b ⥤ Over b where
  obj Y := Over.mk (pr Y.left ≫ Y.hom)
  map {Y Y'} φ := Over.homMk (T.map φ.left) (by
    change T.map φ.left ≫ pr Y'.left ≫ Y'.hom = pr Y.left ≫ Y.hom
    rw [← Category.assoc, T_map_pr, Category.assoc, Over.w φ])
  map_id _ := Over.OverMorphism.ext (T.map_id _)
  map_comp _ _ := Over.OverMorphism.ext (T.map_comp _ _)

/-- The end `ε` of the cylinder on `□/b`. -/
def endb (ε : Bool) : 𝟭 (Over b) ⟶ Tb b where
  app Y := Over.homMk ((endι ε).app Y.left) (by
    change (endι ε).app Y.left ≫ pr Y.left ≫ Y.hom = Y.hom
    rw [← Category.assoc, endι_pr]
    exact Category.id_comp _)
  naturality _ _ φ := Over.OverMorphism.ext ((endι ε).naturality φ.left)

/-- The cylinder data of `□/b`. -/
def cylDataOver : CylData (Over b) where
  T := Tb b
  ι := endb b false
  mono Y := by
    have : Mono ((endb b false).app Y).left := inferInstanceAs (Mono ((endι false).app Y.left))
    exact Over.mono_of_mono_left _
  fac_of {Z Y Y'} f k g e := by
    obtain ⟨g', hg'⟩ := fac_of f.left k.left g.left (congrArg CommaMorphism.left e)
    refine ⟨Over.homMk g' ?_, Over.OverMorphism.ext hg'⟩
    rw [← Over.w k]
    change _ = k.left ≫ pr Y.left ≫ Y.hom
    rw [← hg']
    have : (g' ≫ (endι false).app Y.left) ≫ pr Y.left ≫ Y.hom = g' ≫ Y.hom := by
      rw [Category.assoc, ← Category.assoc ((endι false).app Y.left) (pr Y.left) Y.hom, endι_pr]
      exact congrArg (g' ≫ ·) (Category.id_comp _)
    exact this.symm
  ι₁ := endb b true
  not_fac₁ h g e := not_fac₁ h.left g.left (congrArg CommaMorphism.left e)

end Slice

/-- **`□` is a local test category**, for every fundamental localizer. -/
theorem isLocalTest_cube (L : FundamentalLocalizer.{0}) : IsLocalTest Cube L := fun b =>
  have : HasTerminal (Over b) := Over.mkIdTerminal.hasTerminal
  (cylDataOver b).isWeakTest L

/-- **`□` is a test category**, for every fundamental localizer. -/
theorem isTest_cube (L : FundamentalLocalizer.{0}) :
    IsWeakTest Cube L ∧ IsLocalTest Cube L :=
  ⟨isWeakTest_cube L, isLocalTest_cube L⟩

end Cube

end LeanPool.ToposTheoreticBridges.Examples
