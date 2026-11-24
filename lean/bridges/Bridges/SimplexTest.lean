/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Bridges.FundamentalLocalizers
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.WithTerminal.Basic

/-!
# `Δ` is a test category, from the axioms of a fundamental localizer

In the axiomatic setting of `Bridges.FundamentalLocalizers` (Grothendieck's axioms for a class `W`
of functors, and Cisinski's definitions of weak and local test categories), this file proves that
the simplex category `Δ` is a weak and a local test category for every fundamental localizer, with
no hypothesis on `W` (not even `AsphericalConnected`):

* `mem_iff_of_natTrans`: two functors joined by a natural transformation are both in `W` or
  neither (the projection `Δ¹ × D ⥤ D` is in `W` by the relative Theorem A, and its two sections
  are then in `W` by two out of three);
* `isAspherical_of_contraction`: a category with an endofunctor `t` and natural transformations
  `𝟭 ⟶ t ⟵ const d` is aspherical (the constant functor is in `W`, and the functor to the point is
  a retract of it);
* `FacData`, `ConeData`, `ConeData.isWeakTest`: a category with a « cone » structure (an
  endofunctor `T` adding a final vertex, `ι : 𝟭 ⟶ T` mono, a vertex `π : const p ⟶ T`, and a
  decidable factorisation through `ι`) is a weak test category. For `C` with a terminal object,
  the contraction of `A/i_A^*(C)` sends `(a, F)` to `(T a, F⁺)`, where `F⁺ : A/T a ⥤ C` is `F`
  on what factors through `ι a` and the terminal object elsewhere (`FacData.chi`,
  `FacData.plus`); `ι` and `π` give `𝟭 ⟶ t ⟵ const (p, ⋆)`;
* `SimplexCone.coneData`, `SimplexCone.coneDataOver`: the cone data of `Δ` (`[n] ↦ [n + 1]`) and
  of every slice `Δ/b` (the new vertex over the top of `b`);
* `isWeakTest_simplexCategory`, `isLocalTest_simplexCategory`, `isTest_simplexCategory`: `Δ` is a
  test category.

The usual weak equivalences (through the nerve) are not shown to form a fundamental localizer;
the statement is about every class satisfying the axioms.
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace LeanPool.ToposTheoreticBridges.Examples

section Homotopy
variable (L : FundamentalLocalizer.{0})

/-- The projection `Δ¹ × D ⥤ D` is a `W`-equivalence: its slices have a terminal object. -/
theorem snd_mem (D : Type) [SmallCategory D] : L.W (CategoryTheory.Prod.snd (Fin 2) D) := by
  refine L.mem_of_costructuredArrow _ (𝟭 D) fun d => ?_
  have : HasTerminal (CostructuredArrow (CategoryTheory.Prod.snd (Fin 2) D ⋙ 𝟭 D) d) := by
    refine (IsTerminal.ofUniqueHom (X := CostructuredArrow.mk (Y := (Fin.last 1, d))
      (𝟙 d)) (fun x => CostructuredArrow.homMk
        (show x.left ⟶ (Fin.last 1, d) from (homOfLE (Fin.le_last x.left.1), x.hom))
      (by simp)) fun x m => ?_).hasTerminal
    ext
    · exact Subsingleton.elim _ _
    · have := CostructuredArrow.w m
      simpa using this
  have : HasTerminal (CostructuredArrow (𝟭 D) d) := CostructuredArrow.mkIdTerminal.hasTerminal
  exact L.mem_of_hasTerminal _

/-- The two ends `D ⥤ Δ¹ × D`. -/
def endIncl (D : Type) [SmallCategory D] (i : Fin 2) : D ⥤ Fin 2 × D :=
  ((Functor.const D).obj i).prod' (𝟭 D)

theorem endIncl_mem (D : Type) [SmallCategory D] (i : Fin 2) : L.W (endIncl D i) :=
  L.of_comp_right _ _ (snd_mem L D) (by
    have : endIncl D i ⋙ CategoryTheory.Prod.snd (Fin 2) D = 𝟭 D := rfl
    rw [this]; exact L.id_mem _)

/-- **Homotopy invariance.** Two functors joined by a natural transformation are both
`W`-equivalences or neither. -/
theorem mem_iff_of_natTrans {D E : Type} [SmallCategory D] [SmallCategory E] {f g : D ⥤ E}
    (α : f ⟶ g) : L.W f ↔ L.W g := by
  let H : Fin 2 × D ⥤ E := Functor.uncurry.obj (ComposableArrows.mk₁ α)
  have h0 : endIncl D 0 ⋙ H = f := CategoryTheory.Functor.ext (fun _ => rfl) fun x y φ => by
    simp only [Fin.isValue, endIncl, Functor.comp_obj, Functor.prod'_obj, Functor.const_obj_obj,
      Functor.id_obj, Functor.uncurry_obj_obj, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj,
      Functor.comp_map, Functor.prod'_map, Functor.const_obj_map, Functor.id_map,
      Functor.uncurry_obj_map, ComposableArrows.mk₁_map, ComposableArrows.Mk₁.map, Fin.zero_eta,
      NatTrans.id_app, Category.id_comp, eqToHom_naturality, eqToHom_refl, H]
    erw [eqToHom_refl, Category.id_comp]
  have h1 : endIncl D 1 ⋙ H = g := CategoryTheory.Functor.ext (fun _ => rfl) fun x y φ => by
    simp only [Fin.isValue, endIncl, Functor.comp_obj, Functor.prod'_obj, Functor.const_obj_obj,
      Functor.id_obj, Functor.uncurry_obj_obj, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj,
      Functor.comp_map, Functor.prod'_map, Functor.const_obj_map, Functor.id_map,
      Functor.uncurry_obj_map, ComposableArrows.mk₁_map, ComposableArrows.Mk₁.map,
      NatTrans.id_app, Category.id_comp, eqToHom_naturality, eqToHom_refl, H]
    erw [eqToHom_refl, Category.id_comp]
  have key : ∀ i, L.W (endIncl D i ⋙ H) ↔ L.W H := fun i =>
    ⟨L.of_comp_left _ _ (endIncl_mem L D i), L.comp_mem _ _ (endIncl_mem L D i)⟩
  rw [← h0, ← h1, key, key]

/-- **Contraction.** A category with an endofunctor `t` and natural transformations
`𝟭 ⟶ t ⟵ const d` is aspherical. -/
theorem isAspherical_of_contraction {D : Type} [SmallCategory D] (t : D ⥤ D) (d : D)
    (α : 𝟭 D ⟶ t) (β : (Functor.const D).obj d ⟶ t) : L.IsAspherical D := by
  have ht : L.W t := (mem_iff_of_natTrans L α).1 (L.id_mem _)
  have hc : L.W ((Functor.const D).obj d) := (mem_iff_of_natTrans L β).2 ht
  let i : Discrete PUnit.{1} ⥤ D := (Functor.const _).obj d
  refine L.of_retract i (Functor.star D) (Functor.punit_ext' _ _) ?_
  exact hc

end Homotopy

/-- An extension structure on `A`: an endofunctor `T` with a monomorphism `ι : 𝟭 ⟶ T`, such that
factoring through `ι` is reflected by `T`. -/
structure FacData (A : Type) [SmallCategory A] where
  T : A ⥤ A
  ι : 𝟭 A ⟶ T
  mono : ∀ a, Mono (ι.app a)
  fac_of : ∀ {z a b : A} (f : a ⟶ b) (k : z ⟶ T.obj a) (g : z ⟶ b),
    g ≫ ι.app b = k ≫ T.map f → ∃ g' : z ⟶ a, g' ≫ ι.app a = k

/-- A cone structure on `A`: adding a final vertex `T a` to each object `a`, the vertex being
`π a : p ⟶ T a`, natural in `a`. -/
structure ConeData (A : Type) [SmallCategory A] extends FacData A where
  p : A
  π : (Functor.const A).obj p ⟶ T
  not_fac_π : ∀ {z a : A} (h : z ⟶ p) (g : z ⟶ a), g ≫ ι.app a ≠ h ≫ π.app a

namespace FacData

attribute [local instance] Classical.propDecidable
variable {A : Type} [SmallCategory A] (D : FacData A)

/-- `Z` factors through `ι a`. -/
def Fac {a : A} (Z : Over (D.T.obj a)) : Prop := ∃ g : Z.left ⟶ a, g ≫ D.ι.app a = Z.hom

variable {D}

/-- The factored object. -/
noncomputable def lift {a : A} {Z : Over (D.T.obj a)} (h : D.Fac Z) : Over a := Over.mk h.choose

theorem lift_hom {a : A} {Z : Over (D.T.obj a)} (h : D.Fac Z) :
    (lift h).hom ≫ D.ι.app a = Z.hom := h.choose_spec

theorem fac_of_hom {a : A} {Z' Z : Over (D.T.obj a)} (φ : Z' ⟶ Z) (h : D.Fac Z) : D.Fac Z' :=
  ⟨φ.left ≫ h.choose, by rw [Category.assoc, h.choose_spec, Over.w φ]⟩

/-- The factored map. -/
noncomputable def liftMap {a : A} {Z' Z : Over (D.T.obj a)} (φ : Z' ⟶ Z) (h : D.Fac Z) :
    lift (fac_of_hom φ h) ⟶ lift h :=
  Over.homMk φ.left (by
    have := D.mono a
    change φ.left ≫ h.choose = (fac_of_hom φ h).choose
    rw [← cancel_mono (D.ι.app a), Category.assoc, h.choose_spec, (fac_of_hom φ h).choose_spec,
      Over.w φ])

variable (D)

/-- The object part of `χ`. -/
noncomputable def chiObj {a : A} (Z : Over (D.T.obj a)) : WithTerminal (Over a) :=
  if h : D.Fac Z then .of (lift h) else .star

variable {D}

theorem chiObj_pos {a : A} {Z : Over (D.T.obj a)} (h : D.Fac Z) :
    D.chiObj Z = .of (lift h) := by simp [chiObj, h]

theorem chiObj_neg {a : A} {Z : Over (D.T.obj a)} (h : ¬ D.Fac Z) :
    D.chiObj Z = .star := by simp [chiObj, h]

/-- An object not factoring through `ι a` goes to the terminal object. -/
noncomputable def chiTerminal {a : A} {Z : Over (D.T.obj a)} (h : ¬ D.Fac Z) :
    IsTerminal (D.chiObj Z) :=
  WithTerminal.starTerminal.ofIso (eqToIso (chiObj_neg h).symm)

variable (D)

/-- The map part of `χ`. -/
noncomputable def chiMap {a : A} {Z' Z : Over (D.T.obj a)} (φ : Z' ⟶ Z) :
    D.chiObj Z' ⟶ D.chiObj Z :=
  if h : D.Fac Z then
    eqToHom (chiObj_pos (fac_of_hom φ h)) ≫ WithTerminal.incl.map (liftMap φ h) ≫
      eqToHom (chiObj_pos h).symm
  else (chiTerminal h).from _

variable {D}

theorem chiMap_pos {a : A} {Z' Z : Over (D.T.obj a)} (φ : Z' ⟶ Z) (h : D.Fac Z) :
    D.chiMap φ = eqToHom (chiObj_pos (fac_of_hom φ h)) ≫ WithTerminal.incl.map (liftMap φ h) ≫
      eqToHom (chiObj_pos h).symm := by simp [chiMap, h]

variable (D)

/-- **`χ_a : A/T a ⥤ (A/a)▷`**: an object factoring through `ι a` goes to its factorisation,
the others to the added terminal object. -/
noncomputable def chi (a : A) : Over (D.T.obj a) ⥤ WithTerminal (Over a) where
  obj := D.chiObj
  map := D.chiMap
  map_id Z := by
    by_cases h : D.Fac Z
    · rw [chiMap_pos _ h]
      have : liftMap (𝟙 Z) h = 𝟙 _ := by ext; rfl
      rw [this]; erw [Category.id_comp, eqToHom_trans, eqToHom_refl]
    · exact (chiTerminal h).hom_ext _ _
  map_comp {Z'' Z' Z} φ ψ := by
    by_cases h : D.Fac Z
    · rw [chiMap_pos _ h, chiMap_pos _ h, chiMap_pos _ (fac_of_hom ψ h)]
      have : liftMap (φ ≫ ψ) h = liftMap φ (fac_of_hom ψ h) ≫ liftMap ψ h := by
        ext; rfl
      rw [this]; simp
    · exact (chiTerminal h).hom_ext _ _


variable {D}

theorem fac_map_ι {a : A} (X : Over a) : D.Fac ((Over.map (D.ι.app a)).obj X) := ⟨X.hom, rfl⟩

theorem choose_map_ι {a : A} (X : Over a) : (fac_map_ι (D := D) X).choose = X.hom := by
  have := D.mono a
  rw [← cancel_mono (D.ι.app a), (fac_map_ι X).choose_spec]; rfl

theorem lift_map_ι {a : A} (X : Over a) : lift (fac_map_ι (D := D) X) = X := by
  change Over.mk _ = Over.mk X.hom
  rw [choose_map_ι]

/-- `χ_a` restricted along `ι a` is the inclusion. -/
theorem map_ι_comp_chi (a : A) : Over.map (D.ι.app a) ⋙ D.chi a = WithTerminal.incl := by
  refine CategoryTheory.Functor.ext (fun X => (chiObj_pos (fac_map_ι X)).trans
    (congrArg WithTerminal.of (lift_map_ι X))) fun X Y φ => ?_
  change D.chiMap _ = _
  rw [chiMap_pos _ (fac_map_ι Y)]
  have : liftMap ((Over.map (D.ι.app a)).map φ) (fac_map_ι Y) =
      eqToHom (lift_map_ι X) ≫ φ ≫ eqToHom (lift_map_ι Y).symm := by
    ext
    simp only [Over.comp_left, Over.eqToHom_left]
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  rw [this, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

theorem not_fac_map_of {a x : A} {v : x ⟶ D.T.obj a}
    (hv : ∀ {z : A} (h : z ⟶ x) (g : z ⟶ a), g ≫ D.ι.app a ≠ h ≫ v) (X : Over x) :
    ¬ D.Fac ((Over.map v).obj X) :=
  fun ⟨g, hg⟩ => hv X.hom g hg

/-- `χ_a` restricted along a map `v` that nothing factors through `ι a` along is constant at the
added terminal object. -/
theorem map_comp_chi_of {a x : A} {v : x ⟶ D.T.obj a}
    (hv : ∀ {z : A} (h : z ⟶ x) (g : z ⟶ a), g ≫ D.ι.app a ≠ h ≫ v) :
    Over.map v ⋙ D.chi a = (Functor.const _).obj WithTerminal.star :=
  CategoryTheory.Functor.ext (fun X => chiObj_neg (not_fac_map_of hv X)) fun _ Y _ =>
    (chiTerminal (not_fac_map_of hv Y)).hom_ext _ _

theorem comp_T_eq {a b : A} (f : a ⟶ b) {Z : Over (D.T.obj a)} (h : D.Fac Z) :
    (h.choose ≫ f) ≫ D.ι.app b = Z.hom ≫ D.T.map f := by
  have n := D.ι.naturality f
  simp only [Functor.id_map] at n
  rw [Category.assoc, n, ← Category.assoc]
  exact congrArg (· ≫ D.T.map f) h.choose_spec

theorem fac_map_T {a b : A} (f : a ⟶ b) {Z : Over (D.T.obj a)} (h : D.Fac Z) :
    D.Fac ((Over.map (D.T.map f)).obj Z) :=
  ⟨h.choose ≫ f, comp_T_eq f h⟩

theorem fac_of_fac_map_T {a b : A} (f : a ⟶ b) {Z : Over (D.T.obj a)}
    (h : D.Fac ((Over.map (D.T.map f)).obj Z)) : D.Fac Z :=
  D.fac_of f Z.hom h.choose h.choose_spec

theorem choose_map_T {a b : A} (f : a ⟶ b) {Z : Over (D.T.obj a)} (h : D.Fac Z) :
    (fac_map_T (D := D) f h).choose = h.choose ≫ f := by
  have := D.mono b
  rw [← cancel_mono (D.ι.app b), (fac_map_T f h).choose_spec, comp_T_eq f h]; rfl

theorem lift_map_T {a b : A} (f : a ⟶ b) {Z : Over (D.T.obj a)} (h : D.Fac Z) :
    lift (fac_map_T (D := D) f h) = (Over.map f).obj (lift h) := by
  change Over.mk _ = Over.mk (h.choose ≫ f)
  rw [choose_map_T]

/-- `χ` is natural in `T`. -/
theorem map_T_comp_chi {a b : A} (f : a ⟶ b) :
    Over.map (D.T.map f) ⋙ D.chi b = D.chi a ⋙ WithTerminal.map (Over.map f) := by
  have hobj : ∀ Z, (Over.map (D.T.map f) ⋙ D.chi b).obj Z =
      (D.chi a ⋙ WithTerminal.map (Over.map f)).obj Z := fun Z => by
    by_cases h : D.Fac Z
    · change D.chiObj _ = (WithTerminal.map _).obj (D.chiObj Z)
      rw [chiObj_pos (fac_map_T f h), chiObj_pos h, lift_map_T]; rfl
    · change D.chiObj _ = (WithTerminal.map _).obj (D.chiObj Z)
      rw [chiObj_neg (fun h' => h (fac_of_fac_map_T f h')), chiObj_neg h]; rfl
  refine CategoryTheory.Functor.ext hobj fun Z' Z φ => ?_
  by_cases h : D.Fac ((Over.map (D.T.map f)).obj Z)
  · have hZ := fac_of_fac_map_T f h
    rw [conj_eqToHom_iff_heq _ _ _ (hobj Z)]
    change HEq (D.chiMap _) ((WithTerminal.map _).map (D.chiMap φ))
    rw [chiMap_pos _ h, chiMap_pos _ hZ]
    have : liftMap ((Over.map (D.T.map f)).map φ) h =
        eqToHom (lift_map_T f (fac_of_hom φ hZ)) ≫ (Over.map f).map (liftMap φ hZ) ≫
          eqToHom (lift_map_T f hZ).symm := by
      ext
      simp only [Over.comp_left, Over.eqToHom_left]
      erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    rw [this]
    simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_comp_eqToHom_iff, heq_eqToHom_comp_iff]
    rfl
  · exact (chiTerminal h).hom_ext _ _

end FacData
section Plus
variable {C : Type} [SmallCategory C] [HasTerminal C]

/-- `F ↦ F▷`, extended by the terminal object. -/
noncomputable def ext' {X : Type} [Category X] (F : X ⥤ C) : WithTerminal X ⥤ C :=
  WithTerminal.lift F (fun _ => terminal.from _) fun _ _ _ => terminal.hom_ext _ _

theorem incl_comp_ext' {X : Type} [Category X] (F : X ⥤ C) : WithTerminal.incl ⋙ ext' F = F :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ => by
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]; rfl

theorem const_comp_ext' {X Y : Type} [Category X] [Category Y] (F : X ⥤ C) :
    (Functor.const Y).obj WithTerminal.star ⋙ ext' F = (Functor.const Y).obj (⊤_ C) :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ => by simp [ext']; rfl

theorem map_comp_ext' {X Y : Type} [Category X] [Category Y] (G : X ⥤ Y) (F : Y ⥤ C) :
    WithTerminal.map G ⋙ ext' F = ext' (G ⋙ F) := by
  refine CategoryTheory.Functor.ext (fun x => by cases x <;> rfl) fun x y φ => ?_
  cases x <;> cases y
  all_goals first
    | exact φ.elim
    | (erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
    | exact terminal.hom_ext _ _

end Plus

namespace FacData
variable {A : Type} [SmallCategory A] (D : FacData A) {C : Type} [SmallCategory C] [HasTerminal C]

/-- `F⁺ : A/T a ⥤ C`: `F` on what factors through `ι a`, the terminal object elsewhere. -/
noncomputable def plus {a : A} (F : Over a ⥤ C) : Over (D.T.obj a) ⥤ C := D.chi a ⋙ ext' F

theorem map_ι_comp_plus {a : A} (F : Over a ⥤ C) : Over.map (D.ι.app a) ⋙ D.plus F = F := by
  rw [plus, ← Functor.assoc, map_ι_comp_chi, incl_comp_ext']

theorem map_comp_plus_of {a x : A} {v : x ⟶ D.T.obj a}
    (hv : ∀ {z : A} (h : z ⟶ x) (g : z ⟶ a), g ≫ D.ι.app a ≠ h ≫ v) (F : Over a ⥤ C) :
    Over.map v ⋙ D.plus F = (Functor.const _).obj (⊤_ C) := by
  rw [plus, ← Functor.assoc, map_comp_chi_of hv, const_comp_ext']

theorem map_T_comp_plus {a b : A} (f : a ⟶ b) (G : Over b ⥤ C) :
    Over.map (D.T.map f) ⋙ D.plus G = D.plus (Over.map f ⋙ G) := by
  rw [plus, plus, ← Functor.assoc, map_T_comp_chi, Functor.assoc, map_comp_ext']

/-- The underlying object of an element. -/
abbrev E (A : Type) [SmallCategory A] (C : Type) [SmallCategory C] := (iStar A C).Elementsᵒᵖ

/-- The functor carried by an element. -/
abbrev valF {C : Type} [SmallCategory C] (X : E A C) : Over X.unop.obj.unop ⥤ C := X.unop.val

/-- The contraction `(a, F) ↦ (T a, F⁺)`. -/
noncomputable def cone (C : Type) [SmallCategory C] [HasTerminal C] : E A C ⥤ E A C where
  obj X := op ((iStar A C).elementsMk (op (D.T.obj X.unop.obj.unop)) (D.plus (valF X)))
  map {X Y} φ := Quiver.Hom.op ⟨(D.T.map φ.unop.hom.unop).op,
    (map_T_comp_plus D φ.unop.hom.unop (valF Y)).trans (congrArg D.plus φ.unop.map_val)⟩
  map_id X := Quiver.Hom.unop_inj (Functor.Elements.Hom.ext (by
    change (D.T.map (𝟙 _)).op = _; rw [D.T.map_id]; rfl))
  map_comp φ ψ := Quiver.Hom.unop_inj (Functor.Elements.Hom.ext (by
    change (D.T.map (φ.unop.hom.unop ≫ ψ.unop.hom.unop)).op = _; rw [D.T.map_comp]; rfl))

/-- `𝟭 ⟶ cone`, by `ι`. -/
noncomputable def coneι (C : Type) [SmallCategory C] [HasTerminal C] : 𝟭 (E A C) ⟶ D.cone C where
  app X := Quiver.Hom.op ⟨(D.ι.app X.unop.obj.unop).op, map_ι_comp_plus D (valF X)⟩
  naturality X Y φ := Quiver.Hom.unop_inj (Functor.Elements.Hom.ext (by
    change (φ.unop.hom.unop ≫ D.ι.app _).op = (D.ι.app _ ≫ D.T.map φ.unop.hom.unop).op
    exact congrArg Quiver.Hom.op (D.ι.naturality φ.unop.hom.unop)))

end FacData

namespace ConeData
variable {A : Type} [SmallCategory A] (D : ConeData A) {C : Type} [SmallCategory C] [HasTerminal C]

open FacData

/-- The cone point of `A/i_A^*(C)`: the vertex `p` with the constant functor. -/
noncomputable def pt (C : Type) [SmallCategory C] [HasTerminal C] : E A C :=
  op ((iStar A C).elementsMk (op D.p) ((Functor.const _).obj (⊤_ C)))

/-- `const pt ⟶ cone`, by `π`. -/
noncomputable def coneπ (C : Type) [SmallCategory C] [HasTerminal C] :
    (Functor.const (E A C)).obj (D.pt C) ⟶ D.toFacData.cone C where
  app X := Quiver.Hom.op ⟨(D.π.app X.unop.obj.unop).op,
    map_comp_plus_of D.toFacData D.not_fac_π (valF X)⟩
  naturality X Y φ := Quiver.Hom.unop_inj (Functor.Elements.Hom.ext (by
    change (𝟙 _ ≫ D.π.app _).op = (D.π.app _ ≫ D.T.map φ.unop.hom.unop).op
    exact congrArg Quiver.Hom.op (D.π.naturality φ.unop.hom.unop)))

include D in
/-- **A category with cone data is a weak test category**, for every fundamental localizer. -/
theorem isWeakTest (L : FundamentalLocalizer.{0}) : IsWeakTest A L := fun C _ _ =>
  isAspherical_of_contraction L (D.toFacData.cone C) (D.pt C) (D.toFacData.coneι C) (D.coneπ C)

end ConeData

namespace SimplexCone
open SimplexCategory

/-- Extend a monotone map by sending the new top to the new top. -/
def extTop {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) : Fin (m + 2) →o Fin (n + 2) where
  toFun := Fin.lastCases (Fin.last _) fun i => (f i).castSucc
  monotone' i j hij := by
    induction j using Fin.lastCases with
    | last => simp [Fin.le_last]
    | cast j =>
      induction i using Fin.lastCases with
      | last => exact absurd hij (by simp)
      | cast i => simpa using f.monotone (by simpa using hij)

@[simp] theorem extTop_last {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    extTop f (Fin.last _) = Fin.last _ := by
  change Fin.lastCases (motive := fun _ => Fin (n + 2)) _ _ _ = _; exact Fin.lastCases_last

@[simp] theorem extTop_castSucc {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    extTop f i.castSucc = (f i).castSucc := by
  change Fin.lastCases (motive := fun _ => Fin (n + 2)) _ _ _ = _
  exact Fin.lastCases_castSucc _

/-- `T : Δ ⥤ Δ`, `[n] ↦ [n + 1]`, adding a final vertex. -/
def T : SimplexCategory ⥤ SimplexCategory where
  obj x := SimplexCategory.mk (x.len + 1)
  map f := Hom.mk (extTop f.toOrderHom)
  map_id x := by
    ext i; induction i using Fin.lastCases <;> simp
  map_comp f g := by
    ext i; induction i using Fin.lastCases <;> simp

/-- `ι : 𝟭 ⟶ T`, the inclusion of `[n]` as the first `n + 1` vertices. -/
def ι : 𝟭 SimplexCategory ⟶ T where
  app x := Hom.mk (Fin.castSuccOrderEmb (n := x.len + 1)).toOrderHom
  naturality x y f := by
    ext i
    change ((f.toOrderHom i).castSucc : ℕ) = (extTop f.toOrderHom i.castSucc : ℕ)
    rw [extTop_castSucc]

theorem ι_apply (x : SimplexCategory) (i : Fin (x.len + 1)) :
    (ι.app x).toOrderHom i = i.castSucc := rfl

instance (x : SimplexCategory) : Mono (ι.app x) := by
  rw [SimplexCategory.mono_iff_injective]
  exact Fin.castSucc_injective _

/-- `π : const [0] ⟶ T`, the new final vertex. -/
def π : (Functor.const SimplexCategory).obj (SimplexCategory.mk 0) ⟶ T where
  app x := const _ _ (Fin.last (x.len + 1))
  naturality x y f := by ext i; simp [T]

theorem T_map_apply {x y : SimplexCategory} (f : x ⟶ y) (i : Fin (x.len + 2)) :
    (T.map f).toOrderHom i = extTop f.toOrderHom i := rfl

theorem not_fac_π {z a : SimplexCategory} (h : z ⟶ SimplexCategory.mk 0) (g : z ⟶ a) :
    g ≫ ι.app a ≠ h ≫ π.app a := by
  intro e
  have := congrArg (fun φ => ((Hom.toOrderHom φ) 0 : ℕ)) e
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply] at this
  change (((g.toOrderHom 0).castSucc : Fin _) : ℕ) = ((Fin.last (a.len + 1) : Fin _) : ℕ) at this
  have := (g.toOrderHom 0).isLt
  simp at *; omega

theorem extTop_val_of {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) {j : Fin (m + 2)}
    (hj : (j : ℕ) = m + 1) : (extTop f j : ℕ) = n + 1 := by
  have : j = Fin.last _ := Fin.ext hj
  subst this; simp

theorem fac_of {z a b : SimplexCategory} (f : a ⟶ b) (k : z ⟶ T.obj a) (g : z ⟶ b)
    (e : g ≫ ι.app b = k ≫ T.map f) : ∃ g' : z ⟶ a, g' ≫ ι.app a = k := by
  have hk : ∀ i, ((k.toOrderHom i : Fin (a.len + 2)) : ℕ) < a.len + 1 := by
    intro i
    by_contra hi
    have hv : ((k.toOrderHom i : Fin (a.len + 2)) : ℕ) = a.len + 1 := by
      have := (k.toOrderHom i).isLt
      change _ < a.len + 1 + 1 at this
      omega
    have := congrArg (fun φ => ((Hom.toOrderHom φ) i : ℕ)) e
    simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply] at this
    change (((g.toOrderHom i).castSucc : Fin _) : ℕ) = (extTop f.toOrderHom (k.toOrderHom i) : ℕ)
      at this
    rw [extTop_val_of f.toOrderHom hv] at this
    have := (g.toOrderHom i).isLt
    simp at *; omega
  refine ⟨Hom.mk ⟨fun i => (⟨(k.toOrderHom i : ℕ), hk i⟩ : Fin (a.len + 1)), fun i j hij => ?_⟩, ?_⟩
  · exact k.toOrderHom.monotone hij
  · ext i; rfl

/-- The cone data of `Δ`: adding a final vertex. -/
def coneData : ConeData SimplexCategory where
  T := T
  ι := ι
  mono := inferInstance
  p := SimplexCategory.mk 0
  π := π
  not_fac_π := not_fac_π
  fac_of := fac_of

/-- **`Δ` is a weak test category**, for every fundamental localizer. -/
theorem isWeakTest_simplexCategory (L : FundamentalLocalizer.{0}) : IsWeakTest SimplexCategory L :=
  coneData.isWeakTest L

/-- Extend a monotone map by sending the new top to the top. -/
def extBy {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) : Fin (m + 2) →o Fin (n + 1) where
  toFun := Fin.lastCases (Fin.last _) fun i => f i
  monotone' i j hij := by
    induction j using Fin.lastCases with
    | last => simp [Fin.le_last]
    | cast j =>
      induction i using Fin.lastCases with
      | last => exact absurd hij (by simp)
      | cast i => simpa using f.monotone (by simpa using hij)

theorem extBy_last {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) :
    extBy f (Fin.last _) = Fin.last _ := by
  change Fin.lastCases (motive := fun _ => Fin (n + 1)) _ _ _ = _; exact Fin.lastCases_last

theorem extBy_castSucc {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    extBy f i.castSucc = f i := by
  change Fin.lastCases (motive := fun _ => Fin (n + 1)) _ _ _ = _
  exact Fin.lastCases_castSucc _

theorem extBy_extTop {l m n : ℕ} (g : Fin (m + 1) →o Fin (n + 1)) (f : Fin (l + 1) →o Fin (m + 1))
    (j : Fin (l + 2)) : extBy g (extTop f j) = extBy (g.comp f) j := by
  induction j using Fin.lastCases with
  | last => rw [extTop_last, extBy_last, extBy_last]
  | cast i => rw [extTop_castSucc, extBy_castSucc, extBy_castSucc]; rfl

section Slice
variable (b : SimplexCategory)

/-- The structure map of the cone `T Y → b`, the new vertex going to the top of `b`. -/
def top (Y : Over b) : T.obj Y.left ⟶ b := Hom.mk (extBy Y.hom.toOrderHom)

theorem ι_top (Y : Over b) : ι.app Y.left ≫ top b Y = Y.hom := by
  ext i
  change (extBy Y.hom.toOrderHom i.castSucc : ℕ) = _
  rw [extBy_castSucc]

theorem T_map_top {Y Y' : Over b} (φ : Y ⟶ Y') :
    T.map φ.left ≫ top b Y' = top b Y := by
  have hw : Y'.hom.toOrderHom.comp φ.left.toOrderHom = Y.hom.toOrderHom := by
    rw [← comp_toOrderHom, Over.w φ]
  ext i
  exact congrArg Fin.val ((extBy_extTop Y'.hom.toOrderHom φ.left.toOrderHom i).trans
    (congrArg (fun g => extBy g i) hw))

/-- `T` on `Δ/b`. -/
def Tb : Over b ⥤ Over b where
  obj Y := Over.mk (top b Y)
  map φ := Over.homMk (T.map φ.left) (T_map_top b φ)
  map_id _ := Over.OverMorphism.ext (T.map_id _)
  map_comp _ _ := Over.OverMorphism.ext (T.map_comp _ _)

/-- `ι` on `Δ/b`. -/
def ιb : 𝟭 (Over b) ⟶ Tb b where
  app Y := Over.homMk (ι.app Y.left) (ι_top b Y)
  naturality _ _ φ := Over.OverMorphism.ext (ι.naturality φ.left)

/-- The cone vertex of `Δ/b`: `[0]` over the top of `b`. -/
def pb : Over b := Over.mk (const (SimplexCategory.mk 0) b (Fin.last _))

theorem π_top (Y : Over b) : π.app Y.left ≫ top b Y = (pb b).hom := by
  ext i
  change (extBy Y.hom.toOrderHom (Fin.last _) : ℕ) = _
  rw [extBy_last]; rfl

/-- `π` on `Δ/b`. -/
def πb : (Functor.const (Over b)).obj (pb b) ⟶ Tb b where
  app Y := Over.homMk (π.app Y.left) (π_top b Y)
  naturality _ _ φ := Over.OverMorphism.ext (π.naturality φ.left)

/-- The cone data of `Δ/b`. -/
def coneDataOver : ConeData (Over b) where
  T := Tb b
  ι := ιb b
  mono Y := by
    have : Mono ((ιb b).app Y).left := inferInstanceAs (Mono (ι.app Y.left))
    exact Over.mono_of_mono_left _
  p := pb b
  π := πb b
  not_fac_π h g e := not_fac_π h.left g.left (congrArg CommaMorphism.left e)
  fac_of {Z Y Y'} f k g e := by
    obtain ⟨g', hg'⟩ := fac_of f.left k.left g.left (congrArg CommaMorphism.left e)
    refine ⟨Over.homMk g' ?_, ?_⟩
    · rw [← ι_top b Y, ← Category.assoc, hg']
      exact Over.w k
    · exact Over.OverMorphism.ext hg'

end Slice

/-- **`Δ` is a local test category**, for every fundamental localizer. -/
theorem isLocalTest_simplexCategory (L : FundamentalLocalizer.{0}) :
    IsLocalTest SimplexCategory L := fun b => (coneDataOver b).isWeakTest L

/-- **`Δ` is a test category**, for every fundamental localizer: Grothendieck's founding
example, proved from the axioms alone. -/
theorem isTest_simplexCategory (L : FundamentalLocalizer.{0}) :
    IsWeakTest SimplexCategory L ∧ IsLocalTest SimplexCategory L :=
  ⟨isWeakTest_simplexCategory L, isLocalTest_simplexCategory L⟩

end SimplexCone

end LeanPool.ToposTheoreticBridges.Examples
