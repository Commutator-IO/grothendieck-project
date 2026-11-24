/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Bridges.SimplexTest

/-!
# Grothendieck's criterion for local test categories

In the axiomatic setting of `Bridges.FundamentalLocalizers`, this file proves Grothendieck's
criterion (Cisinski, Astérisque 308, Th. 4.1.19): a small category `A` is a local test category
iff its Lawvere object `L_A = i_A^*(Δ¹)` is locally aspherical, that is, iff every `A/(a × L_A)`
is aspherical (`isLocalTest_iff_isLocallyAspherical`). No hypothesis on `W` is needed.

* `prodY`, `hatMap`: the presheaf `a × X` and the functor `A/(a × X) ⥤ A/(a × Y)` induced by a
  map `X ⟶ Y`, strictly functorial;
* `isAspherical_iff_of_retraction`: two categories are aspherical together when one is a
  retract of the other up to a natural transformation;
* `isAspherical_slice_iff`: `(A/a)/i_{A/a}^*(C)` and `A/(a × i_A^*(C))` are aspherical together,
  through the iterated slices (`forward_backward`, `map_backward`);
* `pmap_mem`: if `L_A` is locally aspherical, the projection
  `A/(a × i_A^*(Δ¹ × C)) ⥤ A/(a × i_A^*(C))` is a `W`-equivalence. Its slices retract onto
  `A/(b × L_A)`, by relative Theorem A (`sliceIn`, `sliceOut`, `sliceUnit`);
* `isAspherical_prodY_of_pmap`: Grothendieck's homotopy argument. The contraction
  `Δ¹ × C ⥤ C` of `C` onto its terminal object (`contr`) gives `i_A^*(Δ¹ × C) ⟶ i_A^*(C)`. Its
  end `0` is the identity, and its end `1` factors through the terminal presheaf. So
  `A/(a × i_A^*(C))` retracts onto `A/(a × 1) = A/a`, which has a terminal object.
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace LeanPool.ToposTheoreticBridges.Examples

section Criterion
variable (L : FundamentalLocalizer.{0})

/-- Asphericity passes along a retraction up to a natural transformation. -/
theorem isAspherical_of_retraction {S T : Type} [SmallCategory S] [SmallCategory T]
    (i : T ⥤ S) (r : S ⥤ T) (h : i ⋙ r = 𝟭 T) (α : 𝟭 S ⟶ r ⋙ i) (hT : L.IsAspherical T) :
    L.IsAspherical S := by
  have hri : L.W (r ⋙ i) := (mem_iff_of_natTrans L α).1 (L.id_mem _)
  have hr : L.W r := L.of_retract i r h hri
  unfold FundamentalLocalizer.IsAspherical at hT ⊢
  rw [Functor.punit_ext' (Functor.star S) (r ⋙ Functor.star T)]
  exact L.comp_mem _ _ hr hT

theorem isAspherical_of_retraction' {S T : Type} [SmallCategory S] [SmallCategory T]
    (i : T ⥤ S) (r : S ⥤ T) (h : i ⋙ r = 𝟭 T) (α : r ⋙ i ⟶ 𝟭 S) (hT : L.IsAspherical T) :
    L.IsAspherical S := by
  have hri : L.W (r ⋙ i) := (mem_iff_of_natTrans L α).2 (L.id_mem _)
  have hr : L.W r := L.of_retract i r h hri
  unfold FundamentalLocalizer.IsAspherical at hT ⊢
  rw [Functor.punit_ext' (Functor.star S) (r ⋙ Functor.star T)]
  exact L.comp_mem _ _ hr hT

/-- The same, as an equivalence. -/
theorem isAspherical_iff_of_retraction {S T : Type} [SmallCategory S] [SmallCategory T]
    (i : T ⥤ S) (r : S ⥤ T) (h : i ⋙ r = 𝟭 T) (α : 𝟭 S ⟶ r ⋙ i) :
    L.IsAspherical S ↔ L.IsAspherical T := by
  have hri : L.W (r ⋙ i) := (mem_iff_of_natTrans L α).1 (L.id_mem _)
  have hr : L.W r := L.of_retract i r h hri
  unfold FundamentalLocalizer.IsAspherical
  rw [Functor.punit_ext' (Functor.star S) (r ⋙ Functor.star T)]
  exact ⟨L.of_comp_left _ _ hr, L.comp_mem _ _ hr⟩

end Criterion

variable {A : Type} [SmallCategory A]

/-- The presheaf `a × X`. -/
@[simps]
def prodY (a : A) (X : Aᵒᵖ ⥤ Type) : Aᵒᵖ ⥤ Type where
  obj b := (b.unop ⟶ a) × X.obj b
  map g := ↾fun p => (g.unop ≫ p.1, X.map g p.2)
  map_id b := by ext p <;> simp
  map_comp f g := by ext p <;> simp

/-- `a × α`. -/
@[simps]
def prodMap (a : A) {X Y : Aᵒᵖ ⥤ Type} (α : X ⟶ Y) : prodY a X ⟶ prodY a Y where
  app b := ↾fun p => (p.1, α.app b p.2)
  naturality b b' g := by
    ext p
    refine Prod.ext rfl ?_
    change α.app b' (X.map g p.2) = Y.map g (α.app b p.2)
    exact NatTrans.naturality_apply α g p.2

/-- The category of elements `A/X`. -/
abbrev El (X : Aᵒᵖ ⥤ Type) := X.Elementsᵒᵖ

/-- `A/(a × α)`. -/
def hatMap (a : A) {X Y : Aᵒᵖ ⥤ Type} (α : X ⟶ Y) : El (prodY a X) ⥤ El (prodY a Y) :=
  (NatTrans.mapElements (prodMap a α)).op

theorem hatMap_comp (a : A) {X Y Z : Aᵒᵖ ⥤ Type} (α : X ⟶ Y) (β : Y ⟶ Z) :
    hatMap a (α ≫ β) = hatMap a α ⋙ hatMap a β := rfl

theorem hatMap_id (a : A) (X : Aᵒᵖ ⥤ Type) : hatMap a (𝟙 X) = 𝟭 _ := rfl

section Core
variable (A) (C : Type) [SmallCategory C]

/-- `i_A^*(Δ¹ × C) ⟶ i_A^*(C)`, the projection. -/
def pmap : iStar A (Fin 2 × C) ⟶ iStar A C where
  app _ := ↾fun F => F ⋙ CategoryTheory.Prod.snd _ _
  naturality _ _ _ := rfl

/-- `i_A^*(C) ⟶ i_A^*(Δ¹ × C)`, the end `i`. -/
def smap (i : Fin 2) : iStar A C ⟶ iStar A (Fin 2 × C) where
  app _ := ↾fun F => ((Functor.const _).obj i).prod' F
  naturality _ _ _ := rfl

theorem smap_pmap (i : Fin 2) : smap A C i ≫ pmap A C = 𝟙 _ := rfl

variable [HasTerminal C]

/-- The contraction `Δ¹ × C ⥤ C` of `C` onto its terminal object. -/
noncomputable def contr : Fin 2 × C ⥤ C :=
  Functor.uncurry.obj (ComposableArrows.mk₁
    ({ app := fun _ => terminal.from _ } : 𝟭 C ⟶ (Functor.const C).obj (⊤_ C)))

/-- `i_A^*(Δ¹ × C) ⟶ i_A^*(C)`, along the contraction. -/
noncomputable def hmap : iStar A (Fin 2 × C) ⟶ iStar A C where
  app _ := ↾fun F => F ⋙ contr C
  naturality _ _ _ := rfl

/-- The terminal presheaf. -/
abbrev one : Aᵒᵖ ⥤ Type := (Functor.const _).obj PUnit

/-- `i_A^*(C) ⟶ 1`. -/
def rmap : iStar A C ⟶ one A where
  app _ := ↾fun _ => PUnit.unit

/-- `1 ⟶ i_A^*(C)`, the constant functor at the terminal object. -/
noncomputable def σmap : one A ⟶ iStar A C where
  app _ := ↾fun _ => (Functor.const _).obj (⊤_ C)
  naturality _ _ _ := rfl

theorem σmap_rmap : σmap A C ≫ rmap A C = 𝟙 _ := rfl

omit [HasTerminal C] in
theorem const_prod'_uncurry {D E X : Type} [Category D] [Category E] [Category X]
    (G : Fin 2 ⥤ (D ⥤ E)) (i : Fin 2) (F : X ⥤ D) :
    ((Functor.const X).obj i).prod' F ⋙ Functor.uncurry.obj G = F ⋙ G.obj i :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun x y φ => by simp

theorem smap_zero_hmap : smap A C 0 ≫ hmap A C = 𝟙 _ := by
  ext b F
  exact const_prod'_uncurry _ 0 F

theorem smap_one_hmap : smap A C 1 ≫ hmap A C = rmap A C ≫ σmap A C := by
  ext b F
  exact (const_prod'_uncurry _ 1 F).trans
    (CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ => terminal.hom_ext _ _)

/-- `A/(a × 1) = A/a` has a terminal object, `𝟙 a`. -/
def prodOneTerminal (a : A) :
    IsTerminal (op ((prodY a (one A)).elementsMk (op a) (𝟙 a, PUnit.unit)) :
    El (prodY a (one A))) :=
  IsTerminal.ofUniqueHom
    (fun X => Quiver.Hom.op ⟨X.unop.val.1.op, Prod.ext (Category.comp_id _) rfl⟩)
    fun X m => Quiver.Hom.unop_inj (Functor.Elements.Hom.ext (by
      have := congrArg Prod.fst m.unop.map_val
      change m.unop.hom.unop ≫ 𝟙 a = X.unop.val.1 at this
      rw [Category.comp_id] at this
      exact congrArg Quiver.Hom.op this))

/-- **The homotopy core of Grothendieck's criterion.** If the projection
`A/(a × i_A^*(Δ¹ × C)) ⥤ A/(a × i_A^*(C))` is a `W`-equivalence, then `A/(a × i_A^*(C))` is
aspherical: the end `0` of the contraction `Δ¹ × C ⥤ C` is the identity, the end `1` factors
through `A/(a × 1) = A/a`, which has a terminal object. -/
theorem isAspherical_prodY_of_pmap (L : FundamentalLocalizer.{0}) (C : Type) [SmallCategory C]
    [HasTerminal C] (a : A) (hp : L.W (hatMap a (pmap A C))) :
    L.IsAspherical (El (prodY a (iStar A C))) := by
  have hs : ∀ i, L.W (hatMap a (smap A C i)) := fun i =>
    L.of_comp_right _ _ hp (by rw [← hatMap_comp, smap_pmap, hatMap_id]; exact L.id_mem _)
  have hH : L.W (hatMap a (hmap A C)) :=
    L.of_comp_left _ _ (hs 0) (by rw [← hatMap_comp, smap_zero_hmap, hatMap_id]; exact L.id_mem _)
  have hc : L.W (hatMap a (rmap A C) ⋙ hatMap a (σmap A C)) := by
    rw [← hatMap_comp, ← smap_one_hmap, hatMap_comp]; exact L.comp_mem _ _ (hs 1) hH
  have hr : L.W (hatMap a (rmap A C)) :=
    L.of_retract _ _ (by rw [← hatMap_comp, σmap_rmap, hatMap_id]) hc
  have : HasTerminal (El (prodY a (one A))) := (prodOneTerminal A a).hasTerminal
  unfold FundamentalLocalizer.IsAspherical
  rw [Functor.punit_ext' (Functor.star _) (hatMap a (rmap A C) ⋙ Functor.star _)]
  exact L.comp_mem _ _ hr (L.star_mem_of_hasTerminal _)

end Core

section Slices
variable (C : Type) [SmallCategory C] (a : A) (e : El (prodY a (iStar A C)))

/-- The vertex of `e`. -/
abbrev eb : A := e.unop.obj.unop
/-- The map to `a` of `e`. -/
abbrev ef : eb C a e ⟶ a := e.unop.val.1
/-- The section of `e`. -/
abbrev ex : Over (eb C a e) ⥤ C := e.unop.val.2

/-- The slice of the projection over `e`. -/
abbrev Src := CostructuredArrow (hatMap a (pmap A C) ⋙ 𝟭 _) e

/-- `A/(b × L_A) ⥤` the slice over `e = (b, f, x)`: `(g, l) ↦ (g ≫ f, (l, g^*x))`. -/
def sliceIn : El (prodY (eb C a e) (iStar A (Fin 2))) ⥤ Src C a e where
  obj t := CostructuredArrow.mk (Y := op ((prodY a (iStar A (Fin 2 × C))).elementsMk t.unop.obj
      (t.unop.val.1 ≫ ef C a e, (t.unop.val.2 : Over _ ⥤ Fin 2).prod'
        (Over.map t.unop.val.1 ⋙ ex C a e))))
    (Quiver.Hom.op ⟨t.unop.val.1.op, rfl⟩)
  map {t t'} φ := CostructuredArrow.homMk (Quiver.Hom.op ⟨φ.unop.hom, by
      have h1 : φ.unop.hom.unop ≫ t'.unop.val.1 = t.unop.val.1 :=
        congrArg Prod.fst φ.unop.map_val
      have h2 : Over.map φ.unop.hom.unop ⋙ (t'.unop.val.2 : Over _ ⥤ Fin 2) = t.unop.val.2 :=
        congrArg Prod.snd φ.unop.map_val
      refine Prod.ext ?_ ?_
      · change φ.unop.hom.unop ≫ t'.unop.val.1 ≫ ef C a e = t.unop.val.1 ≫ ef C a e
        rw [← h1, Category.assoc]
      · change Over.map φ.unop.hom.unop ⋙ ((t'.unop.val.2 : Over _ ⥤ Fin 2).prod'
          (Over.map t'.unop.val.1 ⋙ ex C a e)) = (t.unop.val.2 : Over _ ⥤ Fin 2).prod'
          (Over.map t.unop.val.1 ⋙ ex C a e)
        rw [← h2, ← h1, over_map_comp_eq]
        rfl⟩) (Quiver.Hom.unop_inj (Functor.Elements.Hom.ext (by
      have h1 : φ.unop.hom.unop ≫ t'.unop.val.1 = t.unop.val.1 :=
        congrArg Prod.fst φ.unop.map_val
      change t'.unop.val.1.op ≫ φ.unop.hom = t.unop.val.1.op
      rw [← h1]; rfl)))
  map_id _ := CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj (Functor.Elements.Hom.ext rfl))
  map_comp _ _ :=
    CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj (Functor.Elements.Hom.ext rfl))

/-- The slice over `e` ⥤ `A/(b × L_A)`: forget `x`. -/
def sliceOut : Src C a e ⥤ El (prodY (eb C a e) (iStar A (Fin 2))) where
  obj s := op ((prodY (eb C a e) (iStar A (Fin 2))).elementsMk s.left.unop.obj
    (s.hom.unop.hom.unop,
      (s.left.unop.val.2 : Over _ ⥤ Fin 2 × C) ⋙ CategoryTheory.Prod.fst _ _))
  map {s s'} ψ := Quiver.Hom.op ⟨ψ.left.unop.hom, by
    have hw := congrArg (fun m => m.unop.hom) ψ.w
    have h2 : Over.map ψ.left.unop.hom.unop ⋙ (s'.left.unop.val.2 : Over _ ⥤ Fin 2 × C) =
        s.left.unop.val.2 := congrArg Prod.snd ψ.left.unop.map_val
    refine Prod.ext ?_ ?_
    · change ψ.left.unop.hom.unop ≫ s'.hom.unop.hom.unop = s.hom.unop.hom.unop
      exact congrArg Quiver.Hom.unop hw
    · change Over.map ψ.left.unop.hom.unop ⋙ (s'.left.unop.val.2 : Over _ ⥤ Fin 2 × C) ⋙
        CategoryTheory.Prod.fst _ _ = (s.left.unop.val.2 : Over _ ⥤ Fin 2 × C) ⋙
          CategoryTheory.Prod.fst _ _
      rw [← h2]; rfl⟩
  map_id _ := Quiver.Hom.unop_inj (Functor.Elements.Hom.ext rfl)
  map_comp _ _ := Quiver.Hom.unop_inj (Functor.Elements.Hom.ext rfl)

theorem sliceIn_sliceOut : sliceIn C a e ⋙ sliceOut C a e = 𝟭 _ := rfl

/-- `𝟭 ⟶ sliceOut ⋙ sliceIn`, the identity on vertices. -/
def sliceUnit : 𝟭 (Src C a e) ⟶ sliceOut C a e ⋙ sliceIn C a e where
  app s := CostructuredArrow.homMk (Quiver.Hom.op ⟨𝟙 _, by
    have hm := s.hom.unop.map_val
    have h1 : s.hom.unop.hom.unop ≫ ef C a e = s.left.unop.val.1 := congrArg Prod.fst hm
    have h2 : Over.map s.hom.unop.hom.unop ⋙ ex C a e =
        (s.left.unop.val.2 : Over _ ⥤ Fin 2 × C) ⋙ CategoryTheory.Prod.snd _ _ :=
      congrArg Prod.snd hm
    refine Prod.ext ?_ ?_
    · change 𝟙 _ ≫ s.hom.unop.hom.unop ≫ ef C a e = s.left.unop.val.1
      rw [Category.id_comp, h1]
    · change Over.map (𝟙 _) ⋙ ((s.left.unop.val.2 : Over _ ⥤ Fin 2 × C) ⋙
        CategoryTheory.Prod.fst _ _).prod' (Over.map s.hom.unop.hom.unop ⋙ ex C a e) =
          s.left.unop.val.2
      rw [over_map_id_eq]
      exact congrArg (fun G => ((s.left.unop.val.2 : Over _ ⥤ Fin 2 × C) ⋙
        CategoryTheory.Prod.fst _ _).prod' G) h2⟩)
    (Quiver.Hom.unop_inj (Functor.Elements.Hom.ext (by
      exact Category.comp_id (obj := Aᵒᵖ) _)))
  naturality _ _ _ := CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj
    (Functor.Elements.Hom.ext (by
      exact (Category.id_comp (obj := Aᵒᵖ) _).trans (Category.comp_id (obj := Aᵒᵖ) _).symm)))

/-- `W` contains the projection `A/(a × i_A^*(Δ¹ × C)) ⥤ A/(a × i_A^*(C))` as soon as `L_A` is
locally aspherical: its slices retract onto `A/(b × L_A)` (Theorem A). -/
theorem pmap_mem (L : FundamentalLocalizer.{0})
    (hL : ∀ b : A, L.IsAspherical (El (prodY b (iStar A (Fin 2))))) (C : Type) [SmallCategory C]
    (a : A) : L.W (hatMap a (pmap A C)) := by
  refine L.mem_of_costructuredArrow _ (𝟭 _) fun e => ?_
  have hsrc : L.IsAspherical (Src C a e) :=
    (isAspherical_iff_of_retraction L (sliceIn C a e) (sliceOut C a e) (sliceIn_sliceOut C a e)
      (sliceUnit C a e)).2 (hL _)
  have : HasTerminal (CostructuredArrow (𝟭 (El (prodY a (iStar A C)))) e) :=
    CostructuredArrow.mkIdTerminal.hasTerminal
  refine L.of_comp_right _ (Functor.star _) (L.star_mem_of_hasTerminal _) ?_
  rw [Functor.punit_ext' (_ ⋙ Functor.star _) (Functor.star (Src C a e))]
  exact hsrc

end Slices

section Compare
variable (C : Type) [SmallCategory C] (a : A)

theorem forward_backward (Y : Over a) :
    Over.iteratedSliceForward Y ⋙ Over.iteratedSliceBackward Y = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun Z => ?_) fun Z Z' κ => ?_
  · obtain ⟨⟨l, ⟨⟨⟩⟩, h⟩, ⟨⟨⟩⟩, ⟨g, ⟨⟨⟩⟩, w⟩⟩ := Z
    change l ⟶ Y.left at g
    have w' : g ≫ Y.hom = h := by simpa using w
    subst w'
    rfl
  · ext
    simp only [Functor.comp_map, Functor.id_map, Over.comp_left, Over.eqToHom_left]
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

theorem over_mk_eq {Y' : Over a} {l : A} (k : l ⟶ Y'.left) {p : l ⟶ a} (hp : p = k ≫ Y'.hom)
    (q : Over.mk p ⟶ Y') (hq : q.left = k) :
    Over.mk q = Over.mk (Over.homMk k : Over.mk (k ≫ Y'.hom) ⟶ Y') := by
  subst hp
  congr 1
  exact Over.OverMorphism.ext hq

theorem map_backward {Y Y' : Over a} (m : Y ⟶ Y') :
    Over.map m.left ⋙ Over.iteratedSliceBackward Y' =
      Over.iteratedSliceBackward Y ⋙ Over.map m := by
  refine CategoryTheory.Functor.ext (fun g => ?_) fun g g' κ => ?_
  · change Over.mk (Over.homMk (g.hom ≫ m.left) : Over.mk ((g.hom ≫ m.left) ≫ Y'.hom) ⟶ Y') =
      Over.mk ((Over.homMk g.hom : Over.mk (g.hom ≫ Y.hom) ⟶ Y) ≫ m)
    exact (over_mk_eq a (g.hom ≫ m.left) (by rw [Category.assoc, Over.w m]) _ rfl).symm
  · ext
    simp only [Functor.comp_map, Over.comp_left, Over.eqToHom_left]
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- The functor carried by an element of `A/(a × i_A^*(C))`. -/
abbrev tF (t : El (prodY a (iStar A C))) : Over t.unop.obj.unop ⥤ C := t.unop.val.2

/-- The functor carried by an element of `(A/a)/i_{A/a}^*(C)`. -/
abbrev sG (s : (iStar (Over a) C).Elementsᵒᵖ) : Over s.unop.obj.unop ⥤ C := s.unop.val

/-- `A/(a × X) ⥤ (A/a)/X`, `(b, f, F) ↦ (f, F)`, for `X = i_A^*(C)`. -/
def toSlice : El (prodY a (iStar A C)) ⥤ (iStar (Over a) C).Elementsᵒᵖ where
  obj t := op ((iStar (Over a) C).elementsMk (op (Over.mk t.unop.val.1))
    (Over.iteratedSliceForward (Over.mk t.unop.val.1) ⋙ tF C a t))
  map {t t'} φ := Quiver.Hom.op ⟨(Over.homMk φ.unop.hom.unop
      (congrArg Prod.fst φ.unop.map_val) : Over.mk t.unop.val.1 ⟶ Over.mk t'.unop.val.1).op, by
    have h2 : Over.map φ.unop.hom.unop ⋙ tF C a t' = tF C a t :=
      congrArg Prod.snd φ.unop.map_val
    exact congrArg (fun F => Over.iteratedSliceForward (Over.mk t.unop.val.1) ⋙ F) h2⟩
  map_id _ := Quiver.Hom.unop_inj (Functor.Elements.Hom.ext rfl)
  map_comp _ _ := Quiver.Hom.unop_inj (Functor.Elements.Hom.ext rfl)

/-- `(A/a)/X ⥤ A/(a × X)`, `(Y, G) ↦ (Y.left, Y.hom, G)`, for `X = i_A^*(C)`. -/
def fromSlice : (iStar (Over a) C).Elementsᵒᵖ ⥤ El (prodY a (iStar A C)) where
  obj s := op ((prodY a (iStar A C)).elementsMk (op s.unop.obj.unop.left)
    (s.unop.obj.unop.hom,
      Over.iteratedSliceBackward s.unop.obj.unop ⋙ sG C a s))
  map {s s'} φ := Quiver.Hom.op ⟨φ.unop.hom.unop.left.op, by
    have hG : Over.map φ.unop.hom.unop ⋙ sG C a s' = sG C a s := φ.unop.map_val
    refine Prod.ext (Over.w φ.unop.hom.unop) ?_
    exact (congrArg (fun F => F ⋙ sG C a s') (map_backward a φ.unop.hom.unop)).trans
      (congrArg (fun F => Over.iteratedSliceBackward s.unop.obj.unop ⋙ F) hG)⟩
  map_id _ := Quiver.Hom.unop_inj (Functor.Elements.Hom.ext rfl)
  map_comp _ _ := Quiver.Hom.unop_inj (Functor.Elements.Hom.ext rfl)

theorem toSlice_fromSlice : toSlice C a ⋙ fromSlice C a = 𝟭 _ := rfl

/-- `𝟭 ⟶ fromSlice ⋙ toSlice`, the identity of `Y`. -/
def sliceCompare : 𝟭 _ ⟶ fromSlice C a ⋙ toSlice C a where
  app s := Quiver.Hom.op ⟨𝟙 _, by
    exact (congrArg (fun F => F ⋙ Over.iteratedSliceForward s.unop.obj.unop ⋙
        Over.iteratedSliceBackward s.unop.obj.unop ⋙ sG C a s) (over_map_id_eq (Over a) _)).trans
      (congrArg (fun F => F ⋙ sG C a s) (forward_backward a s.unop.obj.unop))⟩
  naturality _ _ _ := Quiver.Hom.unop_inj (Functor.Elements.Hom.ext
    ((Category.id_comp (obj := (Over a)ᵒᵖ) _).trans (Category.comp_id (obj := (Over a)ᵒᵖ) _).symm))

/-- **`(A/a)/i_{A/a}^*(C)` and `A/(a × i_A^*(C))` are aspherical together.** -/
theorem isAspherical_slice_iff (L : FundamentalLocalizer.{0}) :
    L.IsAspherical (iStar (Over a) C).Elementsᵒᵖ ↔ L.IsAspherical (El (prodY a (iStar A C))) :=
  isAspherical_iff_of_retraction L (toSlice C a) (fromSlice C a) (toSlice_fromSlice C a)
    (sliceCompare C a)

end Compare

/-- A presheaf `X` is **locally aspherical** when every `A/(a × X)` is aspherical. -/
def IsLocallyAspherical (L : FundamentalLocalizer.{0}) (X : Aᵒᵖ ⥤ Type) : Prop :=
  ∀ a : A, L.IsAspherical (El (prodY a X))

/-- **Grothendieck's criterion** (Cisinski, Astérisque 308, Th. 4.1.19, (i) ⇔ (ii)): a small
category `A` is a local test category iff its Lawvere object `L_A = i_A^*(Δ¹)` is locally
aspherical. -/
theorem isLocalTest_iff_isLocallyAspherical (L : FundamentalLocalizer.{0}) :
    IsLocalTest A L ↔ IsLocallyAspherical L (iStar A (Fin 2)) := by
  constructor
  · intro h a
    exact (isAspherical_slice_iff (Fin 2) a L).1 (h a (Fin 2))
  · intro hL a C _ _
    exact (isAspherical_slice_iff C a L).2
      (isAspherical_prodY_of_pmap A L C a (pmap_mem L hL C a))

end LeanPool.ToposTheoreticBridges.Examples
