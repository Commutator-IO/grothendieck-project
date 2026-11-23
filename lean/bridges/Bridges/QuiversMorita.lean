/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.EssentialPoints
public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Bridges for the free category of a quiver

For a quiver `V`, the free category `Paths V` has the paths of `V` as morphisms. Its functors to
sets `Paths V ⥤ Type u` are the representations of `V` in sets, and its presheaves
`(Paths V)ᵒᵖ ⥤ Type u` are the representations of the opposite quiver. We read the bridges of
this project on `Paths V`.

* Idempotents and isomorphisms. The length of paths is additive, so an idempotent of `Paths V`
  is an identity (`paths_eq_id_of_idempotent`), a morphism is an isomorphism exactly when it has
  length zero, that is, when it is `eqToHom` of an equality of vertices
  (`paths_isIso_iff_eq_eqToHom`), and isomorphic objects are equal (`paths_nonempty_iso_iff`).
  Hence `Paths V` is idempotent complete and `Karoubi (Paths V) ≌ Paths V`
  (`karoubiPathsEquiv`).
* Morita equivalence. By the bridge `moritaEquivalentCat_iff_karoubi`, two quivers have
  equivalent presheaf topoi on their free categories exactly when the free categories are
  equivalent (`moritaEquivalentCat_paths_iff_nonempty_equivalence`), exactly when the quivers
  are isomorphic (`moritaEquivalentCat_paths_iff`); the same holds for the categories of
  representations (`nonempty_representations_equiv_iff`). Here a `QuiverIso V W` is a bijection
  of vertices together with bijections of the arrows between corresponding vertices. An
  equivalence of free categories is bijective on objects (`QuiverIso.ofEquivalence`) and
  preserves the indecomposable morphisms (`indecomposable_map_iff`), which are the paths of
  length one (`pathLength_eq_one_iff_indecomposable`), that is, the arrows of the quiver.
* Essential points. By the bridge `essentialPointEquivKaroubiOp`, the essential points of the
  presheaf topos of `Paths V` form a category equivalent to `(Paths V)ᵒᵖ`
  (`essentialPointPathsEquiv`); two essential points are isomorphic exactly when they have the
  same vertex (`nonempty_iso_iff_essentialPointVertex_eq`). Every essential point is isomorphic
  to the evaluation at a vertex (`exists_iso_evaluationPoint`), and the evaluations at two
  vertices are isomorphic exactly when the vertices are equal
  (`nonempty_evaluationPoint_iso_iff`).
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory Opposite Idempotents

universe u u₁ v₁ u₂ v₂ u₃ v₃

section Indecomposable

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A morphism is *indecomposable* when it is not an isomorphism and, in every factorisation
of it, one of the two factors is an isomorphism. -/
def Indecomposable {X Y : C} (f : X ⟶ Y) : Prop :=
  ¬ IsIso f ∧ ∀ (Z : C) (g : X ⟶ Z) (h : Z ⟶ Y), g ≫ h = f → IsIso g ∨ IsIso h

/-- A fully faithful, essentially surjective functor preserves and reflects indecomposable
morphisms. -/
theorem indecomposable_map_iff (F : C ⥤ D) [F.Full] [F.Faithful] [F.EssSurj] {X Y : C}
    (f : X ⟶ Y) : Indecomposable (F.map f) ↔ Indecomposable f := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun hf => h₁ inferInstance, fun Z g h hgh => ?_⟩
    rcases h₂ _ (F.map g) (F.map h) (by rw [← F.map_comp, hgh]) with hg | hh
    · exact Or.inl (isIso_of_fully_faithful F g)
    · exact Or.inr (isIso_of_fully_faithful F h)
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun hf => h₁ (isIso_of_fully_faithful F f), fun Z' g' h' hgh => ?_⟩
    let i := F.objObjPreimageIso Z'
    rcases h₂ _ (F.preimage (g' ≫ i.inv)) (F.preimage (i.hom ≫ h'))
      (F.map_injective (by simp [hgh])) with hg | hh
    · have : IsIso (g' ≫ i.inv) := by
        rw [← F.map_preimage (g' ≫ i.inv)]
        infer_instance
      exact Or.inl (IsIso.of_isIso_comp_right g' i.inv)
    · have : IsIso (i.hom ≫ h') := by
        rw [← F.map_preimage (i.hom ≫ h')]
        infer_instance
      exact Or.inr (IsIso.of_isIso_comp_left i.hom h')

end Indecomposable

section Paths

variable {V : Type u₁} [Quiver.{v₁} V]

/-- The length of a morphism of the free category `Paths V`. -/
def pathLength {a b : Paths V} (f : a ⟶ b) : ℕ := @Quiver.Path.length V _ a b f

@[simp]
theorem pathLength_id (a : Paths V) : pathLength (𝟙 a) = 0 := rfl

@[simp]
theorem pathLength_comp {a b c : Paths V} (f : a ⟶ b) (g : b ⟶ c) :
    pathLength (f ≫ g) = pathLength f + pathLength g :=
  Quiver.Path.length_comp _ _

@[simp]
theorem pathLength_of_map {a b : V} (e : a ⟶ b) : pathLength ((Paths.of V).map e) = 1 := rfl

/-- A morphism of `Paths V` is an isomorphism exactly when it has length zero. -/
theorem paths_isIso_iff {a b : Paths V} (f : a ⟶ b) : IsIso f ↔ pathLength f = 0 := by
  constructor
  · intro hf
    have := congrArg pathLength (IsIso.hom_inv_id f)
    rw [pathLength_comp, pathLength_id] at this
    omega
  · intro h
    obtain rfl := Quiver.Path.eq_of_length_zero (V := V) f h
    rw [show f = 𝟙 a from Quiver.Path.eq_nil_of_length_zero (V := V) f h]
    infer_instance

/-- In the free category of a quiver, every idempotent is an identity. -/
theorem paths_eq_id_of_idempotent {a : Paths V} (f : a ⟶ a) (hf : f ≫ f = f) : f = 𝟙 a := by
  have := congrArg pathLength hf
  rw [pathLength_comp] at this
  exact Quiver.Path.eq_nil_of_length_zero (V := V) f (show pathLength f = 0 by omega)

/-- Isomorphic objects of the free category of a quiver are equal. -/
theorem paths_eq_of_iso {a b : Paths V} (e : a ≅ b) : a = b :=
  Quiver.Path.eq_of_length_zero (V := V) e.hom ((paths_isIso_iff e.hom).1 inferInstance)

/-- In the free category of a quiver, the isomorphisms are the identities: a morphism is an
isomorphism exactly when it is `eqToHom` of an equality of vertices. -/
theorem paths_isIso_iff_eq_eqToHom {a b : Paths V} (f : a ⟶ b) :
    IsIso f ↔ ∃ h : a = b, f = eqToHom h := by
  constructor
  · intro hf
    obtain rfl := paths_eq_of_iso (asIso f)
    exact ⟨rfl, Quiver.Path.eq_nil_of_length_zero (V := V) f ((paths_isIso_iff f).1 hf)⟩
  · rintro ⟨rfl, rfl⟩
    infer_instance

/-- Two objects of the free category of a quiver are isomorphic exactly when they are equal. -/
theorem paths_nonempty_iso_iff {a b : Paths V} : Nonempty (a ≅ b) ↔ a = b :=
  ⟨fun ⟨e⟩ => paths_eq_of_iso e, fun h => ⟨eqToIso h⟩⟩

/-- The free category of a quiver is idempotent complete. -/
instance : IsIdempotentComplete (Paths V) where
  idempotents_split X p hp :=
    ⟨X, 𝟙 X, 𝟙 X, Category.id_comp _,
      by rw [paths_eq_id_of_idempotent p hp, Category.id_comp]⟩

/-- The Karoubi envelope of the free category of a quiver is the free category itself. -/
noncomputable def karoubiPathsEquiv : Karoubi (Paths V) ≌ Paths V :=
  (toKaroubiEquivalence (Paths V)).symm

/-- A morphism of `Paths V` has length one exactly when it is indecomposable. -/
theorem pathLength_eq_one_iff_indecomposable {a b : Paths V} (f : a ⟶ b) :
    pathLength f = 1 ↔ Indecomposable f := by
  constructor
  · intro h
    refine ⟨fun hf => by rw [(paths_isIso_iff f).1 hf] at h; exact zero_ne_one h,
      fun Z g k hgk => ?_⟩
    have := congrArg pathLength hgk
    rw [pathLength_comp, h] at this
    simp only [paths_isIso_iff]
    omega
  · rintro ⟨h₁, h₂⟩
    change @Quiver.Path V _ a b at f
    cases f with
    | nil => exact absurd ((paths_isIso_iff (𝟙 a)).2 rfl) h₁
    | @cons c _ p e =>
      rcases h₂ c p ((Paths.of V).map e) rfl with hp | he
      · exact congrArg (· + 1) ((paths_isIso_iff (a := a) (b := c) p).1 hp)
      · exact absurd ((paths_isIso_iff _).1 he) one_ne_zero

/-- Every path of length one is an arrow. -/
theorem exists_toPath_eq {a b : V} (p : Quiver.Path a b) (hp : p.length = 1) :
    ∃ e : a ⟶ b, e.toPath = p := by
  cases p with
  | nil => exact absurd hp zero_ne_one
  | cons p e =>
    simp only [Quiver.Path.length_cons, Nat.add_eq_right] at hp
    obtain rfl := Quiver.Path.eq_of_length_zero p hp
    obtain rfl := Quiver.Path.eq_nil_of_length_zero p hp
    exact ⟨e, rfl⟩

/-- The arrows `a ⟶ b` of a quiver are the morphisms of length one of its free category. -/
noncomputable def arrowEquivPathLengthOne (a b : V) :
    (a ⟶ b) ≃ {f : (Paths.of V).obj a ⟶ (Paths.of V).obj b // pathLength f = 1} :=
  Equiv.ofBijective (fun e => ⟨(Paths.of V).map e, rfl⟩)
    ⟨fun _ _ h => eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons (congrArg Subtype.val h)),
      fun ⟨f, hf⟩ =>
        let ⟨e, he⟩ := exists_toPath_eq (V := V) f hf
        ⟨e, Subtype.ext he⟩⟩

end Paths

/-! ### Isomorphisms of quivers and equivalences of free categories -/

/-- An isomorphism of quivers: a bijection of vertices together with bijections between the
arrows of corresponding pairs of vertices. -/
structure QuiverIso (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  /-- The bijection of vertices. -/
  obj : V ≃ W
  /-- The bijections of arrows. -/
  hom (a b : V) : (a ⟶ b) ≃ (obj a ⟶ obj b)

namespace QuiverIso

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W]

/-- The prefunctor of an isomorphism of quivers. -/
def toPrefunctor (e : QuiverIso V W) : V ⥤q W where
  obj := e.obj
  map {a b} := e.hom a b

theorem length_mapPath (P : V ⥤q W) {a b : V} (p : Quiver.Path a b) :
    (P.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih]

/-- A prefunctor injective on vertices and on arrows is injective on paths. -/
theorem mapPath_injective (P : V ⥤q W) (hobj : Function.Injective P.obj)
    (hmap : ∀ a b : V, Function.Injective (P.map : (a ⟶ b) → _)) {a b : V}
    (p : Quiver.Path a b) : ∀ q : Quiver.Path a b, P.mapPath p = P.mapPath q → p = q := by
  induction p with
  | nil =>
    intro q h
    have := congrArg Quiver.Path.length h
    rw [length_mapPath, length_mapPath] at this
    exact (Quiver.Path.eq_nil_of_length_zero q this.symm).symm
  | @cons c b p e ih =>
    intro q h
    cases q with
    | nil => exact absurd h (Quiver.Path.cons_ne_nil _ _)
    | @cons c' _ q e' =>
      simp only [Prefunctor.mapPath_cons] at h
      obtain rfl := hobj (Quiver.Path.obj_eq_of_cons_eq_cons h)
      obtain rfl := ih q (eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h))
      rw [hmap _ _ (eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons h))]

/-- A prefunctor surjective on vertices and on arrows is surjective on paths. -/
theorem exists_mapPath_heq (P : V ⥤q W) (hobj : Function.Surjective P.obj)
    (hmap : ∀ a b : V, Function.Surjective (P.map : (a ⟶ b) → _)) {a : V} {b' : W}
    (p' : Quiver.Path (P.obj a) b') :
    ∃ (b : V) (p : Quiver.Path a b), P.obj b = b' ∧ P.mapPath p ≍ p' := by
  induction p' with
  | nil => exact ⟨a, Quiver.Path.nil, rfl, HEq.rfl⟩
  | @cons c' b' p' e' ih =>
    obtain ⟨c, p, rfl, hp⟩ := ih
    obtain rfl := eq_of_heq hp
    obtain ⟨b, rfl⟩ := hobj b'
    obtain ⟨e, rfl⟩ := hmap c b e'
    exact ⟨b, p.cons e, rfl, HEq.rfl⟩

/-- The functor between free categories induced by an isomorphism of quivers. -/
def pathsFunctor (e : QuiverIso V W) : Paths V ⥤ Paths W where
  obj := e.obj
  map {a b} p := e.toPrefunctor.mapPath (a := a) (b := b) p
  map_id _ := rfl
  map_comp _ _ := Prefunctor.mapPath_comp _ _ _

instance (e : QuiverIso V W) : e.pathsFunctor.Faithful where
  map_injective {_ _} p q h :=
    mapPath_injective e.toPrefunctor e.obj.injective (fun a b => (e.hom a b).injective) p q h

instance (e : QuiverIso V W) : e.pathsFunctor.Full where
  map_surjective {a _} f := by
    obtain ⟨b₀, p, hb, hp⟩ := exists_mapPath_heq e.toPrefunctor e.obj.surjective
      (fun a b => (e.hom a b).surjective) (a := a) f
    obtain rfl := e.obj.injective hb
    exact ⟨p, eq_of_heq hp⟩

instance (e : QuiverIso V W) : e.pathsFunctor.EssSurj where
  mem_essImage Y := ⟨e.obj.symm Y, ⟨eqToIso (e.obj.apply_symm_apply Y)⟩⟩

/-- An isomorphism of quivers induces an equivalence of their free categories. -/
noncomputable def pathsEquivalence (e : QuiverIso V W) : Paths V ≌ Paths W :=
  have : e.pathsFunctor.IsEquivalence := { }
  e.pathsFunctor.asEquivalence

/-- An equivalence of free categories induces an isomorphism of quivers: it is bijective on
objects since isomorphic objects are equal, and it restricts to the morphisms of length one,
the indecomposable ones. -/
noncomputable def ofEquivalence (E : Paths V ≌ Paths W) : QuiverIso V W where
  obj :=
    { toFun := E.functor.obj
      invFun := E.inverse.obj
      left_inv a := (paths_eq_of_iso (E.unitIso.app a)).symm
      right_inv b := paths_eq_of_iso (E.counitIso.app b) }
  hom a b := (arrowEquivPathLengthOne a b).trans <|
    (Equiv.subtypeEquiv (p := fun f => pathLength f = 1) (q := fun f => pathLength f = 1)
      E.fullyFaithfulFunctor.homEquiv fun f => by
      rw [pathLength_eq_one_iff_indecomposable, pathLength_eq_one_iff_indecomposable]
      exact (indecomposable_map_iff E.functor f).symm).trans
    (arrowEquivPathLengthOne (V := W) _ _).symm

end QuiverIso

section Morita

/-- Two idempotent complete small categories are Morita equivalent exactly when they are
equivalent. -/
theorem moritaEquivalentCat_iff_of_isIdempotentComplete (C D : Type u) [SmallCategory C]
    [SmallCategory D] [IsIdempotentComplete C] [IsIdempotentComplete D] :
    MoritaEquivalentCat C D ↔ Nonempty (C ≌ D) := by
  rw [moritaEquivalentCat_iff_karoubi]
  exact ⟨fun ⟨e⟩ =>
      ⟨(toKaroubiEquivalence C).trans (e.trans (toKaroubiEquivalence D).symm)⟩,
    fun ⟨e⟩ => ⟨(toKaroubiEquivalence C).symm.trans (e.trans (toKaroubiEquivalence D))⟩⟩

variable {V : Type u₁} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W]

/-- The free categories of two quivers are equivalent exactly when the quivers are
isomorphic. -/
theorem nonempty_paths_equiv_iff : Nonempty (Paths V ≌ Paths W) ↔ Nonempty (QuiverIso V W) :=
  ⟨fun ⟨E⟩ => ⟨QuiverIso.ofEquivalence E⟩, fun ⟨e⟩ => ⟨e.pathsEquivalence⟩⟩

variable (R R' : Type u) [Quiver.{u} R] [Quiver.{u} R']

/-- Two quivers have equivalent presheaf topoi on their free categories exactly when their free
categories are equivalent. -/
theorem moritaEquivalentCat_paths_iff_nonempty_equivalence :
    MoritaEquivalentCat (Paths R) (Paths R') ↔ Nonempty (Paths R ≌ Paths R') :=
  moritaEquivalentCat_iff_of_isIdempotentComplete _ _

/-- **Morita equivalence of free categories.** Two quivers have equivalent presheaf topoi on
their free categories exactly when they are isomorphic. -/
theorem moritaEquivalentCat_paths_iff :
    MoritaEquivalentCat (Paths R) (Paths R') ↔ Nonempty (QuiverIso R R') :=
  (moritaEquivalentCat_paths_iff_nonempty_equivalence R R').trans nonempty_paths_equiv_iff

/-- Two quivers have equivalent categories of representations in sets exactly when they are
isomorphic. -/
theorem nonempty_representations_equiv_iff :
    Nonempty ((Paths R ⥤ Type u) ≌ (Paths R' ⥤ Type u)) ↔ Nonempty (QuiverIso R R') := by
  rw [← nonempty_paths_equiv_iff]
  have h := moritaEquivalentCat_iff_of_isIdempotentComplete (Paths R)ᵒᵖ (Paths R')ᵒᵖ
  constructor
  · rintro ⟨e⟩
    obtain ⟨e'⟩ := h.1 ⟨(opOpEquivalence (Paths R)).congrLeft.trans
      (e.trans (opOpEquivalence (Paths R')).congrLeft.symm)⟩
    exact ⟨e'.unop⟩
  · rintro ⟨e⟩
    obtain ⟨e'⟩ := h.2 ⟨e.op⟩
    exact ⟨(opOpEquivalence (Paths R)).congrLeft.symm.trans
      (e'.trans (opOpEquivalence (Paths R')).congrLeft)⟩

/-- The vertices of two Morita-equivalent quivers are in bijection. -/
theorem nonempty_equiv_of_moritaEquivalentCat_paths
    (h : MoritaEquivalentCat (Paths R) (Paths R')) : Nonempty (R ≃ R') :=
  let ⟨e⟩ := (moritaEquivalentCat_paths_iff R R').1 h; ⟨e.obj⟩

end Morita

/-! ### Essential points of the presheaf topos of a free category -/

section EssentialPoints

variable (R : Type u) [Quiver.{u} R]

/-- The essential points of the presheaf topos of the free category of a quiver form a category
equivalent to the opposite of the free category. -/
noncomputable def essentialPointPathsEquiv :
    EssentialPoint.{u} ((Paths R)ᵒᵖ ⥤ Type u) ≌ (Paths R)ᵒᵖ :=
  (essentialPointEquivKaroubiOp (Paths R)).trans karoubiPathsEquiv.op

variable {R}

/-- The vertex of an essential point of the presheaf topos of `Paths R`. -/
noncomputable def essentialPointVertex (p : EssentialPoint.{u} ((Paths R)ᵒᵖ ⥤ Type u)) : R :=
  unop ((essentialPointPathsEquiv R).functor.obj p)

/-- Two essential points of the presheaf topos of the free category of a quiver are isomorphic
exactly when they have the same vertex. -/
theorem nonempty_iso_iff_essentialPointVertex_eq
    (p q : EssentialPoint.{u} ((Paths R)ᵒᵖ ⥤ Type u)) :
    Nonempty (p ≅ q) ↔ essentialPointVertex p = essentialPointVertex q := by
  let E := essentialPointPathsEquiv R
  constructor
  · rintro ⟨i⟩
    exact (paths_eq_of_iso (E.functor.mapIso i).unop).symm
  · intro h
    exact ⟨E.fullyFaithfulFunctor.preimageIso (eqToIso (unop_injective h))⟩

/-- Every vertex is the vertex of an essential point. -/
theorem essentialPointVertex_surjective :
    Function.Surjective (essentialPointVertex (R := R)) := fun a =>
  ⟨(essentialPointPathsEquiv R).inverse.obj (op a),
    paths_eq_of_iso ((essentialPointPathsEquiv R).counitIso.app (op a)).unop.symm⟩

/-- The essential point of the presheaf topos of `Paths R` given by evaluation at a vertex. -/
noncomputable def evaluationPoint (a : R) : EssentialPoint.{u} ((Paths R)ᵒᵖ ⥤ Type u) :=
  ⟨(evaluation (Paths R)ᵒᵖ (Type u)).obj (op a),
    isEssentialPoint_evaluation (C := Paths R) a⟩

/-- The evaluations at two vertices are isomorphic essential points exactly when the vertices
are equal. -/
theorem nonempty_evaluationPoint_iso_iff (a b : R) :
    Nonempty (evaluationPoint a ≅ evaluationPoint b) ↔ a = b := by
  constructor
  · rintro ⟨i⟩
    let i' : coyoneda.obj (op (yoneda.obj (show Paths R from a))) ≅
        coyoneda.obj (op (yoneda.obj (show Paths R from b))) :=
      coyonedaYonedaIsoEvaluation (show Paths R from a) ≪≫
        (isEssentialPoint.{u} _).ι.mapIso i ≪≫
        (coyonedaYonedaIsoEvaluation (show Paths R from b)).symm
    exact (paths_eq_of_iso
      (Yoneda.fullyFaithful.preimageIso (Coyoneda.fullyFaithful.preimageIso i').unop)).symm
  · rintro rfl
    exact ⟨Iso.refl _⟩

/-- A retract of a representable presheaf on the free category of a quiver is isomorphic to
the representable presheaf. -/
noncomputable def isoOfRetractYoneda {P : (Paths R)ᵒᵖ ⥤ Type u} {X : Paths R}
    (r : Retract P (yoneda.obj X)) : P ≅ yoneda.obj X where
  hom := r.i
  inv := r.r
  hom_inv_id := r.retract
  inv_hom_id := by
    let g := Yoneda.fullyFaithful.preimage (r.r ≫ r.i)
    have hg : g ≫ g = g := yoneda.map_injective (by simp [g])
    rw [← Yoneda.fullyFaithful.map_preimage (r.r ≫ r.i)]
    change yoneda.map g = _
    rw [paths_eq_id_of_idempotent g hg, yoneda.map_id]

/-- Every essential point of the presheaf topos of the free category of a quiver is isomorphic
to the evaluation at a vertex. -/
theorem exists_iso_evaluationPoint (p : EssentialPoint.{u} ((Paths R)ᵒᵖ ⥤ Type u)) :
    ∃ a : R, Nonempty (p ≅ evaluationPoint a) := by
  obtain ⟨P, ⟨X, ⟨r⟩⟩, ⟨i⟩⟩ := (isEssentialPoint_iff p.obj).1 p.2
  exact ⟨X, ⟨(isEssentialPoint.{u} _).fullyFaithfulι.preimageIso
    (i ≪≫ coyoneda.mapIso (isoOfRetractYoneda r).symm.op ≪≫
      coyonedaYonedaIsoEvaluation X)⟩⟩

end EssentialPoints

end LeanPool.ToposTheoreticBridges.Examples
