import Buffalo.Topos.Part01d
import Buffalo.Topos.Part01c

/-!
# Buffalo, topos theory, part 2a: étale morphisms, ring objects, internal Hom (18 May 1973)

Entries of `docs/buffalo-topos/index.tex` from « Étale morphisms and slice categories » to
« Internal Hom and the subobject sheaf » (video `URU5jgTvjhU`, 5:39:20–6:50:49). The status of
each entry is in `docs/buffalo-topos/lean/Part02.json`.

Conventions are those of `Part01`: sheaves of sets on a space `X` are
`TopCat.Sheaf (Type u) X = Sheaf (Opens.grothendieckTopology X) (Type u)`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Topology MonoidalCategory

namespace Buffalo.Topos.Part02

noncomputable section

open Buffalo.Topos.Part01

variable {X Y : TopCat.{u}}

/-! ## Sheaves on a point -/

/-- The one-point space. -/
abbrev pt : TopCat.{u} := TopCat.of PUnit.{u + 1}

theorem opens_pt (U : Opens pt.{u}) : U = ⊥ ∨ U = ⊤ := by
  by_cases h : PUnit.unit ∈ U
  · right; ext x; cases x; simpa using h
  · left; ext x; cases x; simpa using h

/-- On a sheaf, the sections over an empty open set form a singleton. -/
abbrev uniqueOfEqBot (F : TopCat.Sheaf (Type u) X) {U : Opens X} (h : U = ⊥) :
    Unique (F.obj.obj (op U)) :=
  Types.isTerminalEquivUnique _ (F.isTerminalOfEqEmpty h)

/-- The global sections functor `Sh(pt) → Set`, `F ↦ F(pt)`. -/
abbrev ptSections : TopCat.Sheaf (Type u) pt.{u} ⥤ Type u :=
  (sheafSections (Opens.grothendieckTopology pt) (Type u)).obj (op ⊤)

instance : ptSections.{u}.Faithful where
  map_injective {F G} f g h := by
    apply Sheaf.hom_ext
    ext U s
    rcases opens_pt U.unop with hU | hU
    · exact (uniqueOfEqBot G hU).instSubsingleton.elim _ _
    · obtain ⟨U⟩ := U
      dsimp at hU
      subst hU
      exact congr($h s)

open scoped Classical in
/-- The morphism of sheaves on the point defined by a map on global sections. -/
def ptMap {F G : TopCat.Sheaf (Type u) pt.{u}}
    (φ : F.obj.obj (op ⊤) → G.obj.obj (op ⊤)) : F ⟶ G where
  hom :=
    { app := fun U => ↾fun s =>
        if h : U.unop = ⊤ then G.obj.map (homOfLE le_top).op (φ (F.obj.map (eqToHom h.symm).op s))
        else (uniqueOfEqBot G ((opens_pt U.unop).resolve_right h)).default
      naturality := by
        intro U V i
        ext s
        by_cases hV : V.unop = ⊤
        · have hU : U.unop = ⊤ := top_le_iff.1 (hV ▸ i.unop.le)
          obtain ⟨U⟩ := U
          obtain ⟨V⟩ := V
          dsimp at hU hV
          subst hU hV
          have hi : i = 𝟙 _ := Subsingleton.elim _ _
          subst hi
          simp
        · exact (uniqueOfEqBot G ((opens_pt V.unop).resolve_right hV)).instSubsingleton.elim
            _ _ }

instance : ptSections.{u}.Full where
  map_surjective {F G} φ := ⟨ptMap φ, by
    ext s
    classical
    change (if h : (⊤ : Opens pt) = ⊤ then _ else _) = _
    simp⟩

open scoped Classical in
instance : ptSections.{u}.EssSurj where
  mem_essImage S := ⟨skyscraperSheaf (PUnit.unit : pt.{u}) S,
    ⟨eqToIso (by simp [skyscraperSheaf])⟩⟩

instance : ptSections.{u}.IsEquivalence where

/-- URU5jgTvjhU-33248 (9:14:08) [prop] and URU5jgTvjhU-2745 (0:45:45) [prop] `Sh(pt) ≃ Set` via
`F ↦ F(pt)`: the point topos. -/
def sheafPtEquiv : TopCat.Sheaf (Type u) pt.{u} ≌ Type u :=
  ptSections.asEquivalence

/-! ## Étale morphisms and slice categories -/

/-- The inclusion of a point `y` into `Y`. -/
def pointMap (y : Y) : pt.{u} ⟶ Y := TopCat.ofHom ⟨fun _ => y, continuous_const⟩

/-- URU5jgTvjhU-20360 (5:39:20) [prop] For `i_y : {y} → Y`, `i_y^*F ≃ F_y`: the stalk of the
inverse image at the unique point is the stalk of `F` at `y`. -/
def pointPullback_stalk (y : Y) (F : Y.Presheaf (Type u)) :
    F.stalk y ≅ ((TopCat.Presheaf.pullback (Type u) (pointMap y)).obj F).stalk PUnit.unit :=
  TopCat.Presheaf.stalkPullbackIso (Type u) (pointMap y) F PUnit.unit

/-- URU5jgTvjhU-20491 (5:41:31) [prop] A composite of étale morphisms (local homeomorphisms) is
étale. -/
theorem etale_comp {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {g : B → C} {f : A → B} (hg : IsLocalHomeomorph g) (hf : IsLocalHomeomorph f) :
    IsLocalHomeomorph (g ∘ f) :=
  hg.comp hf

/-- URU5jgTvjhU-20491 (5:41:31) [prop] For an open embedding `U ⊆ Y`, `Sh(U)` is equivalent to the
sheaves on the site `𝒪(Y)/U` (Mathlib's `Opens.sheafEquivOver`). -/
def sheafOpenEquivOver (U : Opens Y) :
    Sheaf ((Opens.grothendieckTopology Y).over U) (Type u) ≌ Sheaf (Opens.grothendieckTopology U)
      (Type u) :=
  U.sheafEquivOver

/-- URU5jgTvjhU-20620 (5:43:40) [def] The objects of `C/X` are the arrows `X' → X` and its
morphisms the commutative triangles (Mathlib's `Over X`). -/
example {C : Type*} [Category C] (X : C) {A B : Over X} (h : A ⟶ B) :
    h.left ≫ B.hom = A.hom :=
  Over.w h

/-- URU5jgTvjhU-20684 (5:44:44) [prop] The object `G × U → U` of `Sh(Y)/U` (Mathlib's
`Over.star U`) has, as sections over `V → U`, the sections `G(V)`: these are the sections of the
restriction `G|_U`. -/
def star_sections (U : Opens Y) (G : TopCat.Sheaf (Type u) Y) (V : Over (opensSheaf U)) :
    (V ⟶ (Over.star (opensSheaf U)).obj G) ≃ (V.left ⟶ G) :=
  ((Over.forgetAdjStar (opensSheaf U)).homEquiv V G).symm

/-- URU5jgTvjhU-20820 (5:47:00) [prop] For `g : X' → X`, `g^* : C/X → C/X'` is the base change
`F ↦ F ×_X X'`, right adjoint to composition with `g`. -/
def baseChange_adj {C : Type*} [Category C] [HasPullbacks C] {X' X : C} (g : X' ⟶ X) :
    Over.map g ⊣ Over.pullback g :=
  Over.mapPullbackAdj g

/-- URU5jgTvjhU-21075 (5:51:15) [prop] `f_*` commutes with limits, hence sends group objects to group
objects. -/
def pushforward_grp (f : X ⟶ Y) :
    Grp (Sheaf (Opens.grothendieckTopology X) (Type u)) ⥤
      Grp (Sheaf (Opens.grothendieckTopology Y) (Type u)) :=
  let F : Sheaf (Opens.grothendieckTopology X) (Type u) ⥤ Sheaf (Opens.grothendieckTopology Y)
    (Type u) := TopCat.Sheaf.pushforward (Type u) f
  have : PreservesLimits F := (pullback_adjunction f).rightAdjoint_preservesLimits
  have : PreservesFiniteProducts F :=
    ⟨fun _ => preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _⟩
  mapGrpOfPreserves F

/-- URU5jgTvjhU-21139 (5:52:19) [prop] and URU5jgTvjhU-13813 (3:50:13) [prop] `f^*` commutes with
finite limits. -/
instance pullback_preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback (Type u) f) := by
  have := @reflectsLimits_of_reflectsIsomorphisms
  unfold TopCat.Sheaf.pullback
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

/-- URU5jgTvjhU-21139 (5:52:19) [prop] `f^*` commutes with finite limits and colimits, hence sends
group objects to group objects. -/
def pullback_grp (f : X ⟶ Y) :
    Grp (Sheaf (Opens.grothendieckTopology Y) (Type u)) ⥤
      Grp (Sheaf (Opens.grothendieckTopology X) (Type u)) :=
  let F : Sheaf (Opens.grothendieckTopology Y) (Type u) ⥤ Sheaf (Opens.grothendieckTopology X)
    (Type u) := TopCat.Sheaf.pullback (Type u) f
  have : PreservesFiniteLimits F := pullback_preservesFiniteLimits f
  have : PreservesFiniteProducts F := ⟨fun _ => inferInstance⟩
  mapGrpOfPreserves F

/-! ## Ring and field objects -/

section RingObj

variable {C : Type*} [Category C]

/-- URU5jgTvjhU-21393 (5:56:33) [def] A ring object of `C` is an object `A` with a (here
commutative) ring structure on each `A(Z) = Hom(Z, A)`, functorial in `Z`. -/
class RingObj (A : C) where
  /-- The ring structure on `Hom(Z, A)`. -/
  ring : ∀ Z : C, CommRing (Z ⟶ A)
  comp_add : ∀ {Z Z' : C} (h : Z' ⟶ Z) (a b : Z ⟶ A),
    h ≫ (a + b) = (h ≫ a : Z' ⟶ A) + (h ≫ b : Z' ⟶ A)
  comp_mul : ∀ {Z Z' : C} (h : Z' ⟶ Z) (a b : Z ⟶ A),
    h ≫ (a * b) = (h ≫ a : Z' ⟶ A) * (h ≫ b : Z' ⟶ A)
  comp_zero : ∀ {Z Z' : C} (h : Z' ⟶ Z), h ≫ (0 : Z ⟶ A) = 0
  comp_one : ∀ {Z Z' : C} (h : Z' ⟶ Z), h ≫ (1 : Z ⟶ A) = 1

attribute [reducible, instance] RingObj.ring

variable [HasBinaryProducts C] [HasTerminal C] (A : C) [RingObj A]

/-- The multiplication `m : A × A → A`. -/
def ringMul : A ⨯ A ⟶ A := (prod.fst : A ⨯ A ⟶ A) * prod.snd

/-- The unit section `1 : e → A`. -/
def ringOne : ⊤_ C ⟶ A := 1

/-- The zero section `0 : e → A`. -/
def ringZero : ⊤_ C ⟶ A := 0

variable {A}

omit [HasTerminal C] in
theorem lift_ringMul {Z : C} (a b : Z ⟶ A) : prod.lift a b ≫ ringMul A = a * b := by
  rw [ringMul, RingObj.comp_mul, prod.lift_fst, prod.lift_snd]

omit [HasBinaryProducts C] in
theorem from_ringOne (Z : C) : terminal.from Z ≫ ringOne A = 1 := RingObj.comp_one _

omit [HasBinaryProducts C] in
theorem from_ringZero (Z : C) : terminal.from Z ≫ ringZero A = 0 := RingObj.comp_zero _

variable [HasPullbacks C] (A)

/-- The object of units, the fibre product of `m : A × A → A` and `1 : e → A`. -/
abbrev unitsObj : C := pullback (ringMul A) (ringOne A)

/-- URU5jgTvjhU-21458 (5:57:38) [prop] The units `A^*(Z) ⊂ A(Z)` are represented by the fibre
product of `m : A × A → A` and `1 : e → A`. -/
def unitsObj_hom (Z : C) : (Z ⟶ unitsObj A) ≃ (Z ⟶ A)ˣ where
  toFun g :=
    { val := g ≫ pullback.fst _ _ ≫ prod.fst
      inv := g ≫ pullback.fst _ _ ≫ prod.snd
      val_inv := by
        rw [← lift_ringMul, ← Category.assoc g, ← Category.assoc g, ← prod.comp_lift,
          prod.lift_fst_snd, Category.comp_id, Category.assoc, pullback.condition,
          ← Category.assoc, show g ≫ pullback.snd _ _ = terminal.from Z from Subsingleton.elim _ _, from_ringOne]
      inv_val := by
        rw [mul_comm, ← lift_ringMul, ← Category.assoc g, ← Category.assoc g, ← prod.comp_lift,
          prod.lift_fst_snd, Category.comp_id, Category.assoc, pullback.condition,
          ← Category.assoc, show g ≫ pullback.snd _ _ = terminal.from Z from Subsingleton.elim _ _, from_ringOne] }
  invFun v := pullback.lift (prod.lift v.val v.inv) (terminal.from Z)
    (by rw [lift_ringMul, v.val_inv, from_ringOne])
  left_inv g := by
    apply pullback.hom_ext
    · apply prod.hom_ext <;> simp
    · exact Subsingleton.elim _ _
  right_inv v := by ext; simp

/-- The arrow `A^* ⊔ e → A` (inclusion of the units and zero section). -/
def unitsZeroArrow [HasBinaryCoproducts C] : unitsObj A ⨿ ⊤_ C ⟶ A :=
  coprod.desc (pullback.fst _ _ ≫ prod.fst) (ringZero A)

/-- URU5jgTvjhU-21587 (5:59:47) [def] A ring object is a field object if `A^* ⊔ e → A` is an
isomorphism. -/
def IsFieldObj [HasBinaryCoproducts C] : Prop := IsIso (unitsZeroArrow A)

/-- The object `m⁻¹(0) ⊂ A × A`. -/
abbrev zeroDivObj : C := pullback (ringMul A) (ringZero A)

/-- The two arrows `A → m⁻¹(0)`, `x ↦ (x, 0)` and `x ↦ (0, x)`. -/
def zeroDivLeft : A ⟶ zeroDivObj A :=
  pullback.lift (prod.lift (𝟙 A) (terminal.from A ≫ ringZero A)) (terminal.from A)
    (by rw [lift_ringMul, from_ringZero, mul_zero])

/-- `x ↦ (0, x)`. -/
def zeroDivRight : A ⟶ zeroDivObj A :=
  pullback.lift (prod.lift (terminal.from A ≫ ringZero A) (𝟙 A)) (terminal.from A)
    (by rw [lift_ringMul, from_ringZero, zero_mul])

/-- URU5jgTvjhU-21778 (6:02:58) [def] Integrality, first condition: `A ⊔ A → m⁻¹(0)`,
`x ↦ (x, 0)`, `x ↦ (0, x)`, is an epimorphism. -/
def IsIntegralObj₁ [HasBinaryCoproducts C] : Prop :=
  Epi (coprod.desc (zeroDivLeft A) (zeroDivRight A))

/-- URU5jgTvjhU-22099 (6:08:19) [def] Integrality, second condition (`0 ≠ 1`): the kernel `e' ⊂ e`
of `0, 1 : e ⇉ A` is initial. -/
def IsIntegralObj₂ [HasEqualizers C] : Prop := Nonempty (IsInitial (equalizer (ringZero A)
  (ringOne A)))

end RingObj

/-- URU5jgTvjhU-22035 (6:07:15) [prop] A morphism `f : S → C` is an epimorphism iff the codiagonal
`C ⊔_S C → C` is an isomorphism. -/
theorem epi_iff_isIso_codiagonal {C : Type*} [Category C] {S T : C} (f : S ⟶ T)
    [HasPushout f f] : Epi f ↔ IsIso (pushout.desc (f := f) (g := f) (𝟙 T) (𝟙 T) rfl) := by
  rw [epi_iff_isIso_inl (pushout.isColimit f f)]
  have h : pushout.inl f f ≫ pushout.desc (f := f) (g := f) (𝟙 T) (𝟙 T) rfl = 𝟙 _ := pushout.inl_desc _ _ _
  constructor
  · intro hi
    change IsIso (pushout.inl f f) at hi
    have : pushout.desc (f := f) (g := f) (𝟙 T) (𝟙 T) rfl = inv (pushout.inl f f) := by
      rw [← cancel_epi (pushout.inl f f), h, IsIso.hom_inv_id]
    rw [this]; infer_instance
  · intro hi
    change IsIso (pushout.inl f f)
    have : pushout.inl f f = inv (pushout.desc (f := f) (g := f) (𝟙 T) (𝟙 T) rfl) := by
      rw [← cancel_mono (pushout.desc (f := f) (g := f) (𝟙 T) (𝟙 T) rfl), h, IsIso.inv_hom_id]
    rw [this]; infer_instance

/-- URU5jgTvjhU-22099 (6:08:19) [def] In `Sh(X)`, `e'` is the largest open set where `A = 0`: the
sections of a sheaf of rings `A` over `U` satisfy `0 = 1` iff `U` lies in the union of the open
sets where `0 = 1`. -/
theorem zero_eq_one_iff_le (A : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X) :
    (0 : A.obj.obj (op U)) = 1 ↔ U ≤ sSup {V : Opens X | (0 : A.obj.obj (op V)) = 1} := by
  constructor
  · intro h; exact le_sSup h
  · intro hU
    let S := {V : Opens X | (0 : A.obj.obj (op V)) = 1}
    let W : S → Opens X := fun V => U ⊓ V.1
    have hcov : U ≤ iSup W := by
      intro x hx
      obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.1 (hU hx)
      exact Opens.mem_iSup.2 ⟨⟨V, hV⟩, ⟨hx, hxV⟩⟩
    apply TopCat.Sheaf.eq_of_locally_eq' A W U (fun V => homOfLE inf_le_left) hcov
    intro V
    have h1 : (0 : A.obj.obj (op V.1)) = 1 := V.2
    have := congrArg (A.obj.map (homOfLE (inf_le_right : W V ≤ V.1)).op) h1
    rw [map_zero, map_one] at this
    rw [map_zero, map_one]
    exact this

/-- URU5jgTvjhU-22420 (6:13:40) [prop] A sheaf of rings is never a presheaf of fields: its value
on `∅` is the zero ring. -/
theorem sheaf_empty_not_field (A : TopCat.Sheaf CommRingCat.{u} X) :
    ¬ IsField (A.obj.obj (op ⊥)) := by
  intro h
  obtain ⟨x, y, hxy⟩ := h.exists_pair_ne
  have := CommRingCat.subsingleton_of_isTerminal (A.isTerminalOfEmpty)
  exact hxy (Subsingleton.elim x y)

/-! ## Constant sheaves -/

instance sheaf_hasColimits : HasColimits (Sheaf (Opens.grothendieckTopology X) (Type u)) :=
  have := (sheaf_colimits (X := X)).1
  ⟨fun K _ => this K⟩

/-- URU5jgTvjhU-22609 (6:16:49) [def] The constant sheaf `I_X` (Mathlib's `constantSheaf`, the
sheaf associated to the constant presheaf, i.e. `p^*I` for `p : X → pt`). -/
abbrev constSheaf (I : Type u) : Sheaf (Opens.grothendieckTopology X) (Type u) :=
  (constantSheaf (Opens.grothendieckTopology X) (Type u)).obj I

instance constantSheaf_preservesFiniteLimits :
    PreservesFiniteLimits (constantSheaf (Opens.grothendieckTopology X) (Type u)) := by
  unfold constantSheaf
  infer_instance

/-- The constant sheaf functor `I ↦ I_X` is left adjoint to `Γ`. -/
def constantSheaf_adj :
    constantSheaf (Opens.grothendieckTopology X) (Type u) ⊣
      (sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op ⊤) :=
  constantSheafAdj _ _ isTerminalTop

/-- URU5jgTvjhU-22609 (6:16:49) [def] `I_X` is the coproduct of `I` copies of the terminal
object. -/
def constSheaf_iso_coprod (I : Type u) :
    constSheaf (X := X) I ≅ ∐ fun _ : I => ⊤_ (Sheaf (Opens.grothendieckTopology X) (Type u)) := by
  have : PreservesColimits (constantSheaf (Opens.grothendieckTopology X) (Type u)) :=
    (constantSheaf_adj (X := X)).leftAdjoint_preservesColimits
  let e : I ≅ ∐ fun _ : I => ⊤_ (Type u) :=
    (Equiv.toIso ((Equiv.sigmaPUnit I).symm.trans
      (Equiv.sigmaCongrRight fun _ => (Types.terminalIso.toEquiv).symm))) ≪≫
      (Types.coproductIso fun _ : I => ⊤_ (Type u)).symm
  exact (constantSheaf _ _).mapIso e ≪≫
    PreservesCoproduct.iso (constantSheaf (Opens.grothendieckTopology X) (Type u)) _ ≪≫
    Sigma.mapIso (fun _ => PreservesTerminal.iso (constantSheaf _ _))

/-- URU5jgTvjhU-22740 (6:19:00) [prop] Since `I ↦ I_X` commutes with finite limits, a group `I`
gives a sheaf of groups `I_X`. -/
def constSheaf_grp :
    Grp (Type u) ⥤ Grp (Sheaf (Opens.grothendieckTopology X) (Type u)) :=
  haveI : PreservesFiniteProducts (constantSheaf (Opens.grothendieckTopology X) (Type u)) :=
    ⟨fun _ => inferInstance⟩
  mapGrpOfPreserves (constantSheaf (Opens.grothendieckTopology X) (Type u))

/-- URU5jgTvjhU-22740 (6:19:00) [prop] A ring `I` gives a sheaf of rings `I_X` (Mathlib's constant
sheaf with values in `CommRingCat`). -/
abbrev constSheafRing (R : CommRingCat.{u}) : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  (constantSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj R

/-- URU5jgTvjhU-22867 (6:21:07) [prop] The total ring of fractions of a domain is a field. -/
example (R : Type*) [CommRing R] [IsDomain R] : Field (FractionRing R) := inferInstance

/-- URU5jgTvjhU-22934 (6:22:14) [prop] On an irreducible space, every nonempty open set is
connected, so a locally constant section of `I_X` over it is constant: the constant sheaf has
value `I` on every nonempty open set. -/
theorem irreducible_locallyConstant_const {Z I : Type*} [TopologicalSpace Z] [IrreducibleSpace Z]
    {U : Set Z} (hU : IsOpen U) {f : U → I} (hf : IsLocallyConstant f) (x y : U) : f x = f y := by
  have hpre : IsPreconnected U :=
    (IsPreirreducible.open_subset (IrreducibleSpace.isIrreducible_univ Z).isPreirreducible hU
      (Set.subset_univ _)).isPreconnected
  have : PreconnectedSpace U := Subtype.preconnectedSpace hpre
  exact hf.apply_eq_of_preconnectedSpace x y

/-- URU5jgTvjhU-22545 (6:15:45) [prop] On a space, the axiom of fields is checked stalkwise: the
stalks of a presheaf of rings `A` are all fields iff `A` is nonzero over every nonempty open set and
every section is, near each point, invertible or zero (the condition « `A^* ⊔ e → A` is an
isomorphism », read on sections). -/
theorem stalks_field_iff (A : X.Presheaf CommRingCat.{u}) :
    (∀ x, IsField (A.stalk x)) ↔
      (∀ (U : Opens X) (x : X), x ∈ U → (0 : A.obj (op U)) ≠ 1) ∧
      ∀ (U : Opens X) (s : A.obj (op U)) (x : X), x ∈ U →
        ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧
          (IsUnit (A.map (homOfLE h).op s) ∨ A.map (homOfLE h).op s = 0) := by
  constructor
  · intro hA
    refine ⟨fun U x hx h01 => ?_, fun U s x hx => ?_⟩
    · obtain ⟨a, b, hab⟩ := (hA x).exists_pair_ne
      have : (0 : A.stalk x) = 1 := by
        have := congrArg (A.germ U x hx) h01
        rwa [map_zero, map_one] at this
      exact hab (by
        rw [← one_mul a, ← one_mul b, ← this, zero_mul, zero_mul])
    · by_cases hg : A.germ U x hx s = 0
      · rw [← map_zero (A.germ U x hx).hom] at hg
        obtain ⟨W, hxW, iU, iV, he⟩ := A.germ_eq x hx hx s 0 hg
        refine ⟨W, iU.le, hxW, Or.inr ?_⟩
        rw [show homOfLE iU.le = iU from rfl, he, map_zero]
      · obtain ⟨h, hh⟩ := (hA x).mul_inv_cancel hg
        obtain ⟨W, hWU, hxW, t, ht⟩ := A.exists_le_germ_eq h hx
        have h1 : A.germ W x hxW (A.map (homOfLE hWU).op s * t) = A.germ W x hxW 1 := by
          rw [map_mul, map_one, ht, A.germ_res_apply, hh]
        obtain ⟨W', hxW', iU, iV, he⟩ := A.germ_eq x hxW hxW _ _ h1
        refine ⟨W', iU.le.trans hWU, hxW', Or.inl ?_⟩
        rw [map_mul, map_one] at he
        refine isUnit_iff_exists_inv.2 ⟨A.map iV.op t, ?_⟩
        rw [Subsingleton.elim iV iU, ← he]
        congr 1
        rw [← ConcreteCategory.comp_apply, ← A.map_comp]
        rfl
  · rintro ⟨h0, hloc⟩ x
    refine ⟨⟨0, 1, fun h01 => ?_⟩, mul_comm, fun {g} hg => ?_⟩
    · have hx : x ∈ (⊤ : Opens X) := trivial
      have : A.germ ⊤ x hx 0 = A.germ ⊤ x hx 1 := by rw [map_zero, map_one, h01]
      obtain ⟨W, hxW, iU, iV, he⟩ := A.germ_eq x hx hx _ _ this
      rw [map_zero, map_one] at he
      exact h0 W x hxW he
    · obtain ⟨U, hxU, s, rfl⟩ := A.exists_germ_eq g
      obtain ⟨V, hVU, hxV, hu | hz⟩ := hloc U s x hxU
      · obtain ⟨v, hv⟩ := hu.exists_right_inv
        refine ⟨A.germ V x hxV v, ?_⟩
        rw [← A.germ_res_apply (homOfLE hVU) x hxV s, ← map_mul, hv, map_one]
      · exact absurd (by rw [← A.germ_res_apply (homOfLE hVU) x hxV s, hz, map_zero]) hg

/-! ## Internal Hom and the subobject sheaf -/

/-- URU5jgTvjhU-22998 (6:23:18) [def] `𝓗om(F,G)(U) = Hom(F|_U, G|_U)` is a sheaf (Mathlib's
`sheafHom`), distinct from the set `Hom(F, G)` of its global sections. -/
example (F G : Sheaf (Opens.grothendieckTopology X) (Type u)) (U : Opens X) :
    (presheafHom F.obj G.obj).obj (op U) =
      ((Over.forget U).op ⋙ F.obj ⟶ (Over.forget U).op ⋙ G.obj) :=
  rfl

/-- The global sections of `𝓗om(F,G)` are the morphisms `F → G`. -/
def sheafHom_sections (F G : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    (presheafHom F.obj G.obj).sections ≃ (F ⟶ G) :=
  (presheafHomSectionsEquiv F.obj G.obj).trans (fullyFaithfulSheafToPresheaf _ _).homEquiv.symm

section Closed

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- URU5jgTvjhU-23169 (6:26:09) [prop] and URU5jgTvjhU-23366 (6:29:26) [def] `𝓗om(F,G)` represents
`X' ↦ Hom(F × X', G)` (Mathlib's internal Hom `ihom F`). -/
def ihom_homEquiv (F G X' : C) : (X' ⟶ (ihom F).obj G) ≃ (F ⊗ X' ⟶ G) :=
  ((ihom.adjunction F).homEquiv X' G).symm

/-- URU5jgTvjhU-23169 (6:26:09) [prop] `Hom_{X'}(F × X', G × X') ≃ Hom(F × X', G)`: morphisms over
`X'` between the objects `X' × F → X'` and `X' × G → X'` (Mathlib's `Over.star`). -/
def star_homEquiv [HasBinaryProducts C] (F G X' : C) :
    ((Over.star X').obj F ⟶ (Over.star X').obj G) ≃ (X' ⨯ F ⟶ G) :=
  ((Over.forgetAdjStar X').homEquiv _ _).symm

/-- In `Sh(X)` the internal Hom exists. -/
example : MonoidalClosed (Sheaf (Opens.grothendieckTopology X) (Type u)) := inferInstance

attribute [local instance] Over.cartesianMonoidalCategory in
/-- URU5jgTvjhU-23428 (6:30:28) [def] For group objects `F, G`, `Hom_gr(F_{X'}, G_{X'})`: the
homomorphisms between the group objects `F × X'`, `G × X'` of `C/X'`. -/
def HomGr [HasBinaryProducts C] [HasPullbacks C] (F G : Grp C) (X' : C) : Type _ :=
  have : PreservesLimits (Over.star X') := (Over.forgetAdjStar X').rightAdjoint_preservesLimits
  have : PreservesFiniteProducts (Over.star X') :=
    ⟨fun _ => preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift.{v₁}) _⟩
  (mapGrpOfPreserves (Over.star X')).obj F ⟶ (mapGrpOfPreserves (Over.star X')).obj G

variable [HasPullbacks C] (𝒞 : Subobject.Classifier C)

/-- URU5jgTvjhU-23555 (6:32:35) [def] The object `𝓟(F) = Ω^F`. -/
abbrev powerObj (F : C) : C := (ihom F).obj 𝒞.Ω

/-- URU5jgTvjhU-23684 (6:34:44) [prop] `𝓟(F)` represents `X' ↦ Sub(F × X')`. -/
def powerObj_homEquiv (F X' : C) : (X' ⟶ powerObj 𝒞 F) ≃ Subobject (F ⊗ X') :=
  (ihom_homEquiv F 𝒞.Ω X').trans 𝒞.representableBy.homEquiv

/-- URU5jgTvjhU-23881 (6:38:01) [prop] `𝓟(e) = Ω` represents `X' ↦ Sub(X')`. -/
def classifier_homEquiv (X' : C) : (X' ⟶ 𝒞.Ω) ≃ Subobject X' :=
  𝒞.representableBy.homEquiv

end Closed

/-- URU5jgTvjhU-23555 (6:32:35) [def] For `X` a point (sets), the subobjects of `F` are its
subsets. -/
def subobject_types (F : Type u) : Subobject F ≃o Set F := Types.subobjectEquivSet F

/-- URU5jgTvjhU-24070 (6:41:10) [prop] In `Set`, `𝓟(e) = Ω` has two elements. -/
def classifier_types (𝒞 : Subobject.Classifier (Type u)) : 𝒞.Ω ≃ Bool :=
  (Equiv.mk (α := 𝒞.Ω) (β := PUnit.{u + 1} ⟶ 𝒞.Ω) (fun x => ↾fun _ => x) (fun f => f PUnit.unit)
    (fun _ => rfl) (fun _ => by ext ⟨⟩; rfl)).trans <|
  (classifier_homEquiv 𝒞 PUnit.{u + 1}).trans <| (subobject_types PUnit.{u + 1}).toEquiv.trans <|
    (Equiv.punitArrowEquiv Prop).trans Equiv.propEquivBool

/-- URU5jgTvjhU-24459 (6:47:39) [prop] `f^*` commutes with binary products, the hypothesis under which
the canonical arrow `f^*𝓗om(F,G) → 𝓗om(f^*F, f^*G)` is defined (Mathlib's `expComparison`). -/
example (f : X ⟶ Y) :
    PreservesLimitsOfShape (Discrete WalkingPair) (TopCat.Sheaf.pullback (Type u) f) :=
  inferInstance

end

end Buffalo.Topos.Part02
