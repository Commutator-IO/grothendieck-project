import Mathlib

/-!
# Buffalo, topos theory, part 6a: accessible categories, `Ind`, cardinal filtrations (10 July 1973)

Entries of `docs/buffalo-topos/index.tex` lines 831–879 (video `4gynb9uTEE4`, 4:14:44–5:32:58):
accessible functors, objects and categories, the examples `Set^op` and topoi, `Ind`-categories and
cardinal filtrations. The status of each entry is in `docs/buffalo-topos/lean/Part06.json`.

Grothendieck's cardinal `π` (families of cardinality `≤ π`) corresponds to Mathlib's regular
cardinal `κ = π⁺` (families of cardinality `< κ`): an ordered set dominating `π` is a
`κ`-filtered ordered set (`dominates_iff_isCardinalFiltered`). His `π`-accessible functors and
objects are Mathlib's `Functor.IsCardinalAccessible` and `IsCardinalPresentable`; his
`π`-accessible categories with small colimits are Mathlib's `IsCardinalLocallyPresentable`.
-/

universe w v u

open CategoryTheory Limits Opposite Cardinal

namespace Buffalo.Topos.Part06

noncomputable section

/-! ## Accessible categories -/

section Dominates

/-- 4gynb9uTEE4-15284 (4:14:44) [def] A preordered set `I` dominates `π` if it is filtered
(nonempty and directed) and every family of cardinality `≤ π` of elements of `I` has an upper
bound. -/
def Dominates (π : Cardinal.{w}) (I : Type w) [Preorder I] : Prop :=
  Nonempty I ∧ IsDirected I (· ≤ ·) ∧
    ∀ (K : Type w) (s : K → I), Cardinal.mk K ≤ π → ∃ j, ∀ k, s k ≤ j

/-- ... for `π ≥ 2`, the second condition implies the first. -/
theorem dominates_of_bound {π : Cardinal.{w}} (hπ : 2 ≤ π) {I : Type w} [Preorder I]
    (h : ∀ (K : Type w) (s : K → I), Cardinal.mk K ≤ π → ∃ j, ∀ k, s k ≤ j) :
    Dominates π I := by
  refine ⟨?_, ⟨fun a b => ?_⟩, h⟩
  · obtain ⟨j, -⟩ := h PEmpty PEmpty.elim (by simp)
    exact ⟨j⟩
  · obtain ⟨j, hj⟩ := h (ULift.{w} Bool) (fun x => if x.down then a else b) (by simpa using hπ)
    exact ⟨j, by simpa using hj ⟨true⟩, by simpa using hj ⟨false⟩⟩

/-- For `π` infinite, an ordered set dominates `π` iff it is `π⁺`-filtered in Mathlib's sense. -/
theorem dominates_iff_isCardinalFiltered {π : Cardinal.{w}} (hπ : ℵ₀ ≤ π) (I : Type w)
    [Preorder I] [Fact (Order.succ π).IsRegular] :
    Dominates π I ↔ IsCardinalFiltered I (Order.succ π) := by
  constructor
  · rintro ⟨-, -, h⟩
    exact isCardinalFiltered_preorder I _ (fun K s hK => h K s (Order.lt_succ_iff.1 hK))
  · intro hI
    refine dominates_of_bound ((Cardinal.natCast_lt_aleph0 (n := 2)).le.trans hπ) (fun K s hK => ?_)
    have hK' : HasCardinalLT K (Order.succ π) := by
      rw [hasCardinalLT_iff_cardinal_mk_lt]; exact Order.lt_succ_iff.2 hK
    exact ⟨IsCardinalFiltered.max s hK', fun k => leOfHom (IsCardinalFiltered.toMax s hK' k)⟩

end Dominates

section Accessible

variable {E : Type u} [Category.{v} E] {E' : Type*} [Category* E']

/-- 4gynb9uTEE4-15352 (4:15:52) [def] `E` satisfies `L_π`: colimits indexed by every small ordered
set dominating `π` exist in `E`. (`E` satisfies `L` if it satisfies `L_π` for some `π`.) -/
def SatisfiesL (π : Cardinal.{w}) (E : Type u) [Category.{v} E] : Prop :=
  ∀ (I : Type w) [Preorder I], Dominates π I → HasColimitsOfShape I E

/-- A category with small colimits satisfies every `L_π`. -/
theorem satisfiesL_of_hasColimits [HasColimitsOfSize.{w, w} E] (π : Cardinal.{w}) :
    SatisfiesL π E := fun _ _ _ => inferInstance

/-- Mathlib's `κ`-filtered colimits (`κ = π⁺`) give `L_π`. -/
theorem satisfiesL_of_hasCardinalFilteredColimits {π : Cardinal.{w}} (hπ : ℵ₀ ≤ π)
    [Fact (Order.succ π).IsRegular] [HasCardinalFilteredColimits.{w} E (Order.succ π)] :
    SatisfiesL π E := fun I _ hI => by
  have := (dominates_iff_isCardinalFiltered hπ I).1 hI
  exact HasCardinalFilteredColimits.hasColimitsOfShape (C := E) (Order.succ π) I

/-- 4gynb9uTEE4-15482 (4:18:02) [def] A functor `F : E → E'` is `π`-accessible if `E` satisfies
`L_π` and `F` commutes with colimits indexed by the ordered sets dominating `π`. -/
def IsPiAccessible (π : Cardinal.{w}) (F : E ⥤ E') : Prop :=
  SatisfiesL.{w} π E ∧ ∀ (I : Type w) [Preorder I], Dominates π I → PreservesColimitsOfShape I F

/-- A Mathlib `π⁺`-accessible functor (commuting with all `π⁺`-filtered colimits) is
`π`-accessible in Grothendieck's sense. -/
theorem isPiAccessible_of_isCardinalAccessible {π : Cardinal.{w}} (hπ : ℵ₀ ≤ π)
    [Fact (Order.succ π).IsRegular] [HasCardinalFilteredColimits.{w} E (Order.succ π)]
    (F : E ⥤ E') [F.IsCardinalAccessible (Order.succ π)] : IsPiAccessible π F :=
  ⟨satisfiesL_of_hasCardinalFilteredColimits hπ, fun I _ hI => by
    have := (dominates_iff_isCardinalFiltered hπ I).1 hI
    exact Functor.preservesColimitsOfShape_of_isCardinalAccessible F (Order.succ π) I⟩

/-- 4gynb9uTEE4-15673 (4:21:13) [def] An object `X` is `π`-accessible if `Hom(X, -) : E → Set` is a
`π`-accessible functor (Mathlib: `IsCardinalPresentable X π⁺`). -/
def IsPiAccessibleObj (π : Cardinal.{w}) (X : E) : Prop :=
  IsPiAccessible π (coyoneda.obj (op X))

theorem isPiAccessibleObj_of_isCardinalPresentable {π : Cardinal.{w}} (hπ : ℵ₀ ≤ π)
    [Fact (Order.succ π).IsRegular] [HasCardinalFilteredColimits.{w} E (Order.succ π)]
    (X : E) [IsCardinalPresentable X (Order.succ π)] : IsPiAccessibleObj π X :=
  isPiAccessible_of_isCardinalAccessible hπ _

/-- 4gynb9uTEE4-15809 (4:23:29) [def] `E` is `π`-accessible if it satisfies `L_π` and has a small
full strictly generating subcategory `C` of `π`-accessible objects: every object `X` is the
colimit of the canonical diagram `C/X → E` (`C.ι` is dense). -/
def IsPiAccessibleCat (π : Cardinal.{w}) (E : Type u) [Category.{v} E] : Prop :=
  SatisfiesL.{w} π E ∧ ∃ C : ObjectProperty E, ObjectProperty.EssentiallySmall.{w} C ∧
    (∀ X, C X → IsPiAccessibleObj.{w} π X) ∧ C.ι.IsDense

/-- 4gynb9uTEE4-15877 (4:24:37) [rem] A strictly generating (dense) subcategory is in particular a
(strong) generator, so the definition is stronger than mere generation. -/
theorem isStrongGenerator_of_isDense (C : ObjectProperty E) [C.ι.IsDense] :
    (ObjectProperty.ofObj C.ι.obj).IsStrongGenerator :=
  Functor.isStrongGenerator_of_isDense C.ι

/-- 4gynb9uTEE4-16008 (4:26:48) [prop] A colimit, computed argumentwise, of `κ`-accessible
functors is `κ`-accessible. -/
theorem colimit_isCardinalAccessible {J : Type*} [Category* J] [HasColimitsOfShape J E']
    (F : J ⥤ E ⥤ E') (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [∀ j, (F.obj j).IsCardinalAccessible κ] : (colimit F).IsCardinalAccessible κ where
  preservesColimitOfShape I _ _ := by
    have : PreservesColimitsOfShape I F.flip :=
      preservesColimitsOfShape_of_evaluation _ _ (fun j =>
        Functor.preservesColimitsOfShape_of_isCardinalAccessible (F.obj j) κ I)
    exact preservesColimitsOfShape_of_natIso (colimitIsoFlipCompColim F).symm

/-- 4gynb9uTEE4-16076 (4:27:56) [prop] (corrected) With values in `Set`, a limit, computed
argumentwise and indexed by a category with `< κ` arrows, of `κ`-accessible functors is
`κ`-accessible. (For a general target `E'` one needs colimits along the `I` dominating `π` to
commute with such limits in `E'`.) -/
theorem limit_isCardinalAccessible {K : Type*} [Category* K] {F : K ⥤ E ⥤ Type w}
    (c : Cone F) (hc : IsLimit c) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasLimitsOfShape K (Type w)] (hK : HasCardinalLT (Arrow K) κ)
    [∀ k, (F.obj k).IsCardinalAccessible κ] : c.pt.IsCardinalAccessible κ :=
  Functor.isCardinalAccessible_of_isLimit c hc κ hK

/-- 4gynb9uTEE4-16213 (4:30:13) [prop] In `Set`, colimits along a `κ`-filtered category commute
with limits along a category with `< κ` arrows: `lim : Set^K → Set` commutes with them. -/
theorem lim_preservesCardinalFilteredColimits {K : Type w} [SmallCategory K] (κ : Cardinal.{w})
    [Fact κ.IsRegular] (hK : HasCardinalLT (Arrow K) κ) (I : Type w) [SmallCategory I]
    [IsCardinalFiltered I κ] : PreservesColimitsOfShape I (lim : (K ⥤ Type w) ⥤ Type w) := by
  have : (limit (evaluation K (Type w))).IsCardinalAccessible κ :=
    Functor.isCardinalAccessible_of_isLimit _ (limit.isLimit _) κ hK
  have e : limit (evaluation K (Type w)) ≅ lim :=
    limitIsoFlipCompLim _ ≪≫ Functor.isoWhiskerRight
      (NatIso.ofComponents (fun G => NatIso.ofComponents (fun _ => Iso.refl _))) lim ≪≫
      Functor.leftUnitor _
  have := Functor.isCardinalAccessible_of_natIso e κ
  exact Functor.preservesColimitsOfShape_of_isCardinalAccessible _ κ I

/-- A regular cardinal above a small family of cardinals and above the size of a small type. -/
theorem exists_regular_ge {ι : Type w} (f : ι → Cardinal.{w}) (X : Type w) :
    ∃ κ : Cardinal.{w}, κ.IsRegular ∧ (∀ i, f i ≤ κ) ∧ HasCardinalLT X κ := by
  refine ⟨Order.succ (max (max (⨆ i, f i) (Cardinal.mk X)) ℵ₀),
    isRegular_succ (le_max_right _ _), fun i => ?_, ?_⟩
  · exact ((le_ciSup (Cardinal.bddAbove_of_small (s := Set.range f)) i).trans
      ((le_max_left _ _).trans (le_max_left _ _))).trans (Order.le_succ _)
  · rw [hasCardinalLT_iff_cardinal_mk_lt]
    exact Order.lt_succ_iff.2 ((le_max_right _ _).trans (le_max_left _ _))

/-- 4gynb9uTEE4-16213 (4:30:13) [prop] (corrected) Accessible functors are stable under small
colimits computed argumentwise ... -/
theorem colimit_isAccessible {J : Type w} [SmallCategory J] [HasColimitsOfShape J E']
    (F : J ⥤ E ⥤ E') [∀ j, (F.obj j).IsAccessible.{w}] : (colimit F).IsAccessible.{w} := by
  choose κ hκ h using fun j => Functor.IsAccessible.exists_cardinal (F.obj j)
  obtain ⟨μ, hμ, hle, -⟩ := exists_regular_ge κ PUnit
  have : Fact μ.IsRegular := ⟨hμ⟩
  have : ∀ j, (F.obj j).IsCardinalAccessible μ := fun j =>
    Functor.isCardinalAccessible_of_le (F.obj j) (hle j)
  have := colimit_isCardinalAccessible F μ
  exact Functor.isAccessible_of_isCardinalAccessible _ μ

/-- ... and (with values in `Set`) under small limits computed argumentwise. -/
theorem limit_isAccessible {K : Type w} [SmallCategory K] (F : K ⥤ E ⥤ Type w)
    [∀ k, (F.obj k).IsAccessible.{w}] : (limit F).IsAccessible.{w} := by
  choose κ hκ h using fun k => Functor.IsAccessible.exists_cardinal (F.obj k)
  obtain ⟨μ, hμ, hle, hK⟩ := exists_regular_ge κ (Arrow K)
  have : Fact μ.IsRegular := ⟨hμ⟩
  have : ∀ k, (F.obj k).IsCardinalAccessible μ := fun k =>
    Functor.isCardinalAccessible_of_le (F.obj k) (hle k)
  have := Functor.isCardinalAccessible_of_isLimit _ (limit.isLimit F) μ hK
  exact @Functor.isAccessible_of_isCardinalAccessible _ _ _ _ (limit F) μ _ this

/-- 4gynb9uTEE4-16276 (4:31:16) [prop] The `κ`-accessible objects are stable under colimits
indexed by a category with `< κ` arrows (Mathlib). -/
theorem isClosedUnderColimitsOfShape_presentable [LocallySmall.{w} E] {κ : Cardinal.{w}}
    [Fact κ.IsRegular] {J : Type*} [Category* J] [HasLimitsOfShape Jᵒᵖ (Type w)]
    (hJ : HasCardinalLT (Arrow J) κ) :
    (isCardinalPresentable E κ).IsClosedUnderColimitsOfShape J :=
  isClosedUnderColimitsOfShape_isCardinalPresentable E hJ

/-- 4gynb9uTEE4-16341 (4:32:21) [prop] The accessible objects are stable under small colimits. -/
theorem isPresentable_of_isColimit [LocallySmall.{w} E] {K : Type w} [SmallCategory K]
    {Y : K ⥤ E} (c : Cocone Y) (hc : IsColimit c) [h : ∀ k, IsPresentable.{w} (Y.obj k)] :
    IsPresentable.{w} c.pt := by
  choose κ hκ h' using fun k => Functor.IsAccessible.exists_cardinal (coyoneda.obj (op (Y.obj k)))
  obtain ⟨μ, hμ, hle, hK⟩ := exists_regular_ge κ (Arrow K)
  have : Fact μ.IsRegular := ⟨hμ⟩
  have : ∀ k, IsCardinalPresentable (Y.obj k) μ := fun k =>
    isCardinalPresentable_of_le (Y.obj k) (hle k)
  have := isCardinalPresentable_of_isColimit c hc μ hK
  exact isPresentable_of_isCardinalPresentable c.pt μ

/-- 4gynb9uTEE4-16406 (4:33:26) [prop] In an accessible category every object is accessible
(Mathlib). -/
theorem isPresentable_of_isAccessibleCategory [IsAccessibleCategory.{w} E] (X : E) :
    IsPresentable.{w} X := inferInstance

end Accessible

/-! ## Examples of accessible categories -/

section Examples

/-- 4gynb9uTEE4-16654 (4:37:34) [prop] (special case `Set`) An epimorphic family is jointly
surjective ... -/
theorem jointly_surjective_of_epi {B : Type u} {α : Type*} (X : α → Type u) (π : ∀ a, X a ⟶ B)
    (h : ∀ (W : Type u) (f g : B ⟶ W), (∀ a, π a ≫ f = π a ≫ g) → f = g) (b : B) :
    ∃ a x, π a x = b := by
  by_contra hb
  push Not at hb
  let f : B ⟶ ULift Prop := ↾fun _ => ULift.up True
  let g : B ⟶ ULift Prop := ↾fun y => ULift.up (∃ a x, π a x = y)
  have hfg : ∀ a, π a ≫ f = π a ≫ g := by
    intro a; ext x; simpa [f, g] using ⟨a, x, rfl⟩
  have := congrArg ULift.down (ConcreteCategory.congr_hom (h _ f g hfg) b)
  simp only [f, g] at this
  obtain ⟨a, x, hx⟩ := cast this trivial
  exact hb a x hx

/-- ... a jointly surjective family is strictly epimorphic ... -/
def effectiveEpiFamilyStructOfSurjective {B : Type u} {α : Type*} (X : α → Type u)
    (π : ∀ a, X a ⟶ B) (hπ : ∀ b, ∃ a x, π a x = b) : EffectiveEpiFamilyStruct X π where
  desc {W} e h := ↾fun b => e (hπ b).choose (hπ b).choose_spec.choose
  fac {W} e h a := by
    ext x
    have hx := (hπ (π a x)).choose_spec.choose_spec
    have := h (Z := PUnit) _ a (↾fun _ => (hπ (π a x)).choose_spec.choose) (↾fun _ => x)
      (by ext; exact hx)
    exact ConcreteCategory.congr_hom this PUnit.unit
  uniq {W} e h m hm := by
    ext b
    have hb := (hπ b).choose_spec.choose_spec
    change m b = e (hπ b).choose (hπ b).choose_spec.choose
    conv_lhs => rw [← hb]
    exact ConcreteCategory.congr_hom (hm _) _

/-- ... and universal: its pullback along any map is again jointly surjective. -/
theorem jointly_surjective_pullback {B B' : Type u} {α : Type*} (X : α → Type u)
    (π : ∀ a, X a ⟶ B) (hπ : ∀ b, ∃ a x, π a x = b) (f : B' → B) (b' : B') :
    ∃ a, ∃ x : {p : X a × B' // π a p.1 = f p.2}, x.1.2 = b' := by
  obtain ⟨a, x, hx⟩ := hπ (f b')
  exact ⟨a, ⟨(x, b'), hx⟩, rfl⟩

theorem effectiveEpiFamily_of_epi {B : Type u} {α : Type*} (X : α → Type u) (π : ∀ a, X a ⟶ B)
    (h : ∀ (W : Type u) (f g : B ⟶ W), (∀ a, π a ≫ f = π a ≫ g) → f = g) :
    EffectiveEpiFamily X π :=
  ⟨⟨effectiveEpiFamilyStructOfSurjective X π (jointly_surjective_of_epi X π h)⟩⟩

/-- 4gynb9uTEE4-16654 (4:37:34) [prop] (special case: presheaf topoi, which satisfy all the
hypotheses of SGA 4 I 9.11) presheaf categories on a small category are locally presentable. -/
theorem presheaf_isLocallyPresentable (C : Type u) [SmallCategory C] :
    IsLocallyPresentable.{u} (Cᵒᵖ ⥤ Type u) := inferInstance

/-- 4gynb9uTEE4-16782 (4:39:42) [ex] (presheaf topoi) Every presheaf topos is accessible. -/
theorem presheaf_isAccessibleCategory (C : Type u) [SmallCategory C] :
    IsAccessibleCategory.{u} (Cᵒᵖ ⥤ Type u) := inferInstance

section SetOp

variable {I : Type u} (Y : I → Type u)

/-- The partial product `∏_{i ∈ S} Y_i`. -/
abbrev partialProd (S : Set I) : Type u := ∀ i : S, Y i

/-- 4gynb9uTEE4-16908 (4:41:48) [prop] The diagram of partial products over the subsets of `I` of
cardinality `< κ` (an ordered set that is `κ`-filtered: Mathlib instance). -/
@[simps]
def partialProdDiagram (κ : Cardinal.{u}) : (HasCardinalLT.Set I κ)ᵒᵖ ⥤ Type u where
  obj S := partialProd Y S.unop.1
  map {S T} h := ↾fun z i => z ⟨i.1, leOfHom h.unop i.2⟩

/-- The cone of restrictions from `∏_{i ∈ I} Y_i`. -/
@[simps]
def partialProdCone (κ : Cardinal.{u}) : Cone (partialProdDiagram Y κ) where
  pt := ∀ i, Y i
  π := { app S := ↾fun z i => z i.1 }

/-- ... `∏_{i ∈ I} Y_i` is the limit of the partial products (`κ` infinite). -/
def partialProdConeIsLimit {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) :
    IsLimit (partialProdCone Y κ) where
  lift s := ↾fun x i => (s.π.app (op ⟨({i} : Set I), hasCardinalLT_of_finite _ _ hκ⟩) x) ⟨i, rfl⟩
  fac s S := by
    ext x
    funext ⟨i, hi⟩
    have h1 : (⟨({i} : Set I), hasCardinalLT_of_finite _ _ hκ⟩ : HasCardinalLT.Set I κ) ≤
        S.unop := by
      intro j hj; rw [Set.mem_singleton_iff.1 hj]; exact hi
    have := ConcreteCategory.congr_hom (s.w (homOfLE h1).op) x
    exact (congrFun this ⟨i, rfl⟩).symm
  uniq s m hm := by
    ext x
    funext i
    have := ConcreteCategory.congr_hom (hm (op ⟨({i} : Set I), hasCardinalLT_of_finite _ _ hκ⟩)) x
    exact congrFun this ⟨i, rfl⟩

open Classical in
/-- 4gynb9uTEE4-17102 (4:45:02) [prop] If some index `i ∉ S` exists and every `Y_i` has two
distinct points, the indicator of a point `y₀` of `∏ Y_i` factors through no partial product
`∏_{i ∈ S} Y_i`. -/
theorem indicator_not_factor (hY : ∀ i, ∃ a b : Y i, a ≠ b) (y₀ : ∀ i, Y i) {S : Set I}
    {i : I} (hi : i ∉ S) {T : Type*} (g : partialProd Y S → T) {t₁ t₂ : T} (ht : t₁ ≠ t₂)
    (f : (∀ i, Y i) → T) (hf : ∀ z, f z = if z = y₀ then t₁ else t₂)
    (hfg : ∀ z, f z = g (fun j => z j.1)) : False := by
  classical
  obtain ⟨a, b, hab⟩ := hY i
  let c : Y i := if y₀ i = a then b else a
  have hc : c ≠ y₀ i := by
    by_cases h : y₀ i = a
    · simp only [c, h, ite_true]; exact fun e => hab (e.symm)
    · simp only [c, h, ite_false]; exact fun e => h e.symm
  let z := Function.update y₀ i c
  have hz : z ≠ y₀ := fun e => hc (by simpa [z] using congrFun e i)
  have hres : (fun j : S => z j.1) = fun j : S => y₀ j.1 := by
    funext j
    have : j.1 ≠ i := fun e => hi (e ▸ j.2)
    simp [z, Function.update_of_ne this]
  have := (hfg z).trans ((congrArg g hres).trans (hfg y₀).symm)
  rw [hf, hf] at this
  simp only [hz, ite_false, ite_true] at this
  exact ht this.symm

/-- 4gynb9uTEE4-16782 (4:39:42) [cex] A set `X` with two distinct points is not an accessible
object of `Set^op`: for no regular `κ` is `X` `κ`-presentable in `Set^op`. -/
theorem not_isCardinalPresentable_op {X : Type u} {x₁ x₂ : X} (hx : x₁ ≠ x₂) (κ : Cardinal.{u})
    [Fact κ.IsRegular] : ¬ IsCardinalPresentable (op X) κ := by
  classical
  intro hX
  let I : Type u := κ.out
  have hI : ¬ HasCardinalLT I κ := by
    rw [hasCardinalLT_iff_cardinal_mk_lt]; simp [I]
  let Y : I → Type u := fun _ => ULift Bool
  have hκ : ℵ₀ ≤ κ := (Fact.out : κ.IsRegular).aleph0_le
  let c := (partialProdCone Y κ)
  have hc : IsColimit c.op := (partialProdConeIsLimit Y hκ).op
  have : IsCardinalFiltered (HasCardinalLT.Set I κ)ᵒᵖᵒᵖ κ :=
    IsCardinalFiltered.of_equivalence κ (opOpEquivalence _).symm
  let y₀ : ∀ i, Y i := fun _ => ⟨true⟩
  let f : (∀ i, Y i) → X := fun z => if z = y₀ then x₁ else x₂
  obtain ⟨S, g, hg⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hc (X := op X)
    (Quiver.Hom.op (↾f))
  have hS := S.unop.unop.2
  obtain ⟨i, hi⟩ : ∃ i, i ∉ S.unop.unop.1 := by
    by_contra h
    push Not at h
    exact hI (hS.of_injective (fun i => ⟨i, h i⟩) (fun _ _ e => congrArg Subtype.val e))
  have hg' := congrArg Quiver.Hom.unop hg
  refine indicator_not_factor Y (fun _ => ⟨⟨true⟩, ⟨false⟩, by decide⟩) y₀ hi g.unop hx f
    (fun _ => rfl) (fun z => ?_)
  have := ConcreteCategory.congr_hom hg' z
  exact this.symm

/-- ... hence `Set^op` is not an accessible category ... -/
theorem not_isAccessibleCategory_typeOp : ¬ IsAccessibleCategory.{u} (Type u)ᵒᵖ := by
  intro h
  obtain ⟨κ, hκ, hP⟩ := Functor.IsAccessible.exists_cardinal.{u}
    (coyoneda.obj (op (op (ULift.{u} Bool))))
  exact not_isCardinalPresentable_op (x₁ := ULift.up true) (x₂ := ULift.up false) (by simp) κ hP

/-- ... although it has small colimits and a generator (`2 = {0, 1}` is a coseparator of `Set`). -/
theorem typeOp_hasColimits : HasColimits (Type u)ᵒᵖ := inferInstance

theorem typeOp_isSeparator : IsSeparator (op (ULift.{u} Prop)) := by
  rw [isSeparator_op_iff, isCoseparator_def]
  intro A B f g h
  ext a
  have h2 := congrArg ULift.down
    (ConcreteCategory.congr_hom (h (↾fun b => ULift.up (b = f a))) a)
  exact (cast h2 rfl).symm

end SetOp

end Examples

/-! ## Ind-categories -/

section Ind

variable {C : Type u} [Category.{v} C]

/-- 4gynb9uTEE4-17429 (4:50:29) [def] `Ind(C)`: the full subcategory of `Ĉ` of the filtered
colimits of representables (Mathlib `Ind`, `IsIndObject`). -/
abbrev IndCat (C : Type u) [Category.{v} C] : Type (max u (v + 1)) := Ind C

theorem ind_inclusion_fullyFaithful : (Ind.inclusion C).Full ∧ (Ind.inclusion C).Faithful :=
  ⟨inferInstance, inferInstance⟩

/-- 4gynb9uTEE4-17557 (4:52:37) [prop] `Hom((X_i), (Y_j)) = lim_i colim_j Hom(X_i, Y_j)`: first
`Hom(colim_i yX_i, P) ≅ lim_i P(X_i)` ... -/
def indHomIsoLimit {I J : Type v} [SmallCategory I] [SmallCategory J] (D : I ⥤ C) (G : J ⥤ C) :
    (colimit (D ⋙ yoneda) ⟶ colimit (G ⋙ yoneda)) ≅
      limit (D.op ⋙ colimit (G ⋙ yoneda) ⋙ uliftFunctor.{u}) :=
  colimitYonedaHomIsoLimitOp D _

/-- ... and `(colim_j yY_j)(X) ≅ colim_j Hom(X, Y_j)` (colimits of presheaves are pointwise). -/
def indColimitObjIso {J : Type v} [SmallCategory J] (G : J ⥤ C) (X : C) :
    (colimit (G ⋙ yoneda)).obj (op X) ≅ colimit (G ⋙ yoneda ⋙ (evaluation _ _).obj (op X)) :=
  colimitObjIsoColimitCompEvaluation _ _

/-- 4gynb9uTEE4-17684 (4:54:44) [prop] (partial) `C → Ind(C)` is fully faithful and `Ind(C)` has
filtered colimits; the universal property is not in Mathlib. -/
theorem ind_yoneda_filtered :
    (Ind.yoneda (C := C)).Full ∧ (Ind.yoneda (C := C)).Faithful ∧ HasFilteredColimits (Ind C) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- 4gynb9uTEE4-17880 (4:58:00) [prop] (partial) If `C` has finite colimits, `Ind(C)` has small
colimits (Mathlib) ... -/
theorem ind_hasColimits [HasFiniteColimits C] : HasColimits (Ind C) := inferInstance

/-- ... and (for `C` small with finite colimits) `Ind(C)` is the category of left exact presheaves,
i.e. of functors `C^op → Set` commuting with finite limits (Mathlib). -/
theorem isIndObject_iff_lex {C : Type u} [SmallCategory C] [HasFiniteColimits C]
    (A : Cᵒᵖ ⥤ Type u) : IsIndObject A ↔ PreservesFiniteLimits A :=
  isIndObject_iff_preservesFiniteLimits A

/-- 4gynb9uTEE4-18008 (5:00:08) [def] `Ind_π(C)`: the presheaves that are colimits of
representables indexed by an ordered set dominating `π` (`κ = π⁺`-filtered). -/
def IsIndPi (κ : Cardinal.{v}) [Fact κ.IsRegular] (A : Cᵒᵖ ⥤ Type v) : Prop :=
  ∃ (I : Type v) (_ : Preorder I) (_ : IsCardinalFiltered I κ) (F : I ⥤ C),
    Nonempty (A ≅ colimit (F ⋙ yoneda))

/-- `Ind_π(C) ⊂ Ind(C)`. -/
theorem IsIndPi.isIndObject {κ : Cardinal.{v}} [Fact κ.IsRegular] {A : Cᵒᵖ ⥤ Type v}
    (h : IsIndPi κ A) : IsIndObject A := by
  obtain ⟨I, _, _, F, ⟨e⟩⟩ := h
  have := isFiltered_of_isCardinalFiltered I κ
  exact IsIndObject.map e.inv
    (isIndObject_colimit I (F ⋙ yoneda) (fun i => isIndObject_yoneda _))

/-- 4gynb9uTEE4-18331 (5:05:31) [prop] (partial) A retract ("direct summand") of a `κ`-accessible
object is `κ`-accessible (Mathlib). -/
theorem retract_isCardinalPresentable {E : Type*} [Category* E] {X Y : E} (h : Retract Y X)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalPresentable X κ] :
    IsCardinalPresentable Y κ :=
  h.isCardinalPresentable κ

/-- 4gynb9uTEE4-18396 (5:06:36) [def] `C` Karoubian: Mathlib `IsIdempotentComplete`; Karoubian
envelope `Karoubi`. Presheaves do not change when `C` is replaced by its Karoubian envelope. -/
instance type_isIdempotentComplete : IsIdempotentComplete (Type v) :=
  (Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent _).2 (fun _ _ _ => inferInstance)

def presheafKaroubiEquiv : (Cᵒᵖ ⥤ Type v) ≌ (Idempotents.Karoubi Cᵒᵖ ⥤ Type v) :=
  Idempotents.karoubiUniversal _ _

theorem karoubi_isIdempotentComplete : IsIdempotentComplete (Idempotents.Karoubi C) :=
  inferInstance

end Ind

/-! ## Cardinal filtrations -/

section Filtrations

variable {E : Type u} [Category.{v} E]

/-- 4gynb9uTEE4-18524 (5:08:44) [prop] (partial) An ordered set dominating `π` of cardinality
`≤ π` has a largest element ... -/
theorem exists_top_of_dominates {π : Cardinal.{w}} {I : Type w} [Preorder I] (h : Dominates π I)
    (hI : Cardinal.mk I ≤ π) : ∃ t : I, ∀ i, i ≤ t :=
  h.2.2 I id hI

/-- ... so a system indexed by it has colimit its value at the top: `Fil^π ≃ C`. -/
def isColimitOfTop {I : Type w} [Preorder I] {t : I} (ht : ∀ i, i ≤ t) (F : I ⥤ E) :
    IsColimit (coconeOfDiagramTerminal
      (IsTerminal.ofUniqueHom (fun i => homOfLE (ht i)) (fun _ _ => Subsingleton.elim _ _)) F) :=
  colimitOfDiagramTerminal _ F

/-- 4gynb9uTEE4-18589 (5:09:49) [prop] (partial) The objects of `Fil^{π'}` are `π'`-accessible: a
colimit of `κ`-presentable objects indexed by a category with `< κ'` arrows is `κ'`-presentable
for `κ ≤ κ'`. -/
theorem fil_isCardinalPresentable [LocallySmall.{w} E] {I : Type w} [SmallCategory I]
    {κ κ' : Cardinal.{w}} [Fact κ.IsRegular] [Fact κ'.IsRegular] (hκ : κ ≤ κ')
    (hI : HasCardinalLT (Arrow I) κ') {Y : I ⥤ E} [∀ i, IsCardinalPresentable (Y.obj i) κ]
    (c : Cocone Y) (hc : IsColimit c) : IsCardinalPresentable c.pt κ' := by
  have : ∀ i, IsCardinalPresentable (Y.obj i) κ' := fun i => isCardinalPresentable_of_le _ hκ
  exact isCardinalPresentable_of_isColimit c hc κ' hI

/-- 4gynb9uTEE4-18652 (5:10:52) [def] A cardinal filtration of `E` (above `π`): essentially small
full subcategories `Fil^{π'}`, `π' ≥ π`, increasing, stable under colimits indexed by ordered sets
`I` dominating `π` with `card I ≤ π'`, every object of `Fil^{π''}` being such a colimit, indexed by
an `I` dominating `π'` with `card I ≤ π''`, of objects of `Fil^{π'}`. -/
structure CardinalFiltration (π : Cardinal.{w}) (E : Type u) [Category.{v} E] where
  /-- The subcategories. -/
  Fil : Cardinal.{w} → ObjectProperty E
  essSmall : ∀ π', π ≤ π' → ObjectProperty.EssentiallySmall.{w} (Fil π')
  mono : ∀ π' π'', π ≤ π' → π' ≤ π'' → Fil π' ≤ Fil π''
  stable : ∀ π', π ≤ π' → ∀ (I : Type w) [Preorder I], Dominates π I → Cardinal.mk I ≤ π' →
    ∀ (Y : I ⥤ E) (c : Cocone Y), IsColimit c → (∀ i, Fil π' (Y.obj i)) → Fil π' c.pt
  colim : ∀ π' π'', π ≤ π' → π' ≤ π'' → ∀ X, Fil π'' X →
    ∃ (I : Type w) (_ : Preorder I) (_ : Dominates π' I) (_ : Cardinal.mk I ≤ π'')
      (Y : I ⥤ E) (c : Cocone Y) (_ : IsColimit c), (∀ i, Fil π' (Y.obj i)) ∧ Nonempty (c.pt ≅ X)

/-- A property containing, up to isomorphism, a strong generator is a strong generator. -/
theorem isStrongGenerator_of_le_isoClosure {P Q : ObjectProperty E} (hQ : Q.IsStrongGenerator)
    (h : Q ≤ P.isoClosure) : P.IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff] at hQ ⊢
  obtain ⟨hQ₁, hQ₂⟩ := hQ
  refine ⟨fun X Y f g hfg => hQ₁ f g (fun G hG k => ?_),
    fun X Y i _ hi => hQ₂ i (fun G hG f => ?_)⟩
  · obtain ⟨G', hG', ⟨e⟩⟩ := h G hG
    have := hfg G' hG' (e.inv ≫ k)
    simpa using e.hom ≫= this
  · obtain ⟨G', hG', ⟨e⟩⟩ := h G hG
    obtain ⟨f', hf'⟩ := hi G' hG' (e.inv ≫ f)
    refine ⟨e.hom ≫ f', ?_⟩
    simp only at hf' ⊢
    rw [Category.assoc, hf', Iso.hom_inv_id_assoc]

/-- 4gynb9uTEE4-18911 (5:15:11) [thm] (partial: a ⇔ c) For `E` with small colimits, `E` is
`κ`-accessible (locally `κ`-presentable) iff `E_κ` is essentially small and strictly generating
(the inclusion `E_κ → E` is dense). -/
theorem locallyPresentable_iff_dense [HasColimitsOfSize.{w, w} E] [LocallySmall.{w} E]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalLocallyPresentable E κ ↔
      ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable E κ) ∧
        (isCardinalPresentable E κ).ι.IsDense := by
  constructor
  · intro _
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨h₁, h₂⟩
    rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
    obtain ⟨P, hP, hle, hle'⟩ := ObjectProperty.EssentiallySmall.exists_small_le
      (isCardinalPresentable E κ)
    refine ⟨P, hP, isStrongGenerator_of_le_isoClosure
      (Functor.isStrongGenerator_of_isDense (isCardinalPresentable E κ).ι) ?_, hle⟩
    rintro _ ⟨x⟩
    exact hle' _ x.2

/-- 4gynb9uTEE4-19371 (5:22:51) [prop] (false as stated: "limits" must be "colimits")
Counterexample: in `E = Set`, `C = {1}` is made of finitely presentable objects, is strictly
generating and stable under all limits, but `Ind(C) → Set` is not an equivalence: a filtered
colimit of one-point sets is never empty. -/
theorem filtered_colimit_of_punit_nonempty {I : Type u} [Category I] [IsFiltered I]
    (F : I ⥤ Type u) (hF : ∀ i, Nonempty (F.obj i)) (c : Cocone F) : Nonempty c.pt :=
  ⟨c.ι.app (IsFiltered.nonempty.some) (hF _).some⟩

theorem empty_not_filtered_colimit_of_punit {I : Type u} [Category I] [IsFiltered I]
    (F : I ⥤ Type u) (hF : ∀ i, Nonempty (F.obj i)) (c : Cocone F) :
    IsEmpty (c.pt ≅ (PEmpty : Type u)) :=
  ⟨fun e => (e.hom (filtered_colimit_of_punit_nonempty F hF c).some).elim⟩

/-- ... while every limit of one-point sets is a one-point set. -/
theorem limit_of_punit_unique {K : Type u} [SmallCategory K] (F : K ⥤ Type u)
    (hF : ∀ k, Unique (F.obj k)) : Nonempty (Unique (limit F)) := by
  let s : F.sections := ⟨fun k => (hF k).default, fun _ => (hF _).uniq _⟩
  refine ⟨⟨⟨(Types.limitEquivSections F).symm s⟩, fun x => ?_⟩⟩
  apply (Types.limitEquivSections F).injective
  ext k
  exact ((hF k).uniq _).trans ((hF k).uniq _).symm

/-- 4gynb9uTEE4-19433 (5:23:53) [prop] (false as stated; corrected: a colimit is the filtered
colimit of the partial colimits) Special case of the corrected form: a set `X = ∐_{x ∈ X} 1` is
the colimit, along the `κ`-filtered ordered set of its subsets of cardinality `< κ`, of these
subsets (Mathlib). -/
def isColimit_partialCoproducts (X : Type u) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) :
    IsColimit (HasCardinalLT.Set.cocone X κ) :=
  HasCardinalLT.Set.isColimitCocone X κ hκ

/-- 4gynb9uTEE4-19702 (5:28:22) [prop] A locally `κ`-presentable category is locally
`κ'`-presentable for every regular `κ' ≥ κ` (Mathlib). -/
theorem locallyPresentable_of_le {κ κ' : Cardinal.{w}}
    [Fact κ.IsRegular] [Fact κ'.IsRegular] [IsCardinalLocallyPresentable E κ] (h : κ ≤ κ') : IsCardinalLocallyPresentable E κ' :=
  IsCardinalLocallyPresentable.of_le E h

/-- 4gynb9uTEE4-19912 (5:31:52) [cex] A functor from the point commutes with all colimits indexed
by connected (e.g. filtered) categories, and the point is `κ`-presentable; but its image `X` need
not be: take `X` a set of cardinality `κ`. -/
theorem point_isCardinalPresentable (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    IsCardinalPresentable (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}) κ := by
  let e : coyoneda.obj (op (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1})) ≅
      (Functor.const _).obj PUnit.{u + 1} :=
    NatIso.ofComponents (fun X => Equiv.toIso
      { toFun := fun _ => PUnit.unit
        invFun := fun _ => eqToHom (Subsingleton.elim _ _)
        left_inv := fun _ => Subsingleton.elim (α := Discrete.mk PUnit.unit ⟶ X) _ _
        right_inv := fun _ => rfl })
  exact Functor.isCardinalAccessible_of_natIso e.symm κ

theorem not_isCardinalPresentable_card (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    ¬ IsCardinalPresentable (κ.out) κ := by
  rw [Types.isCardinalPresentable_iff, hasCardinalLT_iff_cardinal_mk_lt]
  simp

/-- 4gynb9uTEE4-19978 (5:32:58) [prop] (partial) Uniformization: an accessible functor between
accessible categories is `κ`-accessible and sends `κ`-presentable objects to `κ`-presentable
objects for some `κ` (Mathlib), so it restricts to `f : E_κ → E'_κ`. -/
theorem uniformization {E' : Type*} [Category* E'] [IsAccessibleCategory.{w} E]
    [IsAccessibleCategory.{w} E'] (F : E ⥤ E') [Functor.IsAccessible.{w} F] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory E κ ∧ IsCardinalAccessibleCategory E' κ ∧
        F.IsCardinalAccessible κ ∧ F.PreservesCardinalPresentable κ :=
  IsCardinalAccessibleCategory.uniformization F

end Filtrations

end

end Buffalo.Topos.Part06
