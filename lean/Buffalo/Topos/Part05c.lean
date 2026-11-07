import Buffalo.Topos.Part05a

/-!
# Buffalo, topos theory, part 5c: exactness properties, envelopes, categories of fractions (2 July 1973)

Entries of `docs/buffalo-topos/index.tex` lines 767–811 (video `4gynb9uTEE4`, 1:57:30–3:31:07):
representability of theories, exactness properties (groupoids, preorders, discrete categories),
limits in `T(C)`, change of `Δ`, the envelope `Ĵ` and the saturated categories of fractions
`C[Σ'⁻¹]` in `Δ` = categories with small limits. The status of each entry is in
`docs/buffalo-topos/lean/Part05.json`.

The saturation `Σ'` of a class `Σ` of arrows is formalised literally: the arrows inverted by every
limit-preserving functor inverting `Σ` (`saturation`). Its properties (isomorphisms, composition,
two out of three, base change, diagonals, infinite fibre products, right calculus of fractions)
are proved for an arbitrary category with the relevant limits.
-/

universe w v u v' u' w' v'' u''

open CategoryTheory Limits Opposite

namespace Buffalo.Topos.Part05

noncomputable section

/-! ## Representability of theories -/

/-- 4gynb9uTEE4-8276 (2:17:56) [prop, partial] A representable `Hom(R, -)` commutes with limits
(1-categorical shadow of `T(lim Cᵢ) ≃ lim T(Cᵢ)`). -/
theorem coyoneda_preservesLimits {C : Type u} [Category.{v} C] (R : C) :
    PreservesLimits (coyoneda.obj (op R)) :=
  inferInstance

/-- 4gynb9uTEE4-8410 (2:20:10) [prop] `Hom(R, -)` sends faithful functors to faithful functors... -/
instance whiskeringRight_faithful {R : Type u} [Category.{v} R] {C : Type u'} [Category.{v'} C]
    {C' : Type u''} [Category.{v''} C'] (F : C ⥤ C') [F.Faithful] :
    ((Functor.whiskeringRight R C C').obj F).Faithful :=
  inferInstance

/-- ... and fully faithful ones to fully faithful ones. -/
def whiskeringRight_fullyFaithful {R : Type u} [Category.{v} R] {C : Type u'} [Category.{v'} C]
    {C' : Type u''} [Category.{v''} C'] {F : C ⥤ C'} (hF : F.FullyFaithful) :
    ((Functor.whiskeringRight R C C').obj F).FullyFaithful :=
  hF.whiskeringRight R

/-! ## Exactness properties -/

/-- 4gynb9uTEE4-8607 (2:23:27) [def] An exactness property given by `(R, Σ)`: the localization
`R → R[Σ⁻¹]` identifies `Hom(R[Σ⁻¹], C)` with the functors `R → C` inverting `Σ`
(`Localization.functorEquivalence`). -/
def exactness_equivalence {R : Type u} [Category.{v} R] {R' : Type u'} [Category.{v'} R']
    (L : R ⥤ R') (W : MorphismProperty R) [L.IsLocalization W] (C : Type u'') [Category.{v''} C] :
    (R' ⥤ C) ≌ W.FunctorsInverting C :=
  Localization.functorEquivalence L W C

/-- 4gynb9uTEE4-8738 (2:25:38) [def] Generalized exactness property given by `u : R → R'`:
`Hom(R', C) → Hom(R, C)` is an equivalence (resp. fully faithful, faithful). -/
def SatisfiesExactness {R : Type u} [Category.{v} R] {R' : Type u'} [Category.{v'} R']
    (u : R ⥤ R') (C : Type u'') [Category.{v''} C] : Prop :=
  ((Functor.whiskeringLeft R R' C).obj u).IsEquivalence

/-- The « fully faithful » variant. -/
def SatisfiesExactnessFF {R : Type u} [Category.{v} R] {R' : Type u'} [Category.{v'} R']
    (u : R ⥤ R') (C : Type u'') [Category.{v''} C] : Prop :=
  ((Functor.whiskeringLeft R R' C).obj u).Full ∧ ((Functor.whiskeringLeft R R' C).obj u).Faithful

/-- 4gynb9uTEE4-8802 (2:26:42) [prop, partial] Stability under products: a functor into a
product inverts an arrow iff each component does. -/
theorem isIso_map_pi_iff {R : Type u} [Category.{v} R] {I : Type w} (C : I → Type u')
    [∀ i, Category.{v'} (C i)] (F : R ⥤ ∀ i, C i) {X Y : R} (s : X ⟶ Y) :
    IsIso (F.map s) ↔ ∀ i, IsIso ((F ⋙ Pi.eval C i).map s) := by
  constructor
  · intro h i
    exact ⟨⟨(inv (F.map s)) i, congr_fun (IsIso.hom_inv_id (F.map s)) i,
      congr_fun (IsIso.inv_hom_id (F.map s)) i⟩⟩
  · intro h
    exact ⟨⟨fun i => (h i).out.choose, funext fun i => (h i).out.choose_spec.1,
      funext fun i => (h i).out.choose_spec.2⟩⟩

/-- 4gynb9uTEE4-8931 (2:28:51) [ex] Requiring the arrow of `{0 → 1}` to be inverted by every functor
defines the groupoids. -/
theorem groupoid_iff (C : Type u) [Category.{v} C] :
    (∀ F : Fin 2 ⥤ C, IsIso (F.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)))) ↔
      ∀ (X Y : C) (f : X ⟶ Y), IsIso f := by
  constructor
  · intro h X Y f
    simpa using h (ComposableArrows.mk₁ f)
  · intro h F
    exact h _ _ _

/-- 4gynb9uTEE4-8998 (2:29:58) [ex] Equalizing the two arrows of `{0 ⇉ 1}` defines the preordered
categories (all Hom-sets subsingletons). -/
theorem preordered_iff (C : Type u) [Category.{v} C] :
    (∀ F : WalkingParallelPair ⥤ C,
      F.map WalkingParallelPairHom.left = F.map WalkingParallelPairHom.right) ↔
      ∀ X Y : C, Subsingleton (X ⟶ Y) := by
  constructor
  · intro h X Y
    exact ⟨fun f g => by simpa using h (parallelPair f g)⟩
  · intro h F
    exact (h _ _).elim _ _

/-- ... a preordered category is equivalent to an ordered set, its thin skeleton
(`ThinSkeleton.equivalence`). -/
def thin_equivalence (C : Type u) [Category.{v} C] [Quiver.IsThin C] : ThinSkeleton C ≌ C :=
  ThinSkeleton.equivalence C

/-- 4gynb9uTEE4-9126 (2:32:06) [ex] Both conditions together: the thin skeleton is discrete
(`≤` is equality), so the category is essentially discrete, equivalent to a set. -/
theorem thinSkeleton_discrete (C : Type u) [Category.{v} C] [Quiver.IsThin C]
    (h : ∀ (X Y : C) (f : X ⟶ Y), IsIso f) (a b : ThinSkeleton C) (hab : a ≤ b) : a = b := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  rename_i X Y
  obtain ⟨f⟩ := hab
  exact Quotient.sound ⟨@asIso _ _ _ _ f (h _ _ f)⟩

/-- 4gynb9uTEE4-9190 (2:33:10) [ex] For `Δ = Cat`, problem two is solved by the Gabriel–Zisman
category of fractions (`MorphismProperty.Localization`). -/
theorem gabrielZisman {C : Type u} [Category.{v} C] (W : MorphismProperty C) :
    W.Q.IsLocalization W :=
  inferInstance

/-- 4gynb9uTEE4-9256 (2:34:16) [ex, partial] For groupoids, the envelope of `I` is `I[I⁻¹]`: every
functor from `I` to a groupoid factors through the localization at all arrows. -/
def groupoid_lift {I : Type u} [Category.{v} I] {G : Type u'} [Groupoid.{v'} G] (F : I ⥤ G) :
    (⊤ : MorphismProperty I).Localization ⥤ G :=
  Localization.Construction.lift F (fun _ _ _ _ => inferInstance)

theorem groupoid_lift_fac {I : Type u} [Category.{v} I] {G : Type u'} [Groupoid.{v'} G]
    (F : I ⥤ G) : (⊤ : MorphismProperty I).Q ⋙ groupoid_lift F = F :=
  Localization.Construction.fac F _

/-- The preorder envelope of a category: same objects, `x ≤ y` iff there is an arrow `x → y`. -/
structure PreEnv (I : Type u) where
  /-- the underlying object -/
  obj : I

instance (I : Type u) [Category.{v} I] : Preorder (PreEnv I) where
  le a b := Nonempty (a.obj ⟶ b.obj)
  le_refl a := ⟨𝟙 _⟩
  le_trans _ _ _ := fun ⟨f⟩ ⟨g⟩ => ⟨f ≫ g⟩

/-- 4gynb9uTEE4-9381 (2:36:21) [ex] For preorders, the envelope of `I` is `Ob I` preordered by the
existence of arrows: `I → PreEnv I` is a functor, and every functor from `I` to a preorder is
monotone for this preorder. (Mathlib's convention: an arrow `x → y` means `x ≤ y`.) -/
def toPreEnv (I : Type u) [Category.{v} I] : I ⥤ PreEnv I where
  obj x := ⟨x⟩
  map f := homOfLE ⟨f⟩

theorem preEnv_universal {I : Type u} [Category.{v} I] {P : Type u'} [Preorder P] (F : I ⥤ P) :
    Monotone (fun a : PreEnv I => F.obj a.obj) :=
  fun _ _ ⟨f⟩ => (F.map f).le

/-- 4gynb9uTEE4-9444 (2:37:24) [ex] Making relations `xᵢ ≤ yᵢ` invertible: the preorder generated
by `≤` and the `yᵢ ≤ xᵢ` has the universal property. -/
def genRel {P : Type u} [Preorder P] {ι : Type w} (x y : ι → P) : P → P → Prop :=
  Relation.ReflTransGen (fun a b => a ≤ b ∨ ∃ i, a = y i ∧ b = x i)

theorem genRel_universal {P : Type u} [Preorder P] {ι : Type w} (x y : ι → P) {Q : Type u'}
    [Preorder Q] (f : P → Q) (hf : Monotone f) (hxy : ∀ i, f (y i) ≤ f (x i)) {a b : P}
    (h : genRel x y a b) : f a ≤ f b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih =>
    rcases hbc with hbc | ⟨i, rfl, rfl⟩
    · exact ih.trans (hf hbc)
    · exact ih.trans (hxy i)

/-- 4gynb9uTEE4-9510 (2:38:30) [ex] For discrete categories the envelope of `I` is `π₀(I)`:
functors from `I` to a discrete category are functions on the connected components
(`ConnectedComponents.typeToCatHomEquiv`). -/
def discrete_envelope (I : Type u) [Category.{v} I] (X : Type u') :
    (ConnectedComponents I → X) ≃ (I ⥤ Discrete X) :=
  ConnectedComponents.typeToCatHomEquiv I X

/-! ## Limits in `T(C)` -/

/-- 4gynb9uTEE4-9714 (2:41:54) [prop, partial] Limits of functors `R → C` exist and are computed
argumentwise (for `D'' = ∅`, 4gynb9uTEE4-10103, the limit of `D'`-continuous functors is again
`D'`-continuous, limits commuting with limits). -/
theorem functor_hasLimitsOfShape {R : Type u} [Category.{v} R] {C : Type u'} [Category.{v'} C]
    (K : Type w) [Category.{w'} K] [HasLimitsOfShape K C] : HasLimitsOfShape K (R ⥤ C) :=
  inferInstance

/-- 4gynb9uTEE4-9978 (2:46:18) [prop, partial] The evaluation `r_C : T(C) → C` commutes with these
limits. -/
theorem evaluation_preserves {R : Type u} [Category.{v} R] {C : Type u'} [Category.{v'} C]
    (K : Type w) [Category.{w'} K] [HasLimitsOfShape K C] (r : R) :
    PreservesLimitsOfShape K ((evaluation R C).obj r) :=
  inferInstance

/-- 4gynb9uTEE4-9915 (2:45:15) [prop, partial] `T(C) → T(C')` commutes with these limits if
`C → C'` does. -/
theorem whiskeringRight_preserves {R : Type u} [Category.{v} R] {C : Type u'} [Category.{v'} C]
    {C' : Type u''} [Category.{v''} C'] (K : Type w) [Category.{w'} K] [HasLimitsOfShape K C]
    (G : C ⥤ C') [PreservesLimitsOfShape K G] :
    PreservesLimitsOfShape K ((Functor.whiskeringRight R C C').obj G) :=
  inferInstance

/-! ## Torsors: no limits at all -/

section Torsors

variable (G : Type u) [Group G] [Nontrivial G]

/-- 4gynb9uTEE4-10040 (2:47:20) [ex] The category of torsors under `G ≠ 1` (equivalent to the
one-object groupoid `SingleObj G`, all torsors being isomorphic with automorphisms `G`) has no
terminal object... -/
theorem torsor_no_terminal (X : SingleObj G) : IsTerminal X → False := by
  intro h
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  exact ha (h.hom_ext (show X ⟶ X from a) (show X ⟶ X from (1 : G)))

/-- ... no initial object... -/
theorem torsor_no_initial (X : SingleObj G) : IsInitial X → False := by
  intro h
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  exact ha (h.hom_ext (show X ⟶ X from a) (show X ⟶ X from (1 : G)))

/-- ... no products (of the object with itself)... -/
theorem torsor_no_product {X : SingleObj G} (c : BinaryFan X X) : IsLimit c → False := by
  intro hc
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  obtain ⟨l₁, h₁, h₁'⟩ := BinaryFan.IsLimit.lift' hc (show X ⟶ X from (1 : G)) (show X ⟶ X from (1 : G))
  obtain ⟨l₂, h₂, h₂'⟩ := BinaryFan.IsLimit.lift' hc (show X ⟶ X from (1 : G)) (show X ⟶ X from a)
  rw [SingleObj.comp_as_mul] at h₁ h₁' h₂ h₂'
  have : l₁ = l₂ := by
    have e : (c.fst : G) * l₁ = c.fst * l₂ := by rw [h₁, h₂]
    exact mul_left_cancel e
  apply ha
  rw [← h₂', ← this, h₁']

/-- ... and no coproducts. -/
theorem torsor_no_coproduct {X : SingleObj G} (c : BinaryCofan X X) : IsColimit c → False := by
  intro hc
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  obtain ⟨l₁, h₁, h₁'⟩ := BinaryCofan.IsColimit.desc' hc (show X ⟶ X from (1 : G)) (show X ⟶ X from (1 : G))
  obtain ⟨l₂, h₂, h₂'⟩ := BinaryCofan.IsColimit.desc' hc (show X ⟶ X from (1 : G)) (show X ⟶ X from a)
  rw [SingleObj.comp_as_mul] at h₁ h₁' h₂ h₂'
  have : l₁ = l₂ := by
    have e : l₁ * (c.inl : G) = l₂ * c.inl := by rw [h₁, h₂]
    exact mul_right_cancel e
  apply ha
  rw [← h₂', ← this, h₁']

end Torsors

/-! ## Envelopes -/

/-- 4gynb9uTEE4-11448 (3:10:48) [prop] `J → Ĵ` is the envelope under colimits: a cocontinuous
functor on `Ĵ` is determined by its restriction to `J`, being the left Kan extension of it along
Yoneda (`Presheaf.uniqueExtensionAlongULiftYoneda`). -/
def yoneda_extension_unique {J : Type u} [SmallCategory J] {ℰ : Type u'} [Category.{u} ℰ]
    (A : J ⥤ ℰ) (L : (Jᵒᵖ ⥤ Type u) ⥤ ℰ) (e : A ≅ uliftYoneda.{u} ⋙ L)
    [PreservesColimitsOfSize.{u, u} L] [HasColimitsOfSize.{u, u} ℰ] :
    L ≅ uliftYoneda.{u}.leftKanExtension A :=
  Presheaf.uniqueExtensionAlongULiftYoneda L e

/-! ## The saturation of a class of arrows -/

section Saturation

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

/-- The saturation `Σ'` of `Σ = W` in `Δ` = categories with small limits (here: in the universes
of `C`): the arrows inverted by every limit-preserving functor inverting `W`. -/
def saturation : MorphismProperty C := fun _ _ u =>
  ∀ (D : Type u) [Category.{v} D] (F : C ⥤ D), PreservesLimitsOfSize.{v, v} F →
    W.IsInvertedBy F → IsIso (F.map u)

/-- 4gynb9uTEE4-12093 (3:21:33) [prop] `Σ'` contains `Σ`... -/
theorem le_saturation : W ≤ saturation W := fun _ _ _ hu _ _ _ _ hF => hF _ hu

/-- ... the isomorphisms... -/
theorem saturation_of_isIso {X Y : C} (u : X ⟶ Y) [IsIso u] : saturation W u :=
  fun _ _ _ _ _ => inferInstance

/-- ... is stable under composition... -/
theorem saturation_comp {X Y Z : C} {u : X ⟶ Y} {v : Y ⟶ Z} (hu : saturation W u)
    (hv : saturation W v) : saturation W (u ≫ v) := by
  intro D _ F hF hW
  have := hu D F hF hW
  have := hv D F hF hW
  rw [F.map_comp]
  infer_instance

/-- ... has the two-out-of-three property (the two remaining cases)... -/
theorem saturation_of_comp_left {X Y Z : C} {u : X ⟶ Y} {v : Y ⟶ Z}
    (hu : saturation W u) (huv : saturation W (u ≫ v)) :
    saturation W v := by
  intro D _ F hF hW
  have := hu D F hF hW
  have : IsIso (F.map u ≫ F.map v) := by rw [← F.map_comp]; exact huv D F hF hW
  exact IsIso.of_isIso_comp_left (F.map u) (F.map v)

theorem saturation_of_comp_right {X Y Z : C} {u : X ⟶ Y} {v : Y ⟶ Z}
    (hv : saturation W v) (huv : saturation W (u ≫ v)) :
    saturation W u := by
  intro D _ F hF hW
  have := hv D F hF hW
  have : IsIso (F.map u ≫ F.map v) := by rw [← F.map_comp]; exact huv D F hF hW
  exact IsIso.of_isIso_comp_right (F.map u) (F.map v)

/-- ... and is stable under base change. -/
theorem saturation_baseChange {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (hg : saturation W g) : saturation W fst := by
  intro D _ F hF hW
  have := hg D F hF hW
  have := PreservesLimitsOfSize.preservesFiniteLimits F
  exact (h.map F).isIso_fst_of_isIso

/-- 4gynb9uTEE4-12219 (3:23:39) [prop] If `u : X → Y` is in `Σ'`, so is the diagonal
`X → X ×_Y X` (its composite with the first projection, a base change of `u`, is `𝟙`). -/
theorem saturation_diagonal {X Y : C} (u : X ⟶ Y) [HasPullback u u]
    (hu : saturation W u) : saturation W (pullback.diagonal u) := by
  have hfst : saturation W (pullback.fst u u) :=
    saturation_baseChange W (IsPullback.of_hasPullback u u) hu
  refine saturation_of_comp_right W hfst ?_
  rw [pullback.diagonal_fst]
  exact saturation_of_isIso W _

/-- 4gynb9uTEE4-12539 (3:28:59) [prop] `Σ'` is stable under arbitrary fibre products: if the
`uᵢ : Xᵢ → Y` are in `Σ'`, so is `∏_Y Xᵢ → Y`. -/
theorem saturation_widePullback {ι : Type v} {Y : C} (X : ι → C) (u : ∀ i, X i ⟶ Y)
    [HasWidePullback Y X u] (hu : ∀ i, saturation W (u i)) :
    saturation W (WidePullback.base u) := by
  intro D _ F hF hW
  have hi : ∀ i, IsIso (F.map (u i)) := fun i => hu i D F hF hW
  have hc := isLimitOfPreserves F (limit.isLimit (WidePullbackShape.wideCospan Y X u))
  let s : Cone (WidePullbackShape.wideCospan Y X u ⋙ F) :=
    WidePullbackShape.mkCone (𝟙 (F.obj Y)) (fun i => inv (F.map (u i))) (fun i => by simp)
  refine ⟨⟨hc.lift s, ?_, ?_⟩⟩
  · apply hc.hom_ext
    rintro (_ | i)
    · simp only [Category.assoc, hc.fac, Category.id_comp]
      dsimp [s, WidePullbackShape.mkCone]
      rw [Category.comp_id]
    · simp only [Category.assoc, hc.fac, Category.id_comp]
      dsimp [s, WidePullbackShape.mkCone]
      rw [IsIso.comp_inv_eq, ← F.map_comp]
      congr 1
      exact (WidePullback.π_arrow u i).symm
  · exact hc.fac s none

/-- 4gynb9uTEE4-12284 (3:24:44) [prop] `Σ'` admits a (right) calculus of fractions when `C` has
pullbacks and equalizers: spans are completed by fibre products, and two arrows equalized by
`s ∈ Σ'` are equalized by their kernel, which is in `Σ'`; so (Mathlib) `Hom(X, Y)` in
`C[Σ'⁻¹]` is the colimit of the `Hom_C(X', Y)` over the `X' → X` in `Σ'`. -/
theorem saturation_hasRightCalculusOfFractions [HasPullbacks C] [HasEqualizers C] :
    (saturation W).HasRightCalculusOfFractions where
  id_mem X := saturation_of_isIso W (𝟙 X)
  comp_mem _ _ hu hv := saturation_comp W hu hv
  exists_rightFraction X Y φ :=
    ⟨⟨pullback.fst φ.f φ.s,
      saturation_baseChange W (IsPullback.of_hasPullback φ.f φ.s) φ.hs, pullback.snd φ.f φ.s⟩,
      pullback.condition⟩
  ext X Y Y' f₁ f₂ s hs hf := by
    refine ⟨equalizer f₁ f₂, equalizer.ι f₁ f₂, ?_, equalizer.condition f₁ f₂⟩
    intro D _ F hF hW
    have := hs D F hF hW
    have := PreservesLimitsOfSize.preservesFiniteLimits F
    rw [← map_eq_iff_isIso_map_ι]
    rw [← cancel_mono (F.map s), ← F.map_comp, ← F.map_comp, hf]

/-- 4gynb9uTEE4-12473 (3:27:53) [prop, partial] With a class stable under finite products, the
localization has finite products and the localization functor preserves them
(`Localization.hasFiniteProducts`). -/
theorem localization_hasFiniteProducts [HasFiniteProducts C] [W.ContainsIdentities]
    [W.IsStableUnderFiniteProducts] :
    HasFiniteProducts W.Localization :=
  inferInstance

end Saturation

end

end Buffalo.Topos.Part05
