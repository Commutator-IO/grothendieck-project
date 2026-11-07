import Buffalo.Topos.Part02b
import Buffalo.Topos.Part02c

/-!
# Buffalo, topos theory, part 2d: definitions and first examples of topoi (25 May 1973)

Entries of `docs/buffalo-topos/index.tex` from « Points and morphisms of sober spaces » (the
uniqueness statement 8:29:59) to « Basic examples of topoi » (video `URU5jgTvjhU`,
8:29:59–9:25:54). The status of each entry is in `docs/buffalo-topos/lean/Part02.json`.

Mathlib has no notion of Grothendieck topos as such; the definitions below state Giraud's axioms
with Mathlib's notions, and the propositions are proved for the topoi `Sh(X)`, or for any category
having the properties used.
-/

universe v u

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace Buffalo.Topos.Part02

noncomputable section

open Buffalo.Topos.Part01

variable {X : TopCat.{u}}

/-! ## Functors commuting with colimits -/

/-- The open sets of `X` are subcanonical: the presheaves `𝒪(-, U)` are sheaves. -/
instance opens_subcanonical : (Opens.grothendieckTopology X).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ fun U =>
    (isSheaf_iff_isSheaf_of_type _ _).1 (yoneda_isSheaf U)

/-- URU5jgTvjhU-30599 (8:29:59) [prop] Two functors on `Sh(Y)` that commute with colimits and are
isomorphic on the generating subcategory `𝒪(Y)` (the representable sheaves) are isomorphic. -/
theorem iso_of_iso_on_opens {E : Type*} [Category.{u} E]
    (L₁ L₂ : Sheaf (Opens.grothendieckTopology X) (Type u) ⥤ E)
    [PreservesColimitsOfSize.{u, u} L₁] [PreservesColimitsOfSize.{u, u} L₂]
    (e : (Opens.grothendieckTopology X).yoneda ⋙ L₁ ≅ (Opens.grothendieckTopology X).yoneda ⋙ L₂) :
    Nonempty (L₁ ≅ L₂) := by
  let J := Opens.grothendieckTopology X
  let a := presheafToSheaf J (Type u)
  have : PreservesColimitsOfSize.{u, u} a :=
    (sheafificationAdjunction J (Type u)).leftAdjoint_preservesColimits
  let k : uliftYoneda.{u} ⋙ a ≅ J.yoneda :=
    Functor.isoWhiskerRight uliftYonedaIsoYoneda a ≪≫
      Functor.isoWhiskerRight (GrothendieckTopology.yonedaCompSheafToPresheaf J).symm a ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft J.yoneda (asIso (sheafificationAdjunction J (Type u)).counit) ≪≫
      J.yoneda.rightUnitor
  let e₂ : uliftYoneda.{u} ⋙ a ⋙ L₁ ≅ uliftYoneda.{u} ⋙ a ⋙ L₂ :=
    Functor.isoWhiskerRight k L₁ ≪≫ e ≪≫ (Functor.isoWhiskerRight k L₂).symm
  let M : a ⋙ L₁ ≅ a ⋙ L₂ :=
    Presheaf.uniqueExtensionAlongULiftYoneda.{u} (a ⋙ L₁) (Iso.refl _) ≪≫
      (Presheaf.uniqueExtensionAlongULiftYoneda.{u} (a ⋙ L₂) e₂).symm
  let c := asIso (sheafificationAdjunction J (Type u)).counit
  exact ⟨L₁.leftUnitor.symm ≪≫ Functor.isoWhiskerRight c.symm L₁ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J (Type u)) M ≪≫
    Functor.isoWhiskerRight c L₂ ≪≫ L₂.leftUnitor⟩

/-! ## Definitions of a topos -/

section Defs

variable {C : Type u} [Category.{v} C]

/-- URU5jgTvjhU-31132 (8:38:52) [def] `(Gᵢ)` is generating if `X ↦ Hom(-, X)|_C` is faithful:
two arrows agreeing after every `Gᵢ → E` are equal. -/
def IsSeparatingFamily {ι : Type*} (G : ι → C) : Prop :=
  ∀ ⦃E F : C⦄ (f g : E ⟶ F), (∀ i (a : G i ⟶ E), a ≫ f = a ≫ g) → f = g

/-- The functor `E → Ĉ`, `X ↦ Hom(-, X)|_C`, for the full subcategory `C` on the `Gᵢ`. -/
abbrev restrictedYonedaFamily {ι : Type*} (G : ι → C) :
    C ⥤ (ObjectProperty.ofObj G).FullSubcategoryᵒᵖ ⥤ Type v :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (ObjectProperty.ofObj G).ι.op

/-- URU5jgTvjhU-31132 (8:38:52) [def] The family is generating iff `E → Ĉ` is faithful. -/
theorem isSeparatingFamily_iff_faithful {ι : Type*} (G : ι → C) :
    IsSeparatingFamily G ↔ (restrictedYonedaFamily G).Faithful := by
  constructor
  · intro h
    refine ⟨fun {E F} f g hfg => h f g fun i a => ?_⟩
    have := congrArg (fun φ => φ.app (op ⟨G i, ⟨i⟩⟩) a) hfg
    exact this
  · intro h E F f g hfg
    apply (restrictedYonedaFamily G).map_injective
    ext ⟨⟨_, ⟨i⟩⟩⟩ a
    exact hfg i a

/-- URU5jgTvjhU-31258 (8:40:58) [prop] With equalizers, « conservative on monomorphisms » (the SGA 4
definition, `Part01.IsGeneratingFamily`) implies « faithful ». -/
theorem IsGeneratingFamily.isSeparatingFamily [HasEqualizers C] {ι : Type*} {G : ι → C}
    (hG : IsGeneratingFamily G) : IsSeparatingFamily G := by
  intro E F f g h
  have : IsIso (equalizer.ι f g) := hG (equalizer.ι f g) fun i =>
    ⟨fun a b hab => (cancel_mono _).1 hab, fun a => ⟨equalizer.lift a (h i a), by simp⟩⟩
  exact eq_of_epi_equalizer

/-- URU5jgTvjhU-31258 (8:40:58) [prop] In a balanced category (such as a topos), « faithful »
implies « conservative » (`Part01.IsConservativeFamily`). -/
theorem IsSeparatingFamily.isConservativeFamily [Balanced C] {ι : Type*} {G : ι → C}
    (hG : IsSeparatingFamily G) : IsConservativeFamily G := by
  intro E F f hf
  have : Mono f := ⟨fun {W} a b hab => hG a b fun i c => (hf i).1 (by simp [hab])⟩
  have : Epi f := ⟨fun {T} u w huw => hG u w fun i c => by
    obtain ⟨d, rfl⟩ := (hf i).2 c
    simp [huw]⟩
  exact isIso_of_mono_of_epi f

/-- URU5jgTvjhU-31066 (8:37:46) [def] A topos, first (provisional) form: arbitrary colimits, finite
limits, and a small generating family. -/
structure IsToposFirstForm (C : Type u) [Category.{v} C] : Prop where
  hasColimits : HasColimitsOfSize.{v, v} C
  hasFiniteLimits : HasFiniteLimits C
  generator : ∃ (ι : Type v) (G : ι → C), IsSeparatingFamily G

/-- URU5jgTvjhU-31573 (8:46:13) [def] A coproduct `∐ Xᵢ` is universal if it is stable under every
base change `X' → ∐ Xᵢ` (Mathlib's `IsUniversalColimit`). -/
def IsUniversalCoproduct {ι : Type*} (Xs : ι → C) [HasCoproduct Xs] : Prop :=
  IsUniversalColimit (colimit.cocone (Discrete.functor Xs))

/-- URU5jgTvjhU-31704 (8:48:24) [def] It is disjoint if the `Xᵢ → ∐ Xᵢ` are monomorphisms and
`Xᵢ ×_X Xⱼ` is initial for `i ≠ j`. -/
def IsDisjointCoproduct [HasPullbacks C] {ι : Type*} (Xs : ι → C) [HasCoproduct Xs] : Prop :=
  (∀ i, Mono (Sigma.ι Xs i)) ∧
    ∀ i j, i ≠ j → Nonempty (IsInitial (pullback (Sigma.ι Xs i) (Sigma.ι Xs j)))

/-- URU5jgTvjhU-31896 (8:51:36) [def] An equivalence relation `R ⇉ X`: `R(Z) → X(Z) × X(Z)` is, for
every `Z`, the graph of an equivalence relation. -/
structure IsEquivRel {R Y : C} (r₁ r₂ : R ⟶ Y) : Prop where
  mono : ∀ {Z : C} (a b : Z ⟶ R), a ≫ r₁ = b ≫ r₁ → a ≫ r₂ = b ≫ r₂ → a = b
  refl : ∀ {Z : C} (y : Z ⟶ Y), ∃ a : Z ⟶ R, a ≫ r₁ = y ∧ a ≫ r₂ = y
  symm : ∀ {Z : C} (a : Z ⟶ R), ∃ b : Z ⟶ R, b ≫ r₁ = a ≫ r₂ ∧ b ≫ r₂ = a ≫ r₁
  trans : ∀ {Z : C} (a b : Z ⟶ R), a ≫ r₂ = b ≫ r₁ →
    ∃ c : Z ⟶ R, c ≫ r₁ = a ≫ r₁ ∧ c ≫ r₂ = b ≫ r₂

/-- URU5jgTvjhU-31896 (8:51:36) [def] It is effective if `R ≃ X ×_{X/R} X`. -/
def IsEffectiveEquivRel {R Y : C} (r₁ r₂ : R ⟶ Y) [HasCoequalizer r₁ r₂] : Prop :=
  IsEquivRel r₁ r₂ ∧ Nonempty (IsLimit (PullbackCone.mk r₁ r₂ (coequalizer.condition r₁ r₂)))

/-- URU5jgTvjhU-31962 (8:52:42) [def] It is universal if passage to the quotient commutes with base
changes `Y' → X/R` (the coequalizer is a universal colimit; `X → X/R` is then a universal
epimorphism). -/
def IsUniversalQuotient {R Y : C} (r₁ r₂ : R ⟶ Y) [HasCoequalizer r₁ r₂] : Prop :=
  IsUniversalColimit (colimit.cocone (parallelPair r₁ r₂))

/-- URU5jgTvjhU-31446 (8:44:06) [def] A topos (Giraud): (a) finite limits, (b) universal disjoint
small coproducts, (c) universal effective equivalence relations, (d) a small generating family. -/
structure IsGiraudTopos (C : Type u) [Category.{v} C] : Prop where
  finiteLimits : HasFiniteLimits C
  coproducts : HasCoproducts.{v} C
  coproducts_universal_disjoint : ∀ (ι : Type v) (Xs : ι → C),
    IsUniversalCoproduct Xs ∧ (haveI := finiteLimits; IsDisjointCoproduct Xs)
  equivRel : ∀ {R Y : C} (r₁ r₂ : R ⟶ Y), IsEquivRel r₁ r₂ →
    ∃ _ : HasCoequalizer r₁ r₂, IsEffectiveEquivRel r₁ r₂ ∧ IsUniversalQuotient r₁ r₂
  generator : ∃ (ι : Type v) (G : ι → C), IsSeparatingFamily G

/-- URU5jgTvjhU-32152 (8:55:52) [prop] In a (locally small) category with a subobject classifier,
the subobjects of an object form a small set (`Sub(Y) ≃ Hom(Y, Ω)`). -/
theorem small_subobject [HasPullbacks C] (𝒞 : Subobject.Classifier C) (Y : C) :
    Small.{v} (Subobject Y) :=
  small_of_injective (f := (𝒞.representableBy.homEquiv (X := Y)).symm) (Equiv.injective _)

end Defs

/-- URU5jgTvjhU-31066 (8:37:46) [def] `Sh(X)` is a topos in the first sense. -/
theorem sheaf_isToposFirstForm :
    IsToposFirstForm (Sheaf (Opens.grothendieckTopology X) (Type u)) :=
  ⟨inferInstance, inferInstance, ⟨Opens X, opensSheaf, fun _ _ f g h => opensSheaf_separating f g h⟩⟩

/-! ## Cohomology in a topos -/

/-- URU5jgTvjhU-32217 (8:56:57) [prop] `ℰ_ab` (here for `ℰ = Sh(X)`) is a Grothendieck abelian
category (abelian, exact filtered colimits, a generator), hence has enough injectives. -/
theorem ab_grothendieck_injectives :
    IsGrothendieckAbelian.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ∧
      EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ⟨inferInstance, ab_enoughInjectives⟩

/-- URU5jgTvjhU-32283 (8:58:03) [prop] An injective object of `ℰ_ab` is injective in `ℰ` as soon as
the free abelian group functor `ℰ → ℰ_ab` (left adjoint of the forgetful functor) preserves
monomorphisms. -/
theorem injective_of_adjoint {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    [L.PreservesMonomorphisms] (adj : L ⊣ R) (I : D) (hI : Injective I) : Injective (R.obj I) :=
  adj.map_injective I hI

/-- URU5jgTvjhU-32541 (9:02:21) [def] `Γ(X) = Hom(e, X)`: Mathlib's `Sheaf.Γ`, the sections over the
terminal open set. -/
def gammaIso : Sheaf.Γ (Opens.grothendieckTopology X) (Type u) ≅
    (sheafSections (Opens.grothendieckTopology X) (Type u)).obj (op ⊤) :=
  Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop

/-- URU5jgTvjhU-32668 (9:04:28) [def] `I ↦ I_ℰ = ∐_I e` commutes with colimits (it is a left
adjoint) and with finite limits (`Part02.constantSheaf_preservesFiniteLimits`). -/
theorem constantSheaf_exact :
    Nonempty (PreservesColimits (constantSheaf (Opens.grothendieckTopology X) (Type u))) ∧
      Nonempty (PreservesFiniteLimits (constantSheaf (Opens.grothendieckTopology X) (Type u))) :=
  ⟨⟨(constantSheaf_adj (X := X)).leftAdjoint_preservesColimits⟩, ⟨inferInstance⟩⟩

/-! ## Basic examples of topoi -/

/-- URU5jgTvjhU-32997 (9:09:57) [prop] `Sh(∅)` is equivalent to the point category. -/
theorem sheaf_empty_equiv_point :
    Nonempty (Sheaf (Opens.grothendieckTopology (TopCat.of PEmpty.{u + 1})) (Type u) ≌
      Discrete PUnit.{1}) :=
  sheaf_equiv_point_iff.2 inferInstance

/-- URU5jgTvjhU-33121 (9:12:01) [prop] A category with strict initial objects (such as a topos) is
« empty » (equivalent to the point) iff `∅ → e` is an isomorphism. -/
theorem empty_iff_isIso {C : Type*} [Category C] [HasInitial C] [HasTerminal C]
    [HasStrictInitialObjects C] :
    Nonempty (C ≌ Discrete PUnit.{1}) ↔ IsIso (initial.to (⊤_ C)) := by
  rw [isIso_initial_to_terminal_iff, allInitial_iff_equiv_point]

/-- URU5jgTvjhU-33443 (9:17:23) [prop] For the point topos, `I ↦ I_ℰ` is an equivalence
`Set → Sh(pt)` (the left adjoint of the equivalence `Γ`). -/
theorem constantSheaf_pt_isEquivalence :
    (constantSheaf (Opens.grothendieckTopology pt.{u}) (Type u)).IsEquivalence :=
  have : ((sheafSections (Opens.grothendieckTopology pt.{u}) (Type u)).obj (op ⊤)).IsEquivalence :=
    inferInstanceAs ptSections.IsEquivalence
  (constantSheaf_adj (X := pt.{u})).isEquivalence_left_of_isEquivalence_right

/-- URU5jgTvjhU-33698 (9:21:38) [def] `B_G`, the category of `G`-sets (Mathlib's `Action`). -/
abbrev BG (G : Type u) [Group G] : Type _ := Action (Type u) G

/-- URU5jgTvjhU-33505 (9:18:25) [prop] (case `X = pt`) `B_G` is the category of presheaves on the
one-object category `G`, a topos. -/
def BG_equiv (G : Type u) [Group G] : BG G ≌ (SingleObj G ⥤ Type u) :=
  Action.functorCategoryEquivalence (Type u) G

/-- URU5jgTvjhU-33822 (9:23:42) [prop] `H^i(G, M)` is `Ext^i(ℤ, M)` in the category of `G`-modules
(Mathlib's `groupCohomologyIsoExt`), and `H⁰(G, M) = M^G`. -/
def groupCohomology_ext (G : Type) [Group G] (M : Rep ℤ G) (n : ℕ) :=
  groupCohomologyIsoExt M n

/-- URU5jgTvjhU-33822 (9:23:42) [prop] `Γ(M) = M^G`. -/
def groupCohomology_zero (G : Type) [Group G] (M : Rep ℤ G) :=
  groupCohomology.H0Iso M

end

end Buffalo.Topos.Part02
