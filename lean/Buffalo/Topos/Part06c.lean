import Buffalo.Topos.Part06b

/-!
# Buffalo, topos theory, part 6c: morphisms of sites, classifying topoi, subtopoi (1973)

Entries of `docs/buffalo-topos/index.tex` lines 932–964 (video `4gynb9uTEE4`, 7:21:48–7:34:39, and
video `ORG14LNb5gE`, 0:00:05–0:23:02): continuous functors and morphisms of sites, the classifying
topos `Ĉ` of a finite-limit theory, subtopoi and localization. The status of each entry is in
`docs/buffalo-topos/lean/Part06.json`.

Morphisms of topoi are `Buffalo.Topos.Part03.TopMor`; a subtopos (embedding) is a `TopMor` whose
direct image is fully faithful.
-/

universe w v u

open CategoryTheory Limits Opposite TopologicalSpace

namespace Buffalo.Topos.Part06

noncomputable section

open Part03 (TopMor)

/-! ## Continuous functors and morphisms of sites -/

section Sites

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]

/-- 4gynb9uTEE4-26508 (7:21:48) [def] `f : C → C'` is continuous if `F ↦ F ∘ f` sends sheaves on
`C'` to sheaves on `C` (Mathlib `Functor.IsContinuous`). -/
theorem isContinuous_def (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] (G : Sheaf K (Type w)) : Presieve.IsSheaf J (F.op ⋙ G.obj) :=
  Functor.op_comp_isSheaf_of_types F J K G

/-- 4gynb9uTEE4-26704 (7:25:04) [prop] If `C` has finite limits and `f` commutes with them, `f` is
continuous iff it sends covering families to covering families (Mathlib). -/
theorem isContinuous_iff_coverPreserving [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) :
    F.IsContinuous J K ↔ CoverPreserving J K F := by
  have := flat_of_preservesFiniteLimits F
  exact Functor.isContinuous_iff_coverPreserving

/-- 4gynb9uTEE4-26704 (7:25:04) [ex] For `f : X' → X` continuous, `U ↦ f⁻¹(U)` is a continuous
functor from the site of open sets of `X` to that of `X'` (Mathlib). -/
theorem opens_map_isContinuous {X X' : TopCat.{u}} (f : X' ⟶ X) :
    (Opens.map f).IsContinuous (Opens.grothendieckTopology X) (Opens.grothendieckTopology X') :=
  inferInstance

/-- 4gynb9uTEE4-26832 (7:27:12) [prop] (partial: "only if") If `R` is a covering sieve of `X`,
the inclusion `R → yX` becomes an isomorphism after sheafification (it is in `J.W`), i.e.
`ε(X) = colim_{C/R} ε(Y)` (Mathlib). -/
theorem covering_sieve_W [LocallySmall.{w} C] (J : GrothendieckTopology C) {X : C} (S : Sieve X)
    (hS : S ∈ J X) : J.W (Sieve.shrinkFunctor.{w} S).ι :=
  Sieve.W_shrinkFunctor_ι_of_mem (J := J) S hS

/-- 4gynb9uTEE4-27021 (7:30:21) [prop] (partial: "if") Between small sites, a continuous left
exact functor `G : C → D` induces a morphism of topoi `Sh(D) → Sh(C)`, with left exact inverse
image `G^s` and direct image `F ↦ F ∘ G`. -/
def morphismOfSites {C D : Type u} [SmallCategory C] [SmallCategory D] [HasFiniteLimits C]
    (G : C ⥤ D) [PreservesFiniteLimits G] (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [Functor.IsContinuous.{u} G J K] :
    TopMor (Sheaf K (Type u)) (Sheaf J (Type u)) :=
  have := flat_of_preservesFiniteLimits G
  { inv := G.sheafPullback (Type u) J K
    dir := G.sheafPushforwardContinuous (Type u) J K
    adj := G.sheafAdjunctionContinuous (Type u) J K
    lex := by
      have := Part03.lan_lex G
      exact Functor.sheafPullbackConstruction.preservesFiniteLimits G (Type u) J K }

/-- 4gynb9uTEE4-27085 (7:31:25) [def] A morphism of sites: a continuous functor whose induced
inverse image is left exact (it then induces a morphism of topoi, `morphismOfSites`). -/
def IsMorphismOfSites {C D : Type u} [SmallCategory C] [SmallCategory D] (G : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) : Prop :=
  ∃ _ : Functor.IsContinuous.{u} G J K, PreservesFiniteLimits (G.sheafPullback (Type u) J K)

/-- 4gynb9uTEE4-27279 (7:34:39) [prop] `Ĉ = C̃` for the coarsest topology `⊥`: every presheaf is a
sheaf (Mathlib) ... -/
theorem isSheaf_bot (P : Cᵒᵖ ⥤ Type w) : Presieve.IsSheaf (⊥ : GrothendieckTopology C) P :=
  Presieve.isSheaf_bot

/-- ... and a family covers for `⊥` iff it has a member with a section. -/
theorem bot_covers_iff {X : C} (R : Presieve X) :
    Sieve.generate R ∈ (⊥ : GrothendieckTopology C) X ↔
      ∃ (Y : C) (f : Y ⟶ X), R f ∧ ∃ s : X ⟶ Y, s ≫ f = 𝟙 X := by
  rw [GrothendieckTopology.bot_covering, ← Sieve.id_mem_iff_eq_top]
  constructor
  · rintro ⟨Y, s, f, hf, e⟩
    exact ⟨Y, f, hf, s, e⟩
  · rintro ⟨Y, f, hf, s, e⟩
    exact ⟨Y, s, f, hf, e⟩

end Sites

/-! ## Classifying topoi of finite-limit theories -/

/-- ORG14LNb5gE-5 (0:00:05) [thm] (partial) A morphism of topoi `f : E → Ĉ` gives the left exact
functor `X ↦ f^*(yX)` ... -/
theorem classifying_toLex {C : Type u} [SmallCategory C] {E : Type*} [Category* E]
    (f : TopMor E (Cᵒᵖ ⥤ Type u)) : PreservesFiniteLimits (yoneda ⋙ f.inv) :=
  yoneda_comp_inv_lex f

/-- ... and conversely (for `E = D̂`, and a left exact functor with values in representables) a left
exact `φ : C → D` gives a morphism of topoi `D̂ → Ĉ` with inverse image `φ_!` (Part 3). -/
def classifying_ofLex {C D : Type u} [SmallCategory C] [SmallCategory D] [HasFiniteLimits C]
    (φ : C ⥤ D) [PreservesFiniteLimits φ] : TopMor (Dᵒᵖ ⥤ Type u) (Cᵒᵖ ⥤ Type u) :=
  have := Part03.lan_lex φ
  Part03.presheafMorOp φ

/-- ORG14LNb5gE-195 (0:03:15) [ex] (partial) Affine schemes are the opposite of commutative rings
(Mathlib), so presheaves on affine schemes of finite type over `ℤ` are functors on finitely
presented rings. -/
def affineSchemeEquiv : AlgebraicGeometry.AffineScheme.{u} ≌ CommRingCat.{u}ᵒᵖ :=
  AlgebraicGeometry.AffineScheme.equivCommRingCat

/-! ## Subtopoi and localization -/

section Subtopoi

variable {E : Type*} [Category* E] {E' : Type*} [Category* E'] {F : Type*} [Category* F]

/-- ORG14LNb5gE-801 (0:13:21) [def] A morphism of topoi `i : E' → E` is an embedding if `i_*` is
fully faithful ... -/
def IsEmbedding (i : TopMor E' E) : Prop := i.dir.Full ∧ i.dir.Faithful

/-- ... and then `i^*` is a localization functor (Mathlib). -/
theorem IsEmbedding.isLocalization {i : TopMor E' E} (h : IsEmbedding i) :
    i.inv.IsLocalization ((MorphismProperty.isomorphisms E').inverseImage i.inv) := by
  obtain ⟨_, _⟩ := h
  exact i.adj.isLocalization

/-- ORG14LNb5gE-930 (0:15:30) [prop] A full subcategory whose inclusion has a left exact left
adjoint gives a subtopos ... -/
def ofReflective (ι : E' ⥤ E) [Reflective ι] [PreservesFiniteLimits (reflector ι)] :
    TopMor E' E where
  inv := reflector ι
  dir := ι
  adj := reflectorAdjunction ι
  lex := inferInstance

theorem ofReflective_isEmbedding (ι : E' ⥤ E) [Reflective ι] [PreservesFiniteLimits (reflector ι)] :
    IsEmbedding (ofReflective ι) := ⟨inferInstanceAs ι.Full, inferInstanceAs ι.Faithful⟩

/-- ... and conversely the direct image of an embedding is reflective, with left exact
reflector. -/
theorem IsEmbedding.reflective {i : TopMor E' E} (h : IsEmbedding i) :
    Nonempty (Reflective i.dir) :=
  have := h.1
  have := h.2
  ⟨{ L := i.inv, adj := i.adj }⟩

/-- ORG14LNb5gE-997 (0:16:37) [prop] (partial) For a topology `J` on `C`, `Sh(C, J)` is a subtopos
of `Ĉ` (sheafification is left exact). -/
def sheafSubtopos {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    TopMor (Sheaf J (Type u)) (Cᵒᵖ ⥤ Type u) where
  inv := presheafToSheaf J (Type u)
  dir := sheafToPresheaf J (Type u)
  adj := sheafificationAdjunction J (Type u)
  lex := inferInstance

theorem sheafSubtopos_isEmbedding {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    IsEmbedding (sheafSubtopos J) :=
  ⟨inferInstanceAs (sheafToPresheaf J (Type u)).Full,
    inferInstanceAs (sheafToPresheaf J (Type u)).Faithful⟩

/-- ORG14LNb5gE-1059 (0:17:39) [prop] (partial) If `f : X → Y` is inducing (the topology of `X` is
the inverse image of that of `Y`), every open set of `X` is `f⁻¹(V)`: `O(Y) → O(X)` is
surjective. -/
theorem opens_map_surjective_of_isInducing {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : Topology.IsInducing f) (U : Opens X) : ∃ V : Opens Y, (Opens.map f).obj V = U := by
  obtain ⟨V, hV, e⟩ := hf.isOpen_iff.1 U.2
  exact ⟨⟨V, hV⟩, Opens.ext e⟩

/-- ORG14LNb5gE-1124 (0:18:44) [prop] (partial) If the direct image of `f : F → E` factors (up to
isomorphism) through the subtopos `i : E' → E`, then `f` factors through `E'`: there is
`g : F → E'` with `g_* i_* ≅ f_*`. -/
theorem factors_through_embedding {i : TopMor E' E} (hi : IsEmbedding i) (f : TopMor F E)
    (hf : ∀ X, i.dir.essImage (f.dir.obj X)) :
    ∃ g : TopMor F E', Nonempty (g.dir ⋙ i.dir ≅ f.dir) := by
  obtain ⟨_, _⟩ := hi
  let gd : F ⥤ E' := Functor.essImage.liftFunctor f.dir i.dir hf
  have e : gd ⋙ i.dir ≅ f.dir := Functor.essImage.liftFunctorCompIso f.dir i.dir hf
  have : PreservesLimits i.dir := i.adj.rightAdjoint_preservesLimits
  have := i.lex
  have := f.lex
  refine ⟨{ inv := i.dir ⋙ f.inv
            dir := gd
            adj := f.adj.restrictFullyFaithful (Functor.FullyFaithful.ofFullyFaithful i.dir)
              (Functor.FullyFaithful.id F) (Functor.rightUnitor _).symm
              (Functor.leftUnitor _ ≪≫ e.symm)
            lex := comp_preservesFiniteLimits _ _ }, ⟨e⟩⟩

/-- ORG14LNb5gE-1189 (0:19:49) [prop] To a subtopos one associates the arrows made invertible by
`i^*`: they are the arrows `Y → Z` such that `Hom(Z, X) → Hom(Y, X)` is bijective for every `X` in
the subtopos (Mathlib, Bousfield localization) ... -/
theorem inverted_eq_isLocal {i : TopMor E' E} (hi : IsEmbedding i) :
    (MorphismProperty.isomorphisms E').inverseImage i.inv =
      ObjectProperty.isLocal (· ∈ Set.range i.dir.obj) := by
  obtain ⟨_, _⟩ := hi
  exact (ObjectProperty.isLocal_eq_inverseImage_isomorphisms i.adj).symm

/-- ORG14LNb5gE-1320 (0:22:00) [thm] (partial: second half) Every subtopos is obtained by inverting
a family of arrows: the objects local for the arrows inverted by `i^*` are exactly those of the
subtopos. -/
theorem subtopos_eq_local {i : TopMor E' E} (hi : IsEmbedding i) (X : E)
    (hX : ((MorphismProperty.isomorphisms E').inverseImage i.inv).isLocal X) :
    ∃ Y : E', Nonempty (i.dir.obj Y ≅ X) := by
  obtain ⟨_, _⟩ := hi
  have hη : (MorphismProperty.isomorphisms E').inverseImage i.inv (i.adj.unit.app X) := by
    rw [inverted_eq_isLocal ⟨inferInstance, inferInstance⟩]
    exact ObjectProperty.isLocal_adj_unit_app i.adj X
  obtain ⟨r, hr⟩ := (hX _ hη).2 (𝟙 X)
  have hloc := ObjectProperty.isLocal_adj_unit_app i.adj X
  simp only at hr
  have h2 : r ≫ i.adj.unit.app X = 𝟙 _ :=
    (hloc _ ⟨_, rfl⟩).1 (by dsimp only; rw [← Category.assoc, hr]; simp)
  exact ⟨i.inv.obj X, ⟨Iso.mk r (i.adj.unit.app X) h2 hr⟩⟩

/-- ORG14LNb5gE-1382 (0:23:02) [prop] (partial) For topologies `J ≤ K` on `C`, every `K`-sheaf is a
`J`-sheaf, so `Sh(C, K) ⊂ Sh(C, J)` (Mathlib). -/
theorem isSheaf_of_le {C : Type u} [Category.{v} C] {J K : GrothendieckTopology C} (h : J ≤ K)
    (P : Cᵒᵖ ⥤ Type w) (hP : Presieve.IsSheaf K P) : Presieve.IsSheaf J P :=
  Presieve.isSheaf_of_le P h hP

end Subtopoi

end

end Buffalo.Topos.Part06
