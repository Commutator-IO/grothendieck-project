import Buffalo.AG.Part04b

/-!
# Buffalo, algebraic geometry, part 04 (c): 18 June 1973, schemes as Zariski sheaves

The entries of `docs/buffalo-ag/index.tex` lines 552–611 (video `thSz9ZHDK9o`, 4:04:17–5:58:36):
morphisms into an affine scheme and the adjunction `Γ ⊣ Spec`, schemes as sheaves for the
Zariski topology and the comparison with affine schemes, sums of schemes, epimorphisms of
Zariski sheaves, open immersions of sheaves and the representability criterion.

All statements are over `k = ℤ` (all schemes, all rings) unless said otherwise.
-/

open CategoryTheory Limits Opposite IsLocalRing TopologicalSpace AlgebraicGeometry

universe u

namespace Buffalo.AG.Part04

noncomputable section

/-! ### Morphisms into an affine scheme -/

/-- thSz9ZHDK9o-14657 (4:04:17) [prop] To `u : A → Γ(X, 𝒪_X)`, `X` locally ringed, one associates
`φ : x ↦ ker(A → κ(x))` (here `u⁻¹` of the point `toΓSpecFun x` of `Spec Γ(X)`), continuous, with
`φ⁻¹(D(f)) = X_{u(f)}`. -/
theorem prop_14657 (X : LocallyRingedSpace.{u}) {A : Type u} [CommRing A]
    (u : A →+* LocallyRingedSpace.Γ.obj (op X)) :
    (∀ (x : X) (a : A), a ∈ (PrimeSpectrum.comap u (X.toΓSpecFun x)).asIdeal ↔
      IsLocalRing.residue (X.presheaf.stalk x) (X.presheaf.Γgerm x (u a)) = 0) ∧
    Continuous (fun x => PrimeSpectrum.comap u (X.toΓSpecFun x)) ∧
    ∀ f : A, (fun x => PrimeSpectrum.comap u (X.toΓSpecFun x)) ⁻¹' PrimeSpectrum.basicOpen f =
      SetLike.coe (X.toRingedSpace.basicOpen (u f)) := by
  refine ⟨fun x a => ?_, (PrimeSpectrum.continuous_comap u).comp X.toΓSpec_continuous,
    fun f => ?_⟩
  · rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, IsLocalRing.residue_eq_zero_iff,
      ← not_iff_not, LocallyRingedSpace.notMem_prime_iff_unit_in_stalk,
      IsLocalRing.notMem_maximalIdeal]
  · rw [← X.toΓSpec_preimage_basicOpen_eq (u f)]
    rfl

/-- thSz9ZHDK9o-14721 (4:05:21) [prop] The map `φ` completes into a morphism of locally ringed
spaces `X → Spec A`: for `u = id`, the unit `X → Spec Γ(X)` of the adjunction (mathlib's
`toΓSpec`), composed with `Spec u` in general (`prop_14251`). -/
example (X : LocallyRingedSpace.{u}) :
    X ⟶ Spec.toLocallyRingedSpace.obj (op (LocallyRingedSpace.Γ.obj (op X))) :=
  X.toΓSpec

/-- thSz9ZHDK9o-14914 (4:08:34) [thm] For every locally ringed space `X`,
`Hom(X, Spec A) ≃ Hom(A, Γ(X, 𝒪_X))` functorially: `Spec` is right adjoint to `Γ` (opposite
rings). -/
def thm_14914 : LocallyRingedSpace.Γ.rightOp ⊣ Spec.toLocallyRingedSpace.{u} :=
  ΓSpec.locallyRingedSpaceAdjunction

/-! ### Schemes as sheaves for the Zariski topology -/

/-- thSz9ZHDK9o-15240 (4:14:00) [prop] The opposite of the category of `k`-algebras is equivalent
to the category of affine schemes over `Spec k`. -/
def prop_15240 (k : CommRingCat.{u}) :
    (CommAlgCat.{u} k)ᵒᵖ ≌ Over (AffineScheme.equivCommRingCat.inverse.obj (op k)) :=
  (Buffalo.AG.Part01.prop_12039 k).symm.trans (Over.postEquiv _ AffineScheme.equivCommRingCat.symm)

/-- thSz9ZHDK9o-15432 (4:17:12) [prop] A `k`-scheme `X → Spec k` defines a functor from
`k`-algebras to sets, `k' ↦ X(k') = Hom_k(Spec k', X)`. -/
def ptsOver (k : CommRingCat.{u}) (X : Over (Spec k)) : CommAlgCat.{u} k ⥤ Type u where
  obj k' := {f : Spec (CommRingCat.of k') ⟶ X.left //
    f ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k k'))}
  map {k' k''} g := ↾fun f => ⟨Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫ f.1, by
    rw [Category.assoc, f.2, ← Spec.map_comp]
    congr 1
    ext c
    exact g.hom.commutes c⟩
  map_id k' := by
    ext f
    exact (congrArg (· ≫ f.1) (Spec.map_id (CommRingCat.of k'))).trans (Category.id_comp _)
  map_comp {k₁ k₂ k₃} g h := by
    ext f
    change Spec.map (CommRingCat.ofHom (g ≫ h).hom.toRingHom) ≫ f.1 =
      Spec.map (CommRingCat.ofHom h.hom.toRingHom) ≫ Spec.map (CommRingCat.ofHom g.hom.toRingHom)
        ≫ f.1
    rw [← Category.assoc, ← Spec.map_comp]
    rfl

/-- thSz9ZHDK9o-15698 (4:21:38) [prop] The functor represented by a scheme is a sheaf for the
Zariski topology. -/
theorem prop_15698 (X : Scheme.{u}) :
    Presieve.IsSheaf Scheme.zariskiTopology (yoneda.obj X) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- thSz9ZHDK9o-15892 (4:24:52) [prop] The jointly surjective families of open immersions form a
pretopology on schemes (`Scheme.zariskiPretopology`) generating the Zariski topology. -/
theorem prop_15892 :
    Scheme.zariskiTopology.{u} = Scheme.zariskiPretopology.toGrothendieck :=
  Scheme.zariskiTopology_eq

/-- `Spec` is cover-dense for the Zariski topology: every scheme is covered by affine schemes. -/
instance Spec_isCoverDense : Scheme.Spec.{u}.IsCoverDense Scheme.zariskiTopology where
  is_cover X := by
    refine Scheme.zariskiTopology.superset_covering ?_ X.affineCover.mem_grothendieckTopology
    rintro Y f ⟨Z, h, g, ⟨i⟩, rfl⟩
    exact ⟨⟨op _, h, X.affineCover.f i, rfl⟩⟩

/-- thSz9ZHDK9o-16149 (4:29:09) [prop] Restriction to affine schemes is fully faithful from
Zariski sheaves on schemes: morphisms between restrictions extend uniquely. -/
def prop_16149 (F G : Sheaf Scheme.zariskiTopology.{u} (Type u)) :
    (Scheme.Spec.op ⋙ F.obj ⟶ Scheme.Spec.op ⋙ G.obj) ≃ (F.obj ⟶ G.obj) :=
  Functor.IsCoverDense.restrictHomEquivHom

/-- thSz9ZHDK9o-17450 (4:50:50) [prop] Restriction of Zariski sheaves to affine schemes is an
equivalence (comparison lemma). Partial: `Spec` is cover-dense (`Spec_isCoverDense`), so
`(Spec, induced topology)` is a dense subsite and the restriction is fully faithful
(`prop_16149`); mathlib's comparison lemma `Functor.IsDenseSubsite.sheafEquiv` needs limits of
`Type u` indexed by the large categories `StructuredArrow X Spec.op`, which do not exist, so
essential surjectivity is not obtained. -/
example : Scheme.Spec.{u}.IsDenseSubsite (Scheme.Spec.inducedTopology Scheme.zariskiTopology)
    Scheme.zariskiTopology := inferInstance

/-- thSz9ZHDK9o-16277 (4:31:17) [prop] Every open subset of a scheme is a scheme (with an open
immersion into it); the affine opens form a basis; on an affine scheme, the `X_f` do. -/
theorem prop_16277 (X : Scheme.{u}) (U : X.Opens) :
    IsOpenImmersion U.ι ∧ Opens.IsBasis X.affineOpens ∧
      (IsAffine X → Opens.IsBasis (Set.range (X.basicOpen : Γ(X, ⊤) → X.Opens))) :=
  ⟨inferInstance, X.isBasis_affineOpens, fun _ => isBasis_basicOpen X⟩

/-! ### Sums of schemes -/

/-- thSz9ZHDK9o-16684 (4:38:04) [prop] Sums exist in locally ringed spaces and in ringed
(sheafed) spaces, and are computed on the underlying spaces: the forgetful functors
`LRS → SheafedSpace → Top` preserve them. -/
theorem prop_16684 (ι : Type u) :
    HasColimitsOfShape (Discrete ι) LocallyRingedSpace.{u} ∧
      PreservesColimitsOfShape (Discrete ι) LocallyRingedSpace.forgetToSheafedSpace.{u} ∧
      HasColimitsOfShape (Discrete ι) (SheafedSpace.{u + 1, u, u} CommRingCat.{u}) ∧
      PreservesColimitsOfShape (Discrete ι) (SheafedSpace.forget.{u + 1, u, u} CommRingCat.{u}) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- thSz9ZHDK9o-16874 (4:41:14) [prop] The sum of schemes is a scheme, the sum in the category of
schemes, computed on underlying spaces, its summands being disjoint open sets; sums also exist
over a base `S`. -/
theorem prop_16874 {σ : Type u} (g : σ → Scheme.{u}) (S : Scheme.{u}) :
    HasColimitsOfShape (Discrete σ) Scheme.{u} ∧
      PreservesColimitsOfShape (Discrete σ) Scheme.forgetToTop.{u} ∧
      (∀ i, IsOpenImmersion (Sigma.ι g i)) ∧
      (∀ i j, i ≠ j → Disjoint (Sigma.ι g i).opensRange (Sigma.ι g j).opensRange) ∧
      HasColimitsOfShape (Discrete σ) (Over S) :=
  ⟨inferInstance, inferInstance, fun _ => inferInstance,
    fun i j h => disjoint_opensRange_sigmaι g i j h, inferInstance⟩

/-- thSz9ZHDK9o-17064 (4:44:24) [prop] A morphism `S' → ∐ X_i` amounts to a decomposition of `S'`
into the disjoint open sets `S'_i = f⁻¹(X_i)`, covering `S'`, with morphisms `S'_i → X_i`. -/
theorem prop_17064 {σ : Type u} (g : σ → Scheme.{u}) {S' : Scheme.{u}} (f : S' ⟶ ∐ g) :
    (∀ i j, i ≠ j → Disjoint (f.base ⁻¹' Set.range (Sigma.ι g i).base)
      (f.base ⁻¹' Set.range (Sigma.ι g j).base)) ∧
    (⋃ i, f.base ⁻¹' Set.range (Sigma.ι g i).base) = Set.univ ∧
    ∀ i, ∃ h : (f ⁻¹ᵁ (Sigma.ι g i).opensRange).toScheme ⟶ g i,
      h ≫ Sigma.ι g i = (f ⁻¹ᵁ (Sigma.ι g i).opensRange).ι ≫ f := by
  refine ⟨fun i j hij => Set.disjoint_left.2 fun s ⟨x, hx⟩ ⟨y, hy⟩ => hij ?_, ?_, fun i => ?_⟩
  · have := (sigmaι_eq_iff g i j x y).1 (hx.trans hy.symm)
    exact congrArg Sigma.fst this
  · refine Set.eq_univ_of_forall fun s => Set.mem_iUnion.2 ?_
    obtain ⟨i, x, hx⟩ := (sigmaOpenCover g).exists_eq (f.base s)
    exact ⟨i, x, hx⟩
  · refine ⟨f.resLE _ _ le_rfl ≫ (Sigma.ι g i).isoOpensRange.inv, ?_⟩
    rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, Scheme.Hom.resLE_comp_ι]

/-- In general a morphism into a sum factors through no summand: the identity of `∐ X_i`, when
two summands are nonempty. -/
theorem prop_17064_cex {σ : Type u} (g : σ → Scheme.{u}) {k l : σ} (hkl : k ≠ l)
    (hl : Nonempty (g l)) : ¬ ∃ h : ∐ g ⟶ g k, h ≫ Sigma.ι g k = 𝟙 _ := by
  rintro ⟨h, hh⟩
  obtain ⟨y⟩ := hl
  have := congrArg (fun φ : ∐ g ⟶ ∐ g => φ.base (Sigma.ι g l |>.base y)) hh
  simp only [Scheme.Hom.comp_base, TopCat.comp_app, Scheme.Hom.id_base, TopCat.id_app] at this
  exact hkl (congrArg Sigma.fst ((sigmaι_eq_iff g k l _ y).1 this))

/-- thSz9ZHDK9o-17128 (4:45:28) [prop] Among Zariski sheaves, the sheaf represented by `∐ X_i`
is the sum of the sheaves represented by the `X_i`: every Zariski sheaf `F` takes sums of
schemes to products, `F(∐ X_i) = ∏ F(X_i)` (so `Hom(h_{∐X_i}, F) = ∏ Hom(h_{X_i}, F)`). -/
theorem prop_17128 {F : Scheme.{u}ᵒᵖ ⥤ Type u} (hF : Presieve.IsSheaf Scheme.zariskiTopology F)
    (ι : Type u) : PreservesLimitsOfShape (Discrete ι) F :=
  preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF

/-- thSz9ZHDK9o-17192 (4:46:32) [prop] A family of monomorphisms `F_i → F` with pairwise disjoint
images, jointly epimorphic, makes `F` the sum of the `F_i`. Partial: the case of sets (sheaves on
a point); for Zariski sheaves, epimorphisms are only local surjections. -/
theorem prop_17192 {ι F : Type u} {X : ι → Type u} (f : ∀ i, X i → F)
    (hinj : ∀ i, Function.Injective (f i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (f i)) (Set.range (f j)))
    (hcov : ∀ y, ∃ i x, f i x = y) :
    Function.Bijective (fun p : Σ i, X i => f p.1 p.2) := by
  refine ⟨fun ⟨i, x⟩ ⟨j, y⟩ hxy => ?_, fun y => ?_⟩
  · by_cases hij : i = j
    · subst hij
      exact congrArg (Sigma.mk i) (hinj i hxy)
    · exact ((Set.disjoint_left.1 (hdisj i j hij)) ⟨x, rfl⟩ ⟨y, hxy.symm⟩).elim
  · obtain ⟨i, x, hx⟩ := hcov y
    exact ⟨⟨i, x⟩, hx⟩

/-- A Zariski sheaf takes the empty scheme to a one-point set (empty covering). -/
theorem unique_obj_empty {F : Scheme.{u}ᵒᵖ ⥤ Type u}
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F) (E : Scheme.{u}) [IsEmpty E] :
    ∃! _t : F.obj (op E), True := by
  have h := hF ⊥ (Scheme.bot_mem_grothendieckTopology E)
  obtain ⟨t, -, ht⟩ := h (by intro Y f hf; simp at hf)
    (by intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁; simp at h₁)
  exact ⟨t, trivial, fun t' _ => ht t' (by intro Y f hf; simp at hf)⟩

/-- thSz9ZHDK9o-17324 (4:48:44) [prop] For `i ≠ j`, `X_i ×_X X_j` is empty; the empty scheme
represents the initial sheaf: `Hom(S', ∅)` is a point if `S'` is empty and empty otherwise, and
it maps uniquely to every Zariski sheaf. -/
theorem prop_17324 {σ : Type u} (g : σ → Scheme.{u}) {i j : σ} (hij : i ≠ j) (S' : Scheme.{u})
    (F : Sheaf Scheme.zariskiTopology.{u} (Type u)) :
    IsEmpty ↑(pullback (Sigma.ι g i) (Sigma.ι g j) : Scheme.{u}) ∧
      (Nonempty (S' ⟶ ∅) ↔ IsEmpty S') ∧ Subsingleton (S' ⟶ ∅) ∧
      ∃! _t : F.obj.obj (op (∅ : Scheme.{u})), True := by
  refine ⟨isEmpty_pullback_sigmaι_of_ne g hij, ⟨fun ⟨f⟩ => ⟨fun x => isEmptyElim (f.base x)⟩,
    fun _ => ⟨isInitialOfIsEmpty.to _⟩⟩, ⟨fun f g' => ?_⟩, unique_obj_empty ((isSheaf_iff_isSheaf_of_type _ _).1 F.property) _⟩
  have : IsEmpty S' := ⟨fun x => isEmptyElim (f.base x)⟩
  exact isInitialOfIsEmpty.hom_ext f g'

/-! ### Epimorphisms of Zariski sheaves -/

/-- thSz9ZHDK9o-17740 (4:55:40) [prop] Subsheaves `F_i` cover `F` (their supremum among
subsheaves, the sheafification of `⋃ F_i`, is `F`) iff every section of `F` belongs, locally,
to one of the `F_i`. Stated for any site. -/
theorem prop_17740 {C : Type*} [Category C] (J : GrothendieckTopology C) {F : Cᵒᵖ ⥤ Type*}
    {ι : Type*} (G : ι → Subfunctor F) :
    ((⨆ i, G i).sheafify J = ⊤ ↔
      ∀ (U : Cᵒᵖ) (s : F.obj U), (⨆ i, G i).sieveOfSection s ∈ J U.unop) ∧
    ∀ (U : Cᵒᵖ) (s : F.obj U) (V : C) (f : V ⟶ U.unop),
      (⨆ i, G i).sieveOfSection s f ↔ ∃ i, F.map f.op s ∈ (G i).obj (op V) := by
  refine ⟨⟨fun h U s => ?_, fun h => ?_⟩, fun U s V f => ?_⟩
  · have : s ∈ ((⨆ i, G i).sheafify J).obj U := by rw [h]; trivial
    exact this
  · refine le_antisymm le_top fun U s _ => h U s
  · simp [Subfunctor.iSup_obj]

/-- thSz9ZHDK9o-17546 (4:52:26) [prop] A morphism of Zariski sheaves is an epimorphism if every
section lifts locally. Partial: this direction (`epi_of_isLocallySurjective`); the converse uses
sheafification, which mathlib does not provide on the large site of schemes. -/
theorem prop_17546 {F G : Sheaf Scheme.zariskiTopology.{u} (Type u)} (φ : F ⟶ G)
    [Sheaf.IsLocallySurjective φ] : Epi φ :=
  inferInstance

/-- thSz9ZHDK9o-18065 (5:01:05) [prop] If `U = ⋃ U_i` is open in `X`, every morphism `S' → U`
factors, locally on `S'`, through some `U_i` (so `h_U = sup h_{U_i}`). -/
theorem prop_18065 {X S' : Scheme.{u}} {ι : Type*} (U : ι → X.Opens) (f : S' ⟶ X)
    (hf : Set.range f.base ⊆ ⋃ i, (U i : Set X)) (s : S') :
    ∃ i, s ∈ f ⁻¹ᵁ U i ∧ ∃ h : (f ⁻¹ᵁ U i).toScheme ⟶ (U i).toScheme,
      h ≫ (U i).ι = (f ⁻¹ᵁ U i).ι ≫ f := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hf ⟨s, rfl⟩)
  exact ⟨i, hi, f.resLE _ _ le_rfl, Scheme.Hom.resLE_comp_ι _ _⟩

/-- thSz9ZHDK9o-17934 (4:58:54) [prop] For `X = ∐ X_i`, every morphism `S' → X` factors locally
on `S'` through some `X_i`, on the preimages of the `X_i` (`prop_17064`). -/
theorem prop_17934 {σ : Type u} (g : σ → Scheme.{u}) {S' : Scheme.{u}} (f : S' ⟶ ∐ g)
    (s : S') : ∃ i, s ∈ f ⁻¹ᵁ (Sigma.ι g i).opensRange ∧
      ∃ h : (f ⁻¹ᵁ (Sigma.ι g i).opensRange).toScheme ⟶ g i,
        h ≫ Sigma.ι g i = (f ⁻¹ᵁ (Sigma.ι g i).opensRange).ι ≫ f := by
  obtain ⟨-, hcov, hfac⟩ := prop_17064 g f
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov ▸ Set.mem_univ s)
  exact ⟨i, hi, hfac i⟩

/-- The sheaf represented by the empty scheme. -/
def emptySheaf : Sheaf Scheme.zariskiTopology.{u} (Type u) where
  obj := yoneda.obj (∅ : Scheme.{u})
  property := (isSheaf_iff_isSheaf_of_type _ _).2 (prop_15698 _)

/-- The empty scheme represents the initial Zariski sheaf. -/
def emptySheafIsInitial : IsInitial (emptySheaf.{u}) :=
  IsInitial.ofUniqueHom
    (fun F => (fullyFaithfulSheafToPresheaf _ _).preimage
      (yonedaEquiv.symm (unique_obj_empty ((isSheaf_iff_isSheaf_of_type _ _).1 F.property)
        ∅).choose))
    (fun F m => (fullyFaithfulSheafToPresheaf _ _).map_injective (yonedaEquiv.injective (by
      have h := unique_obj_empty ((isSheaf_iff_isSheaf_of_type _ _).1 F.property) ∅
      exact h.unique trivial trivial)))

/-- thSz9ZHDK9o-18390 (5:06:30) [prop] The inclusion of Zariski sheaves into presheaves commutes
with (small) projective limits, but not with inductive limits: the initial sheaf, represented by
the empty scheme, is not the initial presheaf (which is empty on `∅`). -/
theorem prop_18390 :
    (∀ (K : Type u) [SmallCategory K],
      PreservesLimitsOfShape K (sheafToPresheaf Scheme.zariskiTopology.{u} (Type u))) ∧
    Nonempty (IsInitial emptySheaf.{u}) ∧
    ¬ Nonempty (IsInitial ((sheafToPresheaf Scheme.zariskiTopology.{u} (Type u)).obj
      emptySheaf.{u})) := by
  refine ⟨fun K _ => inferInstance, ⟨emptySheafIsInitial⟩, fun ⟨h⟩ => ?_⟩
  let E : Scheme.{u}ᵒᵖ ⥤ Type u := (Functor.const _).obj PEmpty
  exact ((h.to E).app (op ∅) (𝟙 (∅ : Scheme.{u}))).elim

/-- thSz9ZHDK9o-19298 (5:21:38) [prop] `Spec A' = ⋃ D(fᵢ)` iff the `fᵢ` generate the unit
ideal. -/
theorem prop_19298 {A' : Type u} [CommRing A'] {ι : Type*} (f : ι → A') :
    (⨆ i, PrimeSpectrum.basicOpen (f i)) = ⊤ ↔ Ideal.span (Set.range f) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff

/-- thSz9ZHDK9o-19365 (5:22:45) [prop] For `fᵢ ∈ A'` generating the unit ideal, the
`Spec A'_{fᵢ} → Spec A'` form a Zariski covering, so a Zariski sheaf `F` gives an exact
`F(A') → ∏ F(A'_{fᵢ}) ⇉ ∏ F(A'_{fᵢfⱼ})`. Partial: the converse (exactness for these coverings
suffices for the sheaf property) is the comparison lemma (`prop_17450`). -/
theorem prop_19365 {R : CommRingCat.{u}} {ι : Type u} (s : ι → R)
    (hs : Ideal.span (Set.range s) = ⊤) :
    Sieve.ofArrows (fun i => Spec (CommRingCat.of (Localization.Away (s i))))
      (fun i => Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (s i))))) ∈
        Scheme.zariskiTopology (Spec R) :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop s hs).openCover.mem_grothendieckTopology

/-! ### Open immersions of sheaves -/

/-- thSz9ZHDK9o-19840 (5:30:40) [def] `F → G` is an open immersion if its base change by every
`S' → G`, `S'` a scheme, is (representable and) an open immersion `U' ⊂ S'` (mathlib's
`IsOpenImmersion.presheaf`, i.e. `MorphismProperty.relative yoneda`). -/
theorem def_19840 {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (f : F ⟶ G) (hf : IsOpenImmersion.presheaf f)
    {S' : Scheme.{u}} (g : yoneda.obj S' ⟶ G) :
    IsOpenImmersion (hf.rep.snd g) :=
  hf.property_snd g

/-- thSz9ZHDK9o-19970 (5:32:50) [prop] A property `P` of morphisms of schemes stable under base
change extends to morphisms of sheaves (`P.presheaf`), and on morphisms of schemes it is `P`
again. -/
theorem prop_19970 (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : P.presheaf (yoneda.map f) ↔ P f :=
  MorphismProperty.relative_map_iff

/-- thSz9ZHDK9o-20034 (5:33:54) [prop] If `U' ⊂ S'` is open and `S'' → S'`, the preimage `U''` is
`S'' ×_{S'} U'`; open immersions of schemes are stable under base change. -/
def prop_20034 {S'' S' : Scheme.{u}} (f : S'' ⟶ S') (U' : S'.Opens) :
    pullback f U'.ι ≅ (f ⁻¹ᵁ U').toScheme :=
  pullbackRestrictIsoRestrict f U'

example : MorphismProperty.IsStableUnderBaseChange (@IsOpenImmersion) := inferInstance

/-- thSz9ZHDK9o-20162 (5:36:02) [prop] Open immersions of sheaves are stable under base change. -/
theorem prop_20162 :
    MorphismProperty.IsStableUnderBaseChange
      (IsOpenImmersion.presheaf : MorphismProperty (Scheme.{u}ᵒᵖ ⥤ Type u)) :=
  MorphismProperty.relative_isStableUnderBaseChange _

/-- thSz9ZHDK9o-20290 (5:38:10) [prop] The composite of two open immersions of sheaves is an open
immersion. -/
theorem prop_20290 :
    MorphismProperty.IsStableUnderComposition
      (IsOpenImmersion.presheaf : MorphismProperty (Scheme.{u}ᵒᵖ ⥤ Type u)) :=
  inferInstance

/-! ### A representability criterion -/

/-- thSz9ZHDK9o-20468 (5:41:08) [thm] (Representability criterion, sufficiency.) A Zariski sheaf
`F` with open immersions `h_{X_i} → F` that cover it (jointly locally surjective) is
representable by a scheme. Necessity: `prop_21454`. -/
theorem thm_20468 (F : Sheaf Scheme.zariskiTopology.{u} (Type u)) {ι : Type u}
    {X : ι → Scheme.{u}} (f : ∀ i, yoneda.obj (X i) ⟶ F.obj)
    (hf : ∀ i, IsOpenImmersion.presheaf (f i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)] :
    F.obj.IsRepresentable :=
  Scheme.LocalRepresentability.isRepresentable hf

/-- thSz9ZHDK9o-20672 (5:44:32) [prop] In the criterion one may take the `F_i` representable by
affine schemes, `F_i = h_{Spec R_i}`. -/
theorem prop_20672 (F : Sheaf Scheme.zariskiTopology.{u} (Type u)) {ι : Type u}
    {R : ι → CommRingCat.{u}} (f : ∀ i, yoneda.obj (Spec (R i)) ⟶ F.obj)
    (hf : ∀ i, IsOpenImmersion.presheaf (f i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)] :
    F.obj.IsRepresentable :=
  thm_20468 F f hf

/-- thSz9ZHDK9o-20995 (5:49:55) [prop] An open set of `Spec k'` is a union of open sets
`D(g_λ)` (and `h_{U'}` is then the supremum of the `h_{D(g_λ)}`, `prop_18065`). -/
theorem prop_20995 {k' : Type u} [CommRing k'] (U' : Opens (PrimeSpectrum k')) :
    ∃ Us ⊆ Set.range (@PrimeSpectrum.basicOpen k' _), U' = sSup Us :=
  Opens.isBasis_iff_cover.1 PrimeSpectrum.isBasis_basic_opens U'

/-- thSz9ZHDK9o-21254 (5:54:14) [prop] `Spec k' ∖ V(J)` represents the subfunctor
`B ↦ {u : k' → B | u(J)B = B}`: `Spec u` lands in it iff `u(J)` generates the unit ideal; if
`J = (g_λ)`, iff the `u(g_λ)` generate the unit ideal of `B`. -/
theorem prop_21254 {k' B : Type u} [CommRing k'] [CommRing B] (u : k' →+* B) (J : Ideal k') :
    (Set.range (PrimeSpectrum.comap u) ⊆ (PrimeSpectrum.zeroLocus (J : Set k'))ᶜ ↔
      J.map u = ⊤) ∧
    ∀ g : Set k', J = Ideal.span g → (J.map u = ⊤ ↔ Ideal.span (u '' g) = ⊤) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun g hg => by rw [hg, Ideal.map_span]⟩
  · by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    refine h ⟨⟨m, hm.isPrime⟩, rfl⟩ ?_
    intro x hx
    exact hle (Ideal.mem_map_of_mem u hx)
  · rintro _ ⟨p, rfl⟩ hp
    apply p.isPrime.ne_top
    rw [eq_top_iff, ← h, Ideal.map_le_iff_le_comap]
    exact hp

/-- thSz9ZHDK9o-21454 (5:57:34) [prop] For a scheme covered by affine opens `X_i`, the
`h_{X_i} → h_X` are open immersions of sheaves (`relative_map`), and they cover `h_X`: every
`S' → X` factors locally through some `X_i` (`prop_18065`). -/
theorem prop_21454 (X : Scheme.{u}) (i : X.affineCover.I₀) :
    IsOpenImmersion.presheaf (yoneda.map (X.affineCover.f i)) :=
  MorphismProperty.relative_map inferInstance

/-- thSz9ZHDK9o-21516 (5:58:36) [prop] If `F_j → F` is an open immersion, so is its base change
`F_i ∩ F_j → F_i` by `F_i → F` (`prop_20162`). -/
theorem prop_21516 {F Fi Fj : Scheme.{u}ᵒᵖ ⥤ Type u} (fi : Fi ⟶ F) (fj : Fj ⟶ F)
    (hj : IsOpenImmersion.presheaf fj) :
    IsOpenImmersion.presheaf (pullback.snd fj fi) :=
  have := prop_20162.{u}
  IsOpenImmersion.presheaf.pullback_snd _ _ hj

end

end Buffalo.AG.Part04
