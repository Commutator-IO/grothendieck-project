import Mathlib

/-!
# Buffalo, topos theory, part 1a: presheaves and sheaves on a space (4 April 1973)

Entries of `docs/buffalo-topos/index.tex` from « Presheaves and sheaves on a space » to « Limits
and colimits » (video `URU5jgTvjhU`, 0:03:26–1:54:21). The status of each entry is in
`docs/buffalo-topos/lean/Part01.json`.

Presheaves of sets on a space `X` are Mathlib's `X.Presheaf (Type u)`, functors
`(Opens X)ᵒᵖ ⥤ Type u`; sheaves are `TopCat.Sheaf (Type u) X`, the full subcategory of those
satisfying `TopCat.Presheaf.IsSheaf`. Most proofs below go through the unique-gluing form of the
sheaf condition, `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace Buffalo.Topos.Part01

noncomputable section

variable {X : TopCat.{u}}

/-! ## Presheaves and sheaves on a space -/

/-- URU5jgTvjhU-206 (0:03:26) [prop] The open sets `𝒪(X)`, ordered by inclusion, form a category:
`Hom(U,V)` is a singleton if `U ⊆ V`, empty otherwise. -/
theorem opens_hom (U V : Opens X) : Subsingleton (U ⟶ V) ∧ (Nonempty (U ⟶ V) ↔ U ≤ V) :=
  ⟨inferInstance, fun ⟨f⟩ => f.le, fun h => ⟨homOfLE h⟩⟩

/-- URU5jgTvjhU-335 (0:05:35) [def] A presheaf of sets on `X` is a functor `𝒪(X)ᵒᵖ → Set`. -/
example : X.Presheaf (Type u) = ((Opens X)ᵒᵖ ⥤ Type u) := rfl

/-- URU5jgTvjhU-466 (0:07:46) [def] A morphism of presheaves is a natural transformation. -/
example (F G : X.Presheaf (Type u)) : (F ⟶ G) = NatTrans F G := rfl

/-- URU5jgTvjhU-596 (0:09:56) [def] `F` is separated if, for every open covering `U = ⋃ Uᵢ`,
`F(U) → ∏ F(Uᵢ)` is injective. -/
def IsSeparated (F : X.Presheaf (Type u)) : Prop :=
  ∀ ⦃ι : Type u⦄ (U : ι → Opens X) (s t : F.obj (op (iSup U))),
    (∀ i, F.map (Opens.leSupr U i).op s = F.map (Opens.leSupr U i).op t) → s = t

/-- URU5jgTvjhU-859 (0:14:19) [def] `F` is a sheaf if, for every covering, `F(U)` is the equalizer
of `∏ F(Uᵢ) ⇉ ∏ F(Uᵢ ∩ Uⱼ)`: Mathlib's sheaf condition is equivalent to this one. -/
theorem isSheaf_iff_equalizer (F : X.Presheaf (Type u)) :
    F.IsSheaf ↔ F.IsSheafEqualizerProducts :=
  TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts F

/-- A sheaf is separated. -/
theorem IsSeparated.of_isSheaf {F : X.Presheaf (Type u)} (hF : F.IsSheaf) : IsSeparated F := by
  intro ι U s t h
  exact TopCat.Sheaf.eq_of_locally_eq ⟨F, hF⟩ U s t h

/-- URU5jgTvjhU-988 (0:16:28) [prop] The sheaves form a full subcategory of the presheaves. -/
def sheafToPresheaf_fullyFaithful :
    (sheafToPresheaf (Opens.grothendieckTopology X) (Type u)).FullyFaithful :=
  fullyFaithfulSheafToPresheaf _ _

/-! ## Examples of sheaves -/

/-- URU5jgTvjhU-1127 (0:18:47) [ex] For a set `E`, `U ↦ E^U` is a sheaf. -/
theorem maps_isSheaf (E : Type u) : (X.presheafToTypes fun _ => E).IsSheaf :=
  TopCat.Presheaf.toTypes_isSheaf X _

/-- URU5jgTvjhU-1254 (0:20:54) [def] A subpresheaf `G ⊆ F` is a family of subsets stable under the
restrictions: Mathlib's `Subfunctor`. -/
example (F : X.Presheaf (Type u)) (G : Subfunctor F) (U V : (Opens X)ᵒᵖ) (i : U ⟶ V) :
    G.obj U ⊆ F.map i ⁻¹' G.obj V :=
  G.map i

/-- URU5jgTvjhU-1452 (0:24:12) [prop] A subpresheaf of a separated presheaf is separated. -/
theorem IsSeparated.subfunctor {F : X.Presheaf (Type u)} (hF : IsSeparated F) (G : Subfunctor F) :
    IsSeparated (G.toFunctor : X.Presheaf (Type u)) := by
  intro ι U s t h
  apply Subtype.ext
  apply hF U
  intro i
  exact congrArg Subtype.val (h i)

/-- URU5jgTvjhU-1452 (0:24:12) [prop] A subpresheaf `G` of a sheaf `F` is a sheaf if and only if
membership of a section in `G` is a local property. -/
theorem subfunctor_isSheaf_iff {F : X.Presheaf (Type u)} (hF : F.IsSheaf) (G : Subfunctor F) :
    TopCat.Presheaf.IsSheaf (X := X) G.toFunctor ↔
      ∀ ⦃ι : Type u⦄ (U : ι → Opens X) (s : F.obj (op (iSup U))),
        (∀ i, F.map (Opens.leSupr U i).op s ∈ G.obj (op (U i))) → s ∈ G.obj (op (iSup U)) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types]
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types] at hF
  constructor
  · intro hG ι U s hs
    obtain ⟨t, ht, -⟩ := hG U (fun i => ⟨_, hs i⟩) (by
      intro i j
      apply Subtype.ext
      change F.map _ (F.map _ s) = F.map _ (F.map _ s)
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
      rfl)
    have : t.val = s := by
      obtain ⟨g, -, hg⟩ := hF U (fun i => F.map (Opens.leSupr U i).op s) (by
        intro i j
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
        rfl)
      rw [hg t.val (fun i => congrArg Subtype.val (ht i)), hg s (fun i => rfl)]
    exact this ▸ t.prop
  · intro hloc ι U sf hsf
    obtain ⟨s, hs, hu⟩ := hF U (fun i => (sf i).val) (fun i j => congrArg Subtype.val (hsf i j))
    refine ⟨⟨s, hloc U s (fun i => (hs i).symm ▸ (sf i).prop)⟩, fun i => Subtype.ext (hs i), ?_⟩
    intro t ht
    exact Subtype.ext (hu t.val (fun i => congrArg Subtype.val (ht i)))

/-- URU5jgTvjhU-1579 (0:26:19) [ex] For a topological space `E`, the continuous maps from open sets
of `X` to `E` form a subsheaf of `U ↦ E^U` (Mathlib's `TopCat.continuousLocal`). -/
def continuousSheaf (E : Type u) [TopologicalSpace E] : TopCat.Sheaf (Type u) X :=
  TopCat.subsheafToTypes (TopCat.continuousLocal X E)

/-- The local predicate « `f` is a continuous section of `p` ». -/
def sectionPred {E : Type u} [TopologicalSpace E] (p : E → X) :
    TopCat.LocalPredicate fun _ : X => E where
  pred {U} f := Continuous f ∧ ∀ x : U, p (f x) = x
  res {U V} i f h := ⟨(TopCat.continuousLocal X E).res i f h.1, fun x => h.2 (i x)⟩
  locality {U} f w := by
    refine ⟨(TopCat.continuousLocal X E).locality f fun x => ?_, fun x => ?_⟩
    · obtain ⟨V, m, i, h⟩ := w x
      exact ⟨V, m, i, h.1⟩
    · obtain ⟨V, m, i, h⟩ := w x
      exact h.2 ⟨x, m⟩

/-- URU5jgTvjhU-1769 (0:29:29) [ex] For `p : E → X` continuous, the continuous sections of `p`
over the open sets form a sheaf. -/
def sectionSheaf {E : Type u} [TopologicalSpace E] (p : E → X) : TopCat.Sheaf (Type u) X :=
  TopCat.subsheafToTypes (sectionPred p)

/-- URU5jgTvjhU-1965 (0:32:45) [prop] The sheaf of continuous maps to `E` is isomorphic to the sheaf
of sections of the second projection `E × X → X`. -/
def continuousIsoSections (E : Type u) [TopologicalSpace E] :
    (continuousSheaf (X := X) E).obj ≅ (sectionSheaf (Prod.snd : E × X → X)).obj :=
  NatIso.ofComponents
    (fun U => Equiv.toIso
      { toFun := fun f => ⟨fun x => (f.1 x, x.1), ⟨f.2.prodMk continuous_subtype_val, fun _ => rfl⟩⟩
        invFun := fun s => ⟨fun x => (s.1 x).1, continuous_fst.comp s.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun s => by
          apply Subtype.ext
          funext x
          exact Prod.ext rfl (s.2.2 x).symm })
    (fun _ => rfl)

/-- URU5jgTvjhU-2164 (0:36:04) [ex] `U ↦ {subsets of U}`, restriction by intersection, is a sheaf
(a subset of `U` being a map `U → Prop`). -/
theorem subsets_isSheaf : (X.presheafToTypes fun _ => Prop).IsSheaf :=
  TopCat.Presheaf.toTypes_isSheaf X _

/-! ## Sheaves of sections and the case of a point -/

/-- The sheaf of sections of a space over `X`, as a presheaf. -/
noncomputable abbrev sectionsOver (E : Over X) : X.Presheaf (Type u) :=
  (sectionSheaf (fun e : E.left => E.hom.hom e)).obj

/-- URU5jgTvjhU-2487 (0:41:27) [prop] The sheaf of sections defines a functor from spaces over `X`
to sheaves on `X`, `f ↦ (s ↦ f ∘ s)` (here with values in presheaves; each value is a sheaf by
`sectionSheaf`). -/
noncomputable def sectionsFunctor : Over X ⥤ X.Presheaf (Type u) where
  obj E := sectionsOver E
  map {E E'} g :=
    { app := fun U => ↾fun s => ⟨fun x => g.left.hom (s.1 x),
        ⟨g.left.hom.continuous.comp s.2.1, fun x => by
          have h := ConcreteCategory.congr_hom (Over.w g) (s.1 x)
          simp only [ConcreteCategory.comp_apply] at h
          exact h.trans (s.2.2 x)⟩⟩
      naturality := fun _ _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- URU5jgTvjhU-2680 (0:44:40) [cex] Over a point the functor of sections is the forgetful functor
from spaces to sets, which is not full (hence not fully faithful): `decide : Prop → Bool` is a map
of sets from the Sierpiński space to the discrete space `Bool` that is not continuous. -/
theorem forget_topCat_not_full : ¬ (forget TopCat.{0}).Full := by
  intro hfull
  let d : Prop → Bool := fun p => @decide p (Classical.dec p)
  obtain ⟨g, hg⟩ := (forget TopCat.{0}).map_surjective
    (X := TopCat.of Prop) (Y := TopCat.of Bool) (↾d)
  have hgd : ∀ p, g.hom p = d p := fun p => congrArg (fun φ => φ p) hg
  have hc : Continuous d := by
    have : (fun p => g.hom p) = d := funext hgd
    exact this ▸ g.hom.continuous
  have hopen : IsOpen (d ⁻¹' {false}) := (isOpen_discrete _).preimage hc
  have hmem : d ⁻¹' {false} ∈ 𝓝 False := hopen.mem_nhds (by simp [d])
  rw [nhds_false, Filter.mem_top] at hmem
  have : True ∈ d ⁻¹' {false} := hmem ▸ Set.mem_univ True
  simp [d] at this

/-- URU5jgTvjhU-2811 (0:46:51) [def] For `U` open, `Γ_U : F ↦ F(U)` is a functor `Sh(X) → Set`. -/
def sectionsOn (U : Opens X) : TopCat.Sheaf (Type u) X ⥤ Type u :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)

/-! ## Limits and colimits -/

/-- URU5jgTvjhU-5826 (1:37:06) [def] The dual notions: an initial object of `C` is a terminal
object of `Cᵒᵖ` (likewise coproducts, coequalizers, pushouts: Mathlib's `coprod`, `coequalizer`,
`pushout`). -/
example {C : Type*} [Category C] {I : C} (h : IsInitial I) : IsTerminal (op I) := h.op

/-- URU5jgTvjhU-5888 (1:38:08) [prop] In `Set`, the initial object is `∅` and coproducts are
disjoint unions. -/
theorem types_initial_coproduct {J : Type u} (F : J → Type u) :
    Nonempty (IsInitial (PEmpty.{u + 1})) ∧
      (Types.coproductColimitCocone.{u, u} F).cocone.pt = Σ j, F j :=
  ⟨⟨Types.isInitialPEmpty⟩, rfl⟩

/-- URU5jgTvjhU-5888 (1:38:08) [prop] In `Set`, the coequalizer of `f, g : E ⇉ F` (Mathlib's
`Types.coequalizerColimit`, on `Function.Coequalizer f g`) is the quotient of `F` by the
equivalence relation generated by the image of `E` in `F × F`. -/
theorem types_coequalizer {E F : Type u} (f g : E → F) (a b : F) :
    (Types.coequalizerColimit (↾f) (↾g)).cocone.pt = Function.Coequalizer f g ∧
    (Function.Coequalizer.mk f g a = Function.Coequalizer.mk f g b ↔
      Relation.EqvGen (fun x y => ∃ e, f e = x ∧ g e = y) a b) := by
  refine ⟨rfl, ?_⟩
  have hrel : Function.Coequalizer.Rel f g = fun x y => ∃ e, f e = x ∧ g e = y := by
    ext x y
    constructor
    · rintro ⟨e⟩; exact ⟨e, rfl, rfl⟩
    · rintro ⟨e, rfl, rfl⟩; exact ⟨e⟩
  rw [← hrel]
  exact ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

/-- URU5jgTvjhU-6015 (1:40:15) [ex] In groups the coproduct is the free product (universal property
of `Monoid.CoprodI`); the free product of copies of `ℤ` indexed by `ι` is the free group on `ι`. -/
def coprodI_int_equiv_freeGroup (ι : Type u) :
    Monoid.CoprodI (fun _ : ι => Multiplicative ℤ) ≃* FreeGroup ι :=
  MonoidHom.toMulEquiv
    (Monoid.CoprodI.lift fun i => zpowersHom _ (FreeGroup.of i))
    (FreeGroup.lift fun i => Monoid.CoprodI.of (i := i) (Multiplicative.ofAdd 1))
    (Monoid.CoprodI.ext_hom _ _ fun i => MonoidHom.ext_mint (by simp))
    (FreeGroup.ext_hom _ _ fun i => by simp)

/-- URU5jgTvjhU-6015 (1:40:15) [ex] The free product is the coproduct of groups. -/
def coprodI_universal {ι : Type u} (G : ι → Type u) [∀ i, Group (G i)] (H : Type u) [Group H] :
    (∀ i, G i →* H) ≃ (Monoid.CoprodI G →* H) :=
  Monoid.CoprodI.lift

/-- URU5jgTvjhU-6082 (1:41:22) [rem] For groups, limits are computed on the underlying sets
(the forgetful functor preserves limits) but colimits are not: the initial group is not sent to the
initial (empty) set. -/
theorem grp_forget_limits_not_colimits :
    Nonempty (PreservesLimits (forget GrpCat.{u})) ∧
      ¬ Nonempty (IsInitial ((forget GrpCat.{u}).obj (⊥_ GrpCat.{u}))) := by
  refine ⟨⟨inferInstance⟩, fun ⟨h⟩ => ?_⟩
  exact (h.to PEmpty.{u + 1} (1 : (⊥_ GrpCat.{u}))).elim

/-- URU5jgTvjhU-6212 (1:43:32) [prop] If `S` has limits of shape `J`, so has `Hom(Cᵒᵖ, S)`, and they
are computed argumentwise (evaluation preserves them); likewise for colimits. -/
theorem functor_limits {C S J : Type*} [Category C] [Category S] [Category J]
    [HasLimitsOfShape J S] [HasColimitsOfShape J S] (c : Cᵒᵖ) :
    HasLimitsOfShape J (Cᵒᵖ ⥤ S) ∧ Nonempty (PreservesLimitsOfShape J ((evaluation Cᵒᵖ S).obj c)) ∧
      HasColimitsOfShape J (Cᵒᵖ ⥤ S) ∧
        Nonempty (PreservesColimitsOfShape J ((evaluation Cᵒᵖ S).obj c)) :=
  ⟨inferInstance, ⟨inferInstance⟩, inferInstance, ⟨inferInstance⟩⟩

/-- URU5jgTvjhU-6275 (1:44:35) [prop] The category opposite to `Hom(Cᵒᵖ, S)` is `Hom(C, Sᵒᵖ)`. -/
def functor_op_equiv (C S : Type*) [Category C] [Category S] : (Cᵒᵖ ⥤ S)ᵒᵖ ≌ (C ⥤ Sᵒᵖ) :=
  (Functor.opUnopEquiv Cᵒᵖ S).trans (opOpEquivalence C).congrLeft

/-- URU5jgTvjhU-6401 (1:46:41) [prop] Presheaves on `X` admit all colimits, computed open set by
open set. -/
theorem presheaf_colimits (U : Opens X) :
    HasColimits (X.Presheaf (Type u)) ∧
      Nonempty (PreservesColimits ((evaluation (Opens X)ᵒᵖ (Type u)).obj (op U))) :=
  ⟨inferInstance, ⟨inferInstance⟩⟩

/-- URU5jgTvjhU-6730 (1:52:10) [prop] For every sheaf `F`, `F(∅)` is a singleton. -/
theorem sheaf_empty_unique (F : TopCat.Sheaf (Type u) X) : Nonempty (Unique (F.obj.obj (op ⊥))) :=
  ⟨Types.isTerminalEquivUnique _ (TopCat.Sheaf.isTerminalOfEmpty F)⟩

/-- URU5jgTvjhU-6602 (1:50:02) [ex] The constant presheaf with two elements (the coproduct, taken
in presheaves, of the terminal object with itself) is not a sheaf. -/
theorem const_bool_not_isSheaf :
    ¬ TopCat.Presheaf.IsSheaf (X := X) ((Functor.const (Opens X)ᵒᵖ).obj (ULift.{u} Bool)) := by
  intro h
  obtain ⟨hu⟩ := sheaf_empty_unique ⟨_, h⟩
  exact absurd (hu.uniq ⟨true⟩ ▸ (hu.uniq ⟨false⟩).symm) (by simp)

/-- URU5jgTvjhU-6797 (1:53:17) [ex] The initial presheaf `U ↦ ∅` is not a sheaf. -/
theorem const_empty_not_isSheaf :
    ¬ TopCat.Presheaf.IsSheaf (X := X) ((Functor.const (Opens X)ᵒᵖ).obj PEmpty.{u + 1}) := by
  intro h
  obtain ⟨hu⟩ := sheaf_empty_unique ⟨_, h⟩
  exact hu.default.elim

/-- URU5jgTvjhU-6469 (1:47:49) [cex] `Sh(X)` is not stable in presheaves under the usual colimits:
neither the initial presheaf nor the presheaf coproduct `1 ⊔ 1` is a sheaf, on any space. -/
theorem sheaves_not_stable_colimits :
    ¬ TopCat.Presheaf.IsSheaf (X := X) ((Functor.const (Opens X)ᵒᵖ).obj PEmpty.{u + 1}) ∧
      ¬ TopCat.Presheaf.IsSheaf (X := X) ((Functor.const (Opens X)ᵒᵖ).obj (ULift.{u} Bool)) :=
  ⟨const_empty_not_isSheaf, const_bool_not_isSheaf⟩

/-! ## The associated sheaf -/

/-- URU5jgTvjhU-7053 (1:57:33) [def] The sheaf associated to `P` is a sheaf `aP` with `P → aP`
universal among morphisms from `P` to sheaves (Mathlib's `presheafToSheaf`, `toSheafify`). -/
def sheafifyUniversal (P : X.Presheaf (Type u)) (F : TopCat.Sheaf (Type u) X) :
    ((presheafToSheaf (Opens.grothendieckTopology X) (Type u)).obj P ⟶ F) ≃ (P ⟶ F.obj) :=
  (sheafificationAdjunction _ _).homEquiv P F

/-- URU5jgTvjhU-7116 (1:58:36) [thm] Every presheaf admits an associated sheaf (unique up to unique
isomorphism, as the left adjoint of the inclusion). -/
theorem hasSheafify : HasSheafify (Opens.grothendieckTopology X) (Type u) := inferInstance

/-- URU5jgTvjhU-7310 (2:01:50) [prop] `Sh(X)` admits all colimits, and the associated-sheaf functor
preserves them: the colimit of sheaves is the sheaf associated to the presheaf colimit. -/
theorem sheaf_colimits :
    (∀ (K : Type u) [SmallCategory K], HasColimitsOfShape K (Sheaf (Opens.grothendieckTopology X) (Type u))) ∧
      Nonempty (PreservesColimits (presheafToSheaf (Opens.grothendieckTopology X) (Type u))) := by
  have := hasSheafify (X := X)
  exact ⟨fun K _ => inferInstance, ⟨inferInstance⟩⟩

/-- URU5jgTvjhU-7310 (2:01:50) [prop] A presheaf and its associated sheaf have the same stalks. -/
def sheafify_stalk (F : X.Presheaf (Type u)) (x : X) : TopCat.Presheaf.stalk F.sheafify.obj x ≅ F.stalk x :=
  TopCat.Presheaf.sheafifyStalkIso F x

/-- A continuous, open, locally injective map is a local homeomorphism (« étalé »). -/
theorem isLocalHomeomorph_of_isOpenMap {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} (hc : Continuous f) (ho : IsOpenMap f) (hi : IsLocallyInjective f) :
    IsLocalHomeomorph f := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro x
  obtain ⟨U, hU, hx, hinj⟩ := hi x
  refine ⟨U, hU.mem_nhds hx, ?_⟩
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap (hc.comp continuous_subtype_val)
    (fun a b h => Subtype.ext (hinj a.2 b.2 h)) ?_
  exact ho.comp hU.isOpenMap_subtype_val

/-- URU5jgTvjhU-7450 (2:04:10) [prop] The disjoint topological sum of a family of étalé spaces over
`X` is étalé over `X`. -/
theorem sigma_isLocalHomeomorph {B ι : Type*} [TopologicalSpace B] {E : ι → Type*}
    [∀ i, TopologicalSpace (E i)] (p : ∀ i, E i → B) (hp : ∀ i, IsLocalHomeomorph (p i)) :
    IsLocalHomeomorph fun z : Σ i, E i => p z.1 z.2 := by
  refine isLocalHomeomorph_of_isOpenMap (continuous_sigma fun i => (hp i).continuous)
    (isOpenMap_sigma.2 fun i => (hp i).isOpenMap) ?_
  rintro ⟨i, e⟩
  obtain ⟨U, hU, he, hinj⟩ := (hp i).isLocallyInjective e
  refine ⟨Sigma.mk i '' U, isOpenMap_sigmaMk _ hU, ⟨e, he, rfl⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
  rw [hinj ha hb h]

/-- URU5jgTvjhU-7516 (2:05:16) [prop] For étalé `q : G → X` and two maps `a, b : F ⇉ G` over `X`
(continuous and open, as maps of étalé spaces are), the quotient `G/R` of `G` by the equivalence
relation generated by `a(e) ~ b(e)`, with the quotient topology, is étalé over `X`. -/
theorem quot_isLocalHomeomorph {F G B : Type*} [TopologicalSpace F] [TopologicalSpace G]
    [TopologicalSpace B] (q : G → B) (hq : IsLocalHomeomorph q) (a b : F → G)
    (hac : Continuous a) (hbc : Continuous b) (ha : IsOpenMap a) (hb : IsOpenMap b)
    (hab : ∀ e, q (a e) = q (b e)) :
    IsLocalHomeomorph (Quot.lift q (by rintro _ _ ⟨e⟩; exact hab e) :
      Quot (Function.Coequalizer.Rel a b) → B) := by
  set r := Function.Coequalizer.Rel a b
  set qbar := (Quot.lift q (by rintro _ _ ⟨e⟩; exact hab e) : Quot r → B) with hqbar
  let mk : G → Quot r := Quot.mk r
  let T : Set G → Set G := fun W => W ∪ b '' (a ⁻¹' W) ∪ a '' (b ⁻¹' W)
  have hT : ∀ W, IsOpen W → IsOpen (T W) := fun W hW =>
    (hW.union (hb _ (hW.preimage hac))).union (ha _ (hW.preimage hbc))
  have hTn : ∀ n W, IsOpen W → IsOpen (T^[n] W) := by
    intro n
    induction n with
    | zero => exact fun W hW => hW
    | succ n ih => exact fun W hW => by rw [Function.iterate_succ_apply']; exact hT _ (ih W hW)
  have claim : ∀ g g', Relation.EqvGen r g g' →
      ∃ n, ∀ W, (g ∈ W → g' ∈ T^[n] W) ∧ (g' ∈ W → g ∈ T^[n] W) := by
    intro g g' h
    induction h with
    | rel x y hxy =>
      cases hxy with
      | intro e => exact ⟨1, fun W => ⟨fun hx => Or.inl (Or.inr ⟨e, hx, rfl⟩),
          fun hy => Or.inr ⟨e, hy, rfl⟩⟩⟩
    | refl x => exact ⟨0, fun W => ⟨id, id⟩⟩
    | symm x y _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, fun W => (hn W).symm⟩
    | trans x y z _ _ ih₁ ih₂ =>
      obtain ⟨n, hn⟩ := ih₁
      obtain ⟨m, hm⟩ := ih₂
      refine ⟨m + n, fun W => ⟨fun hx => ?_, fun hz => ?_⟩⟩
      · rw [Function.iterate_add_apply]; exact (hm _).1 ((hn W).1 hx)
      · rw [add_comm, Function.iterate_add_apply]; exact (hn _).2 ((hm W).2 hz)
  have sat : ∀ W : Set G, mk ⁻¹' (mk '' W) = ⋃ n, T^[n] W := by
    intro W
    ext g'
    constructor
    · rintro ⟨g, hg, hgg'⟩
      obtain ⟨n, hn⟩ := claim g g' (Quot.eqvGen_exact hgg')
      exact Set.mem_iUnion.2 ⟨n, (hn W).1 hg⟩
    · intro h
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
      have step : ∀ S, S ⊆ mk ⁻¹' (mk '' W) → T S ⊆ mk ⁻¹' (mk '' W) := by
        rintro S hS x ((hx | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩)
        · exact hS hx
        · obtain ⟨g, hg, hge⟩ := hS he
          exact ⟨g, hg, hge.trans (Quot.sound ⟨e⟩)⟩
        · obtain ⟨g, hg, hge⟩ := hS he
          exact ⟨g, hg, hge.trans (Quot.sound ⟨e⟩).symm⟩
      have : ∀ k, T^[k] W ⊆ mk ⁻¹' (mk '' W) := by
        intro k
        induction k with
        | zero => exact fun x hx => ⟨x, hx, rfl⟩
        | succ k ih => rw [Function.iterate_succ_apply']; exact step _ ih
      exact this n hn
  have mk_open : IsOpenMap mk := fun W hW => by
    rw [← isQuotientMap_quot_mk.isOpen_preimage, sat]
    exact isOpen_iUnion fun n => hTn n W hW
  refine isLocalHomeomorph_of_isOpenMap (continuous_quot_lift _ hq.continuous) ?_ ?_
  · intro V hV
    have : qbar '' V = q '' (mk ⁻¹' V) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        induction z using Quot.ind with
        | mk g => exact ⟨g, hz, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨mk g, hg, rfl⟩
    rw [this]
    exact hq.isOpenMap _ (hV.preimage continuous_quot_mk)
  · intro z
    induction z using Quot.ind with
    | mk g =>
      obtain ⟨U, hU, hg, hinj⟩ := hq.isLocallyInjective g
      refine ⟨mk '' U, mk_open U hU, ⟨g, hg, rfl⟩, ?_⟩
      rintro _ ⟨u₁, hu₁, rfl⟩ _ ⟨u₂, hu₂, rfl⟩ h
      exact congrArg mk (hinj hu₁ hu₂ h)

/-- URU5jgTvjhU-7642 (2:07:22) [prop] Coproducts and coequalizers suffice to construct all
colimits. -/
theorem colimits_of_coproducts_coequalizers {C : Type*} [Category C] [HasCoproducts.{u} C]
    [HasCoequalizers C] : HasColimitsOfSize.{u, u} C :=
  has_colimits_of_hasCoequalizers_and_coproducts

/-! ## Exactness properties of sheaves -/

/-- URU5jgTvjhU-7960 (2:12:40) [prop] In a category of presheaves of sets, limits and colimits are
computed argumentwise; in particular a morphism is an epimorphism if and only if it is surjective
on every argument. -/
theorem presheaf_epi_iff {C : Type u} [SmallCategory C] {F G : Cᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    Epi f ↔ ∀ c, Function.Surjective (f.app c) := by
  rw [NatTrans.epi_iff_epi_app]
  exact forall_congr' fun c => epi_iff_surjective _

/-- URU5jgTvjhU-8025 (2:13:45) [prop] The associated-sheaf functor `a` is left adjoint to the
inclusion; hence it commutes with colimits. -/
theorem sheafify_adjoint :
    Nonempty (presheafToSheaf (Opens.grothendieckTopology X) (Type u) ⊣
      sheafToPresheaf (Opens.grothendieckTopology X) (Type u)) ∧
      Nonempty (PreservesColimits (presheafToSheaf (Opens.grothendieckTopology X) (Type u))) :=
  ⟨⟨sheafificationAdjunction _ _⟩, ⟨inferInstance⟩⟩

/-- URU5jgTvjhU-8089 (2:14:49) [thm] The associated-sheaf functor is left exact. -/
theorem sheafify_leftExact :
    Nonempty (PreservesFiniteLimits (presheafToSheaf (Opens.grothendieckTopology X) (Type u))) :=
  ⟨inferInstance⟩

/-- URU5jgTvjhU-8672 (2:24:32) [prop] In `Sh(X)`, (finite) coproducts are stable under base change
and disjoint: `Sh(X)` is finitary extensive. -/
theorem sheaf_finitaryExtensive : FinitaryExtensive (Sheaf (Opens.grothendieckTopology X) (Type u)) :=
  inferInstance

/-! ## Quotients and equivalence relations -/

/-- URU5jgTvjhU-8863 (2:27:43) [def] A quotient object of `F` is an epimorphism out of `F` up to
isomorphism under `F`, i.e. a subobject of `F` in the opposite category. -/
abbrev QuotientObject {C : Type*} [Category C] (F : C) := Subobject (op F)

/-- URU5jgTvjhU-8923 (2:28:43) [prop] For every morphism `f : F → G` of presheaves, the fibre product
`F ×_G F ⊆ F × F`, computed section by section, is an equivalence relation on each `F(U)`. -/
theorem kernelPair_equivalence {F G : X.Presheaf (Type u)} (f : F ⟶ G) (U : (Opens X)ᵒᵖ) :
    Equivalence fun a b : F.obj U => f.app U a = f.app U b :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- URU5jgTvjhU-8987 (2:29:47) [prop] The coequalizer of `R ⇉ F` is a quotient of `F`
(an epimorphism). -/
theorem coequalizer_epi {C : Type*} [Category C] {R F : C} (r₁ r₂ : R ⟶ F)
    [HasCoequalizer r₁ r₂] : Epi (coequalizer.π r₁ r₂) :=
  inferInstance

/-- URU5jgTvjhU-9052 (2:30:52) [def] A relation `r₁, r₂ : R ⇉ F` is effective if it is the kernel
pair of its quotient `F → F/R`. (An effective quotient is Mathlib's `EffectiveEpi`.) -/
def IsEffectiveRelation {C : Type*} [Category C] {R F : C} (r₁ r₂ : R ⟶ F)
    [HasCoequalizer r₁ r₂] : Prop :=
  Nonempty (IsKernelPair (coequalizer.π r₁ r₂) r₁ r₂)

/-- URU5jgTvjhU-9117 (2:31:57) [prop] In `Sh(X)`, as in `Set`, quotients are effective: every
epimorphism is regular (the effectivity of equivalence relations is not formalised). -/
theorem sheaf_isRegularEpiCategory :
    IsRegularEpiCategory (Sheaf (Opens.grothendieckTopology X) (Type u)) :=
  inferInstance

end

end Buffalo.Topos.Part01
