import Buffalo.Topos.Part03b

/-!
# Buffalo, topos theory, part 3c: sober spaces, ordered categories, very dense subsets (4 June 1973)

Entries of `docs/buffalo-topos/index.tex` lines 390–535 on sober spaces and generic points, the
Zariski-type topologies, tensor products of sheaves of modules, algebras of finite presentation,
points of presheaf topoi, the topoi of ordered categories, very dense subsets, the equivariant
topoi `Top(X, G)`, and localization (video `PqCQM3Pcl6Q`, 0:39:21 and 1:55:37–3:22:52). The status of
each entry is in `docs/buffalo-topos/lean/Part03.json`.
-/

universe w u

open CategoryTheory Limits TopologicalSpace Opposite Topology TypeCat GrothendieckTopology

namespace Buffalo.Topos.Part03

noncomputable section

/-! ## Sober spaces -/

/-- PqCQM3Pcl6Q-6937 (1:55:37) [def] Sober: every irreducible closed subset has exactly one generic
point (Mathlib: `QuasiSober` and `T0Space`). -/
theorem sober_iff (X : Type*) [TopologicalSpace X] :
    (QuasiSober X ∧ T0Space X) ↔
      ∀ S : Set X, IsIrreducible S → IsClosed S → ∃! x, IsGenericPoint x S := by
  constructor
  · rintro ⟨_, _⟩ S hS hSc
    obtain ⟨x, hx⟩ := QuasiSober.sober hS hSc
    exact ⟨x, hx, fun y hy => hy.eq hx⟩
  · intro h
    refine ⟨⟨fun hS hSc => (h _ hS hSc).exists⟩, ?_⟩
    rw [t0Space_iff_inseparable]
    intro x y hxy
    obtain ⟨z, -, hz⟩ := h (closure {x}) isIrreducible_singleton.closure isClosed_closure
    have hy : IsGenericPoint y (closure {x}) := (inseparable_iff_closure_eq.1 hxy).symm
    exact (hz x isGenericPoint_closure).trans (hz y hy).symm

/-- PqCQM3Pcl6Q-7188 (1:59:48) [ex] Hausdorff spaces and schemes are sober. -/
theorem t2_sober (X : Type*) [TopologicalSpace X] [T2Space X] : QuasiSober X ∧ T0Space X :=
  ⟨inferInstance, inferInstance⟩

theorem scheme_sober (X : AlgebraicGeometry.Scheme) : QuasiSober X ∧ T0Space X :=
  ⟨inferInstance, inferInstance⟩

/-- PqCQM3Pcl6Q-7248 (2:00:48) [ex] In a topological group the closure of a point is a translate
of the closure of the unit. -/
theorem closure_singleton_eq (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (g : G) : closure {g} = (g * ·) '' closure {1} := by
  have := (Homeomorph.mulLeft g).image_closure {1}
  simp only [Set.image_singleton, Homeomorph.coe_mulLeft, mul_one] at this
  exact this.symm

/-- ... the separated quotient `G / closure {1}` is Hausdorff, hence sober. -/
theorem separationQuotient_sober (G : Type*) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    T2Space (SeparationQuotient G) ∧ QuasiSober (SeparationQuotient G) :=
  ⟨inferInstance, inferInstance⟩

/-- PqCQM3Pcl6Q-5819 (1:36:59) [def] A map out of a sum of spaces is continuous iff its
restrictions are; each summand is open. -/
theorem sigma_universal {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {Y : Type*}
    [TopologicalSpace Y] (f : Sigma X → Y) :
    Continuous f ↔ ∀ i, Continuous fun a => f ⟨i, a⟩ := continuous_sigma_iff

theorem sigma_open {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (i : ι) :
    IsOpen (Set.range (Sigma.mk i : X i → Sigma X)) := isOpen_range_sigmaMk

/-- PqCQM3Pcl6Q-5628 (1:33:48) [cex] The trivial group is initial and final in groups, yet a
non-trivial group maps to it: strict initiality fails. -/
theorem grp_not_strict : IsZero (GrpCat.of PUnit.{1}) ∧
    ∃ f : GrpCat.of (Multiplicative (ZMod 2)) ⟶ GrpCat.of PUnit.{1}, ¬ IsIso f := by
  refine ⟨GrpCat.isZero_of_subsingleton _, ⟨GrpCat.ofHom 1, fun h => ?_⟩⟩
  have hb := (isIso_iff_bijective ((forget GrpCat).map (GrpCat.ofHom 1 :
    GrpCat.of (Multiplicative (ZMod 2)) ⟶ GrpCat.of PUnit.{1}))).1 inferInstance
  have := hb.1 (a₁ := Multiplicative.ofAdd (1 : ZMod 2)) (a₂ := 1) (Subsingleton.elim _ _)
  exact absurd (congrArg Multiplicative.toAdd this) (by decide)

section Zariski

variable {R : Type*} [CommRing R]

/-- PqCQM3Pcl6Q-7368 (2:02:48) [def] The Zariski-type topology on a set `T` of ideals: the basic
closed sets are the `V(S) = {I ∈ T | S ⊆ I}`, the closed sets their finite unions' intersections
(so the complements of the `V(S)` form a subbasis of opens). -/
@[reducible] def zariskiType (T : Set (Ideal R)) : TopologicalSpace T :=
  TopologicalSpace.generateFrom {U | ∃ S : Set R, U = {I : T | ¬ S ⊆ (I : Ideal R)}}

/-- PqCQM3Pcl6Q-7431 (2:03:51) [rem] In such a space `J ∈ closure {I}` iff `I ⊆ J`: specialization
is inclusion, an order. -/
theorem zariskiType_specializes (T : Set (Ideal R)) (I J : T) :
    @Specializes T (zariskiType T) I J ↔ (I : Ideal R) ≤ J := by
  let _ : TopologicalSpace T := zariskiType T
  rw [specializes_iff_pure, zariskiType, TopologicalSpace.nhds_generateFrom]
  simp only [le_iInf_iff, Filter.le_principal_iff, Filter.mem_pure]
  constructor
  · intro h x hx
    by_contra hxJ
    have := h {K : T | ¬ ({x} : Set R) ⊆ (K : Ideal R)} ⟨by simpa using hxJ, {x}, rfl⟩
    exact this (by simpa using hx)
  · rintro h U ⟨hJ, S, rfl⟩ hI
    exact hJ (hI.trans h)

/-- ... and it need not be symmetric: `⊥ ⊆ ⊤` in `ℤ` but not conversely. -/
theorem zariskiType_not_symm :
    @Specializes (Set.univ : Set (Ideal ℤ)) (zariskiType _) ⟨⊥, trivial⟩ ⟨⊤, trivial⟩ ∧
      ¬ @Specializes (Set.univ : Set (Ideal ℤ)) (zariskiType _) ⟨⊤, trivial⟩ ⟨⊥, trivial⟩ := by
  rw [zariskiType_specializes, zariskiType_specializes]
  exact ⟨bot_le, fun h => bot_ne_top (le_bot_iff.1 h).symm⟩

end Zariski

section MaxSpec

open Polynomial

variable (K : Type u) [Field K] [Infinite K]

/-- The maximal ideal `(X - a)` of `K[X]`, as the kernel of evaluation at `a`. -/
def evalPoint (a : K) : MaximalSpectrum K[X] :=
  ⟨RingHom.ker (evalRingHom a),
    RingHom.ker_isMaximal_of_surjective _ fun b => ⟨C b, eval_C⟩⟩

omit [Infinite K] in
theorem mem_evalPoint (a : K) (p : K[X]) : p ∈ (evalPoint K a).asIdeal ↔ p.eval a = 0 :=
  RingHom.mem_ker

/-- PqCQM3Pcl6Q-7063 (1:57:43) [ex] For `K` infinite, the maximal spectrum of `K[X]` (Serre's
variety, the affine line) is irreducible... -/
theorem maxSpec_irreducible : IsIrreducible (Set.univ : Set (MaximalSpectrum K[X])) := by
  refine ⟨⟨evalPoint K 0, trivial⟩, fun u v hu hv ⟨x, _, hxu⟩ ⟨y, _, hyv⟩ => ?_⟩
  obtain ⟨t, ht, rfl⟩ := isOpen_induced_iff.1 hu
  obtain ⟨t', ht', rfl⟩ := isOpen_induced_iff.1 hv
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isOpen_iff _).1 ht
  obtain ⟨s', hs'⟩ := (PrimeSpectrum.isOpen_iff _).1 ht'
  have mem : ∀ {t : Set (PrimeSpectrum K[X])} {s : Set K[X]}, tᶜ = PrimeSpectrum.zeroLocus s →
      ∀ m : PrimeSpectrum K[X], m ∈ t ↔ ¬ s ⊆ m.asIdeal := fun {t s} h m => by
    rw [← not_iff_not, not_not, ← Set.mem_compl_iff, h, PrimeSpectrum.mem_zeroLocus]
  rw [Set.mem_preimage, mem hs] at hxu
  rw [Set.mem_preimage, mem hs'] at hyv
  obtain ⟨f, hfs, hfx⟩ := Set.not_subset.1 hxu
  obtain ⟨g, hgs, hgy⟩ := Set.not_subset.1 hyv
  have hf : f ≠ 0 := fun h => hfx (h ▸ Submodule.zero_mem _)
  have hg : g ≠ 0 := fun h => hgy (h ▸ Submodule.zero_mem _)
  obtain ⟨a, ha⟩ : ∃ a, (f * g).eval a ≠ 0 := by
    by_contra h
    push Not at h
    exact mul_ne_zero hf hg (Polynomial.funext (by simpa using h))
  rw [eval_mul] at ha
  refine ⟨evalPoint K a, trivial, ?_, ?_⟩
  · rw [Set.mem_preimage, mem hs]
    exact fun h => left_ne_zero_of_mul ha ((mem_evalPoint K a f).1 (h hfs))
  · rw [Set.mem_preimage, mem hs']
    exact fun h => right_ne_zero_of_mul ha ((mem_evalPoint K a g).1 (h hgs))

omit [Infinite K] in
/-- ... but has no generic point, so it is not sober. -/
theorem maxSpec_no_genericPoint (x : MaximalSpectrum K[X]) :
    ¬ IsGenericPoint x Set.univ := by
  intro h
  rw [isGenericPoint_def, closure_singleton] at h
  have h0 : evalPoint K 0 ∈ ({x} : Set _) := h ▸ trivial
  have h1 : evalPoint K 1 ∈ ({x} : Set _) := h ▸ trivial
  rw [Set.mem_singleton_iff] at h0 h1
  have : X ∈ (evalPoint K 0).asIdeal := (mem_evalPoint K 0 X).2 (by simp)
  rw [h0, ← h1, mem_evalPoint] at this
  simp at this

theorem maxSpec_not_quasiSober : ¬ QuasiSober (MaximalSpectrum K[X]) := fun h =>
  let ⟨x, hx⟩ := h.sober (maxSpec_irreducible K) isClosed_univ
  maxSpec_no_genericPoint K x hx

end MaxSpec

/-- Sheaves for equal topologies. -/
def sheafEquivOfEq {C : Type*} [Category C] {A : Type*} [Category A] {J₁ J₂ : GrothendieckTopology C}
    (h : J₁ = J₂) : Sheaf J₁ A ≌ Sheaf J₂ A := by subst h; exact CategoryTheory.Equivalence.refl

variable {X : Type u} [TopologicalSpace X]

/-- The comparison lemma for a basis of minimal neighbourhoods: let `G : C → Opens X` be fully
faithful, such that each `G c` is the smallest open neighbourhood of a point `pt c` and the `G c`
form a basis of opens. Then `Sh(X) ≃ Ĉ`. -/
def sheafEquivPresheafOfMinimalBasis {C : Type u} [SmallCategory C] (G : C ⥤ Opens X)
    [G.Full] [G.Faithful] (pt : C → X) (hpt : ∀ c, pt c ∈ G.obj c)
    (hmin : ∀ c (V : Opens X), pt c ∈ V → G.obj c ≤ V)
    (hcov : ∀ (U : Opens X), ∀ x ∈ U, ∃ c, x ∈ G.obj c ∧ G.obj c ≤ U) :
    Sheaf (Opens.grothendieckTopology X) (Type u) ≌ (Cᵒᵖ ⥤ Type u) := by
  have : G.IsCoverDense (Opens.grothendieckTopology X) := ⟨fun U x hx => by
    obtain ⟨c, hxc, hcU⟩ := hcov U x hx
    exact ⟨G.obj c, homOfLE hcU, Presieve.in_coverByImage G _, hxc⟩⟩
  have hbot : G.inducedTopology (Opens.grothendieckTopology X) = ⊥ := by
    apply le_antisymm _ bot_le
    intro c S hS
    rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hS
    rw [GrothendieckTopology.bot_covering, ← Sieve.id_mem_iff_eq_top]
    obtain ⟨V, f, ⟨d, g, h, hg, rfl⟩, hV⟩ := hS (pt c) (hpt c)
    have hcd : G.obj c ≤ G.obj d := hmin c _ ((leOfHom h) hV)
    have : G.preimage (homOfLE hcd) ≫ g = 𝟙 c := G.map_injective (Subsingleton.elim _ _)
    rw [← this]
    exact S.downward_closed hg _
  exact (G.sheafInducedTopologyEquivOfIsCoverDense (Opens.grothendieckTopology X) (Type u)).symm.trans
    ((sheafEquivOfEq hbot).trans (sheafBotEquivalence _))


/-! ## Ordered categories and their spaces -/

section Ordered

open Topology

variable (P : Type u) [Preorder P]

/-- The basic open `O_x = {y ≤ x}` of the space `X_C` (opens = sieves = lower sets). -/
def basicOpen (x : P) : Opens (WithLowerSet P) :=
  ⟨Set.Iic (WithLowerSet.toLowerSet x),
    (IsLowerSet.isOpen_iff_isLowerSet).2 (isLowerSet_Iic _)⟩

variable {P}

/-- PqCQM3Pcl6Q-9632 (2:40:32) [def] The open sets of `X_C` are the sieves (lower sets). -/
theorem isOpen_iff_sieve (O : Set (WithLowerSet P)) : IsOpen O ↔ IsLowerSet O :=
  IsLowerSet.isOpen_iff_isLowerSet

/-- PqCQM3Pcl6Q-9820 (2:43:40) [prop] The smallest open set containing `x` is `{y ≤ x}`. -/
theorem basicOpen_smallest (x : P) :
    WithLowerSet.toLowerSet x ∈ basicOpen P x ∧
      ∀ V : Opens (WithLowerSet P), WithLowerSet.toLowerSet x ∈ V → basicOpen P x ≤ V :=
  ⟨le_refl _, fun V hV _ hy => ((IsLowerSet.isOpen_iff_isLowerSet).1 V.2) hy hV⟩

/-- PqCQM3Pcl6Q-9878 (2:44:38) [prop] `O_x ⊆ O_y` iff `x ≤ y`, and the `O_x` form a basis. -/
theorem basicOpen_le_iff (x y : P) : basicOpen P x ≤ basicOpen P y ↔ x ≤ y :=
  Set.Iic_subset_Iic

theorem basicOpen_isBasis : Opens.IsBasis (Set.range (basicOpen P)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  exact ⟨basicOpen P x, ⟨x, rfl⟩, le_refl _, (basicOpen_smallest x).2 U hx⟩

/-- The functor `x ↦ O_x`, fully faithful. -/
def basicOpenFunctor : P ⥤ Opens (WithLowerSet P) :=
  (show Monotone (basicOpen P) from fun x y h => (basicOpen_le_iff x y).2 h).functor

@[simp] theorem basicOpenFunctor_obj (x : P) : basicOpenFunctor.obj x = basicOpen P x := rfl

instance : (basicOpenFunctor (P := P)).Full :=
  ⟨fun {x y} f => ⟨homOfLE ((basicOpen_le_iff x y).1 (leOfHom (X := Opens (WithLowerSet P)) f)),
    Subsingleton.elim _ _⟩⟩

instance : (basicOpenFunctor (P := P)).Faithful :=
  ⟨fun {_ _} _ _ _ => Subsingleton.elim _ _⟩

/-- PqCQM3Pcl6Q-10006 (2:46:46) [thm] / PqCQM3Pcl6Q-9505 (2:38:25) [prop] For an ordered category
`C` (a preorder) with the space `X_C` (underlying set `Ob C`, opens the sieves),
`Top(X_C) ≃ Ĉ`. -/
def alexandrovSheafEquiv : Sheaf (Opens.grothendieckTopology (WithLowerSet P)) (Type u) ≌
    (Pᵒᵖ ⥤ Type u) :=
  sheafEquivPresheafOfMinimalBasis basicOpenFunctor (fun x => WithLowerSet.toLowerSet x)
    (fun x => (basicOpen_smallest x).1) (fun x => (basicOpen_smallest x).2)
    (fun U x hx => ⟨WithLowerSet.ofLowerSet x, (basicOpen_smallest (WithLowerSet.ofLowerSet x)).1,
      (basicOpen_smallest (WithLowerSet.ofLowerSet x)).2 U hx⟩)

end Ordered

/-! ## Very dense subsets and essential points -/

/-- PqCQM3Pcl6Q-10259 (2:50:59) [def] `E ⊆ X` is very dense if every non-empty locally closed
subset of `X` meets `E`. -/
def IsVeryDense (E : Set X) : Prop :=
  ∀ L : Set X, IsLocallyClosed L → L.Nonempty → (L ∩ E).Nonempty

/-- ... equivalently, two opens with the same trace on `E` are equal. -/
theorem isVeryDense_iff (E : Set X) :
    IsVeryDense E ↔ ∀ U V : Opens X, (U : Set X) ∩ E ⊆ V → U ≤ V := by
  constructor
  · intro h U V hUV x hxU
    by_contra hxV
    obtain ⟨y, ⟨hyU, hyV⟩, hyE⟩ := h ((U : Set X) ∩ (V : Set X)ᶜ)
      ⟨U, (V : Set X)ᶜ, U.2, V.2.isClosed_compl, rfl⟩ ⟨x, hxU, hxV⟩
    exact hyV (hUV ⟨hyU, hyE⟩)
  · rintro h L ⟨U, Z, hU, hZ, rfl⟩ ⟨x, hxU, hxZ⟩
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have := h ⟨U, hU⟩ ⟨U ∩ Zᶜ, hU.inter hZ.isOpen_compl⟩ (fun y ⟨hyU, hyE⟩ =>
      ⟨hyU, fun hyZ => (Set.eq_empty_iff_forall_notMem.1 hne) y ⟨⟨hyU, hyZ⟩, hyE⟩⟩)
    exact (this hxU).2 hxZ

/-- PqCQM3Pcl6Q-10259 ... and equivalently the fibre functors at the points of `E` form a
conservative family. -/
theorem isVeryDense_iff_conservative (E : Set X) : IsVeryDense E ↔
    (ObjectProperty.ofObj (fun e : E => Opens.pointGrothendieckTopology e.1)).IsConservativeFamilyOfPoints := by
  rw [isVeryDense_iff]
  constructor
  · intro h
    refine ObjectProperty.IsConservativeFamilyOfPoints.mk' (fun U S hS x hx => ?_)
    let W : Opens X := sSup {V | ∃ f : V ⟶ U, S f}
    have hUW : U ≤ W := h U W (fun e ⟨heU, heE⟩ => by
      obtain ⟨Y, g, hg, ⟨⟨hy⟩⟩, -⟩ := hS ⟨_, ⟨(⟨e, heE⟩ : E)⟩⟩ ⟨⟨heU⟩⟩
      exact Opens.mem_sSup.2 ⟨Y, ⟨g, hg⟩, hy⟩)
    obtain ⟨V, ⟨f, hf⟩, hxV⟩ := Opens.mem_sSup.1 (hUW hx)
    exact ⟨V, f, hf, hxV⟩
  · intro hP U V hUV
    have := (hP.jointly_reflect_ofArrows_mem (X := U) (ι := PUnit.{u + 1})
      (fun _ => homOfLE (inf_le_left : U ⊓ V ≤ U))).2 (by
        rintro ⟨_, ⟨e⟩⟩ ⟨⟨he⟩⟩
        exact ⟨PUnit.unit, ⟨⟨he, hUV ⟨he, e.2⟩⟩⟩, rfl⟩)
    intro x hx
    obtain ⟨W, f, ⟨Z, g, k, ⟨⟩, -⟩, hxW⟩ := this x hx
    exact ((leOfHom g) hxW).2

/-- `x` is an essential point: it has a smallest open neighbourhood. -/
def HasMinNbhd (x : X) : Prop := ∃ U : Opens X, x ∈ U ∧ ∀ V : Opens X, x ∈ V → U ≤ V

/-- The smallest open neighbourhood of an essential point. -/
def minNbhd (x : {x : X // HasMinNbhd x}) : Opens X := x.2.choose

theorem mem_minNbhd (x : {x : X // HasMinNbhd x}) : x.1 ∈ minNbhd x := x.2.choose_spec.1

theorem minNbhd_le (x : {x : X // HasMinNbhd x}) (V : Opens X) (h : x.1 ∈ V) : minNbhd x ≤ V :=
  x.2.choose_spec.2 V h

variable (X) in
/-- The essential points ordered by specialization (`x → y` iff `O_x ⊆ O_y`). -/
abbrev EssCat := InducedCategory (Opens X) (minNbhd (X := X))

/-- PqCQM3Pcl6Q-10388 (2:53:08) [thm], one direction: if the essential points of `X` are very
dense, then `Top(X) ≃ Ĉ` for `C` the set of essential points ordered by specialization. -/
def sheafEquivOfVeryDense (h : IsVeryDense {x : X | HasMinNbhd x}) :
    Sheaf (Opens.grothendieckTopology X) (Type u) ≌ ((EssCat X)ᵒᵖ ⥤ Type u) :=
  sheafEquivPresheafOfMinimalBasis (inducedFunctor _) Subtype.val mem_minNbhd minNbhd_le
    (fun U x hx => by
      let W : Opens X := sSup {V | ∃ e : {x : X // HasMinNbhd x}, e.1 ∈ U ∧ V = minNbhd e}
      have hW : U ≤ W := (isVeryDense_iff _).1 h U W (fun e ⟨heU, he⟩ =>
        Opens.mem_sSup.2 ⟨_, ⟨⟨e, he⟩, heU, rfl⟩, mem_minNbhd ⟨e, he⟩⟩)
      obtain ⟨V, ⟨e, heU, rfl⟩, hxV⟩ := Opens.mem_sSup.1 (hW hx)
      exact ⟨e, hxV, minNbhd_le e U heU⟩)

/-! ## Stalks at points with a smallest open neighbourhood -/

section MinNbhd

variable {X : TopCat.{u}}

/-- If `U` is the smallest open neighbourhood of `x`, the germ map `F(U) → F_x` is bijective for
every presheaf `F`: the stalk functor at `x` is evaluation at `U`, representable by an object of
`O_X` (not only a pro-object), and commutes with all limits. -/
theorem isIso_germ_of_smallest (F : X.Presheaf (Type u)) {x : X} {U : Opens X} (hx : x ∈ U)
    (hU : ∀ V : Opens X, x ∈ V → U ≤ V) : IsIso (F.germ U x hx) := by
  have hI : IsInitial (⟨U, hx⟩ : OpenNhds x) :=
    IsInitial.ofUniqueHom (fun V => homOfLE (hU V.1 V.2)) (fun _ _ => Subsingleton.elim _ _)
  exact (colimit.isColimit _).isIso_ι_app_of_isTerminal _ hI.op

/-- The stalk functor at such a point is isomorphic to evaluation at `U`. -/
def stalkIsoEval {x : X} {U : Opens X} (hx : x ∈ U) (hU : ∀ V : Opens X, x ∈ V → U ≤ V) :
    (evaluation _ (Type u)).obj (op U) ≅ TopCat.Presheaf.stalkFunctor (Type u) x :=
  NatIso.ofComponents (fun F =>
    @asIso _ _ _ _ (TopCat.Presheaf.germ (X := X) F U x hx) (isIso_germ_of_smallest F hx hU))
    (fun f => (TopCat.Presheaf.stalkFunctor_map_germ U x hx f).symm)

/-- PqCQM3Pcl6Q-10135 (2:48:55) [prop], one direction: a point with a smallest open neighbourhood
is essential (its fibre functor commutes with arbitrary limits). -/
theorem stalk_preservesLimits {x : X} {U : Opens X} (hx : x ∈ U)
    (hU : ∀ V : Opens X, x ∈ V → U ≤ V) :
    PreservesLimits (TopCat.Presheaf.stalkFunctor (Type u) x) :=
  have := eval_preservesLimits (C := Opens X) U
  preservesLimits_of_natIso (stalkIsoEval hx hU)

end MinNbhd

/-- PqCQM3Pcl6Q-1011 (correction). In the Sierpiński space (`Bool` with opens the lower sets
`∅, {false}, Bool`), the closed point `true` has a smallest open neighbourhood (the whole space,
whose sections compute the stalk at `true`) but is not an open point. -/
theorem sierpinski_closed_point :
    (∀ V : Opens (Topology.WithLowerSet Bool), Topology.WithLowerSet.toLowerSet true ∈ V →
      basicOpen Bool true ≤ V) ∧ ¬ IsOpen ({Topology.WithLowerSet.toLowerSet true} :
        Set (Topology.WithLowerSet Bool)) := by
  refine ⟨(basicOpen_smallest true).2, fun h => ?_⟩
  rw [isOpen_iff_sieve] at h
  have := h (show Topology.WithLowerSet.toLowerSet false ≤ Topology.WithLowerSet.toLowerSet true
    from Bool.false_le true) rfl
  exact Bool.false_ne_true this

/-! ## Points of presheaf topoi and pro-objects -/

/-- PqCQM3Pcl6Q-9126 (2:32:06) [prop], one direction: a pro-object of `C` (a cofiltered, initially
small diagram `p : N → C`) defines a point of `Ĉ`, whose fibre functor is
`F ↦ colim_N F(p(n))` (`Point.isColimitPresheafFiberOfIsCofilteredCocone`). -/
def proPoint {C : Type u} [SmallCategory C] {N : Type u} [SmallCategory N] [IsCofiltered N]
    [InitiallySmall.{u} N]
    (p : N ⥤ C) : Point.{u} (⊥ : GrothendieckTopology C) :=
  Point.ofIsCofiltered p (fun _ R hR _ f => by
    obtain rfl : R = ⊤ := by simpa using hR
    exact ⟨_, f, trivial, _, 𝟙 _, 𝟙 _, by simp⟩)

/-! ## Equivariant étale spaces: the topos `Top(X, G)` -/

section Equivariant

/-- PqCQM3Pcl6Q-2361 (0:39:21) [def] An object of `Top(X, G)`: an étale space `p : E → X` with an
action of the discrete group `G` by homeomorphisms making `p` equivariant. -/
structure EquivEtale (X : Type u) [TopologicalSpace X] (G : Type u) [Group G] [MulAction G X] where
  /-- The total space. -/
  E : Type u
  [top : TopologicalSpace E]
  [act : MulAction G E]
  /-- The projection. -/
  p : E → X
  etale : IsLocalHomeomorph p
  cont : ∀ g : G, Continuous fun e : E => g • e
  equivariant : ∀ (g : G) (e : E), p (g • e) = g • p e

/-- PqCQM3Pcl6Q-3136 (0:52:16) [rem] The opens of `X/G` (quotient topology) are the images of the
`G`-invariant opens of `X`; the quotient map is open. -/
theorem quotient_opens (X : Type u) [TopologicalSpace X] (G : Type u) [Group G] [MulAction G X]
    [ContinuousConstSMul G X] :
    IsOpenQuotientMap (Quotient.mk (MulAction.orbitRel G X)) :=
  MulAction.isOpenQuotientMap_quotientMk

end Equivariant

/-! ## Tensor products and finiteness -/

/-- PqCQM3Pcl6Q-7746 (2:09:06) [prop], sectionwise: `M ⊗_R R^n ≅ M^n`, naturally. -/
def tensor_free (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (n : ℕ) :
    TensorProduct R M (Fin n → R) ≃ₗ[R] (Fin n → M) :=
  TensorProduct.piScalarRight R R M (Fin n)

/-- PqCQM3Pcl6Q-8242 (2:17:22) [prop], the case of orders in number fields: the normalization of
`ℤ` in a number field (its ring of integers) is a finite `ℤ`-module, hence of finite type. -/
theorem ringOfIntegers_finite (K : Type*) [Field K] [NumberField K] :
    Module.Finite ℤ (NumberField.RingOfIntegers K) ∧ Algebra.FiniteType ℤ (NumberField.RingOfIntegers K) :=
  ⟨inferInstance, inferInstance⟩

/-- PqCQM3Pcl6Q-8368 (2:19:28) [prop], the first step: finitely many elements of `K` (the
coefficients of a finite presentation) lie in a subalgebra of finite type over `ℤ`. -/
theorem coefficients_fg {K : Type*} [CommRing K] (s : Finset K) :
    (Algebra.adjoin ℤ (s : Set K)).FG :=
  ⟨s, rfl⟩

end

end Buffalo.Topos.Part03
