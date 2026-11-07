import Mathlib

/-!
# Buffalo, topos theory, part 4a: coverings, `f_!` and `f^!`, sites and sheaves on a site

Entries of `docs/buffalo-topos/index.tex` from « Galois theory of coverings and classifying topoi »
to « The associated sheaf on a site » (video `PqCQM3Pcl6Q`, 3:23:52–5:09:50). The status of each
entry is in `docs/buffalo-topos/lean/Part04.json`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Topology
open scoped TensorProduct

namespace Buffalo.Topos.Part04

noncomputable section

/-! ## Galois theory of coverings: the algebraic side (`G`-sets) -/

/-- PqCQM3Pcl6Q-12618 (3:30:18) [prop] A subgroup `H ⊆ G` is recovered from the pointed transitive
`G`-set `G/H` as the stabilizer of its base point, and every pointed transitive `G`-set `(X, x)` is
`G/Stab(x)`. (The covering side, `G/H ↔ Z' → Z`, is not formalised.) -/
theorem subgroup_pointed_transitive {G : Type*} [Group G] (H : Subgroup G) :
    MulAction.stabilizer G ((1 : G) : G ⧸ H) = H ∧
      ∀ (X : Type*) [MulAction G X] [MulAction.IsPretransitive G X] (x : X),
        Nonempty (X ≃ G ⧸ MulAction.stabilizer G x) :=
  ⟨MulAction.stabilizer_quotient H, fun X _ _ x =>
    ⟨(Equiv.ofBijective (MulAction.ofQuotientStabilizer G x)
      ⟨MulAction.injective_ofQuotientStabilizer G x, fun y => by
        obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
        exact ⟨g, MulAction.ofQuotientStabilizer_mk G x g⟩⟩).symm⟩⟩

/-- PqCQM3Pcl6Q-13017 (3:36:57) [thm], case `Z` a point: `BG/(G/H) ≃ BH`. For a `G`-set `E` over
`G/H`, the fibre `F` over the base point is stable under `H`, and `E = G ×^H F`: every element of
`E` is some `g • x` with `x ∈ F`, and `g • x = g' • x'` iff `g' = g h⁻¹`, `x' = h • x` for some
`h ∈ H`. -/
theorem fibre_over_quotient {G E : Type*} [Group G] [MulAction G E] (H : Subgroup G)
    (p : E → G ⧸ H) (hp : ∀ (g : G) (e : E), p (g • e) = g • p e) :
    (∀ h ∈ H, ∀ x, p x = ((1 : G) : G ⧸ H) → p (h • x) = ((1 : G) : G ⧸ H)) ∧
    (∀ e : E, ∃ g : G, ∃ x, p x = ((1 : G) : G ⧸ H) ∧ g • x = e) ∧
    (∀ (g g' : G) (x x' : E), p x = ((1 : G) : G ⧸ H) → p x' = ((1 : G) : G ⧸ H) →
      (g • x = g' • x' ↔ ∃ h ∈ H, g' = g * h⁻¹ ∧ x' = h • x)) := by
  have key : ∀ (g : G) x, p x = ((1 : G) : G ⧸ H) → p (g • x) = (g : G ⧸ H) := by
    intro g x hx
    rw [hp, hx, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  refine ⟨fun h hh x hx => ?_, fun e => ?_, fun g g' x x' hx hx' => ⟨fun heq => ?_, ?_⟩⟩
  · rw [key h x hx, QuotientGroup.eq]
    simpa using H.inv_mem hh
  · obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (p e)
    refine ⟨g, g⁻¹ • e, ?_, smul_inv_smul g e⟩
    rw [hp, ← hg, MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
  · have h1 := key g x hx
    rw [heq, key g' x' hx', eq_comm, QuotientGroup.eq] at h1
    refine ⟨g'⁻¹ * g, by simpa using H.inv_mem h1, by group, ?_⟩
    rw [mul_smul, heq, inv_smul_smul]
  · rintro ⟨h, -, rfl, rfl⟩
    rw [← mul_smul, inv_mul_cancel_right]

/-! ## Adjoints `f_!` and `f^!` in examples -/

/-- PqCQM3Pcl6Q-13743 (3:49:03) [prop], the limit half: the direct image of sheaves of abelian
groups `i_*` is a right adjoint, hence commutes with all limits (for every continuous map). -/
theorem pushforward_preservesLimits {X Y : TopCat.{u}} (i : Y ⟶ X) :
    PreservesLimits (TopCat.Sheaf.pushforward (Type u) i) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i).rightAdjoint_preservesLimits

/-- PqCQM3Pcl6Q-14059 (3:54:19) [prop], presheaf form: for an open embedding `j : Y → X`, `j^*`
(restriction along `V ↦ j(V)`) commutes with all limits and has a left adjoint `j_!` (the left
Kan extension) on presheaves of sets. -/
theorem openEmbedding_restrict_isRightAdjoint {X Y : TopCat.{u}} (j : Y ⟶ X)
    (hj : IsOpenEmbedding j) :
    ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ (Type u)).obj
      hj.isOpenMap.functor.op).IsRightAdjoint ∧
    Nonempty (PreservesLimits ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ (Type u)).obj
      hj.isOpenMap.functor.op)) :=
  ⟨(Functor.lanAdjunction _ _).isRightAdjoint,
    ⟨(Functor.lanAdjunction _ _).rightAdjoint_preservesLimits⟩⟩

/-- PqCQM3Pcl6Q-14625 (4:03:45) [prop], the space case. The initial sheaf `∅_X` has `∅_X(U) = pt`
if `U = ∅` and `∅_X(U) = ∅` otherwise, so `f_*∅_X(V) = ∅_X(f⁻¹V)`; hence `f_*∅_X = ∅_Y` iff
`f⁻¹V = ∅` forces `V = ∅` for open `V`, iff the image of `f` is dense. -/
theorem pushforward_empty_iff_denseRange {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) :
    (∀ V : Set Y, IsOpen V → (f ⁻¹' V = ∅ ↔ V = ∅)) ↔ DenseRange f := by
  rw [DenseRange, dense_iff_inter_open]
  constructor
  · intro h U hU hne
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have : f ⁻¹' U = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact (Set.eq_empty_iff_forall_notMem.1 hc) (f x) ⟨hx, x, rfl⟩
    exact hne.ne_empty ((h U hU).1 this)
  · intro h V hV
    refine ⟨fun hpre => ?_, fun hV' => by simp [hV']⟩
    by_contra hne
    obtain ⟨y, hyV, x, rfl⟩ := h V hV (Set.nonempty_iff_ne_empty.2 hne)
    exact (Set.eq_empty_iff_forall_notMem.1 hpre) x hyV

/-! ## Local properties: locally trivial maps, torsors -/

section Trivial

variable {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]

/-- A map `p : E → X` is trivial if `E ≅ X × F` over `X` for some space `F`. -/
def IsTrivialMap (p : E → X) : Prop :=
  ∃ (F : Type u) (_ : TopologicalSpace F) (e : E ≃ₜ X × F), ∀ y, (e y).1 = p y

/-- PqCQM3Pcl6Q-15006 (4:10:06) [def] `p : E → X` is locally trivial if every point has an open
neighbourhood `U` with `E|_U ≅ U × F_U` over `U`. -/
def IsLocallyTrivialMap (p : E → X) : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ (F : Type u) (_ : TopologicalSpace F)
    (e : (p ⁻¹' U) ≃ₜ U × F), ∀ y, (e y).1 = ⟨p y, y.2⟩

end Trivial

/-- The point `pt → Bool`, `pt ↦ true` (`Bool` discrete). -/
def ptToBool : PUnit.{u + 1} → ULift.{u} Bool := fun _ => ⟨true⟩

private def discreteHomeo {A B : Type*} [TopologicalSpace A] [DiscreteTopology A]
    [TopologicalSpace B] [DiscreteTopology B] (e : A ≃ B) : A ≃ₜ B where
  toEquiv := e
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

private lemma ptToBool_false (y : ptToBool.{u} ⁻¹' {⟨false⟩}) : False := by
  have h : ptToBool.{u} y.1 = ⟨false⟩ := y.2
  exact Bool.noConfusion (congrArg ULift.down h : true = false)

/-- PqCQM3Pcl6Q-15006 (4:10:06) [def], the claim « being locally trivial is local, being trivial is
not »: the inclusion of a point into the discrete two-point space is locally trivial (fibres a point
over `true`, empty over `false`) but not trivial. -/
theorem ptToBool_locallyTrivial_not_trivial :
    IsLocallyTrivialMap ptToBool.{u} ∧ ¬ IsTrivialMap ptToBool.{u} := by
  refine ⟨fun ⟨x⟩ => ⟨{⟨x⟩}, isOpen_discrete _, rfl, ?_⟩, ?_⟩
  · cases x
    · refine ⟨PEmpty, ⊥, discreteHomeo ⟨fun y => (ptToBool_false y).elim,
        fun z => z.2.elim, fun y => (ptToBool_false y).elim, fun z => z.2.elim⟩,
        fun y => (ptToBool_false y).elim⟩
    · refine ⟨PUnit, ⊥, discreteHomeo ⟨fun _ => (⟨⟨true⟩, rfl⟩, PUnit.unit),
        fun _ => ⟨PUnit.unit, rfl⟩, fun _ => rfl, ?_⟩, fun y => rfl⟩
      rintro ⟨⟨_, h⟩, _⟩
      simp only [Set.mem_singleton_iff] at h
      subst h; rfl
  · rintro ⟨F, _, e, he⟩
    have hF : IsEmpty F := ⟨fun f => by
      have := he (e.symm (⟨false⟩, f))
      simp [ptToBool] at this⟩
    exact hF.false (e PUnit.unit).2

/-- PqCQM3Pcl6Q-15261 (4:14:21) [def] A torsor in the functorial sense: for every `K'` (an index
`i`), `X(K')` is empty or a principal homogeneous space under `G(K')`. -/
def IsFunctorialTorsor {ι : Type*} (G X : ι → Type*) [∀ i, Group (G i)]
    [∀ i, MulAction (G i) (X i)] : Prop :=
  ∀ i, IsEmpty (X i) ∨
    (MulAction.IsPretransitive (G i) (X i) ∧ ∀ (g : G i) (x : X i), g • x = x → g = 1)

/-- PqCQM3Pcl6Q-15387 (4:16:27) [rem] A principal homogeneous space with a point (a section) is
trivial: `g ↦ g • x` is a `G`-equivariant bijection `G ≃ X`. -/
theorem torsor_trivial_of_point {G X : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) (x : X) :
    Function.Bijective (fun g : G => g • x) := by
  refine ⟨fun g g' h => ?_, fun y => MulAction.exists_smul_eq G x y⟩
  have : (g'⁻¹ * g) • x = x := by
    simp only [mul_smul]
    exact inv_smul_eq_iff.2 h
  simpa [inv_mul_eq_one, eq_comm] using hfree _ x this

/-! ## Sites, pretopologies and local properties -/

section Sites

variable {C : Type u} [SmallCategory C]

/-- PqCQM3Pcl6Q-15517 (4:18:37) [def] A site: a category with a Grothendieck topology. -/
example : Type u := GrothendieckTopology C

/-- PqCQM3Pcl6Q-15640 (4:20:40) [def] A topology given by covering families `Cov(X)`: Mathlib's
`Precoverage` (for every `X`, a set of presieves on `X`). -/
example (K : Precoverage C) (X : C) : Set (Presieve X) := K.coverings X

/-- PqCQM3Pcl6Q-15774 (4:22:54) [ex], in Mathlib's geometric form: the fpqc precoverage on schemes
(quasi-compact, jointly surjective families of flat morphisms) contains the isomorphisms and is
stable under base change and composition; and faithful flatness is stable under base change
and composition. -/
theorem fpqc_pretopology_axioms :
    Precoverage.HasIsos AlgebraicGeometry.Scheme.fpqcPrecoverage.{u} ∧
      Precoverage.IsStableUnderBaseChange AlgebraicGeometry.Scheme.fpqcPrecoverage.{u} ∧
      Precoverage.IsStableUnderComposition AlgebraicGeometry.Scheme.fpqcPrecoverage.{u} ∧
      (∀ (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
        [Module.FaithfullyFlat A B], Module.FaithfullyFlat A' (A' ⊗[A] B)) :=
  ⟨inferInstance, inferInstance, inferInstance, fun _ _ _ _ _ _ _ _ _ => inferInstance⟩

variable [Limits.HasPullbacks C]

/-- PqCQM3Pcl6Q-15905 (4:25:05) [def] Base change and PqCQM3Pcl6Q-15905 (4:25:05) [def]
transitivity: the axioms `pullbacks` and `transitive` of Mathlib's `Pretopology`. -/
example (K : Pretopology C) {X Y : C} (f : Y ⟶ X) (S : Presieve X) (hS : S ∈ K X) :
    Presieve.pullbackArrows f S ∈ K Y :=
  K.pullbacks f S hS

example (K : Pretopology C) {X : C} (S : Presieve X) (Ti : ∀ ⦃Y⦄ (f : Y ⟶ X), S f → Presieve Y)
    (hS : S ∈ K X) (hTi : ∀ ⦃Y⦄ (f) (H : S f), Ti f H ∈ K Y) : S.bind Ti ∈ K X :=
  K.transitive S Ti hS hTi

/-- PqCQM3Pcl6Q-16027 (4:27:07) [def] A single isomorphism covers (`Pretopology.has_isos`), and a
topology is saturated under refinement (`GrothendieckTopology.superset_covering`). -/
example (K : Pretopology C) {X Y : C} (f : Y ⟶ X) [IsIso f] : Presieve.singleton f ∈ K X :=
  K.has_isos f

example (J : GrothendieckTopology C) {X : C} {S R : Sieve X} (h : S ≤ R) (hS : S ∈ J X) :
    R ∈ J X :=
  J.superset_covering h hS

/-- PqCQM3Pcl6Q-16285 (4:31:25) [def] Saturating a pretopology gives a topology: a sieve covers
for `K.toGrothendieck` iff it contains a covering family of `K`. -/
theorem mem_toGrothendieck_iff (K : Pretopology C) {X : C} (S : Sieve X) :
    S ∈ K.toGrothendieck X ↔ ∃ R ∈ K X, R ≤ (S : Presieve X) :=
  Iff.rfl

/-- PqCQM3Pcl6Q-16476 (4:34:36) [def] A property `P` of the arrows `Y → X` (the property of the
pulled-back situation over `Y`) holds locally on `X` if it holds on the members of a covering. -/
def HoldsLocally (J : GrothendieckTopology C) {X : C} (P : ∀ ⦃Y : C⦄, (Y ⟶ X) → Prop) : Prop :=
  ∃ S ∈ J X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → P f

/-- PqCQM3Pcl6Q-16608 (4:36:48) [prop] For the topology generated by a pretopology `K`, a property
stable under further pullback holds locally iff it holds on a covering family of `K`. -/
theorem holdsLocally_toGrothendieck_iff (K : Pretopology C) {X : C}
    (P : ∀ ⦃Y : C⦄, (Y ⟶ X) → Prop)
    (hP : ∀ ⦃Y Z : C⦄ (g : Z ⟶ Y) (f : Y ⟶ X), P f → P (g ≫ f)) :
    HoldsLocally K.toGrothendieck P ↔ ∃ R ∈ K X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → P f := by
  constructor
  · rintro ⟨S, ⟨R, hR, hRS⟩, h⟩
    exact ⟨R, hR, fun Y f hf => h f (hRS _ f hf)⟩
  · rintro ⟨R, hR, h⟩
    refine ⟨Sieve.generate R, ⟨R, hR, Sieve.le_generate R⟩, ?_⟩
    rintro Y f ⟨Z, g, r, hr, rfl⟩
    exact hP g r (h r hr)

end Sites

/-! ## Sheaves on a site -/

section Sheaves

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- PqCQM3Pcl6Q-16734 (4:38:54) [def] Separated presheaves and sheaves on a site with fibre
products: the sheaf condition for a covering family is the exactness of
`F(X) → ∏ F(X_i) ⇉ ∏ F(X_i ×_X X_j)` (Mathlib's `Equalizer.Presieve.sheaf_condition`). -/
example [HasPullbacks C] (P : Cᵒᵖ ⥤ Type u) {X : C} (R : Presieve X) [R.HasPairwisePullbacks] :
    R.IsSheafFor P ↔ Nonempty (IsLimit (Fork.ofι _ (Equalizer.Presieve.w P R))) :=
  Equalizer.Presieve.sheaf_condition P R

/-- PqCQM3Pcl6Q-16924 (4:42:04) [thm], in the elementary form Mathlib can state: the category of
sheaves of sets on a small site has all limits and colimits and a subobject classifier. -/
theorem sheaf_topos_axioms :
    HasLimitsOfSize.{u, u} (Sheaf J (Type u)) ∧
      (∀ (K : Type u) [SmallCategory K], HasColimitsOfShape K (Sheaf J (Type u))) ∧
      HasSubobjectClassifier (Sheaf J (Type u)) :=
  ⟨inferInstance, fun _ _ => inferInstance, inferInstance⟩

/-- PqCQM3Pcl6Q-17114 (4:45:14) [prop], the half « covering families become epimorphic »: the
inclusion of a covering sieve `R ↪ X` in `Ĉ` becomes an isomorphism after sheafification. -/
theorem coveringSieve_inverted {X : C} (S : Sieve X) (hS : S ∈ J X) :
    IsIso ((presheafToSheaf J (Type u)).map (Sieve.shrinkFunctor.{u} S).ι) :=
  (J.W_iff _).1 (Sieve.W_shrinkFunctor_ι_of_mem J S hS)

/-! ## The associated sheaf on a site -/

/-- PqCQM3Pcl6Q-17743 (4:55:43) [thm] The inclusion `Sh(C) → Ĉ` has a left adjoint `a`, which is
left exact. -/
theorem sheafification_leftExact :
    Nonempty (presheafToSheaf J (Type u) ⊣ sheafToPresheaf J (Type u)) ∧
      Nonempty (PreservesFiniteLimits (presheafToSheaf J (Type u))) :=
  ⟨⟨sheafificationAdjunction J _⟩, ⟨inferInstance⟩⟩

/-- PqCQM3Pcl6Q-17868 (4:57:48) [def] `LF(X)` is the colimit, over the covers of `X`, of the
matching families (multiequalizers): Mathlib's `GrothendieckTopology.plusObj`. -/
example (P : Cᵒᵖ ⥤ Type u) (X : C) :
    (J.plusObj P).obj (op X) = colimit (J.diagram P X) :=
  rfl

/-- Separatedness for covers: two sections agreeing on a cover are equal. -/
def CoverSeparated (P : Cᵒᵖ ⥤ Type u) : Prop :=
  ∀ (X : C) (S : J.Cover X) (x y : P.obj (op X)),
    (∀ I : S.Arrow, P.map I.f.op x = P.map I.f.op y) → x = y

/-- PqCQM3Pcl6Q-18127 (5:02:07) [prop] `L` is left exact, `LF` is separated, and
`Hom(F, G) ≃ Hom(LF, G)` for every sheaf `G`. -/
theorem plus_properties :
    Nonempty (PreservesFiniteLimits (J.plusFunctor (Type u))) ∧
      (∀ P : Cᵒᵖ ⥤ Type u, CoverSeparated J (J.plusObj P)) ∧
      (∀ (P Q : Cᵒᵖ ⥤ Type u), Presheaf.IsSheaf J Q → Nonempty ((P ⟶ Q) ≃ (J.plusObj P ⟶ Q))) :=
  ⟨⟨inferInstance⟩, fun P _ S x y h => GrothendieckTopology.Plus.sep P S x y h,
    fun P _ hQ => ⟨{ toFun := fun η => J.plusLift η hQ
                     invFun := fun γ => J.toPlus P ≫ γ
                     left_inv := fun η => J.toPlus_plusLift η hQ
                     right_inv := fun γ => (J.plusLift_unique _ hQ γ rfl).symm }⟩⟩

/-- PqCQM3Pcl6Q-18258 (5:04:18) [prop] `F → LF` is injective iff `F` is separated, an isomorphism
iff `F` is a sheaf; if `F` is separated, `LF` is a sheaf; and `a = L ∘ L`. -/
theorem toPlus_properties (P : Cᵒᵖ ⥤ Type u) :
    (CoverSeparated J P ↔ ∀ X, Function.Injective ((J.toPlus P).app (op X))) ∧
      (Presheaf.IsSheaf J P ↔ IsIso (J.toPlus P)) ∧
      (CoverSeparated J P → Presheaf.IsSheaf J (J.plusObj P)) ∧
      J.sheafify P = J.plusObj (J.plusObj P) := by
  have sep_iff : CoverSeparated J P ↔ ∀ X, Function.Injective ((J.toPlus P).app (op X)) := by
    refine ⟨fun h X => GrothendieckTopology.Plus.inj_of_sep P (fun X S x y hxy => h X S x y hxy) X, fun h X S x y hxy => ?_⟩
    apply h X
    apply GrothendieckTopology.Plus.sep P S
    intro I
    have hn := fun z => NatTrans.naturality_apply (J.toPlus P) I.f.op z
    exact (hn x).symm.trans ((congrArg _ (hxy I)).trans (hn y))
  refine ⟨sep_iff, ⟨fun hP => J.isIso_toPlus_of_isSheaf P hP, fun hiso => ?_⟩,
    fun h => GrothendieckTopology.Plus.isSheaf_of_sep P (fun X S x y hxy => h X S x y hxy), rfl⟩
  have hinj : ∀ X, Function.Injective ((J.toPlus P).app (op X)) := fun X => by
    have : IsIso ((J.toPlus P).app (op X)) := inferInstance
    exact ((isIso_iff_bijective _).1 this).1
  have hsep := sep_iff.2 hinj
  exact (Presheaf.isSheaf_of_iso_iff (asIso (J.toPlus P))).2
    (GrothendieckTopology.Plus.isSheaf_of_sep P (fun X S x y hxy => hsep X S x y hxy))

/-- PqCQM3Pcl6Q-18454 (5:07:34) [prop] Sheaves are closed under limits in `Ĉ` (the inclusion
creates limits), and a colimit of sheaves is the associated sheaf of the colimit in `Ĉ`. -/
theorem sheaf_limits_colimits {K : Type u} [SmallCategory K] (F : K ⥤ Sheaf J (Type u)) :
    Nonempty (CreatesLimitsOfShape K (sheafToPresheaf J (Type u))) ∧
      Nonempty (colimit F ≅ (presheafToSheaf J (Type u)).obj
        (colimit (F ⋙ sheafToPresheaf J (Type u)))) :=
  ⟨⟨inferInstance⟩, ⟨(HasColimit.isoOfNatIso
      (Functor.isoWhiskerLeft F (asIso (sheafificationAdjunction J (Type u)).counit)).symm ≪≫
      (preservesColimitIso (presheafToSheaf J (Type u)) (F ⋙ sheafToPresheaf J (Type u))).symm)⟩⟩

/-- PqCQM3Pcl6Q-18590 (5:09:50) [def] A subcanonical topology (every representable is a sheaf), and
then `C → Ĉ` factors through `Sh(C)`. -/
example [J.Subcanonical] : C ⥤ Sheaf J (Type u) := J.yoneda

end Sheaves

end

end Buffalo.Topos.Part04
