import Mathlib

/-!
# Buffalo, algebraic geometry, part 05 (b): 20 June 1973

The entries of `docs/buffalo-ag/index.tex` lines 684–733 (video `thSz9ZHDK9o`, 8:56:26–10:31:34):
fibres and base change for projective bundles, the relative spectrum and affine morphisms, fibre
products of schemes, Grassmannians and automorphism groups, localization at a point.

Conventions. As in `Part05a`, mathlib has no projective bundle `𝐏(ℳ)` and no relative spectrum
`Spec 𝒜` of a quasi-coherent algebra; the entries on them are formalised in their affine or
ring-theoretic content (`S = Spec K`, the absolute `Spec`, the `Γ ⊣ Spec` adjunction, and
`Proj` of a graded algebra for the properness of projective bundles).
-/

open CategoryTheory Limits Opposite AlgebraicGeometry TensorProduct Topology

universe u

namespace Buffalo.AG.Part05

noncomputable section

/-! ### Fibres and base change for projective bundles -/

section Fibres

/-- thSz9ZHDK9o-32186 (8:56:26) [prop] (the module identity behind it) Base change of `M_{k'}`
along `k' → k''` is `M_{k''}`: `k'' ⊗_{k'} (k' ⊗_k M) = k'' ⊗_k M`, so invertible quotients of
`(M_{S'})_{S''}` are those of `M_{S''}`. -/
def prop_32186 (k k' k'' : Type*) [CommRing k] [CommRing k'] [CommRing k''] [Algebra k k']
    [Algebra k' k''] [Algebra k k''] [IsScalarTower k k' k''] (M : Type*) [AddCommGroup M]
    [Module k M] : k'' ⊗[k'] (k' ⊗[k] M) ≃ₗ[k''] k'' ⊗[k] M :=
  AlgebraTensorModule.cancelBaseChange k k' k'' k'' M

/-- thSz9ZHDK9o-32313 (8:58:33) [prop] The fibre `X_s` is the base change of `X → S` along
`Spec κ(s) → S` (mathlib: `Scheme.Hom.fiber`), a scheme over `κ(s)`. -/
theorem prop_32313 {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    f.fiber s = pullback f (S.fromSpecResidueField s) ∧
      f.fiberToSpecResidueField s ≫ S.fromSpecResidueField s = f.fiberι s ≫ f :=
  ⟨rfl, (pullback.condition).symm⟩

/-- thSz9ZHDK9o-32379 (8:59:39) [prop] The underlying space of `X_s` is the set-theoretic fibre
`f⁻¹(s)` with the induced topology (mathlib: `Scheme.Hom.fiberHomeo`). -/
def prop_32379 {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : f.fiber s ≃ₜ f ⁻¹' {s} :=
  f.fiberHomeo s

/-- thSz9ZHDK9o-32506 (9:01:46) [prop] (the module identity) `M(s) = M ⊗ κ(s) = M_s ⊗_{A_s} κ(s)
= M_s / 𝔪_s M_s`, `κ(s) = A_𝔭/𝔪`. -/
def prop_32506 {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] (M : Type u) [AddCommGroup M]
    [Module A M] :
    (Localization.AtPrime p ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime p)) ⊗[A] M ≃ₗ[A]
      LocalizedModule p.primeCompl M ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p) •
        (⊤ : Submodule (Localization.AtPrime p) (LocalizedModule p.primeCompl M))) :=
  let Ap := Localization.AtPrime p
  let k := Ap ⧸ IsLocalRing.maximalIdeal Ap
  let e1 : k ⊗[A] M ≃ₗ[Ap] k ⊗[Ap] (Ap ⊗[A] M) :=
    ((AlgebraTensorModule.cancelBaseChange A Ap k k M).symm).restrictScalars Ap
  let e2 : Ap ⊗[A] M ≃ₗ[Ap] LocalizedModule p.primeCompl M :=
    (IsLocalizedModule.isBaseChange p.primeCompl Ap
      (LocalizedModule.mkLinearMap p.primeCompl M)).equiv
  ((e1.trans (e2.lTensor k)).trans
    (quotTensorEquivQuotSMul (LocalizedModule p.primeCompl M)
      (IsLocalRing.maximalIdeal Ap))).restrictScalars A

/-- thSz9ZHDK9o-32636 (9:03:56) [prop] (the mechanism) A morphism of `S`-schemes from a proper
`S`-scheme (such as `𝐏(ℳ)`, `ℳ` of finite type) to a separated one has closed image. -/
theorem prop_32636 {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsProper f] [IsSeparated g]
    (h : X ⟶ Y) (hh : h ≫ g = f) : IsClosed (Set.range h) := by
  subst hh
  have : IsProper h := IsProper.of_comp h g
  exact h.isClosedMap.isClosed_range

/-- thSz9ZHDK9o-32636 (9:03:56) [prop] (properness) `Proj` of a graded algebra of finite type
over its degree-zero part (e.g. `Sym ℳ`, `ℳ` finitely generated, i.e. `𝐏(ℳ)`) is proper over
`Spec 𝒜₀` (mathlib). -/
theorem prop_32636_proper {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A] :
    IsProper (Proj.toSpecZero 𝒜) :=
  inferInstance

/-- thSz9ZHDK9o-32959 (9:09:19) [prop] (affine pieces) An epimorphism `M → N` induces a
surjection `Sym M → Sym N`, hence a closed immersion `Spec Sym N → Spec Sym M` (and likewise on
the affine pieces `Sym/(e_i - 1)` of the projective bundles). -/
theorem prop_32959 (R M N : Type u) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (q : M →ₗ[R] N) (hq : Function.Surjective q) :
    Function.Surjective (SymmetricAlgebra.lift (SymmetricAlgebra.ι R N ∘ₗ q)) ∧
      IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (SymmetricAlgebra.lift (SymmetricAlgebra.ι R N ∘ₗ q)).toRingHom)) := by
  have hs : Function.Surjective (SymmetricAlgebra.lift (SymmetricAlgebra.ι R N ∘ₗ q)) := by
    intro b
    induction b using SymmetricAlgebra.induction with
    | algebraMap r => exact ⟨algebraMap R _ r, AlgHom.commutes _ r⟩
    | ι x =>
      obtain ⟨m, rfl⟩ := hq x
      exact ⟨SymmetricAlgebra.ι R M m, by simp⟩
    | mul a b ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' * b', map_mul _ _ _⟩
    | add a b ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩
  exact ⟨hs, IsClosedImmersion.spec_of_surjective _ hs⟩

/-- thSz9ZHDK9o-33023 (9:10:23) [prop] For `u : M → L` with `L` finite (e.g. invertible), the set
of points where `u` is surjective (where `L/u(M)` vanishes) is open. -/
theorem prop_33023 {A : Type u} [CommRing A] {M L : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup L] [Module A L] [Module.Finite A L] (v : M →ₗ[A] L) :
    IsOpen {p : PrimeSpectrum A | Subsingleton
      (LocalizedModule p.asIdeal.primeCompl (L ⧸ LinearMap.range v))} := by
  have hc := Module.isClosed_support (R := A) (M := L ⧸ LinearMap.range v)
  convert hc.isOpen_compl using 1
  ext p
  simp [Module.notMem_support_iff]

/-- thSz9ZHDK9o-33086 (9:11:26) [ex] (the first two cases) Over a nonzero ring, the zero module
has no invertible quotient (`𝐏(0) = ∅`), and the only quotient of `R` isomorphic to `R` is `R`
itself, an epimorphism `R → R` being bijective (`𝐏(𝒪_S) = S`). -/
theorem ex_33086 {A : Type u} [CommRing A] [Nontrivial A] :
    (∀ q : PUnit.{u + 1} →ₗ[A] A, ¬ Function.Surjective q) ∧
      ∀ q : A →ₗ[A] A, Function.Surjective q → Function.Bijective q := by
  refine ⟨fun q hq => ?_, fun q hq => ⟨OrzechProperty.injective_of_surjective_endomorphism q hq, hq⟩⟩
  obtain ⟨x, hx⟩ := hq 1
  rw [Subsingleton.elim x 0, map_zero] at hx
  exact zero_ne_one hx

end Fibres

/-! ### Relative spectrum and affine morphisms -/

section RelativeSpec

/-- thSz9ZHDK9o-33684 (9:21:24) [def] (affine base) The functor of points of `Spec A`:
`Hom(S', Spec A) = Hom(A, Γ(S', 𝒪_{S'}))` (mathlib: the adjunction `Γ ⊣ Spec`). -/
def def_33684 (X : Scheme.{u}) (R : CommRingCat.{u}) :
    (X ⟶ Spec R) ≃ (R ⟶ Γ(X, ⊤)) :=
  (ΓSpec.adjunction.homEquiv X (op R)).symm.trans (opEquiv _ _)

/-- thSz9ZHDK9o-34198 (9:29:58) [prop] (absolute case) `Spec`, from rings to schemes, is fully
faithful. -/
def prop_34198 : Scheme.Spec.{u}.FullyFaithful := Spec.fullyFaithful

/-- thSz9ZHDK9o-34263 (9:31:03) [prop] Over an affine base, a scheme is affine over `S` (preimages
of affine open sets are affine, mathlib's `IsAffineHom`) if and only if it is affine: the schemes
affine over `Spec K` are the `Spec A`. -/
theorem prop_34263 {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] : IsAffineHom f ↔ IsAffine X :=
  ⟨fun _ => isAffine_of_isAffineHom f, fun _ => inferInstance⟩

/-- thSz9ZHDK9o-34392 (9:33:12) [prop] (affine case) `Spec A ×_{Spec K} Spec K' =
Spec(A ⊗_K K')`: the spectrum commutes with base change. -/
def prop_34392 (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅ Spec (.of (S ⊗[R] T)) :=
  pullbackSpecIso R S T

/-- thSz9ZHDK9o-34520 (9:35:20) [prop] (affine base) `X ↦ Γ(X, 𝒪_X)` and `Spec` are inverse
anti-equivalences between affine schemes and rings. -/
def prop_34520 : AffineScheme.{u} ≌ CommRingCat.{u}ᵒᵖ := AffineScheme.equivCommRingCat

/-- thSz9ZHDK9o-34651 (9:37:31) [prop] (sections over `D(k)`) For `φ : K → A` and an `A`-module
`M`, the sections of the direct image of `M~` over `D(k) ⊂ Spec K`, i.e. `M_{φ(k)}`, are the
localization `M_k` of `M` viewed as a `K`-module: the direct image is `(M_K)~`. -/
theorem prop_34651 {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] {M N : Type*}
    [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M] [AddCommGroup N]
    [Module A N] [Module K N] [IsScalarTower K A N] (k : K) (f : M →ₗ[A] N)
    [IsLocalizedModule (.powers (algebraMap K A k)) f] :
    IsLocalizedModule (.powers k) (f.restrictScalars K) :=
  IsLocalizedModule.restrictScalars_powers k f

end RelativeSpec

/-! ### Fibre products of schemes -/

section FibreProducts

/-- thSz9ZHDK9o-34882 (9:41:22) [thm] Finite projective limits exist in schemes and in `Sch/S`. -/
theorem thm_34882 (S : Scheme.{u}) : HasFiniteLimits Scheme.{u} ∧ HasPullbacks (Over S) ∧
    HasTerminal (Over S) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- thSz9ZHDK9o-34949 (9:42:29) [prop] `Spec ℤ` is the final scheme. -/
def prop_34949 : IsTerminal (Spec (.of ℤ)) := specZIsTerminal

/-- thSz9ZHDK9o-34949 (9:42:29) [prop] `S` (with the identity) is the final object of `Sch/S`. -/
def prop_34949_over (S : Scheme.{u}) : IsTerminal (Over.mk (𝟙 S)) := Over.mkIdTerminal

/-- thSz9ZHDK9o-35214 (9:46:54) [prop] For open immersions `U → X`, `V → Y` over `S`, the image of
`U ×_S V → X ×_S Y` is the intersection of the preimages of `U` and `V`, an open set; it is an
open immersion (mathlib: `IsOpenImmersion` of `pullback.map`). -/
theorem prop_35214 {X Y S U V : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : U ⟶ X) (j : V ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    Set.range (pullback.map (i ≫ f) (j ≫ g) f g i j (𝟙 S) (by simp) (by simp)) =
      pullback.fst f g ⁻¹' Set.range i ∩ pullback.snd f g ⁻¹' Set.range j ∧
    IsOpen (Set.range (pullback.map (i ≫ f) (j ≫ g) f g i j (𝟙 S) (by simp) (by simp))) := by
  have h := Scheme.Pullback.range_map (i ≫ f) (j ≫ g) f g i j (𝟙 S) (by simp) (by simp)
  refine ⟨h, h ▸ ?_⟩
  exact ((pullback.fst f g).continuous.isOpen_preimage _ i.isOpenEmbedding.isOpen_range).inter
    ((pullback.snd f g).continuous.isOpen_preimage _ j.isOpenEmbedding.isOpen_range)

/-- thSz9ZHDK9o-35214 (9:46:54) [prop] (the covering) If the `X_i` cover `X` and the `Y_j` cover
`Y`, the `X_i ×_S Y_j` cover `X ×_S Y`. -/
theorem prop_35214_cover {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (𝒰 : X.OpenCover)
    (𝒱 : Y.OpenCover) (z : ↑(pullback f g)) :
    ∃ i j, z ∈ Set.range (pullback.map (𝒰.f i ≫ f) (𝒱.f j ≫ g) f g (𝒰.f i) (𝒱.f j) (𝟙 S)
      (by simp) (by simp)) := by
  refine ⟨𝒰.idx (pullback.fst f g z), 𝒱.idx (pullback.snd f g z), ?_⟩
  rw [Scheme.Pullback.range_map]
  exact ⟨𝒰.covers _, 𝒱.covers _⟩

/-- thSz9ZHDK9o-35549 (9:52:29) [thm] Fibre products of schemes exist; in the affine case
`Spec A ×_{Spec K} Spec B = Spec(A ⊗_K B)` (`prop_34392`). -/
theorem thm_35549 : HasPullbacks Scheme.{u} := inferInstance

/-- thSz9ZHDK9o-35871 (9:57:51) [prop] `X_s → X` is a monomorphism and a homeomorphism onto its
image (a preimmersion). -/
theorem prop_35871 {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    Mono (f.fiberι s) ∧ IsEmbedding (f.fiberι s) :=
  ⟨inferInstance, (f.fiberι s).isEmbedding⟩

/-- thSz9ZHDK9o-36147 (10:02:27) [prop] (affine base) A projective limit of affine schemes
`Spec A_i` is `Spec(lim→ A_i)`: `Spec` preserves limits (it is a right adjoint). -/
theorem prop_36147 : PreservesLimits Scheme.Spec.{u} := inferInstance

/-- thSz9ZHDK9o-36210 (10:03:30) [rem] (binary case) The sum of two commutative `R`-algebras is
their tensor product (the pushout of rings). -/
theorem rem_36210 (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] :
    IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B)))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom) :=
  CommRingCat.isPushout_tensorProduct R A B

/-- thSz9ZHDK9o-36274 (10:04:34) [prop] (affine base) `M ↦ M~` commutes with inductive limits
(a left adjoint), so an inductive limit of quasi-coherent modules `M_i~` is `(lim→ M_i)~`. -/
theorem prop_36274 (R : CommRingCat.{u}) :
    PreservesColimitsOfSize.{u, u} (AlgebraicGeometry.tilde.functor R) :=
  AlgebraicGeometry.tilde.adjunction.leftAdjoint_preservesColimits

/-- thSz9ZHDK9o-36401 (10:06:41) [prop] (affine base, `𝒜 = A`) `Hom(Z, Spec A) = Hom(A,
Γ(Z, 𝒪_Z))` (`def_33684`). -/
def prop_36401 (Z : Scheme.{u}) (R : CommRingCat.{u}) : (Z ⟶ Spec R) ≃ (R ⟶ Γ(Z, ⊤)) :=
  def_33684 Z R

/-- thSz9ZHDK9o-36923 (10:15:23) [rem] For every locally ringed space `Z`,
`Hom(Z, Spec A) = Hom(A, Γ(Z, 𝒪_Z))` (mathlib: `ΓSpec.locallyRingedSpaceAdjunction`). -/
def rem_36923 (Z : LocallyRingedSpace.{u}) (R : CommRingCat.{u}) :
    (Z ⟶ Spec.toLocallyRingedSpace.obj (op R)) ≃ (op (LocallyRingedSpace.Γ.obj (op Z)) ⟶ op R) :=
  (ΓSpec.locallyRingedSpaceAdjunction.homEquiv Z (op R)).symm

end FibreProducts

/-! ### Automorphism groups -/

section Aut

/-- thSz9ZHDK9o-37247 (10:20:47) [prop] (free case, pointwise) The automorphisms of the free
module `k'^n` are `GL_n(k')`. -/
def prop_37247 (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
    Matrix.GeneralLinearGroup n R ≃* ((n → R) ≃ₗ[R] (n → R)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv R _)

end Aut

/-! ### Localization at a point -/

section LocalizationPoint

/-- thSz9ZHDK9o-37565 (10:26:05) [def] The localization `Spec 𝒪_{X,x} → X` (mathlib:
`Scheme.fromSpecStalk`). -/
def def_37565 (X : Scheme.{u}) (x : X) : Spec (X.presheaf.stalk x) ⟶ X := X.fromSpecStalk x

/-- thSz9ZHDK9o-37701 (10:28:21) [prop] For an affine open `U ∋ x`, the morphism
`Spec 𝒪_{X,x} = Spec Γ(U)_𝔭 → U ⊂ X` does not depend on `U` (mathlib:
`IsAffineOpen.fromSpecStalk_eq_fromSpecStalk`; `𝒪_{X,x} = Γ(U)_𝔭` is
`IsAffineOpen.isLocalization_stalk`). -/
theorem prop_37701 {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    hU.fromSpecStalk hx = X.fromSpecStalk x :=
  hU.fromSpecStalk_eq_fromSpecStalk hx

/-- thSz9ZHDK9o-37765 (10:29:25) [prop] `Spec 𝒪_{X,x} → X` is a monomorphism, injective on
points. -/
theorem prop_37765 (X : Scheme.{u}) (x : X) :
    Mono (X.fromSpecStalk x) ∧ Function.Injective (X.fromSpecStalk x) :=
  ⟨inferInstance, (X.fromSpecStalk x).isEmbedding.injective⟩

/-- thSz9ZHDK9o-37831 (10:30:31) [prop] `Spec 𝒪_{X,x} → X` is a homeomorphism onto its image. -/
theorem prop_37831 (X : Scheme.{u}) (x : X) : IsEmbedding (X.fromSpecStalk x) :=
  (X.fromSpecStalk x).isEmbedding

/-- thSz9ZHDK9o-37831 (10:30:31) [prop] The spectrum of a local ring has a unique closed point,
a specialization of every point. -/
theorem prop_37831_closedPoint (R : Type*) [CommRing R] [IsLocalRing R] :
    IsClosed ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R)) ∧
      (∀ y : PrimeSpectrum R, y ⤳ IsLocalRing.closedPoint R) ∧
      ∀ y : PrimeSpectrum R, IsClosed ({y} : Set (PrimeSpectrum R)) →
        y = IsLocalRing.closedPoint R := by
  refine ⟨IsLocalRing.isClosed_singleton_closedPoint R, IsLocalRing.specializes_closedPoint,
    fun y hy => ?_⟩
  rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal] at hy
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hy)

/-- thSz9ZHDK9o-37894 (10:31:34) [prop] A continuous map preserves specialization. -/
theorem prop_37894 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf : Continuous f) {x y : X} (h : x ⤳ y) : f x ⤳ f y :=
  h.map hf

end LocalizationPoint

end

end Buffalo.AG.Part05
