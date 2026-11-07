import Buffalo.AG.Part03b

/-!
# Buffalo, algebraic geometry, part 03 (c): 12 June 1973, to 1:36:31

The entries of `docs/buffalo-ag/index.tex` lines 442–491 (video `thSz9ZHDK9o`, 0:01:06–1:36:31):
disjoint and universal sums, constant objects, monomorphisms and the spectrum, the structure sheaf
and quasi-coherent modules, gluing and descent.

Conventions. An affine algebraic space over `K` is a `K`-algebra read in the opposite category; a
monomorphism `Y → S` of affine spaces is an epimorphism of rings `A → C`, stated as: two ring maps
out of `C` that agree on `A` are equal. Statements about fibre products of spectra are made either
at the level of rings or for mathlib's schemes.
-/

open CategoryTheory TensorProduct Topology PrimeSpectrum

universe u

namespace Buffalo.AG.Part03

noncomputable section

/-! ### Flatness, diagonal, sums -/

section Sums

variable {A : Type*} [CommRing A]

/-- thSz9ZHDK9o-66 (0:01:06) [def] `M` is flat if `- ⊗ M` is exact (mathlib: `Module.Flat`; see
`_lTf_L0yvrU-17573`). -/
example (M : Type*) [AddCommGroup M] [Module A M] [Module.Flat A M] {N₁ N₂ N₃ : Type*}
    [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂] [Module A N₂] [AddCommGroup N₃] [Module A N₃]
    (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃) (h : Function.Exact f g) :
    Function.Exact (f.rTensor M) (g.rTensor M) :=
  Module.Flat.rTensor_exact M h

/-- thSz9ZHDK9o-129 (0:02:09) [prop] The diagonal of `Spec A` over `K` is a closed immersion,
`A ⊗_K A → A` being surjective (`prop_37586`). -/
theorem prop_129 (K : Type*) [CommRing K] [Algebra K A] :
    IsClosedEmbedding (comap (Algebra.TensorProduct.lmul' K : A ⊗[K] A →ₐ[K] A).toRingHom) :=
  (prop_37586 K).2

/-- thSz9ZHDK9o-336 (0:05:36) [prop] Finite sums of affine spaces correspond to finite products of
algebras (mathlib, for affine schemes: `AlgebraicGeometry.sigmaSpec` is an isomorphism for a finite
family). -/
theorem prop_336 {ι : Type u} [Finite ι] (R : ι → CommRingCat.{u}) :
    IsIso (AlgebraicGeometry.sigmaSpec R) :=
  inferInstance

/-- thSz9ZHDK9o-401 (0:06:41) [def] A sum is disjoint if the injections are monomorphisms and the
`X_i ×_X X_j`, `i ≠ j`, are initial (mathlib: `Limits.CoproductDisjoint`,
`Limits.BinaryCoproductDisjoint`). -/
example {C : Type*} [Category C] (X Y : C) : Prop := Limits.BinaryCoproductDisjoint X Y

/-- thSz9ZHDK9o-464 (0:07:44) [def] A sum is universal if it is stable under every base change
(mathlib: `IsUniversalColimit`; finitely: `FinitaryPreExtensive`). -/
example {C : Type*} [Category C] {X Y : C} (c : Limits.BinaryCofan X Y) : Prop :=
  IsUniversalColimit c

/-- thSz9ZHDK9o-527 (0:08:47) [prop] `u` is a monomorphism iff `X ×_Y X ≃ X` via the diagonal
(mathlib: `Limits.pullback.isIso_diagonal_iff`). -/
theorem prop_527 {C : Type*} [Category C] {X Y : C} (u : X ⟶ Y) [Limits.HasPullback u u] :
    IsIso (Limits.pullback.diagonal u) ↔ Mono u :=
  Limits.pullback.isIso_diagonal_iff u

/-- If an element of `R` acts as `1` on `S` and as `0` on `T`, then `S ⊗_R T = 0`. -/
theorem subsingleton_tensor_of_idempotent {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (e : R) (hS : algebraMap R S e = 1) (hT : algebraMap R T e = 0) :
    Subsingleton (S ⊗[R] T) := by
  refine subsingleton_of_zero_eq_one ?_
  rw [Algebra.TensorProduct.one_def]
  have h1 : (1 : S) = e • (1 : S) := by rw [Algebra.smul_def, hS, mul_one]
  rw [h1, smul_tmul, Algebra.smul_def, hT, zero_mul, tmul_zero]

/-- The same, for algebra structures given by ring homomorphisms. -/
theorem subsingleton_tensor_of_ringHom {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (fS : R →+* S) (fT : R →+* T) (e : R) (hS : fS e = 1) (hT : fT e = 0) :
    @Subsingleton (@TensorProduct R _ S T _ _ fS.toAlgebra.toModule fT.toAlgebra.toModule) := by
  let := fS.toAlgebra
  let := fT.toAlgebra
  exact subsingleton_tensor_of_idempotent e hS hT

/-- thSz9ZHDK9o-658 (0:10:58) [prop] For `A = A₁ × A₂`, the `A → A_i` are surjective (closed
immersions) and `A₁ ⊗_A A₂ = 0`. -/
theorem prop_658 (A₁ A₂ : Type*) [CommRing A₁] [CommRing A₂] :
    Function.Surjective (RingHom.fst A₁ A₂) ∧ Function.Surjective (RingHom.snd A₁ A₂) ∧
      @Subsingleton (@TensorProduct (A₁ × A₂) _ A₁ A₂ _ _ (RingHom.fst A₁ A₂).toAlgebra.toModule
        (RingHom.snd A₁ A₂).toAlgebra.toModule) := by
  exact ⟨fun a => ⟨(a, 0), rfl⟩, fun a => ⟨(0, a), rfl⟩,
    subsingleton_tensor_of_ringHom _ _ (1, 0) rfl rfl⟩

/-- thSz9ZHDK9o-593 (0:09:53) [prop] Finite sums of affine algebraic spaces are disjoint and
universal. Proved: the disjointness `A₁ ⊗_{A₁ × A₂} A₂ = 0` (`prop_658`); mathlib has finitary
extensivity (universal and disjoint finite sums) for all schemes (`FinitaryExtensive Scheme`). -/
theorem prop_593 : FinitaryExtensive AlgebraicGeometry.Scheme.{u} := inferInstance

/-- thSz9ZHDK9o-918 (0:15:18) [prop] If finite sums are universal, products (and fibre products)
distribute over them: `∐ (X_i ×_S Y_j) ≃ (∐ X_i) ×_S (∐ Y_j)` (mathlib:
`FinitaryPreExtensive.isIso_sigmaDesc_map`). -/
theorem prop_918 {C : Type*} [Category C] [Limits.HasPullbacks C] [FinitaryPreExtensive C]
    {ι ι' : Type*} [Finite ι] [Finite ι'] {S : C} {X : ι → C} {Y : ι' → C}
    (f : ∀ i, X i ⟶ S) (g : ∀ i, Y i ⟶ S) :
    IsIso (Limits.Sigma.desc fun (p : ι × ι') ↦
      Limits.pullback.map (f p.1) (g p.2) (Limits.Sigma.desc f) (Limits.Sigma.desc g)
        (Limits.Sigma.ι _ p.1) (Limits.Sigma.ι _ p.2) (𝟙 S) (by simp) (by simp)) :=
  inferInstance

/-- thSz9ZHDK9o-1176 (0:19:36) [def] The constant object `I_C = ∐_I e`. -/
abbrev constObj (C : Type*) [Category C] [Limits.HasTerminal C] (I : Type*)
    [Limits.HasCoproduct fun _ : I => ⊤_ C] : C :=
  ∐ fun _ : I => ⊤_ C

/-- thSz9ZHDK9o-1239 (0:20:39) [prop] (corrected) If finite sums are disjoint and universal,
`I ↦ I_C` is left exact. Proved: the product part `I_C × J_C ≃ (I × J)_C`, which needs only
universality (`prop_918` over the final object), and, for affine spaces, the disjointness used for
fibre products: two distinct points `e ⇉ I_C` have empty intersection, `K ⊗_{K^I} K = 0`. -/
theorem prop_1239 {C : Type*} [Category C] [Limits.HasPullbacks C] [FinitaryPreExtensive C]
    (T : C) (hT : Limits.IsTerminal T) {I J : Type*} [Finite I] [Finite J] :
    IsIso (Limits.Sigma.desc fun (p : I × J) ↦
      Limits.pullback.map (hT.from T) (hT.from T) (Limits.Sigma.desc fun _ : I => hT.from T)
        (Limits.Sigma.desc fun _ : J => hT.from T) (Limits.Sigma.ι (fun _ : I => T) p.1)
        (Limits.Sigma.ι (fun _ : J => T) p.2) (𝟙 T) (by simp) (by simp)) :=
  prop_918 _ _

theorem prop_1239_disjoint (K : Type*) [Field K] {I : Type*} [DecidableEq I] {i j : I}
    (hij : i ≠ j) :
    @Subsingleton (@TensorProduct (I → K) _ K K _ _ (Pi.evalRingHom (fun _ => K) i).toAlgebra.toModule
      (Pi.evalRingHom (fun _ => K) j).toAlgebra.toModule) := by
  exact subsingleton_tensor_of_ringHom _ _ (Pi.single i 1) (by simp) (by simp [hij.symm])

/-- thSz9ZHDK9o-1369 (0:22:49) [prop] For `I` a finite group, `I_K` is an affine algebraic group.
Proved: its points with values in a field `L` are the elements of `I` (every `K`-algebra map
`K^I → L` is an evaluation); the Hopf algebra structure is `comul` (`prop_1568`). -/
theorem prop_1369 (K L : Type*) [Field K] [Field L] [Algebra K L] {I : Type*} [Fintype I]
    [DecidableEq I] (φ : (I → K) →ₐ[K] L) : ∃! i : I, ∀ x : I → K, φ x = algebraMap K L (x i) := by
  set e : I → (I → K) := fun i => Pi.single i 1 with he
  have hsmul : ∀ (x : I → K) j, Pi.single j (x j) = x j • e j := fun x j => by
    ext k; by_cases h : k = j <;> simp [he, h]
  have hexp : ∀ x : I → K, φ x = ∑ j, algebraMap K L (x j) * φ (e j) := fun x => by
    conv_lhs => rw [← Finset.univ_sum_single x]
    simp [map_sum, hsmul, Algebra.smul_def]
  have hidem : ∀ i, φ (e i) = 0 ∨ φ (e i) = 1 := fun i =>
    IsIdempotentElem.iff_eq_zero_or_one.1 (by
      rw [IsIdempotentElem, ← map_mul]
      congr 1; ext k; by_cases h : k = i <;> simp [he, h])
  have horth : ∀ i j, i ≠ j → φ (e i) * φ (e j) = 0 := fun i j hij => by
    rw [← map_mul, show e i * e j = 0 by
      ext k; by_cases h : k = i <;> simp [he, Pi.single_apply, h, hij], map_zero]
  have hsum : ∑ i, φ (e i) = 1 := by
    rw [← map_sum, show ∑ i, e i = 1 from Finset.univ_sum_single (fun _ => (1 : K)), map_one]
  obtain ⟨i, hi⟩ : ∃ i, φ (e i) = 1 := by
    by_contra! h
    have : ∀ i, φ (e i) = 0 := fun i => (hidem i).resolve_right (h i)
    simp [this] at hsum
  have hj : ∀ j, j ≠ i → φ (e j) = 0 := fun j hji => by
    simpa [hi] using horth i j hji.symm
  refine ⟨i, fun x => ?_, fun j hj' => ?_⟩
  · rw [hexp x, Finset.sum_eq_single i (fun j _ h => by rw [hj j h, mul_zero])
      (fun h => absurd (Finset.mem_univ i) h), hi, mul_one]
  · by_contra h
    have := hj' (e i)
    have hi' : φ (Pi.single i 1) = 1 := hi
    simp [he, h, hi'] at this

/-- thSz9ZHDK9o-1437 (0:23:57) [prop] A functor between categories with finite limits is left exact
iff it preserves fibre products and the final object (mathlib:
`Limits.preservesFiniteLimits_of_preservesTerminal_and_pullbacks`). -/
theorem prop_1437 {C D : Type*} [Category C] [Category D] [Limits.HasTerminal C]
    [Limits.HasPullbacks C] (G : C ⥤ D) :
    Limits.PreservesFiniteLimits G ↔
      Limits.PreservesLimitsOfShape (Discrete PEmpty.{1}) G ∧
        Limits.PreservesLimitsOfShape Limits.WalkingCospan G :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ =>
    Limits.preservesFiniteLimits_of_preservesTerminal_and_pullbacks G⟩

/-- thSz9ZHDK9o-1502 (0:25:02) [prop] `I_K = Spec K^I`: `K^I` is the product of `I` copies of `K`
in `K`-algebras, so its spectrum is the sum of `I` copies of the final object (mathlib, for
schemes: `prop_336`). -/
def prop_1502 (K A : Type*) [CommRing K] [CommRing A] [Algebra K A] (I : Type*) :
    (A →ₐ[K] (I → K)) ≃ (I → (A →ₐ[K] K)) where
  toFun φ i := (Pi.evalAlgHom K (fun _ => K) i).comp φ
  invFun ψ := AlgHom.pi ψ
  left_inv φ := by ext; rfl
  right_inv ψ := by ext; rfl

/-- thSz9ZHDK9o-1568 (0:26:08) [prop] The law `I × I → I` induces the comultiplication
`K^I → K^{I×I}`, `φ ↦ ((i, j) ↦ φ(ij))`, transpose to the law, and `K^{I×I} ≃ K^I ⊗_K K^I` for
`I` finite (mathlib: `finsuppTensorFinsupp'`). -/
def comul (K : Type*) [CommRing K] (I : Type*) [Mul I] : (I → K) →ₐ[K] (I × I → K) :=
  AlgHom.pi fun p => Pi.evalAlgHom K (fun _ => K) (p.1 * p.2)

theorem prop_1568 (K : Type*) [CommRing K] (I : Type*) [Mul I] (φ : I → K) (i j : I) :
    comul K I φ (i, j) = φ (i * j) ∧
      Nonempty (((I →₀ K) ⊗[K] (I →₀ K)) ≃ₗ[K] (I × I →₀ K)) :=
  ⟨rfl, ⟨finsuppTensorFinsupp' K I I⟩⟩

end Sums

/-! ### Monomorphisms, fibres and the spectrum -/

section Mono

/-- thSz9ZHDK9o-1836 (0:30:36) [prop] If `Y → S` is a monomorphism of affine spaces, i.e.
`u : A → C` is an epimorphism of rings, `Spec C → Spec A` is injective: two primes over the same
`𝔭` give two maps of `C` to a common field over `κ(𝔭)`, which agree on `A`. -/
theorem prop_1836 {A C : Type u} [CommRing A] [CommRing C] (u : A →+* C)
    (hu : ∀ (T : Type u) [CommRing T] (g h : C →+* T), g.comp u = h.comp u → g = h) :
    Function.Injective (comap u) := by
  intro q₁ q₂ hq
  have h₁ : (comap u q₁).asIdeal = q₁.asIdeal.comap u := rfl
  have h₂ : (comap u q₁).asIdeal = q₂.asIdeal.comap u := by rw [hq]; rfl
  let : Algebra (comap u q₁).asIdeal.ResidueField q₁.asIdeal.ResidueField :=
    (Ideal.ResidueField.map _ _ u h₁).toAlgebra
  let : Algebra (comap u q₁).asIdeal.ResidueField q₂.asIdeal.ResidueField :=
    (Ideal.ResidueField.map _ _ u h₂).toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal
    (q₁.asIdeal.ResidueField ⊗[(comap u q₁).asIdeal.ResidueField] q₂.asIdeal.ResidueField)
  let L := (q₁.asIdeal.ResidueField ⊗[(comap u q₁).asIdeal.ResidueField]
    q₂.asIdeal.ResidueField) ⧸ m
  let : Field L := Ideal.Quotient.field m
  let j₁ : q₁.asIdeal.ResidueField →+* L :=
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom
  let j₂ : q₂.asIdeal.ResidueField →+* L :=
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom
  have key := hu L (j₁.comp (algebraMap C _)) (j₂.comp (algebraMap C _)) (by
    ext a
    simp only [RingHom.comp_apply, j₁, j₂, Algebra.TensorProduct.includeLeftRingHom_apply]
    rw [← Ideal.ResidueField.map_algebraMap _ _ u h₁, ← Ideal.ResidueField.map_algebraMap _ _ u h₂]
    congr 1
    change (algebraMap _ q₁.asIdeal.ResidueField (algebraMap A _ a)) ⊗ₜ 1 =
      1 ⊗ₜ (algebraMap _ q₂.asIdeal.ResidueField (algebraMap A _ a))
    rw [Algebra.algebraMap_eq_smul_one (A := q₁.asIdeal.ResidueField),
      Algebra.algebraMap_eq_smul_one (A := q₂.asIdeal.ResidueField), smul_tmul])
  have hker : ∀ (q : PrimeSpectrum C) (j : q.asIdeal.ResidueField →+* L),
      RingHom.ker (j.comp (algebraMap C _)) = q.asIdeal := fun q j => by
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot j).1 j.injective,
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
  exact PrimeSpectrum.ext ((hker q₁ j₁).symm.trans (by rw [key]; exact hker q₂ j₂))

/-- thSz9ZHDK9o-1899 (0:31:39) [prop] `Spec(X ×_S Y)` is, in `Spec X`, the preimage of `Spec Y`
(mathlib, for schemes and without the monomorphism hypothesis for the image:
`Scheme.Pullback.range_fst`; with `prop_1836` the map is moreover injective in the affine case). -/
theorem prop_1899 {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (Limits.pullback.fst f g) = f ⁻¹' Set.range g :=
  AlgebraicGeometry.Scheme.Pullback.range_fst f g

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- thSz9ZHDK9o-2093 (0:34:53) [prop] If `A → C` is surjective, so is `B → B ⊗_A C`, and the
topology of `Spec(B ⊗_A C)` is induced by that of `Spec B` (closed embedding). -/
theorem prop_2093 (C : Type*) [CommRing C] [Algebra A C]
    (hC : Function.Surjective (algebraMap A C)) :
    Function.Surjective (algebraMap B (B ⊗[A] C)) ∧
      IsClosedEmbedding (comap (algebraMap B (B ⊗[A] C))) := by
  have hs : Function.Surjective (algebraMap B (B ⊗[A] C)) :=
    Algebra.TensorProduct.includeLeft_surjective (R := A) (T := C) B B hC
  exact ⟨hs, isClosedEmbedding_comap_of_surjective _ _ hs⟩

/-- thSz9ZHDK9o-2156 (0:35:56) [prop] `B ⊗_A A_f = B_f` and the topology of `Spec(B ⊗_A A_f)` is
induced by that of `Spec B` (open embedding) (mathlib: `IsLocalization.Away.tensor`). -/
theorem prop_2156 (f : A) :
    IsLocalization.Away (algebraMap A B f) (B ⊗[A] Localization.Away f) ∧
      IsOpenEmbedding (comap (algebraMap B (B ⊗[A] Localization.Away f))) :=
  ⟨inferInstance, localization_away_isOpenEmbedding _ (algebraMap A B f)⟩

/-- thSz9ZHDK9o-2288 (0:38:08) [prop] If `A → C` is a quotient followed by a localization (an
immersion), the topology of `Spec(B ⊗_A C)` is induced by that of `Spec B`. Proved for schemes:
immersions are stable under base change and are embeddings, with image the preimage
(`prop_1899`). -/
theorem prop_2288 {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [AlgebraicGeometry.IsImmersion g] :
    IsEmbedding (Limits.pullback.fst f g) ∧ Set.range (Limits.pullback.fst f g) = f ⁻¹' Set.range g :=
  ⟨AlgebraicGeometry.Scheme.Hom.isEmbedding _, AlgebraicGeometry.Scheme.Pullback.range_fst f g⟩

/-- thSz9ZHDK9o-2416 (0:40:16) [prop] For two subobjects `X`, `Y` of `S`,
`Spec(X ∩ Y) = Spec X ∩ Spec Y` in `Spec S` (mathlib, for schemes:
`Scheme.Pullback.range_fst_comp`; true for any two morphisms). -/
theorem prop_2416 {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (Limits.pullback.fst f g ≫ f) = Set.range f ∩ Set.range g :=
  AlgebraicGeometry.Scheme.Pullback.range_fst_comp f g

/-- thSz9ZHDK9o-2613 (0:43:33) [prop] The fibre `X ×_S Spec κ(𝔭)` has as underlying space the fibre
of `X → S` at `𝔭`, with the induced topology (mathlib: `Scheme.Hom.fiberHomeo`). -/
def prop_2613 {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (s : S) :
    f.fiber s ≃ₜ f ⁻¹' {s} :=
  f.fiberHomeo s

/-- thSz9ZHDK9o-2810 (0:46:50) [prop] The closure of `φ(V(J))` is `V(u⁻¹(J))` (mathlib:
`PrimeSpectrum.closure_image_comap_zeroLocus`). -/
theorem prop_2810 {A B : Type*} [CommRing A] [CommRing B] (u : A →+* B) (J : Ideal B) :
    closure (comap u '' zeroLocus (J : Set B)) = zeroLocus (J.comap u : Set A) :=
  closure_image_comap_zeroLocus u J

/-- thSz9ZHDK9o-3134 (0:52:14) [prop] `Spec u` is dominant iff `ker u ⊂ nil(A)`; for `A` reduced, iff
`u` is injective (mathlib: `PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical`). -/
theorem prop_3134 {A B : Type*} [CommRing A] [CommRing B] (u : A →+* B) :
    (DenseRange (comap u) ↔ RingHom.ker u ≤ nilradical A) ∧
      (IsReduced A → (DenseRange (comap u) ↔ Function.Injective u)) := by
  refine ⟨denseRange_comap_iff_ker_le_nilRadical u, fun _ => ?_⟩
  rw [denseRange_comap_iff_ker_le_nilRadical u, nilradical_eq_zero, Ideal.zero_eq_bot, le_bot_iff,
    ← RingHom.injective_iff_ker_eq_bot]

end Mono

/-! ### The structure sheaf and quasi-coherent modules -/

section Quasicoherent

/-- thSz9ZHDK9o-3405 (0:56:45) [prop] `X_f ↦ M_f` defines a sheaf `M~` of `A`-modules (mathlib:
`AlgebraicGeometry.tilde`; sections over `D(f)` are `M_f`, `_lTf_L0yvrU-14490`). -/
example {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f : R) :
    IsLocalizedModule.Away f (AlgebraicGeometry.tilde.toOpen M (basicOpen f)).hom :=
  inferInstance

/-- thSz9ZHDK9o-3469 (0:57:49) [prop] `A~` is a sheaf of `A`-algebras with `Γ(X, A~) = A`
(mathlib: `AlgebraicGeometry.StructureSheaf.globalSectionsIso`). -/
def prop_3469 (R : Type u) [CommRing R] :
    CommRingCat.of R ≅ (AlgebraicGeometry.Spec.structureSheaf R).obj.obj (Opposite.op ⊤) :=
  AlgebraicGeometry.StructureSheaf.globalSectionsIso R

/-- thSz9ZHDK9o-3533 (0:58:53) [def] The structure sheaf `𝒪_X = A~` of `X = Spec A` (mathlib:
`AlgebraicGeometry.Spec.structureSheaf`); `A = Γ(X, 𝒪_X)` (`prop_3469`). -/
example (R : Type u) [CommRing R] :
    (AlgebraicGeometry.Spec.topObj (CommRingCat.of R)).Sheaf CommRingCat.{u} :=
  AlgebraicGeometry.Spec.structureSheaf R

/-- thSz9ZHDK9o-3728 (1:02:08) [prop] `M ↦ M~` is exact and commutes with inductive limits and
tensor products. Proved: it commutes with all colimits, being a left adjoint (mathlib:
`AlgebraicGeometry.tilde.adjunction`); exactness and tensor products are not formalised (sections
over `D(f)`: `prop_4112`). -/
theorem prop_3728 (R : CommRingCat.{u}) :
    Limits.PreservesColimitsOfSize.{u, u} (AlgebraicGeometry.tilde.functor R) :=
  AlgebraicGeometry.tilde.adjunction.leftAdjoint_preservesColimits

/-- thSz9ZHDK9o-3792 (1:03:12) [prop] For `M` finitely presented, `Hom_A(M, N)~ ≃ Hom(M~, N~)`;
for `A` noetherian, finitely presented = finitely generated. Proved: on each `D(f)`,
`Hom_A(M, N)_f = Hom_{A_f}(M_f, N_f)` (mathlib: `Module.FinitePresentation.isLocalizedModule_map`),
and the noetherian case (mathlib: `Module.finitePresentation_of_finite`); the internal `Hom` of
sheaves of modules is not formalised. -/
theorem prop_3792 {A : Type*} [CommRing A] (M N : Type*) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.FinitePresentation A M] (f : A) :
    IsLocalizedModule (Submonoid.powers f)
      (IsLocalizedModule.map (Submonoid.powers f) (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) N)) ∧
    (IsNoetherianRing A → (Module.Finite A N ↔ Module.FinitePresentation A N)) :=
  ⟨Module.FinitePresentation.isLocalizedModule_map _ _ _,
    fun _ => ⟨fun _ => Module.finitePresentation_of_finite A N, fun _ => inferInstance⟩⟩

/-- thSz9ZHDK9o-3856 (1:04:16) [prop] `M ↦ M~` is fully faithful (mathlib:
`AlgebraicGeometry.tilde.fullyFaithfulFunctor`). -/
def prop_3856 (R : CommRingCat.{u}) : (AlgebraicGeometry.tilde.functor R).FullyFaithful :=
  AlgebraicGeometry.tilde.fullyFaithfulFunctor

/-- thSz9ZHDK9o-4112 (1:08:32) [prop] `M~ ⊗ N~ ≃ (M ⊗ N)~`. Proved on sections over each `D(f)`:
`(M ⊗ N)_f ≃ M_f ⊗_{A_f} N_f` (mathlib: `AlgebraTensorModule.distribBaseChange`, with
`M_f = A_f ⊗ M`, `prop_17115`); the tensor product of sheaves of modules is not formalised. -/
def prop_4112 {A : Type*} [CommRing A] (M N : Type*) [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : A) :
    Localization.Away f ⊗[A] (M ⊗[A] N) ≃ₗ[Localization.Away f]
      (Localization.Away f ⊗[A] M) ⊗[Localization.Away f] (Localization.Away f ⊗[A] N) :=
  TensorProduct.AlgebraTensorModule.distribBaseChange A _ M N

/-- thSz9ZHDK9o-4703 (1:18:23) [def] An `𝒪_X`-module is quasi-coherent if it is locally a cokernel
of free modules (mathlib: `SheafOfModules.IsQuasicoherent`). -/
example (R : CommRingCat.{u}) (M : (AlgebraicGeometry.Spec R).Modules) : Prop := M.IsQuasicoherent

/-- thSz9ZHDK9o-4841 (1:20:41) [thm] On `Spec A`, an `𝒪_X`-module is quasi-coherent iff it is
isomorphic to some `M~` (mathlib: `AlgebraicGeometry.essImage_tilde`). -/
theorem thm_4841 (R : CommRingCat.{u}) :
    (AlgebraicGeometry.tilde.functor R).essImage =
      SheafOfModules.isQuasicoherent (AlgebraicGeometry.Spec R).ringCatSheaf :=
  AlgebraicGeometry.essImage_tilde

/-- thSz9ZHDK9o-4903 (1:21:43) [prop] Every `M~` is a cokernel of free modules, and conversely
such a cokernel is some `M~` (mathlib: `AlgebraicGeometry.presentationTilde`,
`AlgebraicGeometry.isIso_fromTildeΓ_of_presentation`). -/
theorem prop_4903 {R : CommRingCat.{u}} (M : (AlgebraicGeometry.Spec R).Modules)
    (P : M.Presentation) : IsIso M.fromTildeΓ :=
  AlgebraicGeometry.isIso_fromTildeΓ_of_presentation M P

end Quasicoherent

/-! ### Gluing and descent -/

section Descent

variable {A : Type*} [CommRing A]

/-- thSz9ZHDK9o-5103 (1:25:03) [prop] Modules on a finite cover by `X_{f_i}` with gluing data
come from an `A`-module. Proved: extension of scalars along the faithfully flat
`A → ∏ A_{f_i}` (`prop_37263`) is comonadic (mathlib: `comonadicExtendScalars`), i.e. descent
for modules is effective; the identification of coalgebras with gluing data is not stated. -/
@[instance_reducible]
def prop_5103 {ι : Type u} [Fintype ι] {R : Type u} [CommRing R] (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤) :
    ComonadicLeftAdjoint (ModuleCat.extendScalars.{_, _, u}
      (algebraMap R (Π i, Localization.Away (f i)))) :=
  comonadicExtendScalars (RingHom.faithfullyFlat_algebraMap_iff.2 (prop_37263 f hf))

/-- thSz9ZHDK9o-5165 (1:26:05) [prop] For `A' = ∏ A_{f_i}`, `A' ⊗_A A' ≃ ∏ A_{f_i f_j}`, so the
gluing datum is a descent datum. Proved: each `A_f ⊗_A A_g ≃ (A_f)_g` (`prop_17311`). -/
def prop_5165 (f g : A) :
    Localization.Away f ⊗[A] Localization.Away g ≃ₐ[Localization.Away f]
      Localization.Away (algebraMap A (Localization.Away f) g) :=
  prop_17311 f g

/-- thSz9ZHDK9o-5297 (1:28:17) [prop] If `X = ⋃ X_{f_i}` (finite), `A → ∏ A_{f_i}` is faithfully
flat (`prop_37263`). -/
theorem prop_5297 {ι : Type*} [Fintype ι] (f : ι → A) (hf : Ideal.span (Set.range f) = ⊤) :
    Module.FaithfullyFlat A (Π i, Localization.Away (f i)) :=
  prop_37263 f hf

/-- thSz9ZHDK9o-5551 (1:32:31) [def] `X' → X` is of effective descent for a fibred category `F` if
`F(X) → D_{X'/X}(F(X'))` is an equivalence (mathlib: `Pseudofunctor.DescentData`,
`Pseudofunctor.toDescentData`; full faithfulness is `IsPrestackFor`). -/
example {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) : Prop :=
  (F.toDescentData f).IsEquivalence

/-- thSz9ZHDK9o-5614 (1:33:34) [prop] If `X' → X` admits a section, it is of effective descent for
every fibred category. Proved: its descent data are equivalent, compatibly with `F(X) → D`, to the
descent data for the identity of `X` (both families generate the maximal sieve; mathlib:
`Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq`); that the identity is of effective
descent is not stated in mathlib. -/
theorem prop_5614 {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {X S : C} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) :
    ∃ e : F.DescentData (fun _ : Unit => f) ≌ F.DescentData (fun _ : Unit => 𝟙 S),
      Nonempty (F.toDescentData (fun _ : Unit => f) ⋙ e.functor ≅
        F.toDescentData (fun _ : Unit => 𝟙 S)) := by
  refine Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq F _ _ ?_
  have h₁ : Sieve.ofArrows (fun _ : Unit => X) (fun _ => f) = ⊤ := by
    refine Sieve.id_mem_iff_eq_top.1 ?_
    rw [← hs]
    exact Sieve.downward_closed _ (Sieve.ofArrows_mk (fun _ : Unit => X) (fun _ => f) ()) s
  have h₂ : Sieve.ofArrows (fun _ : Unit => S) (fun _ => 𝟙 S) = ⊤ :=
    Sieve.id_mem_iff_eq_top.1 (Sieve.ofArrows_mk _ _ ())
  rw [h₁, h₂]

/-- thSz9ZHDK9o-5680 (1:34:40) [prop] If `A → A'` is faithfully flat, `Spec A' → Spec A` is of
effective descent for modules. Proved in comonadic form (mathlib: `comonadicExtendScalars`), with
`H⁰` (`thm_35250`). -/
@[instance_reducible]
def prop_5680 {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.FaithfullyFlat) :
    ComonadicLeftAdjoint (ModuleCat.extendScalars.{_, _, u} f) :=
  comonadicExtendScalars hf

/-- thSz9ZHDK9o-5791 (1:36:31) [thm] `M ↦ M~` is an equivalence between `A`-modules and
quasi-coherent `𝒪_X`-modules (mathlib: `AlgebraicGeometry.tildeEquiv`). -/
def thm_5791 (R : CommRingCat.{u}) :
    ModuleCat R ≌ (SheafOfModules.isQuasicoherent (AlgebraicGeometry.Spec R).ringCatSheaf).FullSubcategory :=
  AlgebraicGeometry.tildeEquiv

end Descent

end

end Buffalo.AG.Part03
