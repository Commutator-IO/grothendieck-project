import Buffalo.AG.Part01a

/-!
# Buffalo, algebraic geometry, part 01 (b): 30 May 1973

The session of 30 May 1973 (video `51wmmpHand0`, 1:34:31–3:07:15): the dictionary between
closed subspaces and ideals, radicals and the Nullstellensatz (tested on fields, on finite
extensions, on `k` when `k` is algebraically closed), the algebra of functions of an affine space,
and products, sums and filtered limits. Notation as in `Buffalo.AG.Part01a`.
-/

open CategoryTheory MvPolynomial

universe u

namespace Buffalo.AG.Part01

noncomputable section

section May30

variable (k : Type u) [CommRing k] {I : Type u}

/-- 51wmmpHand0-5809 (1:36:49) [prop] `E^1` (the forgetful functor `k' ↦ k'`) is represented by
`k[t]`, by `φ ↦ φ(t)`. -/
def E1.corepresentableBy :
    (forget (CommAlgCat.{u} k)).CorepresentableBy (CommAlgCat.of k (Polynomial k)) where
  homEquiv :=
    { toFun := fun φ => φ Polynomial.X
      invFun := fun t => CommAlgCat.ofHom (Polynomial.aeval t)
      left_inv := fun φ => by
        apply CommAlgCat.hom_ext
        apply Polynomial.algHom_ext
        exact Polynomial.aeval_X _
      right_inv := fun t => Polynomial.aeval_X t }
  homEquiv_comp _ _ := rfl

/-- 51wmmpHand0-5809 (1:36:49) [prop] `E^I` is the `I`-th cartesian power of `E^1`. -/
theorem prop_5809 (k' : CommAlgCat.{u} k) :
    (E k I).obj k' = (I → (forget (CommAlgCat.{u} k)).obj k') := rfl

/-- 51wmmpHand0-5871 (1:37:51) [def] The `k'`-points of `V_S` are the elements of `k'^I` that
satisfy the equations of `S`. -/
example (S : Set (MvPolynomial I k)) (k' : CommAlgCat.{u} k) (x : I → k') :
    x ∈ (VS k S).obj k' ↔ ∀ f ∈ S, aeval x f = 0 := Iff.rfl

/-- 51wmmpHand0-6129 (1:42:09) [prop] The functors isomorphic to some `V_S` are exactly the
representable functors; `V_J` is represented by `P_I/J`. -/
theorem prop_6129 (F : CommAlgCat.{u} k ⥤ Type u) :
    ((∃ (I : Type u) (S : Set (MvPolynomial I k)), Nonempty (F ≅ (VS k S).toFunctor)) ↔
      F.IsCorepresentable) ∧
    ∀ J : Ideal (MvPolynomial I k), Nonempty ((VJ k J).toFunctor ≅ V k (MvPolynomial I k ⧸ J)) :=
  ⟨prop_2430 k F, fun J => ⟨prop_2889 k J⟩⟩

/-- The essential image of `coyoneda` consists of the representable functors. -/
theorem essImage_coyoneda_iff (F : CommAlgCat.{u} k ⥤ Type u) :
    coyoneda.essImage F ↔ F.IsCorepresentable := by
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    exact Functor.IsCorepresentable.mk' (X := X.unop) e
  · intro _
    exact ⟨Opposite.op F.coreprX, ⟨F.coreprW⟩⟩

/-- 51wmmpHand0-6911 (1:55:11) [prop] The morphisms `V_A → V_{A'}` correspond to the
homomorphisms `A' → A` (`prop_4188`), and the category of affine algebraic spaces (the
representable functors, the essential image of `coyoneda`) is anti-equivalent to that of
`k`-algebras. -/
theorem prop_6911 : (coyoneda (C := CommAlgCat.{u} k)).toEssImage.IsEquivalence ∧
    ∀ F : CommAlgCat.{u} k ⥤ Type u, coyoneda.essImage F ↔ IsAffineAlgSpace k F :=
  ⟨inferInstance, fun F => (essImage_coyoneda_iff k F).trans (prop_3423 k F).symm⟩

/-! ### Radicals and the Nullstellensatz -/

/-- 51wmmpHand0-7174 (1:59:34) [prop] Tested on fields (more generally on reduced `k'`),
`V'_J = V'_{√J}`. -/
theorem prop_7174 (J : Ideal (MvPolynomial I k)) (L : Type*) [CommRing L] [IsReduced L]
    [Algebra k L] : Z k (J : Set _) L = Z k (J.radical : Set (MvPolynomial I k)) L := by
  ext x
  refine ⟨fun hx f hf => ?_, fun hx f hf => hx f (Ideal.le_radical hf)⟩
  obtain ⟨n, hn⟩ := hf
  have : aeval x f ^ n = 0 := by rw [← map_pow]; exact hx _ hn
  exact IsReduced.eq_zero _ ⟨n, this⟩

/-- 51wmmpHand0-7240 (2:00:40) [prop] `√J` is the preimage of the nilradical of `P_I/J`;
`P_I/√J` is reduced, and is `P_I/J` modulo its nilradical. -/
theorem prop_7240 {R : Type*} [CommRing R] (J : Ideal R) :
    J.radical = (nilradical (R ⧸ J)).comap (Ideal.Quotient.mk J) ∧ IsReduced (R ⧸ J.radical) ∧
      Nonempty (((R ⧸ J) ⧸ nilradical (R ⧸ J)) ≃+* R ⧸ J.radical) := by
  have h1 : J.radical = (nilradical (R ⧸ J)).comap (Ideal.Quotient.mk J) := by
    ext f
    rw [Ideal.mem_comap, mem_nilradical]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn⟩
    · rintro ⟨n, hn⟩
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn
      exact ⟨n, hn⟩
  refine ⟨h1, (Ideal.isRadical_iff_quotient_reduced _).1 (Ideal.radical_isRadical J), ⟨?_⟩⟩
  have h2 : nilradical (R ⧸ J) = J.radical.map (Ideal.Quotient.mk J) := by
    rw [h1, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  exact (Ideal.quotEquivOfEq h2).trans (DoubleQuot.quotQuotEquivQuotOfLE Ideal.le_radical)

/-- 51wmmpHand0-7502 (2:05:02) [prop] `√J` is the set of `f` vanishing on `V_J(k')` for every
field `k'` over `k`. -/
theorem prop_7502 (J : Ideal (MvPolynomial I k)) (f : MvPolynomial I k) :
    f ∈ J.radical ↔
      ∀ (K : Type u) [Field K] [Algebra k K], ∀ x ∈ Z k (J : Set _) K, aeval x f = 0 := by
  constructor
  · intro hf K _ _ x hx
    rw [prop_7174 k J K] at hx
    exact hx f hf
  · intro h
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro p ⟨hJp, hp⟩
    have := hp
    let K := FractionRing (MvPolynomial I k ⧸ p)
    let φ : (MvPolynomial I k ⧸ p) →ₐ[k] K := IsScalarTower.toAlgHom k _ K
    have hx : (fun i => φ (can k p i)) ∈ Z k (J : Set _) K := fun g hg => by
      rw [aeval_comp_algHom k φ, aeval_can, Ideal.Quotient.eq_zero_iff_mem.2 (hJp hg), map_zero]
    have := h K _ hx
    rw [aeval_comp_algHom k φ, aeval_can, ← map_zero φ] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ K this)

/-- 51wmmpHand0-7367 (2:02:47) [prop] Over fields, `V'_J ⊆ V'_{J'}` iff `√J ⊇ √J'`. -/
theorem prop_7367 (J J' : Ideal (MvPolynomial I k)) :
    (∀ (K : Type u) [Field K] [Algebra k K], Z k (J : Set _) K ⊆ Z k (J' : Set (MvPolynomial I k)) K) ↔
      J'.radical ≤ J.radical := by
  constructor
  · intro h
    rw [Ideal.radical_le_radical_iff]
    intro f hf
    exact (prop_7502 k J f).2 fun K _ _ x hx => h K hx f hf
  · intro h K _ _ x hx f hf
    rw [prop_7174 k J K] at hx
    exact hx f (h (Ideal.le_radical hf))

/-- 51wmmpHand0-7367 (2:02:47) [prop] `J ↦ V'_J` is injective on radical ideals. -/
theorem prop_7367_inj (J J' : Ideal (MvPolynomial I k)) (hJ : J.IsRadical) (hJ' : J'.IsRadical)
    (h : ∀ (K : Type u) [Field K] [Algebra k K], Z k (J : Set _) K = Z k (J' : Set (MvPolynomial I k)) K) :
    J = J' := by
  have h1 := (prop_7367 k J J').1 fun K _ _ => (h K).le
  have h2 := (prop_7367 k J' J).1 fun K _ _ => (h K).ge
  rw [hJ.radical, hJ'.radical] at h1 h2
  exact le_antisymm h2 h1

/-- 51wmmpHand0-7566 (2:06:06) [prop] If `f ∈ A` is killed by every homomorphism from `A` to a
field, then `f` is nilpotent. -/
theorem prop_7566 {A : Type u} [CommRing A] (f : A)
    (h : ∀ (K : Type u) [Field K] (φ : A →+* K), φ f = 0) : IsNilpotent f := by
  rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
  intro p hp
  have : p.IsPrime := hp
  have := h (FractionRing (A ⧸ p)) ((algebraMap (A ⧸ p) _).comp (Ideal.Quotient.mk p))
  rw [RingHom.comp_apply, ← map_zero (algebraMap (A ⧸ p) (FractionRing (A ⧸ p)))] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 (IsFractionRing.injective _ _ this)

/-- 51wmmpHand0-7663 (2:07:43) [prop] Every nonzero ring has a maximal ideal (Krull,
`Ideal.exists_maximal`); the intersection of the kernels of the homomorphisms into fields is the
nilradical. -/
theorem prop_7663 {A : Type u} [CommRing A] :
    (Nontrivial A → ∃ m : Ideal A, m.IsMaximal) ∧
      ∀ f : A, IsNilpotent f ↔ ∀ (K : Type u) [Field K] (φ : A →+* K), φ f = 0 :=
  ⟨fun _ => Ideal.exists_maximal A, fun f => ⟨fun hf _ _ φ => (hf.map φ).eq_zero, prop_7566 f⟩⟩

/-- 51wmmpHand0-7725 (2:08:45) [prop] The kernels of the homomorphisms from `A` to fields are
the prime ideals of `A`; the nilradical is the intersection of the prime ideals. -/
theorem prop_7725 {A : Type u} [CommRing A] :
    (∀ (K : Type u) [Field K] (φ : A →+* K), (RingHom.ker φ).IsPrime) ∧
      (∀ p : Ideal A, p.IsPrime → ∃ (K : Type u) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p) ∧
      nilradical A = sInf {p : Ideal A | p.IsPrime} := by
  refine ⟨fun K _ φ => RingHom.ker_isPrime φ, fun p hp => ?_, nilradical_eq_sInf A⟩
  have := hp
  refine ⟨FractionRing (A ⧸ p), inferInstance,
    (algebraMap (A ⧸ p) _).comp (Ideal.Quotient.mk p), ?_⟩
  ext a
  rw [RingHom.mem_ker, RingHom.comp_apply,
    ← map_zero (algebraMap (A ⧸ p) (FractionRing (A ⧸ p))),
    (IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff,
    Ideal.Quotient.eq_zero_iff_mem]

/-- 51wmmpHand0-7993 (2:13:13) [thm] Nullstellensatz: over an algebraically closed field, in
finitely many variables, `√J` is the set of polynomials vanishing on the zeros of `J` in `k^n`
(mathlib: `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`). -/
theorem thm_7993 {K : Type u} [Field K] [IsAlgClosed K] {σ : Type u} [Finite σ]
    (J : Ideal (MvPolynomial σ K)) : vanishingIdeal K (zeroLocus K J) = J.radical :=
  vanishingIdeal_zeroLocus_eq_radical J

/-- Statement (a) of the course over a field `K`. -/
def StmtA (K : Type u) [Field K] : Prop :=
  ∀ (A : Type u) [Field A] [Algebra K A] [Algebra.FiniteType K A], Function.Bijective (algebraMap K A)

/-- Statement (b) of the course over a field `K`. -/
def StmtB (K : Type u) [Field K] : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra K A] [Algebra.FiniteType K A],
    nilradical A = (⊥ : Ideal A).jacobson

/-- The algebraic form of the Nullstellensatz over a field `K`. -/
def NS (K : Type u) [Field K] : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra K A] [Algebra.FiniteType K A] (f : A),
    (∀ u : A →ₐ[K] K, u f = 0) → IsNilpotent f

/-- 51wmmpHand0-8263 (2:17:43) [thm] Statement (a): a finitely generated algebra over an
algebraically closed field `K` which is a field is `K`. -/
theorem thm_8263 (K : Type u) [Field K] [IsAlgClosed K] : StmtA K := by
  intro A _ _ _
  have : Module.Finite K A := finite_of_finite_type_of_isJacobsonRing K A
  have : Algebra.IsIntegral K A := Algebra.IsIntegral.of_finite K A
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- 51wmmpHand0-8327 (2:18:47) [thm] Statement (b): over any field, the nilradical of a
finitely generated algebra is the intersection of its maximal ideals. -/
theorem thm_8327 (K : Type u) [Field K] : StmtB K := by
  intro A _ _ _
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  exact Ideal.radical_eq_jacobson ⊥

/-- Under (a), every maximal ideal of a finitely generated `K`-algebra is the kernel of a
`K`-homomorphism to `K`. -/
theorem exists_algHom_ker_eq {K : Type u} [Field K] (hA : StmtA K) {A : Type u} [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    ∃ u : A →ₐ[K] K, RingHom.ker u = m := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let e : K ≃ₐ[K] A ⧸ m := AlgEquiv.ofBijective (Algebra.ofId K _) (hA (A ⧸ m))
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K m), ?_⟩
  ext a
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

theorem mem_jacobson_bot_iff {A : Type*} [CommRing A] (f : A) :
    f ∈ (⊥ : Ideal A).jacobson ↔ ∀ m : Ideal A, m.IsMaximal → f ∈ m := by
  show f ∈ sInf _ ↔ _
  rw [Ideal.mem_sInf]
  exact ⟨fun h m hm => h ⟨bot_le, hm⟩, fun h m hm => h m hm.2⟩

/-- 51wmmpHand0-8519 (2:21:59) [thm] The Nullstellensatz (algebraic form) is equivalent to the
conjunction of (a) and (b) (over every field `K`). -/
theorem thm_8519 (K : Type u) [Field K] : NS K ↔ StmtA K ∧ StmtB K := by
  constructor
  · intro hNS
    refine ⟨fun A _ _ _ => ?_, fun A _ _ _ => ?_⟩
    · by_cases hu : Nonempty (A →ₐ[K] K)
      · obtain ⟨u⟩ := hu
        refine ⟨(algebraMap K A).injective, fun a => ⟨u a, ?_⟩⟩
        apply u.toRingHom.injective
        change u (algebraMap K A (u a)) = u a
        rw [AlgHom.commutes]; rfl
      · exfalso
        obtain ⟨n, hn⟩ := hNS A (1 : A) fun u => (hu ⟨u⟩).elim
        rw [one_pow] at hn
        exact one_ne_zero hn
    · refine le_antisymm Ideal.radical_le_jacobson fun f hf => ?_
      rw [mem_nilradical]
      refine hNS A f fun u => ?_
      have hm : (RingHom.ker u).IsMaximal :=
        RingHom.ker_isMaximal_of_surjective u fun c => ⟨algebraMap K A c, u.commutes c⟩
      exact (RingHom.mem_ker).1 ((mem_jacobson_bot_iff f).1 hf _ hm)
  · rintro ⟨hA, hB⟩ A _ _ _ f hf
    rw [← mem_nilradical, hB A, mem_jacobson_bot_iff]
    intro m hm
    obtain ⟨u, hu⟩ := exists_algHom_ker_eq hA m
    rw [← hu, RingHom.mem_ker]
    exact hf u

/-- 51wmmpHand0-8519 (2:21:59) [thm] (a) requires `K` to be algebraically closed: `ℂ` is a
finitely generated `ℝ`-algebra and a field, but not `ℝ`. -/
theorem thm_8519_real : ¬ StmtA ℝ := fun h => by
  have : Algebra.FiniteType ℝ ℂ := inferInstance
  obtain ⟨r, hr⟩ := (h ℂ).2 Complex.I
  have := congrArg Complex.im hr
  simp at this

/-- 51wmmpHand0-8200 (2:16:40) [thm] Algebraic form of the Nullstellensatz: over an
algebraically closed field, an element of a finitely generated algebra killed by every
`K`-homomorphism to `K` is nilpotent. -/
theorem thm_8200 (K : Type u) [Field K] [IsAlgClosed K] : NS K :=
  (thm_8519 K).2 ⟨thm_8263 K, thm_8327 K⟩

/-- 51wmmpHand0-8452 (2:20:52) [prop] Over an algebraically closed field, `u ↦ ker u` is a
bijection from `Hom_K(A, K)` onto the maximal ideals of a finitely generated `A`. -/
theorem prop_8452 {K A : Type u} [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] :
    Function.Bijective (fun u : A →ₐ[K] K => (⟨RingHom.ker u, RingHom.ker_isMaximal_of_surjective u
      (fun c => ⟨algebraMap K A c, u.commutes c⟩)⟩ : {m : Ideal A // m.IsMaximal})) := by
  refine ⟨fun u v huv => ?_, fun ⟨m, hm⟩ => ?_⟩
  · have hker : RingHom.ker u = RingHom.ker v := congrArg Subtype.val huv
    ext a
    have h1 : a - algebraMap K A (u a) ∈ RingHom.ker u := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero]; rfl
    rw [hker, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at h1
    exact h1.symm
  · obtain ⟨u, hu⟩ := exists_algHom_ker_eq (thm_8263 K) m
    exact ⟨u, Subtype.ext hu⟩

/-- 51wmmpHand0-8585 (2:23:05) [thm] Statement (a'): over any field, a finitely generated algebra
that is a field is a finite extension (Zariski's lemma; mathlib:
`finite_of_finite_type_of_isJacobsonRing`). -/
theorem thm_8585 {K A : Type u} [Field K] [Field A] [Algebra K A] [Algebra.FiniteType K A] :
    Module.Finite K A :=
  finite_of_finite_type_of_isJacobsonRing K A

/-- 51wmmpHand0-8650 (2:24:10) [prop] An element of a finitely generated algebra over a field
`K` killed by every `K`-homomorphism to a finite extension of `K` is nilpotent. -/
theorem prop_8650 {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (f : A) (h : ∀ (L : Type u) [Field L] [Algebra K L] [Module.Finite K L] (u : A →ₐ[K] L),
      u f = 0) : IsNilpotent f := by
  rw [← mem_nilradical, thm_8327 K A, mem_jacobson_bot_iff]
  intro m hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  have := h (A ⧸ m) (Ideal.Quotient.mkₐ K m)
  rwa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at this

theorem mem_radical_iff_isNilpotent {R : Type*} [CommRing R] (J : Ideal R) (f : R) :
    f ∈ J.radical ↔ IsNilpotent (Ideal.Quotient.mk J f) := by
  rw [(prop_7240 J).1, Ideal.mem_comap, mem_nilradical]

/-- 51wmmpHand0-8717 (2:25:17) [prop] Over a field `K`, in finitely many variables, the
correspondence between closed subspaces and radical ideals holds when one tests only on finite
extensions of `K`. -/
theorem prop_8717 {K : Type u} [Field K] {σ : Type u} [Finite σ] (J J' : Ideal (MvPolynomial σ K)) :
    (∀ (L : Type u) [Field L] [Algebra K L] [Module.Finite K L],
      Z K (J : Set _) L ⊆ Z K (J' : Set (MvPolynomial σ K)) L) ↔ J'.radical ≤ J.radical := by
  constructor
  · intro h
    rw [Ideal.radical_le_radical_iff]
    intro f hf
    rw [mem_radical_iff_isNilpotent]
    refine prop_8650 (K := K) (A := MvPolynomial σ K ⧸ J) _ fun L _ _ _ u => ?_
    have hx : (fun i => u (can K J i)) ∈ Z K (J : Set _) L := fun g hg => by
      rw [aeval_comp_algHom K u, aeval_can, Ideal.Quotient.eq_zero_iff_mem.2 hg, map_zero]
    have := h L hx f hf
    rwa [aeval_comp_algHom K u, aeval_can] at this
  · intro h L _ _ _ x hx f hf
    rw [prop_7174 K J L] at hx
    exact hx f (h (Ideal.le_radical hf))

/-- 51wmmpHand0-8717 (2:25:17) [prop] If `K` is algebraically closed, testing on `K` itself
suffices. -/
theorem prop_8717_algClosed {K : Type u} [Field K] [IsAlgClosed K] {σ : Type u} [Finite σ]
    (J J' : Ideal (MvPolynomial σ K)) :
    Z K (J : Set _) K ⊆ Z K (J' : Set (MvPolynomial σ K)) K ↔ J'.radical ≤ J.radical := by
  constructor
  · intro h
    rw [Ideal.radical_le_radical_iff]
    intro f hf
    rw [mem_radical_iff_isNilpotent]
    refine thm_8200 K (MvPolynomial σ K ⧸ J) _ fun u => ?_
    have hx : (fun i => u (can K J i)) ∈ Z K (J : Set _) K := fun g hg => by
      rw [aeval_comp_algHom K u, aeval_can, Ideal.Quotient.eq_zero_iff_mem.2 hg, map_zero]
    have := h hx f hf
    rwa [aeval_comp_algHom K u, aeval_can] at this
  · intro h x hx f hf
    rw [prop_7174 K J K] at hx
    exact hx f (h (Ideal.le_radical hf))

/-! ### Algebras of functions -/

/-- 51wmmpHand0-9373 (2:36:13) [prop] For `X = V_A`, `Hom(X, E^1) ≃ A`: the morphisms
`V_A → E^1` are the elements of `A` (an element `a` acting by `u ↦ u(a)`). -/
def prop_9373 (A : Type u) [CommRing A] [Algebra k A] :
    (V k A ⟶ forget (CommAlgCat.{u} k)) ≃ A :=
  homEquivOfCorep k (V.corepresentableBy k A)

theorem prop_9373_apply (A : Type u) [CommRing A] [Algebra k A] (a : A) (k' : CommAlgCat.{u} k)
    (u : (V k A).obj k') : ((prop_9373 k A).symm a).app k' u = (show A →ₐ[k] k' from u) a :=
  rfl

/-- 51wmmpHand0-9437 (2:37:17) [prop] `E^1` is an algebra object: addition, multiplication
`E^1 × E^1 → E^1` (here `E^2 → E^1`) and scalars are natural transformations. -/
def addE : E k (ULift.{u} (Fin 2)) ⟶ forget (CommAlgCat.{u} k) where
  app _ := ↾fun x => x ⟨0⟩ + x ⟨1⟩
  naturality _ _ u := ConcreteCategory.hom_ext _ _ fun x =>
    (map_add (show _ →ₐ[k] _ from u.hom) (x ⟨0⟩) (x ⟨1⟩)).symm

/-- Multiplication on `E^1` (51wmmpHand0-9437). -/
def mulE : E k (ULift.{u} (Fin 2)) ⟶ forget (CommAlgCat.{u} k) where
  app _ := ↾fun x => x ⟨0⟩ * x ⟨1⟩
  naturality _ _ u := ConcreteCategory.hom_ext _ _ fun x =>
    (map_mul (show _ →ₐ[k] _ from u.hom) (x ⟨0⟩) (x ⟨1⟩)).symm

/-- Scalars on `E^1` (51wmmpHand0-9437). -/
def smulE (c : k) : forget (CommAlgCat.{u} k) ⟶ forget (CommAlgCat.{u} k) where
  app _ := ↾fun x => c • x
  naturality _ _ u := ConcreteCategory.hom_ext _ _ fun x =>
    (map_smul (show _ →ₐ[k] _ from u.hom) c x).symm

/-- 51wmmpHand0-9504 (2:38:24) [prop] and 51wmmpHand0-9652 (2:40:52) [prop] The ring structure
of `Hom(V_A, E^1)` deduced from that of `E^1` (pointwise operations in each `k'`) is that of
`A`. -/
theorem prop_9504 (A : Type u) [CommRing A] [Algebra k A] (a b : A) (c : k)
    (k' : CommAlgCat.{u} k) (u : (V k A).obj k') :
    ((prop_9373 k A).symm (a + b)).app k' u =
        ((prop_9373 k A).symm a).app k' u + ((prop_9373 k A).symm b).app k' u ∧
      ((prop_9373 k A).symm (a * b)).app k' u =
        ((prop_9373 k A).symm a).app k' u * ((prop_9373 k A).symm b).app k' u ∧
      ((prop_9373 k A).symm (c • a)).app k' u = c • ((prop_9373 k A).symm a).app k' u := by
  exact ⟨map_add (show A →ₐ[k] k' from u) a b, map_mul (show A →ₐ[k] k' from u) a b,
    map_smul (show A →ₐ[k] k' from u) c a⟩

/-- 51wmmpHand0-9780 (2:43:00) [prop] A morphism `E^I → E^1` is given by a unique polynomial of
`P_I`. -/
def prop_9780 : (E k I ⟶ forget (CommAlgCat.{u} k)) ≃ MvPolynomial I k :=
  homEquivOfCorep k (E.corepresentableBy k I)

theorem prop_9780_apply (f : MvPolynomial I k) (k' : CommAlgCat.{u} k) (x : (E k I).obj k') :
    ((prop_9780 k).symm f).app k' x = aeval (show I → k' from x) f :=
  rfl

/-- 51wmmpHand0-9910 (2:45:10) [prop] For `X = V_J`, restricting polynomials to `V_J(k')`
identifies `P_I/J` with the morphisms `V_J → E^1`. -/
def prop_9910 (J : Ideal (MvPolynomial I k)) :
    ((VJ k J).toFunctor ⟶ forget (CommAlgCat.{u} k)) ≃ MvPolynomial I k ⧸ J :=
  homEquivOfCorep k (VJ.corepresentableBy k J)

theorem prop_9910_apply (J : Ideal (MvPolynomial I k)) (f : MvPolynomial I k)
    (k' : CommAlgCat.{u} k) (x : (VJ k J).toFunctor.obj k') :
    ((prop_9910 k J).symm (Ideal.Quotient.mk J f)).app k' x = aeval x.1 f :=
  rfl

/-! ### Products, sums and fibre products -/

/-- 51wmmpHand0-10536 (2:55:36) [prop] The category of affine spaces is opposite to that of
`k`-algebras (`prop_6911`); its projective limits are the inductive limits of `k`-algebras, which
exist. -/
theorem prop_10536 : Limits.HasLimits (CommAlgCat.{u} k)ᵒᵖ := inferInstance

/-- 51wmmpHand0-10603 (2:56:43) [def] Products (mathlib: `CategoryTheory.Limits.Fan`, a limit
cone); the empty product is the final object. -/
example : Limits.HasTerminal (CommAlgCat.{u} k)ᵒᵖ := inferInstance

/-- 51wmmpHand0-10732 (2:58:52) [def] Sums (mathlib: `CategoryTheory.Limits.Cofan`); the products
of affine spaces are the sums of `k`-algebras, which exist. -/
example : Limits.HasCoproducts.{u} (CommAlgCat.{u} k) := inferInstance

/-- 51wmmpHand0-10867 (3:01:07) [prop] The sum of two `k`-algebras is `A' ⊗_k A''`, with
`x' ↦ x' ⊗ 1` and `x'' ↦ 1 ⊗ x''`. -/
def prop_10867 (A B C : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    [CommRing C] [Algebra k C] :
    (TensorProduct k A B →ₐ[k] C) ≃ (A →ₐ[k] C) × (B →ₐ[k] C) where
  toFun φ := (φ.comp Algebra.TensorProduct.includeLeft, φ.comp Algebra.TensorProduct.includeRight)
  invFun p := Algebra.TensorProduct.productMap p.1 p.2
  left_inv φ := Algebra.TensorProduct.ext (by ext; simp)
    (by ext; simp [← Algebra.TensorProduct.one_def])
  right_inv p := by ext <;> simp

/-- 51wmmpHand0-11119 (3:05:19) [prop] Sums of arbitrary families of `k`-algebras exist (the
description as the filtered limit of the finite tensor products is not formalised). -/
example : Limits.HasCoproducts.{u} (CommAlgCat.{u} k) := inferInstance

/-- The forgetful functor of `k`-algebras, through rings under `k`. -/
def forgetIsoUnder : forget (CommAlgCat.{u} k) ≅
    (commAlgCatEquivUnder (CommRingCat.of k)).functor ⋙ Under.forget _ ⋙ forget CommRingCat :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- 51wmmpHand0-11182 (3:06:22) [prop] Filtered inductive limits of `k`-algebras are computed on
the underlying sets. -/
instance prop_11182 : Limits.PreservesFilteredColimits (forget (CommAlgCat.{u} k)) :=
  ⟨fun _ _ _ => Limits.preservesColimitsOfShape_of_natIso (forgetIsoUnder k).symm⟩

/-- `k` is the initial `k`-algebra. -/
def isInitialSelf : Limits.IsInitial (CommAlgCat.of k k) :=
  Limits.IsInitial.ofUniqueHom (fun Y => CommAlgCat.ofHom (Algebra.ofId k Y))
    (fun _ _ => CommAlgCat.hom_ext (Subsingleton.elim _ _))

/-- 51wmmpHand0-11182 (3:06:22) [prop] … unlike sums: the empty sum of `k`-algebras is `k`, not
the empty set, so the forgetful functor does not preserve initial objects. -/
theorem prop_11182_sums :
    ¬ Limits.PreservesColimit (Functor.empty.{0} (CommAlgCat.{u} k)) (forget (CommAlgCat.{u} k)) := by
  intro h
  have hi := Limits.IsInitial.isInitialObj (forget (CommAlgCat.{u} k)) _ (isInitialSelf k)
  exact (hi.to PEmpty.{u + 1} (0 : k)).elim

end May30

end

end Buffalo.AG.Part01
