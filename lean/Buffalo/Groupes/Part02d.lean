import Buffalo.Groupes.Part02c

/-!
# Buffalo, algebraic groups, Part 02 (d): connected components, étale schemes, irreducibility

Entries `3ULFIl_2Wis-119` to `3ULFIl_2Wis-5696` of `docs/buffalo-groupes/index.tex` (27 June and
2 July 1973). Statuses in `docs/buffalo-groupes/lean/Part02.json`.

Affine statements are made for algebras (`Spec A`); étale `k`-algebras are Mathlib's
`Algebra.Etale`, Galois groups `Gal(L/k)` with the Krull topology.
-/

namespace Buffalo.Groupes.Part02

open TensorProduct Polynomial

universe u

/-! ## Openness -/

section Open

open AlgebraicGeometry CategoryTheory

/-- 3ULFIl_2Wis-575 (0:09:35) [prop] A morphism to the spectrum of a field is universally open;
the affine case: for `X = Spec A` and base change `Spec B`, the projection
`Spec (A ⊗_K B) → Spec A` is open (Mathlib `isOpenMap_comap_algebraMap_tensorProduct_of_field`). -/
theorem open_over_field {K A B : Type*} [Field K] [CommRing A] [CommRing B] [Algebra K A]
    [Algebra K B] : IsOpenMap (PrimeSpectrum.comap (algebraMap A (A ⊗[K] B))) :=
  PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field

/-- 3ULFIl_2Wis-638 (0:10:38) [prop] A flat morphism locally of finite presentation is open
(Mathlib `UniversallyOpen.of_flat`). -/
theorem open_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    IsOpenMap f :=
  f.isOpenMap

end Open

/-! ## Reduced schemes -/

section Reduced

/-- 3ULFIl_2Wis-2460 (0:41:00) [prop] (affine) A morphism `Spec A → Spec B` from a reduced
scheme that lands set-theoretically in `V(I)` factors through `Spec (B/I)`. -/
theorem factor_of_reduced {A B : Type*} [CommRing A] [CommRing B] [IsReduced A] (φ : B →+* A)
    (I : Ideal B) (h : ∀ x ∈ I, ∀ P : PrimeSpectrum A, φ x ∈ P.asIdeal) :
    ∃ ψ : B ⧸ I →+* A, ψ.comp (Ideal.Quotient.mk I) = φ := by
  have h0 : ∀ x ∈ I, φ x = 0 := by
    intro x hx
    have : φ x ∈ nilradical A := by
      rw [nilradical_eq_sInf, Submodule.mem_sInf]
      exact fun J hJ ↦ h x hx ⟨J, hJ⟩
    rwa [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact ⟨Ideal.Quotient.lift I φ h0, Ideal.Quotient.lift_comp_mk I φ h0⟩

end Reduced

/-! ## Étale schemes over a field -/

section Etale

variable (k : Type u) [Field k]

/-- 3ULFIl_2Wis-2844 (0:47:24) [def] (quasi-compact case, Mathlib
`Algebra.Etale.iff_exists_algEquiv_prod`) `Spec A` is étale over `k` iff `A` is a finite product of
finite separable extensions of `k`. -/
theorem etale_iff (A : Type u) [CommRing A] [Algebra k A] :
    Algebra.Etale k A ↔
      ∃ (I : Type u) (_ : Finite I) (Ai : I → Type u) (_ : ∀ i, Field (Ai i))
        (_ : ∀ i, Algebra k (Ai i)) (_ : A ≃ₐ[k] Π i, Ai i),
        ∀ i, Module.Finite k (Ai i) ∧ Algebra.IsSeparable k (Ai i) :=
  Algebra.Etale.iff_exists_algEquiv_prod k A

/-- 3ULFIl_2Wis-2844 (0:47:24) [def] The entry's "equivalent to geometrically reduced" is false:
`𝔸¹_k = Spec k[X]` is geometrically reduced but not étale. -/
theorem affineLine_geomReduced_not_etale :
    Algebra.IsGeometricallyReduced k k[X] ∧ ¬ Algebra.Etale k k[X] := by
  refine ⟨(Algebra.isGeometricallyReduced_field_iff k k[X]).mpr ?_, fun h ↦ ?_⟩
  · exact isReduced_of_injective _ (polyEquivTensor k (AlgebraicClosure k)).symm.injective
  · exact Polynomial.not_finite (Algebra.FormallyUnramified.finite_of_free k k[X])

/-- 3ULFIl_2Wis-2911 (0:48:31) [prop] (Mathlib `equivPiOfIsSepClosed`) Over a separably closed
field, an étale algebra is constant: `A ≃ k^{Spec A}`. -/
noncomputable def etale_constant (A : Type u) [CommRing A] [Algebra k A] [Algebra.EssFiniteType k A]
    [Algebra.FormallyEtale k A] [IsSepClosed k] : A ≃ₐ[k] (PrimeSpectrum A → k) :=
  Algebra.FormallyEtale.equivPiOfIsSepClosed k A

/-- 3ULFIl_2Wis-3119 (0:51:59) [prop] Being étale is stable under base change (Mathlib
`Algebra.Etale.baseChange`). -/
example (A K : Type u) [CommRing A] [Algebra k A] [Field K] [Algebra k K] [Algebra.Etale k A] :
    Algebra.Etale K (K ⊗[k] A) := inferInstance

/-- 3ULFIl_2Wis-3449 (0:57:29) [prop] For `X = Spec K`, `K/k` separable, the `k'`-points are
the `k̄`-points, `k̄` the separable closure of `k` in `k'`: every `K → k'` lands in `k̄`. -/
theorem points_in_sepClosure {K L : Type u} [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra.IsSeparable k K] (f : K →ₐ[k] L) (x : K) : f x ∈ separableClosure k L :=
  (map_mem_separableClosure_iff f).mpr (Algebra.IsSeparable.isSeparable k x)

/-- 3ULFIl_2Wis-3514 (0:58:34) [prop] The action of `π = Gal(L/k)` on the points `K → L` of
`Spec K` (`K/k` finite) is continuous: the stabilizer of a point is the fixing subgroup of its
image, an open subgroup (Mathlib `fixingSubgroup_isOpen`; `Gal(L/k)` is profinite,
`InfiniteGalois.continuousMulEquivToLimit`). -/
theorem stabilizer_isOpen {K L : Type u} [Field K] [Field L] [Algebra k K] [Algebra k L]
    [FiniteDimensional k K] (f : K →ₐ[k] L) :
    IsOpen {σ : Gal(L/k) | (σ : L →ₐ[k] L).comp f = f} := by
  have hfin : FiniteDimensional k f.fieldRange :=
    LinearMap.finiteDimensional_range f.toLinearMap
  have : {σ : Gal(L/k) | (σ : L →ₐ[k] L).comp f = f} = (f.fieldRange.fixingSubgroup : Set _) := by
    ext σ
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff,
      AlgHom.mem_fieldRange, forall_exists_index, forall_apply_eq_imp_iff]
    constructor
    · intro h x; exact congrArg (fun g : K →ₐ[k] L ↦ g x) h
    · intro h; ext x; exact h x
  rw [this]
  exact IntermediateField.fixingSubgroup_isOpen _

/-- 3ULFIl_2Wis-3644 (1:00:44) [thm] On connected étale schemes (Mathlib, infinite Galois
theory): intermediate fields of `L/k` correspond to closed subgroups of `Gal(L/k)`, the finite
ones (`Spec K`, `K/k` finite) to the open subgroups. -/
noncomputable def galoisCorrespondence (L : Type u) [Field L] [Algebra k L] [IsGalois k L] :
    IntermediateField k L ≃o (ClosedSubgroup Gal(L/k))ᵒᵈ :=
  InfiniteGalois.IntermediateFieldEquivClosedSubgroup

theorem open_iff_finite (L : Type u) [Field L] [Algebra k L] [IsGalois k L]
    (E : IntermediateField k L) :
    IsOpen E.fixingSubgroup.carrier ↔ FiniteDimensional k E :=
  InfiniteGalois.isOpen_iff_finite E

/-- 3ULFIl_2Wis-3706 (1:01:46) [prop] Finite products of étale `k`-schemes (tensor products of
étale algebras) are étale. -/
example (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Algebra.Etale k A]
    [Algebra.Etale k B] : Algebra.Etale k (A ⊗[k] B) := Algebra.Etale.comp k A (A ⊗[k] B)

/-- 3ULFIl_2Wis-3836 (1:03:56) [prop] Finite sums of étale `k`-schemes (finite products of
étale algebras) are (formally) étale (Mathlib `Algebra.FormallyEtale.pi_iff`). -/
example {I : Type u} [Finite I] (A : I → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra k (A i)]
    [∀ i, Algebra.FormallyEtale k (A i)] : Algebra.FormallyEtale k (Π i, A i) :=
  (Algebra.FormallyEtale.pi_iff A).mpr inferInstance

/-- 3ULFIl_2Wis-4027 (1:07:07) [cex] For `K/k` finite separable of degree `n` and `k''`
separably closed, `Spec (k'' ⊗_k K)` has exactly `n` points. -/
theorem card_points_baseChange (K K'' : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsSeparable k K] [Field K''] [Algebra k K''] [IsSepClosed K''] :
    Nat.card (PrimeSpectrum (K'' ⊗[k] K)) = Module.finrank k K := by
  have : Algebra.FormallyEtale k K := Algebra.FormallyEtale.of_isSeparable k K
  have e := Algebra.FormallyEtale.equivPiOfIsSepClosed K'' (K'' ⊗[k] K)
  have : IsArtinianRing (K'' ⊗[k] K) := isArtinian_of_tower K'' inferInstance
  have : Fintype (PrimeSpectrum (K'' ⊗[k] K)) := Fintype.ofFinite _
  rw [← Module.finrank_baseChange (R := K'') (S := k) (M' := K), e.toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

/-- 3ULFIl_2Wis-4156 (1:09:16) [ex] For `k'/k` purely inseparable of degree `p`,
`k' = k[t]/(t^p - a)`, after extension to a field `k''` in which `a = b^p`, the point carries
the non-zero nilpotent `t - b`. -/
theorem insep_nilpotent {K'' : Type u} [Field K''] (p : ℕ) [hp : Fact p.Prime] [CharP K'' p]
    (b : K'') : (AdjoinRoot.root (X ^ p - C (b ^ p)) - AdjoinRoot.of _ b) ^ p = 0 ∧
      AdjoinRoot.root (X ^ p - C (b ^ p)) - AdjoinRoot.of (X ^ p - C (b ^ p)) b ≠ 0 := by
  have hdeg : (X ^ p - C (b ^ p) : K''[X]).degree ≠ 0 := by
    rw [degree_X_pow_sub_C hp.out.pos]; exact_mod_cast hp.out.ne_zero
  have : CharP (AdjoinRoot (X ^ p - C (b ^ p) : K''[X])) p :=
    charP_of_injective_algebraMap (AdjoinRoot.of.injective_of_degree_ne_zero hdeg) p
  constructor
  · rw [sub_pow_char, ← map_pow, ← AdjoinRoot.mk_X, ← map_pow, ← AdjoinRoot.mk_C, ← map_sub,
      AdjoinRoot.mk_self]
  · rw [← AdjoinRoot.mk_X, ← AdjoinRoot.mk_C, ← map_sub, ne_eq, AdjoinRoot.mk_eq_zero]
    intro hdvd
    have hne : (X - C b : K''[X]) ≠ 0 := X_sub_C_ne_zero b
    have := Polynomial.natDegree_le_of_dvd hdvd hne
    rw [natDegree_X_pow_sub_C, natDegree_X_sub_C] at this
    exact absurd this (by have := hp.out.two_le; omega)

/-- 3ULFIl_2Wis-4291 (1:11:31) [prop] (affine, `I` finite) A morphism `Spec A → ∐_I Spec k`,
i.e. an algebra map `k^I → A`, gives a decomposition `1 = ∑ eᵢ` into complete orthogonal
idempotents (`Spec A = ∐ Spec Aeᵢ`). -/
theorem decomposition_of_map {I : Type*} [Fintype I] [DecidableEq I] (A : Type*) [CommRing A]
    [Algebra k A] (f : (I → k) →ₐ[k] A) :
    CompleteOrthogonalIdempotents fun i ↦ f (Pi.single i 1) :=
  (CompleteOrthogonalIdempotents.single (fun _ : I ↦ k)).map f.toRingHom

end Etale

/-! ## Geometric irreducibility -/

section Irreducible

/-- 3ULFIl_2Wis-5302 (1:28:22) [cex] `ℝ[x, y]/(x² + y²)` is a domain (irreducible, with the
rational point `0`) … -/
theorem real_irreducible : Irreducible (X ^ 2 + C (X ^ 2) : ℝ[X][X]) := by
  have hm : (X ^ 2 + C (X ^ 2) : ℝ[X][X]).Monic := by
    apply Monic.add_of_left (monic_X_pow 2)
    rw [degree_C (pow_ne_zero 2 X_ne_zero), degree_X_pow]; norm_num
  have hdeg : (X ^ 2 + C (X ^ 2) : ℝ[X][X]).natDegree = 2 := by
    rw [natDegree_add_C, natDegree_X_pow]
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun g hg ↦ ?_
  rw [mem_roots hm.ne_zero, IsRoot, eval_add, eval_pow, eval_X, eval_C] at hg
  have := congrArg (eval 1) hg
  simp only [eval_add, eval_pow, eval_zero, eval_X, one_pow] at this
  nlinarith [sq_nonneg (eval 1 g)]

theorem real_quotient_domain : (Ideal.span {X ^ 2 + C (X ^ 2)} : Ideal ℝ[X][X]).IsPrime :=
  (Ideal.span_singleton_prime real_irreducible.ne_zero).mpr real_irreducible.prime

/-- … but over `ℂ` it is not: `x² + y² = (y + ix)(y - ix)`, a zero divisor in the quotient. -/
theorem complex_not_domain :
    (X ^ 2 + C (X ^ 2) : ℂ[X][X]) = (X + C (Complex.I • X)) * (X - C (Complex.I • X)) ∧
      ¬ (X ^ 2 + C (X ^ 2) : ℂ[X][X]) ∣ (X + C (Complex.I • X)) := by
  constructor
  · have hc : (C (Complex.I • (X : ℂ[X])) : ℂ[X][X]) ^ 2 = - C ((X : ℂ[X]) ^ 2) := by
      rw [← C_pow, _root_.smul_pow, Complex.I_sq, neg_one_smul, C_neg]
    linear_combination hc
  · intro h
    have hne : (X + C (Complex.I • X) : ℂ[X][X]) ≠ 0 := X_add_C_ne_zero _
    have := natDegree_le_of_dvd h hne
    rw [natDegree_X_add_C] at this
    have h2 : (X ^ 2 + C (X ^ 2) : ℂ[X][X]).natDegree = 2 := by
      rw [natDegree_add_C, natDegree_X_pow]
    omega

/-- 3ULFIl_2Wis-5696 (1:34:56) [prop] The entry's "only one irreducible component of `X_{k'}`
passes over the point" is too strong: for `X = Spec ℂ` over `ℝ` (regular, so geometrically normal)
`X_ℂ = Spec (ℂ ⊗_ℝ ℂ)` has two points, i.e. two irreducible components over the one point of `X`. -/
theorem two_components : Nat.card (PrimeSpectrum (ℂ ⊗[ℝ] ℂ)) = 2 := by
  rw [card_points_baseChange ℝ ℂ ℂ, Complex.finrank_real_complex]

/-- … what holds: at a normal (local domain) point, only one component passes through each point
of `X_{k'}` (a domain has a unique minimal prime). -/
theorem unique_minimal_prime (R : Type*) [CommRing R] [IsDomain R] : minimalPrimes R = {⊥} :=
  IsDomain.minimalPrimes_eq_singleton_bot R

end Irreducible

end Buffalo.Groupes.Part02
