import Buffalo.AG.Part02a

/-!
# Buffalo, algebraic geometry, part 02 (b): 6 June 1973

The entries of `docs/buffalo-ag/index.tex` for the session of 6 June 1973 (video `51wmmpHand0`,
6:38:51–8:10:17): the Zariski topology, irreducible closed sets and generic points, irreducible
components, closed points, noetherian spaces and rings, points with values in `k` and closed
points of algebras of finite type, and very dense subsets (Jacobson spaces). Notation as in
`Buffalo.AG.Part02a`.
-/

open CategoryTheory Limits TopologicalSpace PrimeSpectrum

universe u

namespace Buffalo.AG.Part02

open Buffalo.AG.Part01

noncomputable section

section June6

variable (k : Type u) [CommRing k]

/-! ### The spectral topology -/

/-- 51wmmpHand0-24256 (6:44:16) [def] The `V(S)` are the closed sets of the spectral (Zariski)
topology on `Spec A` (mathlib: `PrimeSpectrum.zariskiTopology`), and `V(J) = V(J')` iff
`√J = √J'`. -/
theorem def_24256 {A : Type*} [CommRing A] (J J' : Ideal A) :
    (∀ S : Set A, IsClosed (zeroLocus S)) ∧
      (zeroLocus (J : Set A) = zeroLocus J' ↔ J.radical = J'.radical) := by
  refine ⟨isClosed_zeroLocus, ?_⟩
  constructor
  · intro h
    rw [← vanishingIdeal_zeroLocus_eq_radical, h, vanishingIdeal_zeroLocus_eq_radical]
  · intro h
    rw [← zeroLocus_radical, h, zeroLocus_radical]

/-- 51wmmpHand0-24326 (6:45:26) [prop] The nilradical is the intersection of the prime ideals
(mathlib: `nilradical_eq_sInf`). -/
theorem prop_24326 (A : Type*) [CommRing A] : nilradical A = sInf {J : Ideal A | J.IsPrime} :=
  nilradical_eq_sInf A

/-- 51wmmpHand0-24456 (6:47:36) [prop] The points with values in a field `K'` of class
`x ∈ Spec A` correspond to the homomorphisms `κ(x) → K'` (`prop_21989`, for `K = ℤ`). -/
theorem prop_24456 {A : Type*} [CommRing A] (x : PrimeSpectrum A) (K' : Type*) [Field K'] :
    Nonempty ({u : A →+* K' // RingHom.ker u = x.asIdeal} ≃
      (FractionRing (A ⧸ x.asIdeal) →+* K')) :=
  (prop_21989 x.asIdeal K').2

/-- 51wmmpHand0-24518 (6:48:38) [prop] A nonempty space is irreducible iff two nonempty open sets
always meet, iff every nonempty open set is dense. -/
theorem prop_24518 (X : Type*) [TopologicalSpace X] [Nonempty X] :
    List.TFAE [IrreducibleSpace X,
      ∀ U V : Set X, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty → (U ∩ V).Nonempty,
      ∀ U : Set X, IsOpen U → U.Nonempty → Dense U] := by
  tfae_have 1 → 2 := fun _ U V hU hV hU' hV' => nonempty_preirreducible_inter hU hV hU' hV'
  tfae_have 2 → 1 := fun h =>
    { toPreirreducibleSpace := PreirreducibleSpace.of_forall_nonempty_inter fun U V => h U V,
      toNonempty := inferInstance }
  tfae_have 1 → 3 := fun _ U hU hU' => hU.dense hU'
  tfae_have 3 → 1 := fun h =>
    { toPreirreducibleSpace := (preirreducibleSpace_iff_open_dense X).2 fun U => h U,
      toNonempty := inferInstance }
  tfae_finish

/-- 51wmmpHand0-24714 (6:51:54) [prop] For every ideal `J`, the closed set `V(J)` with the induced
topology is homeomorphic to `Spec(A/J)`. -/
theorem prop_24714 {A : Type*} [CommRing A] (J : Ideal A) :
    Nonempty (PrimeSpectrum (A ⧸ J) ≃ₜ zeroLocus (J : Set A)) := by
  have hs : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have he := isClosedEmbedding_comap_of_surjective _ _ hs
  have hr : Set.range (comap (Ideal.Quotient.mk J)) = zeroLocus (J : Set A) := by
    rw [range_comap_of_surjective _ _ hs, Ideal.mk_ker]
  exact ⟨he.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)⟩

/-- 51wmmpHand0-25035 (6:57:15) [prop] `V(J)` is irreducible iff `√J` is prime (mathlib:
`PrimeSpectrum.isIrreducible_zeroLocus_iff`); `P ↦ V(P)` is a bijection from `Spec A` onto the
irreducible closed sets (mathlib: `PrimeSpectrum.pointsEquivIrreducibleCloseds`). -/
theorem prop_25035 {A : Type*} [CommRing A] (J : Ideal A) :
    (IsIrreducible (zeroLocus (J : Set A)) ↔ J.radical.IsPrime) ∧
      ∀ x : PrimeSpectrum A,
        ((PrimeSpectrum.pointsEquivIrreducibleCloseds A x).ofDual : Set (PrimeSpectrum A)) =
          zeroLocus (x.asIdeal : Set A) := by
  refine ⟨isIrreducible_zeroLocus_iff J, fun x => ?_⟩
  change closure {x} = _
  exact closure_singleton x

/-- 51wmmpHand0-25167 (6:59:27) [prop] This bijection is `x ↦ closure {x}`: `Spec A` is sober,
every irreducible closed set having a unique generic point (mathlib: `QuasiSober`, `T0Space`,
`irreducibleSetEquivPoints`). -/
theorem prop_25167 {A : Type*} [CommRing A] :
    QuasiSober (PrimeSpectrum A) ∧ T0Space (PrimeSpectrum A) ∧
      ∀ Z : Set (PrimeSpectrum A), IsIrreducible Z → IsClosed Z → ∃! x, closure {x} = Z :=
  ⟨inferInstance, inferInstance, prop_23357.2⟩

/-- 51wmmpHand0-25297 (7:01:37) [ex] The spectrum of an integral domain `A` is Hausdorff iff `A`
is a field; those of `ℤ`, of `k[T]` and of a discrete valuation ring are not Hausdorff. -/
theorem ex_25297 (A : Type*) [CommRing A] [IsDomain A] :
    T2Space (PrimeSpectrum A) ↔ IsField A := by
  constructor
  · intro _
    rw [Ring.isField_iff_maximal_bot]
    obtain ⟨M, hM⟩ := Ideal.exists_maximal A
    have h := (IrreducibleSpace.isIrreducible_univ (PrimeSpectrum A)).isPreirreducible.subsingleton
    have : (⟨M, hM.isPrime⟩ : PrimeSpectrum A) = ⟨⊥, Ideal.isPrime_bot⟩ := h trivial trivial
    rw [show (⊥ : Ideal A) = M from congrArg PrimeSpectrum.asIdeal this.symm]
    exact hM
  · intro hA
    let _ := hA.toField
    have : Subsingleton (PrimeSpectrum A) := ⟨fun x y => PrimeSpectrum.ext (by
      rw [@Ideal.eq_bot_of_prime _ _ x.asIdeal x.isPrime,
        @Ideal.eq_bot_of_prime _ _ y.asIdeal y.isPrime])⟩
    exact ⟨fun x y h => absurd (Subsingleton.elim x y) h⟩

/-- 51wmmpHand0-25297 (7:01:37) [ex] `Spec ℤ`, `Spec k[T]` and the spectrum of a discrete
valuation ring are not Hausdorff. -/
theorem ex_25297_examples (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsDomain k] :
    ¬ T2Space (PrimeSpectrum ℤ) ∧ ¬ T2Space (PrimeSpectrum (Polynomial k)) ∧
      ¬ T2Space (PrimeSpectrum R) := by
  rw [ex_25297, ex_25297, ex_25297]
  exact ⟨Int.not_isField, Polynomial.not_isField k, IsDiscreteValuationRing.not_isField R⟩

/-! ### Irreducible components -/

/-- 51wmmpHand0-25433 (7:03:53) [def] An irreducible component is an irreducible closed set
maximal among irreducible closed sets (mathlib's `irreducibleComponents`, defined as the maximal
irreducible sets, which are closed: `irreducibleComponents_eq_maximals_closed`). -/
theorem def_25433 (X : Type*) [TopologicalSpace X] :
    irreducibleComponents X = {s | Maximal (fun t => IsClosed t ∧ IsIrreducible t) s} :=
  irreducibleComponents_eq_maximals_closed X

/-- 51wmmpHand0-25498 (7:04:58) [prop] Every irreducible subset lies in an irreducible component
(Zorn), and the space is the union of its components (mathlib:
`exists_mem_irreducibleComponents_subset_of_isIrreducible`, `sUnion_irreducibleComponents`). -/
theorem prop_25498 {X : Type*} [TopologicalSpace X] (s : Set X) (hs : IsIrreducible s) :
    (∃ Z ∈ irreducibleComponents X, s ⊆ Z) ∧ ⋃₀ irreducibleComponents X = Set.univ :=
  ⟨exists_mem_irreducibleComponents_subset_of_isIrreducible s hs, sUnion_irreducibleComponents⟩

/-- 51wmmpHand0-25626 (7:07:06) [prop] A filtered (directed) union of irreducible subsets is
irreducible. -/
theorem prop_25626 {X : Type*} [TopologicalSpace X] (S : Set (Set X)) (hne : S.Nonempty)
    (hd : DirectedOn (· ⊆ ·) S) (h : ∀ s ∈ S, IsIrreducible s) : IsIrreducible (⋃₀ S) := by
  obtain ⟨s₀, hs₀⟩ := hne
  refine ⟨(h s₀ hs₀).nonempty.mono (Set.subset_sUnion_of_mem hs₀), ?_⟩
  rintro u v hu hv ⟨x, hxS, hxu⟩ ⟨y, hyS, hyv⟩
  obtain ⟨s, hs, hxs⟩ := Set.mem_sUnion.1 hxS
  obtain ⟨t, ht, hyt⟩ := Set.mem_sUnion.1 hyS
  obtain ⟨r, hr, hsr, htr⟩ := hd s hs t ht
  obtain ⟨z, hzr, hz⟩ := (h r hr).2 u v hu hv ⟨x, hsr hxs, hxu⟩ ⟨y, htr hyt, hyv⟩
  exact ⟨z, Set.mem_sUnion_of_mem hzr hr, hz⟩

/-- 51wmmpHand0-25626 (7:07:06) [prop] In a Hausdorff space the irreducible components are the
points. -/
theorem prop_25626_t2 (X : Type*) [TopologicalSpace X] [T2Space X] :
    irreducibleComponents X = Set.range fun x : X => ({x} : Set X) := by
  ext s
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := hs.1.nonempty
    exact ⟨x, (hs.1.isPreirreducible.subsingleton.eq_singleton_of_mem hx).symm⟩
  · rintro ⟨x, rfl⟩
    have hc := irreducibleComponent_mem_irreducibleComponents x
    have : irreducibleComponent x = {x} :=
      isIrreducible_irreducibleComponent.isPreirreducible.subsingleton.eq_singleton_of_mem
        mem_irreducibleComponent
    rwa [this] at hc

/-- 51wmmpHand0-25689 (7:08:09) [prop] The irreducible components of `Spec A` correspond to the
minimal primes of `A` (mathlib: `PrimeSpectrum.vanishingIdeal_irreducibleComponents`). -/
theorem prop_25689 (A : Type*) [CommRing A] :
    vanishingIdeal '' irreducibleComponents (PrimeSpectrum A) = minimalPrimes A :=
  vanishingIdeal_irreducibleComponents A

/-- 51wmmpHand0-25949 (7:12:29) [prop] For `A` of finite type over `ℂ`, the points of `X(ℂ)`
correspond to the maximal ideals of `A` (the Nullstellensatz, `Buffalo.AG.Part01.prop_8452`),
i.e. to the closed points of `Spec A` (`PrimeSpectrum.isClosed_singleton_iff_isMaximal`). -/
theorem prop_25949 (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] :
    Function.Bijective (fun u : A →ₐ[ℂ] ℂ => (⟨RingHom.ker u, RingHom.ker_isMaximal_of_surjective u
      (fun c => ⟨algebraMap ℂ A c, u.commutes c⟩)⟩ : {m : Ideal A // m.IsMaximal})) ∧
      ∀ x : PrimeSpectrum A, IsClosed ({x} : Set (PrimeSpectrum A)) ↔ x.asIdeal.IsMaximal :=
  ⟨prop_8452, isClosed_singleton_iff_isMaximal⟩

/-- 51wmmpHand0-26144 (7:15:44) [prop] A space is irreducible iff it has exactly one irreducible
component; the empty space has none. -/
theorem prop_26144 (X : Type*) [TopologicalSpace X] :
    (IrreducibleSpace X ↔ ∃ Z, irreducibleComponents X = {Z}) ∧
      (IsEmpty X → irreducibleComponents X = ∅) := by
  refine ⟨⟨fun _ => ⟨_, irreducibleComponents_eq_singleton⟩, fun ⟨Z, hZ⟩ => ?_⟩, fun _ => ?_⟩
  · have hu := sUnion_irreducibleComponents (X := X)
    rw [hZ, Set.sUnion_singleton] at hu
    have hZm : Z ∈ irreducibleComponents X := by rw [hZ]; rfl
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hu]
    exact hZm.1
  · ext s
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hs
    obtain ⟨x, -⟩ := hs.1.nonempty
    exact isEmptyElim x

/-- 51wmmpHand0-26208 (7:16:48) [prop] In a sober space, the irreducible components are the
closures of the maximal points for specialization (the generic points of the components). -/
theorem prop_26208 {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X] :
    (∀ x : X, closure {x} ∈ irreducibleComponents X ↔ ∀ y, y ⤳ x → y = x) ∧
      ∀ Z ∈ irreducibleComponents X, ∃ x, closure {x} = Z := by
  refine ⟨fun x => ⟨fun h y hyx => ?_, fun h => ⟨isIrreducible_singleton.closure, ?_⟩⟩,
    fun Z hZ => ?_⟩
  · have hsub : closure {x} ⊆ closure {y} := specializes_iff_closure_subset.1 hyx
    have := h.2 isIrreducible_singleton.closure hsub
    exact (hyx.antisymm (specializes_iff_closure_subset.2 this)).eq
  · intro T hT hxT
    have hTc := hT.closure
    obtain ⟨y, hy⟩ := QuasiSober.sober hTc isClosed_closure
    have hyx : y ⤳ x := by
      rw [specializes_iff_closure_subset, hy.def]
      exact hxT.trans subset_closure
    rw [h y hyx] at hy
    rw [hy.def]
    exact subset_closure
  · obtain ⟨x, hx⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
    exact ⟨x, hx.def⟩

/-- 51wmmpHand0-26376 (7:19:36) [prop] In a quasi-compact space, every irreducible closed set
contains a minimal irreducible closed set (Zorn). -/
theorem prop_26376 {X : Type*} [TopologicalSpace X] [CompactSpace X] (Z : Set X)
    (hZ : IsIrreducible Z) (hZc : IsClosed Z) :
    ∃ M ⊆ Z, Minimal (fun s => IsIrreducible s ∧ IsClosed s) M := by
  obtain ⟨V, hVZ, hVne, hVc, hV⟩ := hZc.exists_minimal_nonempty_closed_subset hZ.nonempty
  refine ⟨V, hVZ, ⟨⟨hVne, ?_⟩, hVc⟩, fun T hT hTV => (hV T hTV hT.1.nonempty hT.2).ge⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro z₁ z₂ h₁ h₂ h
  by_cases hn : (V ∩ z₁).Nonempty
  · left
    rw [← hV (V ∩ z₁) Set.inter_subset_left hn (hVc.inter h₁)]
    exact Set.inter_subset_right
  · right
    intro x hx
    rcases h hx with h' | h'
    · exact absurd ⟨x, hx, h'⟩ hn
    · exact h'

/-- 51wmmpHand0-26508 (7:21:48) [prop] A nonempty subset equal to the closure of each of its
points is a minimal irreducible closed set, and conversely. -/
theorem prop_26508 {X : Type*} [TopologicalSpace X] (S : Set X) :
    (S.Nonempty ∧ ∀ x ∈ S, closure {x} = S) ↔ Minimal (fun s => IsIrreducible s ∧ IsClosed s) S := by
  constructor
  · rintro ⟨⟨x, hx⟩, h⟩
    refine ⟨⟨h x hx ▸ isIrreducible_singleton.closure, h x hx ▸ isClosed_closure⟩,
      fun T hT hTS => ?_⟩
    obtain ⟨y, hy⟩ := hT.1.nonempty
    rw [← h y (hTS hy)]
    exact closure_minimal (Set.singleton_subset_iff.2 hy) hT.2
  · intro h
    refine ⟨h.1.1.nonempty, fun x hx => ?_⟩
    have hsub : closure {x} ⊆ S := closure_minimal (Set.singleton_subset_iff.2 hx) h.1.2
    exact le_antisymm hsub (h.2 ⟨isIrreducible_singleton.closure, isClosed_closure⟩ hsub)

/-- 51wmmpHand0-26698 (7:24:58) [prop] In a sober space (indeed in any `T₀` space) the minimal
irreducible closed sets are the closed points; if the space is moreover quasi-compact, every
nonempty closed set contains a closed point (mathlib: `IsClosed.exists_closed_singleton`). -/
theorem prop_26698 {X : Type*} [TopologicalSpace X] [T0Space X] :
    ∀ S : Set X, Minimal (fun s => IsIrreducible s ∧ IsClosed s) S ↔
      ∃ x, IsClosed ({x} : Set X) ∧ S = {x} := by
  refine fun S => ⟨fun h => ?_, ?_⟩
  · obtain ⟨⟨x, hx⟩, hcl⟩ := (prop_26508 S).2 h
    have hS : S = {x} := Set.eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy =>
      (inseparable_iff_closure_eq.2 ((hcl y hy).trans (hcl x hx).symm)).eq⟩
    exact ⟨x, hS ▸ h.1.2, hS⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨isIrreducible_singleton, hx⟩, fun T hT hTS => ?_⟩
    obtain ⟨y, hy⟩ := hT.1.nonempty
    intro z hz
    rw [Set.mem_singleton_iff.1 hz, ← Set.mem_singleton_iff.1 (hTS hy)]
    exact hy

/-- 51wmmpHand0-26698 (7:24:58) [prop] In a quasi-compact `T₀` space every nonempty closed set
contains a closed point (mathlib: `IsClosed.exists_closed_singleton`). -/
theorem prop_26698_compact {X : Type*} [TopologicalSpace X] [T0Space X] [CompactSpace X]
    (S : Set X) (hS : IsClosed S) (hne : S.Nonempty) : ∃ x ∈ S, IsClosed ({x} : Set X) :=
  hS.exists_closed_singleton hne

/-- 51wmmpHand0-26762 (7:26:02) [prop] The closed points of `Spec A` are the maximal ideals, and
for `A ≠ 0` a maximal ideal exists (Krull) (mathlib:
`PrimeSpectrum.isClosed_singleton_iff_isMaximal`, `Ideal.exists_maximal`). -/
theorem prop_26762 (A : Type*) [CommRing A] :
    (∀ x : PrimeSpectrum A, IsClosed ({x} : Set (PrimeSpectrum A)) ↔ x.asIdeal.IsMaximal) ∧
      (Nontrivial A → ∃ M : Ideal A, M.IsMaximal) :=
  ⟨isClosed_singleton_iff_isMaximal, fun _ => Ideal.exists_maximal A⟩

/-! ### Noetherian spaces -/

/-- 51wmmpHand0-26826 (7:27:06) [def] A space is noetherian (mathlib's `NoetherianSpace`) iff every
increasing sequence of open sets is stationary, iff every decreasing sequence of closed sets is
(`WellFoundedLT (Closeds X)`). -/
theorem def_26826 (X : Type*) [TopologicalSpace X] :
    (NoetherianSpace X ↔ ∀ f : ℕ →o Opens X, ∃ n, ∀ m, n ≤ m → f n = f m) ∧
      (NoetherianSpace X ↔ WellFoundedLT (Closeds X)) := by
  refine ⟨?_, (noetherianSpace_TFAE X).out 1 2⟩
  rw [← wellFoundedGT_iff_monotone_chain_condition]

/-- 51wmmpHand0-26888 (7:28:08) [prop] A space is noetherian iff all its open sets are
quasi-compact (mathlib: `noetherianSpace_TFAE`). -/
theorem prop_26888 (X : Type*) [TopologicalSpace X] :
    NoetherianSpace X ↔ ∀ U : Opens X, IsCompact (U : Set X) :=
  (noetherianSpace_TFAE X).out 1 4

/-- 51wmmpHand0-27083 (7:31:23) [prop] In a noetherian space every subset is quasi-compact and
noetherian (mathlib: `NoetherianSpace.isCompact`, `NoetherianSpace.set`). -/
theorem prop_27083 {X : Type*} [TopologicalSpace X] [NoetherianSpace X] (s : Set X) :
    IsCompact s ∧ NoetherianSpace s :=
  ⟨NoetherianSpace.isCompact s, inferInstance⟩

/-- 51wmmpHand0-27151 (7:32:31) [prop] A noetherian Hausdorff space is finite and discrete. -/
theorem prop_27151 (X : Type*) [TopologicalSpace X] [NoetherianSpace X] [T2Space X] :
    Finite X ∧ DiscreteTopology X := by
  have := NoetherianSpace.discrete (α := X)
  exact ⟨finite_of_compact_of_discrete, this⟩

/-- 51wmmpHand0-27151 (7:32:31) [prop] The spectrum of a noetherian ring is a noetherian space
(mathlib instance). -/
theorem prop_27151_spec (A : Type*) [CommRing A] [IsNoetherianRing A] :
    NoetherianSpace (PrimeSpectrum A) :=
  inferInstance

/-- 51wmmpHand0-27214 (7:33:34) [prop] Fields and principal rings are noetherian; if `A` is
noetherian so is `A[T]` (Hilbert); a ring is noetherian iff its ideals are finitely generated
(mathlib instances and `isNoetherianRing_iff_ideal_fg`). -/
theorem prop_27214 (K R A : Type*) [Field K] [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing A] [IsNoetherianRing A] :
    IsNoetherianRing K ∧ IsNoetherianRing R ∧ IsNoetherianRing (Polynomial A) ∧
      (IsNoetherianRing A ↔ ∀ J : Ideal A, J.FG) :=
  ⟨inferInstance, inferInstance, inferInstance, isNoetherianRing_iff_ideal_fg A⟩

/-- 51wmmpHand0-27282 (7:34:42) [prop] A noetherian space has finitely many irreducible
components; a noetherian ring has finitely many minimal primes (mathlib:
`NoetherianSpace.finite_irreducibleComponents`, `minimalPrimes.finite_of_isNoetherianRing`). -/
theorem prop_27282 (X A : Type*) [TopologicalSpace X] [NoetherianSpace X] [CommRing A]
    [IsNoetherianRing A] : (irreducibleComponents X).Finite ∧ (minimalPrimes A).Finite :=
  ⟨NoetherianSpace.finite_irreducibleComponents, minimalPrimes.finite_of_isNoetherianRing A⟩

/-- 51wmmpHand0-27535 (7:38:55) [prop] In a noetherian space every nonempty family of closed sets
has a minimal element (noetherian induction). -/
theorem prop_27535 {X : Type*} [TopologicalSpace X] [NoetherianSpace X] (S : Set (Set X))
    (hS : ∀ s ∈ S, IsClosed s) (hne : S.Nonempty) : ∃ m ∈ S, ∀ s ∈ S, ¬ s ⊂ m := by
  obtain ⟨s₀, hs₀⟩ := hne
  have wf : WellFounded ((· < ·) : Closeds X → Closeds X → Prop) := wellFounded_lt
  obtain ⟨m, hm, hmin⟩ := wf.has_min {c : Closeds X | (c : Set X) ∈ S} ⟨⟨s₀, hS s₀ hs₀⟩, hs₀⟩
  refine ⟨m, hm, fun s hs hsm => hmin ⟨s, hS s hs⟩ hs ?_⟩
  exact hsm

/-- The ideal of `K ⊕ V` (`V = K^ℕ`, `V² = 0`) of the `(0, v)` with `v_m = 0` for `m ≥ n`. -/
def chainIdeal (K : Type*) [Field K] (n : ℕ) : Ideal (TrivSqZeroExt K (ℕ → K)) where
  carrier := {x | x.fst = 0 ∧ ∀ m, n ≤ m → x.snd m = 0}
  zero_mem' := ⟨rfl, fun _ _ => rfl⟩
  add_mem' {x y} hx hy := ⟨by simp [hx.1, hy.1], fun m hm => by simp [hx.2 m hm, hy.2 m hm]⟩
  smul_mem' c x hx := ⟨by simp [hx.1], fun m hm => by
    simp [TrivSqZeroExt.snd_mul, hx.1, hx.2 m hm]⟩

/-- 51wmmpHand0-27747 (7:42:27) [cex] A non-noetherian ring can have a noetherian spectrum:
`K ⊕ V` with `V = K^ℕ` infinite-dimensional and `V² = 0` is not noetherian, and its spectrum is a
single point. -/
theorem cex_27747 (K : Type*) [Field K] :
    ¬ IsNoetherianRing (TrivSqZeroExt K (ℕ → K)) ∧
      (Nonempty (PrimeSpectrum (TrivSqZeroExt K (ℕ → K))) ∧
        Subsingleton (PrimeSpectrum (TrivSqZeroExt K (ℕ → K)))) ∧
      NoetherianSpace (PrimeSpectrum (TrivSqZeroExt K (ℕ → K))) := by
  let R := TrivSqZeroExt K (ℕ → K)
  let fst : R →ₐ[K] K := TrivSqZeroExt.fstHom K K (ℕ → K)
  have hfs : Function.Surjective fst := fun c => ⟨TrivSqZeroExt.inl c, rfl⟩
  have hmax : (RingHom.ker fst).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hfs
  have hall : ∀ P : Ideal R, P.IsPrime → P = RingHom.ker fst := fun P hP => by
    refine (hmax.eq_of_le hP.ne_top fun x hx => ?_).symm
    have hx0 : x.fst = 0 := hx
    have : x * x = 0 := by
      ext n
      · rw [TrivSqZeroExt.fst_mul, hx0, zero_mul]; rfl
      · rw [TrivSqZeroExt.snd_mul, hx0, zero_smul, MulOpposite.op_zero, zero_smul, add_zero]; rfl
    exact hP.mem_of_pow_mem 2 (by rw [pow_two, this]; exact P.zero_mem)
  have hsub : Subsingleton (PrimeSpectrum R) := ⟨fun x y => PrimeSpectrum.ext
    ((hall _ x.isPrime).trans (hall _ y.isPrime).symm)⟩
  refine ⟨fun hN => ?_, ⟨⟨⟨_, hmax.isPrime⟩⟩, hsub⟩, inferInstance⟩
  let f : ℕ →o Ideal R := ⟨chainIdeal K, fun n n' h x hx => ⟨hx.1, fun m hm => hx.2 m (h.trans hm)⟩⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.2 hN f
  have hmem : (TrivSqZeroExt.inr (Pi.single n 1) : R) ∈ f (n + 1) :=
    ⟨rfl, fun m hm => by simp [Pi.single_eq_of_ne (show m ≠ n by omega)]⟩
  rw [← hn (n + 1) (Nat.le_succ n)] at hmem
  have := hmem.2 n le_rfl
  simp at this

/-- 51wmmpHand0-27809 (7:43:29) [prop] `Spec A` is noetherian iff the radical ideals of `A`
satisfy the ascending chain condition. -/
theorem prop_27809 (A : Type*) [CommRing A] :
    NoetherianSpace (PrimeSpectrum A) ↔ WellFoundedGT {J : Ideal A // J.IsRadical} := by
  let e : (Closeds (PrimeSpectrum A))ᵒᵈ ≃o {J : Ideal A // J.IsRadical} :=
    { toFun := fun Z => ⟨vanishingIdeal ((OrderDual.ofDual Z : Closeds (PrimeSpectrum A)) :
          Set (PrimeSpectrum A)), isRadical_vanishingIdeal _⟩
      invFun := fun J => OrderDual.toDual ⟨zeroLocus (J.1 : Set A), isClosed_zeroLocus _⟩
      left_inv := fun Z => by
        apply OrderDual.ofDual.injective
        apply Closeds.ext
        change zeroLocus (vanishingIdeal ((OrderDual.ofDual Z : Closeds (PrimeSpectrum A)) :
          Set (PrimeSpectrum A)) : Set A) = ((OrderDual.ofDual Z : Closeds (PrimeSpectrum A)) :
            Set (PrimeSpectrum A))
        rw [zeroLocus_vanishingIdeal_eq_closure, (OrderDual.ofDual Z).isClosed.closure_eq]
      right_inv := fun J => Subtype.ext (by
        change vanishingIdeal (zeroLocus _) = _
        rw [vanishingIdeal_zeroLocus_eq_radical, J.2.radical])
      map_rel_iff' := fun {Z Z'} => by
        change vanishingIdeal _ ≤ vanishingIdeal _ ↔ OrderDual.ofDual Z' ≤ OrderDual.ofDual Z
        rw [← vanishingIdeal_anti_mono_iff (OrderDual.ofDual Z).isClosed]
        rfl }
  have h1 : NoetherianSpace (PrimeSpectrum A) ↔ WellFoundedLT (Closeds (PrimeSpectrum A)) :=
    (noetherianSpace_TFAE (PrimeSpectrum A)).out 1 2
  rw [h1, ← wellFoundedGT_dual_iff (Closeds (PrimeSpectrum A))]
  constructor
  · intro h
    exact e.symm.toOrderEmbedding.wellFoundedGT
  · intro h
    exact e.toOrderEmbedding.wellFoundedGT

/-- 51wmmpHand0-28019 (7:46:59) [prop] The `k`-points of `Spec A` (for a field `k`) correspond to
the maximal ideals `M` with residue field `k` (`k → A/M` bijective), by `u ↦ ker u`; if `k` is
algebraically closed and `A` finitely generated, these are all the maximal ideals
(`Buffalo.AG.Part01.prop_8452`). -/
theorem prop_28019 {K A : Type u} [Field K] [CommRing A] [Algebra K A] :
    Function.Injective (fun u : A →ₐ[K] K => RingHom.ker u) ∧
      Set.range (fun u : A →ₐ[K] K => RingHom.ker u) =
        {M | M.IsMaximal ∧ Function.Bijective (algebraMap K (A ⧸ M))} := by
  refine ⟨fun u v huv => ?_, ?_⟩
  · ext a
    have h1 : a - algebraMap K A (u a) ∈ RingHom.ker u := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero]; rfl
    simp only at huv
    rw [huv, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at h1
    exact h1.symm
  · ext M
    constructor
    · rintro ⟨u, rfl⟩
      have hM := RingHom.ker_isMaximal_of_surjective u fun c => ⟨algebraMap K A c, u.commutes c⟩
      refine ⟨hM, (algebraMap K (A ⧸ RingHom.ker u)).injective, fun x => ?_⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨u a, ?_⟩
      rw [IsScalarTower.algebraMap_apply K A (A ⧸ RingHom.ker u), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero]
      rfl
    · rintro ⟨hM, hb⟩
      let e := (AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ M)) hb).symm
      refine ⟨e.toAlgHom.comp (Ideal.Quotient.mkₐ K M), ?_⟩
      ext a
      simp only [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      change e (Ideal.Quotient.mk M a) = 0 ↔ _
      rw [map_eq_zero_iff e e.injective, Ideal.Quotient.eq_zero_iff_mem]

/-- 51wmmpHand0-28083 (7:48:03) [prop] For `A` finitely generated over a field `k`,
`X(k) ⊂ X₀ ⊂ Spec A`: the kernel of a `k`-point is maximal (a closed point), and if `k` is
algebraically closed every closed point arises (`Buffalo.AG.Part01.prop_8452`). -/
theorem prop_28083 {K A : Type u} [Field K] [CommRing A] [Algebra K A] :
    ∀ u : A →ₐ[K] K, IsClosed ({⟨RingHom.ker u, (RingHom.ker_isMaximal_of_surjective u
      fun c => ⟨algebraMap K A c, u.commutes c⟩).isPrime⟩} : Set (PrimeSpectrum A)) :=
  fun u => (isClosed_singleton_iff_isMaximal _).2
    (RingHom.ker_isMaximal_of_surjective u fun c => ⟨algebraMap K A c, u.commutes c⟩)

/-- 51wmmpHand0-28083 (7:48:03) [prop] If moreover `k` is algebraically closed, every closed
point of `Spec A` is the kernel of a `k`-point. -/
theorem prop_28083_algClosed {K A : Type u} [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (x : PrimeSpectrum A) (hx : IsClosed ({x} : Set (PrimeSpectrum A))) :
    ∃ u : A →ₐ[K] K, RingHom.ker u = x.asIdeal := by
  obtain ⟨u, hu⟩ := (prop_8452 (K := K)).2 ⟨x.asIdeal, (isClosed_singleton_iff_isMaximal x).1 hx⟩
  exact ⟨u, congrArg Subtype.val hu⟩

/-! ### Very dense subsets -/

/-- 51wmmpHand0-28151 (7:49:11) [def] A subset `X₀ ⊆ X` is very dense if `U ↦ U ∩ X₀`, from the
open sets of `X` to those of `X₀`, is injective. -/
def VeryDense {X : Type*} [TopologicalSpace X] (X₀ : Set X) : Prop :=
  Function.Injective fun U : Opens X => (U : Set X) ∩ X₀

/-- 51wmmpHand0-28151 (7:49:11) [def] The map from the open sets of `X` to those of `X₀` is always
surjective (subspace topology), hence bijective when `X₀` is very dense. -/
theorem def_28151 {X : Type*} [TopologicalSpace X] (X₀ : Set X) :
    Function.Surjective (fun U : Opens X => (⟨Subtype.val ⁻¹' (U : Set X),
      U.2.preimage continuous_subtype_val⟩ : Opens X₀)) := fun W => by
  obtain ⟨t, ht, hW⟩ := isOpen_induced_iff.1 W.2
  exact ⟨⟨t, ht⟩, Opens.ext hW⟩

/-- 51wmmpHand0-28339 (7:52:19) [prop] `X₀` is very dense iff every nonempty locally closed subset
of `X` meets `X₀`. -/
theorem prop_28339 {X : Type*} [TopologicalSpace X] (X₀ : Set X) :
    VeryDense X₀ ↔ ∀ Z : Set X, Z.Nonempty → IsLocallyClosed Z → (Z ∩ X₀).Nonempty := by
  constructor
  · rintro h Z ⟨x, hx⟩ ⟨U, C, hU, hC, rfl⟩
    by_contra hne
    have heq : ((⟨U, hU⟩ : Opens X) : Set X) ∩ X₀ = ((⟨U, hU⟩ ⊓ ⟨Cᶜ, hC.isOpen_compl⟩ : Opens X) :
        Set X) ∩ X₀ := by
      ext y
      simp only [Opens.coe_inf, Opens.coe_mk, Set.mem_inter_iff, Set.mem_compl_iff]
      constructor
      · rintro ⟨hyU, hy0⟩
        exact ⟨⟨hyU, fun hyC => hne ⟨y, ⟨hyU, hyC⟩, hy0⟩⟩, hy0⟩
      · rintro ⟨⟨hyU, -⟩, hy0⟩
        exact ⟨hyU, hy0⟩
    have := congrArg (fun V : Opens X => x ∈ (V : Set X)) (h heq)
    simp only [Opens.coe_inf, Opens.coe_mk, Set.mem_inter_iff, Set.mem_compl_iff, eq_iff_iff] at this
    exact (this.1 hx.1).2 hx.2
  · intro h U V hUV
    by_contra hne
    have key : ∀ U V : Opens X, (U : Set X) ∩ X₀ = (V : Set X) ∩ X₀ → (U : Set X) ⊆ V := by
      intro U V hUV x hxU
      by_contra hxV
      obtain ⟨y, ⟨hyU, hyV⟩, hy0⟩ := h ((U : Set X) ∩ (V : Set X)ᶜ) ⟨x, hxU, hxV⟩
        (U.2.isLocallyClosed.inter V.2.isClosed_compl.isLocallyClosed)
      have : y ∈ (V : Set X) ∩ X₀ := hUV ▸ ⟨hyU, hy0⟩
      exact hyV this.1
    exact hne (Opens.ext (le_antisymm (key U V hUV) (key V U hUV.symm)))

/-- 51wmmpHand0-28403 (7:53:23) [prop] `X₀` is very dense iff `T ∩ X₀` is dense in `T` for every
closed `T`. -/
theorem prop_28403 {X : Type*} [TopologicalSpace X] (X₀ : Set X) :
    VeryDense X₀ ↔ ∀ T : Set X, IsClosed T → T ⊆ closure (T ∩ X₀) := by
  rw [prop_28339]
  constructor
  · intro h T hT x hxT
    by_contra hx
    obtain ⟨y, ⟨hyU, hyT⟩, hy0⟩ := h ((closure (T ∩ X₀))ᶜ ∩ T) ⟨x, hx, hxT⟩
      (isClosed_closure.isOpen_compl.isLocallyClosed.inter hT.isLocallyClosed)
    exact hyU (subset_closure ⟨hyT, hy0⟩)
  · rintro h Z ⟨x, hx⟩ ⟨U, C, hU, hC, rfl⟩
    have hxc := h C hC hx.2
    obtain ⟨y, hyU, hyC, hy0⟩ := mem_closure_iff.1 hxc U hU hx.1
    exact ⟨y, ⟨hyU, hyC⟩, hy0⟩

/-- 51wmmpHand0-28472 (7:54:32) [prop] If `X₀` is very dense, the lattices of open sets of `X` and
of `X₀` are isomorphic (by `U ↦ U ∩ X₀`). -/
def prop_28472 {X : Type*} [TopologicalSpace X] (X₀ : Set X) (h : VeryDense X₀) :
    Opens X ≃o Opens X₀ := by
  let f : Opens X → Opens X₀ := fun U => ⟨Subtype.val ⁻¹' (U : Set X),
    U.2.preimage continuous_subtype_val⟩
  have hle : ∀ U V : Opens X, f U ≤ f V ↔ U ≤ V := fun U V => by
    refine ⟨fun hUV => ?_, fun hUV x hx => hUV hx⟩
    have : ((U ⊔ V : Opens X) : Set X) ∩ X₀ = (V : Set X) ∩ X₀ := by
      ext x
      simp only [Opens.coe_sup, Set.mem_inter_iff, Set.mem_union]
      constructor
      · rintro ⟨hx | hx, h0⟩
        · exact ⟨@hUV ⟨x, h0⟩ hx, h0⟩
        · exact ⟨hx, h0⟩
      · rintro ⟨hx, h0⟩
        exact ⟨Or.inr hx, h0⟩
    rw [← h this]
    exact le_sup_left
  exact
    { Equiv.ofBijective f ⟨fun U V hUV => le_antisymm ((hle U V).1 hUV.le) ((hle V U).1 hUV.ge),
        def_28151 X₀⟩ with
      map_rel_iff' := fun {U V} => hle U V }

/-- 51wmmpHand0-28537 (7:55:37) [prop] Conversely, if restriction to `X₀` is conservative on the
open sets (the subobjects of the final sheaf): `U ⊆ V` and `U ∩ X₀ = V ∩ X₀` imply `U = V`, then
`X₀` is very dense. -/
theorem prop_28537 {X : Type*} [TopologicalSpace X] (X₀ : Set X)
    (h : ∀ U V : Opens X, U ≤ V → (U : Set X) ∩ X₀ = (V : Set X) ∩ X₀ → U = V) :
    VeryDense X₀ := by
  intro U V hUV
  simp only at hUV
  have h1 : U ⊓ V = U := h _ _ inf_le_left (by
    change (U : Set X) ∩ V ∩ X₀ = _
    rw [Set.inter_assoc, ← hUV, ← Set.inter_assoc, Set.inter_self])
  have h2 : U ⊓ V = V := h _ _ inf_le_right (by
    change (U : Set X) ∩ V ∩ X₀ = _
    rw [Set.inter_comm (U : Set X), Set.inter_assoc, hUV, ← Set.inter_assoc, Set.inter_self])
  exact h1.symm.trans h2

/-- 51wmmpHand0-28667 (7:57:47) [prop] If `X` is sober and `X₀` very dense, the points of `X`
correspond to the irreducible closed subsets of `X₀` (`x ↦ closure {x} ∩ X₀`), so `X` is the sober
space associated to `X₀`. -/
theorem prop_28667 {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X] (X₀ : Set X)
    (h : VeryDense X₀) :
    Set.BijOn (fun x : X => closure {x} ∩ X₀) Set.univ
      {S : Set X | IsIrreducible S ∧ ∃ Z, IsClosed Z ∧ S = Z ∩ X₀} := by
  have hcl : ∀ Z : Set X, IsClosed Z → closure (Z ∩ X₀) = Z := fun Z hZ =>
    le_antisymm (closure_minimal Set.inter_subset_left hZ) ((prop_28403 X₀).1 h Z hZ)
  refine ⟨fun x _ => ⟨?_, closure {x}, isClosed_closure, rfl⟩, fun x _ y _ hxy => ?_, ?_⟩
  · rw [← isIrreducible_iff_closure, hcl _ isClosed_closure]
    exact isIrreducible_singleton.closure
  · have := congrArg closure hxy
    simp only [hcl _ isClosed_closure] at this
    exact (inseparable_iff_closure_eq.2 this).eq
  · rintro S ⟨hS, Z, hZ, rfl⟩
    have hZi : IsIrreducible Z := by rw [← hcl Z hZ]; exact hS.closure
    obtain ⟨x, hx⟩ := QuasiSober.sober hZi hZ
    exact ⟨x, trivial, by simp only [hx.def]⟩

/-- 51wmmpHand0-28733 (7:58:53) [prop] For `A` finitely generated over a field, the closed points
of `Spec A` are very dense (Nullstellensatz: `Spec A` is a Jacobson space). -/
theorem prop_28733 (K A : Type*) [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A] :
    VeryDense (closedPoints (PrimeSpectrum A)) := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  rw [prop_28339]
  exact jacobsonSpace_iff_locallyClosed.1 inferInstance

/-- 51wmmpHand0-28988 (8:03:08) [prop] For `A` finitely generated over a field, the nilradical is
the intersection of the maximal ideals; for any ring it is the intersection of the primes. -/
theorem prop_28988 (K A : Type*) [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A] :
    nilradical A = sInf {M : Ideal A | M.IsMaximal} ∧
      nilradical A = sInf {P : Ideal A | P.IsPrime} := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  refine ⟨?_, nilradical_eq_sInf A⟩
  have h := IsJacobsonRing.out' (nilradical A) (Ideal.radical_isRadical ⊥)
  rw [← h, nilradical, Ideal.jacobson_radical_eq_jacobson, Ideal.jacobson]
  simp

/-- 51wmmpHand0-29114 (8:05:14) [prop] For `k` algebraically closed and `A` of finite type,
`X(k)` (the closed points) is very dense in `Spec A`, so it has the same lattice of open sets (and
of closed, locally closed and irreducible closed sets) as `Spec A`; it contains no non-closed,
in particular no generic, point. -/
theorem prop_29114 (K A : Type u) [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] :
    VeryDense (closedPoints (PrimeSpectrum A)) ∧
      Nonempty (Opens (PrimeSpectrum A) ≃o Opens (closedPoints (PrimeSpectrum A))) ∧
      (∀ x : PrimeSpectrum A, x ∈ closedPoints (PrimeSpectrum A) ↔
        ∃ u : A →ₐ[K] K, RingHom.ker u = x.asIdeal) := by
  refine ⟨prop_28733 K A, ⟨prop_28472 _ (prop_28733 K A)⟩, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · exact prop_28083_algClosed x hx
  · rintro ⟨u, hu⟩
    have := prop_28083 (K := K) (A := A) u
    rwa [show (⟨RingHom.ker u, _⟩ : PrimeSpectrum A) = x from PrimeSpectrum.ext hu] at this

/-- 51wmmpHand0-29287 (8:08:07) [rem] The topology of `Spec A` does not determine `A`: `ℤ/4` and
`(ℤ/4)/nil` have homeomorphic spectra (`prop_23611`) but are not isomorphic, one being reduced
and not the other. -/
theorem rem_29287 :
    Nonempty (PrimeSpectrum (ZMod 4 ⧸ nilradical (ZMod 4)) ≃ₜ PrimeSpectrum (ZMod 4)) ∧
      IsEmpty (ZMod 4 ≃+* ZMod 4 ⧸ nilradical (ZMod 4)) := by
  refine ⟨prop_23611 _, ⟨fun e => ?_⟩⟩
  have : IsReduced (ZMod 4 ⧸ nilradical (ZMod 4)) :=
    (Ideal.isRadical_iff_quotient_reduced _).1 (Ideal.radical_isRadical ⊥)
  have : IsReduced (ZMod 4) := isReduced_of_injective e.toRingHom e.injective
  have h2 : (2 : ZMod 4) ^ 2 = 0 := by decide
  exact absurd (IsReduced.eq_zero 2 ⟨2, h2⟩) (by decide)

end June6

end

end Buffalo.AG.Part02
