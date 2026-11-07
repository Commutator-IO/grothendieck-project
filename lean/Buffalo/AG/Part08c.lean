import Buffalo.AG.Part08b

/-!
# Buffalo, algebraic geometry, part 08 (c): 9 July 1973 (tape 3) and 10 July 1973 (to 4:14:24)

The entries of `docs/buffalo-ag/index.tex` lines 1110–1124 and 1142–1190 (video `vuys5SNs2eQ`,
1:06:53–1:14:24 and 2:49:55–4:14:24): closures of images of quasi-compact morphisms, descent of
subsets and open sets, monomorphisms that are not immersions, constructible sets and Chevalley's
theorem, descent of integrality and finiteness.

Statements about the closure of the image of a quasi-compact morphism are proved for
`Spec B → Spec A` (a quasi-compact morphism of affine schemes) and, abstractly, for any continuous
map satisfying the conclusion of `prop_12865` (`SpecClosure`).
-/

open CategoryTheory Limits TensorProduct Topology PrimeSpectrum AlgebraicGeometry

universe u v

namespace Buffalo.AG.Part08

noncomputable section

/-! ### Closure of the image of a quasi-compact morphism -/

section Closure

/-- The closure of the image of `f` consists of the specializations of points of the image (true
for quasi-compact morphisms of schemes, `prop_12865`). -/
def SpecClosure {Z S : Type*} [TopologicalSpace Z] [TopologicalSpace S] (f : Z → S) : Prop :=
  ∀ s, s ∈ closure (Set.range f) ↔ ∃ z, f z ⤳ s

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- vuys5SNs2eQ-12865 (3:34:25) [prop] If `f : Z → S` is quasi-compact, `s ∈ closure f(Z)` iff `s`
has a generization in `f(Z)`. Proved for `Spec B → Spec A` (mathlib:
`PrimeSpectrum.closure_range_comap`, `Ideal.exists_ideal_comap_le_prime`). -/
theorem prop_12865 (φ : A →+* B) : SpecClosure (comap φ) := by
  intro s
  rw [closure_range_comap]
  constructor
  · intro hs
    obtain ⟨Q, -, hQ, hle⟩ := Ideal.exists_ideal_comap_le_prime (f := φ) s.asIdeal ⊥ (by
      rw [← RingHom.ker_eq_comap_bot]; exact hs)
    exact ⟨⟨Q, hQ⟩, (le_iff_specializes _ _).1 hle⟩
  · rintro ⟨z, hz⟩
    have : (comap φ z).asIdeal ≤ s.asIdeal := (le_iff_specializes _ _).2 hz
    intro x hx
    exact this (show φ x ∈ z.asIdeal by rw [RingHom.mem_ker.1 hx]; exact zero_mem _)

/-- vuys5SNs2eQ-12993 (3:36:33) [prop] `s` is interior to the complement of `f(Z)` iff all
generizations of `s` lie outside `f(Z)` (from `prop_12865`, for `Spec B → Spec A`). -/
theorem prop_12993 (φ : A →+* B) (s : PrimeSpectrum A) :
    s ∈ interior (Set.range (comap φ))ᶜ ↔ ∀ t, t ⤳ s → t ∉ Set.range (comap φ) := by
  rw [interior_compl, Set.mem_compl_iff, prop_12865 φ s]
  constructor
  · rintro h t hts ⟨z, rfl⟩
    exact h ⟨z, hts⟩
  · rintro h ⟨z, hz⟩
    exact h _ hz ⟨z, rfl⟩

variable {X Y S S' : Type*} [TopologicalSpace X] [TopologicalSpace S] [TopologicalSpace S']

/-- vuys5SNs2eQ-4013 (1:06:53) [prop] If `g` is generalizing and `f` quasi-compact,
`g⁻¹(closure f(Z)) = closure (g⁻¹ f(Z))` (here for any `f` with `SpecClosure f`). -/
theorem prop_4013 {f : X → S} (hf : SpecClosure f) {g : S' → S} (hgc : Continuous g)
    (hg : GeneralizingMap g) :
    g ⁻¹' closure (Set.range f) = closure (g ⁻¹' Set.range f) := by
  refine subset_antisymm (fun s' hs' => ?_) (hgc.closure_preimage_subset _)
  obtain ⟨z, hz⟩ := (hf (g s')).1 hs'
  obtain ⟨t, ht, hgt⟩ := hg hz
  exact closure_mono (Set.singleton_subset_iff.2 (show t ∈ g ⁻¹' Set.range f from ⟨z, hgt.symm⟩))
    (specializes_iff_mem_closure.1 ht)

/-- vuys5SNs2eQ-4142 (1:09:02) [prop] If `g` is generalizing and `f` quasi-compact dominant, the
base change is dominant (its image is `g⁻¹ f(Z)`, mathlib `Scheme.Pullback.range_snd`); the
converse holds if `g` is surjective. -/
theorem prop_4142 {f : X → S} (hf : SpecClosure f) {g : S' → S} (hgc : Continuous g)
    (hg : GeneralizingMap g) :
    (Dense (Set.range f) → Dense (g ⁻¹' Set.range f)) ∧
      (Function.Surjective g → Dense (g ⁻¹' Set.range f) → Dense (Set.range f)) := by
  refine ⟨fun h => ?_, fun hs h => ?_⟩
  · rw [dense_iff_closure_eq, ← prop_4013 hf hgc hg, h.closure_eq, Set.preimage_univ]
  · rw [dense_iff_closure_eq, ← prop_4013 hf hgc hg, ← Set.preimage_univ (f := g)] at h
    rw [dense_iff_closure_eq]
    exact Set.preimage_injective.2 hs h

/-- vuys5SNs2eQ-4464 (1:14:24) [prop] A quasi-compact `f` is dominant iff its fibre at each
maximal point of `S` is nonempty (for `S` sober and any `f` with `SpecClosure f`). -/
theorem prop_4464 [QuasiSober S] [T0Space S] {f : X → S} (hf : SpecClosure f) :
    Dense (Set.range f) ↔ ∀ η, IsMaximalPoint η → η ∈ Set.range f := by
  constructor
  · intro h η hη
    obtain ⟨z, hz⟩ := (hf η).1 (h.closure_eq ▸ Set.mem_univ η)
    have h1 : closure {η} ⊆ closure {f z} := hz.closure_subset
    have h2 : closure {f z} ⊆ closure {η} := hη.2 isIrreducible_singleton.closure h1
    have : η ⤳ f z := specializes_iff_closure_subset.2 h2
    exact ⟨z, (hz.antisymm this).eq⟩
  · intro h
    rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro s
    have hC := irreducibleComponent_mem_irreducibleComponents s
    have hgen := hC.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    have hmax : IsMaximalPoint hC.1.genericPoint :=
      (congrArg (· ∈ irreducibleComponents S) hgen).mpr hC
    have hs : s ∈ closure {hC.1.genericPoint} := hgen.ge mem_irreducibleComponent
    exact closure_minimal (Set.singleton_subset_iff.2 (subset_closure (h _ hmax))) isClosed_closure
      hs

end Closure

/-! ### Descent of subsets and open sets -/

section Subsets

variable {S S' : Scheme.{u}} (g : S' ⟶ S)

/-- vuys5SNs2eQ-10517 (2:55:17) [prop] A subset `T'` of `S'` comes from a subset of `S` iff its two
inverse images in `S'' = S' ×_S S'` coincide (surjectivity of `g` makes the subset unique), and then
it comes from `g(T')`. -/
theorem prop_10517 (T' : Set S') :
    (∃ T : Set S, T' = g ⁻¹' T) ↔
      pullback.fst g g ⁻¹' T' = pullback.snd g g ⁻¹' T' := by
  constructor
  · rintro ⟨T, rfl⟩
    rw [← Set.preimage_comp, ← Set.preimage_comp]
    ext p
    simp only [Set.mem_preimage, Function.comp_apply]
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  · intro h
    refine ⟨g '' T', subset_antisymm (Set.subset_preimage_image _ _) ?_⟩
    rintro x ⟨y, hy, hxy⟩
    obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := g) x y hxy.symm
    have : p ∈ pullback.snd g g ⁻¹' T' := by simpa [hp2] using hy
    rw [← h] at this
    simpa [hp1] using this

/-- vuys5SNs2eQ-10644 (2:57:24) [prop] If `g` is faithfully flat and quasi-compact, the open (resp.
closed) sets of `S` are identified with the open (resp. closed) sets of `S'` having the same two
inverse images in `S''` (`prop_10517` and `g` submersive, `prop_4795`). -/
theorem prop_10644 [Surjective g] [Flat g] [QuasiCompact g] (T' : Set S') :
    ((∃ T : Set S, IsOpen T ∧ T' = g ⁻¹' T) ↔
      IsOpen T' ∧ pullback.fst g g ⁻¹' T' = pullback.snd g g ⁻¹' T') ∧
    ((∃ T : Set S, IsClosed T ∧ T' = g ⁻¹' T) ↔
      IsClosed T' ∧ pullback.fst g g ⁻¹' T' = pullback.snd g g ⁻¹' T') := by
  have hq := prop_4795 g
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨hT.preimage g.continuous, (prop_10517 g _).1 ⟨T, rfl⟩⟩
  · rintro ⟨hT', h⟩
    obtain ⟨T, rfl⟩ := (prop_10517 g T').2 h
    exact ⟨T, hq.isOpen_preimage.1 hT', rfl⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨hT.preimage g.continuous, (prop_10517 g _).1 ⟨T, rfl⟩⟩
  · rintro ⟨hT', h⟩
    obtain ⟨T, rfl⟩ := (prop_10517 g T').2 h
    exact ⟨T, hq.isClosed_preimage.1 hT', rfl⟩

end Subsets

/-! ### Monomorphisms that are not immersions; non locally closed images -/

section Counterexamples

/-- No nonzero integer is divisible by every prime. -/
theorem exists_prime_not_dvd {n : ℤ} (hn : n ≠ 0) : ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ n := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (n := n.natAbs + 1) (by omega)
  refine ⟨p, hp, fun h => ?_⟩
  have h1 : (p : ℤ) ∣ (n.natAbs : ℤ) := (Int.dvd_natAbs).2 h
  have h2 : (p : ℤ) ∣ ((n.natAbs + 1 : ℕ) : ℤ) := by exact_mod_cast hpn
  have : (p : ℤ) ∣ 1 := by simpa using Int.dvd_sub h2 h1
  exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)

/-- A point of a spectrum whose singleton is open is the generic point `⊥` of a domain. -/
theorem eq_bot_of_isOpen_singleton {R : Type u} [CommRing R] [IsDomain R] (x : PrimeSpectrum R)
    (hx : IsOpen ({x} : Set (PrimeSpectrum R))) : x.asIdeal = ⊥ := by
  have hb : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ⤳ x :=
    (le_iff_specializes _ _).1 bot_le
  have := hx.stableUnderGeneralization hb rfl
  rw [Set.mem_singleton_iff] at this
  rw [← this]

/-- vuys5SNs2eQ-10967 (3:02:47) [cex] `(𝔸¹ ∖ {0}) ⊔ {0} → 𝔸¹` is a monomorphism that is not an
immersion. Proved: on the underlying spaces (`𝔸¹ = Spec k[X]`, `0 = (X)`) the map is a continuous
bijection that is not an embedding, since `{0}` is open in the source but not in `𝔸¹`. -/
theorem cex_10967 (k : Type u) [Field k] :
    let m : PrimeSpectrum (Polynomial k) :=
      ⟨Ideal.span {Polynomial.X},
        (Ideal.span_singleton_prime Polynomial.X_ne_zero).2 Polynomial.prime_X⟩
    let ι : ({x | x ≠ m} : Set (PrimeSpectrum (Polynomial k))) ⊕ Unit → PrimeSpectrum (Polynomial k) :=
      Sum.elim Subtype.val (fun _ => m)
    Continuous ι ∧ Function.Bijective ι ∧ ¬ IsEmbedding ι := by
  intro m ι
  refine ⟨continuous_sum_dom.2 ⟨continuous_subtype_val, continuous_const⟩, ⟨?_, ?_⟩, fun he => ?_⟩
  · rintro (⟨a, ha⟩ | a) (⟨b, hb⟩ | b) h
    · simp only [ι, Sum.elim_inl] at h; subst h; rfl
    · exact absurd h ha
    · exact absurd h.symm hb
    · rfl
  · intro y
    by_cases hy : y = m
    · exact ⟨Sum.inr (), hy.symm⟩
    · exact ⟨Sum.inl ⟨y, hy⟩, rfl⟩
  · have hopen : IsOpen ({Sum.inr ()} : Set (({x | x ≠ m} : Set _) ⊕ Unit)) := by
      have := isOpen_range_inr (X := ({x | x ≠ m} : Set (PrimeSpectrum (Polynomial k))))
        (Y := Unit)
      convert this using 1
      ext x
      constructor
      · rintro rfl; exact ⟨(), rfl⟩
      · rintro ⟨⟨⟩, rfl⟩; rfl
    obtain ⟨V, hV, hpre⟩ := he.isInducing.isOpen_iff.1 hopen
    have hV' : V = {m} := by
      ext y
      constructor
      · intro hy
        by_contra hym
        have : (Sum.inl ⟨y, hym⟩ : ({x | x ≠ m} : Set _) ⊕ Unit) ∈ ι ⁻¹' V := hy
        rw [hpre] at this
        simp at this
      · rintro rfl
        have : (Sum.inr () : ({x | x ≠ m} : Set _) ⊕ Unit) ∈ ι ⁻¹' V := by rw [hpre]; rfl
        exact this
    rw [hV'] at hV
    have h0 := eq_bot_of_isOpen_singleton m hV
    have : (Polynomial.X : Polynomial k) ∈ (⊥ : Ideal (Polynomial k)) :=
      h0 ▸ Ideal.mem_span_singleton_self _
    exact Polynomial.X_ne_zero ((Submodule.mem_bot _).1 this)

/-- vuys5SNs2eQ-12606 (3:30:06) [cex] A filtered union of pieces mapped onto locally closed subsets
need not map onto a locally closed subset: the closed points of a line (here `Spec ℤ`), each finite
set of which is closed, form a dense subset that is not locally closed. -/
theorem cex_12606 :
    let P := {x : PrimeSpectrum ℤ | x.asIdeal.IsMaximal}
    (∀ s : Finset (PrimeSpectrum ℤ), (↑s : Set _) ⊆ P → IsClosed (↑s : Set (PrimeSpectrum ℤ))) ∧
      Dense P ∧ ¬ IsLocallyClosed P := by
  intro P
  have hdense : Dense P := by
    rw [dense_iff_closure_eq, ← zeroLocus_vanishingIdeal_eq_closure, Set.eq_univ_iff_forall]
    intro x n hn
    by_contra hnx
    have hn0 : n ≠ 0 := fun h => hnx (h ▸ zero_mem _)
    obtain ⟨p, hp, hpn⟩ := exists_prime_not_dvd hn0
    have hpI : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
    have := (mem_vanishingIdeal _ _).1 hn ⟨_, hpI.isPrime⟩ hpI
    exact hpn (Ideal.mem_span_singleton.1 this)
  refine ⟨fun s hs => ?_, hdense, fun hlc => ?_⟩
  · rw [← Set.biUnion_of_singleton (s : Set (PrimeSpectrum ℤ))]
    exact s.finite_toSet.isClosed_biUnion fun x hx => (isClosed_singleton_iff_isMaximal x).2 (hs hx)
  · rw [isLocallyClosed_iff_isOpen_coborder, coborder, hdense.closure_eq, ← Set.compl_eq_univ_sdiff,
      compl_compl] at hlc
    have h2 : (⟨Ideal.span {(2 : ℤ)}, (PrincipalIdealRing.isMaximal_of_irreducible
        (Int.prime_two.irreducible)).isPrime⟩ : PrimeSpectrum ℤ) ∈ P :=
      PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible
    have hb := hlc.stableUnderGeneralization
      ((le_iff_specializes (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℤ) _).1 bot_le) h2
    have hb' : (⊥ : Ideal ℤ).IsMaximal := hb
    have h2' : (Ideal.span {(2 : ℤ)}).IsMaximal := h2
    have e := hb'.eq_of_le h2'.ne_top bot_le
    have : (2 : ℤ) ∈ (⊥ : Ideal ℤ) := e ▸ Ideal.mem_span_singleton_self _
    exact two_ne_zero ((Submodule.mem_bot ℤ).1 this)

end Counterexamples

/-! ### Chevalley's theorem, openness, integrality -/

section Chevalley

variable {A B : Type u} [CommRing A] [CommRing B]

/-- vuys5SNs2eQ-13186 (3:39:46) [thm] Chevalley: if `f` is of finite presentation, `f(Z)` is
(locally) constructible. Affine case (mathlib: `PrimeSpectrum.isConstructible_comap_image`). -/
theorem thm_13186 (φ : A →+* B) (hφ : φ.FinitePresentation) {s : Set (PrimeSpectrum B)}
    (hs : IsConstructible s) : IsConstructible (comap φ '' s) :=
  isConstructible_comap_image hφ hs

/-- vuys5SNs2eQ-13380 (3:43:00) [prop] A generalizing morphism locally of finite presentation is
open (mathlib: `isOpenMap_of_generalizingMap`). -/
theorem prop_13380 {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (hf : GeneralizingMap f) : IsOpenMap f :=
  isOpenMap_of_generalizingMap f hf

variable [Algebra A B]

/-- vuys5SNs2eQ-15009 (4:10:09) [prop] `B` is integral over `A` iff its finitely generated
`A`-subalgebras are finite over `A`. -/
theorem prop_15009 :
    Algebra.IsIntegral A B ↔ ∀ C : Subalgebra A B, C.FG → Module.Finite A C := by
  constructor
  · intro _ C ⟨s, hs⟩
    subst hs
    exact Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
      (fun x _ => Algebra.IsIntegral.isIntegral x)
  · intro h
    refine ⟨fun b => ?_⟩
    have := h (Algebra.adjoin A {b}) ⟨{b}, by simp⟩
    have hb : IsIntegral A (⟨b, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {b}) :=
      IsIntegral.of_finite A _
    exact (isIntegral_algHom_iff (Algebra.adjoin A {b}).val Subtype.val_injective).2 hb

/-- vuys5SNs2eQ-14946 (4:09:06) [prop] If `A → A'` is faithfully flat, `B` is finite over `A` iff
`A' ⊗_A B` is over `A'` (mathlib: `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`);
the integral case is not proved here. -/
theorem prop_14946 (A' : Type u) [CommRing A'] [Algebra A A'] [Module.FaithfullyFlat A A'] :
    Module.Finite A' (A' ⊗[A] B) ↔ Module.Finite A B :=
  prop_3491 B

end Chevalley

section Immersions

variable {S S' X : Scheme.{u}} (g : S' ⟶ S) (f : X ⟶ S)

/-- vuys5SNs2eQ-12211 (3:23:31) [prop] If `g` is faithfully flat quasi-compact, `f` is an open
immersion iff `f'` is (mathlib:
`descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`); closed and quasi-compact
immersions are not covered. -/
theorem prop_12211 [Surjective g] [Flat g] [QuasiCompact g] :
    IsOpenImmersion (pullback.snd f g) ↔ IsOpenImmersion f :=
  MorphismProperty.pullback_snd_iff (P := @IsOpenImmersion) (fpqc_hyp g)

/-- vuys5SNs2eQ-14816 (4:06:56) [prop] `f` is quasi-affine if `X → Spec f_*𝒪_X` is an open
immersion. Absolute case (`Y = Spec ℤ`, mathlib `Scheme.IsQuasiAffine`): a quasi-compact `X` is
quasi-affine as soon as `X → Spec Γ(X, 𝒪_X)` is an open immersion. -/
theorem prop_14816 (Z : Scheme.{u}) [CompactSpace Z] [IsOpenImmersion Z.toSpecΓ] :
    Z.IsQuasiAffine :=
  { }

end Immersions

end

end Buffalo.AG.Part08
