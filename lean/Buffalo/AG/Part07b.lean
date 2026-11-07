import Mathlib

/-!
# Buffalo, algebraic geometry, part 07 (b): 2 July 1973

The entries of `docs/buffalo-ag/index.tex` lines 941–995 (video `Oqhr-Gt66es`, 6:47:12–8:27:42):
finite presentation and limits, projective, ample and proper morphisms, valuative criteria,
integral extensions, finite and integral morphisms.

Conventions. Mathlib has no projective bundle `ℙ(E)`, no ample or very ample invertible sheaves and
no Picard group of a scheme: the entries on them are not formalised, except through `Proj` of a
graded ring (`Proj.toSpecZero`), which is the affine-base case `ℙ(E) = Proj(Sym E)`. The valuative
criteria are mathlib's, for all valuation rings (the lecture's discrete valuation rings need
noetherian hypotheses).
-/

open TensorProduct AlgebraicGeometry CategoryTheory Limits

universe u

namespace Buffalo.AG.Part07

noncomputable section

section FinitePresentation

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {G : ι → Type*}
  [∀ i, CommRing (G i)] (f : ∀ i j, i ≤ j → G i →+* G j)
  [DirectedSystem G fun i j h => f i j h]

omit [DirectedSystem G fun i j h => f i j h] in
/-- Oqhr-Gt66es-24432 (6:47:12) [prop] (key step, one variable) If `A = lim→ A_i` is a filtered
inductive limit of rings, finitely many polynomials over `A` (the relations of a finite
presentation) all come from polynomials over a single `A_i`. -/
theorem prop_24432 (s : Finset (Polynomial (Ring.DirectLimit G fun i j h => f i j h))) :
    ∃ i, ∀ q ∈ s, ∃ p : Polynomial (G i),
      p.map (Ring.DirectLimit.of G (fun i j h => f i j h) i) = q := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | insert q s _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, p, hp⟩ := Ring.DirectLimit.Polynomial.exists_of q
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
    have key : ∀ {a b : ι} (hab : a ≤ b) (p : Polynomial (G a)),
        (p.map (f a b hab)).map (Ring.DirectLimit.of G (fun i j h => f i j h) b) =
          p.map (Ring.DirectLimit.of G (fun i j h => f i j h) a) := by
      intro a b hab p
      rw [Polynomial.map_map]
      congr 1
      ext x
      exact Ring.DirectLimit.of_f hab x
    refine ⟨l, fun r hr => ?_⟩
    rcases Finset.mem_insert.1 hr with rfl | hr
    · exact ⟨p.map (f j l hjl), by rw [key, hp]⟩
    · obtain ⟨p', hp'⟩ := hi r hr
      exact ⟨p'.map (f i l hil), by rw [key, hp']⟩

end FinitePresentation

section Proper

variable {X Y Z : Scheme.{u}}

/-- Oqhr-Gt66es-25222 (7:00:22) [prop] (graded form) For a graded ring `A = ⊕ 𝒜_n` of finite
type over `𝒜_0`, `Proj A → Spec 𝒜_0` is separated and of finite type (for `ℙ(E) = Proj(Sym E)`). -/
theorem prop_25222 {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
    [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A] :
    IsSeparated (Proj.toSpecZero 𝒜) ∧ LocallyOfFiniteType (Proj.toSpecZero 𝒜) ∧
      QuasiCompact (Proj.toSpecZero 𝒜) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- Oqhr-Gt66es-27355 (7:35:55) [def] (proper half) `f` is proper iff it is of finite type, separated
and universally closed (mathlib: `IsProper`, whose quasi-compactness follows from universal
closedness). -/
theorem def_27355 (f : X ⟶ Y) :
    IsProper f ↔ (LocallyOfFiniteType f ∧ QuasiCompact f) ∧ IsSeparated f ∧ UniversallyClosed f :=
  ⟨fun _ => ⟨⟨inferInstance, inferInstance⟩, inferInstance, inferInstance⟩,
    fun ⟨⟨h1, _⟩, h2, h3⟩ => @IsProper.mk _ _ f h2 h3 h1⟩

/-- Oqhr-Gt66es-28150 (7:49:10) [prop] Proper morphisms are stable under composition and base
change. -/
theorem prop_28150 (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g] (h : X ⟶ Z) :
    IsProper (f ≫ g) ∧ (∀ [IsProper g], IsProper (pullback.fst h g)) :=
  ⟨inferInstance, fun {_} => inferInstance⟩

/-- Oqhr-Gt66es-28218 (7:50:18) [prop] If `X` is proper over `Y` and `Z` separated over `Y`, every
`Y`-morphism `X → Z` is closed (it is proper). -/
theorem prop_28218 (p : X ⟶ Y) (q : Z ⟶ Y) [IsProper p] [IsSeparated q] (h : X ⟶ Z)
    (w : h ≫ q = p) : IsClosedMap h := by
  subst w
  have := IsProper.of_comp h q
  exact h.isClosedMap

/-- Oqhr-Gt66es-28347 (7:52:27) [prop] If `g : X → Z` is a `Y`-immersion into a proper `Y`-scheme,
`X` is proper over `Y` iff `g` is a closed immersion; closed immersions are proper. -/
theorem prop_28347 (g : X ⟶ Z) (q : Z ⟶ Y) [IsImmersion g] [IsProper q] :
    (IsProper (g ≫ q) ↔ IsClosedImmersion g) ∧ (∀ i : X ⟶ Y, IsClosedImmersion i → IsProper i) := by
  refine ⟨⟨fun _ => ?_, fun _ => inferInstance⟩, fun _ _ => inferInstance⟩
  have := IsProper.of_comp g q
  exact (IsClosedImmersion.iff_isProper_and_mono g).2 ⟨inferInstance, inferInstance⟩

/-- Oqhr-Gt66es-28411 (7:53:31) [prop] (first half, graded form) Projective morphisms are proper:
`Proj A → Spec 𝒜_0` is proper for `A` of finite type over `𝒜_0`. -/
theorem prop_28411 {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
    [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A] : IsProper (Proj.toSpecZero 𝒜) :=
  inferInstance

/-- Oqhr-Gt66es-28743 (7:59:03) [thm] (valuation-ring form) Valuative criterion of properness:
`f` is proper iff it is quasi-compact, quasi-separated, locally of finite type and satisfies the
valuative criterion (existence and uniqueness of lifts over all valuation rings). -/
theorem thm_28743 :
    @IsProper = ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType :=
  IsProper.eq_valuativeCriterion

/-- Oqhr-Gt66es-28870 (8:01:10) [prop] (valuation-ring form) Valuative criterion of separatedness:
`f` is separated iff it is quasi-separated and lifts over valuation rings are unique. -/
theorem prop_28870 : @IsSeparated = ValuativeCriterion.Uniqueness ⊓ @QuasiSeparated :=
  IsSeparated.eq_valuativeCriterion

end Proper

/-- Oqhr-Gt66es-29317 (8:08:37) [prop] (key step) Over a discrete valuation ring, a finitely
generated torsion-free module is free; this makes the quotient `M/(M ∩ H_K)` (torsion-free, since it
embeds in `M_K/H_K`) free of rank one. -/
theorem prop_29317 (A M : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.IsTorsionFree A M] :
    Module.Free A M :=
  Module.free_of_finite_type_torsion_free'

section Integral

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]

/-- Oqhr-Gt66es-29521 (8:12:01) [prop] For `x ∈ B`: `x` integral over `A` iff `A[x]` is a finitely
generated `A`-module iff `x` lies in a subalgebra finite over `A`. -/
theorem prop_29521 (x : B) :
    (IsIntegral A x → (Subalgebra.toSubmodule (Algebra.adjoin A {x})).FG) ∧
    ((Subalgebra.toSubmodule (Algebra.adjoin A {x})).FG → IsIntegral A x) ∧
    (IsIntegral A x ↔ ∃ S : Subalgebra A B, (Subalgebra.toSubmodule S).FG ∧ x ∈ S) :=
  ⟨IsIntegral.fg_adjoin_singleton,
    fun h => IsIntegral.of_mem_of_fg _ h x (Algebra.subset_adjoin rfl),
    fun h => ⟨_, h.fg_adjoin_singleton, Algebra.subset_adjoin rfl⟩,
    fun ⟨S, hS, hx⟩ => IsIntegral.of_mem_of_fg S hS x hx⟩

/-- Oqhr-Gt66es-29585 (8:13:05) [prop] `B` is integral over `A` iff it is the union of its
subalgebras finite over `A`. -/
theorem prop_29585 :
    Algebra.IsIntegral A B ↔ ∀ x : B, ∃ S : Subalgebra A B, (Subalgebra.toSubmodule S).FG ∧ x ∈ S := by
  rw [Algebra.isIntegral_def]
  exact forall_congr' fun x => (prop_29521 x).2.2

/-- Oqhr-Gt66es-29651 (8:14:11) [prop] Subalgebras and quotients of an integral algebra are
integral; integrality is stable under base change `C ⊗_A B`; the integral elements form the
subalgebra `integralClosure A B`. -/
theorem prop_29651 [Algebra.IsIntegral A B] (S : Subalgebra A B) (I : Ideal B) [Algebra A C] :
    Algebra.IsIntegral A S ∧ Algebra.IsIntegral (A ⧸ I.comap (algebraMap A B)) (B ⧸ I) ∧
    Algebra.IsIntegral C (C ⊗[A] B) ∧ (∀ x : B, x ∈ integralClosure A B ↔ IsIntegral A x) :=
  ⟨inferInstance, Algebra.IsIntegral.quotient, Algebra.IsIntegral.tensorProduct A C B,
    fun _ => mem_integralClosure_iff A B⟩

/-- Oqhr-Gt66es-29718 (8:15:18) [prop] Transitivity of integrality. -/
theorem prop_29718 [Algebra B C] [Algebra A C] [IsScalarTower A B C] [Algebra.IsIntegral A B]
    [Algebra.IsIntegral B C] : Algebra.IsIntegral A C :=
  Algebra.IsIntegral.trans B

end Integral

section FiniteMorphisms

variable {X Y Z : Scheme.{u}}

/-- Oqhr-Gt66es-29849 (8:17:29) [def] Finite (resp. integral) morphisms (mathlib: `IsFinite`,
`IsIntegralHom`, affine morphisms whose algebra is finite, resp. integral); on spectra. -/
theorem def_29849 {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (IsFinite (Spec.map φ) ↔ φ.hom.Finite) ∧ (IsIntegralHom (Spec.map φ) ↔ φ.hom.IsIntegral) :=
  ⟨IsFinite.SpecMap_iff φ, IsIntegralHom.SpecMap_iff⟩

/-- Oqhr-Gt66es-29981 (8:19:41) [prop] Finite and integral morphisms are stable under base change
and composition. -/
theorem prop_29981 :
    MorphismProperty.IsStableUnderBaseChange @IsFinite ∧
    MorphismProperty.IsStableUnderComposition @IsFinite ∧
    MorphismProperty.IsStableUnderBaseChange @IsIntegralHom ∧
    MorphismProperty.IsStableUnderComposition @IsIntegralHom :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Oqhr-Gt66es-30136 (8:22:16) [prop] Finite = integral and of finite type, for morphisms and for
algebras. -/
theorem prop_30136 (f : X ⟶ Y) {A' B' : Type*} [CommRing A'] [CommRing B'] [Algebra A' B'] :
    (IsFinite f ↔ IsIntegralHom f ∧ LocallyOfFiniteType f) ∧
    (Module.Finite A' B' ↔ Algebra.IsIntegral A' B' ∧ Algebra.FiniteType A' B') :=
  ⟨IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f, Algebra.finite_iff_isIntegral_and_finiteType⟩

/-- Oqhr-Gt66es-30201 (8:23:21) [prop] An integral morphism is affine, separated and universally
closed; a finite morphism is proper. -/
theorem prop_30201 (f : X ⟶ Y) :
    (IsIntegralHom f → IsAffineHom f ∧ IsSeparated f ∧ UniversallyClosed f) ∧
    (IsFinite f → IsProper f) :=
  ⟨fun _ => ⟨inferInstance, inferInstance, inferInstance⟩, fun _ => inferInstance⟩

/-- Oqhr-Gt66es-30267 (8:24:27) [prop] Every closed immersion is finite; `A/J` is finite over `A`. -/
theorem prop_30267 (f : X ⟶ Y) [IsClosedImmersion f] {A' : Type*} [CommRing A'] (J : Ideal A') :
    IsFinite f ∧ Module.Finite A' (A' ⧸ J) :=
  ⟨inferInstance, inferInstance⟩

/-- Oqhr-Gt66es-30399 (8:26:39) [thm] Lying over: if `A ⊂ B` is integral, every prime of `A` is
induced by a prime of `B`. -/
theorem thm_30399 {A' B' : Type*} [CommRing A'] [CommRing B'] [Algebra A' B']
    [Algebra.IsIntegral A' B'] (hinj : Function.Injective (algebraMap A' B')) (p : Ideal A')
    [p.IsPrime] : ∃ Q : Ideal B', Q.IsPrime ∧ Q.comap (algebraMap A' B') = p := by
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal B') (by
    rw [Ideal.under_def, Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  exact ⟨Q, hQ, hQp⟩

/-- Oqhr-Gt66es-30462 (8:27:42) [prop] For `k'/k` algebraic, the projection `X_{k'} → X` is
closed (it is integral, hence universally closed). -/
theorem prop_30462 {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [Algebra.IsAlgebraic k k']
    (f : X ⟶ Spec (.of k)) :
    IsClosedMap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) := by
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := by
    rw [IsIntegralHom.SpecMap_iff]
    exact (Algebra.isIntegral_iff (R := k) (A := k')).1 inferInstance
  exact (pullback.fst f _).isClosedMap

end FiniteMorphisms

end

end Buffalo.AG.Part07
