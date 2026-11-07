import Buffalo.AG.Part08a

/-!
# Buffalo, algebraic geometry, part 08 (b): 9 July 1973, tape 2

The entries of `docs/buffalo-ag/index.tex` lines 1099–1138 (video `vuys5SNs2eQ`, 0:48:33–2:26:00):
descent of properties of morphisms, of modules and of topological properties along faithfully
flat morphisms.

Conventions as in `Part08a`: `g : S' ⟶ S` is the base change, `f : X ⟶ S`,
`f' = pullback.snd f g : X ×_S S' ⟶ S'` and `g' = pullback.fst f g`. "Faithfully flat
quasi-compact" is mathlib's `@Surjective ⊓ @Flat ⊓ @QuasiCompact`, along which mathlib proves
fpqc descent of many properties (`Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`).
-/

open CategoryTheory Limits TensorProduct Topology PrimeSpectrum AlgebraicGeometry

universe u v

namespace Buffalo.AG.Part08

noncomputable section

attribute [local instance] surjective_descendsAlong quasiCompact_descendsAlong

/-! ### Descent of properties along faithfully flat morphisms -/

section Properties

variable {S S' X : Scheme.{u}} (g : S' ⟶ S) (f : X ⟶ S)

/-- The fpqc hypothesis on `g`. -/
theorem fpqc_hyp [Surjective g] [Flat g] [QuasiCompact g] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) g :=
  ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- vuys5SNs2eQ-2913 (0:48:33) [prop] `f` is quasi-separated iff its diagonal is quasi-compact;
coherent means quasi-compact and quasi-separated (mathlib:
`quasiSeparated_eq_diagonal_is_quasiCompact`). -/
theorem prop_2913 :
    @QuasiSeparated.{u} = MorphismProperty.diagonal @QuasiCompact :=
  quasiSeparated_eq_diagonal_is_quasiCompact

/-- vuys5SNs2eQ-3040 (0:50:40) [prop] If `g` is faithfully flat and quasi-compact, `f` is locally of
finite type (resp. finite presentation) iff `f'` is (mathlib: `LocalFlatDescent`). -/
theorem prop_3040 [Surjective g] [Flat g] [QuasiCompact g] :
    (LocallyOfFiniteType (pullback.snd f g) ↔ LocallyOfFiniteType f) ∧
      (LocallyOfFinitePresentation (pullback.snd f g) ↔ LocallyOfFinitePresentation f) :=
  ⟨MorphismProperty.pullback_snd_iff (fpqc_hyp g), MorphismProperty.pullback_snd_iff (fpqc_hyp g)⟩

/-- vuys5SNs2eQ-3104 (0:51:44) [prop] Finite type = locally of finite type + quasi-compact, finite
presentation = locally of finite presentation + coherent; both descend along `g` faithfully flat
quasi-compact (`prop_3040`, `prop_2750`). -/
theorem prop_3104 [Surjective g] [Flat g] [QuasiCompact g] :
    ((LocallyOfFiniteType (pullback.snd f g) ∧ QuasiCompact (pullback.snd f g)) ↔
        (LocallyOfFiniteType f ∧ QuasiCompact f)) ∧
      ((LocallyOfFinitePresentation (pullback.snd f g) ∧ QuasiCompact (pullback.snd f g) ∧
          QuasiSeparated (pullback.snd f g)) ↔
        (LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f)) :=
  ⟨and_congr (prop_3040 g f).1 (prop_2750 g f).1,
    and_congr (prop_3040 g f).2 (and_congr (prop_2750 g f).1 (prop_2750 g f).2.1)⟩

/-- vuys5SNs2eQ-3624 (1:00:24) [prop] `f` is flat iff `f'` is flat, for `Y' → Y` faithfully flat.
Proved here for `g` faithfully flat and quasi-compact, by mathlib's
`HasRingHomProperty.descendsAlong_flat` from flat descent for rings. -/
theorem prop_3624 [Surjective g] [Flat g] [QuasiCompact g] :
    Flat (pullback.snd f g) ↔ Flat f := by
  have : MorphismProperty.DescendsAlong @Flat.{u}
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
    refine HasRingHomProperty.descendsAlong_flat (Q := RingHom.Flat) ?_
    refine .mk _ RingHom.Flat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
    rw [RingHom.flat_algebraMap_iff] at h' ⊢
    rw [RingHom.faithfullyFlat_algebraMap_iff] at h
    exact Module.Flat.of_flat_tensorProduct R T S
  exact MorphismProperty.pullback_snd_iff (fpqc_hyp g)

/-- vuys5SNs2eQ-5811 (1:36:51) [prop] For `g` faithfully flat quasi-compact, `f` is separated
(resp. proper) iff `f'` is. Proved: universal closedness descends (mathlib
`descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`), and finite type
(`prop_3104`). -/
theorem prop_5811 [Surjective g] [Flat g] [QuasiCompact g] :
    UniversallyClosed (pullback.snd f g) ↔ UniversallyClosed f :=
  MorphismProperty.pullback_snd_iff (fpqc_hyp g)

/-- vuys5SNs2eQ-5892 (1:38:12) [prop] For `g` faithfully flat quasi-compact, `f` is an isomorphism
iff `f'` is (mathlib: `descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`). -/
theorem prop_5892 [Surjective g] [Flat g] [QuasiCompact g] :
    IsIso (pullback.snd f g) ↔ IsIso f :=
  MorphismProperty.pullback_snd_iff (P := MorphismProperty.isomorphisms Scheme.{u}) (fpqc_hyp g)

/-- vuys5SNs2eQ-6022 (1:40:22) [prop] Base change along `g` faithfully flat quasi-compact is
faithful and conservative (mathlib: the `(Over.pullback g).Faithful` instance and `prop_5892`). -/
theorem prop_6022 [Surjective g] [Flat g] [QuasiCompact g] :
    (Over.pullback g).Faithful ∧ (IsIso (pullback.snd f g) → IsIso f) :=
  ⟨inferInstance, (prop_5892 g f).1⟩

/-- vuys5SNs2eQ-6088 (1:41:28) [prop] `f` is a monomorphism iff `Δ_f` is an isomorphism (mathlib:
`pullback.isIso_diagonal_iff`); hence `f` is a monomorphism iff `f'` is, for `g` faithfully flat
quasi-compact (descent of isomorphisms applied to the diagonal). -/
theorem prop_6088 [Surjective g] [Flat g] [QuasiCompact g] :
    (IsIso (pullback.diagonal f) ↔ Mono f) ∧ (Mono (pullback.snd f g) ↔ Mono f) := by
  refine ⟨pullback.isIso_diagonal_iff f, ?_⟩
  have : (@Surjective ⊓ @Flat : MorphismProperty Scheme.{u}).IsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}).IsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have : (MorphismProperty.diagonal (MorphismProperty.isomorphisms Scheme.{u})).DescendsAlong
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
    MorphismProperty.instDescendsAlongDiagonalOfRespectsIsoOfIsStableUnderBaseChange _ _
  have : (MorphismProperty.diagonal
      (MorphismProperty.isomorphisms Scheme.{u})).IsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.diagonal
  have h := MorphismProperty.pullback_snd_iff
    (P := MorphismProperty.diagonal (MorphismProperty.isomorphisms Scheme.{u})) (f := f)
    (fpqc_hyp g)
  rwa [MorphismProperty.diagonal_isomorphisms] at h

end Properties

/-! ### Descent of properties of modules and algebras -/

section Modules

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']

/-- vuys5SNs2eQ-3297 (0:54:57) [prop] If `A → A'` is faithfully flat, `B` is finitely generated
(resp. finitely presented) over `A` iff `A' ⊗_A B` is over `A'` (mathlib:
`Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat` and its `FinitePresentation`
variant). -/
theorem prop_3297 [Module.FaithfullyFlat A A'] (B : Type u) [CommRing B] [Algebra A B] :
    (Algebra.FiniteType A' (A' ⊗[A] B) ↔ Algebra.FiniteType A B) ∧
      (Algebra.FinitePresentation A' (A' ⊗[A] B) ↔ Algebra.FinitePresentation A B) :=
  ⟨⟨fun _ => .of_finiteType_tensorProduct_of_faithfullyFlat A', fun _ => inferInstance⟩,
    ⟨fun _ => .of_finitePresentation_tensorProduct_of_faithfullyFlat A', fun _ => inferInstance⟩⟩

/-- vuys5SNs2eQ-3491 (0:58:11) [prop] A quasi-coherent module is of finite type iff `F'` is. Affine
case (mathlib: `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`). -/
theorem prop_3491 [Module.FaithfullyFlat A A'] (M : Type u) [AddCommGroup M] [Module A M] :
    Module.Finite A' (A' ⊗[A] M) ↔ Module.Finite A M :=
  ⟨fun _ => .of_finite_tensorProduct_of_faithfullyFlat A', fun _ => inferInstance⟩

/-- vuys5SNs2eQ-3687 (1:01:27) [prop] If `A → A'` is faithfully flat, `M` is flat iff `A' ⊗_A M`
is flat over `A'` (mathlib: `Module.Flat.iff_flat_tensorProduct`); likewise for faithful
flatness. -/
theorem prop_3687 [Module.FaithfullyFlat A A'] (M : Type u) [AddCommGroup M] [Module A M] :
    (Module.Flat A' (A' ⊗[A] M) ↔ Module.Flat A M) ∧
      (Module.FaithfullyFlat A' (A' ⊗[A] M) ↔ Module.FaithfullyFlat A M) := by
  refine ⟨Module.Flat.iff_flat_tensorProduct A M A', fun h => ?_, fun _ => inferInstance⟩
  have : Module.Flat A M := (Module.Flat.iff_flat_tensorProduct A M A').1 inferInstance
  refine (Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality A M).2
    ⟨this, fun N _ _ hN => ?_⟩
  -- `A' ⊗ (M ⊗ N) ≃ (A' ⊗ M) ⊗_{A'} (A' ⊗ N)`
  have h1 : Subsingleton (A' ⊗[A] (M ⊗[A] N)) := inferInstance
  have e : (A' ⊗[A] M) ⊗[A'] (A' ⊗[A] N) ≃ₗ[A'] A' ⊗[A] (M ⊗[A] N) :=
    (TensorProduct.AlgebraTensorModule.distribBaseChange A A' M N).symm
  have h2 : Subsingleton ((A' ⊗[A] M) ⊗[A'] (A' ⊗[A] N)) := e.toEquiv.subsingleton
  have h3 : Subsingleton (ULift.{u} (A' ⊗[A] N)) := by
    have := Module.FaithfullyFlat.lTensor_reflects_triviality A' (A' ⊗[A] M) (A' ⊗[A] N)
    exact Equiv.ulift.subsingleton
  have h4 : Subsingleton (A' ⊗[A] N) := Equiv.ulift.symm.subsingleton
  exact Module.FaithfullyFlat.lTensor_reflects_triviality A A' N

/-- vuys5SNs2eQ-3752 (1:02:32) [prop] A module is locally free of finite type (finitely generated
projective) iff it is of finite presentation and flat (mathlib:
`Module.Flat.projective_of_finitePresentation`, `Module.finitePresentation_of_projective`). -/
theorem prop_3752 (M : Type u) [AddCommGroup M] [Module A M] :
    (Module.Projective A M ∧ Module.Finite A M) ↔
      (Module.FinitePresentation A M ∧ Module.Flat A M) := by
  constructor
  · rintro ⟨_, _⟩
    exact ⟨Module.finitePresentation_of_projective A M, inferInstance⟩
  · rintro ⟨_, _⟩
    exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩

/-- vuys5SNs2eQ-3556 (0:59:16) [prop] `F` locally free of finite type iff `F'` is. Affine case for a
finitely presented `M`: `M` is projective iff `A' ⊗_A M` is (flat descent and `prop_3752`). -/
theorem prop_3556 [Module.FaithfullyFlat A A'] (M : Type u) [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] :
    Module.Projective A' (A' ⊗[A] M) ↔ Module.Projective A M := by
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  have : Module.Flat A M := (Module.Flat.iff_flat_tensorProduct A M A').1 inferInstance
  exact Module.Flat.projective_of_finitePresentation

/-- vuys5SNs2eQ-6217 (1:43:37) [prop] If `g` is faithfully flat, `M ↦ M'` is exact, faithful and
conservative, and `Hom(M, N) → Hom(M', N')` is injective. Affine case (mathlib:
`Module.FaithfullyFlat.lTensor_exact_iff_exact`, `lTensor_bijective_iff_bijective`,
`zero_iff_lTensor_zero`). -/
theorem prop_6217 [Module.FaithfullyFlat A A'] {M N P : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P] (w : M →ₗ[A] N)
    (w' : N →ₗ[A] P) :
    (Function.Exact (w.lTensor A') (w'.lTensor A') ↔ Function.Exact w w') ∧
      (Function.Bijective (w.lTensor A') ↔ Function.Bijective w) ∧
      ∀ w₁ w₂ : M →ₗ[A] N, w₁.lTensor A' = w₂.lTensor A' → w₁ = w₂ := by
  refine ⟨Module.FaithfullyFlat.lTensor_exact_iff_exact A A' w w',
    Module.FaithfullyFlat.lTensor_bijective_iff_bijective A A' w, fun w₁ w₂ h => ?_⟩
  rw [← sub_eq_zero, Module.FaithfullyFlat.zero_iff_lTensor_zero A A', LinearMap.lTensor_sub, h]
  exact sub_self (LinearMap.lTensor A' w₂)

/-- vuys5SNs2eQ-6408 (1:46:48) [prop] `Hom(M,N) → Hom(M',N') ⇉ Hom(M'',N'')` is a complex, and the
first arrow is injective if `g` is faithfully flat. Proved: the injectivity (`prop_6217`). -/
theorem prop_6408 [Module.FaithfullyFlat A A'] {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] :
    Function.Injective (fun w : M →ₗ[A] N => w.lTensor A') :=
  fun w₁ w₂ h => (prop_6217 w₁ (LinearMap.id : N →ₗ[A] N)).2.2 w₁ w₂ h

omit [Algebra A A'] in
/-- vuys5SNs2eQ-7642 (2:07:22) [prop] A faithfully flat morphism is of descent of rank `0`: the
functor to modules with gluing data is faithful. Affine case: `M ↦ A' ⊗_A M` is faithful
(`prop_6408`), and reflects isomorphisms (mathlib:
`ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat`). -/
theorem prop_7642 (φ : A →+* A') (hφ : φ.FaithfullyFlat) :
    (ModuleCat.extendScalars.{u, u, u} φ).ReflectsIsomorphisms :=
  ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat hφ

omit [Algebra A A'] in
/-- vuys5SNs2eQ-6533 (1:48:53) [thm] A faithfully flat quasi-compact morphism is of effective descent
for quasi-coherent modules. Affine case, in Beck's form: extension of scalars along a faithfully
flat ring map is comonadic (mathlib: `comonadicExtendScalars`); comonad coalgebras are the descent
data. -/
@[instance_reducible]
def thm_6533 (φ : A →+* A') (hφ : φ.FaithfullyFlat) :
    ComonadicLeftAdjoint (ModuleCat.extendScalars.{u, u, u} φ) :=
  comonadicExtendScalars hφ

/-- vuys5SNs2eQ-6663 (1:51:03) [def] A gluing datum on an `A'`-module `M'` (for `A → A'`, with
`A'' = A' ⊗_A A'` and `p₁, p₂ : A' → A''`) is an isomorphism `c : p₁^* M' ≅ p₂^* M'`. -/
structure GluingDatum (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A'] where
  /-- The module on `S'`. -/
  M : ModuleCat.{u} A'
  /-- The gluing isomorphism `p₁^* M' ≅ p₂^* M'`. -/
  c : (ModuleCat.extendScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A') (B := A'))).obj M ≅
      (ModuleCat.extendScalars.{u, u, u}
        (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := A')).toRingHom).obj M

/-- vuys5SNs2eQ-7841 (2:10:41) [def] A descent datum is a gluing datum satisfying the cocycle
condition: mathlib's `Pseudofunctor.DescentData` (for a pseudofunctor `F` and a family of
morphisms). -/
abbrev def_7841 {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {ι : Type u} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) : Type _ :=
  F.DescentData f

/-- vuys5SNs2eQ-6470 (1:47:50) [def] `g` is a descent morphism (rank `1`) if the sequence of `Hom`
is exact, i.e. `M ↦ (M', can)` is fully faithful: mathlib's `Pseudofunctor.IsPrestackFor`. -/
abbrev def_6470 {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {S : C} (R : Presieve S) : Prop :=
  F.IsPrestackFor R

/-- vuys5SNs2eQ-7906 (2:11:46) [def] `g` is of effective descent (rank `2`) if `Mod(S)` is
equivalent to modules on `S'` with descent data: mathlib's `Pseudofunctor.IsStackFor`. -/
abbrev def_7906 {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    {S : C} (R : Presieve S) : Prop :=
  F.IsStackFor R

/-- vuys5SNs2eQ-8840 (2:27:20) [prop] If a descent (resp. effective descent) family factors through
`S' → S`, then `S' → S` is of descent (resp. effective descent). Abstract form for a prestack
(mathlib: `Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le`). -/
theorem prop_8840 {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u})
    (J : GrothendieckTopology C) [F.IsPrestack J] {ι ι' : Type u} {S : C} {X : ι → C}
    {f : ∀ i, X i ⟶ S} {X' : ι' → C} {f' : ∀ j, X' j ⟶ S}
    (h₁ : Sieve.ofArrows _ f' ∈ J _) (h₂ : Sieve.ofArrows _ f' ≤ Sieve.ofArrows _ f)
    [(F.toDescentData f').IsEquivalence] : (F.toDescentData f).IsEquivalence :=
  Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le F h₁ h₂

end Modules

/-! ### Topological descent -/

section Topological

/-- vuys5SNs2eQ-3885 (1:04:45) [prop] For continuous `g` one always has
`closure(g⁻¹ Z) ⊂ g⁻¹(closure Z)`; equality for all `Z` characterizes open maps. -/
theorem prop_3885 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {g : X → Y}
    (hg : Continuous g) :
    (∀ Z, closure (g ⁻¹' Z) ⊆ g ⁻¹' closure Z) ∧
      (IsOpenMap g ↔ ∀ Z, g ⁻¹' closure Z = closure (g ⁻¹' Z)) := by
  refine ⟨hg.closure_preimage_subset, fun h Z => h.preimage_closure_eq_closure_preimage hg Z,
    fun h U hU => ?_⟩
  have hc := h (g '' U)ᶜ
  have : g ⁻¹' closure (g '' U)ᶜ ⊆ Uᶜ := by
    rw [hc]
    exact closure_minimal (fun x hx hxU => hx ⟨x, hxU, rfl⟩) hU.isClosed_compl
  have e : g '' U = (closure (g '' U)ᶜ)ᶜ := by
    refine subset_antisymm ?_ (fun y hy => ?_)
    · rintro _ ⟨x, hx, rfl⟩ hcl
      exact this hcl hx
    · by_contra hyU
      exact hy (subset_closure hyU)
  rw [e]
  exact isClosed_closure.isOpen_compl

/-- vuys5SNs2eQ-3950 (1:05:50) [cex] The inclusion of the generic point of an integral scheme is
flat but in general not open: `Spec ℚ → Spec ℤ` is flat, with image `{(0)}` not open. -/
theorem cex_3950 :
    Module.Flat ℤ ℚ ∧ ¬ IsOpen (Set.range (comap (algebraMap ℤ ℚ))) := by
  refine ⟨IsLocalization.flat ℚ (nonZeroDivisors ℤ), fun hopen => ?_⟩
  have hbot : (⊥ : Ideal ℤ).IsPrime := Ideal.isPrime_bot
  have hmem : (⟨⊥, hbot⟩ : PrimeSpectrum ℤ) ∈ Set.range (comap (algebraMap ℤ ℚ)) := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    ext1
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective ℤ ℚ)
  obtain ⟨_, ⟨n, rfl⟩, hn, hsub⟩ :=
    (isTopologicalBasis_basic_opens (R := ℤ)).isOpen_iff.1 hopen _ hmem
  have hn0 : n ≠ 0 := by simpa [mem_basicOpen] using hn
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (n := n.natAbs + 1) (by omega)
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  have hmemD : (⟨_, hpI⟩ : PrimeSpectrum ℤ) ∈ basicOpen n := by
    rw [mem_basicOpen]
    intro h
    rw [Ideal.mem_span_singleton] at h
    have h1 : (p : ℤ) ∣ (n.natAbs : ℤ) := (Int.dvd_natAbs).2 h
    have h2 : (p : ℤ) ∣ ((n.natAbs + 1 : ℕ) : ℤ) := by exact_mod_cast hpn
    have : (p : ℤ) ∣ 1 := by
      have := Int.dvd_sub h2 h1
      simpa using this
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
  obtain ⟨q, hq⟩ := hsub hmemD
  have hq' : q.asIdeal.comap (algebraMap ℤ ℚ) = Ideal.span {(p : ℤ)} := congrArg (·.asIdeal) hq
  have hq0 : q.asIdeal = ⊥ := by
    rcases (Ideal.isPrime_iff.1 q.isPrime) with ⟨hne, -⟩
    refine (eq_bot_or_eq_top q.asIdeal).resolve_right hne
  rw [hq0, Ideal.comap_bot_of_injective _ (IsFractionRing.injective ℤ ℚ)] at hq'
  have : (p : ℤ) ∈ (⊥ : Ideal ℤ) := hq' ▸ Ideal.mem_span_singleton_self _
  exact hp.ne_zero (by exact_mod_cast (Submodule.mem_bot ℤ).1 this)

variable {S S' X : Scheme.{u}} (g : S' ⟶ S) (f : X ⟶ S)

/-- vuys5SNs2eQ-5252 (1:27:32) [prop] A faithfully flat quasi-compact morphism is universally
submersive (mathlib: `Flat.isQuotientMap_of_surjective`, applied to every base change). -/
theorem prop_5252 [Surjective g] [Flat g] [QuasiCompact g] :
    IsQuotientMap g ∧ IsQuotientMap (pullback.fst f g) :=
  ⟨Flat.isQuotientMap_of_surjective g, Flat.isQuotientMap_of_surjective _⟩

/-- vuys5SNs2eQ-4795 (1:19:55) [prop] If `g` is flat, quasi-compact and surjective, `g` is
submersive (mathlib: `Flat.isQuotientMap_of_surjective`); the quotient topology on `g(S')` for
non-surjective `g` is not stated. -/
theorem prop_4795 [Surjective g] [Flat g] [QuasiCompact g] : IsQuotientMap g :=
  Flat.isQuotientMap_of_surjective g

/-- vuys5SNs2eQ-5590 (1:33:10) [prop] If `g` is surjective, `f` is surjective iff `f'` is, and `f'`
injective implies `f` injective. -/
theorem prop_5590 [Surjective g] :
    (Surjective (pullback.snd f g) ↔ Surjective f) ∧
      (Function.Injective (pullback.snd f g) → Function.Injective f) := by
  refine ⟨(prop_2620 g f).1, fun h x₁ x₂ hx => ?_⟩
  obtain ⟨s, hs⟩ := g.surjective (f x₁)
  obtain ⟨p₁, hp₁, hq₁⟩ := Scheme.Pullback.exists_preimage_pullback x₁ s hs.symm
  obtain ⟨p₂, hp₂, hq₂⟩ := Scheme.Pullback.exists_preimage_pullback x₂ s (hx ▸ hs.symm)
  rw [← hp₁, ← hp₂, h (hq₁.trans hq₂.symm)]

/-- vuys5SNs2eQ-5323 (1:28:43) [prop] For `g` faithfully flat quasi-compact: if `f'` is open (resp.
closed, generalizing, a homeomorphism), so is `f`; likewise for the universal properties (mathlib
for these: `descendsAlong_universallyOpen_…`, `descendsAlong_universallyClosed_…`). Generalizing
needs only `g` flat and surjective. -/
theorem prop_5323 [Surjective g] [Flat g] [QuasiCompact g] :
    (IsOpenMap (pullback.snd f g) → IsOpenMap f) ∧
      (IsClosedMap (pullback.snd f g) → IsClosedMap f) ∧
      (GeneralizingMap (pullback.snd f g) → GeneralizingMap f) ∧
      (IsHomeomorph (pullback.snd f g) → IsHomeomorph f) ∧
      (UniversallyOpen (pullback.snd f g) → UniversallyOpen f) ∧
      (UniversallyClosed (pullback.snd f g) → UniversallyClosed f) := by
  have hq := Flat.isQuotientMap_of_surjective g
  have H := Scheme.image_preimage_eq_of_isPullback (IsPullback.of_hasPullback f g)
  have hopen : IsOpenMap (pullback.snd f g) → IsOpenMap f := fun h U hU => by
    rw [← hq.isOpen_preimage, ← H]
    exact h _ (hU.preimage (pullback.fst f g).continuous)
  have hclosed : IsClosedMap (pullback.snd f g) → IsClosedMap f := fun h U hU => by
    rw [← hq.isClosed_preimage, ← H]
    exact h _ (hU.preimage (pullback.fst f g).continuous)
  refine ⟨hopen, hclosed, fun h x y hxy => ?_, fun h => ?_,
    fun h => MorphismProperty.of_pullback_snd_of_descendsAlong (fpqc_hyp g) h,
    fun h => MorphismProperty.of_pullback_snd_of_descendsAlong (fpqc_hyp g) h⟩
  · obtain ⟨s, hs⟩ := g.surjective (f x)
    obtain ⟨p, hp, hp'⟩ := Scheme.Pullback.exists_preimage_pullback x s hs.symm
    obtain ⟨t, ht, hgt⟩ := Flat.generalizingMap g (hp' ▸ hs ▸ hxy)
    obtain ⟨w, hw, hw'⟩ := h ht
    refine ⟨pullback.fst f g w, hp ▸ hw.map (pullback.fst f g).continuous, ?_⟩
    rw [← hgt, ← hw', ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  · have hsurj := (prop_5590 g f).1.1 ⟨h.bijective.2⟩
    exact ⟨f.continuous, hopen h.isOpenMap, (prop_5590 g f).2 h.bijective.1, hsurj.surj⟩

end Topological

end

end Buffalo.AG.Part08
