import Buffalo.AG.Part03a

/-!
# Buffalo, algebraic geometry, part 03 (b): 11 June 1973, recorded on `_lTf_L0yvrU`

The entries of `docs/buffalo-ag/index.tex` lines 403–439 (video `_lTf_L0yvrU`, 3:45:53–4:59:18,
recorded on the groups course's video but belonging to the algebraic geometry course): sheaves on a
spectrum, the localizations `M_f` and the sheaf `M~`, flat and faithfully flat modules.

Conventions. `M_f` is mathlib's `LocalizedModule (Submonoid.powers f) M` and `A_f` is
`Localization.Away f`; the sheaf `M~` is `AlgebraicGeometry.tilde M`, a sheaf of modules over the
structure sheaf of `Spec A`.
-/

open CategoryTheory TensorProduct Topology PrimeSpectrum

universe u

namespace Buffalo.AG.Part03

noncomputable section

/-! ### Sheaves on a spectrum -/

section Sheaves

/-- _lTf_L0yvrU-13553 (3:45:53) [prop] `Spec A` with its structure sheaf is a locally ringed space
(mathlib: `AlgebraicGeometry.Spec.locallyRingedSpaceObj`). -/
def prop_13553 (R : CommRingCat.{u}) : AlgebraicGeometry.LocallyRingedSpace.{u} :=
  AlgebraicGeometry.Spec.locallyRingedSpaceObj R

/-- _lTf_L0yvrU-13617 (3:46:57) [prop] `Spec` turns tensor products into fibre products:
`Spec(A ⊗_k B) = Spec A ×_{Spec k} Spec B` (mathlib, in schemes: `AlgebraicGeometry.pullbackSpecIso`;
the fibre product of schemes is also the one of locally ringed spaces). -/
def prop_13617 (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] :
    Limits.pullback (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅
      AlgebraicGeometry.Spec (CommRingCat.of (S ⊗[R] T)) :=
  AlgebraicGeometry.pullbackSpecIso R S T

/-- _lTf_L0yvrU-13646 (3:47:26) [prop] A sheaf on `Spec A` is determined by its restriction to the
basic open sets: morphisms to a sheaf are the morphisms of the restrictions to the `X_f` (mathlib:
`TopCat.Sheaf.restrictHomEquivHom`, for any basis). -/
def prop_13646 {C : Type*} [Category C] (A : CommRingCat.{u})
    (F : (AlgebraicGeometry.Spec.topObj A).Presheaf C) (G : (AlgebraicGeometry.Spec.topObj A).Sheaf C) :
    ((inducedFunctor (fun f : A =>
          (basicOpen f : TopologicalSpace.Opens (AlgebraicGeometry.Spec.topObj A)))).op ⋙ F ⟶
        (inducedFunctor (fun f : A =>
          (basicOpen f : TopologicalSpace.Opens (AlgebraicGeometry.Spec.topObj A)))).op ⋙ G.1) ≃ (F ⟶ G.1) :=
  TopCat.Sheaf.restrictHomEquivHom F G isBasis_basic_opens

variable {A : Type*} [CommRing A]

/-- _lTf_L0yvrU-13976 (3:52:56) [prop] `X_f ⊂ X_g` iff `f^n = gh` for some `n ≥ 0` and `h ∈ A`;
the relation is transitive. -/
theorem prop_13976 (f g : A) :
    (basicOpen f ≤ basicOpen g ↔ ∃ (n : ℕ) (h : A), f ^ n = g * h) ∧
      ∀ h : A, basicOpen f ≤ basicOpen g → basicOpen g ≤ basicOpen h → basicOpen f ≤ basicOpen h := by
  refine ⟨?_, fun h h1 h2 => h1.trans h2⟩
  rw [basicOpen_le_basicOpen_iff]
  simp only [Ideal.mem_radical_iff, Ideal.mem_span_singleton', eq_comm (b := f ^ _)]
  exact exists_congr fun n => ⟨fun ⟨h, e⟩ => ⟨h, e.trans (mul_comm _ _)⟩,
    fun ⟨h, e⟩ => ⟨h, e.trans (mul_comm _ _)⟩⟩

/-- _lTf_L0yvrU-14363 (3:59:23) [prop] `X_f = ⋃ X_{f_i}` iff `f_i^{n_i} ∈ fA` for all `i` and
`f^n = ∑ g_i f_i` for some `n` and `g_i` almost all zero. -/
theorem prop_14363 {ι : Type*} (f : A) (fi : ι → A) :
    basicOpen f = ⨆ i, basicOpen (fi i) ↔
      (∀ i, ∃ n : ℕ, fi i ^ n ∈ Ideal.span {f}) ∧
        ∃ (n : ℕ) (g : ι →₀ A), f ^ n = g.sum fun i a => a * fi i := by
  have h1 : basicOpen f ≤ ⨆ i, basicOpen (fi i) ↔
      ∃ (n : ℕ) (g : ι →₀ A), f ^ n = g.sum fun i a => a * fi i := by
    rw [← SetLike.coe_subset_coe, TopologicalSpace.Opens.coe_iSup]
    simp only [basicOpen_eq_zeroLocus_compl, ← Set.compl_iInter, Set.compl_subset_compl,
      ← zeroLocus_iUnion, Set.iUnion_singleton_eq_range]
    rw [← zeroLocus_span (Set.range fi), ← zeroLocus_span {f}, zeroLocus_subset_zeroLocus_iff,
      Ideal.span_singleton_le_iff_mem, Ideal.mem_radical_iff]
    refine exists_congr fun n => ?_
    rw [Ideal.span, Finsupp.mem_span_range_iff_exists_finsupp]
    simp only [smul_eq_mul, eq_comm]
  have h2 : (∀ i, basicOpen (fi i) ≤ basicOpen f) ↔ ∀ i, ∃ n : ℕ, fi i ^ n ∈ Ideal.span {f} := by
    simp only [basicOpen_le_basicOpen_iff, Ideal.mem_radical_iff]
  rw [← h1, ← h2, ← iSup_le_iff, le_antisymm_iff, and_comm]

end Sheaves

/-! ### The sheaf associated to a module -/

section Tilde

variable {A : Type*} [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]

/-- The element `f^n` of the multiplicative set `{f^n}`. -/
def pw (f : A) (n : ℕ) : Submonoid.powers f := ⟨f ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers f) n⟩

@[simp] theorem coe_pw (f : A) (n : ℕ) : (pw f n : A) = f ^ n := rfl

theorem pw_add (f : A) (n m : ℕ) : pw f (n + m) = pw f n * pw f m :=
  Subtype.ext (pow_add f n m)

/-- _lTf_L0yvrU-14427 (4:00:27) [def] To an `A`-module `M` one associates a sheaf `M~` on
`Spec A`; for `M = A` it is the structure sheaf (mathlib: `AlgebraicGeometry.tilde`,
`AlgebraicGeometry.tildeSelf`). -/
def def_14427 {R : CommRingCat.{u}} (N : ModuleCat.{u} R) : (AlgebraicGeometry.Spec R).Modules :=
  AlgebraicGeometry.tilde N

example (R : CommRingCat.{u}) :
    AlgebraicGeometry.tilde (ModuleCat.of R R) ≅ SheafOfModules.unit.{u} _ :=
  AlgebraicGeometry.tildeSelf

/-- _lTf_L0yvrU-14490 (4:01:30) [def] `M~(X_f) = M_f`, the localization of `M` at `f` (mathlib: the
sections of `tilde M` over `D(f)` are a localization of `M` at the powers of `f`). -/
example {R : CommRingCat.{u}} (N : ModuleCat.{u} R) (f : R) :
    IsLocalizedModule.Away f (AlgebraicGeometry.tilde.toOpen N (basicOpen f)).hom :=
  inferInstance

/-- _lTf_L0yvrU-14557 (4:02:37) [prop] In `M_f`, multiplication by `f` is bijective, and
`M → M_f` is the canonical map. -/
theorem prop_14557 (f : A) :
    Function.Bijective (fun x : LocalizedModule (Submonoid.powers f) M => f • x) ∧
      ∀ m : M, LocalizedModule.mkLinearMap (Submonoid.powers f) M m = LocalizedModule.mk m 1 := by
  refine ⟨?_, fun m => rfl⟩
  have := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (pw f 1)
  rw [Module.End.isUnit_iff] at this
  convert this using 1
  funext x
  simp [Module.algebraMap_end_apply]

/-- _lTf_L0yvrU-14682 (4:04:42) [prop] Universal property: every `M → N`, `f` bijective on `N`,
factors uniquely through `M_f` (mathlib: `IsLocalizedModule.lift`, `IsLocalizedModule.lift_comp`,
`IsLocalizedModule.lift_unique`); hence `M ↦ M_f` is a functor (`LocalizedModule.map`). -/
theorem prop_14682 (f : A) {N : Type*} [AddCommGroup N] [Module A N] (g : M →ₗ[A] N)
    (hg : ∀ x : Submonoid.powers f, IsUnit (algebraMap A (Module.End A N) x)) :
    ∃! l : LocalizedModule (Submonoid.powers f) M →ₗ[A] N,
      l ∘ₗ LocalizedModule.mkLinearMap (Submonoid.powers f) M = g :=
  ⟨IsLocalizedModule.lift _ _ g hg, IsLocalizedModule.lift_comp _ _ g hg,
    fun l hl => (IsLocalizedModule.lift_unique _ _ g hg l hl).symm⟩

/-- _lTf_L0yvrU-14941 (4:09:01) [prop] `M_f` is the set of `x/f^n`, with `x/f^n = x'/f^{n'}` iff
`f^m (f^{n'} x - f^n x') = 0` for some `m`. -/
theorem prop_14941 (f : A) (x x' : M) (n n' : ℕ) :
    LocalizedModule.mk x (pw f n) =
        LocalizedModule.mk x' (pw f n') ↔
      ∃ m : ℕ, f ^ m • (f ^ n' • x - f ^ n • x') = 0 := by
  rw [LocalizedModule.mk_eq]
  constructor
  · rintro ⟨⟨_, hm⟩, h⟩
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hm
    exact ⟨m, by rw [smul_sub, sub_eq_zero]; exact h⟩
  · rintro ⟨m, h⟩
    exact ⟨pw f m, by rw [smul_sub, sub_eq_zero] at h; exact h⟩

/-- _lTf_L0yvrU-15076 (4:11:16) [prop] `A_f` is a ring, `A → A_f` a ring homomorphism, and
`x/f^n · y/f^{n'} = xy/f^{n+n'}` (mathlib: `Localization.mk_mul`). -/
theorem prop_15076 (f x y : A) (n n' : ℕ) :
    Localization.mk x (pw f n) * Localization.mk y (pw f n') =
      Localization.mk (x * y) (pw f (n + n')) := by
  rw [Localization.mk_mul, pw_add]

/-- _lTf_L0yvrU-15142 (4:12:22) [prop] `M_f` is an `A_f`-module via
`λ/f^n · x/f^m = λx/f^{n+m}` (mathlib: `LocalizedModule.mk_smul_mk`). -/
theorem prop_15142 (f c : A) (x : M) (n m : ℕ) :
    Localization.mk c (pw f n) •
        LocalizedModule.mk x (pw f m) =
      LocalizedModule.mk (c • x) (pw f (n + m)) := by
  rw [LocalizedModule.mk_smul_mk, pw_add]

/-- _lTf_L0yvrU-15206 (4:13:26) [prop] Every homomorphism from `A` to a ring `R` (even
noncommutative) sending `f` to a unit factors uniquely through `A_f` (existence: mathlib's
`OreLocalization.universalHom`, `A_f` being an Ore localization). -/
theorem prop_15206 (f : A) {R : Type*} [Ring R] (g : A →+* R) (hg : IsUnit (g f)) :
    ∃! h : Localization.Away f →+* R, h.comp (algebraMap A _) = g := by
  have hS : ∀ s : Submonoid.powers f, IsUnit (((g : A →* R).comp (Submonoid.powers f).subtype) s) :=
    fun s => by
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
      change IsUnit (g s)
      rw [← hk, map_pow]; exact hg.pow k
  let fS : Submonoid.powers f →* Rˣ := IsUnit.liftRight _ hS
  have hfS : ∀ s : Submonoid.powers f, g s = fS s := fun s => (IsUnit.coe_liftRight _ hS s).symm
  refine ⟨OreLocalization.universalHom g fS hfS, ?_, fun h hh => ?_⟩
  · exact RingHom.ext fun a =>
      OreLocalization.universalHom_commutes (f := g) (fS := fS) (hf := hfS) (r := a)
  · exact OreLocalization.universalHom_unique (f := g) (fS := fS) (hf := hfS) h
      (fun r => by rw [← hh]; rfl)

/-- _lTf_L0yvrU-15270 (4:14:30) [prop] An `A_f`-module is an `A`-module on which `f` acts
bijectively, and conversely an `A`-module on which `f` acts bijectively is its own localization at
`f`, hence an `A_f`-module (mathlib: `isLocalizedModule_id`). The equivalence of categories itself
is not stated. -/
theorem prop_15270 (f : A) (N : Type*) [AddCommGroup N] [Module A N]
    [Module (Localization.Away f) N] [IsScalarTower A (Localization.Away f) N] :
    Function.Bijective (fun x : N => f • x) ∧
      IsLocalizedModule (Submonoid.powers f) (LinearMap.id : N →ₗ[A] N) := by
  have := isLocalizedModule_id (Submonoid.powers f) N (Localization.Away f)
  refine ⟨?_, this⟩
  have h := IsLocalizedModule.map_units (LinearMap.id : N →ₗ[A] N) (pw f 1)
  rw [Module.End.isUnit_iff] at h
  convert h using 1
  funext x
  simp [Module.algebraMap_end_apply]

/-- _lTf_L0yvrU-15575 (4:19:35) [prop] If `X_f ⊂ X_g`, say `f^n = gh`, then `g` is invertible on
`M_f`, whence a unique restriction `M_g → M_f` compatible with `M → M_g`, `M → M_f`; uniqueness
gives the compatibility with composition (the presheaf is mathlib's `tilde`). -/
theorem prop_15575 (f g h : A) (n : ℕ) (hfg : f ^ n = g * h) :
    Function.Bijective (fun x : LocalizedModule (Submonoid.powers f) M => g • x) ∧
      ∃! r : LocalizedModule (Submonoid.powers g) M →ₗ[A] LocalizedModule (Submonoid.powers f) M,
        r ∘ₗ LocalizedModule.mkLinearMap (Submonoid.powers g) M =
          LocalizedModule.mkLinearMap (Submonoid.powers f) M := by
  have hu : IsUnit (algebraMap A (Module.End A (LocalizedModule (Submonoid.powers f) M)) g) := by
    have hf := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      (pw f n)
    rw [show ((pw f n) : A) = g * h from hfg, map_mul] at hf
    exact ((((Commute.all g h).map (algebraMap A _)).isUnit_mul_iff).1 hf).1
  refine ⟨(Module.End.isUnit_iff _).1 hu, prop_14682 M g _ fun s => ?_⟩
  obtain ⟨_, hk⟩ := s
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hk
  simpa only [map_pow] using hu.pow k

/-- _lTf_L0yvrU-15707 (4:21:47) [thm] `f ↦ M_f` is a sheaf on the base of the `X_f`. Proved: the
separation half (`prop_36939`: an element of `M` vanishing in every `M_{f_i}` is zero); the gluing
half is the sheaf property of mathlib's `tilde`. -/
theorem thm_15707 (s : Set A) (hs : Ideal.span s = ⊤) (x y : M)
    (h : ∀ r : s, LocalizedModule.mkLinearMap (Submonoid.powers r.1) M x =
      LocalizedModule.mkLinearMap (Submonoid.powers r.1) M y) : x = y :=
  prop_36939 M s hs x y h

/-- _lTf_L0yvrU-15842 (4:24:02) [prop] `A~` is a sheaf of rings and `M~` a sheaf of modules over
it (mathlib: `tilde M : (Spec R).Modules`, a sheaf of modules over the structure sheaf). -/
example {R : CommRingCat.{u}} (N : ModuleCat.{u} R) : (AlgebraicGeometry.Spec R).Modules :=
  AlgebraicGeometry.tilde N

/-- _lTf_L0yvrU-16542 (4:35:42) [prop] The `X_f` are quasi-compact (mathlib:
`PrimeSpectrum.isCompact_basicOpen`). -/
theorem prop_16542 (f : A) : IsCompact (basicOpen f : Set (PrimeSpectrum A)) :=
  isCompact_basicOpen f

/-- _lTf_L0yvrU-16989 (4:43:09) [prop] `M~(X) = M` and `M~(X_f) = M_f` (mathlib:
`AlgebraicGeometry.tilde.isoTop`). -/
def prop_16989 {R : CommRingCat.{u}} (N : ModuleCat.{u} R) :
    N ≅ (AlgebraicGeometry.modulesSpecToSheaf.obj (AlgebraicGeometry.tilde N)).presheaf.obj
      (Opposite.op ⊤) :=
  AlgebraicGeometry.tilde.isoTop N

/-- _lTf_L0yvrU-17115 (4:45:15) [prop] `M ⊗_A A_f → M_f` is an isomorphism: `M_f` is the base
change of `M` (mathlib: `IsLocalizedModule.isBaseChange`). -/
theorem prop_17115 (f : A) :
    IsBaseChange (Localization.Away f) (LocalizedModule.mkLinearMap (Submonoid.powers f) M) :=
  IsLocalizedModule.isBaseChange (Submonoid.powers f) (Localization.Away f) _

/-- _lTf_L0yvrU-17311 (4:48:31) [prop] `A' ⊗_A A' = ∏ A_{f_i f_j}` for `A' = ∏ A_{f_i}`. Proved:
each factor `A_f ⊗_A A_g ≃ (A_f)_g`, the localization of `A` at `fg` (mathlib:
`IsLocalization.Away.tensorEquiv`); the identification of the sheaf condition with the descent
sequence is not stated separately. -/
def prop_17311 (f g : A) :
    Localization.Away f ⊗[A] Localization.Away g ≃ₐ[Localization.Away f]
      Localization.Away (algebraMap A (Localization.Away f) g) :=
  IsLocalization.Away.tensorEquiv (Localization.Away f) g (Localization.Away g)

end Tilde

/-! ### Flat and faithfully flat modules -/

section Flat

variable {A : Type*} [CommRing A]

/-- _lTf_L0yvrU-17443 (4:50:43) [thm] If `A'` is faithfully flat, `0 → M → M ⊗ A' ⇉ M ⊗ A' ⊗ A'`
is exact (`thm_35250`); without the hypothesis it can fail, e.g. for `A' = 0`. -/
theorem thm_17443 :
    (∀ (A B M : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
      [AddCommGroup M] [Module A M], Function.Injective (fun m : M => m ⊗ₜ[A] (1 : B))) ∧
    ¬ Function.Injective (fun m : ℤ => m ⊗ₜ[ℤ] (1 : ZMod 1)) := by
  refine ⟨fun A B M _ _ _ _ _ _ => (thm_35250 (A := A) B M).1, fun h => ?_⟩
  have := h (Subsingleton.elim ((1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 1)) ((0 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 1)))
  exact one_ne_zero this

/-- _lTf_L0yvrU-17573 (4:52:53) [def] `M` is flat if `N ↦ N ⊗ M` is exact, i.e. preserves
injections (mathlib: `Module.Flat`, `Module.Flat.iff_lTensor_preserves_injective_linearMap`). -/
example (M : Type u) [AddCommGroup M] [Module A M] [Small.{u} A] :
    Module.Flat A M ↔ ∀ ⦃N N' : Type u⦄ [AddCommGroup N] [AddCommGroup N'] [Module A N]
      [Module A N'] (f : N →ₗ[A] N'), Function.Injective f → Function.Injective (f.lTensor M) :=
  Module.Flat.iff_lTensor_preserves_injective_linearMap'

/-- _lTf_L0yvrU-17766 (4:56:06) [def] `M` is faithfully flat if flat and `M ⊗ N = 0 ⇒ N = 0`
(mathlib: `Module.FaithfullyFlat`, `Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality`). -/
example (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    Module.FaithfullyFlat R M ↔ Module.Flat R M ∧ ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Subsingleton (M ⊗[R] N) → Subsingleton N :=
  Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality R M

/-- _lTf_L0yvrU-17830 (4:57:10) [prop] If `M` is faithfully flat, `N → N'` is injective (resp.
surjective, bijective) iff `M ⊗ N → M ⊗ N'` is (mathlib:
`Module.FaithfullyFlat.lTensor_injective_iff_injective` and its variants). -/
theorem prop_17830 (M : Type*) [AddCommGroup M] [Module A M] [Module.FaithfullyFlat A M]
    {N N' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (g : N →ₗ[A] N') :
    (Function.Injective (g.lTensor M) ↔ Function.Injective g) ∧
      (Function.Surjective (g.lTensor M) ↔ Function.Surjective g) ∧
      (Function.Bijective (g.lTensor M) ↔ Function.Bijective g) :=
  ⟨Module.FaithfullyFlat.lTensor_injective_iff_injective A M g,
    Module.FaithfullyFlat.lTensor_surjective_iff_surjective A M g,
    Module.FaithfullyFlat.lTensor_bijective_iff_bijective A M g⟩

/-- _lTf_L0yvrU-17894 (4:58:14) [def] An algebra is faithfully flat if it is as a module;
extension of scalars is then exact and faithful (mathlib:
`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`,
`ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat`). -/
example {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.FaithfullyFlat) :
    Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{_, _, u} f) ∧
      (ModuleCat.extendScalars.{_, _, u} f).ReflectsIsomorphisms :=
  ⟨ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf.flat,
    ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat hf⟩

/-- _lTf_L0yvrU-17958 (4:59:18) [prop] For `A'` faithfully flat, `0 → M → M ⊗ A' → M ⊗ A' ⊗ A' → ⋯`
is exact. Proved in degrees 0 and 1 (`thm_36802`). -/
theorem prop_17958 (B : Type*) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Injective ((d0 A B).lTensor M) ∧
      Function.Exact ((d0 A B).lTensor M) ((d1 A B).lTensor M) :=
  thm_36802 B M

end Flat

end

end Buffalo.AG.Part03
