import Mathlib

/-!
# Folder 94, pages 8, 9 and 19: regular sequences over a non-reduced base

The modernised reading `transcripts/94/94.modern.tex` states on pages 8–9 (Lemme 6) and 19
(Lemme 16) a substitute for generic flatness over a non-reduced base: for `S = Spec A`
noetherian and `R` coherent, there is a dense open `U ⊆ S` such that
`Tor_i^A(R, A_𝔭/(t)) = 0` for `i > 0`, `𝔭 ∈ U` and every `A_𝔭`-regular sequence `t`. This is
finding `94-generic-tor-regular-sequences`.

The argument of the reading (Lemme 6 b), with the flatness variant of Lemme 16): let `J` be a
nilpotent ideal of `A` (the nilradical, localised at `𝔭`), `A₀ = A/J`, and suppose that the
layers `grᵏ_J(A) = JᵏA/Jᵏ⁺¹A` are free `A₀`-modules and the layers `grᵏ_J(R) = JᵏR/Jᵏ⁺¹R`
flat `A₀`-modules. Then every `A`-regular sequence is `R`-regular; since the Koszul complex
of an `A`-regular sequence `t` resolves `A/(t)`, its homology after `⊗ R` is
`Tor_•^A(R, A/(t))`, which vanishes in positive degrees once `t` is `R`-regular.

Proved here, for any commutative ring `A`, any nilpotent ideal `J` and any `A`-module `R`
(no noetherian or finiteness hypothesis on `R`, so that the case of Lemme 16, `R` coherent on
an `X` of finite type over `S`, is covered):

* `isWeaklyRegular_iff_of_exact`, `injective_mapQ_of_exact`: for a short exact sequence
  `0 → M' → M → M'' → 0` and a sequence `rs` weakly regular on `M''`, `rs` is weakly regular on
  `M'` iff on `M`, and `M'/(rs)M' → M/(rs)M` is injective (the `Tor₁` that the reading kills);
* `isWeaklyRegular_quotient_filt`, `isWeaklyRegular_of_layers`: dévissage along the `J`-adic
  filtration — a sequence weakly regular on every layer is weakly regular on `M`;
* `isWeaklyRegular_quotient_of_layers_free`: if the layers of a nonzero `M` are free over
  `A₀`, every `M`-weakly regular sequence has weakly regular image in `A₀` (the induction step
  of Lemme 6, « bien standard si n = 1, et on continue par récurrence »);
* `isWeaklyRegular_of_flat`: flat `A₀`-modules inherit weak regularity from `A₀`;
* `isWeaklyRegular_of_gr` (main theorem): layers of `A` free and layers of `R` flat over
  `A₀` ⟹ every `A`-weakly regular sequence is `R`-weakly regular;
* `isWeaklyRegular_of_gr_flat_of_isLocalRing`: the stalk form used on pages 9 and 19: over a
  noetherian local ring, flatness of the layers of `A` suffices (they are then free), and
  `isRegular_of_gr_flat_of_isLocalRing` gives a regular sequence for a nonzero finite `R` and
  `t` in the maximal ideal.

**What is not formalised.** The step « `t` is `R`-regular ⟹ `Tor_i^A(R, A/(t)) = 0` for
`i > 0` » (Koszul complex; Mathlib has neither Koszul resolutions nor the long exact sequence of
`Tor`) is cited, not proved; only its `Tor₁`-type consequence `injective_mapQ_of_exact` is.
The dense open `U` is not constructed: for `X = S` it is the free locus of the finitely many
nonzero layers over the reduced ring `A₀` (generic freeness, open and containing the minimal
primes), and for `X` of finite type it needs generic flatness, which Mathlib does not have;
the compatibility of the layers with localisation is not written out either.
-/

open RingTheory.Sequence Submodule Function

namespace Grothendieck.Folder94

variable {A : Type*} [CommRing A]

section Exact

variable {M M' M'' N N' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
  [AddCommGroup M''] [Module A M''] [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']

/-- Every sequence is weakly regular on the zero module. -/
theorem isWeaklyRegular_of_subsingleton [Subsingleton N] (rs : List A) : IsWeaklyRegular N rs := by
  induction rs generalizing N with
  | nil => exact IsWeaklyRegular.nil A N
  | cons x rs ih =>
    exact IsWeaklyRegular.cons (fun a b _ => Subsingleton.elim a b) (ih)

/-- A retract inherits weak regularity. -/
theorem isWeaklyRegular_of_retract {i : N →ₗ[A] N'} {p : N' →ₗ[A] N}
    (hpi : p ∘ₗ i = LinearMap.id) {rs : List A} (h : IsWeaklyRegular N' rs) :
    IsWeaklyRegular N rs := by
  induction rs generalizing N N' with
  | nil => exact IsWeaklyRegular.nil A N
  | cons x rs ih =>
    rw [isWeaklyRegular_cons_iff] at h
    have hinj : Injective i := fun a b hab => by
      have := congrArg p hab
      rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hpi] at this
    refine IsWeaklyRegular.cons (h.1.of_injective i hinj) (ih (i := QuotSMulTop.map x i)
      (p := QuotSMulTop.map x p) ?_ h.2)
    rw [← QuotSMulTop.map_comp, hpi, QuotSMulTop.map_id]

/-- Modding out by an element regular on the cokernel keeps a short exact sequence injective
on the left. -/
theorem injective_map_of_exact {f : M' →ₗ[A] M} {g : M →ₗ[A] M''} (hf : Injective f)
    (hfg : Exact f g) {x : A} (hx : IsSMulRegular M'' x) : Injective (QuotSMulTop.map x f) := by
  have h0 : Exact (0 : PUnit →ₗ[A] M') f := (LinearMap.exact_zero_iff_injective _ f).mpr hf
  have := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last h0 hfg hx
  rw [map_zero] at this
  exact (LinearMap.exact_zero_iff_injective _ _).mp this

/-- **Two out of three.** For a short exact sequence `0 → M' → M → M'' → 0` and `rs` weakly
regular on `M''`, `rs` is weakly regular on `M'` iff it is on `M`. -/
theorem isWeaklyRegular_iff_of_exact {f : M' →ₗ[A] M} {g : M →ₗ[A] M''} (hf : Injective f)
    (hfg : Exact f g) (hg : Surjective g) {rs : List A} (h'' : IsWeaklyRegular M'' rs) :
    IsWeaklyRegular M' rs ↔ IsWeaklyRegular M rs := by
  induction rs generalizing M' M M'' with
  | nil => exact ⟨fun _ => IsWeaklyRegular.nil A M, fun _ => IsWeaklyRegular.nil A M'⟩
  | cons x rs ih =>
    rw [isWeaklyRegular_cons_iff] at h''
    rw [isWeaklyRegular_cons_iff, isWeaklyRegular_cons_iff,
      ih (injective_map_of_exact hf hfg h''.1) (QuotSMulTop.map_exact x hfg hg)
        (QuotSMulTop.map_surjective x hg) h''.2]
    refine and_congr_left' ⟨fun h => ?_, fun h => h.of_injective f hf⟩
    exact isSMulRegular_of_range_eq_ker hf (LinearMap.exact_iff.mp hfg).symm h h''.1

/-- For a short exact sequence `0 → M' → M → M'' → 0` and `rs` weakly regular on `M''`, the map
`M'/(rs)M' → M/(rs)M` is injective: the vanishing of `Tor₁(M'', A/(rs))` in this guise. -/
theorem injective_mapQ_of_exact {f : M' →ₗ[A] M} {g : M →ₗ[A] M''} (hf : Injective f)
    (hfg : Exact f g) (hg : Surjective g) {rs : List A} (h'' : IsWeaklyRegular M'' rs) :
    Injective (mapQ _ _ f (smul_top_le_comap_smul_top (Ideal.ofList rs) f)) := by
  have h0 : Exact (0 : PUnit →ₗ[A] M') f := (LinearMap.exact_zero_iff_injective _ f).mpr hf
  have := map_first_exact_on_four_term_right_exact_of_isSMulRegular_last h0 hfg hg h''
  rw [← LinearMap.exact_zero_iff_injective (PUnit : Type)]
  refine fun y => ⟨fun hy => ?_, fun ⟨z, hz⟩ => ?_⟩
  · obtain ⟨z, rfl⟩ := (this y).mp hy
    induction z using Submodule.Quotient.induction_on with
    | H z => exact ⟨0, by simp⟩
  · rw [← hz]; simp

end Exact

section Filtration

variable (J : Ideal A) (M : Type*) [AddCommGroup M] [Module A M]

/-- The `J`-adic filtration `JᵏM`. -/
abbrev filt (k : ℕ) : Submodule A M := J ^ k • ⊤

/-- The layer `grᵏ_J(M) = JᵏM / Jᵏ⁺¹M`. -/
abbrev layer (k : ℕ) : Type _ := ↥(filt J M k) ⧸ (filt J M (k + 1)).comap (filt J M k).subtype

variable {J M}

theorem filt_antitone {j k : ℕ} (h : j ≤ k) : filt J M k ≤ filt J M j :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

theorem filt_zero : filt J M 0 = ⊤ := by simp [filt]

/-- The inclusion `grᵏ(M) → M/Jᵏ⁺¹M`. -/
def layerToQuot (k : ℕ) : layer J M k →ₗ[A] M ⧸ filt J M (k + 1) :=
  mapQ _ _ (filt J M k).subtype le_rfl

/-- The projection `M/Jᵏ⁺¹M → M/JᵏM`. -/
def quotToQuot (k : ℕ) : M ⧸ filt J M (k + 1) →ₗ[A] M ⧸ filt J M k :=
  factor (filt_antitone (Nat.le_succ k))

theorem layerToQuot_injective (k : ℕ) : Injective (layerToQuot (J := J) (M := M) k) := by
  rw [← LinearMap.ker_eq_bot, layerToQuot, ker_mapQ]
  exact mkQ_map_self _

theorem quotToQuot_surjective (k : ℕ) : Surjective (quotToQuot (J := J) (M := M) k) :=
  factor_surjective (filt_antitone (Nat.le_succ k))

theorem exact_layerToQuot (k : ℕ) :
    Exact (layerToQuot (J := J) (M := M) k) (quotToQuot k) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H m =>
    constructor
    · intro hm
      have hm' : m ∈ filt J M k := by
        simpa [quotToQuot] using hm
      exact ⟨Submodule.Quotient.mk ⟨m, hm'⟩, rfl⟩
    · rintro ⟨z, hz⟩
      rw [← hz]
      induction z using Submodule.Quotient.induction_on with
      | H z => simp [quotToQuot, layerToQuot]

/-- **Dévissage.** If `rs` is weakly regular on the layers `grᵏ(M)` for `k < j`, it is weakly
regular on `M/JʲM`. -/
theorem isWeaklyRegular_quotient_filt {rs : List A} :
    ∀ j, (∀ k < j, IsWeaklyRegular (layer J M k) rs) →
      IsWeaklyRegular (M ⧸ filt J M j) rs
  | 0, _ => by
    have : Subsingleton (M ⧸ filt J M 0) := by
      rw [filt_zero]; infer_instance
    exact isWeaklyRegular_of_subsingleton rs
  | j + 1, h =>
    (isWeaklyRegular_iff_of_exact (layerToQuot_injective j) (exact_layerToQuot j)
      (quotToQuot_surjective j) (isWeaklyRegular_quotient_filt j fun k hk => h k (by omega))).mp
      (h j (by omega))

/-- If `JⁿM = 0` and `rs` is weakly regular on every layer, it is weakly regular on `M`. -/
theorem isWeaklyRegular_of_layers {n : ℕ} (hn : filt J M n = ⊥) {rs : List A}
    (h : ∀ k, IsWeaklyRegular (layer J M k) rs) : IsWeaklyRegular M rs := by
  have := isWeaklyRegular_quotient_filt n fun k _ => h k
  rw [hn] at this
  exact ((quotEquivOfEqBot (⊥ : Submodule A M) rfl).isWeaklyRegular_congr rs).mp this

end Filtration

section Main

variable {J : Ideal A}

/-- A flat `A/J`-module inherits weak regularity from `A/J`. -/
theorem isWeaklyRegular_of_flat (N : Type*) [AddCommGroup N] [Module (A ⧸ J) N] [Module A N]
    [IsScalarTower A (A ⧸ J) N] [Module.Flat (A ⧸ J) N] {rs : List A}
    (h : IsWeaklyRegular (A ⧸ J) rs) : IsWeaklyRegular N rs := by
  rw [← isWeaklyRegular_map_algebraMap_iff (A ⧸ J) N]
  rw [← isWeaklyRegular_map_algebraMap_iff (A ⧸ J) (A ⧸ J)] at h
  have := h.isWeaklyRegular_lTensor (M₂ := N)
  exact ((TensorProduct.rid (A ⧸ J) N).isWeaklyRegular_congr _).mp this

/-- **The induction step of Lemme 6.** If `JⁿM = 0`, `M ≠ 0` and every layer `grᵏ_J(M)` is a free
`A/J`-module, every sequence weakly regular on `M` has weakly regular image in `A/J`. The last
nonzero layer `JᵐM` is a submodule of `M`, free and nonzero over `A/J`; modulo `(t₁, …, tᵢ)` it
still injects into `M/(t₁, …, tᵢ)M`, because `M/JᵐM` is filtered by free layers on which the
`tⱼ` are already known to be regular. -/
theorem isWeaklyRegular_quotient_of_layers_free {M : Type*} [AddCommGroup M] [Module A M]
    [Nontrivial M] {n : ℕ} (hn : filt J M n = ⊥) (ι : ℕ → Type*)
    (e : ∀ k, layer J M k ≃ₗ[A] (ι k →₀ A ⧸ J)) {rs : List A} (h : IsWeaklyRegular M rs) :
    IsWeaklyRegular (A ⧸ J) rs := by
  classical
  have hex : ∃ k, filt J M (k + 1) = ⊥ :=
    ⟨n, eq_bot_iff.mpr ((filt_antitone (Nat.le_succ n)).trans hn.le)⟩
  set m := Nat.find hex with hmdef
  have hm : filt J M (m + 1) = ⊥ := Nat.find_spec hex
  have hm0 : filt J M m ≠ ⊥ := by
    intro h0
    rcases Nat.eq_zero_or_eq_succ_pred m with hz | hs
    · rw [hz, filt_zero] at h0
      exact top_ne_bot h0
    · have := Nat.find_min' hex (m := m.pred) (by rw [show m.pred + 1 = m by omega]; exact h0)
      omega
  have hcomap : (filt J M (m + 1)).comap (filt J M m).subtype = ⊥ := by
    rw [hm, comap_bot, ker_subtype]
  let eL : ↥(filt J M m) ≃ₗ[A] (ι m →₀ A ⧸ J) :=
    (quotEquivOfEqBot _ hcomap).symm.trans (e m)
  have hne : Nonempty (ι m) := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    have : Subsingleton ↥(filt J M m) := eL.toEquiv.subsingleton
    exact hm0 (Submodule.eq_bot_of_subsingleton)
  obtain ⟨i⟩ := hne
  induction rs using List.reverseRecOn with
  | nil => exact IsWeaklyRegular.nil _ _
  | append_singleton rs y ih =>
    rw [isWeaklyRegular_append_iff] at h
    have h0 := ih h.1
    have hlay : ∀ k, IsWeaklyRegular (layer J M k) rs := fun k =>
      ((e k).isWeaklyRegular_congr rs).mpr (isWeaklyRegular_of_flat _ h0)
    have hq : IsWeaklyRegular (M ⧸ filt J M m) rs :=
      isWeaklyRegular_quotient_filt m fun k _ => hlay k
    have hf : Injective (filt J M m).subtype := Submodule.injective_subtype _
    have hfg : Exact (filt J M m).subtype (filt J M m).mkQ := LinearMap.exact_subtype_mkQ _
    have hg := (filt J M m).mkQ_surjective
    have hL : IsWeaklyRegular (filt J M m) rs := (isWeaklyRegular_iff_of_exact hf hfg hg hq).mpr h.1
    have hinj := injective_mapQ_of_exact hf hfg hg hq
    have hL' : IsWeaklyRegular (filt J M m) (rs ++ [y]) := by
      rw [isWeaklyRegular_append_iff]
      refine ⟨hL, ?_⟩
      have h2 := h.2
      rw [isWeaklyRegular_singleton_iff] at h2 ⊢
      exact h2.of_injective _ hinj
    have hF := (eL.isWeaklyRegular_congr _).mp hL'
    exact isWeaklyRegular_of_retract (i := Finsupp.lsingle (R := A) i)
      (p := Finsupp.lapply (R := A) i) (by ext; simp) hF

/-- **Lemmes 6 b) and 16, key step.** Let `J` be a nilpotent ideal of `A` (`Jⁿ = 0`), `A₀ = A/J`.
If every layer `grᵏ_J(A)` is a free `A₀`-module and every layer `grᵏ_J(R)` is a flat
`A₀`-module, every `A`-weakly regular sequence is `R`-weakly regular. -/
theorem isWeaklyRegular_of_gr {R : Type*} [AddCommGroup R] [Module A R] {n : ℕ} (hn : J ^ n = ⊥)
    (ι : ℕ → Type*) (eA : ∀ k, layer J A k ≃ₗ[A] (ι k →₀ A ⧸ J))
    (N : ℕ → Type*) [∀ k, AddCommGroup (N k)] [∀ k, Module (A ⧸ J) (N k)] [∀ k, Module A (N k)]
    [∀ k, IsScalarTower A (A ⧸ J) (N k)] [∀ k, Module.Flat (A ⧸ J) (N k)]
    (eR : ∀ k, layer J R k ≃ₗ[A] N k) {rs : List A} (h : IsWeaklyRegular A rs) :
    IsWeaklyRegular R rs := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have := Module.subsingleton A R
    exact isWeaklyRegular_of_subsingleton rs
  have hA0 := isWeaklyRegular_quotient_of_layers_free (M := A) (n := n) (by simp [filt, hn]) ι eA h
  refine isWeaklyRegular_of_layers (J := J) (n := n) (by simp [filt, hn]) fun k => ?_
  exact ((eR k).isWeaklyRegular_congr rs).mpr (isWeaklyRegular_of_flat _ hA0)

end Main

section Local

variable {J : Ideal A}

/-- **Lemmes 6 b) and 16 at a point.** Over a noetherian local ring `A` (the local ring
`A_𝔭` of the reading), with `J` nilpotent, if the layers of `A` and of the `A`-module `R` are flat
over `A₀ = A/J` (as generic flatness provides on `U`), every `A`-weakly regular sequence is
`R`-weakly regular. The layers of `A` are finite over the local ring `A₀`, hence free; for `R`
flatness is used as such (no finiteness on `R`, as in Lemme 16). -/
theorem isWeaklyRegular_of_gr_flat_of_isLocalRing [IsLocalRing A] [IsNoetherianRing A]
    {R : Type*} [AddCommGroup R] [Module A R] {n : ℕ} (hn : J ^ n = ⊥)
    (P : ℕ → Type*) [∀ k, AddCommGroup (P k)] [∀ k, Module (A ⧸ J) (P k)] [∀ k, Module A (P k)]
    [∀ k, IsScalarTower A (A ⧸ J) (P k)] [∀ k, Module.Flat (A ⧸ J) (P k)]
    (eA : ∀ k, layer J A k ≃ₗ[A] P k)
    (N : ℕ → Type*) [∀ k, AddCommGroup (N k)] [∀ k, Module (A ⧸ J) (N k)] [∀ k, Module A (N k)]
    [∀ k, IsScalarTower A (A ⧸ J) (N k)] [∀ k, Module.Flat (A ⧸ J) (N k)]
    (eR : ∀ k, layer J R k ≃ₗ[A] N k) {rs : List A} (h : IsWeaklyRegular A rs) :
    IsWeaklyRegular R rs := by
  have hJ : J ≠ ⊤ := by
    rintro rfl
    rw [Ideal.top_pow] at hn
    exact top_ne_bot hn
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (A ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hfin : ∀ k, Module.Finite (A ⧸ J) (P k) := fun k =>
    have : Module.Finite A (P k) := Module.Finite.equiv (eA k)
    Module.Finite.of_restrictScalars_finite A (A ⧸ J) (P k)
  have hfree : ∀ k, Module.Free (A ⧸ J) (P k) := fun k => Module.free_of_flat_of_isLocalRing
  exact isWeaklyRegular_of_gr hn (fun k => Module.Free.ChooseBasisIndex (A ⧸ J) (P k))
    (fun k => (eA k).trans ((Module.Free.chooseBasis (A ⧸ J) (P k)).repr.restrictScalars A))
    N eR h

/-- The same, as regular sequences: for `R` finite and nonzero and `t` in the maximal ideal, an
`A`-regular sequence is `R`-regular — so its Koszul complex, which resolves `A/(t)`, stays
acyclic after `⊗ R`, i.e. `Tor_i^A(R, A/(t)) = 0` for `i > 0` (that last step is not formalised). -/
theorem isRegular_of_gr_flat_of_isLocalRing [IsLocalRing A] [IsNoetherianRing A]
    {R : Type*} [AddCommGroup R] [Module A R] [Module.Finite A R] [Nontrivial R] {n : ℕ}
    (hn : J ^ n = ⊥)
    (P : ℕ → Type*) [∀ k, AddCommGroup (P k)] [∀ k, Module (A ⧸ J) (P k)] [∀ k, Module A (P k)]
    [∀ k, IsScalarTower A (A ⧸ J) (P k)] [∀ k, Module.Flat (A ⧸ J) (P k)]
    (eA : ∀ k, layer J A k ≃ₗ[A] P k)
    (N : ℕ → Type*) [∀ k, AddCommGroup (N k)] [∀ k, Module (A ⧸ J) (N k)] [∀ k, Module A (N k)]
    [∀ k, IsScalarTower A (A ⧸ J) (N k)] [∀ k, Module.Flat (A ⧸ J) (N k)]
    (eR : ∀ k, layer J R k ≃ₗ[A] N k) {rs : List A} (h : IsRegular A rs)
    (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal A) :
    IsRegular R rs :=
  (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
    (isWeaklyRegular_of_gr_flat_of_isLocalRing hn P eA N eR h.1)

end Local

end Grothendieck.Folder94
