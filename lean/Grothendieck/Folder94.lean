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
    exact IsWeaklyRegular.cons (fun a b _ => Subsingleton.elim a b) ih

/-- A retract inherits weak regularity. -/
theorem isWeaklyRegular_of_retract {i : N →ₗ[A] N'} {p : N' →ₗ[A] N}
    (hpi : p ∘ₗ i = LinearMap.id) {rs : List A} (h : IsWeaklyRegular N' rs) :
    IsWeaklyRegular N rs := by
  induction rs generalizing N N' with
  | nil => exact IsWeaklyRegular.nil A N
  | cons x rs ih =>
    rw [isWeaklyRegular_cons_iff] at h
    refine IsWeaklyRegular.cons (h.1.of_injective i (LeftInverse.injective (g := p)
      (LinearMap.congr_fun hpi))) (ih (i := QuotSMulTop.map x i)
      (p := QuotSMulTop.map x p) ?_ h.2)
    rw [← QuotSMulTop.map_comp, hpi, QuotSMulTop.map_id]

/-- Modding out by an element regular on the cokernel keeps a short exact sequence injective
on the left. -/
theorem injective_map_of_exact {f : M' →ₗ[A] M} {g : M →ₗ[A] M''} (hf : Injective f)
    (hfg : Exact f g) {x : A} (hx : IsSMulRegular M'' x) : Injective (QuotSMulTop.map x f) := by
  have := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
    ((LinearMap.exact_zero_iff_injective (PUnit : Type) f).mpr hf) hfg hx
  rwa [map_zero, LinearMap.exact_zero_iff_injective] at this

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
  have := map_first_exact_on_four_term_right_exact_of_isSMulRegular_last
    ((LinearMap.exact_zero_iff_injective (PUnit : Type) f).mpr hf) hfg hg h''
  rw [← LinearMap.exact_zero_iff_injective (PUnit : Type)]
  refine fun y => ⟨fun hy => ?_, fun ⟨z, hz⟩ => ?_⟩
  · obtain ⟨z, rfl⟩ := (this y).mp hy
    exact ⟨0, by simp⟩
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
      exact ⟨Submodule.Quotient.mk ⟨m, by simpa [quotToQuot] using hm⟩, rfl⟩
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
    have : Subsingleton (M ⧸ filt J M 0) := by rw [filt_zero]; infer_instance
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
  exact ((TensorProduct.rid (A ⧸ J) N).isWeaklyRegular_congr _).mp
    (h.isWeaklyRegular_lTensor (M₂ := N))

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
    rcases m.eq_zero_or_pos with hz | hs
    · rw [hz, filt_zero] at h0
      exact top_ne_bot h0
    · have := Nat.find_min' hex (m := m - 1) (by rwa [Nat.sub_add_cancel hs])
      omega
  have hcomap : (filt J M (m + 1)).comap (filt J M m).subtype = ⊥ := by
    rw [hm, comap_bot, ker_subtype]
  let eL : ↥(filt J M m) ≃ₗ[A] (ι m →₀ A ⧸ J) :=
    (quotEquivOfEqBot _ hcomap).symm.trans (e m)
  have hne : Nonempty (ι m) := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    have : Subsingleton ↥(filt J M m) := eL.toEquiv.subsingleton
    exact hm0 Submodule.eq_bot_of_subsingleton
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
    have hf := Submodule.injective_subtype (filt J M m)
    have hfg := LinearMap.exact_subtype_mkQ (filt J M m)
    have hg := (filt J M m).mkQ_surjective
    have hinj := injective_mapQ_of_exact hf hfg hg hq
    refine isWeaklyRegular_of_retract (i := Finsupp.lsingle (R := A) i)
      (p := Finsupp.lapply (R := A) i) (by ext; simp) ((eL.isWeaklyRegular_congr _).mp ?_)
    rw [isWeaklyRegular_append_iff]
    refine ⟨(isWeaklyRegular_iff_of_exact hf hfg hg hq).mpr h.1, ?_⟩
    have h2 := h.2
    rw [isWeaklyRegular_singleton_iff] at h2 ⊢
    exact h2.of_injective _ hinj

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
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (by
    rintro rfl
    rw [Ideal.top_pow] at hn
    exact top_ne_bot hn)
  have : IsLocalRing (A ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hfin : ∀ k, Module.Finite (A ⧸ J) (P k) := fun k =>
    have : Module.Finite A (P k) := Module.Finite.equiv (eA k)
    Module.Finite.of_restrictScalars_finite A (A ⧸ J) (P k)
  have hfree : ∀ k, Module.Free (A ⧸ J) (P k) := fun _ => Module.free_of_flat_of_isLocalRing
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

/-!
## Page 7: a counterexample to the converse of Remarque 5 bis (local finiteness only)

Finding `94-rank-constructibility`. Remarque 5 bis claims that, under (i)–(iv) of Lemme 5
(left exactness, filtered colimits, completion at every `𝔭`, `F(M)` finite for `M` of finite
length over `A_𝔭`), condition (v) — `F` representable on a non-empty open of each `V(𝔭)` —
follows from the constructibility of `𝔭 ↦ dim F(k(𝔭))`. It does not. Take `A = k[x, y]`
(written `k[X][X]`, `x` the inner variable), distinct `a_j ∈ k`, `h_j = x − a_j`, and
`F(M) = colim(M →h M →h M → ⋯)`, the telescope `Tele` (a filtered colimit of copies of
`Hom(A, −)`, hence left exact and commuting with filtered colimits).

* `tele_atPrime_bijective`: at every prime `𝔭`, all but at most one `h_j` are units in `A_𝔭`, so
  from some stage on `F(M) ≅ M` for every `A_𝔭`-module (in particular every `Â_𝔭`-module):
  completion and local finiteness hold;
* `finrank_tele_field`: for every field `K` receiving `A` (every residue field `k(𝔭)`),
  `dim_K F(K) = 1` — the rank function is constant;
* `not_finite_tele_away`, `not_representable_away`: for every `g ≠ 0`, `F(A_g)` is not a finite
  `A_g`-module, so `F` restricted to `A_g`-modules is `Hom(Q, −)` for no finite `Q`: (v) fails
  at `𝔭 = 0`.

The general tools are `teleOf_bijective` (a telescope whose maps are eventually units is its
stage) and `exists_isUnit_of_finite` (a finite telescope of a ring along non-zero-divisors has
eventually invertible maps). Left exactness and commutation with filtered colimits are the
standard properties of filtered colimits of representables and are not restated.
-/

open Polynomial

noncomputable section

universe u

section Telescope

variable {R : Type*} [CommRing R] (c : ℕ → R) (M : Type*) [AddCommGroup M] [Module R M]

/-- The transition maps of the telescope `M →c M →c M → ⋯` from stage `i` to stage `j`:
multiplication by `∏_{i < l ≤ j} c l`. -/
def teleMap (i j : ℕ) (_ : i ≤ j) : M →ₗ[R] M := (∏ l ∈ Finset.Ioc i j, c l) • LinearMap.id

instance teleMap_directedSystem :
    DirectedSystem (fun _ : ℕ => M) (fun i j h => teleMap c M i j h) where
  map_self i x := by simp [teleMap]
  map_map k j i hij hjk x := by
    simp only [teleMap, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    rw [mul_comm, Finset.prod_Ioc_consecutive _ hij hjk]

/-- The functor `F(M) = colim(M →c M →c M → ⋯)` of the counterexample. -/
abbrev Tele : Type _ := Module.DirectLimit (fun _ : ℕ => M) (teleMap c M)

/-- The insertion of stage `i`. -/
abbrev teleOf (i : ℕ) : M →ₗ[R] Tele c M := Module.DirectLimit.of R ℕ (fun _ => M) (teleMap c M) i

variable {c M}

theorem teleOf_eq {i j : ℕ} (h : i ≤ j) (x : M) :
    teleOf c M i x = teleOf c M j ((∏ l ∈ Finset.Ioc i j, c l) • x) := by
  rw [← Module.DirectLimit.of_f (hij := h)]; rfl

theorem teleOf_bijective {N : ℕ} (hc : ∀ l, N < l → IsUnit (c l)) : Bijective (teleOf c M N) := by
  have hP : ∀ j, IsUnit (∏ l ∈ Finset.Ioc N j, c l) := fun j =>
    IsUnit.prod_iff.2 (fun l hl => hc l (Finset.mem_Ioc.1 hl).1)
  constructor
  · intro x y hxy
    obtain ⟨j, hj, h⟩ := Module.DirectLimit.exists_eq_of_of_eq hxy
    simpa [teleMap, (hP j).smul_left_cancel] using h
  · intro z
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    rcases le_total i N with h | h
    · exact ⟨_, (teleOf_eq h x).symm⟩
    · obtain ⟨u, hu⟩ := hP i
      refine ⟨u⁻¹ • x, ?_⟩
      rw [teleOf_eq h, ← hu]
      congr 1
      exact smul_inv_smul u x

theorem range_teleOf_mono {i j : ℕ} (h : i ≤ j) :
    LinearMap.range (teleOf c M i) ≤ LinearMap.range (teleOf c M j) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨_, (teleOf_eq h x).symm⟩

theorem exists_isUnit_of_finite (hc : ∀ l, c l ∈ nonZeroDivisors R)
    [Module.Finite R (Tele c R)] : ∃ N, ∀ l, N < l → IsUnit (c l) := by
  classical
  have key : ∀ s : Finset (Tele c R), ∃ N, ∀ z ∈ s, z ∈ LinearMap.range (teleOf c R N) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert z s _ ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
      refine ⟨max N i, fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact range_teleOf_mono (le_max_right N i) ⟨x, rfl⟩
      · exact range_teleOf_mono (le_max_left N i) (hN w hw)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := Tele c R)
  obtain ⟨N, hN⟩ := key s
  have htop : LinearMap.range (teleOf c R N) = ⊤ := by
    rw [eq_top_iff, ← hs, Submodule.span_le]; exact hN
  refine ⟨N, fun l hl => ?_⟩
  obtain ⟨m, hm⟩ : teleOf c R l 1 ∈ LinearMap.range (teleOf c R N) := htop ▸ trivial
  rw [teleOf_eq hl.le] at hm
  obtain ⟨k, hk, h⟩ := Module.DirectLimit.exists_eq_of_of_eq hm
  simp only [teleMap, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at h
  have hQ : (∏ j ∈ Finset.Ioc l k, c j) ∈ nonZeroDivisors R :=
    Submonoid.prod_mem _ (fun j _ => hc j)
  have h1 : (∏ j ∈ Finset.Ioc N l, c j) * m = 1 := by
    have h2 : (∏ j ∈ Finset.Ioc l k, c j) * ((∏ j ∈ Finset.Ioc N l, c j) * m - 1) = 0 := by
      rw [mul_sub, sub_eq_zero]; simpa using h
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hQ).1 _ h2)
  exact IsUnit.prod_iff.1 (IsUnit.of_mul_eq_one _ h1) l (Finset.mem_Ioc.2 ⟨hl, le_rfl⟩)

/-- If at most one index is bad, all large indices are good. -/
theorem exists_forall_gt_not {bad : ℕ → Prop} (h : ∀ i j, bad i → bad j → i = j) :
    ∃ N, ∀ l, N < l → ¬ bad l := by
  by_cases hb : ∃ j, bad j
  · obtain ⟨j, hj⟩ := hb
    exact ⟨j, fun l hl hl' => hl.ne (h j l hj hl')⟩
  · exact ⟨0, fun l _ hl => hb ⟨l, hl⟩⟩

end Telescope

section Plane

variable {k : Type*} [Field k]

/-- `x − a` in `k[x, y]`, written `k[X][X]` with `x` the inner variable. -/
abbrev hx (a : k) : k[X][X] := C (X - C a)

theorem hx_prime (a : k) : Prime (hx a) := Polynomial.prime_C_iff.2 (Polynomial.prime_X_sub_C a)

theorem hx_sub (a b : k) : hx a - hx b = C (C (b - a)) := by
  rw [← map_sub]; congr 1; rw [map_sub]; ring

theorem isUnit_hx_sub {a b : k} (hab : a ≠ b) : IsUnit (hx a - hx b) := by
  rw [hx_sub]; exact isUnit_C.2 (isUnit_C.2 (sub_ne_zero.2 hab.symm).isUnit)

/-- For `g ≠ 0`, only finitely many `x − a_j` divide `g`. -/
theorem finite_setOf_hx_dvd {a : ℕ → k} (ha : Injective a) {g : k[X][X]} (hg : g ≠ 0) :
    {j | hx (a j) ∣ g}.Finite := by
  have hq : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hg
  refine ((Polynomial.finite_setOfPred_isRoot hq).preimage ha.injOn).subset fun j hj => ?_
  have := (Polynomial.C_dvd_iff_dvd_coeff _ _).1 hj g.natDegree
  exact (Polynomial.dvd_iff_isRoot).1 this

theorem dvd_of_isUnit_away {D : Type*} [CommRing D] [IsDomain D] {g h : D} (hg : g ≠ 0)
    (hh : Prime h) (hu : IsUnit (algebraMap D (Localization.Away g) h)) : h ∣ g := by
  obtain ⟨U, hU⟩ := hu
  obtain ⟨⟨b, ⟨s, hs⟩⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) (↑U⁻¹ : Localization.Away g)
  obtain ⟨n, rfl⟩ := hs
  simp only at e
  have hinj := IsLocalization.injective (Localization.Away g)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  have : g ^ n = h * b := by
    apply hinj
    rw [map_mul, ← e, ← mul_assoc, ← hU, Units.mul_inv, one_mul]
  exact hh.dvd_of_dvd_pow (Dvd.intro b this.symm)

/-- `F(A_g)` is not finitely generated over `A_g` for any `g ≠ 0`. -/
theorem not_finite_tele_away {a : ℕ → k} (ha : Injective a) {g : k[X][X]} (hg : g ≠ 0) :
    ¬ Module.Finite (Localization.Away g)
      (Tele (fun j => algebraMap k[X][X] (Localization.Away g) (hx (a j))) (Localization.Away g)) := by
  intro hfin
  have : IsDomain (Localization.Away g) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  have hinj := IsLocalization.injective (Localization.Away g)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  obtain ⟨N, hN⟩ := exists_isUnit_of_finite (R := Localization.Away g)
    (c := fun j => algebraMap k[X][X] (Localization.Away g) (hx (a j)))
    (fun l => mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).2 (hx_prime (a l)).ne_zero))
  obtain ⟨N', hN'⟩ := (finite_setOf_hx_dvd ha hg).bddAbove
  have hl := dvd_of_isUnit_away hg (hx_prime _) (hN (max N N' + 1) (by omega))
  have := hN' hl
  omega

/-- A noetherian ring: the dual of a finite module is finite. -/
theorem finite_dual {R : Type*} [CommRing R] [IsNoetherianRing R] (Q : Type*) [AddCommGroup Q]
    [Module R Q] [Module.Finite R Q] : Module.Finite R (Q →ₗ[R] R) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R Q
  exact Module.Finite.of_injective π.dualMap (LinearMap.dualMap_injective_of_surjective hπ)

/-- Hence `F` restricted to `A_g`-modules is representable by no finite module, for any
`g ≠ 0`: the case `𝔭 = 0` of Lemma 5 (v) fails. -/
theorem not_representable_away {a : ℕ → k} (ha : Injective a) {g : k[X][X]} (hg : g ≠ 0)
    (Q : Type*) [AddCommGroup Q] [Module (Localization.Away g) Q]
    [Module.Finite (Localization.Away g) Q]
    (e : (Q →ₗ[Localization.Away g] Localization.Away g) ≃ₗ[Localization.Away g]
      Tele (fun j => algebraMap k[X][X] (Localization.Away g) (hx (a j))) (Localization.Away g)) :
    False := by
  have := finite_dual (R := Localization.Away g) Q
  exact not_finite_tele_away ha hg (Module.Finite.equiv e)

/-- Two of the `x − a_j` never vanish together in a field. -/
theorem eq_of_map_hx_eq_zero {K : Type*} [Field K] (φ : k[X][X] →+* K) {a : ℕ → k}
    (ha : Injective a) (i j : ℕ) (hi : φ (hx (a i)) = 0) (hj : φ (hx (a j)) = 0) : i = j := by
  by_contra hij
  have := (isUnit_hx_sub (ha.ne hij)).map φ
  rw [map_sub, hi, hj, sub_zero] at this
  exact not_isUnit_zero this

/-- Over any field `K` receiving `k[x, y]` (e.g. a residue field `k(𝔭)`), `F(K)` is
one-dimensional: the fibre rank of `F` is constant, equal to `1`. -/
theorem finrank_tele_field {K : Type*} [Field K] (φ : k[X][X] →+* K) {a : ℕ → k}
    (ha : Injective a) : Module.finrank K (Tele (fun j => φ (hx (a j))) K) = 1 := by
  obtain ⟨N, hN⟩ := exists_forall_gt_not (eq_of_map_hx_eq_zero φ ha)
  let e := LinearEquiv.ofBijective _ (teleOf_bijective (c := fun j => φ (hx (a j))) (M := K)
    (N := N) fun l hl => (Ne.isUnit (hN l hl)))
  rw [← e.finrank_eq, Module.finrank_self]

/-- At every prime `𝔭`, all but at most one `x − a_j` are units of `A_𝔭`, so from some stage
on `F(M) ≅ M` for every `A_𝔭`-module `M` (and every `Â_𝔭`-module): the completion and local
finiteness conditions hold. -/
theorem tele_atPrime_bijective (p : Ideal k[X][X]) [p.IsPrime] {a : ℕ → k} (ha : Injective a) :
    ∃ N, ∀ (M : Type u) [AddCommGroup M] [Module (Localization.AtPrime p) M],
      Bijective (teleOf (fun j => algebraMap k[X][X] (Localization.AtPrime p) (hx (a j))) M N) := by
  obtain ⟨N, hN⟩ := exists_forall_gt_not (bad := fun j => hx (a j) ∈ p) fun i j hi hj => by
    by_contra hij
    exact (Ideal.IsPrime.ne_top ‹_›)
      (Ideal.eq_top_of_isUnit_mem _ (p.sub_mem hi hj) (isUnit_hx_sub (ha.ne hij)))
  exact ⟨N, fun M _ _ => teleOf_bijective fun l hl =>
    (IsLocalization.AtPrime.isUnit_to_map_iff _ p _).2 (hN l hl)⟩

end Plane

end

end Grothendieck.Folder94
