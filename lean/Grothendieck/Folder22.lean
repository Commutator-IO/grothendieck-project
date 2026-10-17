import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Folder 22, Lemme 3.3, Corollaires 3.4, 3.5, and the obstruction of pp. 22, 24

The modernised reading `transcripts/22/22.modern.tex` (typescript page 10, his
page 25) states:

> **Lemme 3.3.** Soient `A` un anneau, `(P_i)_{i ∈ I}` une famille de
> `A`-modules, `P = ∏ P_i` leur produit, et `M` un `A`-module de présentation
> finie. Alors l'homomorphisme canonique `M ⊗_A P → ∏_i (M ⊗_A P_i)` est un
> isomorphisme.
>
> **Corollaire 3.4.** Supposons que tout `A`-module de type fini soit de
> présentation finie — par exemple `A` noethérien. Alors tout produit de
> `A`-modules plats est plat.
>
> **Corollaire 3.5.** Supposons `A` comme en 3.4, par exemple noethérien. Soit
> `P` un `A`-module isomorphe à la limite projective d'un système projectif
> *strict*, admettant un système cofinal dénombrable, de `A`-modules projectifs.
> Alors `P` est un `A`-module plat.

The rest of the folder — formal smoothness of topological algebras (3.2, 3.6),
Cohen algebras (3.7–3.12), the regular-homomorphism criterion 3.13 — needs preadic
topologies and geometric regularity, which mathlib does not have; it is not
formalised here. The discrete-topology half of the obstruction of pages 22 and 24
is (finding `22-power-series-discrete-obstruction`, issue #54): for
`k = ℚ(x_i : i ∈ I)`, `I` infinite, and `A = k[[t]]`, no derivation
`D : A → Ω_k ⊗_k A ≅ A^{(I)}` induces `d_k`, because the `dx_{i_n}`-component of
`D(Σ x_{i_n} tⁿ)` has `tⁿ`-coefficient `1` for every `n`; hence `A` is not formally
smooth over `k` for the discrete topology. The `t`-adic half (formal smoothness
for the `t`-adic topology) is not formalised.

What is proved:

* `lemme3_3` — exactly as stated: for `M` finitely presented, the canonical map
  `TensorProduct.piRightHom : M ⊗ ∏ P_i → ∏ (M ⊗ P_i)` is bijective. The proof is
  the typescript's: a presentation by free modules *of finite type* (the
  handwritten « de type fini », which the reading rightly calls essential),
  right exactness of `⊗`, exactness of products, and the five lemma.
* `corollaire3_4` — under the reading's hypothesis, verbatim.
* `corollaire3_5` — for a projective system indexed by `ℕ` with surjective
  transition maps (the reading's own reduction: « Le système cofinal
  dénombrable permet de se ramener à un système `(P_n)_{n ∈ ℕ}` dont les
  applications de transition sont surjectives — c'est ce que veut dire
  strict »). The reduction from a general countable cofinal system to `ℕ` is not
  formalised. The proof follows the reading's argument: the sequences split,
  `lim P_n ≅ P_0 × ∏ K_n` with `K_n = ker(P_{n+1} → P_n)` projective, then 3.4.
* `no_derivation` — the obstruction, abstractly: if `M` is a free `k`-module with
  basis `b`, no derivation `k⟦t⟧ → k⟦t⟧ ⊗_k M` over any base sends `aₙ` to
  `1 ⊗ b(iₙ)` for infinitely many distinct `iₙ`. The proof is the reading's, with one
  simplification: the reading first reduces to `D(t) = 0`; here `n` is chosen large
  enough that the `b(iₙ)`-coordinate of `D(t)` already vanishes, so the coordinate
  derivation `E` kills `t`, hence `E(t^{n+1}g) = t^{n+1}E(g)`, and the `tⁿ`-coefficient
  of `E(Σ a_m t^m)` is `1`, while `E(Σ a_m t^m)` is itself `0` for `n` large.
* `basisDx`, `no_derivation_extending_d` — page 22's case: `(dx_i)` is a basis of
  `Ω_{k/ℚ}` (polynomial basis, then localisation, which is formally étale), and no
  derivation `D : A → A ⊗_k Ω_{k/ℚ}` satisfies `D(c) = 1 ⊗ dc` on `k`.
* `retraction_of_formallySmooth`, `not_formallySmooth_discrete` — the conclusion the
  reading draws: if `A` were formally smooth over `k` (discrete topology, mathlib's
  `Algebra.FormallySmooth`), Jacobi–Zariski and projectivity of `Ω_{A/k}` would split
  `A ⊗_k Ω_{k/ℚ} → Ω_{A/ℚ}`, and the retraction composed with `d_A` would be such a
  `D`. So `ℚ(x_i)[[t]]` is not formally smooth over `ℚ(x_i)`.
* `not_formallySmooth_of_field` — the same in every characteristic: for a field `K`
  and any base `R` with `Ω_{K/R}` infinite-dimensional, `K[[t]]` is not formally
  smooth over `K` for the discrete topology. Neither characteristic 0 nor the choice
  of `ℚ(x_i)` is used: only a basis of `Ω` containing infinitely many `d aₙ`, which
  over a field can always be extracted from the spanning family `(da)`.

**What the formalisation finds.**

* The hypothesis of 3.4, « tout `A`-module de type fini est de présentation
  finie — par exemple `A` noethérien », is not more general than Noetherian: it
  is *equivalent* to it (`hypothese_iff_noetherien`). If `A/I` is finitely
  presented, the kernel `I` of `A → A/I` is finitely generated. The « par
  exemple » suggests a wider class than there is. The wider class that the
  argument actually reaches is the rings whose *finitely generated ideals* are
  finitely presented — the coherent rings — since the proof of 3.4 only ever
  applies 3.3 to finitely generated ideals (`corollaire3_4_coherent`). That 3.4
  holds for coherent rings is Chase's theorem (1960); the typescript's
  hypothesis is strictly stronger.
* Lemme 3.3 holds over any commutative ring with no further hypothesis, as
  stated.
* The obstruction holds as the reading states it, and the step pages 22–23 carry
  in illegible prose (the reduction to `D(t) = 0` through a finitely generated
  subfield `k_0`) is not needed. The conclusion holds for every field with
  infinite-dimensional `Ω`, in every characteristic, over any base ring.

What this certifies is that the reading holds together at these points, not
that it is what the page says (issue #26).
-/

namespace Grothendieck.Folder22

open TensorProduct LinearMap

universe u

variable {A : Type u} [CommRing A]

section Lemme33

variable {ι : Type*} (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]

/-- The canonical homomorphism `M ⊗_A ∏ P_i → ∏ (M ⊗_A P_i)`. -/
noncomputable abbrev can (M : Type*) [AddCommGroup M] [Module A M] :
    M ⊗[A] (∀ i, P i) →ₗ[A] ∀ i, M ⊗[A] P i :=
  TensorProduct.piRightHom A A M P

/-- The product of the maps `g ⊗ P_i`. -/
noncomputable abbrev piRTensor {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (g : M →ₗ[A] N) : (∀ i, M ⊗[A] P i) →ₗ[A] ∀ i, N ⊗[A] P i :=
  LinearMap.pi fun i => g.rTensor (P i) ∘ₗ LinearMap.proj i

/-- The canonical map is natural in `M`. -/
theorem can_naturality {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (g : M →ₗ[A] N) :
    piRTensor P g ∘ₗ can P M = can P N ∘ₗ g.rTensor (∀ i, P i) := by
  refine TensorProduct.ext' fun m q => ?_
  funext i
  simp

/-- A product of exact sequences is exact. -/
theorem exact_pi {M N Q : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)] [∀ i, AddCommGroup (Q i)]
    [∀ i, Module A (Q i)] {f : ∀ i, M i →ₗ[A] N i} {g : ∀ i, N i →ₗ[A] Q i}
    (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i)
      (LinearMap.pi fun i => g i ∘ₗ LinearMap.proj i) := by
  intro y
  constructor
  · intro hy
    have : ∀ i, ∃ x, f i x = y i := fun i => (h i (y i)).1 (congrFun hy i)
    choose x hx using this
    exact ⟨x, funext hx⟩
  · rintro ⟨x, rfl⟩
    funext i
    exact (h i _).2 ⟨x i, rfl⟩

/-- `(Aⁿ) ⊗ N ≃ Nⁿ`. -/
noncomputable def psi (n : ℕ) (N : Type*) [AddCommGroup N] [Module A N] :
    (Fin n → A) ⊗[A] N ≃ₗ[A] (Fin n → N) :=
  (TensorProduct.comm A (Fin n → A) N).trans (TensorProduct.piScalarRight A A N (Fin n))

theorem psi_tmul (n : ℕ) {N : Type*} [AddCommGroup N] [Module A N] (f : Fin n → A) (x : N) :
    psi n N (f ⊗ₜ x) = fun j => f j • x := by
  simp [psi]

/-- Lemme 3.3 for `M = Aⁿ`, free of finite type. -/
theorem can_bijective_fin (n : ℕ) : Function.Bijective (can (A := A) P (Fin n → A)) := by
  have key : ∀ x i, psi n (P i) (can P (Fin n → A) x i) = fun j => psi n (∀ i, P i) x j i := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul f q => intro i; funext j; simp [psi_tmul]
    | add x y hx hy =>
      intro i; funext j
      simp only [map_add, Pi.add_apply]
      rw [congrFun (hx i) j, congrFun (hy i) j]
  constructor
  · intro x y hxy
    apply (psi n (∀ i, P i)).injective
    funext j i
    have := congrFun (key x i) j
    rw [hxy, key y i] at this
    exact this.symm
  · intro z
    refine ⟨(psi n (∀ i, P i)).symm fun j i => psi n (P i) (z i) j, funext fun i => ?_⟩
    apply (psi n (P i)).injective
    rw [key]
    funext j
    simp

/-- **Lemme 3.3.** For `M` finitely presented, `M ⊗_A ∏ P_i → ∏ (M ⊗_A P_i)` is an
isomorphism. -/
theorem lemme3_3 (M : Type*) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] :
    Function.Bijective (TensorProduct.piRightHom A A M P) := by
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' A M
  exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    (g.rTensor _) (f.rTensor _) (piRTensor P g) (piRTensor P f)
    (can P _) (can P _) (can P M) (can_naturality P g) (can_naturality P f)
    (rTensor_exact _ hfg hf) (exact_pi fun i => rTensor_exact _ hfg hf)
    (can_bijective_fin P m).2 (can_bijective_fin P n) (rTensor_surjective _ hf)
    (fun y => ⟨fun i => (rTensor_surjective (P i) hf (y i)).choose,
      funext fun i => (rTensor_surjective (P i) hf (y i)).choose_spec⟩)

end Lemme33

section Corollaire34

/-- The hypothesis of 3.4: every finitely generated `A`-module is finitely
presented. -/
def Hypothese (A : Type u) [CommRing A] : Prop :=
  ∀ (N : Type u) [AddCommGroup N] [Module A N], Module.Finite A N → Module.FinitePresentation A N

/-- **The hypothesis of 3.4 is exactly Noetherianity.** -/
theorem hypothese_iff_noetherien : Hypothese A ↔ IsNoetherianRing A := by
  refine ⟨fun h => ⟨fun I => ?_⟩, fun _ N _ _ _ => Module.finitePresentation_of_finite A N⟩
  have := h (A ⧸ I) inferInstance
  simpa using Module.FinitePresentation.fg_ker I.mkQ I.mkQ_surjective

/-- **Corollaire 3.4**, in the form its proof uses: if every finitely generated
ideal is finitely presented (a coherent ring), any product of flat modules is
flat. -/
theorem corollaire3_4_coherent
    (hA : ∀ I : Ideal A, I.FG → Module.FinitePresentation A I)
    {ι : Type*} (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module.Flat A (P i)] : Module.Flat A (∀ i, P i) := by
  rw [Module.Flat.iff_rTensor_injective]
  intro I hI
  have := hA I hI
  have hsq := can_naturality P I.subtype
  have h1 : Function.Injective (piRTensor P I.subtype) := fun x y hxy => funext fun i =>
    Module.Flat.rTensor_preserves_injective_linearMap _ I.injective_subtype (congrFun hxy i)
  have hinj : Function.Injective (piRTensor P I.subtype ∘ₗ can P I) := by
    rw [LinearMap.coe_comp]
    exact h1.comp (lemme3_3 P I).1
  rw [hsq, LinearMap.coe_comp] at hinj
  exact hinj.of_comp

/-- **Corollaire 3.4.** If every finitely generated `A`-module is finitely
presented, any product of flat `A`-modules is flat. -/
theorem corollaire3_4 (hA : Hypothese A) {ι : Type*} (P : ι → Type*)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)] [∀ i, Module.Flat A (P i)] :
    Module.Flat A (∀ i, P i) :=
  corollaire3_4_coherent (fun I hI => hA I (Module.Finite.iff_fg.2 hI)) P

end Corollaire34

section Corollaire35

/-- A product of two flat modules is flat (not in mathlib as such). -/
theorem flat_prod (M N : Type*) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Flat A M] [Module.Flat A N] : Module.Flat A (M × N) := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  have hsq : (TensorProduct.prodRight A A A M N).toLinearMap ∘ₗ I.subtype.rTensor (M × N) =
      (I.subtype.rTensor M).prodMap (I.subtype.rTensor N) ∘ₗ
        (TensorProduct.prodRight A A I M N).toLinearMap := by
    refine TensorProduct.ext' fun x m => ?_
    simp
  have h1 : Function.Injective ((I.subtype.rTensor M).prodMap (I.subtype.rTensor N)) :=
    fun x y hxy => Prod.ext
      (Module.Flat.rTensor_preserves_injective_linearMap _ I.injective_subtype
        (congrArg Prod.fst hxy))
      (Module.Flat.rTensor_preserves_injective_linearMap _ I.injective_subtype
        (congrArg Prod.snd hxy))
  have hinj : Function.Injective ((I.subtype.rTensor M).prodMap (I.subtype.rTensor N) ∘ₗ
      (TensorProduct.prodRight A A I M N).toLinearMap) := by
    rw [LinearMap.coe_comp]
    exact h1.comp (TensorProduct.prodRight A A I M N).injective
  rw [← hsq, LinearMap.coe_comp] at hinj
  exact hinj.of_comp

variable (P : ℕ → Type*) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  (π : ∀ n, P (n + 1) →ₗ[A] P n)

/-- The projective limit of `⋯ → P 2 → P 1 → P 0`, as a submodule of the product. -/
def limite : Submodule A (∀ n, P n) where
  carrier := {x | ∀ n, π n (x (n + 1)) = x n}
  add_mem' hx hy n := by simp [hx n, hy n]
  zero_mem' n := by simp
  smul_mem' c x hx n := by simp [hx n]

/-- **Corollaire 3.5** (system indexed by `ℕ`, transition maps surjective). If
every finitely generated `A`-module is finitely presented and every `P n` is
projective, the projective limit is flat. -/
theorem corollaire3_5 (hA : Hypothese A) [∀ n, Module.Projective A (P n)]
    (hπ : ∀ n, Function.Surjective (π n)) : Module.Flat A (limite P π) := by
  -- Each `P (n+1) → P n` splits.
  have hs : ∀ n, ∃ s : P n →ₗ[A] P (n + 1), π n ∘ₗ s = LinearMap.id := fun n =>
    Module.projective_lifting_property (π n) LinearMap.id (hπ n)
  choose s hs using hs
  have hs' : ∀ n x, π n (s n x) = x := fun n x => LinearMap.congr_fun (hs n) x
  let K : ∀ n, Submodule A (P (n + 1)) := fun n => LinearMap.ker (π n)
  -- `K n` is a direct summand of `P (n+1)`, hence projective.
  have hK : ∀ n, Module.Projective A (K n) := fun n =>
    Module.Projective.of_split (K n).subtype
      (LinearMap.codRestrict (K n) (LinearMap.id - s n ∘ₗ π n) fun x => by
        simp [K, hs'])
      (by ext x; simp)
  -- `lim P ≅ P 0 × ∏ K n`.
  let Φ : limite P π →ₗ[A] P 0 × ∀ n, K n :=
    { toFun := fun x => (x.1 0, fun n => ⟨x.1 (n + 1) - s n (x.1 n), by
        simp [K, hs', x.2 n]⟩)
      map_add' := fun x y => by
        ext <;> simp [map_add]; abel
      map_smul' := fun c x => by
        ext <;> simp [smul_sub] }
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro x y hxy
      have h0 : x.1 0 = y.1 0 := congrArg Prod.fst hxy
      have hk : ∀ n, x.1 (n + 1) - s n (x.1 n) = y.1 (n + 1) - s n (y.1 n) := fun n =>
        congrArg Subtype.val (congrFun (congrArg Prod.snd hxy) n)
      apply Subtype.ext
      funext n
      induction n with
      | zero => exact h0
      | succ n ih => have := hk n; rw [ih] at this; exact sub_left_inj.1 this
    · rintro ⟨y, k⟩
      let seq : ∀ n, P n := fun n => Nat.rec (motive := fun n => P n) y
        (fun n xn => s n xn + (k n : P (n + 1))) n
      have hseq : ∀ n, seq (n + 1) = s n (seq n) + k n := fun n => rfl
      refine ⟨⟨seq, fun n => ?_⟩, ?_⟩
      · rw [hseq, map_add, hs', (k n).2, add_zero]
      · ext n
        · rfl
        · simp [Φ, hseq]
  have : Module.Flat A (∀ n, K n) := corollaire3_4 hA _
  have := flat_prod (A := A) (P 0) (∀ n, K n)
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective Φ hΦ)

end Corollaire35

section PowerSeriesObstruction

open PowerSeries

section Obstruction

variable {k : Type*} [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]

/-- The `k⟦t⟧`-linear map `k⟦t⟧ ⊗_k M → k⟦t⟧`, `f ⊗ m ↦ φ(m) f`. -/
noncomputable def coordProj (φ : M →ₗ[k] k) : k⟦X⟧ ⊗[k] M →ₗ[k⟦X⟧] k⟦X⟧ :=
  (TensorProduct.AlgebraTensorModule.rid k k⟦X⟧ k⟦X⟧).toLinearMap ∘ₗ φ.baseChange k⟦X⟧

theorem coordProj_tmul (φ : M →ₗ[k] k) (f : k⟦X⟧) (m : M) : coordProj φ (f ⊗ₜ m) = φ m • f := by
  simp [coordProj]

/-- An element of `k⟦t⟧ ⊗_k M` has only finitely many non-zero coordinates. -/
theorem coordProj_eventually_zero {ι : Type*} (b : Module.Basis ι k M) (z : k⟦X⟧ ⊗[k] M) :
    ∃ s : Finset ι, ∀ i ∉ s, coordProj (b.coord i) z = 0 := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul f m =>
    refine ⟨(b.repr m).support, fun i hi => ?_⟩
    rw [coordProj_tmul, Module.Basis.coord_apply, Finsupp.notMem_support_iff.1 hi, zero_smul]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, fun i hi => ?_⟩
    rw [Finset.mem_union, not_or] at hi
    rw [map_add, hs i hi.1, ht i hi.2, add_zero]

variable {R : Type*} [CommRing R] [Algebra R k]

theorem der_X_pow_mul (E : Derivation R k⟦X⟧ k⟦X⟧) (hX : E X = 0) (m : ℕ) (g : k⟦X⟧) :
    E (X ^ m * g) = X ^ m * E g := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, hX]
  simp

theorem der_C_mul_X_pow (E : Derivation R k⟦X⟧ k⟦X⟧) (hX : E X = 0) (m : ℕ) (c : k) :
    E (C c * X ^ m) = E (C c) * X ^ m := by
  rw [mul_comm, der_X_pow_mul E hX, mul_comm]

/-- `Σ aₙ tⁿ = Σ_{m ≤ n} a_m t^m + t^{n+1} g`. -/
theorem mk_eq_sum_add (a : ℕ → k) (n : ℕ) :
    PowerSeries.mk a = ∑ m ∈ Finset.range (n + 1), C (a m) * X ^ m +
      X ^ (n + 1) * PowerSeries.mk fun j => a (j + (n + 1)) := by
  ext j
  rw [map_add, map_sum, coeff_X_pow_mul']
  simp only [coeff_C_mul_X_pow, coeff_mk, Finset.sum_ite_eq, Finset.mem_range]
  by_cases hj : j < n + 1
  · simp [hj, show ¬ n + 1 ≤ j by omega]
  · simp [hj, show n + 1 ≤ j by omega, Nat.sub_add_cancel (show n + 1 ≤ j by omega)]

/-- **The obstruction (pp. 22, 24).** Let `M` be a free `k`-module with basis `b`, and
`a₀, a₁, …` elements of `k`. There is no derivation `D : k⟦t⟧ → k⟦t⟧ ⊗_k M` (over any base
`R`) with `D(aₙ) = 1 ⊗ b(iₙ)` for infinitely many distinct indices `iₙ`: the coordinate
of `D(Σ aₙ tⁿ)` along `b(iₙ)` has `tⁿ`-coefficient `1` for every `n`. -/
theorem no_derivation [Nontrivial k] {ι : Type*} (b : Module.Basis ι k M) (e : ℕ → ι)
    (he : Function.Injective e) (a : ℕ → k) (D : Derivation R k⟦X⟧ (k⟦X⟧ ⊗[k] M))
    (hD : ∀ n, D (C (a n)) = 1 ⊗ₜ b (e n)) : False := by
  classical
  obtain ⟨s, hs⟩ := coordProj_eventually_zero b (D (PowerSeries.mk a))
  obtain ⟨t, ht⟩ := coordProj_eventually_zero b (D X)
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset ((s ∪ t).preimage e he.injOn)
  rw [Finset.mem_preimage, Finset.mem_union, not_or] at hn
  let E : Derivation R k⟦X⟧ k⟦X⟧ := (coordProj (b.coord (e n))).compDer D
  have hE : ∀ z, E z = coordProj (b.coord (e n)) (D z) := fun _ => rfl
  have hX : E X = 0 := by rw [hE, ht _ hn.2]
  have hC : ∀ m, E (C (a m)) = C (if m = n then 1 else 0) := by
    intro m
    rw [hE, hD, coordProj_tmul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, he.eq_iff]
    split_ifs <;> simp
  have h0 : E (PowerSeries.mk a) = 0 := by rw [hE, hs _ hn.1]
  have h1 := congrArg (coeff n) h0
  rw [mk_eq_sum_add a n, map_add, map_sum, der_X_pow_mul E hX, map_add, map_sum,
    coeff_X_pow_mul', ite_eq_right (by omega)] at h1
  simp only [der_C_mul_X_pow E hX, hC, coeff_C_mul_X_pow] at h1
  simp at h1

end Obstruction

section Discrete

/-- `k = ℚ(x_i : i ∈ I)`. -/
abbrev K (I : Type*) := FractionRing (MvPolynomial I ℚ)

instance (I : Type*) : Algebra.FormallyEtale (MvPolynomial I ℚ) (K I) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial I ℚ))

/-- The generator `x_i` of `k`. -/
noncomputable abbrev x {I : Type*} (i : I) : K I := algebraMap (MvPolynomial I ℚ) (K I) (.X i)

/-- The basis `(dx_i)` of `Ω_{k/ℚ}`: `Ω_k ⊗_k A ≅ A^{(I)}`, as page 22 writes. -/
noncomputable def basisDx (I : Type*) : Module.Basis I (K I) Ω[K I⁄ℚ] :=
  ((KaehlerDifferential.mvPolynomialBasis ℚ I).baseChange (K I)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℚ (MvPolynomial I ℚ) (K I))

theorem basisDx_apply (I : Type*) (i : I) :
    basisDx I i = KaehlerDifferential.D ℚ (K I) (x i) := by
  simp only [basisDx, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply]
  exact (KaehlerDifferential.mapBaseChange_tmul ..).trans
    (by rw [one_smul, KaehlerDifferential.map_D])

/-- **No derivation `D : A → Ω_k ⊗_k A` induces `d_k`** (pp. 22, 24), for `k = ℚ(x_i : i ∈ I)`,
`I` infinite, `A = k[[t]]`. -/
theorem no_derivation_extending_d (I : Type*) [Infinite I] :
    ¬ ∃ D : Derivation ℚ (K I)⟦X⟧ ((K I)⟦X⟧ ⊗[K I] Ω[K I⁄ℚ]),
      ∀ c, D (C c) = 1 ⊗ₜ KaehlerDifferential.D ℚ (K I) c := by
  rintro ⟨D, hD⟩
  let e := Infinite.natEmbedding I
  exact no_derivation (basisDx I) e e.injective
    (fun n => x (e n)) D fun n => by rw [hD, basisDx_apply]

/-- If `S` is formally smooth over `k` (discrete topology), `S ⊗_k Ω_{k/R} → Ω_{S/R}` has a
`S`-linear retraction. -/
theorem retraction_of_formallySmooth (R k S : Type*) [CommRing R] [CommRing k] [CommRing S]
    [Algebra R k] [Algebra R S] [Algebra k S] [IsScalarTower R k S]
    [Algebra.FormallySmooth k S] :
    ∃ r : Ω[S⁄R] →ₗ[S] S ⊗[k] Ω[k⁄R], r ∘ₗ KaehlerDifferential.mapBaseChange R k S =
      LinearMap.id := by
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R k S) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R k S x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  have h := ((KaehlerDifferential.exact_mapBaseChange_map R k S).split_tfae').out 1 2
  exact (h.mp ⟨hinj,
    Module.projective_lifting_property _ _ (KaehlerDifferential.map_surjective R k S)⟩).2

/-- **`k⟦t⟧` is not formally smooth over `k` for the discrete topology** as soon as `Ω_{k/R}`
has a basis containing infinitely many differentials `d aₙ`. -/
theorem not_formallySmooth_of_basis (R k : Type*) [CommRing R] [CommRing k] [Nontrivial k]
    [Algebra R k] {ι : Type*} (b : Module.Basis ι k Ω[k⁄R]) (e : ℕ → ι)
    (he : Function.Injective e) (a : ℕ → k) (ha : ∀ n, KaehlerDifferential.D R k (a n) = b (e n)) :
    ¬ Algebra.FormallySmooth k k⟦X⟧ := by
  intro _
  obtain ⟨r, hr⟩ := retraction_of_formallySmooth R k k⟦X⟧
  refine no_derivation b e he a (r.compDer (KaehlerDifferential.D R k⟦X⟧)) fun n => ?_
  have h := LinearMap.congr_fun hr (1 ⊗ₜ KaehlerDifferential.D R k (a n))
  rw [LinearMap.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul,
    KaehlerDifferential.map_D, LinearMap.id_apply, ha] at h
  simpa using h

/-- **The page's example**: for `k = ℚ(x_i : i ∈ I)`, `I` infinite, `k[[t]]` is not formally
smooth over `k` for the discrete topology. -/
theorem not_formallySmooth_discrete (I : Type*) [Infinite I] :
    ¬ Algebra.FormallySmooth (K I) (K I)⟦X⟧ := by
  let e := Infinite.natEmbedding I
  exact not_formallySmooth_of_basis ℚ (K I) (basisDx I) e e.injective
    (fun n => x (e n)) fun n => (basisDx_apply I _).symm

/-- **The general form, in every characteristic**: for a field `K` and any base ring `R` with
`Ω_{K/R}` infinite-dimensional, `K[[t]]` is not formally smooth over `K` for the discrete
topology. -/
theorem not_formallySmooth_of_field (R K : Type*) [CommRing R] [Field K] [Algebra R K]
    (h : ¬ Module.Finite K Ω[K⁄R]) : ¬ Algebra.FormallySmooth K K⟦X⟧ := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent K (Set.range (KaehlerDifferential.D R K))
  let b : Module.Basis s K Ω[K⁄R] := Module.Basis.mk hli (by
    rw [Subtype.range_coe, hspan, KaehlerDifferential.span_range_derivation])
  have : Infinite s := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    exact h (Module.Finite.of_basis b)
  let e := Infinite.natEmbedding s
  have ha : ∀ n, ∃ c, KaehlerDifferential.D R K c = (e n : Ω[K⁄R]) := fun n => hs (e n).2
  choose a ha using ha
  exact not_formallySmooth_of_basis R K b e e.injective a fun n => by
    rw [ha, Module.Basis.mk_apply]

end Discrete

end PowerSeriesObstruction

end Grothendieck.Folder22
