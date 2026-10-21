import Mathlib

/-!
# Bourbaki rédaction n° 457: degree and number of points in infinite degree

Rédaction n° 457 (October 1965) of the Bourbaki archive is a project for a new edition of
chapter V of *Algèbre*, on commutative fields (Archives Henri Poincaré, item
<https://archives-bourbaki.ahp-numerique.fr/items/show/792>, whose notice names Grothendieck as
author). On PDF pp. 32–33, Bourbaki, rédaction n° 457, Cor. 6 of Prop. 14 concerns a
commutative algebra `A` over a field `k` that is integral and separable (by Prop. 14, a
filtered union of étale subalgebras), an algebraically closed extension `Ω` of `k`, and the
set `P(A)` of `k`-algebra maps `A → Ω`. It equates the degree `[A : k]` with the cardinal of
`P(A)`, and adds that `A` has finite degree if and only if `P(A)` is finite.

In finite degree the equality is the classical count of the points of an étale algebra. In
infinite degree it fails. The proof on the page only shows that `P(A)` is infinite, and its
typed N.B. concedes that « card » has been given the single value `∞` for infinite sets; a
reader's ink margin notes that a countable degree can come with a continuum of points.

This file proves that the equality fails, with one explicit algebra. Write `C = ℕ → Bool` for
the Cantor set and let `A ⊆ (C → k)` be the functions that depend on finitely many
coordinates. These are exactly the locally constant functions `C → k` for the product
topology (`C` is compact and its clopen sets are the finite unions of cylinders); that
identification is not formalised here, and `A` is defined directly.

* `cantorAlg`: the `k`-subalgebra `A`;
* `exists_separable_splits`: every element of `A` is a root of a separable polynomial that
  splits over `k`, so each `k[f]` is étale: `A` is integral and separable in the sense of
  the page;
* `rank_le_aleph0`: `[A : k] ≤ ℵ₀`, the indicators of the cylinders spanning `A`;
* `continuum_le_card_points`: for any nontrivial `k`-algebra `Ω` (an algebraically closed
  extension in particular), evaluation at the points of `C` gives `𝔠` distinct
  `k`-algebra maps `A → Ω`;
* `rank_lt_card_points`, `not_corollary6`: hence `[A : k] < card P(A)`, and Cor. 6 fails as
  an equality of cardinals.

The degree of `A` is in fact `ℵ₀` and, for `Ω` a field, `P(A)` is in bijection with `C`; Lean
proves only the two inequalities, which is all the refutation needs. The finite-degree case of
Cor. 6 and its last assertion (finite degree if and only if `P(A)` finite), which are true, are
not formalised.
-/

open Cardinal Polynomial Function

namespace Grothendieck.Bourbaki457

/-- The Cantor set, as the space of binary sequences. -/
abbrev Cantor := ℕ → Bool

variable (k : Type*) [Field k]

/-- The `k`-algebra of functions on the Cantor set that depend on finitely many coordinates
(the locally constant functions). -/
def cantorAlg : Subalgebra k (Cantor → k) where
  carrier := {f | ∃ n, DependsOn f (Set.Iio n)}
  mul_mem' := by
    rintro f g ⟨m, hf⟩ ⟨n, hg⟩
    exact ⟨max m n, fun x y h ↦ congr_arg₂ (· * ·)
      (hf fun i hi ↦ h i (lt_max_of_lt_left hi : i < max m n))
      (hg fun i hi ↦ h i (lt_max_of_lt_right hi : i < max m n))⟩
  add_mem' := by
    rintro f g ⟨m, hf⟩ ⟨n, hg⟩
    exact ⟨max m n, fun x y h ↦ congr_arg₂ (· + ·)
      (hf fun i hi ↦ h i (lt_max_of_lt_left hi : i < max m n))
      (hg fun i hi ↦ h i (lt_max_of_lt_right hi : i < max m n))⟩
  algebraMap_mem' c := ⟨0, fun _ _ _ ↦ rfl⟩

variable {k}

universe u v

/-- Extend a word of length `n` by zeros. -/
def extendWord {n : ℕ} (v : Fin n → Bool) : Cantor :=
  fun i ↦ if h : i < n then v ⟨i, h⟩ else false

/-- The indicator function of the cylinder of the sequences beginning with the word `v`. -/
def cyl {n : ℕ} (v : Fin n → Bool) : Cantor → k :=
  fun z ↦ if (fun i : Fin n ↦ z i) = v then 1 else 0

omit [Field k] in
theorem eq_extendWord {n : ℕ} {f : Cantor → k} (hf : DependsOn f (Set.Iio n)) (z : Cantor) :
    f z = f (extendWord fun i : Fin n ↦ z i) :=
  hf fun i hi ↦ by simp [extendWord, Set.mem_Iio.1 hi]

/-- A function depending on the first `n` coordinates is a combination of cylinder
indicators. -/
theorem eq_sum_cyl {n : ℕ} {f : Cantor → k} (hf : DependsOn f (Set.Iio n)) :
    f = ∑ v : Fin n → Bool, f (extendWord v) • cyl v := by
  ext z
  rw [Finset.sum_apply, Finset.sum_eq_single (fun i : Fin n ↦ z i)]
  · simp [cyl, ← eq_extendWord hf]
  · intro v _ hv
    simp [cyl, Ne.symm hv]
  · simp

/-- Every element of `A` is a root of a separable polynomial that splits over `k`. -/
theorem exists_separable_splits (f : cantorAlg k) :
    ∃ p : k[X], p.Monic ∧ p.Separable ∧ p.Splits ∧ aeval f p = 0 := by
  classical
  obtain ⟨f, n, hf⟩ := f
  let s : Finset k := Finset.univ.image fun v : Fin n → Bool ↦ f (extendWord v)
  refine ⟨∏ c ∈ s, (X - C c), monic_prod_of_monic _ _ fun c _ ↦ monic_X_sub_C c,
    separable_prod_X_sub_C_iff'.2 fun _ _ _ _ ↦ id,
    Splits.prod fun c _ ↦ Splits.X_sub_C c, Subtype.ext ?_⟩
  ext z
  simp only [Polynomial.aeval_subalgebra_coe, Subalgebra.coe_zero, Pi.zero_apply]
  rw [show (aeval f) (∏ c ∈ s, (X - C c)) z = aeval (f z) (∏ c ∈ s, (X - C c)) from
    (aeval_algHom_apply (Pi.evalAlgHom k (fun _ ↦ k) z) f _).symm]
  simp only [map_prod, map_sub, aeval_X, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  exact Finset.prod_eq_zero (s := s)
    (Finset.mem_image.2 ⟨_, Finset.mem_univ _, (eq_extendWord hf z).symm⟩)
    (sub_self _)

instance : Algebra.IsIntegral k (cantorAlg k) :=
  ⟨fun f ↦ let ⟨p, hm, _, _, hp⟩ := exists_separable_splits f; ⟨p, hm, hp⟩⟩

/-- The degree of `A` over `k` is at most countable. -/
theorem rank_le_aleph0 : Module.rank k (cantorAlg k) ≤ ℵ₀ := by
  let S : Set (Cantor → k) := Set.range fun p : Σ n, Fin n → Bool ↦ cyl p.2
  have hle : Subalgebra.toSubmodule (cantorAlg k) ≤ Submodule.span k S := by
    rintro f ⟨n, hf⟩
    rw [eq_sum_cyl hf]
    exact Submodule.sum_mem _ fun v _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨n, v⟩, rfl⟩)
  rw [← Subalgebra.rank_toSubmodule]
  exact (Submodule.rank_mono hle).trans <| (rank_span_le S).trans <|
    mk_le_aleph0_iff.2 (Set.countable_range _).to_subtype

variable (k) in
/-- Evaluation at a point of the Cantor set, as a `k`-algebra map `A → Ω`. -/
def eval (Ω : Type*) [Ring Ω] [Algebra k Ω] (x : Cantor) : cantorAlg k →ₐ[k] Ω :=
  (Algebra.ofId k Ω).comp ((Pi.evalAlgHom k (fun _ ↦ k) x).comp (cantorAlg k).val)

/-- Distinct points give distinct `k`-algebra maps `A → Ω`. -/
theorem eval_injective (Ω : Type*) [Ring Ω] [Nontrivial Ω] [Algebra k Ω] :
    Injective (eval k Ω) := by
  intro x y hxy
  by_contra hne
  obtain ⟨n, hn⟩ := Function.ne_iff.1 hne
  let f : cantorAlg k := ⟨fun z ↦ if z n then 1 else 0, n + 1, fun a b h ↦ by
    simp [h n (Set.mem_Iio.2 n.lt_succ_self)]⟩
  have h : algebraMap k Ω (if x n then 1 else 0) = algebraMap k Ω (if y n then 1 else 0) :=
    DFunLike.congr_fun hxy f
  cases hx : x n <;> cases hy : y n <;> simp [hx, hy] at h hn

/-- The set `P(A)` of `k`-algebra maps `A → Ω` has at least the cardinality of the
continuum. -/
theorem continuum_le_card_points {k : Type u} [Field k] (Ω : Type v) [Ring Ω] [Nontrivial Ω]
    [Algebra k Ω] : 𝔠 ≤ #(cantorAlg k →ₐ[k] Ω) := by
  have : #Cantor = 𝔠 := by rw [← power_def, mk_bool, mk_nat, two_power_aleph0]
  simpa [this] using lift_mk_le_lift_mk_of_injective (eval_injective (k := k) Ω)

/-- The degree of `A` is strictly smaller than the cardinal of `P(A)`. -/
theorem rank_lt_card_points {k : Type u} [Field k] (Ω : Type v) [Ring Ω] [Nontrivial Ω]
    [Algebra k Ω] : lift.{v} (Module.rank k (cantorAlg k)) < #(cantorAlg k →ₐ[k] Ω) :=
  calc lift.{v} (Module.rank k (cantorAlg k)) ≤ ℵ₀ := lift_le_aleph0.2 rank_le_aleph0
    _ < 𝔠 := aleph0_lt_continuum
    _ ≤ _ := continuum_le_card_points Ω

/-- Cor. 6 of rédaction n° 457 fails as an equality of cardinals: for every field `k` and every
algebraically closed extension `Ω`, there is an integral `k`-algebra all of whose elements are
roots of separable split polynomials, whose degree differs from the cardinal of the set of
`k`-algebra maps into `Ω`. -/
theorem not_corollary6 {k : Type u} [Field k] (Ω : Type v) [Field Ω] [Algebra k Ω]
    [IsAlgClosed Ω] : ∃ A : Subalgebra k (Cantor → k), Algebra.IsIntegral k A ∧
      (∀ f : A, ∃ p : k[X], p.Separable ∧ p.Splits ∧ aeval f p = 0) ∧
      lift.{v} (Module.rank k A) ≠ #(A →ₐ[k] Ω) :=
  ⟨cantorAlg k, inferInstance,
    fun f ↦ let ⟨p, _, hs, hp, h⟩ := exists_separable_splits f; ⟨p, hs, hp, h⟩,
    (rank_lt_card_points Ω).ne⟩

end Grothendieck.Bourbaki457
