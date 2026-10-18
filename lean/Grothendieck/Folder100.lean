import Mathlib

/-!
# Folder 100, pages 36–38: points of dimension one avoiding countably many divisors

The modernised reading `transcripts/100/100.modern.tex` (« Un argument de Baire ») gives the
Corollary of page 38: in an integral complete local scheme, countably many nowhere-dense closed
subsets miss some point of dimension one. The proof reduces to `Θ = V⟦T₁, …, Tₙ⟧`, `V` a complete
discrete valuation ring, parametrises the `V`-homomorphisms `Θ → V` by `𝔪ⁿ` and concludes by
Baire. This file proves the case `n = 1`, `Θ = V⟦T⟧` of dimension `2`, which is the reachable
part of finding `100-baire-dimension-one-points` of `src/content/findings.ts`.

* `quotEquiv`: for `a ∈ 𝔪`, `V⟦T⟧ ⧸ (T − a) ≃ V` (`T − a` is a distinguished polynomial, so the
  quotient is `V[T] ⧸ (T − a)`); the kernel `(T − a)` of `T ↦ a` is a point of dimension one.
* `exists_poly_mul_unit`: a nonzero `f ∈ V⟦T⟧` is `Q · u` with `Q` a nonzero polynomial and `u`
  a unit — `f = ϖ^v g` with `g` of unit content (`exists_content`), then Weierstrass
  preparation for `g`.
* `finite_bad`: `f ∈ (T − a)` iff `Q(a) = 0`, so only finitely many `a` are bad for `f ≠ 0`.
* `uncountable`: a complete discrete valuation ring is uncountable (the series
  `∑ εᵢ ϖⁱ`, `εᵢ ∈ {0, 1}`, are pairwise distinct).
* `exists_avoid`: for countably many nonzero `fᵢ ∈ V⟦T⟧` there is `a ∈ 𝔪` with `fᵢ ∉ (T − a)`
  for every `i`. Countability of the bad set replaces Baire: each `fᵢ` excludes finitely many
  `a`, and `𝔪 = ϖV` is uncountable.

Not formalised: the case of several variables, where the bad set of one `f` is no longer
finite and Baire is needed; the reduction of a complete local domain to a finite extension of
`V⟦T₁, …, Tₙ⟧` (Cohen) and the lifting of points along it; the Proposition of page 36.
-/

namespace Grothendieck.Folder100

open IsLocalRing
open scoped Polynomial PowerSeries

variable {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

/-- `T − a`, for `a ∈ 𝔪`, is distinguished. -/
lemma isDistinguishedAt {a : V} (ha : a ∈ maximalIdeal V) :
    (Polynomial.X - Polynomial.C a).IsDistinguishedAt (maximalIdeal V) where
  mem {n} hn := by
    rw [Polynomial.natDegree_X_sub_C, Nat.lt_one_iff] at hn
    subst hn
    simpa using ha
  monic := Polynomial.monic_X_sub_C a

omit [IsDomain V] [IsDiscreteValuationRing V] in
lemma coe_X_sub_C (a : V) :
    ((Polynomial.X - Polynomial.C a : V[X]) : V⟦X⟧) = PowerSeries.X - PowerSeries.C a := by
  simp

variable [IsAdicComplete (maximalIdeal V) V]

/-- `V⟦T⟧ ⧸ (T − a) ≃ V` for `a ∈ 𝔪`. -/
noncomputable def quotEquiv {a : V} (ha : a ∈ maximalIdeal V) :
    (V⟦X⟧ ⧸ Ideal.span {PowerSeries.X - PowerSeries.C a}) ≃ₐ[V] V :=
  (Ideal.quotientEquivAlgOfEq V (by rw [coe_X_sub_C])).trans
    ((isDistinguishedAt ha).algEquivQuotient.symm.trans (Polynomial.quotientSpanXSubCAlgEquiv a))

/-- A polynomial lies in `(T − a) ⊂ V⟦T⟧` iff it vanishes at `a`. -/
lemma coe_mem_iff {a : V} (ha : a ∈ maximalIdeal V) (Q : V[X]) :
    (Q : V⟦X⟧) ∈ Ideal.span {PowerSeries.X - PowerSeries.C a} ↔ Q.IsRoot a := by
  have e : (isDistinguishedAt ha).algEquivQuotient (Ideal.Quotient.mk _ Q) =
      Ideal.Quotient.mk _ (Q : V⟦X⟧) := rfl
  rw [← coe_X_sub_C, ← Ideal.Quotient.eq_zero_iff_mem, ← e,
    map_eq_zero_iff _ (AlgEquiv.injective _),
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]

omit [IsAdicComplete (maximalIdeal V) V] in
/-- The content: a nonzero `f` is `ϖ^v g` with `g` not zero modulo `𝔪`. -/
lemma exists_content {ϖ : V} (hϖ : Irreducible ϖ) {f : V⟦X⟧} (hf : f ≠ 0) :
    ∃ (v : ℕ) (g : V⟦X⟧), f = PowerSeries.C (ϖ ^ v) * g ∧ g.map (residue V) ≠ 0 := by
  have hex : ∃ v k, ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff k f := by
    obtain ⟨k, hk⟩ : ∃ k, PowerSeries.coeff k f ≠ 0 := by
      by_contra! h
      exact hf (PowerSeries.ext fun n => by simpa using h n)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hk hϖ
    refine ⟨n, k, fun h => hϖ.not_isUnit ?_⟩
    rw [hu, pow_succ, mul_comm (u : V), mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)] at h
    exact isUnit_of_dvd_unit h u.isUnit
  classical
  have hdvd : ∀ k, ϖ ^ Nat.find hex ∣ PowerSeries.coeff k f := by
    intro k
    rcases h : Nat.find hex with _ | w
    · simp
    · by_contra hk
      exact Nat.find_min hex (h ▸ Nat.lt_succ_self w) ⟨k, hk⟩
  choose c hc using hdvd
  obtain ⟨k, hk⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, PowerSeries.mk c, PowerSeries.ext fun n => by
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc], fun h0 => ?_⟩
  have h1 := congrArg (PowerSeries.coeff k) h0
  rw [PowerSeries.coeff_map, map_zero, residue_eq_zero_iff,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton,
    PowerSeries.coeff_mk] at h1
  exact hk (by rw [hc k, pow_succ]; exact mul_dvd_mul_left _ h1)

/-- A nonzero `f ∈ V⟦T⟧` is a nonzero polynomial times a unit. -/
theorem exists_poly_mul_unit {f : V⟦X⟧} (hf : f ≠ 0) :
    ∃ (Q : V[X]) (u : V⟦X⟧), Q ≠ 0 ∧ IsUnit u ∧ f = Q * u := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, g, rfl, hg⟩ := exists_content hϖ hf
  obtain ⟨P, u, H⟩ := g.exists_isWeierstrassFactorization hg
  refine ⟨Polynomial.C (ϖ ^ v) * P, u, mul_ne_zero (by simpa using pow_ne_zero v hϖ.ne_zero)
    H.isDistinguishedAt.monic.ne_zero, H.isUnit, ?_⟩
  rw [H.eq_mul, Polynomial.coe_mul, Polynomial.coe_C, mul_assoc]

/-- A nonzero `f` lies in `(T − a)` for finitely many `a ∈ 𝔪` only. -/
theorem finite_bad {f : V⟦X⟧} (hf : f ≠ 0) :
    {a | a ∈ maximalIdeal V ∧ f ∈ Ideal.span {PowerSeries.X - PowerSeries.C a}}.Finite := by
  obtain ⟨Q, u, hQ, hu, rfl⟩ := exists_poly_mul_unit hf
  refine (Polynomial.finite_setOfPred_isRoot hQ).subset fun a ⟨ha, hm⟩ => (coe_mem_iff ha Q).1 ?_
  simpa [Ideal.mul_unit_mem_iff_mem _ hu] using hm

/-- The partial sums `∑_{i < n} εᵢ ϖⁱ`. -/
def psum (ϖ : V) (ε : ℕ → Bool) (n : ℕ) : V := ∑ i ∈ Finset.range n, if ε i then ϖ ^ i else 0

/-- A complete discrete valuation ring is uncountable: `ε ↦ ∑ εᵢ ϖⁱ` is injective on
`{0, 1}^ℕ`. -/
theorem uncountable : Uncountable V := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hm : ∀ n : ℕ, maximalIdeal V ^ n = Ideal.span {ϖ ^ n} := fun n => by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow]
  have hsm : ∀ (x y : V) n, x ≡ y [SMOD (maximalIdeal V ^ n • ⊤ : Submodule V V)] ↔
      ϖ ^ n ∣ x - y := fun x y n => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hm, Ideal.mem_span_singleton]
  have hs : ∀ ε {m n : ℕ}, m ≤ n → ϖ ^ m ∣ psum ϖ ε n - psum ϖ ε m := fun ε m n hmn => by
    rw [psum, psum, ← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
    exact Finset.dvd_sum fun i hi => by
      split_ifs
      · exact pow_dvd_pow ϖ (Finset.mem_Ico.1 hi).1
      · exact dvd_zero _
  have hL : ∀ ε, ∃ L, ∀ n, ϖ ^ n ∣ psum ϖ ε n - L := fun ε => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := maximalIdeal V) inferInstance (f := psum ϖ ε)
      fun {m n} hmn => (hsm _ _ _).2 (by rw [← neg_sub, dvd_neg]; exact hs ε hmn)
    exact ⟨L, fun n => (hsm _ _ _).1 (hL n)⟩
  choose L hL using hL
  have hinj : Function.Injective L := fun ε ε' h => by
    by_contra hne
    have hex : ∃ j, ε j ≠ ε' j := not_forall.1 fun h' => hne (funext h')
    classical
    set j := Nat.find hex
    have hd : psum ϖ ε (j + 1) - psum ϖ ε' (j + 1) =
        (if ε j then ϖ ^ j else 0) - if ε' j then ϖ ^ j else 0 := by
      have hsum : ∑ i ∈ Finset.range j, (if ε i then ϖ ^ i else 0) =
          ∑ i ∈ Finset.range j, (if ε' i then ϖ ^ i else 0) :=
        Finset.sum_congr rfl fun i hi => by
          rw [not_not.1 (Nat.find_min hex (Finset.mem_range.1 hi))]
      simp only [psum, Finset.sum_range_succ, hsum]
      ring
    have h1 : ϖ ^ (j + 1) ∣ psum ϖ ε (j + 1) - psum ϖ ε' (j + 1) := by
      have := dvd_sub (hL ε (j + 1)) (hL ε' (j + 1))
      rwa [h, sub_sub_sub_cancel_right] at this
    have h2 : ϖ ^ (j + 1) ∣ ϖ ^ j := by
      have hj : ε j ≠ ε' j := Nat.find_spec hex
      rw [hd] at h1
      cases hε : ε j <;> cases hε' : ε' j <;> simp only [hε, hε'] at h1 hj <;>
        simp_all [dvd_neg]
    exact absurd ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h2) (by omega)
  have : Uncountable (ℕ → Bool) := by
    rw [← Cardinal.aleph0_lt_mk_iff, ← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat]
    exact Cardinal.cantor _
  exact hinj.uncountable

/-- The Corollary of page 38 for `Θ = V⟦T⟧`: for countably many nonzero `fᵢ ∈ V⟦T⟧` there is
`a ∈ 𝔪` with `fᵢ ∉ (T − a)` for every `i`; `V⟦T⟧ ⧸ (T − a) ≃ V` by `quotEquiv`, so `(T − a)` is
a point of dimension one outside every `V(fᵢ)`. -/
theorem exists_avoid {ι : Type*} [Countable ι] (f : ι → V⟦X⟧) (hf : ∀ i, f i ≠ 0) :
    ∃ a ∈ maximalIdeal V, ∀ i, f i ∉ Ideal.span {PowerSeries.X - PowerSeries.C a} := by
  by_contra! h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hc : (⋃ i, {a | a ∈ maximalIdeal V ∧
      f i ∈ Ideal.span {PowerSeries.X - PowerSeries.C a}}).Countable :=
    Set.countable_iUnion fun i => (finite_bad (hf i)).countable
  have hϖm : ϖ ∈ maximalIdeal V := hϖ.not_isUnit
  have : Countable V := by
    have := hc.to_subtype
    refine Function.Injective.countable (f := fun x : V => (⟨ϖ * x, ?_⟩ : ↥(⋃ i, {a |
      a ∈ maximalIdeal V ∧ f i ∈ Ideal.span {PowerSeries.X - PowerSeries.C a}}))) ?_
    · obtain ⟨i, hi⟩ := h (ϖ * x) (Ideal.mul_mem_right x _ hϖm)
      exact Set.mem_iUnion.2 ⟨i, Ideal.mul_mem_right x _ hϖm, hi⟩
    · intro x y hxy
      exact mul_left_cancel₀ hϖ.ne_zero (congrArg Subtype.val hxy)
  have hu : Uncountable V := uncountable
  exact not_countable this

end Grothendieck.Folder100
