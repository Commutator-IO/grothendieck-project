import Mathlib

/-!
# Quillen, notebook 1983-4, pp. 71–72: the cohomological equation on the torus

Daniel Quillen's notebook 1983-4 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201983/1983-4.pdf>) computes, on
pp. 71–72, the Picard group of the orbit topos of the Kronecker foliation of slope `θ`. The first
step is the first cohomology of the sheaf of smooth functions constant along the leaves, computed
from the operator `θ ∂_x - ∂_y` on `C^∞(T²)`: on the exponential `e^{2πi(mx + ny)}` it acts by the
scalar `2πi (θ m - n)`, which vanishes only at `(m, n) = (0, 0)`, and the notebook concludes that
the operator is onto the functions of mean zero. That step silently needs a small-divisor bound:
the cokernel is one-dimensional exactly when `θ` is Diophantine (the cohomological equation on the
torus; Arnold, Herman, Katok; for the foliation, El Kacimi Alaoui 1983 and Haefliger 1980).

Smooth functions on `T²` are the rapidly decreasing families of Fourier coefficients on `ℤ²`, so
this file works with sequences on `ℤ × ℤ` and needs no Fourier analysis. The constant `2π` is
dropped from the symbol. A family `a` is rapidly decreasing when `‖a p‖ (1 + |m| + |n|)^k` is
bounded for every `k`; for real `θ`, the multiplier is `i (θ m - n)`.

* `weight`, `one_le_weight`, `weight_pos`: the weight `1 + |m| + |n|` on `ℤ × ℤ`;
* `IsRapidDecay`: rapidly decreasing families `ℤ × ℤ → ℂ`;
* `IsDiophantine`: `∃ C > 0, ∃ N, |θ m - n| ≥ C / |m|^N` for all `m ≠ 0` and all `n`;
* `symbol`: the multiplier `i (θ m - n)`;
* `norm_symbol`, `symbol_zero`, `norm_symbol_le`: its size, its zero at the origin, its growth;
* `IsRapidDecay.symbol_mul`: the operator maps rapidly decreasing families to rapidly decreasing
  families, with vanishing `(0, 0)` coefficient by `symbol_zero`;
* `IsDiophantine.lower_bound`: the small-divisor bound `c ≤ ‖symbol θ p‖ weight(p)^N`, `p ≠ 0`;
* `IsDiophantine.symbol_ne_zero`: for Diophantine `θ` the multiplier vanishes only at `0`;
* `IsDiophantine.isRapidDecay_div`, `IsDiophantine.symbol_mul_div`: if `θ` is Diophantine and
  `b` is rapidly decreasing with `b (0, 0) = 0`, then `b / symbol θ` is a rapidly decreasing
  preimage of `b`;
* `exists_not_mem_range_of_not_isDiophantine`: if `θ` is irrational and not Diophantine, some
  rapidly decreasing `b` with `b (0, 0) = 0` has no rapidly decreasing preimage;
* `surjective_iff_isDiophantine`: for irrational `θ`, the operator is onto the rapidly decreasing
  families with vanishing `(0, 0)` coefficient iff `θ` is Diophantine;
* `not_isDiophantine_of_liouville`, `exists_not_mem_range_of_liouville`: the case of a Liouville
  number.
-/

namespace Quillen.Notebook1983_4

open Complex Filter

/-- The weight `1 + |m| + |n|` on `ℤ × ℤ`. -/
noncomputable def weight (p : ℤ × ℤ) : ℝ := 1 + |(p.1 : ℝ)| + |(p.2 : ℝ)|

theorem one_le_weight (p : ℤ × ℤ) : 1 ≤ weight p := by
  unfold weight; linarith [abs_nonneg (p.1 : ℝ), abs_nonneg (p.2 : ℝ)]

theorem weight_pos (p : ℤ × ℤ) : 0 < weight p := one_pos.trans_le (one_le_weight p)

/-- A family `a : ℤ × ℤ → ℂ` is rapidly decreasing when `‖a p‖ weight(p)^k` is bounded for every
`k`, that is, `‖a p‖ ≤ C_k (1 + |m| + |n|)^(-k)`. -/
def IsRapidDecay (a : ℤ × ℤ → ℂ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ p, ‖a p‖ * weight p ^ k ≤ C

/-- The real number `θ` is Diophantine: `|θ m - n| ≥ C / |m|^N` for some `C > 0`, some `N`, all
`m ≠ 0` and all `n`. -/
def IsDiophantine (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ m n : ℤ, m ≠ 0 → C / |(m : ℝ)| ^ N ≤ |θ * m - n|

/-- The multiplier `i (θ m - n)` of `θ ∂_x - ∂_y` on Fourier coefficients (up to `2π`). -/
noncomputable def symbol (θ : ℝ) (p : ℤ × ℤ) : ℂ := I * ((θ * p.1 - p.2 : ℝ) : ℂ)

variable {θ : ℝ}

theorem norm_symbol (θ : ℝ) (p : ℤ × ℤ) : ‖symbol θ p‖ = |θ * p.1 - p.2| := by
  rw [symbol, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

@[simp] theorem symbol_zero (θ : ℝ) : symbol θ 0 = 0 := by simp [symbol]

theorem norm_symbol_le (θ : ℝ) (p : ℤ × ℤ) : ‖symbol θ p‖ ≤ (|θ| + 1) * weight p := by
  rw [norm_symbol]
  have h1 : |θ * p.1 - p.2| ≤ |θ| * |(p.1 : ℝ)| + |(p.2 : ℝ)| := by
    rw [← abs_mul]; exact abs_sub _ _
  have h2 := one_le_weight p
  unfold weight at h2 ⊢
  nlinarith [abs_nonneg θ, abs_nonneg (p.1 : ℝ), abs_nonneg (p.2 : ℝ)]

/-- The operator maps rapidly decreasing families to rapidly decreasing families. -/
theorem IsRapidDecay.symbol_mul {a : ℤ × ℤ → ℂ} (ha : IsRapidDecay a) (θ : ℝ) :
    IsRapidDecay fun p => symbol θ p * a p := by
  intro k
  obtain ⟨C, hC⟩ := ha (k + 1)
  refine ⟨(|θ| + 1) * C, fun p => ?_⟩
  have h1 := norm_symbol_le θ p
  have h2 := hC p
  have hw := weight_pos p
  rw [norm_mul, pow_succ] at *
  have h3 : 0 ≤ ‖a p‖ * weight p ^ k := by positivity
  calc ‖symbol θ p‖ * ‖a p‖ * weight p ^ k ≤ (|θ| + 1) * weight p * ‖a p‖ * weight p ^ k := by
        gcongr
    _ = (|θ| + 1) * (‖a p‖ * (weight p ^ k * weight p)) := by ring
    _ ≤ (|θ| + 1) * C := by gcongr

/-- The small-divisor bound: for Diophantine `θ`, `c ≤ ‖symbol θ p‖ weight(p)^N` for `p ≠ 0`. -/
theorem IsDiophantine.lower_bound (hθ : IsDiophantine θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ p : ℤ × ℤ, p ≠ 0 → c ≤ ‖symbol θ p‖ * weight p ^ N := by
  obtain ⟨C, hC, N, h⟩ := hθ
  refine ⟨min C 1, lt_min hC one_pos, N, fun p hp => ?_⟩
  rw [norm_symbol]
  have hw1 := one_le_weight p
  by_cases hm : p.1 = 0
  · have hn : p.2 ≠ 0 := fun hn => hp (Prod.ext hm hn)
    have hn1 : (1 : ℝ) ≤ |(p.2 : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    rw [hm]
    simp only [Int.cast_zero, mul_zero, zero_sub, abs_neg]
    calc min C 1 ≤ 1 := min_le_right _ _
      _ ≤ |(p.2 : ℝ)| * 1 := by linarith
      _ ≤ |(p.2 : ℝ)| * weight p ^ N := by gcongr; exact one_le_pow₀ hw1
  · have hm1 : (1 : ℝ) ≤ |(p.1 : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    have hpos : 0 < |(p.1 : ℝ)| ^ N := by positivity
    have h1 := h p.1 p.2 hm
    rw [div_le_iff₀ hpos] at h1
    have hmw : |(p.1 : ℝ)| ≤ weight p := by
      unfold weight; linarith [abs_nonneg (p.2 : ℝ)]
    calc min C 1 ≤ C := min_le_left _ _
      _ ≤ |θ * p.1 - p.2| * |(p.1 : ℝ)| ^ N := h1
      _ ≤ |θ * p.1 - p.2| * weight p ^ N := by gcongr

/-- For Diophantine `θ` the multiplier vanishes only at the origin. -/
theorem IsDiophantine.symbol_ne_zero (hθ : IsDiophantine θ) {p : ℤ × ℤ} (hp : p ≠ 0) :
    symbol θ p ≠ 0 := by
  obtain ⟨c, hc, N, h⟩ := hθ.lower_bound
  intro h0
  linarith [h p hp, show ‖symbol θ p‖ * weight p ^ N = 0 by simp [h0]]

/-- (⇐) For Diophantine `θ` and rapidly decreasing `b` with `b (0, 0) = 0`, the family
`b / symbol θ` (zero at the origin) is rapidly decreasing. -/
theorem IsDiophantine.isRapidDecay_div (hθ : IsDiophantine θ) {b : ℤ × ℤ → ℂ}
    (hb : IsRapidDecay b) (hb0 : b 0 = 0) : IsRapidDecay fun p => b p / symbol θ p := by
  obtain ⟨c, hc, N, hlow⟩ := hθ.lower_bound
  intro k
  obtain ⟨B, hB⟩ := hb (k + N)
  have hB0 : 0 ≤ B := le_trans (by have := weight_pos 0; positivity) (hB 0)
  refine ⟨B / c, fun p => ?_⟩
  by_cases hp : p = 0
  · subst hp; simp only [hb0, zero_div, norm_zero, zero_mul]; exact div_nonneg hB0 hc.le
  have hl := hlow p hp
  have hσ : 0 < ‖symbol θ p‖ := norm_pos_iff.2 (hθ.symbol_ne_zero hp)
  have hb' := hB p
  have hw := weight_pos p
  rw [norm_div, div_mul_eq_mul_div, div_le_div_iff₀ hσ hc]
  rw [pow_add] at hb'
  have h0 : 0 ≤ ‖b p‖ * weight p ^ k := by positivity
  calc ‖b p‖ * weight p ^ k * c ≤ ‖b p‖ * weight p ^ k * (‖symbol θ p‖ * weight p ^ N) := by
        gcongr
    _ = ‖b p‖ * (weight p ^ k * weight p ^ N) * ‖symbol θ p‖ := by ring
    _ ≤ B * ‖symbol θ p‖ := by gcongr

/-- (⇐) The family `b / symbol θ` is a preimage of `b` when `b (0, 0) = 0`. -/
theorem IsDiophantine.symbol_mul_div (hθ : IsDiophantine θ) {b : ℤ × ℤ → ℂ} (hb0 : b 0 = 0)
    (p : ℤ × ℤ) : symbol θ p * (b p / symbol θ p) = b p := by
  by_cases hp : p = 0
  · subst hp; simp [hb0]
  · exact mul_div_cancel₀ _ (hθ.symbol_ne_zero hp)

/-- (⇒) For irrational, non-Diophantine `θ`, some rapidly decreasing `b` with `b (0, 0) = 0` has
no rapidly decreasing preimage under the operator. -/
theorem exists_not_mem_range_of_not_isDiophantine (hirr : Irrational θ)
    (hθ : ¬ IsDiophantine θ) :
    ∃ b : ℤ × ℤ → ℂ, IsRapidDecay b ∧ b 0 = 0 ∧
      ∀ a : ℤ × ℤ → ℂ, IsRapidDecay a → ¬ ∀ p, symbol θ p * a p = b p := by
  -- approximations `p j` with `|θ m - n| < 1 / (j + 1) / |m|^(2j)`
  have happrox : ∀ j : ℕ, ∃ p : ℤ × ℤ, p.1 ≠ 0 ∧
      |θ * p.1 - p.2| < 1 / ((j : ℝ) + 1) / |(p.1 : ℝ)| ^ (2 * j) := by
    intro j
    unfold IsDiophantine at hθ
    push Not at hθ
    obtain ⟨m, n, hm, h⟩ := hθ (1 / ((j : ℝ) + 1)) (by positivity) (2 * j)
    exact ⟨(m, n), hm, h⟩
  choose q hq0 hq using happrox
  set σ : ℕ → ℝ := fun j => ‖symbol θ (q j)‖ with hσdef
  have hσ : ∀ j, σ j = |θ * (q j).1 - (q j).2| := fun j => norm_symbol θ (q j)
  have hσpos : ∀ j, 0 < σ j := fun j => by
    rw [hσ]
    exact abs_pos.2 ((hirr.mul_intCast (hq0 j)).sub_intCast _).ne_zero
  have hm1 : ∀ j, (1 : ℝ) ≤ |((q j).1 : ℝ)| := fun j => mod_cast Int.one_le_abs (hq0 j)
  -- `σ j * |m|^(2j) < 1 / (j + 1)`
  have hq' : ∀ j, σ j * |((q j).1 : ℝ)| ^ (2 * j) < 1 / ((j : ℝ) + 1) := fun j => by
    rw [hσ, ← lt_div_iff₀ (by have := hm1 j; positivity)]
    exact hq j
  have hσlt : ∀ j, σ j * ((j : ℝ) + 1) < 1 := fun j => by
    have h1 : 1 ≤ |((q j).1 : ℝ)| ^ (2 * j) := one_le_pow₀ (hm1 j)
    have h2 := hq' j
    rw [lt_div_iff₀ (by positivity)] at h2
    nlinarith [hσpos j]
  have hσm : ∀ j, Real.sqrt (σ j) * |((q j).1 : ℝ)| ^ j < 1 := fun j => by
    refine lt_of_pow_lt_pow_left₀ 2 zero_le_one ?_
    rw [mul_pow, Real.sq_sqrt (hσpos j).le, ← pow_mul, mul_comm j 2, one_pow]
    have h2 := hq' j
    have h3 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
    linarith
  -- the weight of `q j` is at most `K |m|`
  set K : ℝ := 3 + |θ| with hK
  have hweight : ∀ j, weight (q j) ≤ K * |((q j).1 : ℝ)| := fun j => by
    have h1 : σ j < 1 := by nlinarith [hσlt j, hσpos j, (j.cast_nonneg : (0 : ℝ) ≤ j)]
    rw [hσ] at h1
    have h2 := abs_sub_abs_le_abs_sub ((q j).2 : ℝ) (θ * (q j).1)
    rw [abs_sub_comm, abs_mul] at h2
    have h3 := hm1 j
    unfold weight
    nlinarith [abs_nonneg θ]
  -- the right-hand side, supported on the approximations
  set b : ℤ × ℤ → ℂ := (Set.range q).indicator
    fun p => symbol θ p / ((Real.sqrt ‖symbol θ p‖ : ℝ) : ℂ) with hbdef
  have hbq : ∀ j, ‖b (q j)‖ = Real.sqrt (σ j) := fun j => by
    rw [hbdef, Set.indicator_of_mem (Set.mem_range_self j), norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.div_sqrt
  have hb0 : b 0 = 0 := by simp [hbdef]
  refine ⟨b, ?_, hb0, ?_⟩
  · -- `b` is rapidly decreasing
    intro k
    have hK0 : 0 ≤ K ^ k := by positivity
    have hS0 : 0 ≤ ∑ j ∈ Finset.range k, ‖b (q j)‖ * weight (q j) ^ k := by
      apply Finset.sum_nonneg; intro j _; have := weight_pos (q j); positivity
    refine ⟨K ^ k + ∑ j ∈ Finset.range k, ‖b (q j)‖ * weight (q j) ^ k, fun p => ?_⟩
    by_cases hp : p ∈ Set.range q
    · obtain ⟨j, rfl⟩ := hp
      by_cases hj : j < k
      · have := Finset.single_le_sum (f := fun j => ‖b (q j)‖ * weight (q j) ^ k)
          (fun i _ => by have := weight_pos (q i); positivity) (Finset.mem_range.2 hj)
        linarith
      · rw [hbq]
        have hw0 := weight_pos (q j)
        have hs0 := Real.sqrt_nonneg (σ j)
        have h1 : weight (q j) ^ k ≤ K ^ k * |((q j).1 : ℝ)| ^ j := by
          calc weight (q j) ^ k ≤ (K * |((q j).1 : ℝ)|) ^ k :=
                pow_le_pow_left₀ hw0.le (hweight j) k
            _ = K ^ k * |((q j).1 : ℝ)| ^ k := mul_pow _ _ _
            _ ≤ K ^ k * |((q j).1 : ℝ)| ^ j := by
                gcongr
                · exact hm1 j
                · omega
        calc Real.sqrt (σ j) * weight (q j) ^ k
            ≤ Real.sqrt (σ j) * (K ^ k * |((q j).1 : ℝ)| ^ j) := by gcongr
          _ = K ^ k * (Real.sqrt (σ j) * |((q j).1 : ℝ)| ^ j) := by ring
          _ ≤ K ^ k * 1 := by gcongr; exact (hσm j).le
          _ ≤ _ := by linarith
    · rw [hbdef, Set.indicator_of_notMem hp, norm_zero, zero_mul]
      positivity
  · -- no rapidly decreasing preimage: it would be `1 / √σ` at `q j`, which is unbounded
    intro a ha hab
    obtain ⟨C, hC⟩ := ha 0
    set j := ⌈C ^ 2⌉₊ with hj
    have hjC : C ^ 2 ≤ j := Nat.le_ceil _
    have h1 := hC (q j)
    rw [pow_zero, mul_one] at h1
    have h2 : σ j * ‖a (q j)‖ = Real.sqrt (σ j) := by
      rw [← hbq, ← hab (q j), norm_mul]
    have hs := Real.sqrt_pos.2 (hσpos j)
    have hsq := Real.sq_sqrt (hσpos j).le
    -- `√σ ‖a‖ = 1`
    have h3 : Real.sqrt (σ j) * ‖a (q j)‖ = 1 :=
      mul_left_cancel₀ hs.ne' (by rw [← mul_assoc, ← sq, hsq, h2, mul_one])
    have h4 : 1 ≤ Real.sqrt (σ j) * C := by
      rw [← h3]; gcongr
    have h5 : 1 ≤ σ j * C ^ 2 := by
      have := mul_le_mul h4 h4 zero_le_one (by linarith)
      nlinarith
    have h6 := hσlt j
    nlinarith [hσpos j]

/-- For irrational `θ`, the operator `θ ∂_x - ∂_y` maps the rapidly decreasing families onto the
rapidly decreasing families with vanishing `(0, 0)` coefficient iff `θ` is Diophantine. -/
theorem surjective_iff_isDiophantine (hirr : Irrational θ) :
    (∀ b : ℤ × ℤ → ℂ, IsRapidDecay b → b 0 = 0 →
      ∃ a : ℤ × ℤ → ℂ, IsRapidDecay a ∧ ∀ p, symbol θ p * a p = b p) ↔ IsDiophantine θ := by
  refine ⟨fun h => of_not_not fun hθ => ?_,
    fun hθ b hb hb0 => ⟨_, hθ.isRapidDecay_div hb hb0, hθ.symbol_mul_div hb0⟩⟩
  obtain ⟨b, hb, hb0, hno⟩ := exists_not_mem_range_of_not_isDiophantine hirr hθ
  obtain ⟨a, ha, hab⟩ := h b hb hb0
  exact hno a ha hab

/-- A Liouville number is not Diophantine. -/
theorem not_isDiophantine_of_liouville {x : ℝ} (hx : Liouville x) :
    ¬ IsDiophantine x := by
  rintro ⟨C, hC, N, h⟩
  have hev : ∀ᶠ b : ℕ in atTop, 1 / C ≤ (b : ℝ) ∧ 1 ≤ b :=
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / C)).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop 1)
  obtain ⟨b, ⟨hbC, hb1⟩, a, -, hab⟩ :=
    (hev.and_frequently (hx.frequently_exists_num (N + 2))).exists
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb1
  have hbne : (b : ℤ) ≠ 0 := by exact_mod_cast hb0.ne'
  have h1 := h b a hbne
  push_cast at h1
  rw [abs_of_pos hb0] at h1
  -- `|x b - a| = b |x - a / b| < b / b^(N+2) = 1 / b^(N+1) ≤ C / b^N`
  have h2 : |x * b - a| = b * |x - a / b| := by
    rw [← abs_of_pos hb0, ← abs_mul, abs_of_pos hb0, mul_sub, mul_div_cancel₀ _ hb0.ne',
      mul_comm]
  have hpow : (0 : ℝ) < (b : ℝ) ^ N := by positivity
  have h3 : b * |x - a / b| < C / (b : ℝ) ^ N := by
    calc b * |x - a / b| < b * (1 / (b : ℝ) ^ (N + 2)) := by gcongr
      _ = (1 / b) / (b : ℝ) ^ N := by field_simp; ring
      _ ≤ C / (b : ℝ) ^ N := by
          gcongr
          rw [div_le_iff₀ hb0]
          rw [div_le_iff₀ hC] at hbC
          linarith
  linarith

/-- For a Liouville number `x`, some rapidly decreasing `b` with `b (0, 0) = 0` has no rapidly
decreasing preimage under `x ∂_x - ∂_y`. -/
theorem exists_not_mem_range_of_liouville {x : ℝ} (hx : Liouville x) :
    ∃ b : ℤ × ℤ → ℂ, IsRapidDecay b ∧ b 0 = 0 ∧
      ∀ a : ℤ × ℤ → ℂ, IsRapidDecay a → ¬ ∀ p, symbol x p * a p = b p :=
  exists_not_mem_range_of_not_isDiophantine hx.irrational (not_isDiophantine_of_liouville hx)

end Quillen.Notebook1983_4
