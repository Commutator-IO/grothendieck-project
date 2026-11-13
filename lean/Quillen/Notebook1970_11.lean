import Mathlib

/-!
# Quillen, notebook 1970-11: the 2-parts of `|GL_n(F_q)|` and `|N|` (p. 17); the digit-sum bound (pp. 21–22, and 1974-2, p. 26)

Daniel Quillen's research notebook 1970-11 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201970/1970-11.pdf>) attacks,
on p. 17, the mod 2 cohomology of `GL_n(F_q)` in the exceptional case `q ≡ 3 mod 4`, through
the subgroup `N = (Σ_m ≀ (Gal ⋉ F_{q²}^×)) × (F_q^×)^e`, `n = 2m + e`, `e ∈ {0, 1}`. He compares
the orders `|GL_n(F_q)| = q^{n(n−1)/2} ∏_{i=1}^n (q^i − 1)` and `|N| = m! (2(q² − 1))^m (q − 1)^e`
and says that they have the same power of `2`, because `v_2(q^i − 1) = 1` for `i` odd and
`v_2(q^{2i} − 1) = v_2(i) + v_2(q² − 1)`.

This file proves the two valuation formulas and the comparison of the 2-parts:

* `padicValNat_pow_odd_sub_one`: `v_2(q^k − 1) = 1` for `k` odd and `q ≡ 3 mod 4`;
* `padicValNat_pow_even_sub_one`: `v_2(q^{2i} − 1) = v_2(i) + v_2(q² − 1)` for `i ≥ 1` and any
  odd `q > 1`;
* `padicValNat_card_GL_eq`: **the claim of the page**: for `q ≡ 3 mod 4` and `n = 2m + e`,
  `v_2(q^{n(n−1)/2} ∏_{i=1}^n (q^i − 1)) = v_2(m! (2(q² − 1))^m (q − 1)^e)`.

The order formulas themselves and the group `N` are not formalised.

**pp. 20–22.** To find the first `F_q^×`-invariant class in the cohomology of `F_q`, `q = p^r`,
the page looks at monomials of degree `∑ (2 n_a − ε_a)` and weight `∑ n_a p^a`, `ε_a ∈ {0, 1}`,
`ε_a = 0` if `n_a = 0`, invariant when `p^r − 1 ∣ ∑ n_a p^a`. Carrying `p` units from place `a`
to place `a + 1` (cyclically) keeps the weight modulo `p^r − 1` and lowers the degree, so the
minimum is reached with digits `n_a ≤ p − 1`, where the weight must be `p^r − 1`: the first
invariant is in degree `r (2p − 3)`. (The two pages are crossed out, with « ignore » in the
margin; the statement holds.) The same count, in the form `∑ a_i ≥ d (p − 1)`, is used in
notebook 1974-2, p. 26, for the characters of `F_{p^d}^×` in `Λ^i ⊗ Γ_j`.

* `le_sum_of_dvd`: **the digit-sum bound**: digits `a_0, …, a_{d−1}`, not all zero, with
  `p^d − 1 ∣ ∑ a_i p^i`, satisfy `∑ a_i ≥ d (p − 1)`, by the page's carrying argument
  (`carry`, `val_carry`, `sum_carry`) and the base case `base`;
* `le_degree`: **the claim of pp. 21–22**: `∑ (2 n_a − ε_a) ≥ r (2p − 3)`, with equality at
  `n_a = p − 1`, `ε_a = 1` (`degree_extremal`).
-/

namespace Quillen.Notebook1970_11

open Finset

theorem padicValNat_eq_one {n : ℕ} (hn : n ≠ 0) (h1 : 2 ∣ n) (h2 : ¬ 4 ∣ n) :
    padicValNat 2 n = 1 := by
  have a := (padicValNat_dvd_iff_le (n := 1) hn).mp (by simpa using h1)
  have b : ¬ 2 ≤ padicValNat 2 n := fun h =>
    h2 (by simpa using (padicValNat_dvd_iff_le (n := 2) hn).mpr h)
  omega

theorem padicValNat_prod {f : ℕ → ℕ} (hf : ∀ i, f i ≠ 0) (n : ℕ) :
    padicValNat 2 (∏ i ∈ range n, f i) = ∑ i ∈ range n, padicValNat 2 (f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, sum_range_succ, padicValNat.mul (prod_ne_zero_iff.mpr fun i _ => hf i)
      (hf n), ih]

variable {q : ℕ}

/-- `v_2(q^k − 1) = 1` for `k` odd and `q ≡ 3 mod 4`. -/
theorem padicValNat_pow_odd_sub_one (hq : q % 4 = 3) {k : ℕ} (hk : Odd k) :
    padicValNat 2 (q ^ k - 1) = 1 := by
  obtain ⟨j, rfl⟩ := hk
  have hq1 : 1 < q := by omega
  have hlt : 1 < q ^ (2 * j + 1) := Nat.one_lt_pow (by omega) hq1
  have hmod : q ^ (2 * j + 1) % 4 = 3 := by
    rw [Nat.pow_mod, hq, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  exact padicValNat_eq_one (by omega) (by omega) (by omega)

/-- `v_2(q^{2i} − 1) = v_2(i) + v_2(q² − 1)` for `i ≥ 1` and `q > 1` odd. -/
theorem padicValNat_pow_even_sub_one (hq1 : 1 < q) (hodd : ¬ 2 ∣ q) {i : ℕ} (hi : i ≠ 0) :
    padicValNat 2 (q ^ (2 * i) - 1) = padicValNat 2 i + padicValNat 2 (q ^ 2 - 1) := by
  have h := padicValNat.pow_two_sub_one hq1 hodd (n := 2 * i) (by omega) (even_two_mul i)
  rw [padicValNat.mul (by omega) hi, padicValNat.self (by norm_num)] at h
  rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by rw [← Nat.sq_sub_sq, one_pow],
    padicValNat.mul (by omega) (by omega)]
  omega

/-- The 2-adic valuation of `∏_{i=1}^{2m} (q^i − 1)` for `q ≡ 3 mod 4`. -/
theorem padicValNat_prod_even (hq : q % 4 = 3) (m : ℕ) :
    padicValNat 2 (∏ i ∈ range (2 * m), (q ^ (i + 1) - 1)) =
      m + padicValNat 2 m.factorial + m * padicValNat 2 (q ^ 2 - 1) := by
  have hq1 : 1 < q := by omega
  have hodd : ¬ 2 ∣ q := by omega
  have hne : ∀ i, q ^ (i + 1) - 1 ≠ 0 := fun i =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hq1)
  rw [padicValNat_prod hne]
  induction m with
  | zero => simp
  | succ m ih =>
    have e2 : padicValNat 2 (q ^ (2 * m + 1 + 1) - 1) =
        padicValNat 2 (m + 1) + padicValNat 2 (q ^ 2 - 1) := by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
      exact padicValNat_pow_even_sub_one hq1 hodd (by omega)
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      padicValNat_pow_odd_sub_one hq ⟨m, rfl⟩, e2,
      Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero m)]
    ring

/-- **Quillen, notebook 1970-11, p. 17.** For `q ≡ 3 mod 4` and `n = 2m + e`, `e ∈ {0, 1}`, the
numbers `q^{n(n−1)/2} ∏_{i=1}^n (q^i − 1)` (the order of `GL_n(F_q)`) and
`m! (2(q² − 1))^m (q − 1)^e` (the order of `N`) have the same 2-adic valuation. -/
theorem padicValNat_card_GL_eq (hq : q % 4 = 3) (m e : ℕ) (he : e ≤ 1) :
    padicValNat 2 (q ^ ((2 * m + e) * (2 * m + e - 1) / 2) *
        ∏ i ∈ range (2 * m + e), (q ^ (i + 1) - 1)) =
      padicValNat 2 (m.factorial * (2 * (q ^ 2 - 1)) ^ m * (q - 1) ^ e) := by
  have hq1 : 1 < q := by omega
  have hne : ∀ i, q ^ (i + 1) - 1 ≠ 0 := fun i =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hq1)
  have hsq : q ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hq1)
  have hq0 : padicValNat 2 (q ^ ((2 * m + e) * (2 * m + e - 1) / 2)) = 0 := by
    rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd (by omega), mul_zero]
  have hv1 : padicValNat 2 (q - 1) = 1 := by
    simpa using padicValNat_pow_odd_sub_one hq (k := 1) odd_one
  rw [padicValNat.mul (pow_ne_zero _ (by omega)) (prod_ne_zero_iff.mpr fun i _ => hne i), hq0,
    zero_add, padicValNat.mul (mul_ne_zero (Nat.factorial_ne_zero m)
      (pow_ne_zero _ (mul_ne_zero (by norm_num) hsq))) (pow_ne_zero _ (by omega)),
    padicValNat.mul (Nat.factorial_ne_zero m) (pow_ne_zero _ (mul_ne_zero (by norm_num) hsq)),
    padicValNat.pow, padicValNat.pow,
    padicValNat.mul (by norm_num) hsq, padicValNat.self (by norm_num), hv1]
  interval_cases e
  · simpa [mul_add, add_comm, add_left_comm, add_assoc] using padicValNat_prod_even hq m
  · rw [prod_range_succ, padicValNat.mul (prod_ne_zero_iff.mpr fun i _ => hne i) (hne _),
      padicValNat_prod_even hq, padicValNat_pow_odd_sub_one hq ⟨m, rfl⟩]
    ring

/-- The value `∑ a_i p^i` of a family of digits. -/
def val (p : ℕ) {d : ℕ} (a : Fin d → ℕ) : ℕ := ∑ i, a i * p ^ (i : ℕ)

theorem geom (p d : ℕ) (hp : 1 ≤ p) : ∑ i : Fin d, (p - 1) * p ^ (i : ℕ) = p ^ d - 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (p - 1) * p ^ i), ← mul_sum]
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, mul_add, ih, pow_succ]
    have h1 : 1 ≤ p ^ d := Nat.one_le_pow _ _ hp
    zify [h1, hp, (by nlinarith : 1 ≤ p ^ d * p)]
    ring

/-- Base case: digits at most `p - 1`. -/
theorem base {p d : ℕ} (hp : 2 ≤ p) (a : Fin d → ℕ) (ha : a ≠ 0) (hle : ∀ i, a i ≤ p - 1)
    (hdvd : (p ^ d - 1) ∣ val p a) : ∑ i, a i = d * (p - 1) := by
  have hg := geom p d (by omega)
  have hsplit : ∑ i : Fin d, (p - 1 - a i) * p ^ (i : ℕ) + val p a = p ^ d - 1 := by
    rw [val, ← sum_add_distrib, ← hg]
    refine sum_congr rfl fun i _ => ?_
    rw [← add_mul, Nat.sub_add_cancel (hle i)]
  have hpos : 0 < val p a := by
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra! h; exact ha (funext h)
    exact lt_of_lt_of_le (Nat.mul_pos (Nat.pos_of_ne_zero hi) (by positivity))
      (single_le_sum (f := fun i => a i * p ^ (i : ℕ)) (fun _ _ => Nat.zero_le _) (mem_univ i))
  have hv : val p a = p ^ d - 1 := by
    have hle' : val p a ≤ p ^ d - 1 := by omega
    obtain ⟨c, hc⟩ := hdvd
    rcases c with _ | _ | c
    · omega
    · omega
    · have : p ^ d - 1 ≤ 1 * (p ^ d - 1) := by omega
      nlinarith
  have hz : ∑ i : Fin d, (p - 1 - a i) * p ^ (i : ℕ) = 0 := by omega
  have hall : ∀ i, a i = p - 1 := fun i => by
    have := (mul_eq_zero.mp ((sum_eq_zero_iff.mp hz) i (mem_univ i))).resolve_right
      (by positivity)
    have := hle i
    omega
  simp [hall]

/-- One cyclic carry: take `p` units at place `i`, add one at place `i + 1` (mod `d`). -/
def carry (p : ℕ) {d : ℕ} (a : Fin d → ℕ) (i j : Fin d) : Fin d → ℕ :=
  fun k => a k - (Pi.single i p : Fin d → ℕ) k + (Pi.single j 1 : Fin d → ℕ) k

theorem carry_add {p d : ℕ} (a : Fin d → ℕ) (i j : Fin d) (hi : p ≤ a i) (k : Fin d) :
    carry p a i j k + (Pi.single i p : Fin d → ℕ) k = a k + (Pi.single j 1 : Fin d → ℕ) k := by
  unfold carry
  have : (Pi.single i p : Fin d → ℕ) k ≤ a k := by obtain rfl | h := eq_or_ne k i <;> simp [*]
  omega

theorem sum_carry {p d : ℕ} (a : Fin d → ℕ) (i j : Fin d) (hi : p ≤ a i) :
    ∑ k, carry p a i j k + p = ∑ k, a k + 1 := by
  have := sum_congr rfl fun (k : Fin d) (_ : k ∈ univ) => carry_add a i j hi k
  rw [sum_add_distrib, sum_add_distrib] at this
  simpa [Finset.sum_pi_single'] using this

theorem val_carry {p d : ℕ} (a : Fin d → ℕ) (i j : Fin d) (hi : p ≤ a i) :
    val p (carry p a i j) + p ^ ((i : ℕ) + 1) = val p a + p ^ (j : ℕ) := by
  have := sum_congr rfl fun (k : Fin d) (_ : k ∈ univ) =>
    congrArg (· * p ^ (k : ℕ)) (carry_add a i j hi k)
  simp only [add_mul, sum_add_distrib] at this
  unfold val
  convert this using 2
  · simp [Pi.single_apply, pow_succ, mul_comm]
  · simp [Pi.single_apply]

/-- **The digit-sum bound.** For `p ≥ 2` and digits `a_0, …, a_{d−1}` not all zero with
`p ^ d - 1 ∣ ∑ a_i p^i`, one has `d (p − 1) ≤ ∑ a_i`. -/
theorem le_sum_of_dvd {p d : ℕ} (hp : 2 ≤ p) (a : Fin d → ℕ) (ha : a ≠ 0)
    (hdvd : (p ^ d - 1) ∣ val p a) : d * (p - 1) ≤ ∑ i, a i := by
  induction hS : ∑ i, a i using Nat.strong_induction_on generalizing a with
  | _ S ih =>
  by_cases hbig : ∃ i, p ≤ a i
  · obtain ⟨i, hi⟩ := hbig
    have hd : 0 < d := Fin.pos i
    let j : Fin d := ⟨((i : ℕ) + 1) % d, Nat.mod_lt _ hd⟩
    have hsum := sum_carry a i j hi
    have hne : carry p a i j ≠ 0 := fun h => by
      have h2 := carry_add a i j hi j
      rw [show carry p a i j j = 0 from congrFun h j] at h2
      rcases eq_or_ne j i with hij | hij <;> simp [hij] at h2
      omega
    have hdvd' : (p ^ d - 1) ∣ val p (carry p a i j) := by
      have hv := val_carry a i j hi
      have hpow : (p ^ d - 1) ∣ p ^ ((i : ℕ) + 1) - p ^ (j : ℕ) := by
        by_cases hlt : (i : ℕ) + 1 < d
        · rw [show (j : ℕ) = (i : ℕ) + 1 from Nat.mod_eq_of_lt hlt, Nat.sub_self]
          exact dvd_zero _
        · have h1 : (i : ℕ) + 1 = d := by have := i.isLt; omega
          rw [show (j : ℕ) = 0 by simp [j, h1], h1, pow_zero]
      have hle : p ^ (j : ℕ) ≤ p ^ ((i : ℕ) + 1) :=
        Nat.pow_le_pow_right (by omega) (Nat.mod_le _ _)
      have : val p (carry p a i j) = val p a - (p ^ ((i : ℕ) + 1) - p ^ (j : ℕ)) := by omega
      rw [this]
      exact Nat.dvd_sub hdvd hpow
    have hlt : ∑ k, carry p a i j k < S := by omega
    have := ih _ hlt (carry p a i j) hne hdvd' rfl
    omega
  · push Not at hbig
    rw [← hS, base hp a ha (fun i => by have := hbig i; omega) hdvd]


/-- **Quillen, notebook 1970-11, pp. 21–22.** For `p ≥ 2`, exponents `n_a` not all zero and
`ε_a ∈ {0, 1}` with `ε_a = 0` when `n_a = 0`, if `p^r − 1 ∣ ∑ n_a p^a` then the degree
`∑ (2 n_a − ε_a)` is at least `r (2p − 3)`. -/
theorem le_degree {p r : ℕ} (hp : 2 ≤ p) (n ε : Fin r → ℕ) (hn : n ≠ 0)
    (hε : ∀ a, ε a ≤ 1) (hε0 : ∀ a, n a = 0 → ε a = 0) (hdvd : (p ^ r - 1) ∣ val p n) :
    r * (2 * p - 3) ≤ ∑ a, (2 * n a - ε a) := by
  have h1 := le_sum_of_dvd hp n hn hdvd
  have hle : ∀ a, ε a ≤ 2 * n a := fun a => by
    by_cases h : n a = 0
    · simp [hε0 a h]
    · have := hε a; omega
  have h2 : ∑ a, (2 * n a - ε a) + ∑ a, ε a = 2 * ∑ a, n a := by
    rw [← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun a _ => Nat.sub_add_cancel (hle a)
  have h3 : ∑ a, ε a ≤ r := (sum_le_sum fun a _ => hε a).trans (by simp)
  have h4 : r * (2 * p - 3) + r = 2 * (r * (p - 1)) := by
    rcases Nat.exists_eq_add_of_le hp with ⟨c, rfl⟩
    rw [show 2 * (2 + c) - 3 = 2 * c + 1 by omega, show 2 + c - 1 = c + 1 by omega]
    ring
  omega

/-- The bound of `le_degree` is attained at `n_a = p − 1`, `ε_a = 1`. -/
theorem degree_extremal {p r : ℕ} (hp : 2 ≤ p) :
    (p ^ r - 1) ∣ val p (fun _ : Fin r => p - 1) ∧
      ∑ _a : Fin r, (2 * (p - 1) - 1) = r * (2 * p - 3) := by
  refine ⟨by rw [val, geom p r (by omega)], ?_⟩
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  congr 1; omega

end Quillen.Notebook1970_11
