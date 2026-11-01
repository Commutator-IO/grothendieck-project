import Mathlib
import Quillen.Upstream.QBinomial

/-!
# Quillen, notebook 1970-15, pp. 21–22: the Möbius function of the subspace lattice

Daniel Quillen's notebook 1970-15 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201970/1970-15.pdf>) inverts, on
pp. 21–22, Euler characteristics over the isotropy types of an action, with Möbius coefficients.
For `G` elementary abelian he checks the formula at a point. For rank 3, in our words, the check is
`1 - (q² + q + 1) + q (q² + q + 1) - q³ = 0`: the alternating sum, over the subspaces `W` of an
`n`-dimensional space over `𝔽_q`, of `(-1)^(dim W) q^(dim W choose 2)` vanishes for `n ≥ 1`. That
is the Möbius function of the subspace lattice (P. Hall 1936; Rota 1964; Stanley, *Enumerative
Combinatorics* I, 3.10). The number of `k`-dimensional subspaces is the Gaussian binomial
`[n, k]_q`; this file proves the identity in that polynomial form, for `q` in any commutative ring.

* `qBinom`: the Gaussian binomial `[n, k]_q`, by the recursion
  `[n+1, k+1] = [n, k] + q^(k+1) [n, k+1]`;
* `qBinom_eq_zero_of_lt`: `[n, k] = 0` for `k > n`;
* `prod_one_add_eq_sum`: the `q`-binomial theorem
  `∏_{i < n} (1 + q^i t) = Σ_{k ≤ n} q^(k choose 2) [n, k] t^k`;
* `sum_alternating_eq_zero`: `Σ_{k ≤ n} (-1)^k q^(k choose 2) [n, k] = 0` for `n ≥ 1`;
* `quillen_check_rank_three`: the case `n = 3`, as on p. 22.

The other statement of the notebook first proposed for formalisation, p. 14 (a pro-`ℓ` group has
finitely generated cohomology iff it has an open subgroup with finite cohomology), needs the
cohomology of profinite groups, which mathlib does not have; it is not attempted.

The Gaussian binomials and the `q`-binomial theorem are general and live in
`Quillen.Upstream.QBinomial` (`qBinomial`, `prod_one_add_pow_mul_eq_sum_qBinomial`, …); the
declarations below keep the names of this page.
-/

namespace Quillen.Notebook1970_15

open Finset

variable {R : Type*} [CommRing R]

/-- The Gaussian binomial `[n, k]_q`, by the `q`-Pascal recursion
`[n+1, k+1] = [n, k] + q^(k+1) [n, k+1]`. -/
abbrev qBinom (q : R) : ℕ → ℕ → R := qBinomial q

@[simp] theorem qBinom_zero_right (q : R) (n : ℕ) : qBinom q n 0 = 1 := qBinomial_zero_right q n

@[simp] theorem qBinom_zero_succ (q : R) (k : ℕ) : qBinom q 0 (k + 1) = 0 := rfl

theorem qBinom_succ_succ (q : R) (n k : ℕ) :
    qBinom q (n + 1) (k + 1) = qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1) := rfl

/-- `[n, k] = 0` for `k > n`. -/
theorem qBinom_eq_zero_of_lt (q : R) {n k : ℕ} (h : n < k) : qBinom q n k = 0 :=
  qBinomial_eq_zero_of_lt q h

/-- The `q`-binomial theorem: `∏_{i < n} (1 + q^i t) = Σ_{k ≤ n} q^(k choose 2) [n, k] t^k`. -/
theorem prod_one_add_eq_sum (q : R) (n : ℕ) (t : R) :
    ∏ i ∈ range n, (1 + q ^ i * t) =
      ∑ k ∈ range (n + 1), q ^ k.choose 2 * qBinom q n k * t ^ k :=
  prod_one_add_pow_mul_eq_sum_qBinomial q n t

/-- The alternating sum of the Möbius function of the subspace lattice vanishes:
`Σ_{k ≤ n} (-1)^k q^(k choose 2) [n, k] = 0` for `n ≥ 1`. -/
theorem sum_alternating_eq_zero (q : R) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ range (n + 1), (-1) ^ k * q ^ k.choose 2 * qBinom q n k = 0 :=
  sum_neg_one_pow_mul_qBinomial_eq_zero q hn

/-- Quillen's check on p. 22, for rank `3`: `1 - (q² + q + 1) + q (q² + q + 1) - q³ = 0`. -/
theorem quillen_check_rank_three (q : R) :
    1 - (q ^ 2 + q + 1) + q * (q ^ 2 + q + 1) - q ^ 3 = 0 := by
  have h := sum_alternating_eq_zero q (n := 3) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, qBinom_succ_succ, qBinom_zero_right,
    qBinom_zero_succ] at h
  norm_num [Nat.choose] at h
  linear_combination h

end Quillen.Notebook1970_15
