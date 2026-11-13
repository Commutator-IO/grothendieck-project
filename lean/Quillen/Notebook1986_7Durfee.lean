import Mathlib
import Quillen.Upstream.QBinomial

/-!
# Quillen, notebook 1986-7, pp. 55-56: the Durfee identity

Daniel Quillen's research notebook 1986-7 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201986/1986-7.pdf>), pp. 55-56,
records two proofs (from a conversation with Graeme Segal) of the identity of formal power series
`1 / ∏_{i > 0} (1 − q^i) = Σ_{s ≥ 0} q^{s²} / (∏_{i=1}^s (1 − q^i))²`;
the second is the Durfee square of a Young diagram (Hardy and Wright).

We prove it through its finite form, the Durfee square of a partition in an `m × n` box:
`Σ_s q^{s²} [m, s]_q [n, s]_q = [m + n, m]_q`, for `q` in any commutative ring (`sum_durfee`).
The proof is by induction on `m + n` from the two `q`-Pascal recursions (`qBinomial_succ_succ`
and `pow_mul_qBinomial_succ`, the second one proved here) and a telescoping sum. With the product
formula `[a + b, b] (q)_b (q)_a = (q)_{a+b}` (`qBinomial_mul_qfac`), the power series
`[M, s]` agrees with `1 / (q)_s` below degree `M − s + 1`, and taking `m = n = M` gives the
identity in `R⟦q⟧` degree by degree (`coeff_inverse_qfac`): for `N ≤ M`, the `N`-th coefficients
of `1 / (q)_M` and of `Σ_{s ≤ M} q^{s²} / (q)_s²` agree. Finally `card_partition`: the number of
partitions of `N` is the `N`-th coefficient of `Σ_{s ≤ N} q^{s²} / (q)_s²`, through mathlib's
generating function of partitions with restricted parts.
-/

namespace Quillen.Notebook1986_7Durfee

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Ring

variable {R : Type*} [CommRing R]

theorem qBinomial_self (q : R) : ∀ n, qBinomial q n n = 1
  | 0 => rfl
  | n + 1 => by
    rw [qBinomial_succ_succ, qBinomial_self q n, qBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)]
    ring

/-- The second `q`-Pascal recursion, `[a + b + 1, b + 1] = q^a [a + b, b] + [a + b, b + 1]`. -/
theorem qBinomial_pascal' (q : R) (b : ℕ) : ∀ a : ℕ,
    qBinomial q (a + b + 1) (b + 1) = q ^ a * qBinomial q (a + b) b + qBinomial q (a + b) (b + 1) := by
  induction b with
  | zero =>
    intro a
    induction a with
    | zero => simp [qBinomial_succ_succ]
    | succ a iha =>
      have h1 : qBinomial q (a + 1 + 1) 1 = 1 + q * qBinomial q (a + 1) 1 := by
        rw [qBinomial_succ_succ]; simp
      have h2 : qBinomial q (a + 1) 1 = 1 + q * qBinomial q a 1 := by
        rw [qBinomial_succ_succ]; simp
      have iha' : qBinomial q (a + 1) 1 = q ^ a + qBinomial q a 1 := by
        simpa using iha
      show qBinomial q (a + 1 + 1) 1 = q ^ (a + 1) * qBinomial q (a + 1) 0 + qBinomial q (a + 1) 1
      rw [qBinomial_zero_right]
      linear_combination h1 + q * iha' - h2
  | succ b ihb =>
    intro a
    induction a with
    | zero =>
      simp only [zero_add, pow_zero, one_mul]
      rw [qBinomial_self, qBinomial_self, qBinomial_eq_zero_of_lt q (by omega : b + 1 < b + 1 + 1)]
      ring
    | succ a iha =>
      have e1 : a + 1 + (b + 1) + 1 = (a + b + 2) + 1 := by omega
      have e2 : a + 1 + (b + 1) = a + b + 2 := by omega
      have e3 : a + (b + 1) + 1 = a + b + 2 := by omega
      have e4 : a + (b + 1) = a + b + 1 := by omega
      have e5 : a + 1 + b + 1 = a + b + 2 := by omega
      have e6 : a + 1 + b = a + b + 1 := by omega
      rw [e1, e2]
      rw [e3, e4] at iha
      have hb := ihb (a + 1)
      rw [e5, e6] at hb
      have p1 : qBinomial q (a + b + 2 + 1) (b + 1 + 1) =
          qBinomial q (a + b + 2) (b + 1) + q ^ (b + 1 + 1) * qBinomial q (a + b + 2) (b + 1 + 1) :=
        qBinomial_succ_succ q _ _
      have p2 : qBinomial q (a + b + 2) (b + 1) =
          qBinomial q (a + b + 1) b + q ^ (b + 1) * qBinomial q (a + b + 1) (b + 1) :=
        qBinomial_succ_succ q _ _
      have p3 : qBinomial q (a + b + 2) (b + 1 + 1) =
          qBinomial q (a + b + 1) (b + 1) + q ^ (b + 1 + 1) * qBinomial q (a + b + 1) (b + 1 + 1) :=
        qBinomial_succ_succ q _ _
      linear_combination p1 + hb - q ^ (a + 1) * p2 + q ^ (b + 1 + 1) * iha - p3

/-- The second `q`-Pascal recursion in a form valid for all `m, t`:
`q^t [m + 1, t + 1] = q^m [m, t] + q^t [m, t + 1]`. -/
theorem pow_mul_qBinomial_succ (q : R) (m t : ℕ) :
    q ^ t * qBinomial q (m + 1) (t + 1) = q ^ m * qBinomial q m t + q ^ t * qBinomial q m (t + 1) := by
  rcases le_or_gt t m with h | h
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' h
    rw [qBinomial_pascal']
    ring
  · rw [qBinomial_eq_zero_of_lt q (by omega : m + 1 < t + 1), qBinomial_eq_zero_of_lt q h,
      qBinomial_eq_zero_of_lt q (by omega : m < t + 1)]
    ring

/-- The Durfee sum `Σ_{s ≤ m} q^{s²} [m, s] [n, s]`. -/
def durfee (q : R) (m n : ℕ) : R :=
  ∑ s ∈ range (m + 1), q ^ (s * s) * qBinomial q m s * qBinomial q n s

theorem durfee_zero_left (q : R) (n : ℕ) : durfee q 0 n = 1 := by simp [durfee]

theorem durfee_zero_right (q : R) (m : ℕ) : durfee q m 0 = 1 := by
  rw [durfee, sum_range_succ']
  rw [sum_eq_zero fun s _ => by rw [qBinomial_zero_succ, mul_zero]]
  simp

/-- The recursion of the Durfee sum, matching the first `q`-Pascal recursion of `[m + n, m]`. -/
theorem durfee_succ_succ (q : R) (m n : ℕ) :
    durfee q (m + 1) (n + 1) = durfee q m (n + 1) + q ^ (m + 1) * durfee q (m + 1) n := by
  -- shift every sum to `t + 1`, separating the term `s = 0`
  have hA : durfee q (m + 1) (n + 1) = ∑ t ∈ range (m + 1),
      q ^ ((t + 1) * (t + 1)) * qBinomial q (m + 1) (t + 1) * qBinomial q (n + 1) (t + 1) + 1 := by
    rw [durfee, sum_range_succ']; simp
  have hB : durfee q m (n + 1) = ∑ t ∈ range (m + 1),
      q ^ ((t + 1) * (t + 1)) * qBinomial q m (t + 1) * qBinomial q (n + 1) (t + 1) + 1 := by
    rw [durfee, ← add_zero (∑ s ∈ range (m + 1), _),
      ← show q ^ ((m + 1) * (m + 1)) * qBinomial q m (m + 1) * qBinomial q (n + 1) (m + 1) = 0 by
        rw [qBinomial_eq_zero_of_lt q (Nat.lt_succ_self m)]; ring,
      ← sum_range_succ, sum_range_succ']
    simp
  have hC : durfee q (m + 1) n = ∑ t ∈ range (m + 1),
      q ^ ((t + 1) * (t + 1)) * qBinomial q (m + 1) (t + 1) * qBinomial q n (t + 1) + 1 := by
    rw [durfee, sum_range_succ']; simp
  -- the termwise identity is a telescoping difference
  let g : ℕ → R := fun t => q ^ (m + 1) * q ^ (t * t + t) * qBinomial q m t * qBinomial q n t
  have hterm : ∀ t ∈ range (m + 1),
      q ^ ((t + 1) * (t + 1)) * qBinomial q (m + 1) (t + 1) * qBinomial q (n + 1) (t + 1) -
        q ^ ((t + 1) * (t + 1)) * qBinomial q m (t + 1) * qBinomial q (n + 1) (t + 1) -
        q ^ (m + 1) * (q ^ ((t + 1) * (t + 1)) * qBinomial q (m + 1) (t + 1) *
          qBinomial q n (t + 1)) = g t - g (t + 1) := by
    intro t _
    have h1 := pow_mul_qBinomial_succ q m t
    rw [qBinomial_succ_succ q m t] at h1
    rw [qBinomial_succ_succ q m t, qBinomial_succ_succ q n t]
    simp only [g]
    linear_combination (q ^ (t * t + t + 1) * (qBinomial q n t + q ^ (t + 1) *
      qBinomial q n (t + 1))) * h1
  have hsum := sum_congr rfl hterm
  rw [sum_range_sub', sum_sub_distrib, sum_sub_distrib, ← mul_sum] at hsum
  have hg0 : g 0 = q ^ (m + 1) := by simp [g]
  have hg1 : g (m + 1) = 0 := by
    simp only [g]; rw [qBinomial_eq_zero_of_lt q (Nat.lt_succ_self m)]; ring
  rw [hg0, hg1] at hsum
  rw [hA, hB, hC]
  linear_combination hsum

/-- **The Durfee square in a box**: `Σ_{s ≤ m} q^{s²} [m, s] [n, s] = [m + n, m]`. -/
theorem sum_durfee (q : R) (n : ℕ) : ∀ m : ℕ, durfee q m n = qBinomial q (m + n) m := by
  induction n with
  | zero => intro m; rw [durfee_zero_right, add_zero, qBinomial_self]
  | succ n ihn =>
    intro m
    induction m with
    | zero => rw [durfee_zero_left, qBinomial_zero_right]
    | succ m ihm =>
      rw [durfee_succ_succ, ihm, ihn (m + 1),
        show m + 1 + (n + 1) = (m + (n + 1)) + 1 by omega, qBinomial_succ_succ,
        show m + 1 + n = m + (n + 1) by omega]

/-- `(q)_k = (1 − q)(1 − q²)⋯(1 − q^k)`. -/
def qfac (q : R) (k : ℕ) : R := ∏ i ∈ range k, (1 - q ^ (i + 1))

theorem qfac_succ (q : R) (k : ℕ) : qfac q (k + 1) = qfac q k * (1 - q ^ (k + 1)) :=
  prod_range_succ _ _

/-- The product formula `[a + b, b] (q)_b (q)_a = (q)_{a+b}`. -/
theorem qBinomial_mul_qfac (q : R) (a : ℕ) : ∀ b : ℕ,
    qBinomial q (a + b) b * qfac q b * qfac q a = qfac q (a + b) := by
  induction a with
  | zero => intro b; simp [qBinomial_self, qfac]
  | succ a iha =>
    intro b
    induction b with
    | zero => simp [qfac]
    | succ b ihb =>
      have ih2 := iha (b + 1)
      rw [show a + (b + 1) = a + 1 + b by omega] at ih2
      rw [show a + 1 + (b + 1) = (a + 1 + b) + 1 by omega, qBinomial_succ_succ, qfac_succ q b,
        qfac_succ q a, qfac_succ q (a + 1 + b)]
      rw [qfac_succ q b] at ih2
      rw [qfac_succ q a] at ihb
      linear_combination (1 - q ^ (b + 1)) * ihb + q ^ (b + 1) * (1 - q ^ (a + 1)) * ih2

/-! ### Power series -/

theorem isUnit_qfac (k : ℕ) : IsUnit (qfac (X : R⟦X⟧) k) := by
  rw [isUnit_iff_constantCoeff, qfac, map_prod]
  simp

theorem X_pow_dvd_prod_sub_one {k : ℕ} (s : Finset ℕ) (f : ℕ → R⟦X⟧)
    (hf : ∀ i ∈ s, (X : R⟦X⟧) ^ k ∣ f i - 1) : (X : R⟦X⟧) ^ k ∣ (∏ i ∈ s, f i) - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, show f j * ∏ i ∈ s, f i - 1 =
      f j * ((∏ i ∈ s, f i) - 1) + (f j - 1) by ring]
    exact dvd_add (dvd_mul_of_dvd_right (ih fun i hi => hf i (mem_insert_of_mem hi)) _)
      (hf j (mem_insert_self j s))

/-- `[a + s, s]` agrees with `1 / (q)_s` below degree `a + 1`. -/
theorem X_pow_dvd_qBinomial_sub (a s : ℕ) :
    (X : R⟦X⟧) ^ (a + 1) ∣ qBinomial (X : R⟦X⟧) (a + s) s - (qfac (X : R⟦X⟧) s)⁻¹ʳ := by
  set T : R⟦X⟧ := ∏ i ∈ range s, (1 - X ^ (a + i + 1)) with hT
  have hprod : qfac (X : R⟦X⟧) (a + s) = qfac X a * T := by
    rw [qfac, prod_range_add, qfac, hT]
  have h1 : qBinomial (X : R⟦X⟧) (a + s) s * qfac X s = T := by
    have := qBinomial_mul_qfac (X : R⟦X⟧) a s
    rw [hprod, mul_comm (qfac X a) T] at this
    exact (isUnit_qfac a).mul_left_cancel (by linear_combination this)
  have h2 : qBinomial (X : R⟦X⟧) (a + s) s = T * (qfac X s)⁻¹ʳ := by
    rw [← h1, Ring.mul_inverse_cancel_right _ _ (isUnit_qfac s)]
  have h3 : (X : R⟦X⟧) ^ (a + 1) ∣ T - 1 := by
    apply X_pow_dvd_prod_sub_one
    intro i _
    rw [show (1 : R⟦X⟧) - X ^ (a + i + 1) - 1 = -X ^ (a + i + 1) by ring]
    exact (dvd_neg).mpr (pow_dvd_pow _ (by omega))
  rw [h2, show T * (qfac (X : R⟦X⟧) s)⁻¹ʳ - (qfac X s)⁻¹ʳ = (T - 1) * (qfac X s)⁻¹ʳ by ring]
  exact dvd_mul_of_dvd_left h3 _

/-- **The Durfee identity**, degree by degree: for `N ≤ M`, the `N`-th coefficient of
`1 / ((1 − q)⋯(1 − q^M))` is that of `Σ_{s ≤ M} q^{s²} / ((1 − q)⋯(1 − q^s))²`. -/
theorem coeff_inverse_qfac {N M : ℕ} (h : N ≤ M) :
    coeff N (qfac (X : R⟦X⟧) M)⁻¹ʳ =
      coeff N (∑ s ∈ range (M + 1), (X : R⟦X⟧) ^ (s * s) * ((qfac X s)⁻¹ʳ) ^ 2) := by
  have hbox := sum_durfee (X : R⟦X⟧) M M
  have hleft : (X : R⟦X⟧) ^ (M + 1) ∣ qBinomial X (M + M) M - (qfac X M)⁻¹ʳ :=
    X_pow_dvd_qBinomial_sub M M
  have hright : (X : R⟦X⟧) ^ (M + 1) ∣ durfee X M M -
      ∑ s ∈ range (M + 1), (X : R⟦X⟧) ^ (s * s) * ((qfac X s)⁻¹ʳ) ^ 2 := by
    rw [durfee, ← sum_sub_distrib]
    apply dvd_sum
    intro s hs
    have hs' : s ≤ M := Nat.lt_succ_iff.mp (mem_range.mp hs)
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hs'
    have hd := X_pow_dvd_qBinomial_sub (R := R) a s
    rw [show (X : R⟦X⟧) ^ (s * s) * qBinomial X (a + s) s * qBinomial X (a + s) s -
        X ^ (s * s) * ((qfac X s)⁻¹ʳ) ^ 2 = X ^ (s * s) *
        ((qBinomial X (a + s) s - (qfac X s)⁻¹ʳ) *
          (qBinomial X (a + s) s + (qfac X s)⁻¹ʳ)) by ring]
    have hle : a + s + 1 ≤ s * s + (a + 1) := by nlinarith
    exact (pow_dvd_pow _ hle).trans
      (by rw [pow_add]; exact mul_dvd_mul_left _ (dvd_mul_of_dvd_left hd _))
  rw [hbox] at hright
  have hdiff := dvd_sub hright hleft
  rw [show qBinomial (X : R⟦X⟧) (M + M) M -
      ∑ s ∈ range (M + 1), (X : R⟦X⟧) ^ (s * s) * ((qfac X s)⁻¹ʳ) ^ 2 -
      (qBinomial X (M + M) M - (qfac X M)⁻¹ʳ) = (qfac X M)⁻¹ʳ -
      ∑ s ∈ range (M + 1), (X : R⟦X⟧) ^ (s * s) * ((qfac X s)⁻¹ʳ) ^ 2 by ring] at hdiff
  have := X_pow_dvd_iff.mp hdiff N (by omega)
  rwa [map_sub, sub_eq_zero] at this

/-- The generating function of the partitions with parts `≤ M`, through mathlib: below degree
`M + 1` it counts all partitions. -/
theorem coeff_inverse_qfac_eq_card {N M : ℕ} (h : N ≤ M) :
    coeff N (qfac (X : R⟦X⟧) M)⁻¹ʳ = (Fintype.card (Nat.Partition N) : R) := by
  let _ : TopologicalSpace R := ⊥
  have _ : DiscreteTopology R := ⟨rfl⟩
  have hp := Nat.Partition.hasProd_powerSeriesMk_card_restricted R (· ≤ M)
  have hfin := hasProd_prod_of_ne_finset_one (s := range M)
    (f := fun i ↦ if i + 1 ≤ M then ∑' j : ℕ, (X : R⟦X⟧) ^ ((i + 1) * j) else 1)
    (L := SummationFilter.unconditional ℕ) (fun i hi => by
      rw [mem_range, not_lt] at hi
      simp only [show ¬ i + 1 ≤ M by omega, ite_false])
  have heq := hp.unique hfin
  have hmul : (PowerSeries.mk fun n ↦ (#(Nat.Partition.restricted n (· ≤ M)) : R)) *
      qfac (X : R⟦X⟧) M = 1 := by
    rw [heq, qfac, ← prod_mul_distrib]
    apply prod_eq_one
    intro i hi
    rw [mem_range] at hi
    simp only [show i + 1 ≤ M by omega, ite_true, pow_mul]
    exact WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  have hinv : (qfac (X : R⟦X⟧) M)⁻¹ʳ =
      PowerSeries.mk fun n ↦ (#(Nat.Partition.restricted n (· ≤ M)) : R) := by
    rw [← one_mul (qfac (X : R⟦X⟧) M)⁻¹ʳ, ← hmul, Ring.mul_inverse_cancel_right _ _ (isUnit_qfac M)]
  rw [hinv, coeff_mk, Nat.Partition.restricted, filter_true_of_mem, card_univ]
  intro p _ i hi
  exact (Nat.Partition.le_of_mem_parts hi).trans h

/-- **The Durfee identity for the partition function**: the number of partitions of `N` is the
`N`-th coefficient of `Σ_{s ≤ N} q^{s²} / ((1 − q)⋯(1 − q^s))²`. -/
theorem card_partition (N : ℕ) :
    (Fintype.card (Nat.Partition N) : R) =
      coeff N (∑ s ∈ range (N + 1), (X : R⟦X⟧) ^ (s * s) * ((qfac X s)⁻¹ʳ) ^ 2) := by
  rw [← coeff_inverse_qfac_eq_card le_rfl, coeff_inverse_qfac le_rfl]

end Quillen.Notebook1986_7Durfee
