import Mathlib
import Quillen.Upstream.QBinomial

/-!
# Quillen, notebook 1970-14, p. 4: the Euler characteristic of the Tits building of `GL_n(𝔽_q)`

Daniel Quillen's research notebook 1970-14 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201970/1970-14.pdf>) computes,
on p. 4, the Euler characteristic of the poset of proper nonzero subspaces of `𝔽_q^n` by counting
flags: a flag of type `(s_0, …, s_d)` (a composition of `n` into `d + 1` positive parts) is
counted by the `q`-multinomial `[n]!_q / ∏_a [s_a]!_q`, with `[m]!_q = ∏_{b=1}^m (q^b − 1)` (the
page's normalisation), and the alternating sum comes out as `1 + (−1)^n q^{n(n−1)/2}`
(the reduced Euler characteristic is `±q^{n(n−1)/2}`, after Solomon–Tits).

This file proves the identity of the page, for `q` in a field with `q^b ≠ 1` for `b ≥ 1` (so in
particular in `ℚ(q)`, as an identity of rational functions, or at a prime power in `ℚ`), the sum
running over mathlib's `Composition n`:

* `qf q m = ∏_{b=1}^m (q^b − 1)`;
* `qBinomial_mul_qf`: `[n, k]_q · qf k · qf (n − k) = qf n`, in any commutative ring, for the
  Gaussian binomial of `Quillen.Upstream.QBinomial`;
* `sum_compositions`: `∑_{c ⊨ n} (−1)^{ℓ(c)} qf n / ∏ qf(c_a) = (−1)^n q^{n(n−1)/2}`;
* `euler_characteristic`: **the identity of the page**, the sum over compositions with at least
  two parts (`d ≥ 1`), with sign `(−1)^{d+1}`, is `1 + (−1)^n q^{n(n−1)/2}`, for `n ≥ 1`.

The topology (the poset, its order complex and the flag count) is not formalised; the identity
is the combinatorial core.
-/

namespace Quillen.Notebook1970_14

open Finset

section qf

variable {R : Type*} [CommRing R]

/-- `qf q m = ∏_{b=1}^m (q^b − 1)`, the page's `[m]!_q`. -/
def qf (q : R) (m : ℕ) : R := ∏ b ∈ range m, (q ^ (b + 1) - 1)

@[simp] theorem qf_zero (q : R) : qf q 0 = 1 := by simp [qf]

theorem qf_succ (q : R) (m : ℕ) : qf q (m + 1) = qf q m * (q ^ (m + 1) - 1) :=
  prod_range_succ _ _

/-- `[n, k]_q · qf k · qf (n − k) = qf n` for `k ≤ n`. -/
theorem qBinomial_mul_qf (q : R) :
    ∀ n k : ℕ, k ≤ n → qBinomial q n k * qf q k * qf q (n - k) = qf q n
  | n, 0, _ => by simp
  | 0, k + 1, h => absurd h (by omega)
  | n + 1, k + 1, h => by
    rw [qBinomial_succ_succ, show n + 1 - (k + 1) = n - k by omega]
    rcases Nat.lt_or_ge k n with hk | hk
    · obtain ⟨m, rfl⟩ : ∃ m, n = k + 1 + m := ⟨n - (k + 1), by omega⟩
      have h1 := qBinomial_mul_qf q (k + 1 + m) k (by omega)
      have h2 := qBinomial_mul_qf q (k + 1 + m) (k + 1) (by omega)
      rw [show k + 1 + m - k = m + 1 by omega, qf_succ q m] at h1
      rw [show k + 1 + m - (k + 1) = m by omega, qf_succ q k] at h2
      rw [show k + 1 + m - k = m + 1 by omega, qf_succ q k, qf_succ q m, qf_succ q (k + 1 + m)]
      linear_combination (q ^ (k + 1) - 1) * h1 + q ^ (k + 1) * (q ^ (m + 1) - 1) * h2
    · obtain rfl : k = n := by omega
      have h1 := qBinomial_mul_qf q k k le_rfl
      rw [Nat.sub_self, qf_zero] at h1
      rw [Nat.sub_self, qf_zero, qBinomial_eq_zero_of_lt q (Nat.lt_succ_self k), qf_succ q k]
      linear_combination (q ^ (k + 1) - 1) * h1

end qf

variable {K : Type*} [Field K] {q : K} (hq : ∀ b : ℕ, q ^ (b + 1) ≠ 1)
include hq

theorem qf_ne_zero (m : ℕ) : qf q m ≠ 0 :=
  prod_ne_zero_iff.mpr fun b _ => sub_ne_zero.mpr (hq b)

theorem qBinomial_eq_div {n k : ℕ} (h : k ≤ n) :
    qBinomial q n k = qf q n / (qf q k * qf q (n - k)) := by
  rw [eq_div_iff (mul_ne_zero (qf_ne_zero hq k) (qf_ne_zero hq _)), ← mul_assoc,
    qBinomial_mul_qf q n k h]

theorem qBinomial_symm {n k : ℕ} (h : k ≤ n) : qBinomial q n (n - k) = qBinomial q n k := by
  rw [qBinomial_eq_div hq h, qBinomial_eq_div hq (Nat.sub_le n k), Nat.sub_sub_self h, mul_comm]

omit hq

/-- The weight `(−1)^{ℓ} qf m / ∏_a qf(s_a)` of a composition `(s_a)` of `m`. -/
noncomputable def w (q : K) (m : ℕ) (l : List ℕ) : K :=
  (-1) ^ l.length * qf q m / (l.map (qf q)).prod

/-- The blocks of the compositions of `m`, as a finset of lists. -/
def C (m : ℕ) : Finset (List ℕ) := univ.image fun c : Composition m => c.blocks

theorem mem_C {m : ℕ} {l : List ℕ} : l ∈ C m ↔ (∀ x ∈ l, 0 < x) ∧ l.sum = m := by
  simp only [C, mem_image, mem_univ, true_and]
  exact ⟨fun ⟨c, hc⟩ => hc ▸ ⟨fun _ h => c.blocks_pos h, c.blocks_sum⟩,
    fun h => ⟨⟨l, h.1 _, h.2⟩, rfl⟩⟩

theorem C_zero : C 0 = {[]} := by
  ext l
  rw [mem_C, mem_singleton]
  refine ⟨fun ⟨hpos, hsum⟩ => ?_, fun h => by simp [h]⟩
  rcases l with _ | ⟨x, t⟩
  · rfl
  · have := hpos x (by simp)
    simp at hsum
    omega

theorem C_succ (n : ℕ) :
    C (n + 1) = (range (n + 1)).biUnion
      (fun s => (C (n - s)).map ⟨List.cons (s + 1), List.cons_injective⟩) := by
  ext l
  simp only [mem_biUnion, mem_range, mem_map, Function.Embedding.coeFn_mk, mem_C]
  constructor
  · rintro ⟨hpos, hsum⟩
    rcases l with _ | ⟨x, t⟩
    · simp at hsum
    · have hx := hpos x (by simp)
      simp only [List.sum_cons] at hsum
      refine ⟨x - 1, by omega, t, ⟨fun y hy => hpos y (by simp [hy]), by omega⟩, ?_⟩
      rw [Nat.sub_add_cancel hx]
  · rintro ⟨s, hs, t, ⟨hpos, hsum⟩, rfl⟩
    refine ⟨fun y hy => ?_, ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact hpos y hy
    · simp only [List.sum_cons]
      omega

/-- `F m = ∑_{c ⊨ m} (−1)^{ℓ(c)} qf m / ∏ qf(c_a)`. -/
noncomputable def F (q : K) (m : ℕ) : K := ∑ l ∈ C m, w q m l

theorem F_eq_sum_compositions (q : K) (m : ℕ) :
    F q m = ∑ c : Composition m, w q m c.blocks := by
  rw [F, C, sum_image fun c _ d _ h => Composition.ext h]

include hq in
theorem prod_ne_zero' (l : List ℕ) : (l.map (qf q)).prod ≠ 0 := by
  rw [Ne, List.prod_eq_zero_iff]
  simp only [List.mem_map, not_exists, not_and]
  exact fun x _ h => qf_ne_zero hq x h

include hq in
theorem w_cons (n s : ℕ) (hs : s ≤ n) (l : List ℕ) :
    w q (n + 1) ((s + 1) :: l) = -qBinomial q (n + 1) (s + 1) * w q (n - s) l := by
  rw [qBinomial_eq_div hq (by omega), show n + 1 - (s + 1) = n - s by omega]
  have h1 := qf_ne_zero hq (s + 1)
  have h2 := qf_ne_zero hq (n - s)
  have h3 := prod_ne_zero' hq l
  simp only [w, List.length_cons, List.map_cons, List.prod_cons, pow_succ]
  field_simp

include hq in
theorem F_succ (n : ℕ) :
    F q (n + 1) = -∑ s ∈ range (n + 1), qBinomial q (n + 1) (s + 1) * F q (n - s) := by
  rw [F, C_succ, sum_biUnion]
  · rw [← sum_neg_distrib]
    refine sum_congr rfl fun s hs => ?_
    rw [sum_map, F, mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun l _ => ?_
    simp only [Function.Embedding.coeFn_mk]
    rw [w_cons hq n s (by simpa [Nat.lt_succ_iff] using hs), neg_mul]
  · intro s _ s' _ hss'
    simp only [Function.onFun]
    rw [disjoint_left]
    intro l h1 h2
    simp only [mem_map, Function.Embedding.coeFn_mk] at h1 h2
    obtain ⟨a, _, rfl⟩ := h1
    obtain ⟨b, _, hb⟩ := h2
    exact hss' (by have := (List.cons_eq_cons.mp hb).1; omega)

include hq in
/-- The sum over all compositions of `m`: `(−1)^m q^{m(m−1)/2}`. -/
theorem F_eq (m : ℕ) : F q m = (-1) ^ m * q ^ m.choose 2 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | n
    · simp [F, C_zero, w]
    rw [F_succ hq n]
    have hrec : ∀ s ∈ range (n + 1), qBinomial q (n + 1) (s + 1) * F q (n - s) =
        (-1) ^ (n + 1 - (s + 1)) * q ^ (n + 1 - (s + 1)).choose 2 *
          qBinomial q (n + 1) (n + 1 - (n + 1 - (s + 1))) := by
      intro s hs
      have hs' : s ≤ n := by simpa [Nat.lt_succ_iff] using hs
      rw [ih (n - s) (by omega), show n + 1 - (s + 1) = n - s by omega,
        show n + 1 - (n - s) = s + 1 by omega]
      ring
    rw [sum_congr rfl hrec]
    -- the alternating `q`-binomial sum, reflected
    have h0 := sum_neg_one_pow_mul_qBinomial_eq_zero q (n := n + 1) (by omega)
    rw [← sum_range_reflect] at h0
    have h0' : ∑ k ∈ range (n + 1 + 1), (-1) ^ (n + 1 - k) * q ^ (n + 1 - k).choose 2 *
        qBinomial q (n + 1) (n + 1 - (n + 1 - k)) = 0 := by
      rw [← h0]
      refine sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n + 1 := by simpa [Nat.lt_succ_iff] using hk
      rw [Nat.sub_sub_self hk', show n + 1 + 1 - 1 - k = n + 1 - k by omega,
        qBinomial_symm hq hk']
    rw [sum_range_succ'] at h0'
    simp only [Nat.sub_zero, Nat.sub_self, qBinomial_zero_right, mul_one] at h0'
    linear_combination -h0'

include hq in
/-- The sum over compositions, in mathlib's `Composition`. -/
theorem sum_compositions (n : ℕ) :
    ∑ c : Composition n, (-1) ^ c.length * qf q n / (c.blocks.map (qf q)).prod =
      (-1) ^ n * q ^ n.choose 2 := by
  rw [← F_eq hq n, F_eq_sum_compositions]
  rfl

include hq in
/-- **Quillen, notebook 1970-14, p. 4.** For `n ≥ 1`, the sum over the compositions
`(s_0, …, s_d)` of `n` into `d + 1 ≥ 2` parts of `(−1)^{d+1} [n]!_q / ∏_a [s_a]!_q`, with
`[m]!_q = ∏_{b=1}^m (q^b − 1)`, is `1 + (−1)^n q^{n(n−1)/2}`. -/
theorem euler_characteristic {n : ℕ} (hn : 0 < n) :
    ∑ c ∈ univ.filter (fun c : Composition n => 2 ≤ c.length),
        (-1) ^ c.length * qf q n / (c.blocks.map (qf q)).prod =
      1 + (-1) ^ n * q ^ n.choose 2 := by
  have htot := sum_compositions hq n
  rw [← sum_filter_add_sum_filter_not univ (fun c : Composition n => 2 ≤ c.length)] at htot
  have hsingle : univ.filter (fun c : Composition n => ¬ 2 ≤ c.length) =
      {Composition.single n hn} := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_singleton, not_le]
    rw [Composition.eq_single_iff_length hn]
    have := c.length_pos_of_pos hn
    omega
  rw [hsingle, sum_singleton, Composition.single_length, Composition.single_blocks] at htot
  have h := qf_ne_zero hq n
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one,
    neg_one_mul, neg_div, div_self h] at htot
  linear_combination htot

end Quillen.Notebook1970_14
