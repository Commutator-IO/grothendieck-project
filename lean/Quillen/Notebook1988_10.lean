import Mathlib

/-!
# Quillen, notebook 1988-10, pp. 69-70: `Nb = b'N` and `b(1 − t) = (1 − t)b'`

Daniel Quillen's research notebook 1988-10 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201988/1988-10.pdf>),
pp. 69-70. On the chains `A^{⊗(n+1)}` of an associative ring, with the faces
`d_i(a₀, …, a_n) = (a₀, …, a_i a_{i+1}, …, a_n)` (`i < n`), `d_n(a₀, …, a_n) = (a_n a₀, a₁, …)`,
the bar differential `b' = Σ_{i<n} (−1)^i d_i`, the Hochschild differential `b = b' + (−1)^n d_n`,
the cyclic operator `t(a₀, …, a_n) = (−1)^n (a_n, a₀, …, a_{n−1})` and the norm
`N = Σ_{j ≤ n} t^j`, Quillen obtains `Nb = b'N` and `b(1 − t) = (1 − t)b'` (the identities
of the cyclic bicomplex).

*The model.* We prove the transposed identities, on cochains: functions `f : (ℕ → A) → G` with
values in an abelian group `G`, where a cochain of degree `n` is evaluated on
`(a₀, …, a_n)` (the remaining terms of the sequence are ignored by the operators below, and no
linearity is needed). The operators act by precomposition: `δ_i f = f ∘ d_i` (`dual`),
`T f = (−1)^n f ∘ t` (`T`). An identity `PQ = RS` of operators on chains holds on every
elementary tensor if and only if `Q^*P^* = S^*R^*` holds on all such functions (take for `G` the
chains themselves and for `f` the identity), so this form is equivalent to the page's.

* `face_rot_zero`, `face_rot_succ`: the simplicial relations `d₀ t = (−1)^{n+1} d_{n+1}` and
  `d_{i+1} t = −t d_i`, here as identities of sequences;
* `one_sub_T_b` (p. 70): `(1 − T) ∘ b = b' ∘ (1 − T)`, the transpose of `b(1 − t) = (1 − t)b'`;
* `b_N` (p. 69): `b ∘ N = N ∘ b'`, the transpose of `Nb = b'N`, by a bijection between the
  pairs `(j, i)` of the two double sums.
-/

namespace Quillen.Notebook1988_10

open Finset

variable {A : Type*} [Ring A]

/-- The contraction `(a₀, …, a_i a_{i+1}, …)`. -/
def merge (i : ℕ) (a : ℕ → A) : ℕ → A :=
  fun j => if j < i then a j else if j = i then a i * a (i + 1) else a (j + 1)

/-- The last face `(a_m a₀, a₁, …, a_{m−1}, a_{m+1}, …)`. -/
def lastFace (m : ℕ) (a : ℕ → A) : ℕ → A :=
  fun j => if j = 0 then a m * a 0 else if j < m then a j else a (j + 1)

/-- The faces `d_i` of `(a₀, …, a_m)`, `i ≤ m`. -/
def face (m i : ℕ) (a : ℕ → A) : ℕ → A := if i < m then merge i a else lastFace m a

/-- The rotation `(a_m, a₀, …, a_{m−1}, a_{m+1}, …)`. -/
def rot (m : ℕ) (a : ℕ → A) : ℕ → A :=
  fun j => if j = 0 then a m else if j ≤ m then a (j - 1) else a j

/-- `d₀ t = d_{m}` (signs apart), on `m + 1 = n + 2` entries. -/
theorem face_rot_zero (n : ℕ) (a : ℕ → A) :
    face (n + 1) 0 (rot (n + 1) a) = face (n + 1) (n + 1) a := by
  simp only [face, Nat.zero_lt_succ, lt_self_iff_false, ↓reduceIte]
  funext j
  simp only [rot, merge, lastFace]
  split_ifs <;> first | omega | rfl | (congr 1; omega) | simp_all

/-- `d_{i+1} t = t d_i`, for `i ≤ n` (signs apart). -/
theorem face_rot_succ {n i : ℕ} (hi : i ≤ n) (a : ℕ → A) :
    face (n + 1) (i + 1) (rot (n + 1) a) = rot n (face (n + 1) i a) := by
  funext j
  rcases Nat.lt_or_ge i n with h | h
  · simp only [face, show i + 1 < n + 1 by omega, show i < n + 1 by omega, ↓reduceIte, rot, merge]
    split_ifs <;> first | omega | rfl | (congr 1 <;> omega) | (congr 2 <;> omega) | simp_all
  · obtain rfl : i = n := by omega
    simp only [face, lt_self_iff_false, Nat.lt_succ_self, ↓reduceIte, rot, merge, lastFace]
    split_ifs <;> first | omega | rfl | (congr 1; omega) | (congr 2; omega) | simp_all

variable {G : Type*} [AddCommGroup G]

/-- Cochains: functions of sequences. -/
abbrev Cochain (A G : Type*) := (ℕ → A) → G

/-- The transpose of the face `d_i : C_{n+1} → C_n`. -/
def dual (n i : ℕ) : Cochain A G →+ Cochain A G :=
  AddMonoidHom.mk' (fun f a => f (face (n + 1) i a)) fun _ _ => rfl

/-- The transpose of `t` on `C_m`: `(T f)(a) = (−1)^m f(a_m, a₀, …, a_{m−1})`. -/
def T (m : ℕ) : AddMonoid.End (Cochain A G) :=
  AddMonoidHom.mk' (fun f a => ((-1 : ℤ) ^ m) • f (rot m a)) fun f g => by
    funext a; simp [smul_add]

omit [Ring A] in
theorem T_apply (m : ℕ) (f : Cochain A G) (a : ℕ → A) :
    T m f a = ((-1 : ℤ) ^ m) • f (rot m a) := rfl

theorem dual_apply (n i : ℕ) (f : Cochain A G) (a : ℕ → A) :
    dual n i f a = f (face (n + 1) i a) := rfl

/-- The transpose of `b' = Σ_{i ≤ n} (−1)^i d_i : C_{n+1} → C_n`. -/
def b' (n : ℕ) (f : Cochain A G) : Cochain A G :=
  ∑ i ∈ range (n + 1), ((-1 : ℤ) ^ i) • dual n i f

/-- The transpose of `b = Σ_{i ≤ n+1} (−1)^i d_i : C_{n+1} → C_n`. -/
def b (n : ℕ) (f : Cochain A G) : Cochain A G :=
  ∑ i ∈ range (n + 2), ((-1 : ℤ) ^ i) • dual n i f

/-- The transpose of the norm `N = Σ_{j ≤ m} t^j` on `C_m`. -/
def N (m : ℕ) (f : Cochain A G) : Cochain A G := ∑ j ∈ range (m + 1), (T m ^ j) f

/-- `T δ₀ = (−1)^{n+1} δ_{n+1}`. -/
theorem T_dual_zero (n : ℕ) (f : Cochain A G) :
    T (n + 1) (dual n 0 f) = ((-1 : ℤ) ^ (n + 1)) • dual n (n + 1) f := by
  funext a
  simp only [T_apply, dual_apply, face_rot_zero, Pi.smul_apply]

/-- `T δ_{i+1} = −δ_i T` for `i ≤ n`. -/
theorem T_dual_succ {n i : ℕ} (hi : i ≤ n) (f : Cochain A G) :
    T (n + 1) (dual n (i + 1) f) = -dual n i (T n f) := by
  funext a
  simp only [T_apply, dual_apply, face_rot_succ hi, Pi.neg_apply, pow_succ, mul_neg, mul_one,
    neg_smul]

omit [Ring A] in
theorem pow_succ_apply (m j : ℕ) (f : Cochain A G) :
    (T m ^ (j + 1)) f = T m ((T m ^ j) f) := by
  rw [pow_succ']; rfl

/-- `T^j δ_i = (−1)^j δ_{i−j} T^j` for `j ≤ i ≤ n + 1`. -/
theorem T_pow_dual_le {n : ℕ} (f : Cochain A G) : ∀ {i j : ℕ}, j ≤ i → i ≤ n + 1 →
    (T (n + 1) ^ j) (dual n i f) = ((-1 : ℤ) ^ j) • dual n (i - j) ((T n ^ j) f)
  | i, 0, _, _ => by simp
  | i, j + 1, hj, hi => by
    rw [pow_succ_apply, T_pow_dual_le f (by omega) hi, map_zsmul,
      show i - j = (i - (j + 1)) + 1 by omega, T_dual_succ (by omega), ← pow_succ_apply,
      smul_neg, pow_succ (-1 : ℤ) j, mul_neg_one, neg_smul]

/-- `T^{i+1+k} δ_i = (−1)^{i+n+1+k} δ_{n+1−k} T^{i+k}` for `i ≤ n`, `k ≤ n + 1`. -/
theorem T_pow_dual_gt {n i : ℕ} (hi : i ≤ n) (f : Cochain A G) : ∀ {k : ℕ}, k ≤ n + 1 →
    (T (n + 1) ^ (i + 1 + k)) (dual n i f) =
      ((-1 : ℤ) ^ (i + n + 1 + k)) • dual n (n + 1 - k) ((T n ^ (i + k)) f)
  | 0, _ => by
    rw [add_zero, add_zero, pow_succ_apply, T_pow_dual_le f le_rfl (by omega), Nat.sub_self,
      map_zsmul, T_dual_zero, smul_smul, ← pow_add, Nat.sub_zero]
    simp only [add_zero, add_assoc]
  | k + 1, hk => by
    rw [show i + 1 + (k + 1) = (i + 1 + k) + 1 by ring, pow_succ_apply,
      T_pow_dual_gt hi f (by omega), map_zsmul, show n + 1 - k = (n + 1 - (k + 1)) + 1 by omega,
      T_dual_succ (by omega), ← pow_succ_apply, smul_neg, ← neg_smul,
      show i + (k + 1) = i + k + 1 by ring]
    congr 1
    rw [← add_assoc, pow_succ]; ring

/-- **`b(1 − t) = (1 − t)b'`** (p. 70), transposed: `(1 − T) ∘ b = b' ∘ (1 − T)`. -/
theorem one_sub_T_b (n : ℕ) (f : Cochain A G) :
    b n f - T (n + 1) (b n f) = b' n f - b' n (T n f) := by
  -- `T b = (−1)^{n+1} δ_{n+1} + b' T`
  have hTb : T (n + 1) (b n f) = ((-1 : ℤ) ^ (n + 1)) • dual n (n + 1) f + b' n (T n f) := by
    rw [b, sum_range_succ', map_add, map_sum, map_zsmul, T_dual_zero, pow_zero, one_smul, b',
      add_comm]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [map_zsmul, T_dual_succ (Nat.lt_succ_iff.mp (mem_range.mp hi)), smul_neg, pow_succ,
      mul_neg_one, neg_smul, neg_neg]
  rw [hTb, b, sum_range_succ, ← b']
  abel

/-- **`Nb = b'N`** (p. 69), transposed: `b ∘ N = N ∘ b'`. -/
theorem b_N (n : ℕ) (f : Cochain A G) : b n (N n f) = N (n + 1) (b' n f) := by
  simp only [b, N, b', map_sum, map_zsmul, smul_sum]
  rw [sum_comm, ← sum_product', ← sum_product']
  -- reindex `(j, i) ↦ (j, i − j)` for `j ≤ i`, `(j, i) ↦ (j − 1, n + 2 − j + i)` for `i < j`
  symm
  refine sum_nbij' (fun p => if p.2 < p.1 then (p.1 - 1, n + 2 - p.1 + p.2) else (p.1, p.2 - p.1))
    (fun q => if q.2 ≤ n - q.1 then (q.1, q.2 + q.1) else (q.1 + 1, q.2 + q.1 - (n + 1)))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ h
    simp only [mem_product, mem_range] at h ⊢
    split_ifs <;> omega
  · rintro ⟨j, i⟩ h
    simp only [mem_product, mem_range] at h ⊢
    split_ifs <;> omega
  · rintro ⟨j, i⟩ h
    simp only [mem_product, mem_range] at h
    by_cases hij : i < j
    · simp only [hij, ite_true]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      exact Prod.ext_iff.2 ⟨by omega, by omega⟩
    · simp only [hij, ite_false]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      exact Prod.ext_iff.2 ⟨by omega, by omega⟩
  · rintro ⟨j, i⟩ h
    simp only [mem_product, mem_range] at h
    by_cases hij : i ≤ n - j
    · simp only [hij, ite_true]
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      exact Prod.ext_iff.2 ⟨by omega, by omega⟩
    · simp only [hij, ite_false]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      exact Prod.ext_iff.2 ⟨by omega, by omega⟩
  · rintro ⟨j, i⟩ h
    simp only [mem_product, mem_range] at h
    by_cases hij : i < j
    · simp only [hij, ite_true]
      obtain ⟨k, rfl⟩ : ∃ k, j = i + 1 + k := ⟨j - i - 1, by omega⟩
      rw [T_pow_dual_gt (by omega) f (by omega), smul_smul, ← pow_add,
        show n + 2 - (i + 1 + k) + i = n + 1 - k by omega, show i + 1 + k - 1 = i + k by omega]
      congr 1
      rw [show i + (i + n + 1 + k) = (n + 1 - k) + 2 * (i + k) by omega, pow_add (-1 : ℤ),
        pow_mul]
      simp
    · simp only [hij, ite_false]
      rw [T_pow_dual_le f (by omega) (by omega), smul_smul, ← pow_add]
      congr 1
      rw [show i + j = (i - j) + 2 * j by omega, pow_add (-1 : ℤ), pow_mul]
      simp

end Quillen.Notebook1988_10
