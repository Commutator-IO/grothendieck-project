import Mathlib

/-!
# Quillen, notebook 1982-5: complementary minors, the `K₁` pairing, parametrices

Daniel Quillen's research notebook 1982-5 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201982/1982-5.pdf>) contains,
among determinant-line computations, three algebraic steps checked here.

* p. 15 (and notebook 1985-1, pp. 7-9): for an invertible operator `T` and a projection, the
  determinant of the compressed inverse times `det T` is the determinant of the complementary
  compression — **Jacobi's complementary minor theorem**. In block form:
  `complementary_minor`: if `M = fromBlocks A B C D` is invertible over a commutative ring, then
  `det M · det ((M⁻¹)₂₂) = det A`.
* pp. 55-56: for a bilinear `τ` that is skew and satisfies the cyclic cocycle identity
  `τ(ax, y) − τ(x, ya) + τ(xy, a) = 0`, the map `g ↦ τ(g⁻¹, g)` is a homomorphism on the units
  (`pairing_mul`, `pairing`), and it vanishes on coboundaries `τ(x, y) = φ(xy) − φ(yx)`
  (`coboundary_isCocycle`, `pairing_coboundary`). No linearity of `τ` is used.
* pp. 41, 60: if `PD = 1 − K₀` and `DP = 1 − K₁` in a ring, then
  `P_n = Σ_{k=1}^n (−1)^{k−1} C(n, k) (PD)^{k−1} P` satisfies `P_n D = 1 − K₀ⁿ` and
  `D P_n = 1 − K₁ⁿ` (`parametrix_mul`, `mul_parametrix`); and if `DQ = 1 − p₁` then
  `P − Q = P p₁ − K₀ Q` (`sub_eq_of_parametrices`).
-/

namespace Quillen.Notebook1982_5

open Matrix

section Minor

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]

/-- **Jacobi's complementary minor theorem**, block form: for an invertible block matrix
`M = fromBlocks A B C D`, `det M · det (M⁻¹)₂₂ = det A`. -/
theorem complementary_minor (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R)
    (D : Matrix n n R) (h : IsUnit (fromBlocks A B C D).det) :
    (fromBlocks A B C D).det * ((fromBlocks A B C D)⁻¹.toBlocks₂₂).det = A.det := by
  set M := fromBlocks A B C D with hM
  set N := M⁻¹
  have hMN : M * N = 1 := mul_nonsing_inv M h
  rw [← fromBlocks_toBlocks N, hM, fromBlocks_multiply, ← fromBlocks_one] at hMN
  obtain ⟨-, h12, -, h22⟩ := fromBlocks_inj.mp hMN
  have key : M * fromBlocks 1 N.toBlocks₁₂ 0 N.toBlocks₂₂ = fromBlocks A 0 C 1 := by
    rw [hM, fromBlocks_multiply, h12, h22]; simp
  simpa [det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] using congrArg det key

end Minor

section Pairing

variable {A k : Type*} [Ring A] [AddCommGroup k]

/-- The hypotheses of p. 55: `τ` is skew and a cyclic cocycle. -/
structure IsSkewCocycle (τ : A → A → k) : Prop where
  skew : ∀ x y, τ x y = -τ y x
  cocycle : ∀ a x y, τ (a * x) y - τ x (y * a) + τ (x * y) a = 0

variable {τ : A → A → k}

/-- `τ((gh)⁻¹, gh) = τ(g⁻¹, g) + τ(h⁻¹, h)`. -/
theorem pairing_mul (hτ : IsSkewCocycle τ) (g h : Aˣ) :
    τ ↑(g * h)⁻¹ ↑(g * h) = τ ↑g⁻¹ ↑g + τ ↑h⁻¹ ↑h := by
  have c := hτ.cocycle ↑h⁻¹ ↑g⁻¹ (↑g * ↑h)
  have e1 : (↑h⁻¹ : A) * ↑g⁻¹ = ↑(g * h)⁻¹ := by simp [_root_.mul_inv_rev]
  have e2 : (↑g : A) * ↑h * ↑h⁻¹ = ↑g := by simp [mul_assoc]
  have e3 : (↑g⁻¹ : A) * (↑g * ↑h) = ↑h := by simp [← mul_assoc]
  rw [e1, e2, e3, hτ.skew (↑h) (↑h⁻¹)] at c
  rw [Units.val_mul, ← sub_eq_zero, ← c]
  abel

/-- The pairing `g ↦ τ(g⁻¹, g)` as a homomorphism `Aˣ → k` (written multiplicatively). -/
def pairing (hτ : IsSkewCocycle τ) : Aˣ →* Multiplicative k where
  toFun g := Multiplicative.ofAdd (τ ↑g⁻¹ ↑g)
  map_one' := by simpa using pairing_mul hτ 1 1
  map_mul' g h := by rw [pairing_mul hτ]; rfl

/-- Coboundaries `τ(x, y) = φ(xy) − φ(yx)` are skew cocycles. -/
theorem coboundary_isCocycle (φ : A → k) :
    IsSkewCocycle (fun x y => φ (x * y) - φ (y * x)) where
  skew x y := by abel
  cocycle a x y := by simp only [mul_assoc]; abel

/-- The pairing vanishes on coboundaries. -/
theorem pairing_coboundary (φ : A → k) (g : Aˣ) :
    (fun x y => φ (x * y) - φ (y * x)) ↑g⁻¹ ↑g = 0 := by
  simp

end Pairing

section Parametrix

variable {R : Type*} [Ring R]

/-- `P_n = Σ_{k=1}^n (−1)^{k−1} C(n, k) (PD)^{k−1} P`, indexed from `0`. -/
def Pn (P D : R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range n, ((-1 : ℤ) ^ k * (n.choose (k + 1) : ℤ)) • ((P * D) ^ k * P)

/-- `Σ_{k<n} (−1)^k C(n, k+1) x^{k+1} = 1 − (1 − x)^n`. -/
lemma sum_eq_one_sub_pow (x : R) (n : ℕ) :
    ∑ k ∈ Finset.range n, ((-1 : ℤ) ^ k * (n.choose (k + 1) : ℤ)) • x ^ (k + 1)
      = 1 - (1 - x) ^ n := by
  have h := (Commute.one_right (-x)).add_pow n
  rw [Finset.sum_range_succ'] at h
  rw [show (1 : R) - x = -x + 1 by abel, h]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
  rw [show ∀ S : R, (1 : R) - (S + 1) = -S from fun S => by abel, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [neg_pow x, pow_succ (-1 : R) k, mul_neg_one, mul_assoc,
    ← (Nat.cast_commute (n.choose (k + 1)) (x ^ (k + 1))).eq, ← Int.cast_smul_eq_zsmul R,
    smul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    neg_mul, neg_neg, mul_assoc]

theorem parametrix_mul (P D K₀ : R) (h : P * D = 1 - K₀) (n : ℕ) :
    Pn P D n * D = 1 - K₀ ^ n := by
  rw [Pn, Finset.sum_mul]
  have : K₀ = 1 - P * D := by rw [h]; abel
  rw [this, ← sum_eq_one_sub_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_mul_assoc, mul_assoc, ← pow_succ]

theorem mul_parametrix (P D K₁ : R) (h : D * P = 1 - K₁) (n : ℕ) :
    D * Pn P D n = 1 - K₁ ^ n := by
  rw [Pn, Finset.mul_sum]
  have : K₁ = 1 - D * P := by rw [h]; abel
  rw [this, ← sum_eq_one_sub_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : SemiconjBy D (P * D) (D * P) := by simp [SemiconjBy, mul_assoc]
  rw [mul_smul_comm, ← mul_assoc, (hs.pow_right k).eq, mul_assoc, ← pow_succ]

/-- For `n = 2`: `P₂ = P + K₀ P`. -/
theorem Pn_two (P D K₀ : R) (h : P * D = 1 - K₀) : Pn P D 2 = P + K₀ * P := by
  have : K₀ = 1 - P * D := by rw [h]; abel
  rw [this]
  simp [Pn, Finset.sum_range_succ]
  noncomm_ring

/-- p. 41: `PD = 1 − K₀` and `DQ = 1 − p₁` give `P − Q = P p₁ − K₀ Q`. -/
theorem sub_eq_of_parametrices (P Q D K₀ p₁ : R) (h₀ : P * D = 1 - K₀) (h₁ : D * Q = 1 - p₁) :
    P - Q = P * p₁ - K₀ * Q := by
  have e₀ : K₀ = 1 - P * D := by rw [h₀]; abel
  have e₁ : p₁ = 1 - D * Q := by rw [h₁]; abel
  rw [e₀, e₁]
  noncomm_ring

end Parametrix

end Quillen.Notebook1982_5
