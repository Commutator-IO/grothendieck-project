import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Algebra.CharP.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Algebra.Torsor.Defs
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Choose.Dvd

/-!
# Folder 93, pages 72, 115–123: the Schwarzian difference with divided derivatives

**Partial, and chosen.** The finding `93-integral-schwarzian-level-p2`
(`src/content/findings.ts`) states, from the modernised reading
`transcripts/93/93.modern.tex` (stations III and IX):

> The Schwarzian difference written with divided derivatives,
> `G₀(t,s) = −D⁽³⁾s/D⁽¹⁾s + (D⁽²⁾s/D⁽¹⁾s)² = G/12`, is an `ω^{⊗2}`-valued cocycle defined
> over any base, characteristics 2 and 3 included, and its vanishing forces a homography
> at Frobenius level `p` for `p > 3` but only at level `p²` for `p = 2, 3`.

This file proves the algebraic core, in the local model `R[X]` over an arbitrary
commutative ring `R` (`X` playing the uniformisant `t`, `D k = Polynomial.hasseDeriv k`
the divided derivative `D⁽ᵏ⁾ = (1/k!) dᵏ/dtᵏ`, defined without dividing by `k!`):

* `N f = (D⁽²⁾f)² − D⁽³⁾f · D⁽¹⁾f` and `G0 f = N f / (D⁽¹⁾f)²` (with `Ring.inverse`),
  over any `R`, characteristics 2 and 3 included.
* `Ncl_eq`, `G_eq` (page 120): `G = 12 G₀`, with `G` the classical
  `−2 f⁽³⁾/f' + 3 (f⁽²⁾/f')²`, over any ring (no division by 2 or 3).
* `chain` (Faà di Bruno to order 3), `N_comp` (the cocycle cleared of denominators,
  with no unit hypothesis) and `G0_comp` (the cocycle (II) of pages 115–117:
  `G₀(t, s∘u) = G₀(t, s)∘u · (D⁽¹⁾u)² + G₀(t, u)` when `D⁽¹⁾s`, `D⁽¹⁾u` are units).
* `N_homography`, `G0_homography`, `G0_homography_const` (invariance (1) of page 115):
  if `s · (cX + d) = aX + b`, with `a, b, c, d` killed by `D⁽¹⁾, D⁽²⁾, D⁽³⁾`, then
  `(cX + d)² · N(s) = 0`, hence `G₀(s) = 0` when `cX + d` is a unit.
* `N_X_sq`, `N_X_cube` (page 72): `G₀(t, t²) = 1/(4t²)` (the page writes `1/(2t)`;
  the reading footnotes it) and `G₀(t, t³) = 2/(3t²)`, in cleared form.
* `killed_iff_of_gt`, `killed_iff_two`, `killed_iff_three` (margin of page 121, « OK »):
  over `R` of prime characteristic `p`, `f` is killed by `D⁽¹⁾, D⁽²⁾, D⁽³⁾` iff every
  exponent in `f` is divisible by `p` (`p > 3`), by `4` (`p = 2`), by `9` (`p = 3`);
  `Killed.comp`: every polynomial in a killed `u` is killed.
* `char_two`, `char_three`: in characteristic 2, `D⁽¹⁾(t²) = 0` but
  `G₀(t, t + t²) = 1`; in characteristic 3, `D⁽¹⁾(t³) = D⁽²⁾(t³) = 0` but
  `G₀(t, t + t³) = −1`. Translation by a `p`-th power does not leave `G₀` invariant
  for `p = 2, 3`, which is why the coefficients of the homographies must be taken in
  `O^{p²}` there.

* Rigidity (the Proposition of pages 121–123), in the truncated model
  `B = A[T]/(T^n)` with `α = 0`, written in `A[X]`: `G₀(t, s) = 0` in `B` is `X^n ∣ N s`
  (well defined by `hasseDeriv_X_pow_mul`, `N_add_X_pow_mul` when `n = p^N > 3` in
  characteristic `p`), and `D⁽¹⁾s ∈ B*` is `s₁ ∈ A*`.
  `step` (page 122): if `s · (cX + d)` is affine modulo `X^(j+3)`, the coefficient of `X^j`
  in `(cX + d) · N(s)` is `−C(j+3,3) · s₁ · [X^(j+3)](s · (cX + d))`.
  `rigidity_core`, `rigidity_explicit`, `rigidity`: over any commutative ring `A` in which
  `C(k,3)` is a unit for `3 ≤ k < n`, `X^n ∣ N s` and `s₁ ∈ A*` give `a, b, c ∈ A` with
  `a − bc = s₁` and `s · (cX + 1) ≡ aX + b` modulo `X^n` (`c = −s₂/s₁`).
  `rigidity_of_gt` (`n = p`, any ring of characteristic `p`, no hypothesis on `Pic(A)`),
  `rigidity_iff_of_gt` (with the converse `N_of_homography_trunc`, `p > 3`),
  `rigidity_four` (`n = 4`, level `p²` for `p = 2`: over any ring), `rigidity_nine`
  (`n = 9`, level `p²` for `p = 3`: `C(k,3) ≢ 0 mod 3` for `3 ≤ k ≤ 8`),
  `rigidity_char_zero` (`A` a `ℚ`-algebra, in `A[X]` itself: `s · (cX + 1) = aX + b`).
* `det_one_square`, `det_one_counterexample`: the normalisation « `ad − bc = 1` » added on
  page 121 fails: in `𝔽₅[T]/(T^5)`, `s = 2t` has `G₀ = 0` but is no homography of
  determinant `1`. The determinant `s₁` is a unit, not a square in general.

Not proved: the reduction from `T^(p^N) − α` to `T^(p^N)` for `α ≠ 0` (it is where
`Pic(A) = 0` would enter), the torsor `Conn₀`, uniqueness of `G₀` up to sign over `ℤ`
(page 72), and the passage from the local model to a smooth curve.
Proving these statements says only that they hold as stated; the literature question
of the finding stays open.
-/

open Polynomial
open scoped Ring

namespace Grothendieck.Folder93

variable {R : Type*} [CommRing R]

local notation "D" => Polynomial.hasseDeriv

lemma D_mul_one (f g : R[X]) : D 1 (f * g) = D 1 f * g + f * D 1 g := by
  rw [hasseDeriv_mul]
  simp [Finset.Nat.antidiagonal_succ]
  ring

lemma D_mul_two (f g : R[X]) :
    D 2 (f * g) = D 2 f * g + D 1 f * D 1 g + f * D 2 g := by
  rw [hasseDeriv_mul]
  simp [Finset.Nat.antidiagonal_succ]
  ring

lemma D_mul_three (f g : R[X]) :
    D 3 (f * g) = D 3 f * g + D 2 f * D 1 g + D 1 f * D 2 g + f * D 3 g := by
  rw [hasseDeriv_mul]
  simp [Finset.Nat.antidiagonal_succ]
  ring


@[simp] lemma D1_X : D 1 (X : R[X]) = 1 := by simp
@[simp] lemma D2_X : D 2 (X : R[X]) = 0 := hasseDeriv_X (k := 2) (by norm_num)
@[simp] lemma D3_X : D 3 (X : R[X]) = 0 := hasseDeriv_X (k := 3) (by norm_num)

/-- The chain rule for divided derivatives up to order 3 (Faà di Bruno). -/
theorem chain (s u : R[X]) :
    D 1 (s.comp u) = (D 1 s).comp u * D 1 u ∧
    D 2 (s.comp u) = (D 1 s).comp u * D 2 u + (D 2 s).comp u * D 1 u ^ 2 ∧
    D 3 (s.comp u) = (D 1 s).comp u * D 3 u + 2 * (D 2 s).comp u * D 1 u * D 2 u
      + (D 3 s).comp u * D 1 u ^ 3 := by
  induction s using Polynomial.induction_on with
  | C a =>
    simp [hasseDeriv_C]
  | add f g hf hg =>
    obtain ⟨f1, f2, f3⟩ := hf
    obtain ⟨g1, g2, g3⟩ := hg
    simp only [add_comp, map_add, f1, f2, f3, g1, g2, g3]
    refine ⟨by ring, by ring, by ring⟩
  | monomial n a ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [show C a * X ^ (n + 1) = X * (C a * X ^ n) by ring]
    set w := C a * X ^ n
    simp only [mul_comp, X_comp, D_mul_one, D_mul_two, D_mul_three, D1_X, D2_X, D3_X,
      h1, h2, h3, add_comp, zero_mul, one_mul, add_zero, zero_add]
    refine ⟨by ring, by ring, by ring⟩

/-- Numerator of `G₀`: `G₀(t, f) · (D⁽¹⁾f)² = (D⁽²⁾f)² − D⁽³⁾f · D⁽¹⁾f`. -/
noncomputable def N (f : R[X]) : R[X] := D 2 f ^ 2 - D 3 f * D 1 f

/-- `G₀(t, f) = −D⁽³⁾f / D⁽¹⁾f + (D⁽²⁾f / D⁽¹⁾f)²`, with `Ring.inverse` for the division. -/
noncomputable def G0 (f : R[X]) : R[X] := N f * (D 1 f ^ 2)⁻¹ʳ

/-- Numerator of the classical `G = −2 f⁽³⁾/f' + 3 (f⁽²⁾/f')²`. -/
noncomputable def Ncl (f : R[X]) : R[X] :=
  3 * (derivative^[2] f) ^ 2 - 2 * derivative^[3] f * derivative f

/-- The classical `G`. -/
noncomputable def G (f : R[X]) : R[X] := Ncl f * (derivative f ^ 2)⁻¹ʳ

/-- Page 120: `G = 12 G₀`, cleared of denominators, over any commutative ring. -/
theorem Ncl_eq (f : R[X]) : Ncl f = 12 * N f := by
  have h2 := congrFun (factorial_smul_hasseDeriv (R := R) (k := 2)) f
  have h3 := congrFun (factorial_smul_hasseDeriv (R := R) (k := 3)) f
  simp only [LinearMap.smul_apply] at h2 h3
  rw [Ncl, N, ← h2, ← h3, hasseDeriv_one']
  simp only [Nat.factorial, nsmul_eq_mul]
  push_cast
  ring

/-- Page 120: `G = 12 G₀`. -/
theorem G_eq (f : R[X]) : G f = 12 * G0 f := by
  rw [G, G0, Ncl_eq, hasseDeriv_one', mul_assoc]

/-- The cocycle relation cleared of denominators: no unit hypothesis. -/
theorem N_comp (s u : R[X]) :
    N (s.comp u) = (N s).comp u * D 1 u ^ 4 + ((D 1 s).comp u) ^ 2 * N u := by
  obtain ⟨h1, h2, h3⟩ := chain s u
  simp only [N, h1, h2, h3, sub_comp, mul_comp, pow_comp]
  ring

lemma inverse_comp {x : R[X]} (hx : IsUnit x) (u : R[X]) : (x⁻¹ʳ).comp u = (x.comp u)⁻¹ʳ := by
  obtain ⟨v, rfl⟩ := hx
  have h : (v : R[X]).comp u = ((Units.map (compRingHom u).toMonoidHom v : R[X]ˣ) : R[X]) := rfl
  rw [h, Ring.inverse_unit, Ring.inverse_unit, Units.coe_map_inv]
  rfl

lemma unit_algebra {S : Type*} [CommRing S] {a b n m k : S} (ha : IsUnit a) (hb : IsUnit b)
    (h : n = m * a ^ 4 + b ^ 2 * k) :
    n * ((b * a) ^ 2)⁻¹ʳ = m * (b ^ 2)⁻¹ʳ * a ^ 2 + k * (a ^ 2)⁻¹ʳ := by
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, rfl⟩ := hb
  simp only [← Units.val_mul, ← Units.val_pow_eq_pow_val, Ring.inverse_unit]
  subst h
  have hA : (A : S) * (A⁻¹ : Sˣ) = 1 := A.mul_inv
  have hB : (B : S) * (B⁻¹ : Sˣ) = 1 := B.mul_inv
  push_cast
  rw [mul_inv, Units.val_mul]
  linear_combination (m * (A : S) ^ 2 * ((B⁻¹ : Sˣ) : S) ^ 2 * (A * (A⁻¹ : Sˣ) + 1)) * hA
    + (k * ((A⁻¹ : Sˣ) : S) ^ 2 * (B * (B⁻¹ : Sˣ) + 1)) * hB

/-- Pages 115–117, relation (II): `G₀(t, s∘u) = G₀(u, s∘u) + G₀(t, u)`, where
`G₀(u, s∘u) = G₀(t, s)∘u · (D⁽¹⁾u)²` expresses the quadratic differential in `dt²`. -/
theorem G0_comp (s u : R[X]) (hs : IsUnit (D 1 s)) (hu : IsUnit (D 1 u)) :
    G0 (s.comp u) = (G0 s).comp u * D 1 u ^ 2 + G0 u := by
  have hsu : IsUnit ((D 1 s).comp u) := hs.map (compRingHom u)
  rw [G0, G0, G0, (chain s u).1, mul_comp, inverse_comp (hs.pow 2), pow_comp]
  exact unit_algebra hu hsu (N_comp s u)

/-- `G₀(t, t) = 0`. -/
theorem N_X : N (X : R[X]) = 0 := by simp [N]

theorem G0_X : G0 (X : R[X]) = 0 := by simp [G0, N_X]

/-- Invariance under homographies, cleared of denominators: if `s · q = p` with `p`, `q`
killed by `D⁽²⁾` and `D⁽³⁾`, then `q² · N(s) = 0`. -/
theorem N_homography {s p q : R[X]} (hp2 : D 2 p = 0) (hp3 : D 3 p = 0)
    (hq2 : D 2 q = 0) (hq3 : D 3 q = 0) (h : s * q = p) : q ^ 2 * N s = 0 := by
  have e2 := congrArg (D 2) h
  have e3 := congrArg (D 3) h
  rw [D_mul_two, hp2, hq2] at e2
  rw [D_mul_three, hp3, hq2, hq3] at e3
  rw [N]
  linear_combination (D 2 s * q) * e2 - (D 1 s * q) * e3

lemma D_mul_X_of_const {a : R[X]} (h1 : D 1 a = 0) (h2 : D 2 a = 0) (h3 : D 3 a = 0) :
    D 1 (a * X) = a ∧ D 2 (a * X) = 0 ∧ D 3 (a * X) = 0 := by
  rw [D_mul_one, D_mul_two, D_mul_three, h1, h2, h3, D1_X, D2_X, D3_X]
  simp

/-- Homographies whose coefficients are killed by `D⁽¹⁾, D⁽²⁾, D⁽³⁾` satisfy `G₀ = 0`. -/
theorem G0_homography {s a b c d : R[X]}
    (ha : D 1 a = 0 ∧ D 2 a = 0 ∧ D 3 a = 0) (hb : D 1 b = 0 ∧ D 2 b = 0 ∧ D 3 b = 0)
    (hc : D 1 c = 0 ∧ D 2 c = 0 ∧ D 3 c = 0) (hd : D 1 d = 0 ∧ D 2 d = 0 ∧ D 3 d = 0)
    (hq : IsUnit (c * X + d)) (h : s * (c * X + d) = a * X + b) : G0 s = 0 := by
  obtain ⟨-, a2, a3⟩ := D_mul_X_of_const ha.1 ha.2.1 ha.2.2
  obtain ⟨-, c2, c3⟩ := D_mul_X_of_const hc.1 hc.2.1 hc.2.2
  have key := N_homography (by simp [a2, hb.2.1]) (by simp [a3, hb.2.2])
    (by simp [c2, hd.2.1]) (by simp [c3, hd.2.2]) h
  have hN : N s = 0 := (hq.pow 2).mul_left_cancel (by rw [key, mul_zero])
  simp [G0, hN]

/-- Constant homographies: `a, b, c, d ∈ R`. -/
theorem G0_homography_const {s : R[X]} {a b c d : R} (hq : IsUnit (C c * X + C d))
    (h : s * (C c * X + C d) = C a * X + C b) : G0 s = 0 := by
  have k : ∀ r : R, D 1 (C r) = 0 ∧ D 2 (C r) = 0 ∧ D 3 (C r) = 0 := fun r =>
    ⟨hasseDeriv_C 1 r (by norm_num), hasseDeriv_C 2 r (by norm_num), hasseDeriv_C 3 r (by norm_num)⟩
  exact G0_homography (k a) (k b) (k c) (k d) hq h

/-! ### Test values (page 72) -/

lemma D_X_pow (k n : ℕ) : D k (X ^ n : R[X]) = (n.choose k : R[X]) * X ^ (n - k) := by
  rw [← monomial_one_right_eq_X_pow, hasseDeriv_monomial, mul_one, ← C_mul_X_pow_eq_monomial,
    map_natCast]

/-- `G₀(t, t²) · (2t)² = 1`, so `G₀(t, t²) = 1/(4t²)` where `2` is invertible. -/
theorem N_X_sq : N (X ^ 2 : R[X]) = 1 ∧ D 1 (X ^ 2 : R[X]) = 2 * X := by
  simp only [N, D_X_pow]
  norm_num

/-- `G₀(t, t³) · (3t²)² = 6t²`, so `G₀(t, t³) = 2/(3t²)` where `3` is invertible. -/
theorem N_X_cube : N (X ^ 3 : R[X]) = 6 * X ^ 2 ∧ D 1 (X ^ 3 : R[X]) = 3 * X ^ 2 := by
  simp only [N, D_X_pow]
  norm_num
  ring

/-! ### Characteristics 2 and 3 -/

lemma natCast_eq_zero (p : ℕ) [CharP R p] : (p : R[X]) = 0 := by
  rw [← map_natCast C, CharP.cast_eq_zero, map_zero]

/-- In characteristic 2, `t²` is killed by `D⁽¹⁾` but `G₀(t, t + t²) = 1`. -/
theorem char_two [CharP R 2] :
    D 1 (X ^ 2 : R[X]) = 0 ∧ D 1 (X + X ^ 2 : R[X]) = 1 ∧ G0 (X + X ^ 2 : R[X]) = 1 := by
  have h2 : (2 : R[X]) = 0 := by exact_mod_cast natCast_eq_zero (R := R) 2
  have d1 : D 1 (X + X ^ 2 : R[X]) = 1 := by
    rw [map_add, D_X_pow, D1_X]; norm_num; linear_combination h2
  refine ⟨by rw [D_X_pow]; norm_num; exact h2, d1, ?_⟩
  have n : N (X + X ^ 2 : R[X]) = 1 := by
    simp only [N, map_add, D_X_pow, D1_X, D2_X, D3_X]
    norm_num
  rw [G0, n, d1]
  simp

/-- In characteristic 3, `t³` is killed by `D⁽¹⁾` and `D⁽²⁾` but not by `D⁽³⁾`, and
`G₀(t, t + t³) = −1`. -/
theorem char_three [CharP R 3] :
    D 1 (X ^ 3 : R[X]) = 0 ∧ D 2 (X ^ 3 : R[X]) = 0 ∧ D 3 (X ^ 3 : R[X]) = 1 ∧
      D 1 (X + X ^ 3 : R[X]) = 1 ∧ G0 (X + X ^ 3 : R[X]) = -1 := by
  have h3 : (3 : R[X]) = 0 := by exact_mod_cast natCast_eq_zero (R := R) 3
  have d1 : D 1 (X + X ^ 3 : R[X]) = 1 := by
    rw [map_add, D_X_pow, D1_X]; norm_num; linear_combination X ^ 2 * h3
  refine ⟨by rw [D_X_pow]; norm_num; linear_combination X ^ 2 * h3,
    by rw [D_X_pow]; norm_num; linear_combination h3, by rw [D_X_pow]; norm_num, d1, ?_⟩
  have n : N (X + X ^ 3 : R[X]) = -1 := by
    simp only [N, map_add, D_X_pow, D1_X, D2_X, D3_X]
    norm_num
    linear_combination (2 * X ^ 2) * h3
  rw [G0, n, d1]
  simp

/-! ### The functions killed by `D⁽¹⁾, D⁽²⁾, D⁽³⁾` (margin of page 121) -/

/-- `f` is killed by `D⁽¹⁾`, `D⁽²⁾` and `D⁽³⁾`. -/
def Killed (f : R[X]) : Prop := D 1 f = 0 ∧ D 2 f = 0 ∧ D 3 f = 0

/-- If `u` is killed, so is every polynomial in `u` (by the chain rule). -/
theorem Killed.comp {u : R[X]} (hu : Killed u) (f : R[X]) : Killed (f.comp u) := by
  obtain ⟨h1, h2, h3⟩ := chain f u
  obtain ⟨u1, u2, u3⟩ := hu
  exact ⟨by rw [h1, u1, mul_zero], by rw [h2, u1, u2]; ring, by rw [h3, u1, u2, u3]; ring⟩

lemma hasseDeriv_eq_zero_iff (k : ℕ) (f : R[X]) :
    D k f = 0 ↔ ∀ n, (n.choose k : R) * f.coeff n = 0 := by
  refine ⟨fun h n => ?_, fun h => ext fun n => by
    rw [hasseDeriv_coeff, coeff_zero]; exact h (n + k)⟩
  rcases lt_or_ge n k with hn | hn
  · simp [Nat.choose_eq_zero_of_lt hn]
  · simpa [hasseDeriv_coeff, Nat.sub_add_cancel hn] using congrArg (coeff · (n - k)) h

lemma natCast_isUnit (p : ℕ) [Fact p.Prime] [CharP R p] {m : ℕ} (h : ¬ p ∣ m) :
    IsUnit (m : R) := by
  have hz : (m : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  simpa using (IsUnit.mk0 _ hz).map (ZMod.castHom (dvd_refl p) R)

lemma natCast_mul_eq_zero (p : ℕ) [Fact p.Prime] [CharP R p] (c : ℕ) (a : R) :
    (c : R) * a = 0 ↔ p ∣ c ∨ a = 0 := by
  refine ⟨fun h => or_iff_not_imp_left.2 fun hc => (natCast_isUnit p hc).mul_right_eq_zero.1 h, ?_⟩
  rintro (h | h)
  · rw [(CharP.cast_eq_zero_iff R p c).2 h, zero_mul]
  · rw [h, mul_zero]

/-- In characteristic `p`, `f` is killed if and only if, for every exponent `n` that occurs
in `f`, `p` divides `C(n,1)`, `C(n,2)` and `C(n,3)`. -/
theorem killed_iff (p : ℕ) [Fact p.Prime] [CharP R p] (f : R[X]) :
    Killed f ↔ ∀ n, f.coeff n ≠ 0 → p ∣ n ∧ p ∣ n.choose 2 ∧ p ∣ n.choose 3 := by
  simp only [Killed, hasseDeriv_eq_zero_iff, natCast_mul_eq_zero p]
  constructor
  · rintro ⟨h1, h2, h3⟩ n hn
    exact ⟨by simpa using (h1 n).resolve_right hn, (h2 n).resolve_right hn,
      (h3 n).resolve_right hn⟩
  · intro h
    refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩ <;>
      (by_cases hn : f.coeff n = 0; exact Or.inr hn; left)
    · simpa using (h n hn).1
    · exact (h n hn).2.1
    · exact (h n hn).2.2

/-- Lucas, for `k < p`: `p ∣ n` implies `p ∣ C(n, k)` when `0 < k`. -/
lemma dvd_choose_of_dvd (p : ℕ) [hp : Fact p.Prime] {n k : ℕ} (hk0 : 0 < k) (hkp : k < p)
    (hn : p ∣ n) : p ∣ n.choose k := by
  have := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := p)
  rw [Nat.mod_eq_zero_of_dvd hn, Nat.mod_eq_of_lt hkp, Nat.choose_eq_zero_of_lt hk0,
    zero_mul] at this
  exact Nat.dvd_of_mod_eq_zero this

/-- Margin of page 121, `p > 3`: the killed polynomials are those in `X^p`. -/
theorem killed_iff_of_gt (p : ℕ) [Fact p.Prime] [CharP R p] (hp : 3 < p) (f : R[X]) :
    Killed f ↔ ∀ n, f.coeff n ≠ 0 → p ∣ n := by
  rw [killed_iff p]
  refine forall_congr' fun n => imp_congr_right fun _ => ⟨fun h => h.1, fun h => ⟨h, ?_, ?_⟩⟩
  · exact dvd_choose_of_dvd p (by norm_num) (by omega) h
  · exact dvd_choose_of_dvd p (by norm_num) hp h

/-- Margin of page 121, `p = 2`: the killed polynomials are those in `X^4`. -/
theorem killed_iff_two [CharP R 2] (f : R[X]) :
    Killed f ↔ ∀ n, f.coeff n ≠ 0 → 4 ∣ n := by
  rw [killed_iff 2]
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  have l2 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := 2) (p := 2)
  have l3 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := 3) (p := 2)
  norm_num at l2 l3
  unfold Nat.ModEq at l2 l3
  constructor
  · rintro ⟨h1, h2, -⟩
    omega
  · intro h
    refine ⟨by omega, by omega, ?_⟩
    simp [show n % 2 = 0 by omega] at l3
    omega

/-- Margin of page 121, `p = 3`: the killed polynomials are those in `X^9`. -/
theorem killed_iff_three [CharP R 3] (f : R[X]) :
    Killed f ↔ ∀ n, f.coeff n ≠ 0 → 9 ∣ n := by
  rw [killed_iff 3]
  refine forall_congr' fun n => imp_congr_right fun _ => ?_
  have l2 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := 2) (p := 3)
  have l3 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := 3) (p := 3)
  norm_num at l2 l3
  unfold Nat.ModEq at l2 l3
  constructor
  · rintro ⟨h1, -, h3⟩
    omega
  · intro h
    refine ⟨by omega, ?_, by omega⟩
    simp [show n % 3 = 0 by omega] at l2
    omega

/-! ### Rigidity (the Proposition of pages 121–123) -/

lemma killed_C (r : R) : Killed (C r) :=
  ⟨hasseDeriv_C 1 r (by norm_num), hasseDeriv_C 2 r (by norm_num), hasseDeriv_C 3 r (by norm_num)⟩

lemma D_lin (c d : R) :
    D 1 (C c * X + C d) = C c ∧ D 2 (C c * X + C d) = 0 ∧ D 3 (C c * X + C d) = 0 := by
  obtain ⟨h1, h2, h3⟩ := D_mul_X_of_const (killed_C c).1 (killed_C c).2.1 (killed_C c).2.2
  obtain ⟨k1, k2, k3⟩ := killed_C d
  simp [h2, h3, k2, k3]

/-- The invariance computation with `q = cX + d`, kept with its right-hand side:
`q · N(s) = D⁽²⁾s · D⁽²⁾(sq) − D⁽¹⁾s · D⁽³⁾(sq)`. -/
theorem N_mul_lin (s : R[X]) (c d : R) :
    (C c * X + C d) * N s =
      D 2 s * D 2 (s * (C c * X + C d)) - D 1 s * D 3 (s * (C c * X + C d)) := by
  obtain ⟨q1, q2, q3⟩ := D_lin c d
  rw [D_mul_two, D_mul_three, q1, q2, q3, N]
  ring

lemma coeff_lin_of_two_le (a b : R) {i : ℕ} (hi : 2 ≤ i) : (C a * X + C b).coeff i = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [coeff_add, coeff_C_mul_X, coeff_C]
  simp; omega

/-- The step of page 122: if `s · (cX + d) ≡ aX + b` modulo `X^(j+3)`, the coefficient of
`X^j` in `(cX + d) · N(s)` is `−C(j+3,3) · s₁ · (coefficient of X^(j+3) in s·(cX+d))`. -/
theorem step (s : R[X]) (a b c d : R) (j : ℕ)
    (h : X ^ (j + 3) ∣ s * (C c * X + C d) - (C a * X + C b)) :
    ((C c * X + C d) * N s).coeff j =
      -(((j + 3).choose 3 : ℕ) : R) * s.coeff 1 * (s * (C c * X + C d)).coeff (j + 3) := by
  set r := s * (C c * X + C d) - (C a * X + C b) with hr
  have e : s * (C c * X + C d) = r + (C a * X + C b) := by rw [hr]; ring
  obtain ⟨-, l2, l3⟩ := D_lin a b
  have hD2 : X ^ (j + 1) ∣ D 2 r := X_pow_dvd_iff.2 fun i hi => by
    rw [hasseDeriv_coeff, (X_pow_dvd_iff.1 h) (i + 2) (by omega), mul_zero]
  have hD3 : X ^ j ∣ D 3 r := X_pow_dvd_iff.2 fun i hi => by
    rw [hasseDeriv_coeff, (X_pow_dvd_iff.1 h) (i + 3) (by omega), mul_zero]
  obtain ⟨w2, hw2⟩ := hD2
  obtain ⟨w3, hw3⟩ := hD3
  have c3 : (D 3 r).coeff j = w3.coeff 0 := by
    rw [hw3, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self]
  have rj : r.coeff (j + 3) = (s * (C c * X + C d)).coeff (j + 3) := by
    rw [hr, coeff_sub, coeff_lin_of_two_le a b (by omega), sub_zero]
  have e2 : D 2 (s * (C c * X + C d)) = D 2 r := by rw [e, map_add, l2, add_zero]
  have e3 : D 3 (s * (C c * X + C d)) = D 3 r := by rw [e, map_add, l3, add_zero]
  rw [N_mul_lin, e2, e3, hw2, hw3, coeff_sub,
    show D 2 s * (X ^ (j + 1) * w2) = X ^ (j + 1) * (D 2 s * w2) by ring,
    show D 1 s * (X ^ j * w3) = X ^ j * (D 1 s * w3) by ring,
    coeff_X_pow_mul', coeff_X_pow_mul', ite_eq_right (by omega), ite_eq_left le_rfl, Nat.sub_self,
    mul_coeff_zero, ← c3, hasseDeriv_coeff, hasseDeriv_coeff, ← rj]
  simp
  ring

/-- The induction of pages 121–123, over any commutative ring: if `C(k,3)` is a unit for
`3 ≤ k < n`, `s₁` is a unit, `s · (cX + d)` has no `X²` term and the coefficients of `N(s)`
vanish below `X^(n−3)`, then `s · (cX + d)` is affine modulo `X^n`. -/
theorem rigidity_core (n : ℕ) (hC : ∀ k, 3 ≤ k → k < n → IsUnit ((k.choose 3 : ℕ) : R))
    (s : R[X]) (hs : IsUnit (s.coeff 1)) (c d : R) (h2 : (s * (C c * X + C d)).coeff 2 = 0)
    (hN : ∀ m, m + 3 < n → (N s).coeff m = 0) :
    X ^ n ∣ s * (C c * X + C d) -
      (C ((s * (C c * X + C d)).coeff 1) * X + C ((s * (C c * X + C d)).coeff 0)) := by
  set q := C c * X + C d
  set a := (s * q).coeff 1
  set b := (s * q).coeff 0
  have key : ∀ i, i < n → (s * q - (C a * X + C b)).coeff i = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases lt_or_ge i 3 with h3 | h3
      · interval_cases i <;> simp [a, b, coeff_C, h2]
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' h3
        have hdiv : X ^ (j + 3) ∣ s * q - (C a * X + C b) :=
          X_pow_dvd_iff.2 fun m hm => ih m hm (by omega)
        have hst := step s a b c d j hdiv
        have hz : (q * N s).coeff j = 0 := by
          have : X ^ (j + 1) ∣ N s := X_pow_dvd_iff.2 fun m hm => hN m (by omega)
          exact X_pow_dvd_iff.1 (this.mul_left q) j (by omega)
        rw [hz, neg_mul, neg_mul, zero_eq_neg] at hst
        have u := (hC (j + 3) (by omega) hi).mul hs
        rw [coeff_sub, coeff_lin_of_two_le a b (by omega), sub_zero]
        exact u.mul_right_eq_zero.1 hst
  exact X_pow_dvd_iff.2 key

lemma coeff_mul_lin_zero (s : R[X]) (c d : R) : (s * (C c * X + C d)).coeff 0 = d * s.coeff 0 := by
  rw [mul_add, coeff_add, ← mul_assoc, mul_coeff_zero, coeff_mul_C]
  simp [mul_comm]

lemma coeff_mul_lin_succ (s : R[X]) (c d : R) (i : ℕ) :
    (s * (C c * X + C d)).coeff (i + 1) = c * s.coeff i + d * s.coeff (i + 1) := by
  rw [mul_add, coeff_add, ← mul_assoc, coeff_mul_X, coeff_mul_C, coeff_mul_C]
  ring

/-- The Proposition of pages 121–123 with an explicit homography: for
`c = −s₂/s₁`, `s · (cX + 1) ≡ (s₁ + c s₀) X + s₀` modulo `X^n`. -/
theorem rigidity_explicit (n : ℕ) (hC : ∀ k, 3 ≤ k → k < n → IsUnit ((k.choose 3 : ℕ) : R))
    (s : R[X]) (hs : IsUnit (s.coeff 1)) (hN : ∀ m, m + 3 < n → (N s).coeff m = 0) :
    X ^ n ∣ s * (C (-(s.coeff 2 * (s.coeff 1)⁻¹ʳ)) * X + 1) -
      (C (s.coeff 1 + -(s.coeff 2 * (s.coeff 1)⁻¹ʳ) * s.coeff 0) * X + C (s.coeff 0)) := by
  set c := -(s.coeff 2 * (s.coeff 1)⁻¹ʳ)
  have h2 : (s * (C c * X + C 1)).coeff 2 = 0 := by
    rw [coeff_mul_lin_succ, one_mul]
    have := Ring.inverse_mul_cancel _ hs
    linear_combination (-(s.coeff 2)) * this
  have := rigidity_core n hC s hs c 1 h2 hN
  rwa [coeff_mul_lin_succ, coeff_mul_lin_zero, map_one, zero_add, one_mul, one_mul,
    add_comm (c * _)] at this

/-- The Proposition of pages 121–123 in `B = A[T]/(T^n)` (`G₀(t, s) = 0` in `B` reads
`X^n ∣ N(s)`, and `D⁽¹⁾s` is a unit of `B` iff `s₁` is a unit of `A`), over any commutative
ring `A` in which `C(k,3)` is a unit for `3 ≤ k < n`: `s = (at + b)/(ct + 1)` in `B`, with
`a, b, c ∈ A` and determinant `a − bc = s₁`. -/
theorem rigidity (n : ℕ) (hC : ∀ k, 3 ≤ k → k < n → IsUnit ((k.choose 3 : ℕ) : R))
    (s : R[X]) (hs : IsUnit (s.coeff 1)) (hN : X ^ n ∣ N s) :
    ∃ a b c : R, a - b * c = s.coeff 1 ∧ X ^ n ∣ s * (C c * X + 1) - (C a * X + C b) :=
  ⟨s.coeff 1 + -(s.coeff 2 * (s.coeff 1)⁻¹ʳ) * s.coeff 0, s.coeff 0,
    -(s.coeff 2 * (s.coeff 1)⁻¹ʳ), by ring,
    rigidity_explicit n hC s hs fun m hm => X_pow_dvd_iff.1 hN m (by omega)⟩

/-- Characteristic `p > 3`, `B = A[T]/(T^p)`: the Proposition of pages 121–122, over any
ring of characteristic `p` (no hypothesis on `Pic(A)`). -/
theorem rigidity_of_gt (p : ℕ) [hp : Fact p.Prime] [CharP R p] (s : R[X])
    (hs : IsUnit (s.coeff 1)) (hN : X ^ p ∣ N s) :
    ∃ a b c : R, a - b * c = s.coeff 1 ∧ X ^ p ∣ s * (C c * X + 1) - (C a * X + C b) := by
  refine rigidity p (fun k hk3 hkp => natCast_isUnit p fun hdvd => ?_) s hs hN
  have hf : p ∣ k.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial (show 3 ≤ k from hk3), mul_assoc]
    exact hdvd.mul_right _
  exact absurd ((Nat.Prime.dvd_factorial hp.out).1 hf) (by omega)

/-- `B = A[T]/(T^4)`, the level `p²` for `p = 2` (page 123): only `C(3,3) = 1` occurs, and
the statement holds over any commutative ring. -/
theorem rigidity_four (s : R[X]) (hs : IsUnit (s.coeff 1)) (hN : X ^ 4 ∣ N s) :
    ∃ a b c : R, a - b * c = s.coeff 1 ∧ X ^ 4 ∣ s * (C c * X + 1) - (C a * X + C b) :=
  rigidity 4 (fun k hk3 hk4 => by
    obtain rfl : k = 3 := by omega
    simp) s hs hN

/-- `B = A[T]/(T^9)`, the level `p²` for `p = 3` (page 123, right-hand column):
`C(k,3) ≢ 0 mod 3` for `3 ≤ k ≤ 8`. -/
theorem rigidity_nine [CharP R 3] (s : R[X]) (hs : IsUnit (s.coeff 1)) (hN : X ^ 9 ∣ N s) :
    ∃ a b c : R, a - b * c = s.coeff 1 ∧ X ^ 9 ∣ s * (C c * X + 1) - (C a * X + C b) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine rigidity 9 (fun k hk3 hk9 => natCast_isUnit 3 ?_) s hs hN
  interval_cases k <;> decide

/-- Characteristic `0` (`A` a `ℚ`-algebra), in `A[X]` itself: `N(s) = 0` with `s₁` a unit
forces `s · (cX + 1) = aX + b`. -/
theorem rigidity_char_zero [Algebra ℚ R] (s : R[X]) (hs : IsUnit (s.coeff 1)) (hN : N s = 0) :
    ∃ a b c : R, a - b * c = s.coeff 1 ∧ s * (C c * X + 1) = C a * X + C b := by
  have hC : ∀ k, 3 ≤ k → IsUnit ((k.choose 3 : ℕ) : R) := fun k hk => by
    have h0 : ((k.choose 3 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    simpa using (IsUnit.mk0 _ h0).map (algebraMap ℚ R)
  refine ⟨s.coeff 1 + -(s.coeff 2 * (s.coeff 1)⁻¹ʳ) * s.coeff 0, s.coeff 0,
    -(s.coeff 2 * (s.coeff 1)⁻¹ʳ), by ring, ?_⟩
  set f := s * (C (-(s.coeff 2 * (s.coeff 1)⁻¹ʳ)) * X + 1) -
      (C (s.coeff 1 + -(s.coeff 2 * (s.coeff 1)⁻¹ʳ) * s.coeff 0) * X + C (s.coeff 0))
  have hd := rigidity_explicit (f.natDegree + 1) (fun k hk _ => hC k hk) s hs
    (fun m _ => by rw [hN, coeff_zero])
  have hf : f = 0 := by
    ext i
    rw [coeff_zero]
    rcases lt_or_ge i (f.natDegree + 1) with hi | hi
    · exact X_pow_dvd_iff.1 hd i hi
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  exact sub_eq_zero.1 hf

/-! ### The truncated ring `A[T]/(T^(p^N))` -/

/-- In characteristic `p`, `D⁽ᵏ⁾` for `k < p^N` is `A[X^(p^N)]`-linear on multiples of
`X^(p^N)`; hence it passes to `A[T]/(T^(p^N))`. -/
theorem hasseDeriv_X_pow_mul (p M : ℕ) [hp : Fact p.Prime] [CharP R p] {k : ℕ}
    (hk : k < p ^ M) (g : R[X]) : D k (X ^ (p ^ M) * g) = X ^ (p ^ M) * D k g := by
  rw [hasseDeriv_mul, Finset.sum_eq_single (0, k)]
  · simp
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    have hi : i ≠ 0 := by rintro rfl; simp_all
    rw [D_X_pow, (CharP.cast_eq_zero_iff R[X] p _).2
      (Nat.Prime.dvd_choose_pow hp.out hi (by omega)), zero_mul, zero_mul]
  · simp

/-- `N(s)` modulo `X^(p^N)` depends only on `s` modulo `X^(p^N)` (`3 < p^N`), so
`G₀(t, s) = 0` in `A[T]/(T^(p^N))` reads `X^(p^N) ∣ N(s)`. -/
theorem N_add_X_pow_mul (p M : ℕ) [Fact p.Prime] [CharP R p] (hM : 3 < p ^ M) (s g : R[X]) :
    X ^ (p ^ M) ∣ N (s + X ^ (p ^ M) * g) - N s := by
  rw [N, N, map_add, map_add, map_add, hasseDeriv_X_pow_mul p M (by omega),
    hasseDeriv_X_pow_mul p M (by omega), hasseDeriv_X_pow_mul p M (by omega)]
  exact ⟨2 * D 2 s * D 2 g + X ^ (p ^ M) * D 2 g ^ 2 - D 3 s * D 1 g - D 3 g * D 1 s
    - X ^ (p ^ M) * D 3 g * D 1 g, by ring⟩

lemma X_pow_dvd_of_mul_lin {n : ℕ} {c d : R} (hd : IsUnit d) {F : R[X]}
    (h : X ^ n ∣ F * (C c * X + C d)) : X ^ n ∣ F := by
  rw [X_pow_dvd_iff] at h ⊢
  intro i hi
  induction i with
  | zero => exact hd.mul_right_eq_zero.1 ((coeff_mul_lin_zero F c d).symm.trans (h 0 hi))
  | succ i ih =>
    have := (coeff_mul_lin_succ F c d i).symm.trans (h _ hi)
    rw [ih (by omega), mul_zero, zero_add] at this
    exact hd.mul_right_eq_zero.1 this

/-- The converse in `A[T]/(T^(p^N))`, `3 < p^N`: a homography `(at + b)/(ct + d)` with
`a, b, c, d ∈ A` and `d` a unit has `G₀ = 0`. -/
theorem N_of_homography_trunc (p M : ℕ) [Fact p.Prime] [CharP R p] (hM : 3 < p ^ M)
    (s : R[X]) {a b c d : R} (hd : IsUnit d)
    (h : X ^ (p ^ M) ∣ s * (C c * X + C d) - (C a * X + C b)) : X ^ (p ^ M) ∣ N s := by
  obtain ⟨g, hg⟩ := h
  have e : s * (C c * X + C d) = (C a * X + C b) + X ^ (p ^ M) * g := by
    rw [← hg]; ring
  obtain ⟨-, l2, l3⟩ := D_lin a b
  have key := N_mul_lin s c d
  rw [e, map_add (D 2) (C a * X + C b), map_add (D 3) (C a * X + C b), l2, l3,
    hasseDeriv_X_pow_mul p M (by omega),
    hasseDeriv_X_pow_mul p M (by omega), zero_add, zero_add] at key
  refine X_pow_dvd_of_mul_lin (c := c) hd ⟨D 2 s * D 2 g - D 1 s * D 3 g, ?_⟩
  rw [mul_comm, key]
  ring

/-- The Proposition of pages 121–123 as an equivalence in `A[T]/(T^p)`, `p > 3`. -/
theorem rigidity_iff_of_gt (p : ℕ) [hp : Fact p.Prime] [CharP R p] (hp3 : 3 < p) (s : R[X])
    (hs : IsUnit (s.coeff 1)) :
    X ^ p ∣ N s ↔
      ∃ a b c : R, a - b * c = s.coeff 1 ∧ X ^ p ∣ s * (C c * X + 1) - (C a * X + C b) := by
  refine ⟨rigidity_of_gt p s hs, ?_⟩
  rintro ⟨a, b, c, -, h⟩
  simpa using N_of_homography_trunc p 1 (by simpa using hp3) s (d := 1) isUnit_one
    (by simpa using h)

/-! ### The determinant cannot be normalised to `1` -/

/-- If `uX` is a homography of determinant `1` modulo `X³`, then `u` is a square. -/
theorem det_one_square (u : R) {a b c d : R} (hdet : a * d - b * c = 1)
    (h : X ^ 3 ∣ C u * X * (C c * X + C d) - (C a * X + C b)) : ∃ v, u = v ^ 2 := by
  have h0 := X_pow_dvd_iff.1 h 0 (by norm_num)
  have h1 := X_pow_dvd_iff.1 h 1 (by norm_num)
  rw [coeff_sub, coeff_mul_lin_zero] at h0
  rw [coeff_sub, coeff_mul_lin_succ] at h1
  simp [coeff_C, coeff_X] at h0 h1
  refine ⟨u * d, ?_⟩
  linear_combination (-u) * hdet - u * d * h1 - u * c * h0

/-- Page 121 adds « avec `ad − bc = 1` »: in `𝔽₅[T]/(T^5)`, `s = 2t` has `G₀ = 0` and
`D⁽¹⁾s = 2` a unit, and is `(2t + 0)/(0·t + 1)`, but no homography of determinant `1` gives
it, `2` not being a square mod `5`. -/
theorem det_one_counterexample :
    N (C 2 * X : (ZMod 5)[X]) = 0 ∧ IsUnit ((C 2 * X : (ZMod 5)[X]).coeff 1) ∧
      X ^ 5 ∣ (C 2 * X : (ZMod 5)[X]) * (C 0 * X + C 1) - (C 2 * X + C 0) ∧
      ¬ ∃ a b c d : ZMod 5, a * d - b * c = 1 ∧
        X ^ 5 ∣ (C 2 * X : (ZMod 5)[X]) * (C c * X + C d) - (C a * X + C b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨-, l2, l3⟩ := D_lin (2 : ZMod 5) 0
    rw [map_zero, add_zero] at l2 l3
    simp [N, l2, l3]
  · rw [coeff_C_mul_X]; exact IsUnit.of_mul_eq_one (3 : ZMod 5) (by decide)
  · simp
  · rintro ⟨a, b, c, d, hdet, h⟩
    obtain ⟨v, hv⟩ := det_one_square 2 hdet
      (dvd_trans (pow_dvd_pow X (by norm_num)) h)
    revert v; decide

open CategoryTheory CochainComplex HomComplex

/-! ## Pages 233–235: the derived morphism defined by a torsor

Finding `93-derived-morphism-homotopy-torsor`.

The abelian-group version of pages 234–235: `P` a torsor under an abelian group `G`,
`u : P → Hom⁰(K', K'')`, `k : G → Hom⁻¹(K', K'')` additive with `u(g + p) − u(p) = δ(k g)`
(`δ` is Mathlib's differential of the Hom complex, `dk + kd`), and `u(p)` morphisms of complexes.

* `Gbar`, `ι`, `j`, `e`: the extension `0 → G → Ḡ → ℤ → 0` with `j⁻¹(1) = P`, built as a quotient of
  `G × ℤ[P]` without choosing a point; `ι_injective`, `j_eq_zero_iff`, `j_surjective` (so
  `𝓛 = [G → Ḡ]` is quasi-isomorphic to `ℤ`), `e_injective`, `j_eq_one_iff` (`j⁻¹(1) = P`).
* `φ0`, `φ0_e`, `φ0_ι`, `δ_φ0`: `φ⁰ : Ḡ → Hom⁰` with `φ⁰|_P = u`, `φ⁰ ∘ ι = δ ∘ k`, `δ ∘ φ⁰ = 0`:
  `(k, φ⁰)` is a morphism of complexes `𝓛 → Hom•(K', K'')`.
* `quotient_map_eq`, `derived_map_eq`: the class of `u(p)` in the homotopy category, and in the
  derived category, does not depend on `p`; `φ0_of_j_eq_one`: it is the class `φ` gives on
  `j⁻¹(1)`, the generator of `H⁰(𝓛) = ℤ`.

Not formalised: the sheaf version (where `P` may have no global section and the point is that no
covering is needed), and the de Rham application. -/

section Torsor

variable (G P : Type*) [AddCommGroup G] [AddTorsor G P]

/-- The relations `e(g + p) − e(p) = g` defining `Ḡ`. -/
def barRel : AddSubgroup (G × FreeAbelianGroup P) :=
  AddSubgroup.closure (Set.range fun x : G × P =>
    ((-x.1, FreeAbelianGroup.of (x.1 +ᵥ x.2) - FreeAbelianGroup.of x.2) : G × FreeAbelianGroup P))

/-- `Ḡ`, the extension of `ℤ` by `G` with `j⁻¹(1) = P`, built without choosing a point. -/
abbrev Gbar := (G × FreeAbelianGroup P) ⧸ barRel G P

variable {G P}

/-- `G → Ḡ`. -/
def ι : G →+ Gbar G P := (QuotientAddGroup.mk' _).comp (AddMonoidHom.inl G _)

/-- `P → Ḡ`. -/
def e (p : P) : Gbar G P := QuotientAddGroup.mk' _ (0, FreeAbelianGroup.of p)

/-- `j : Ḡ → ℤ`. -/
def j : Gbar G P →+ ℤ :=
  QuotientAddGroup.lift _ ((FreeAbelianGroup.lift fun _ : P => (1 : ℤ)).comp
    (AddMonoidHom.snd G _)) (by
    rw [barRel, AddSubgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    simp)

theorem j_ι (g : G) : j (ι (P := P) g) = 0 := by simp [j, ι]

theorem j_e (p : P) : j (e (G := G) p) = 1 := by simp [j, e]

theorem ι_add_e (g : G) (p : P) : ι g + e p = e (g +ᵥ p) := by
  have h : ((-g, FreeAbelianGroup.of (g +ᵥ p) - FreeAbelianGroup.of p) :
      G × FreeAbelianGroup P) ∈ barRel G P := AddSubgroup.subset_closure ⟨(g, p), rfl⟩
  simp only [ι, e, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inl_apply,
    QuotientAddGroup.coe_mk', ← QuotientAddGroup.mk_add, QuotientAddGroup.eq]
  convert h using 1
  ext <;> simp
  abel

/-- A retraction of `ι`, depending on a point `p₀`. -/
def r (p₀ : P) : Gbar G P →+ G :=
  QuotientAddGroup.lift _ ((AddMonoidHom.fst G _) +
    (FreeAbelianGroup.lift fun p : P => p -ᵥ p₀).comp (AddMonoidHom.snd G _)) (by
    rw [barRel, AddSubgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    simp [vadd_vsub_assoc])

theorem r_ι (p₀ : P) (g : G) : r p₀ (ι g) = g := by simp [r, ι]

theorem ι_injective : Function.Injective (ι : G →+ Gbar G P) := by
  obtain ⟨p₀⟩ := (inferInstance : Nonempty P)
  exact Function.LeftInverse.injective (r_ι p₀)

/-- Every element of `Ḡ` is `ι g + n • e p₀`. -/
theorem eq_ι_add (p₀ : P) (x : Gbar G P) : x = ι (r p₀ x) + j x • e p₀ := by
  let dif : Gbar G P →+ Gbar G P :=
    AddMonoidHom.id _ - (ι.comp (r p₀) + (zmultiplesHom _ (e p₀)).comp j)
  have hD : dif = 0 := by
    refine QuotientAddGroup.addMonoidHom_ext _ ?_
    set dif' := dif.comp (QuotientAddGroup.mk' (barRel G P))
    have h1 : dif'.comp (AddMonoidHom.inl _ _) = 0 := by
      ext g
      simp [dif', dif, r, ι, j]
    have h2 : dif'.comp (AddMonoidHom.inr _ _) = 0 := by
      ext p
      have h3 := ι_add_e (p -ᵥ p₀) p₀
      rw [vsub_vadd] at h3
      simp only [dif', dif, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.inr_apply,
        AddMonoidHom.sub_apply, AddMonoidHom.id_apply, AddMonoidHom.add_apply,
        AddMonoidHom.zero_apply]
      change e p - (ι (r p₀ (e p)) + zmultiplesHom _ (e p₀) (j (e p))) = 0
      rw [j_e, ← h3, map_add, r_ι]
      simp [r, e]
    ext y
    have hy : y = (AddMonoidHom.inl _ _ y.1) + (AddMonoidHom.inr _ _ y.2) := by ext <;> simp
    rw [AddMonoidHom.zero_comp, AddMonoidHom.zero_apply, hy, map_add,
      ← AddMonoidHom.comp_apply dif' (AddMonoidHom.inl _ _),
      ← AddMonoidHom.comp_apply dif' (AddMonoidHom.inr _ _), h1, h2]
    simp
  have := congrArg (· x) hD
  simpa [dif, sub_eq_zero] using this

/-- The complex `𝓛 = [G → Ḡ]` is quasi-isomorphic to `ℤ`: `ι` is injective (above), its image is
the kernel of `j`, and `j` is onto. -/
theorem j_eq_zero_iff (x : Gbar G P) : j x = 0 ↔ ∃ g, ι g = x := by
  obtain ⟨p₀⟩ := (inferInstance : Nonempty P)
  refine ⟨fun h => ⟨r p₀ x, ?_⟩, fun ⟨g, hg⟩ => hg ▸ j_ι g⟩
  conv_rhs => rw [eq_ι_add p₀ x, h, zero_zsmul, add_zero]

theorem j_surjective : Function.Surjective (j : Gbar G P →+ ℤ) := by
  obtain ⟨p₀⟩ := (inferInstance : Nonempty P)
  exact fun n => ⟨n • e p₀, by rw [map_zsmul, j_e, smul_eq_mul, mul_one]⟩

theorem r_e (p₀ p : P) : r p₀ (e (G := G) p) = p -ᵥ p₀ := by simp [r, e]

/-- `j⁻¹(1) = P`: `e` is a bijection of `P` onto `j⁻¹(1)`. -/
theorem e_injective : Function.Injective (e : P → Gbar G P) := by
  obtain ⟨p₀⟩ := (inferInstance : Nonempty P)
  intro p p' h
  have := congrArg (r p₀) h
  rw [r_e, r_e] at this
  rw [← vsub_vadd p p₀, this, vsub_vadd]

theorem j_eq_one_iff (x : Gbar G P) : j x = 1 ↔ ∃ p, e p = x := by
  obtain ⟨p₀⟩ := (inferInstance : Nonempty P)
  refine ⟨fun h => ⟨r p₀ x +ᵥ p₀, ?_⟩, fun ⟨p, hp⟩ => hp ▸ j_e p⟩
  rw [← ι_add_e]
  conv_rhs => rw [eq_ι_add p₀ x, h, one_zsmul]

section Complex

open CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] {K' K'' : CochainComplex C ℤ}
  (k : G →+ Cochain K' K'' (-1)) (u : P → Cochain K' K'' 0)
  (hu : ∀ (g : G) (p : P), u (g +ᵥ p) - u p = δ (-1) 0 (k g))

/-- `φ⁰ : Ḡ → Hom⁰(K', K'')`, equal to `dk + kd` on `G` and to `u` on `P`. -/
def φ0 : Gbar G P →+ Cochain K' K'' 0 :=
  QuotientAddGroup.lift _ ((((δ_hom ℤ K' K'' (-1) 0).toAddMonoidHom.comp k).comp
      (AddMonoidHom.fst G _)) + (FreeAbelianGroup.lift u).comp (AddMonoidHom.snd G _)) (by
    rw [barRel, AddSubgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, AddMonoidHom.add_apply,
      AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd,
      map_neg, map_sub, FreeAbelianGroup.lift_apply_of, LinearMap.toAddMonoidHom_coe]
    rw [hu]
    simp [δ_hom])

theorem φ0_e (p : P) : φ0 k u hu (e p) = u p := by simp [φ0, e]

/-- `φ⁰ ∘ ι = δ ∘ k`: the square of `φ : 𝓛 → Hom•(K', K'')` in degrees `−1 → 0`. -/
theorem φ0_ι (g : G) : φ0 k u hu (ι g) = δ (-1) 0 (k g) := by simp [φ0, ι, δ_hom]

variable (hc : ∀ p, δ 0 1 (u p) = 0)
include hu hc

/-- `δ ∘ φ⁰ = 0`: the square in degrees `0 → 1`, so `φ` is a morphism of complexes. -/
theorem δ_φ0 (x : Gbar G P) : δ 0 1 (φ0 k u hu x) = 0 := by
  obtain ⟨p₀⟩ := (inferInstance : Nonempty P)
  rw [eq_ι_add p₀ x, map_add, map_zsmul, φ0_ι, φ0_e, δ_add, δ_δ, δ_smul, hc, smul_zero,
    add_zero]

/-- The morphism of complexes `u(p) : K' → K''`. -/
def homOf' (p : P) : K' ⟶ K'' := Cocycle.homOf (Cocycle.mk (u p) 1 (zero_add 1) (hc p))

/-- `k(p' − p)` is a homotopy from `u(p')` to `u(p)`. -/
def homotopy (p p' : P) : Homotopy (homOf' u hc p') (homOf' u hc p) :=
  (Cochain.equivHomotopy _ _).symm ⟨k (p' -ᵥ p), by
    simp only [homOf', Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe]
    rw [← hu, vsub_vadd, sub_add_cancel]⟩

/-- **Pages 234–235.** The class of `u(p)` in the homotopy category does not depend on `p`:
the morphism defined by `(P, u, k)` needs no choice of a point. -/
theorem quotient_map_eq (p p' : P) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (homOf' u hc p) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (homOf' u hc p') :=
  (HomotopyCategory.eq_of_homotopy _ _ (homotopy k u hu hc p p')).symm

omit hc in
/-- The value of `φ⁰` on `j⁻¹(1)` is `u(p)` for some `p`: the class given by `φ` on the
generator of `H⁰(𝓛) = ℤ` is the class of any `u(p)`. -/
theorem φ0_of_j_eq_one (x : Gbar G P) (hx : j x = 1) : ∃ p, φ0 k u hu x = u p := by
  obtain ⟨p, rfl⟩ := (j_eq_one_iff x).1 hx
  exact ⟨p, φ0_e k u hu p⟩

end Complex

section Derived

open CategoryTheory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] {K' K'' : CochainComplex C ℤ}
  (k : G →+ Cochain K' K'' (-1)) (u : P → Cochain K' K'' 0)
  (hu : ∀ (g : G) (p : P), u (g +ᵥ p) - u p = δ (-1) 0 (k g)) (hc : ∀ p, δ 0 1 (u p) = 0)
include hu

/-- The same in the derived category `D(C)`: `(P, u, k)` defines one morphism `K' → K''`. -/
theorem derived_map_eq (p p' : P) :
    DerivedCategory.Q.map (homOf' u hc p) = DerivedCategory.Q.map (homOf' u hc p') :=
  (DerivedCategory.Q_map_eq_of_homotopy (h := homotopy k u hu hc p p')).symm

end Derived

end Torsor

end Grothendieck.Folder93

/-!
## Pages 193–194 and 208: the `p`-curvature in rank one

Over a commutative ring `A` of characteristic `p` with a derivation `D`, in `Module.End ℤ A`
(`μ c` is multiplication by `c`):

* `iterate_leibniz`, `pDerivation`: `Dᵖ` is again a derivation;
* `jacobson`: `(D + μ a)ᵖ = Dᵖ + μ (aᵖ + D^{p-1} a)` (Jacobson's formula in rank one), proved by
  differentiating `(D + t·μ a)ᵖ` in `t` (`Polynomial` over `Module.End ℤ A`);
* `pCurvature_eq_zero`: if `y` is a unit with `D y + a y = 0`, the connection `∇ = D + a` with
  form `ω = -dy/y` has `(∇_D)ᵖ = ∇_{Dᵖ}`: its `p`-curvature vanishes (the easy direction);
* `jacobson_logDeriv`, `jacobson_logDeriv_of_pow_eq_zero`: hence `aᵖ + D^{p-1} a = -(Dᵖ y)/y`,
  and `aᵖ + D^{p-1} a = 0` when `Dᵖ = 0`.
-/

namespace Grothendieck.Folder93.PCurvature

open Finset Polynomial

section CharLemmas

variable {R : Type*} [Ring R] (p : ℕ) [hp : Fact p.Prime] (hR : (p : R) = 0)
include hR

theorem nsmul_choose_eq_zero {k : ℕ} (hk0 : k ≠ 0) (hkp : k < p) (z : R) :
    p.choose k • z = 0 := by
  obtain ⟨j, hj⟩ := Nat.Prime.dvd_choose_self hp.out hk0 hkp
  rw [nsmul_eq_mul, hj, Nat.cast_mul, hR, zero_mul, zero_mul]

theorem eq_zero_of_mul_natCast {n : ℕ} (hn0 : 0 < n) (hnp : n < p) {z : R}
    (h : z * n = 0) : z = 0 := by
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (Nat.coprime_of_lt_prime hn0.ne' hnp hp.out).symm (Nat.Prime.one_lt hp.out)
  have h1 : ((n * k : ℕ) : R) = 1 := by
    rw [← Nat.div_add_mod (n * k) p, hk, Nat.cast_add, Nat.cast_mul, hR, zero_mul, zero_add,
      Nat.cast_one]
  rw [← mul_one z, ← h1, Nat.cast_mul, ← mul_assoc, h, zero_mul]

end CharLemmas

section Abstract

variable {A R : Type*} [Ring R] (M : A → R) (D : A → A) (L : R)
  (hL : ∀ c, L * M c = M c * L + M (D c))
include hL

/-- Leibniz's rule for `Lⁿ` against a family `M c` with `[L, M c] = M (D c)`. -/
theorem pow_mul_eq_sum (n : ℕ) (c : A) :
    L ^ n * M c = ∑ ij ∈ antidiagonal n, n.choose ij.1 • (M (D^[ij.1] c) * L ^ ij.2) := by
  have key : ∀ x j, L * (M x * L ^ j) = M x * L ^ (j + 1) + M (D x) * L ^ j := fun x j => by
    rw [← mul_assoc, hL, add_mul, mul_assoc, ← pow_succ']
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (fun i j => M (D^[i] c) * L ^ j) n, pow_succ',
      mul_assoc, ih, mul_sum]
    simp only [mul_smul_comm, key, smul_add, sum_add_distrib, Function.iterate_succ_apply']
    congr 1
    refine sum_congr rfl fun ⟨i, j⟩ hij => ?_
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]

variable (p : ℕ) [hp : Fact p.Prime] (hR : (p : R) = 0)
include hR

/-- In characteristic `p`, `[Lᵖ, M c] = M (Dᵖ c)`. -/
theorem pow_char_mul (c : A) : L ^ p * M c = M c * L ^ p + M (D^[p] c) := by
  rw [pow_mul_eq_sum M D L hL, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => p.choose i • (M (D^[i] c) * L ^ j)), sum_range_succ', sum_eq_single (p - 1)]
  · simp [Nat.sub_add_cancel (Nat.Prime.one_le hp.out), add_comm]
  · intro k hk hne
    exact nsmul_choose_eq_zero p hR (Nat.succ_ne_zero k) (by simp at hk; omega) _
  · intro h; simp at h; have := (Nat.Prime.one_le hp.out); omega

/-- In characteristic `p`, `∑ᵢ Lⁱ (M c) L^{p-1-i} = M (D^{p-1} c)`. -/
theorem sum_pow_mul_pow (c : A) :
    ∑ i ∈ range p, L ^ i * M c * L ^ (p - 1 - i) = M (D^[p - 1] c) := by
  have hs : ∀ n k, ∑ i ∈ range n, i.choose k = n.choose (k + 1) := fun n k => by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih, Nat.choose_succ_succ', add_comm]
  have step : ∀ i ∈ range p, L ^ i * M c * L ^ (p - 1 - i) =
      ∑ k ∈ range p, i.choose k • (M (D^[k] c) * L ^ (p - 1 - k)) := by
    intro i hi
    rw [mem_range] at hi
    rw [pow_mul_eq_sum M D L hL, Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k j => i.choose k • (M (D^[k] c) * L ^ j)), sum_mul]
    symm
    rw [← sum_subset (range_subset_range.2 (by omega : i + 1 ≤ p)) fun k _ hk => by
      rw [Nat.choose_eq_zero_of_lt (by simp at hk; omega), zero_smul]]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    rw [smul_mul_assoc, mul_assoc, ← pow_add]
    congr 3
    omega
  rw [sum_congr rfl step, sum_comm]
  simp_rw [← sum_smul, hs]
  rw [sum_eq_single (p - 1)]
  · simp [Nat.sub_add_cancel (Nat.Prime.one_le hp.out)]
  · intro k hk hne
    exact nsmul_choose_eq_zero p hR (Nat.succ_ne_zero k) (by simp at hk; omega) _
  · intro h; simp at h; have := (Nat.Prime.one_le hp.out); omega

end Abstract

section Ring

variable {A : Type*} [CommRing A] (D : Derivation ℤ A A)

local notation "μ" => LinearMap.mulLeft ℤ
local notation "δ" => (D : Module.End ℤ A)

/-- Leibniz's rule as an identity of operators: `D ∘ μ c = μ c ∘ D + μ (D c)`. -/
theorem comm_mulLeft (c : A) :
    (D : Module.End ℤ A) * μ c = μ c * (D : Module.End ℤ A) + μ (D c) := by
  ext x; simp [Derivation.leibniz, smul_eq_mul]; ring

variable (p : ℕ) [hp : Fact p.Prime] [CharP A p]

omit hp in
theorem natCast_end : ((p : ℕ) : Module.End ℤ A) = 0 := by
  ext x; simp [Module.End.natCast_apply, nsmul_eq_mul]

/-- **Statement 1.** In characteristic `p`, the iterate `Dᵖ` satisfies Leibniz's rule. -/
theorem iterate_leibniz (x y : A) : D^[p] (x * y) = x * D^[p] y + D^[p] x * y := by
  have := congrArg (· y) (pow_char_mul μ D (D : Module.End ℤ A) (comm_mulLeft D) p
    (natCast_end p) x)
  simpa [Module.End.pow_apply, mul_comm] using this

/-- `Dᵖ` packaged as a derivation. -/
def pDerivation : Derivation ℤ A A :=
  Derivation.mk' ((D : Module.End ℤ A) ^ p) fun x y => by
    simp [Module.End.pow_apply, iterate_leibniz, smul_eq_mul]; ring

theorem pDerivation_apply (x : A) : pDerivation D p x = D^[p] x := by
  simp [pDerivation, Module.End.pow_apply]

/-- **Statement 2 (Jacobson's formula in rank one).** -/
theorem jacobson (a : A) :
    ((D : Module.End ℤ A) + μ a) ^ p = (D : Module.End ℤ A) ^ p + μ (a ^ p + D^[p - 1] a) := by
  set q : (Module.End ℤ A)[X] := C δ + X * C (μ a) with hqdef
  clear_value q
  have hq : ∀ c, q * C (μ c) = C (μ c) * q + C (μ (D c)) := by
    intro c
    have hc : μ a * μ c = μ c * μ a := by ext x; simp; ring
    have hX : C (μ c) * (X * C (μ a)) = X * (C (μ a) * C (μ c)) := by
      rw [← mul_assoc, ← X_mul, mul_assoc, ← C_mul, ← C_mul, hc]
    rw [hqdef, add_mul, mul_add, ← C_mul, comm_mulLeft, C_add, mul_assoc, hX, C_mul]
    abel
  have hP : ((p : ℕ) : (Module.End ℤ A)[X]) = 0 := by
    rw [← map_natCast C, natCast_end, C_0]
  have dq : derivative q = C (μ a) := by simp [hqdef]
  have hdpow : ∀ n, derivative (q ^ n) = ∑ i ∈ range n, q ^ i * C (μ a) * q ^ (n - 1 - i) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, derivative_mul, ih, dq, sum_range_succ, sum_mul]
      refine congrArg₂ (· + ·) (sum_congr rfl fun i hi => ?_) ?_
      · rw [mem_range] at hi
        rw [mul_assoc, ← pow_succ, show n - 1 - i + 1 = n + 1 - 1 - i by omega]
      · simp
  have hd : derivative (q ^ p) = C (μ (D^[p - 1] a)) := by
    rw [hdpow, sum_pow_mul_pow (fun c => C (μ c)) D q hq p hP a]
  have hdeg : q.natDegree ≤ 1 := by
    rw [hqdef, X_mul, add_comm]; exact natDegree_linear_le (a := μ a) (b := δ)
  have ev : ∀ x : Module.End ℤ A, (∀ r, Commute r x) →
      eval₂ (RingHom.id _) x (q ^ p) = (δ + μ a * x) ^ p := by
    intro x hx
    have := map_pow (eval₂RingHom' (RingHom.id _) x hx) q p
    simpa [hqdef, eval₂_X_mul, (hx _).eq] using this
  have key : q ^ p = C (δ ^ p) + C (μ (D^[p - 1] a)) * X + C (μ a ^ p) * X ^ p := by
    ext n : 1
    simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
    have hp2 := (Nat.Prime.two_le hp.out)
    rcases lt_trichotomy n p with h | rfl | h
    · rcases Nat.eq_zero_or_pos n with rfl | hn0
      · rw [coeff_zero_eq_eval_zero, eval, ev 0 fun r => Commute.zero_right r]
        simp; omega
      · have hd' := congrArg (coeff · (n - 1)) hd
        simp only [coeff_derivative, coeff_C, Nat.sub_add_cancel hn0] at hd'
        by_cases hn1 : n = 1
        · subst hn1; simpa [show (1 : ℕ) ≠ p by omega] using hd'
        · simp only [show n - 1 ≠ 0 by omega, ite_false] at hd'
          simp only [show n ≠ 0 by omega, hn1, show n ≠ p by omega, ite_false, add_zero]
          refine eq_zero_of_mul_natCast p (natCast_end p) (z := (q ^ p).coeff n) hn0 h ?_
          rwa [← Nat.cast_add_one, Nat.sub_add_cancel hn0] at hd'
    · simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, ite_false, ite_true, zero_add]
      have hc := coeff_pow_of_natDegree_le (m := n) hdeg
      rw [mul_one] at hc
      rw [hc, hqdef]
      simp
    · rw [coeff_eq_zero_of_natDegree_lt (natDegree_pow_le.trans_lt (by nlinarith))]
      simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ p by omega, ite_false,
        add_zero]
  have h1 := ev 1 fun r => Commute.one_right r
  rw [key, C_mul_X_pow_eq_monomial, C_mul_X_eq_monomial] at h1
  simp only [eval₂_add, eval₂_C, eval₂_monomial, RingHom.id_apply, one_pow, mul_one] at h1
  rw [← h1, LinearMap.pow_mulLeft]
  ext x; simp; ring


omit [CharP A p] in
theorem iterate_one : D^[p] (1 : A) = 0 := by
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel (Nat.Prime.one_le hp.out)).symm⟩
  rw [hm, Function.iterate_succ_apply, Derivation.map_one_eq_zero,
    Function.iterate_fixed (map_zero D)]

/-- **Statement 3 (the easy direction in rank one).** If the unit `y` is horizontal for the
connection `D + a` on `A`, i.e. `D y + a y = 0`, then `(D + a)ᵖ = Dᵖ + ω(Dᵖ)` with
`ω = -dy/y` the connection form: the `p`-curvature `(∇_D)ᵖ - ∇_{Dᵖ}` vanishes. -/
theorem pCurvature_eq_zero (y z a : A) (hu : y * z = 1) (hy : D y + a * y = 0) :
    (δ + μ a) ^ p = δ ^ p + μ (-(D^[p] y) * z) := by
  have h1 : y * D z + z * D y = 0 := by
    have := congrArg D hu
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  have hinv : μ z * μ y = 1 := by ext x; simp [← mul_assoc, mul_comm z y, hu]
  have hconj : δ + μ a = μ y * δ * μ z := by
    ext x
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul]
    linear_combination (-D x - a * x) * hu - x * h1 + x * z * hy
  have hpow : ∀ n, (μ y * δ * μ z) ^ (n + 1) = μ y * δ ^ (n + 1) * μ z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, pow_succ δ (n + 1)]
      calc μ y * δ ^ (n + 1) * μ z * (μ y * δ * μ z)
          = μ y * δ ^ (n + 1) * (μ z * μ y) * δ * μ z := by
            simp only [mul_assoc]
        _ = _ := by rw [hinv, mul_one]; simp only [mul_assoc]
  have hl := iterate_leibniz D p y z
  rw [hu, iterate_one] at hl
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel (Nat.Prime.one_le hp.out)).symm⟩
  rw [hconj, hm, hpow, ← hm, mul_assoc,
    pow_char_mul μ D δ (comm_mulLeft D) p (natCast_end p)]
  ext x
  simp [Module.End.pow_apply, mul_add]
  linear_combination (D^[p] x) * hu - x * hl

/-- Statements 2 and 3 together: `a ^ p + D^{p-1} a = -(Dᵖ y)/y` for `a = -Dy/y`. -/
theorem jacobson_logDeriv (y z a : A) (hu : y * z = 1) (hy : D y + a * y = 0) :
    a ^ p + D^[p - 1] a = -(D^[p] y) * z := by
  have h := congrArg (· 1) ((jacobson D p a).symm.trans (pCurvature_eq_zero D p y z a hu hy))
  simpa [Module.End.pow_apply, iterate_one] using h

/-- When `Dᵖ = 0` (as for `d/dX` on `𝔽_p(X)`), a logarithmic derivative `a = -Dy/y`
satisfies `a ^ p + D^{p-1} a = 0`. -/
theorem jacobson_logDeriv_of_pow_eq_zero (hD : ∀ x, D^[p] x = 0) (y z a : A) (hu : y * z = 1)
    (hy : D y + a * y = 0) : a ^ p + D^[p - 1] a = 0 := by
  rw [jacobson_logDeriv D p y z a hu hy, hD, neg_zero, zero_mul]

end Ring

/-!
## Page 193, an illustration in rank `n` (rank `2` for the examples)

The edition's illustration, not a statement of the page. On `Aⁿ` (`A` commutative of
characteristic `p`, `D` a derivation), the connection `∇ = D + Γ` acts by
`v ↦ D v + Γ v`, `D` applied to each coordinate (`nabla`, `nabla 0` is `D` itself):

* `nabla_comm`: `[∇, c] = D c`, the rule that made `Dᵖ` a derivation in rank one;
* `pCurvature`, `pCurvature_smul`: `ψ = ∇ᵖ - Dᵖ` is `A`-linear (it is `∇ᵖ - ∇_{Dᵖ}` when
  `Dᵖ = 0`, as for `d/dx` on `𝔽_p[x]`);
* `curvMat`, `pCurvature_apply`: `ψ v = Γ_p v` with `Γ₀ = 1`, `Γ_{k+1} = D Γ_k + Γ Γ_k`;
* `curvMat_mul_horizontal`, `curvMat_eq_zero_of_horizontal`: an invertible matrix `Y` of
  horizontal columns gives `Γ_p Y = -Dᵖ Y`, hence `ψ = 0` when `Dᵖ = 0` (the easy direction);
* `curvMat_diagonal_char`: for `Γ` diagonal, `ψ` is diagonal with the rank-one `p`-curvatures
  `aᵖ + D^{p-1} a`;
* `curvMat_unipotent_char`: for `Γ = [[0, f], [0, 0]]`, `ψ = [[0, D^{p-1} f], [0, 0]]`; on
  `𝔽_p[x]` with `f = x^{p-1}`, `ψ = [[0, -1], [0, 0]] ≠ 0` (`curvMat_unipotent_X_pow`), so
  there is no basis of horizontal sections (`not_horizontal_unipotent_X_pow`), although the
  sub-bundle and the quotient are trivial;
* `curvMat_airy_three`, `curvMat_airy_five`: for the Airy connection `Γ = [[0, 1], [x, 0]]`
  (`Dx = 1`), `ψ = [[-1, x], [x², 1]]` in characteristic `3` and
  `ψ = [[x, x²], [x³ - 1, -x]]` in characteristic `5`.
-/

section Rank

variable {A : Type*} [CommRing A] (D : Derivation ℤ A A) {n : ℕ}

/-- The connection `∇ = D + Γ` on `Aⁿ`. -/
def nabla (Γ : Matrix (Fin n) (Fin n) A) : Module.End ℤ (Fin n → A) where
  toFun v i := D (v i) + Γ.mulVec v i
  map_add' v w := by ext i; simp [Matrix.mulVec_add]; ring
  map_smul' m v := by
    ext i; simp only [Pi.smul_apply, map_zsmul, Matrix.mulVec_smul, smul_add, RingHom.id_apply]

/-- Multiplication by `c ∈ A` on `Aⁿ`. -/
def smulEnd (c : A) : Module.End ℤ (Fin n → A) where
  toFun v := c • v
  map_add' := smul_add c
  map_smul' m v := smul_comm c m v

/-- Leibniz's rule `∇ ∘ c = c ∘ ∇ + D c`. -/
theorem nabla_comm (Γ : Matrix (Fin n) (Fin n) A) (c : A) :
    nabla D Γ * smulEnd c = smulEnd c * nabla D Γ + smulEnd (D c) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp [nabla, smulEnd, Matrix.mulVec_smul, smul_eq_mul]; ring

theorem nabla_col (Γ M : Matrix (Fin n) (Fin n) A) (j : Fin n) :
    nabla D Γ (fun i => M i j) = fun i => (M.map D + Γ * M) i j := by
  funext i; simp [nabla, Matrix.mulVec, Matrix.mul_apply, dotProduct]

/-- `Γ₀ = 1`, `Γ_{k+1} = D Γ_k + Γ Γ_k`: the columns of `Γ_k` are `∇ᵏ` of the basis. -/
def curvMat (Γ : Matrix (Fin n) (Fin n) A) : ℕ → Matrix (Fin n) (Fin n) A
  | 0 => 1
  | k + 1 => (curvMat Γ k).map D + Γ * curvMat Γ k

theorem nabla_pow_col (Γ : Matrix (Fin n) (Fin n) A) (k : ℕ) (j : Fin n) :
    (nabla D Γ ^ k) (fun i => (1 : Matrix (Fin n) (Fin n) A) i j) =
      fun i => curvMat D Γ k i j := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, nabla_col]; rfl

theorem nabla_zero_pow (k : ℕ) (v : Fin n → A) :
    (nabla D 0 ^ k) v = fun i => D^[k] (v i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    funext i; simp [nabla, Function.iterate_succ_apply']

theorem curvMat_diagonal (d : Fin n → A) (k : ℕ) : curvMat D (Matrix.diagonal d) k =
    Matrix.diagonal fun i => (((D : Module.End ℤ A) + LinearMap.mulLeft ℤ (d i)) ^ k) 1 := by
  induction k with
  | zero => simp [curvMat]
  | succ k ih =>
    rw [curvMat, ih, Matrix.diagonal_map (map_zero D), Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_add]
    congr 1; funext i; simp [pow_succ']

theorem curvMat_unipotent (f : A) (k : ℕ) :
    curvMat D !![0, f; 0, 0] (k + 1) = !![0, D^[k] f; 0, 0] := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [curvMat]
  | succ k ih =>
    rw [curvMat, ih]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Function.iterate_succ_apply']

theorem curvMat_succ_fin_two (Γ : Matrix (Fin 2) (Fin 2) A) (k : ℕ) (a b c d : A)
    (h : curvMat D Γ k = !![a, b; c, d]) : curvMat D Γ (k + 1) =
      !![D a + (Γ 0 0 * a + Γ 0 1 * c), D b + (Γ 0 0 * b + Γ 0 1 * d);
        D c + (Γ 1 0 * a + Γ 1 1 * c), D d + (Γ 1 0 * b + Γ 1 1 * d)] := by
  rw [curvMat, h]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- The Airy connection `Γ = [[0, 1], [x, 0]]` with `D x = 1`: `Γ₂, …, Γ₅` over any ring. -/
theorem curvMat_airy (x : A) (hx : D x = 1) :
    curvMat D !![0, 1; x, 0] 3 = !![2, x; x ^ 2, 1] ∧
      curvMat D !![0, 1; x, 0] 5 = !![6 * x, x ^ 2; x ^ 3 + 4, 4 * x] := by
  set Γ : Matrix (Fin 2) (Fin 2) A := !![0, 1; x, 0] with hΓ
  have d2 : D 2 = 0 := by exact_mod_cast D.map_natCast 2
  have d4 : D 4 = 0 := by exact_mod_cast D.map_natCast 4
  have h1 : curvMat D Γ 1 = !![0, 1; x, 0] := by
    rw [curvMat_succ_fin_two D Γ 0 1 0 0 1 (Matrix.one_fin_two)]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hΓ]
  have h2 : curvMat D Γ 2 = !![x, 0; 1, x] := by
    rw [curvMat_succ_fin_two D Γ 1 _ _ _ _ h1]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hΓ, hx]
  have h3 : curvMat D Γ 3 = !![2, x; x ^ 2, 1] := by
    rw [curvMat_succ_fin_two D Γ 2 _ _ _ _ h2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hΓ, hx] <;> ring
  have h4 : curvMat D Γ 4 = !![x ^ 2, 2; 4 * x, x ^ 2] := by
    rw [curvMat_succ_fin_two D Γ 3 _ _ _ _ h3]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hΓ, hx, d2, Derivation.leibniz_pow] <;> ring
  refine ⟨h3, ?_⟩
  rw [curvMat_succ_fin_two D Γ 4 _ _ _ _ h4]
  ext i j; fin_cases i <;> fin_cases j <;> simp [hΓ, hx, d2, d4, Derivation.leibniz_pow] <;> ring

/-- In characteristic `3`, the Airy connection has `ψ = [[-1, x], [x², 1]]`. -/
theorem curvMat_airy_three [CharP A 3] (x : A) (hx : D x = 1) :
    curvMat D !![0, 1; x, 0] 3 = !![-1, x; x ^ 2, 1] := by
  have h3 : (3 : A) = 0 := by exact_mod_cast CharP.cast_eq_zero A 3
  rw [(curvMat_airy D x hx).1]
  ext i j; fin_cases i <;> fin_cases j <;> simp; linear_combination h3

/-- In characteristic `5`, the Airy connection has `ψ = [[x, x²], [x³ - 1, -x]]`. -/
theorem curvMat_airy_five [CharP A 5] (x : A) (hx : D x = 1) :
    curvMat D !![0, 1; x, 0] 5 = !![x, x ^ 2; x ^ 3 - 1, -x] := by
  have h5 : (5 : A) = 0 := by exact_mod_cast CharP.cast_eq_zero A 5
  rw [(curvMat_airy D x hx).2]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
    first | linear_combination h5 | linear_combination x * h5

variable (p : ℕ) [hp : Fact p.Prime] [CharP A p]

omit hp in
theorem natCast_endPi : ((p : ℕ) : Module.End ℤ (Fin n → A)) = 0 :=
  LinearMap.ext fun v => funext fun i => by simp [Module.End.natCast_apply, nsmul_eq_mul]

/-- The `p`-curvature `ψ = ∇ᵖ - Dᵖ`. -/
def pCurvature (Γ : Matrix (Fin n) (Fin n) A) : Module.End ℤ (Fin n → A) :=
  nabla D Γ ^ p - nabla D 0 ^ p

/-- **Statement 4.** In characteristic `p`, the `p`-curvature is `A`-linear. -/
theorem pCurvature_smul (Γ : Matrix (Fin n) (Fin n) A) (c : A) (v : Fin n → A) :
    pCurvature D p Γ (c • v) = c • pCurvature D p Γ v := by
  have h : pCurvature D p Γ * smulEnd c = smulEnd c * pCurvature D p Γ := by
    rw [pCurvature, sub_mul, mul_sub,
      pow_char_mul smulEnd D (nabla D Γ) (nabla_comm D Γ) p (natCast_endPi p),
      pow_char_mul smulEnd D (nabla D 0) (nabla_comm D 0) p (natCast_endPi p)]
    abel
  simpa [smulEnd] using congrArg (· v) h

/-- **Statement 5.** `ψ` is the matrix `Γ_p`. -/
theorem pCurvature_apply (Γ : Matrix (Fin n) (Fin n) A) (v : Fin n → A) :
    pCurvature D p Γ v = (curvMat D Γ p).mulVec v := by
  have hcol j : pCurvature D p Γ (fun i => (1 : Matrix (Fin n) (Fin n) A) i j) =
      fun i => curvMat D Γ p i j := by
    rw [pCurvature, LinearMap.sub_apply, nabla_zero_pow, nabla_pow_col]
    funext i
    rw [Pi.sub_apply, Matrix.one_apply]
    split_ifs <;> simp [iterate_one D p, Function.iterate_fixed (map_zero D)]
  have hv : v = ∑ j, v j • fun i => (1 : Matrix (Fin n) (Fin n) A) i j := by
    funext i; simp [Matrix.one_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, pCurvature_smul, hcol]
  funext i; simp [Matrix.mulVec, dotProduct, mul_comm]

/-- **Statement 6 (the easy direction).** If the columns of `Y` are horizontal,
`D Y + Γ Y = 0`, then `Γ_p Y = -Dᵖ Y`. -/
theorem curvMat_mul_horizontal (Γ Y : Matrix (Fin n) (Fin n) A) (hY : Y.map D + Γ * Y = 0) :
    curvMat D Γ p * Y = -Y.map D^[p] := by
  ext i j
  have hcol : nabla D Γ (fun i => Y i j) = 0 := by rw [nabla_col, hY]; rfl
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_le).symm⟩
  have h := congrFun (pCurvature_apply D p Γ fun i => Y i j) i
  rw [pCurvature, LinearMap.sub_apply, nabla_zero_pow, hm, pow_succ, Module.End.mul_apply,
    hcol, map_zero, ← hm] at h
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, eq_neg_iff_add_eq_zero, add_comm] using
    h.symm

/-- A basis of horizontal sections forces `ψ = 0` when `Dᵖ = 0`. -/
theorem curvMat_eq_zero_of_horizontal (hD : ∀ x, D^[p] x = 0) (Γ Y Z : Matrix (Fin n) (Fin n) A)
    (hYZ : Y * Z = 1) (hY : Y.map D + Γ * Y = 0) : curvMat D Γ p = 0 := by
  have h0 : Y.map D^[p] = 0 := by ext; simp [hD]
  rw [← mul_one (curvMat D Γ p), ← hYZ, ← mul_assoc, curvMat_mul_horizontal D p Γ Y hY, h0]
  simp

/-- For `Γ` diagonal, `ψ` is diagonal with the rank-one `p`-curvatures. -/
theorem curvMat_diagonal_char (d : Fin n → A) :
    curvMat D (Matrix.diagonal d) p = Matrix.diagonal fun i => d i ^ p + D^[p - 1] (d i) := by
  rw [curvMat_diagonal]
  congr 1; funext i
  simp [jacobson, Module.End.pow_apply, iterate_one]

omit [CharP A p] in
theorem curvMat_unipotent_char (f : A) :
    curvMat D !![0, f; 0, 0] p = !![0, D^[p - 1] f; 0, 0] := by
  simpa [Nat.sub_add_cancel hp.out.one_le] using curvMat_unipotent D f (p - 1)

end Rank

section Concrete

variable (p : ℕ) [hp : Fact p.Prime]

/-- `d/dx` on `𝔽_p[x]`, as a `ℤ`-derivation. -/
noncomputable def dX : @Derivation ℤ (ZMod p)[X] (ZMod p)[X] _ _ _ (Ring.toIntAlgebra _) _ _ :=
  Derivation.mk' ((derivative : (ZMod p)[X] →ₗ[ZMod p] (ZMod p)[X]).restrictScalars ℤ)
    fun f g => by simp [derivative_mul, smul_eq_mul]; ring

theorem dX_apply (f : (ZMod p)[X]) : dX p f = derivative f := rfl

theorem dX_iterate (k : ℕ) (f : (ZMod p)[X]) : (dX p)^[k] f = derivative^[k] f := rfl

/-- `(d/dx)ᵖ = 0` on `𝔽_p[x]`. -/
theorem dX_iterate_char (f : (ZMod p)[X]) : (dX p)^[p] f = 0 := by
  rw [dX_iterate, iterate_derivative_eq_factorial_smul_sum, nsmul_eq_mul,
    (CharP.cast_eq_zero_iff (ZMod p)[X] p _).2 (Nat.dvd_factorial hp.out.pos le_rfl), zero_mul]

/-- On `𝔽_p[x]`, `∇ = d/dx + [[0, x^{p-1}], [0, 0]]` has `ψ = [[0, -1], [0, 0]]`. -/
theorem curvMat_unipotent_X_pow :
    curvMat (dX p) !![0, X ^ (p - 1); 0, 0] p = !![0, -1; 0, 0] := by
  rw [curvMat_unipotent_char, dX_iterate, iterate_derivative_X_pow_eq_smul,
    Nat.descFactorial_self, ZMod.wilsons_lemma]
  simp

/-- Hence no invertible matrix of horizontal sections exists for it. -/
theorem not_horizontal_unipotent_X_pow :
    ¬ ∃ Y Z : Matrix (Fin 2) (Fin 2) (ZMod p)[X],
      Y * Z = 1 ∧ Y.map (dX p) + !![0, X ^ (p - 1); 0, 0] * Y = 0 := by
  rintro ⟨Y, Z, hYZ, hY⟩
  have := curvMat_eq_zero_of_horizontal (dX p) p (dX_iterate_char p) _ Y Z hYZ hY
  simpa [curvMat_unipotent_X_pow] using congrFun (congrFun this 0) 1

end Concrete

end Grothendieck.Folder93.PCurvature
