import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.ZMod

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

Not proved: the rigidity (the Proposition of pages 121–123: `G₀(t,s) = 0` in
`A[T]/(T^{p^N} − α)` forces a homography), the torsor `Conn₀`, uniqueness of `G₀` up to
sign over `ℤ` (page 72), and the passage from the local model `R[X]` to a smooth curve.
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
    have e : C a * X ^ (n + 1) = X * (C a * X ^ n) := by ring
    rw [e]
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
  constructor
  · intro h n
    rcases lt_or_ge n k with hn | hn
    · simp [Nat.choose_eq_zero_of_lt hn]
    · have := congrArg (fun g => g.coeff (n - k)) h
      simpa [hasseDeriv_coeff, Nat.sub_add_cancel hn] using this
  · intro h
    ext n
    rw [hasseDeriv_coeff, coeff_zero]
    exact h (n + k)

lemma natCast_mul_eq_zero (p : ℕ) [Fact p.Prime] [CharP R p] (c : ℕ) (a : R) :
    (c : R) * a = 0 ↔ p ∣ c ∨ a = 0 := by
  constructor
  · intro h
    by_cases hc : p ∣ c
    · exact Or.inl hc
    · right
      have hz : (c : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
      have hu : IsUnit (c : R) := by
        have := (IsUnit.mk0 _ hz).map (ZMod.castHom (dvd_refl p) R)
        simpa using this
      exact (hu.mul_right_eq_zero).1 h
  · rintro (h | h)
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
    have : n % 2 = 0 := by omega
    rw [this] at l3
    simp at l3
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
    have : n % 3 = 0 := by omega
    rw [this] at l2
    simp at l2
    omega

end Grothendieck.Folder93
