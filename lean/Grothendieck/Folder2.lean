import Mathlib

/-!
# Folder 2, pages 9 and 13: a nonzero class with trivial total Chern class

The modernised reading `transcripts/2/2.modern.tex` (« Contre-exemples : la classe de Chern
d'une immersion, et le facteur (r−1)! », pages 9 to 13) computes, for the class `ξ^r` of a
point of `P^r` (`ξ = 1 − L^{-1}`, `ξ^r = Σ (−1)^i binom(r, i) L^{-i}`, `c(L^{-i}) = 1 − iη`),

  `c(ξ^r) = ∏_{i=0}^{r} (1 − iη)^{(−1)^i binom(r,i)} = 1 + (−1)^{r−1} (r−1)! η^r`

in `Ã(P^r) = ℤ[η]/(η^{r+1})` (page 9), and concludes on page 13 that for a divisor `Y`
of class `x'` with `(r−1)! x' = 0`, `c(i_!(O_Y)) = 1`.

This is finding `2-trivial-total-chern-class` of `src/content/findings.ts`. mathlib has
no `K`-group of coherent sheaves and no Chern classes, so what is proved is the algebra of
the two pages, in the splitting-principle model the reading uses: `i_!(O_Y) = [O_Y] ⊗ ξ^r
= Σ_i (−1)^i binom(r, i) ([L^{-i}] − [L^{-i} ⊗ O(−Y)])`, with `c(L^{-i}) = 1 − iη` and
`c(L^{-i} ⊗ O(−Y)) = 1 − y − iη` (`y = x'`, first Chern classes adding), so that

  `c(i_!(O_Y)) = ∏_{i=0}^{r} ((1 − iη) / (1 − y − iη))^{(−1)^i binom(r,i)}`.

Congruences modulo `X^{r+1}` in `A⟦X⟧` are identities in `A[η]/(η^{r+1})`.

* `chernPoint_int` and `chernPoint` (page 9): for `r ≥ 1` and any commutative ring `A`,
  `∏_{i=0}^{r} (1 − iX)^{(−1)^i binom(r,i)} ≡ 1 + (−1)^{r−1} (r−1)! X^r  (mod X^{r+1})`.
  Proof by the logarithmic derivative over `ℤ`: `P'/P = −Σ_m S(m+1) X^m` with
  `S(k) = Σ_i (−1)^i binom(r,i) i^k`, zero for `k < r` and `(−1)^r r!` for `k = r`
  (mathlib's forward differences), then `n p_n = 0` for `n < r` and `r p_r = −S(r)`.
* `chernImmersion` (page 13): for any commutative ring `A` and `y ∈ A` with `1 − y` a unit
  (`y` nilpotent in the geometric case, `chernImmersion_of_isNilpotent`) and
  `(r−1)! · y = 0`, `∏_{i=0}^{r} ((1 − iX)/(1 − y − iX))^{(−1)^i binom(r,i)} ≡ 1`
  modulo `X^{r+1}`. The denominator product is the numerator one rescaled by `(1 − y)^{-1}`,
  so the two agree modulo `X^{r+1}` once `(r−1)! (1 − (1 − y)^{-r}) = 0`.

That the class `i_!(O_Y)` is nonzero in `K(X × P^r)`, and the restriction `r ≥ 3`, are
geometric and not formalised.
-/

open PowerSeries Finset

namespace Folder2

/-- The exponent `(−1)^i binom(r, i)`. -/
def ε (r i : ℕ) : ℤ := (-1) ^ i * r.choose i

variable {A : Type*} [CommRing A]

/-- The unit `w − aX` of `A⟦X⟧`, for a unit `w` of `A`. -/
noncomputable def lin (w : Aˣ) (a : A) : A⟦X⟧ˣ :=
  (show IsUnit (C (w : A) - C a * X : A⟦X⟧) from
    isUnit_iff_constantCoeff.2 (by simp)).unit

@[simp] theorem coe_lin (w : Aˣ) (a : A) : (lin w a : A⟦X⟧) = C (w : A) - C a * X := rfl

/-- The product `∏_{i=0}^{r} u_i ^ ((−1)^i binom(r, i))`. -/
noncomputable def altProd (r : ℕ) (u : ℕ → A⟦X⟧ˣ) : A⟦X⟧ˣ :=
  ∏ i ∈ range (r + 1), u i ^ ε r i

/-! ### The logarithmic derivative -/

theorem derivative_pow_units (u : A⟦X⟧ˣ) (n : ℕ) :
    d⁄dX (↑(u ^ n) : A⟦X⟧) = n * (↑(u ^ n) * ↑u⁻¹ * d⁄dX (↑u : A⟦X⟧)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, Derivation.leibniz, ih]
    simp only [smul_eq_mul, Nat.cast_succ]
    linear_combination (-(↑(u ^ n) * d⁄dX (↑u : A⟦X⟧))) * Units.mul_inv u

theorem derivative_zpow_units (u : A⟦X⟧ˣ) (n : ℤ) :
    d⁄dX (↑(u ^ n) : A⟦X⟧) = n * (↑(u ^ n) * ↑u⁻¹ * d⁄dX (↑u : A⟦X⟧)) := by
  rcases n with n | n
  · simpa using derivative_pow_units u n
  · rw [zpow_negSucc, derivative_inv, derivative_pow_units]
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
    linear_combination (-(↑(u ^ (n + 1))⁻¹ : A⟦X⟧) * ↑u⁻¹ * d⁄dX (↑u : A⟦X⟧) *
      ((n : A⟦X⟧) + 1)) * Units.mul_inv (u ^ (n + 1))

theorem derivative_prod_units {ι : Type*} (s : Finset ι) (w : ι → A⟦X⟧ˣ) :
    d⁄dX (↑(∏ i ∈ s, w i) : A⟦X⟧) =
      ↑(∏ i ∈ s, w i) * ∑ i ∈ s, ↑(w i)⁻¹ * d⁄dX (↑(w i) : A⟦X⟧) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, Units.val_mul, Derivation.leibniz, ih]
    simp only [smul_eq_mul]
    linear_combination (-(↑(∏ i ∈ s, w i) * d⁄dX (↑(w a) : A⟦X⟧))) * Units.mul_inv (w a)

theorem coe_lin_one_inv (a : A) : (↑(lin 1 a)⁻¹ : A⟦X⟧) = mk fun m => a ^ m := by
  rw [Units.inv_eq_of_mul_eq_one_left]
  simpa [rescale_mk, rescale_X, map_sub] using
    congr(rescale a $(mk_one_mul_one_sub_eq_one (S := A)))

theorem eps_mul_pow {r i : ℕ} (k : ℕ) (hi : i ∈ range (r + 1)) :
    ε r i * (i : ℤ) ^ k = (-1) ^ r * ((-1) ^ (r - i) * r.choose i * (i : ℤ) ^ k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (mem_range.1 hi))
  rw [ε, Nat.add_sub_cancel_left, pow_add]
  have hsq : ((-1 : ℤ) ^ j) ^ 2 = 1 := by rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
  linear_combination (-((-1 : ℤ) ^ i * ((i + j).choose i : ℤ) * (i : ℤ) ^ k)) * hsq

/-- The sums `S(k) = Σ_i (−1)^i binom(r,i) i^k` vanish for `k < r` (forward differences). -/
theorem sum_eps_pow_of_lt {r k : ℕ} (h : k < r) :
    ∑ i ∈ range (r + 1), ε r i * (i : ℤ) ^ k = 0 := by
  have := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) h) 0
  rw [fwdDiff_iter_eq_sum_shift] at this
  simp only [Pi.zero_apply, zero_add, nsmul_eq_mul, mul_one, smul_eq_mul] at this
  rw [sum_congr rfl fun i hi => eps_mul_pow k hi, ← mul_sum, this, mul_zero]

/-- `S(r) = (−1)^r r!`. -/
theorem sum_eps_pow_self (r : ℕ) :
    ∑ i ∈ range (r + 1), ε r i * (i : ℤ) ^ r = (-1) ^ r * r.factorial := by
  have := congrFun (fwdDiff_iter_eq_factorial (R := ℤ) (n := r)) 0
  rw [fwdDiff_iter_eq_sum_shift] at this
  simp only [Pi.natCast_apply, zero_add, nsmul_eq_mul, mul_one, smul_eq_mul] at this
  rw [sum_congr rfl fun i hi => eps_mul_pow r hi, ← mul_sum, this]

theorem logDeriv_zpow (u : A⟦X⟧ˣ) (n : ℤ) :
    ↑(u ^ n)⁻¹ * d⁄dX (↑(u ^ n) : A⟦X⟧) = n * (↑u⁻¹ * d⁄dX (↑u : A⟦X⟧)) := by
  rw [derivative_zpow_units]
  linear_combination ((n : A⟦X⟧) * ↑u⁻¹ * d⁄dX (↑u : A⟦X⟧)) * Units.inv_mul (u ^ n)

/-! ### Page 9 -/

/-- **Page 9**, over `ℤ`: `∏ (1 − iX)^{(−1)^i binom(r,i)} ≡ 1 + (−1)^{r−1}(r−1)! X^r`
modulo `X^{r+1}`. -/
theorem chernPoint_int {r : ℕ} (hr : 1 ≤ r) :
    X ^ (r + 1) ∣ (↑(altProd r fun i => lin 1 (i : ℤ)) : ℤ⟦X⟧) -
      (1 + C ((-1) ^ (r - 1) * ((r - 1).factorial : ℤ)) * X ^ r) := by
  set P : ℤ⟦X⟧ := ↑(altProd r fun i => lin 1 (i : ℤ)) with hPdef
  set L : ℤ⟦X⟧ := mk fun m => -∑ i ∈ range (r + 1), ε r i * (i : ℤ) ^ (m + 1)
  have hD : derivative (R := ℤ) P = P * L := by
    rw [hPdef, altProd, derivative_prod_units]
    congr 1
    simp only [logDeriv_zpow, coe_lin_one_inv]
    ext m
    have hd (i : ℕ) : derivative (R := ℤ) (↑(lin 1 (i : ℤ)) : ℤ⟦X⟧) = C (-(i : ℤ)) := by
      ext (_ | n) <;> simp
    simp only [hd, L, coeff_mk, map_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← map_intCast (C (R := ℤ)), coeff_C_mul, coeff_mul_C, coeff_mk]
    simp only [Int.cast_id]
    ring
  have hL : ∀ m, m + 1 < r → coeff m L = 0 := fun m hm => by
    simp [L, sum_eps_pow_of_lt hm]
  have hLr : coeff (r - 1) L = -((-1) ^ r * r.factorial) := by
    simp [L, Nat.sub_add_cancel hr, sum_eps_pow_self]
  have hP0 : constantCoeff P = 1 := by
    have := congrArg Units.val (show Units.map (constantCoeff (R := ℤ)).toMonoidHom
        (altProd r fun i => lin 1 (i : ℤ)) = 1 by
      rw [altProd, map_prod]
      exact prod_eq_one fun i _ => by
        rw [map_zpow, show Units.map (constantCoeff (R := ℤ)).toMonoidHom (lin 1 (i : ℤ)) = 1
          from Units.ext (by simp), one_zpow])
    simpa [P] using this
  have hcoef : ∀ n, coeff (n + 1) P * (n + 1) =
      ∑ p ∈ antidiagonal n, coeff p.1 P * coeff p.2 L := fun n => by
    rw [← coeff_derivative, hD, coeff_mul]
  have hlow : ∀ n, n + 1 < r → coeff (n + 1) P = 0 := fun n hn => by
    have h := hcoef n
    rw [sum_eq_zero fun p hp => by
      rw [hL p.2 (by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp; omega), mul_zero]] at h
    exact (mul_eq_zero.1 h).resolve_right (by positivity)
  have htop : coeff r P = (-1) ^ (r - 1) * ((r - 1).factorial : ℤ) := by
    have hs : ∑ p ∈ antidiagonal (r - 1), coeff p.1 P * coeff p.2 L =
        coeff 0 P * coeff (r - 1) L := by
      refine sum_eq_single_of_mem (0, r - 1) (by simp) fun p hp hne => ?_
      rcases p with ⟨_ | a, b⟩
      · simp_all
      · simp [hL b (by simp at hp; omega)]
    have h := hcoef (r - 1)
    rw [hs, coeff_zero_eq_constantCoeff_apply, hP0, hLr] at h
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' hr
    simp only [Nat.add_sub_cancel, Nat.factorial_succ] at h ⊢
    have h' : (coeff (s + 1) P - (-1) ^ s * (s.factorial : ℤ)) * ((s : ℤ) + 1) = 0 := by
      push_cast at h; linear_combination h
    linear_combination (mul_eq_zero.1 h').resolve_right (by positivity)
  refine X_pow_dvd_iff.2 fun m hm => ?_
  rcases m with _ | n
  · simp [hP0, show r ≠ 0 by omega]
  · rw [map_sub, map_add, coeff_C_mul_X_pow, coeff_one]
    rcases (Nat.lt_succ_iff.1 hm).lt_or_eq with h | h
    · simp [hlow n h, h.ne]
    · rw [h, htop]; simp [show r ≠ 0 by omega]

/-- **Page 9**, over any commutative ring `A`: in `A[η]/(η^{r+1})`,
`∏_{i=0}^{r} (1 − iη)^{(−1)^i binom(r,i)} = 1 + (−1)^{r−1}(r−1)! η^r`. -/
theorem chernPoint {r : ℕ} (hr : 1 ≤ r) :
    X ^ (r + 1) ∣ (↑(altProd r fun i => lin 1 (i : A)) : A⟦X⟧) -
      (1 + C ((-1) ^ (r - 1) * ((r - 1).factorial : A)) * X ^ r) := by
  have h := map_dvd (PowerSeries.map (Int.castRingHom A)) (chernPoint_int hr)
  have hP : PowerSeries.map (Int.castRingHom A) ↑(altProd r fun i => lin 1 (i : ℤ)) =
      ↑(altProd r fun i => lin 1 (i : A)) :=
    congrArg Units.val (show Units.map (PowerSeries.map (Int.castRingHom A)).toMonoidHom
        (altProd r fun i => lin 1 (i : ℤ)) = altProd r fun i => lin 1 (i : A) by
      simp only [altProd, map_prod, map_zpow]
      exact prod_congr rfl fun i _ => congrArg (· ^ ε r i) (Units.ext (by simp)))
  rw [map_sub, hP] at h
  simpa [map_add, map_mul, map_pow, map_C, map_X] using h

theorem rescale_C (a c : A) : rescale a (C c) = C c := by
  ext (_ | n) <;> simp [coeff_rescale, coeff_C]

theorem prod_zpow_eq_zpow_sum {G : Type*} [CommGroup G] {ι : Type*} (c : G) (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, c ^ f i = c ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, zpow_add]

/-! ### Page 13 -/

/-- **Page 13.** For `y ∈ A` with `1 − y` a unit and `(r−1)! · y = 0`, in `A[η]/(η^{r+1})`:
`∏_{i=0}^{r} ((1 − iη) / (1 − y − iη))^{(−1)^i binom(r,i)} = 1`, that is
`c(i_!(O_Y)) = 1` in the splitting-principle model, `y = x'`. -/
theorem chernImmersion {r : ℕ} (hr : 1 ≤ r) {y : A} (hy : IsUnit (1 - y))
    (h : ((r - 1).factorial : A) * y = 0) :
    X ^ (r + 1) ∣ (↑(∏ i ∈ range (r + 1),
      (lin 1 (i : A) * (lin hy.unit (i : A))⁻¹) ^ ε r i) : A⟦X⟧) - 1 := by
  set w := hy.unit
  set a : A := ↑w⁻¹
  have haw : a * (1 - y) = 1 := by simp [a, w]
  -- the denominators are the numerators rescaled by `a = (1 − y)⁻¹`
  have hlin (i : ℕ) : lin w (i : A) =
      Units.map (C (R := A)).toMonoidHom w * Units.map (rescale a).toMonoidHom (lin 1 (i : A)) := by
    refine Units.ext ?_
    change C (w : A) - C (i : A) * X = C (w : A) * rescale a (C 1 - C (i : A) * X)
    have hwa : C (w : A) * C a = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    rw [map_sub, map_mul, rescale_C, rescale_C, rescale_X, map_one]
    linear_combination (C (i : A) * X) * hwa
  have hsum : ∑ i ∈ range (r + 1), ε r i = 0 :=
    Int.alternating_sum_range_choose_of_ne (by omega)
  have hQ : altProd r (fun i => lin w (i : A)) =
      Units.map (rescale a).toMonoidHom (altProd r fun i => lin 1 (i : A)) := by
    simp only [altProd, hlin, mul_zpow, prod_mul_distrib, prod_zpow_eq_zpow_sum, hsum, zpow_zero,
      one_mul, map_prod, map_zpow]
  set P : A⟦X⟧ := ↑(altProd r fun i => lin 1 (i : A))
  set c : A := (-1) ^ (r - 1) * ((r - 1).factorial : A)
  have hPc : ∀ n, n < r + 1 → coeff n P = coeff n (1 + C c * X ^ r) := fun n hn =>
    sub_eq_zero.1 (by rw [← map_sub]; exact X_pow_dvd_iff.1 (chernPoint hr) n hn)
  have hca : c * a ^ r = c := by
    have hg := geom_sum_mul (1 - y) r
    have hp : a ^ r * (1 - y) ^ r = 1 := by rw [← mul_pow, haw, one_pow]
    linear_combination (c * a ^ r) * hg + c * hp + ((-1) ^ (r - 1) * a ^ r *
      ∑ i ∈ range r, (1 - y) ^ i) * h
  have hPQ : X ^ (r + 1) ∣ P - (↑(altProd r fun i => lin w (i : A)) : A⟦X⟧) := by
    rw [hQ, Units.coe_map]
    change X ^ (r + 1) ∣ P - rescale a P
    refine X_pow_dvd_iff.2 fun n hn => ?_
    rw [map_sub, coeff_rescale, hPc n hn, map_add, coeff_C_mul_X_pow, coeff_one]
    rcases n with _ | n
    · simp
    · obtain rfl | hnr := eq_or_ne (n + 1) r
      · simp only [↓reduceIte, Nat.succ_ne_zero]
        linear_combination -hca
      · simp [hnr]
  have hprod : ∏ i ∈ range (r + 1), (lin 1 (i : A) * (lin w (i : A))⁻¹) ^ ε r i =
      altProd r (fun i => lin 1 (i : A)) * (altProd r fun i => lin w (i : A))⁻¹ := by
    simp only [altProd, mul_zpow, prod_mul_distrib, inv_zpow, prod_inv_distrib]
  rw [hprod, Units.val_mul]
  convert hPQ.mul_right (↑(altProd r fun i => lin w (i : A))⁻¹ : A⟦X⟧) using 1
  linear_combination Units.mul_inv (altProd r fun i => lin w (i : A))

/-- Page 13 with `y` nilpotent, as `x' ∈ Ã(X)` is. -/
theorem chernImmersion_of_isNilpotent {r : ℕ} (hr : 1 ≤ r) {y : A} (hy : IsNilpotent y)
    (h : ((r - 1).factorial : A) * y = 0) :
    X ^ (r + 1) ∣ (↑(∏ i ∈ range (r + 1),
      (lin 1 (i : A) * (lin hy.isUnit_one_sub.unit (i : A))⁻¹) ^ ε r i) : A⟦X⟧) - 1 :=
  chernImmersion hr hy.isUnit_one_sub h

end Folder2
