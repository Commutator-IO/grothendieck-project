import Mathlib

/-!
# Quillen, notebook 1988-3: the operator `(x² − 1)∂ + 4x` on polynomials

Daniel Quillen's research notebook 1988-3 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201988/1988-3.pdf>),
pp. 46-47. On `ℝ[x]` the operator `L = (x² − 1) ∂ₓ + 4x`

* sends `xⁿ` to `(n + 4) x^{n+1} − n x^{n−1}` (`L_X_pow`);
* is injective (`L_injective`): the coefficient of `x^{d+1}` in `L p` is `(d + 4)` times the
  leading coefficient of `p`;
* has for image exactly the kernel of the linear form `phi(q) = ∫₋₁¹ q(x)(x² − 1) dx`
  (`mem_range_iff`), a hyperplane since `phi(1) = −4/3` (`phi_one`). The inclusion holds because
  `(x² − 1) L p = ((x² − 1)² p)'` and `(x² − 1)²` vanishes at `±1`; the converse, by induction
  on the degree, subtracting multiples of `L(x^d)`, down to a constant `c` with `phi(c) = 0`.

The coefficient formula behind both, `[x^{N+1}] L p = (N + 4) p_N − (N + 2) p_{N+2}`, is
`coeff_L_succ`.
-/

namespace Quillen.Notebook1988_3

open Polynomial intervalIntegral

/-- `L p = (X² − 1) p' + 4 X p`. -/
noncomputable def L : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun p := (X ^ 2 - 1) * derivative p + 4 * X * p
  map_add' p q := by simp only [map_add]; ring
  map_smul' c p := by
    simp only [smul_eq_C_mul, RingHom.id_apply, derivative_C_mul]
    ring

lemma L_apply (p : ℝ[X]) : L p = (X ^ 2 - 1) * derivative p + 4 * X * p := rfl

lemma coeff_L_zero (p : ℝ[X]) : (L p).coeff 0 = -p.coeff 1 := by
  rw [L_apply]
  simp [coeff_derivative, sub_mul, mul_assoc]

/-- `[x^{N+1}] L p = (N + 4) p_N − (N + 2) p_{N+2}`. -/
lemma coeff_L_succ (p : ℝ[X]) (N : ℕ) :
    (L p).coeff (N + 1) = (N + 4) * p.coeff N - (N + 2) * p.coeff (N + 2) := by
  rw [L_apply, coeff_add, sub_mul, one_mul, coeff_sub, coeff_X_pow_mul', coeff_derivative,
    mul_assoc, coeff_ofNat_mul, coeff_X_mul]
  rcases N with _ | N
  · simp [coeff_derivative]
    ring
  · rw [ite_eq_left (by omega), coeff_derivative, show N + 1 + 1 - 2 + 1 = N + 1 by omega]
    push_cast
    ring

/-- `L(xⁿ) = (n + 4) x^{n+1} − n x^{n−1}`. -/
theorem L_X_pow (n : ℕ) :
    L (X ^ n) = ((n : ℝ[X]) + 4) * X ^ (n + 1) - (n : ℝ[X]) * X ^ (n - 1) := by
  rw [L_apply, derivative_X_pow, ← C_eq_natCast]
  rcases n with _ | n
  · simp
  · simp only [Nat.cast_succ, map_add, map_one, C_eq_natCast, add_tsub_cancel_right]
    ring

/-- `L` is injective. -/
theorem L_injective : Function.Injective L := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  by_contra hp0
  have h := coeff_L_succ p p.natDegree
  rw [hp, coeff_zero, coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < p.natDegree + 2),
    mul_zero, sub_zero] at h
  have hlc : p.coeff p.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have : ((p.natDegree : ℝ) + 4) ≠ 0 := by positivity
  exact mul_ne_zero this hlc h.symm

/-- The linear form `phi(q) = ∫₋₁¹ q(x)(x² − 1) dx`. -/
noncomputable def phi (q : ℝ[X]) : ℝ := ∫ x in (-1 : ℝ)..1, q.eval x * (x ^ 2 - 1)

lemma phi_sub_C_mul (q r : ℝ[X]) (c : ℝ) : phi (q - C c * r) = phi q - c * phi r := by
  simp only [phi, eval_sub, eval_mul, eval_C, sub_mul, mul_assoc]
  rw [integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), integral_const_mul]

theorem phi_one : phi 1 = -4 / 3 := by
  simp only [phi, eval_one, one_mul]
  rw [integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), integral_pow]
  norm_num

/-- `(x² − 1) L p = ((x² − 1)² p)'`, so `phi (L p) = 0`. -/
theorem phi_L (p : ℝ[X]) : phi (L p) = 0 := by
  set G : ℝ[X] := (X ^ 2 - 1) ^ 2 * p
  have hG : derivative G = (X ^ 2 - 1) * L p := by
    simp only [G, L_apply, derivative_mul, derivative_pow, derivative_sub, derivative_X,
      derivative_one, sub_zero, mul_one]
    simp only [Nat.cast_ofNat, map_ofNat]
    ring
  have h := integral_eq_sub_of_hasDerivAt (a := -1) (b := 1) (f := fun x => G.eval x)
    (f' := fun x => (derivative G).eval x) (fun x _ => G.hasDerivAt x)
    (by apply Continuous.intervalIntegrable; fun_prop)
  simp only [hG, eval_mul, eval_sub, eval_pow, eval_X, eval_one, G] at h
  rw [phi]
  simp_rw [mul_comm _ (_ - 1 : ℝ)]
  rw [h]
  norm_num

/-- **Notebook 1988-3, pp. 46-47**: the image of `L` is the kernel of `phi`. -/
theorem mem_range_iff (q : ℝ[X]) : (∃ p, L p = q) ↔ phi q = 0 := by
  constructor
  · rintro ⟨p, rfl⟩; exact phi_L p
  intro hq
  induction h : q.natDegree using Nat.strong_induction_on generalizing q with
  | _ d ih =>
  rcases d with _ | e
  · -- a constant in the kernel is zero
    have hC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero h
    have hphiC : phi q = q.coeff 0 * phi 1 := by
      rw [hC, phi, phi]
      simp only [eval_C, eval_one, one_mul, coeff_C_zero]
      exact integral_const_mul _ _
    rw [hq, phi_one] at hphiC
    have h0 : q.coeff 0 = 0 := by linarith
    exact ⟨0, by rw [map_zero, hC, h0, map_zero]⟩
  · -- lower the degree with a multiple of `L(x^e)`
    set c := q.coeff (e + 1) / ((e : ℝ) + 4)
    set q' := q - C c * L (X ^ e)
    have hLe : ∀ M : ℕ, e + 1 < M + 1 → (L (X ^ e)).coeff (M + 1) = 0 := by
      intro M hM
      rw [coeff_L_succ, coeff_X_pow, coeff_X_pow, ite_eq_right (by omega), ite_eq_right (by omega)]
      ring
    have hdeg : q'.natDegree < e + 1 := by
      rw [Nat.lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
      intro N hN
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      simp only [q', coeff_sub, coeff_C_mul]
      rcases Nat.lt_or_ge e M with hM | hM
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), hLe M (by omega), mul_zero, sub_zero]
      · have hMe : M = e := by omega
        subst hMe
        rw [coeff_L_succ, coeff_X_pow, coeff_X_pow, ite_eq_left rfl, ite_eq_right (by omega)]
        have : ((M : ℝ) + 4) ≠ 0 := by positivity
        simp only [c]
        field_simp
        ring
    obtain ⟨p', hp'⟩ := ih _ hdeg q' (by rw [phi_sub_C_mul, hq, phi_L, mul_zero, sub_zero]) rfl
    refine ⟨p' + C c * X ^ e, ?_⟩
    rw [map_add, ← smul_eq_C_mul, map_smul, smul_eq_C_mul, hp']
    simp [q']

end Quillen.Notebook1988_3
