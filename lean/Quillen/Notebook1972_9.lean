import Mathlib

/-!
# Quillen, notebook 1972-9, p. 66: an additive polynomial in characteristic `p` has only monomials `X^{p^i}`

Daniel Quillen's research notebook 1972-9 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201972/1972-9.pdf>) considers,
on pp. 66–67, additive polynomial maps between vector spaces in characteristic `p` and their
decomposition into `p^i`-homogeneous pieces; the one-variable statement behind it is that a
polynomial `f` with `f(X + Y) = f(X) + f(Y)` is a combination of the monomials `X^{p^i}`.

This file proves the one-variable statement over a field of prime characteristic `p`. The
identity `f(X + Y) = f(X) + f(Y)` is written in `K[X][Y]`, with `X` the inner variable, as
`(f.map C).comp (Y + C X) = f.map C + C f`.

* `hasseDeriv_eq_C`: the identity gives `D^{(a)} f = f_a` (a constant) for every `a ≥ 1`, where
  `D^{(a)}` is the Hasse derivative (the coefficient of `Y^a` in `f(X + Y)`);
* `coeff_zero_eq_zero`: the constant term vanishes;
* `eq_pow_of_coeff_ne_zero`: **the statement**: if `f_n ≠ 0` then `n` is a power of `p`, since
  `C(n, a) f_n = 0` for `0 < a < n` and, by Lucas's theorem (mathlib's
  `Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat`), some `C(n, a)` is prime to `p`
  unless `n` is a power of `p`.

The several-variable form of the page and the « inverse up to Frobenius » are not formalised.
-/

namespace Quillen.Notebook1972_9

open Polynomial

variable {K : Type*} [Field K] {f : K[X]}

/-- The additivity identity `f(X + Y) = f(X) + f(Y)` in `K[X][Y]`. -/
def IsAdditivePoly (f : K[X]) : Prop :=
  (f.map C).comp (X + C X) = f.map C + C f

theorem coeff_taylor (hf : IsAdditivePoly f) (a : ℕ) :
    (hasseDeriv a f) = (f.map C + C f).coeff a := by
  have := congrArg (fun q => q.coeff a) hf
  rw [← this, ← taylor_apply, taylor_coeff, hasseDeriv_map, eval_map, eval₂_C_X]

/-- The Hasse derivatives of an additive polynomial are constants: `D^{(a)} f = f_a`, `a ≥ 1`. -/
theorem hasseDeriv_eq_C (hf : IsAdditivePoly f) {a : ℕ} (ha : a ≠ 0) :
    hasseDeriv a f = C (f.coeff a) := by
  rw [coeff_taylor hf, coeff_add, coeff_map, coeff_C]
  simp [ha]

/-- The constant term of an additive polynomial is zero. -/
theorem coeff_zero_eq_zero (hf : IsAdditivePoly f) : f.coeff 0 = 0 := by
  have h := coeff_taylor hf 0
  rw [hasseDeriv_zero, LinearMap.id_apply, coeff_add, coeff_map, coeff_C] at h
  simp only [ite_true] at h
  have : C (f.coeff 0) = 0 := by linear_combination -h
  exact C_eq_zero.mp this

/-- `C(n, a) f_n = 0` for `0 < a < n`. -/
theorem choose_mul_coeff (hf : IsAdditivePoly f) {n a : ℕ} (ha : a ≠ 0) (han : a < n) :
    (n.choose a : K) * f.coeff n = 0 := by
  have h := congrArg (fun q => q.coeff (n - a)) (hasseDeriv_eq_C hf ha)
  have hna : n - a ≠ 0 := by omega
  simp only [hasseDeriv_coeff, coeff_C, hna, ite_false, Nat.sub_add_cancel han.le] at h
  exact h

/-- **Quillen, notebook 1972-9, p. 66.** Over a field of prime characteristic `p`, if
`f(X + Y) = f(X) + f(Y)` and the coefficient `f_n` is not zero, then `n` is a power of `p`. -/
theorem eq_pow_of_coeff_ne_zero (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (hf : IsAdditivePoly f) {n : ℕ} (hn : f.coeff n ≠ 0) : ∃ i, n = p ^ i := by
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (coeff_zero_eq_zero hf) hn
    · exact h
  refine ⟨multiplicity p n, Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat hn0 ?_⟩
  intro i hi
  rw [Finset.mem_Icc] at hi
  have h := choose_mul_coeff hf (n := n) (a := i) (by omega) (by omega)
  have hc : (n.choose i : K) = 0 := (mul_eq_zero.mp h).resolve_right hn
  rw [CharP.cast_eq_zero_iff K p] at hc
  exact Nat.modEq_zero_iff_dvd.mpr hc

end Quillen.Notebook1972_9
