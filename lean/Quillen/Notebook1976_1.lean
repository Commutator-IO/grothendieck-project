import Mathlib

/-!
# Quillen, notebook 1976-1: `det(1 + tν)` a unit iff `ν² = 0`

Daniel Quillen's research notebook 1976-1 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201976/1976-1.pdf>).

* p. 49: for a `2 × 2` matrix `ν` over a field, `det(1 + tν) = 1 + t tr ν + t² det ν`
  (`det_one_add`), a unit of `K[t]` iff `ν² = 0` (`isUnit_det_iff`), iff `tr ν = det ν = 0`
  (`sq_eq_zero_iff`, through Cayley–Hamilton `sq_eq`), iff `ν` is nilpotent
  (`isNilpotent_iff`); in every characteristic.
-/

namespace Quillen.Notebook1976_1

open Matrix Polynomial

variable {K : Type*} [Field K]

theorem det_one_add (ν : Matrix (Fin 2) (Fin 2) K) :
    (1 + (X : K[X]) • ν.map C).det = 1 + C ν.trace * X + C ν.det * X ^ 2 := by
  simp [det_fin_two, trace_fin_two, map_sub, map_mul, map_add]; ring

/-- For `2 × 2` matrices over a field (char-free): `ν² = 0` iff `tr ν = det ν = 0`. -/
theorem sq_eq (ν : Matrix (Fin 2) (Fin 2) K) :
    ν ^ 2 = ν.trace • ν - ν.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sq, mul_apply, trace_fin_two, det_fin_two, Fin.sum_univ_two] <;> ring

theorem det_eq_zero_of_pow_eq_zero {ν : Matrix (Fin 2) (Fin 2) K} {k : ℕ} (h : ν ^ k = 0) :
    ν.det = 0 := by
  have := congrArg det h
  rw [det_pow] at this
  rcases k with _ | k
  · simp at h
  · exact pow_eq_zero_iff (Nat.succ_ne_zero k) |>.1 (this.trans det_zero)

theorem sq_eq_zero_iff (ν : Matrix (Fin 2) (Fin 2) K) :
    ν ^ 2 = 0 ↔ ν.trace = 0 ∧ ν.det = 0 := by
  have ch := sq_eq ν
  constructor
  · intro h
    have hd := det_eq_zero_of_pow_eq_zero h
    refine ⟨?_, hd⟩
    rw [h, hd, zero_smul, sub_zero] at ch
    by_contra ht
    have hν : ν = 0 := by simpa [ht] using ch.symm
    exact ht (by simp [hν])
  · rintro ⟨ht, hd⟩; rw [ch, ht, hd]; simp

/-- **p. 49.** `det(1 + tν)` is a unit of `K[t]` iff `ν² = 0`. -/
theorem isUnit_det_iff (ν : Matrix (Fin 2) (Fin 2) K) :
    IsUnit (1 + (X : K[X]) • ν.map C).det ↔ ν ^ 2 = 0 := by
  rw [sq_eq_zero_iff, det_one_add]
  constructor
  · intro h
    obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.1 h
    have h1 := congrArg (coeff · 1) hr
    have h2 := congrArg (coeff · 2) hr
    simp [coeff_C, coeff_one] at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨ht, hd⟩; simp [ht, hd]

/-- For `2 × 2` matrices over a field, nilpotent iff `ν² = 0`. -/
theorem isNilpotent_iff (ν : Matrix (Fin 2) (Fin 2) K) : IsNilpotent ν ↔ ν ^ 2 = 0 := by
  refine ⟨fun ⟨k, hk⟩ => ?_, fun h => ⟨2, h⟩⟩
  have ch := sq_eq ν
  rw [det_eq_zero_of_pow_eq_zero hk, zero_smul, sub_zero] at ch
  have hp : ∀ n, ν ^ (n + 1) = ν.trace ^ n • ν := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, smul_mul_assoc, ← sq, ch, smul_smul, pow_succ]
  rcases k with _ | k
  · exact absurd (congrFun (congrFun hk 0) 0) (by simp)
  rw [hp, smul_eq_zero] at hk
  rcases hk with ht | hν
  · rw [ch, pow_eq_zero_iff'.1 ht |>.1, zero_smul]
  · rw [hν]; simp

end Quillen.Notebook1976_1
