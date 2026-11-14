import Mathlib

/-!
# Quillen, notebook 1972-mixed: square-zero symmetric functions, the cone product, the sum map

Daniel Quillen's research notebook 1972-mixed (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201972/1972-mixed%20papers.pdf>).

(file « 1972-mixed papers ».)

* p. 40: in a commutative ring, if `ε_i² = 0` then `(Σ_{i∈s} ε_i)^k = k! e_k(ε)`
  (`sum_pow_of_sq_eq_zero`), so `(Σ_{i<n} ε_i)^n = n! ∏ ε_i` (`sum_pow_card`).
* p. 17 (and 1971-14, pp. 10-11): if `[d, h] = u − v`, `[d, h'] = u' − v'` and `d` commutes with
  `v` and `u'`, then `[d, hu' + vh'] = uu' − vv'` (`cone_product`), graded commutators with `h`,
  `h'` odd, in any ring.
* p. 33: the kernel of the sum map `K^s → K` has dimension `s − 1` (`finrank_ker_sum`).
-/

namespace Quillen.Notebook1972_Mixed

open Finset

variable {R : Type*} [CommRing R]

theorem add_pow_of_sq_eq_zero {e S : R} (he : e ^ 2 = 0) (k : ℕ) :
    (e + S) ^ (k + 1) = S ^ (k + 1) + (k + 1) * e * S ^ k := by
  induction k with
  | zero => simp [add_comm]
  | succ k ih => rw [pow_succ, ih]; push_cast; linear_combination ((k + 1) * S ^ k) * he

/-- **p. 40.** If `ε_i² = 0`, then `(Σ_{i∈s} ε_i)^k = k! · e_k(ε)`, the `k`-th elementary symmetric
function of the `ε_i`. -/
theorem sum_pow_of_sq_eq_zero {ι : Type*} [DecidableEq ι] (ε : ι → R) (hε : ∀ i, ε i ^ 2 = 0)
    (s : Finset ι) (k : ℕ) :
    (∑ i ∈ s, ε i) ^ k = k.factorial * ∑ t ∈ s.powersetCard k, ∏ i ∈ t, ε i := by
  induction s using Finset.induction_on generalizing k with
  | empty => cases k <;> simp [powersetCard_eq_empty.2 (by simp : (∅ : Finset ι).card < _ + 1)]
  | insert a s ha ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hd : Disjoint (s.powersetCard (k + 1)) ((s.powersetCard k).image (insert a)) :=
        disjoint_left.2 fun t h1 h2 => by
          obtain ⟨u, -, rfl⟩ := mem_image.1 h2
          exact ha (mem_powersetCard.1 h1 |>.1 (mem_insert_self a u))
      have hi : ∀ x ∈ s.powersetCard k, ∀ y ∈ s.powersetCard k, insert a x = insert a y → x = y :=
        fun x hx y hy h => by
          simpa [erase_insert (fun h => ha (mem_powersetCard.1 hx |>.1 h)),
            erase_insert (fun h => ha (mem_powersetCard.1 hy |>.1 h))] using congrArg (·.erase a) h
      rw [sum_insert ha, add_pow_of_sq_eq_zero (hε a), powersetCard_succ_insert ha,
        sum_union hd, sum_image hi, ih, ih, mul_add, Nat.factorial_succ, Nat.cast_mul,
        sum_congr rfl fun t ht => prod_insert fun h => ha (mem_powersetCard.1 ht |>.1 h),
        ← mul_sum]
      push_cast; ring

/-- The top case: `(Σ_{i<n} ε_i)^n = n! ∏ ε_i`. -/
theorem sum_pow_card {n : ℕ} (ε : Fin n → R) (hε : ∀ i, ε i ^ 2 = 0) :
    (∑ i, ε i) ^ n = n.factorial * ∏ i, ε i := by
  have : powersetCard n univ = {(univ : Finset (Fin n))} := by
    simpa using powersetCard_self (univ : Finset (Fin n))
  simpa [this] using sum_pow_of_sq_eq_zero ε hε univ n

/-- **p. 17 (and 1971-14, pp. 10-11).** The cone product: if `[d, h] = u − v`, `[d, h'] = u' − v'`
(graded commutators, `h, h'` odd) and `d` commutes with `v` and `u'`, then
`[d, hu' + vh'] = uu' − vv'`. -/
theorem cone_product {A : Type*} [Ring A] {d h h' u v u' v' : A} (hh : d * h + h * d = u - v)
    (hh' : d * h' + h' * d = u' - v') (hv : d * v = v * d) (hu' : d * u' = u' * d) :
    d * (h * u' + v * h') + (h * u' + v * h') * d = u * u' - v * v' := by
  have e1 : d * h * u' + h * u' * d = (u - v) * u' := by
    rw [← hh, add_mul, mul_assoc h, ← hu', ← mul_assoc]
  have e2 : d * v * h' + v * h' * d = v * (u' - v') := by
    rw [← hh', mul_add, hv, mul_assoc, mul_assoc]
  simp only [mul_add, add_mul, ← mul_assoc] at *
  rw [sub_mul, mul_sub] at *
  calc _ = (d * h * u' + h * u' * d) + (d * v * h' + v * h' * d) := by abel
    _ = _ := by rw [e1, e2]; abel

/-- **p. 33.** The kernel of the sum map `K^s → K` has dimension `s − 1`. -/
theorem finrank_ker_sum {K : Type*} [Field K] {s : ℕ} (hs : 1 ≤ s) :
    Module.finrank K (LinearMap.ker (∑ i : Fin s, LinearMap.proj i : (Fin s → K) →ₗ[K] K)) =
      s - 1 := by
  set f : (Fin s → K) →ₗ[K] K := ∑ i : Fin s, LinearMap.proj i
  have hf : LinearMap.range f = ⊤ := LinearMap.range_eq_top.2 fun c =>
    ⟨Pi.single ⟨0, hs⟩ c, by simp [f, Finset.sum_apply, Pi.single_apply]⟩
  have := f.finrank_range_add_finrank_ker
  rw [hf, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
  omega

end Quillen.Notebook1972_Mixed
