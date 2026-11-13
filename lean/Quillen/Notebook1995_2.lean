import Mathlib

/-!
# Quillen, notebook 1995-2, p. 65: when is `a z + (1 - a)` a unit of `R[z, z⁻¹]`?

Daniel Quillen's research notebook 1995-2 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201995/1995-2.pdf>) studies,
in its entry of July 1, 1995, the maps `K₀ R → K₁ (R[z, z⁻¹]) → K₀ R` of the Atiyah–Bott proof
of periodicity and of Bass's fundamental theorem: the first sends an idempotent `p` to the unit
`z p + 1 - p`. After a change of coordinates on `ℙ¹` he reduces a linear family `a z + b` to
the form `z a + (1 - a)`, and notes (p. 65) that `z a + (1 - a)` is invertible over
`R[z, z⁻¹]` if and only if `a (1 - a)` is nilpotent; so the elements `a` that give units in
this way are exactly those which are idempotent modulo nilpotents.

We prove this for a commutative ring `R` (the page argues for a matrix `a`, in a general ring).

* `bott a`: the Laurent polynomial `C a * T 1 + C (1 - a)`;
* `bott_mul_invert`: `bott a * bott a (z ↦ z⁻¹) = 1 + (z - 2 + z⁻¹) a (1 - a)`, the identity of
  the page;
* `eq_zero_or_eq_zero_of_mul_eq_X_pow`: over a domain, if `a X + b` divides `X ^ N` then
  `a = 0` or `b = 0`;
* `isUnit_bott_iff`: **the statement of the page**: `bott a` is a unit iff `a (1 - a)` is
  nilpotent.

The direction `⇐` follows the page. For `⇒` the page passes to the subring of Laurent
polynomials invariant under `z ↦ z⁻¹`, a polynomial ring in `z - 2 + z⁻¹`; we argue instead
modulo each prime ideal, where a unit `a z + b` must be a monomial.
-/

namespace Quillen.Notebook1995_2

open LaurentPolynomial Polynomial

variable {R : Type*} [CommRing R]

/-- The Laurent polynomial `a z + (1 - a)` of the Atiyah–Bott and Bass constructions; for `a`
idempotent it is the unit `z a + 1 - a` attached to `a`. -/
noncomputable def bott (a : R) : R[T;T⁻¹] :=
  LaurentPolynomial.C a * T 1 + LaurentPolynomial.C (1 - a)

/-- The identity of p. 65: `(a z + 1 - a)(a z⁻¹ + 1 - a) = 1 + (z - 2 + z⁻¹) a (1 - a)`. -/
theorem bott_mul_invert (a : R) :
    bott a * invert (bott a) =
      1 + (T 1 - 2 + T (-1)) * LaurentPolynomial.C (a * (1 - a)) := by
  have h1 : (T 1 : R[T;T⁻¹]) * T (-1) = 1 := by rw [← T_add]; simp
  simp only [bott, map_add, map_mul, invert_C, invert_T, map_sub, map_one]
  linear_combination (LaurentPolynomial.C a) ^ 2 * h1

/-- The direction `⇐`: if `a (1 - a)` is nilpotent, then `a z + (1 - a)` is a unit. -/
theorem isUnit_bott_of_isNilpotent {a : R} (h : IsNilpotent (a * (1 - a))) :
    IsUnit (bott a) :=
  isUnit_of_mul_isUnit_left (by
    rw [bott_mul_invert]
    exact ((Commute.all _ _).isNilpotent_mul_left (h.map LaurentPolynomial.C)).isUnit_one_add)

/-- Over a domain, if `a X + b` divides a power of `X`, then `a = 0` or `b = 0`: a unit
`a z + b` of the Laurent polynomial ring is a monomial. -/
theorem eq_zero_or_eq_zero_of_mul_eq_X_pow {D : Type*} [CommRing D] [IsDomain D] {a b : D} :
    ∀ (N : ℕ) (G : D[X]), (Polynomial.C a * X + Polynomial.C b) * G = X ^ N →
      a = 0 ∨ b = 0 := by
  intro N
  induction N with
  | zero =>
    intro G hG
    have hdeg := Polynomial.natDegree_eq_zero_of_isUnit (IsUnit.of_mul_eq_one _ (by simpa using hG))
    have hc := Polynomial.coeff_eq_zero_of_natDegree_lt
      (p := Polynomial.C a * X + Polynomial.C b) (n := 1) (by omega)
    exact .inl (by simpa using hc)
  | succ n ih =>
    intro G hG
    by_cases hb : b = 0
    · exact Or.inr hb
    obtain ⟨G1, rfl⟩ := Polynomial.X_dvd_iff.mpr
      (by simpa [hb] using congrArg (fun p : D[X] => p.coeff 0) hG)
    exact ih G1 (mul_left_cancel₀ (Polynomial.X_ne_zero (R := D)) (by linear_combination hG))

/-- The direction `⇒`: if `a z + (1 - a)` is a unit, then `a (1 - a)` is nilpotent. -/
theorem isNilpotent_of_isUnit_bott {a : R} (h : IsUnit (bott a)) :
    IsNilpotent (a * (1 - a)) := by
  obtain ⟨g, hg⟩ := h.exists_right_inv
  obtain ⟨N, G, hG⟩ := LaurentPolynomial.exists_T_pow g
  have key : (Polynomial.C a * X + Polynomial.C (1 - a)) * G = X ^ N := by
    apply Polynomial.toLaurent_injective
    have hb : toLaurent (Polynomial.C a * X + Polynomial.C (1 - a)) = bott a := by
      simp [bott]
    rw [map_mul, hb, hG, ← mul_assoc, hg, one_mul, Polynomial.toLaurent_X_pow]
  rw [nilpotent_iff_mem_prime]
  intro p hp
  have := hp
  have hmap := congrArg (Polynomial.map (Ideal.Quotient.mk p)) key
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_pow] at hmap
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
  rcases eq_zero_or_eq_zero_of_mul_eq_X_pow N _ hmap with h0 | h0
  · rw [h0, zero_mul]
  · rw [h0, mul_zero]

/-- **Quillen, notebook 1995-2, p. 65.** For `a` in a commutative ring `R`, the Laurent
polynomial `a z + (1 - a)` is a unit of `R[z, z⁻¹]` if and only if `a (1 - a)` is nilpotent. -/
theorem isUnit_bott_iff (a : R) : IsUnit (bott a) ↔ IsNilpotent (a * (1 - a)) :=
  ⟨isNilpotent_of_isUnit_bott, isUnit_bott_of_isNilpotent⟩

end Quillen.Notebook1995_2
