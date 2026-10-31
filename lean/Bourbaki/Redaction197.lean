import Mathlib

/-!
# Bourbaki rédaction n° 197: a plane curve `y² = P(x)` that is not normal in characteristic 2

Rédaction n° 197 (May 1954) of the Bourbaki archive is a report on algebraic geometry, chapter I,
elementary global theory (Archives Henri Poincaré, item
<https://archives-bourbaki.ahp-numerique.fr/items/show/612>, whose notice names P. Samuel as
author). On p. 39 it asserts that for an irreducible polynomial `P` the affine plane curve
`y² = P(x)` is always normal, that is, its coordinate ring `k[x, y]/(y² − P(x))` is integrally
closed. No hypothesis on the characteristic is made.

The assertion fails in characteristic 2. This file proves it with one explicit curve over `𝔽₂`.
Take `P = x³ + x + 1`, irreducible over `𝔽₂`, and `R = 𝔽₂[x][y]/(y² − P)`. In characteristic 2,
`(y + 1)² = y² + 1 = x³ + x = x (x + 1)²`, so `t = (y + 1)/(x + 1)` satisfies `t² = x`: it is
integral over `R`. It does not lie in `R`, since `x + 1` does not divide `y + 1` there (the map
`R → 𝔽₂[ε]`, `x ↦ 1`, `y ↦ 1 + ε`, kills `x + 1` and not `y + 1`).

* `P_irreducible`: `x³ + x + 1` is irreducible over `𝔽₂`;
* `key`: `(y + 1)² = x (x + 1)²` in `R`;
* `f_irreducible`, `isDomain`: `y² − P` is irreducible over `𝔽₂[x]`, so `R` is a domain
  (the curve is integral);
* `not_dvd`: `x + 1` does not divide `y + 1` in `R`;
* `isIntegral_t`, `t_not_mem`: `t = (y + 1)/(x + 1)` in the fraction field is integral over `R`
  and does not come from `R`;
* `not_isIntegrallyClosed`, `not_page39`: `R` is not integrally closed, although `P` is
  irreducible.

The assertion is true in characteristic different from 2 (Hartshorne, *Algebraic Geometry*,
II, Ex. 6.4, for `P` squarefree); that direction is not formalised here.
-/

open Polynomial

namespace Bourbaki.Redaction197

/-- The prime field `𝔽₂`. -/
abbrev F := ZMod 2

/-- The polynomial `P = x³ + x + 1` over `𝔽₂`. -/
noncomputable abbrev P : F[X] := X ^ 3 + X + 1

/-- The equation `y² − P(x)` of the curve, as a polynomial in `y` over `𝔽₂[x]`. -/
noncomputable abbrev f : F[X][X] := X ^ 2 - C P

/-- The coordinate ring `𝔽₂[x, y]/(y² − P(x))` of the curve. -/
abbrev R := AdjoinRoot f

/-- The coordinate `x` in `R`. -/
noncomputable abbrev x : R := AdjoinRoot.of f X

/-- The coordinate `y` in `R`. -/
noncomputable abbrev y : R := AdjoinRoot.root f

/-- `R` has characteristic 2. -/
theorem two_eq_zero : (2 : R) = 0 := by
  have h : algebraMap F R 2 = 0 := by rw [show (2 : F) = 0 from rfl, map_zero]
  rwa [map_ofNat] at h

/-- The equation of the curve holds in `R`. -/
theorem y_sq : y ^ 2 = x ^ 3 + x + 1 := by
  have h := AdjoinRoot.eval₂_root f
  simp [f, P, eval₂_sub, eval₂_pow, eval₂_C, sub_eq_zero] at h
  simpa [x, y] using h

/-- In characteristic 2, `(y + 1)² = x (x + 1)²`. -/
theorem key : (y + 1) ^ 2 = x * (x + 1) ^ 2 := by
  linear_combination (y_sq) + (y + 1 - x ^ 2) * two_eq_zero

/-- `P` has degree 3. -/
theorem P_natDegree : P.natDegree = 3 := by
  unfold P; compute_degree!

/-- `P = x³ + x + 1` is irreducible over `𝔽₂`: it has degree 3 and no root. -/
theorem P_irreducible : Irreducible P := by
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [P_natDegree]; decide) ?_
  intro a
  simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]
  revert a; decide

/-- `P` is not a square in `𝔽₂[x]`, its degree being odd. -/
theorem not_isSquare_P : ¬ IsSquare P := by
  rintro ⟨s, hs⟩
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact P_irreducible.ne_zero (by simpa using hs)
  have h := congrArg natDegree hs
  rw [P_natDegree, natDegree_mul hs0 hs0] at h
  omega

/-- The equation `y² − P` is monic in `y`. -/
theorem f_monic : f.Monic := by
  unfold f; monicity!

/-- `y² − P` is irreducible over `𝔽₂[x]`: a root in the fraction field would be integral over the
integrally closed ring `𝔽₂[x]`, hence a polynomial whose square is `P`. -/
theorem f_irreducible : Irreducible f := by
  let K := FractionRing F[X]
  rw [f_monic.irreducible_iff_irreducible_map_fraction_map (K := K)]
  have hdeg : (map (algebraMap F[X] K) f).natDegree = 2 := by
    rw [f_monic.natDegree_map]; unfold f; compute_degree!
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) ?_
  intro r hr
  have hr' : r ^ 2 = algebraMap F[X] K P := by
    simpa [f, IsRoot, sub_eq_zero] using hr
  have hint : IsIntegral F[X] r := ⟨f, f_monic, by
    simpa [f, eval₂_sub, sub_eq_zero, ← Polynomial.algebraMap_eq] using hr'⟩
  obtain ⟨s, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← map_pow] at hr'
  exact not_isSquare_P ⟨s, by rw [← IsFractionRing.injective F[X] K hr', sq]⟩

/-- `y² − P` is prime in the factorial ring `𝔽₂[x][y]`. -/
theorem f_prime : Prime f := f_irreducible.prime

/-- The coordinate ring `R` is a domain: the curve is integral. -/
instance isDomain : IsDomain R := AdjoinRoot.isDomain_of_prime f_prime

/-- The dual numbers over `𝔽₂` have characteristic 2. -/
theorem dual_two : (2 : DualNumber F) = 0 := by
  have h : algebraMap F (DualNumber F) 2 = 0 := by rw [show (2 : F) = 0 from rfl, map_zero]
  rwa [map_ofNat] at h

/-- The map `R → 𝔽₂[ε]` sending `x` to `1` and `y` to `1 + ε`: the point `(1, 1)` of the curve,
with a tangent vector along `y` (`(1 + ε)² = 1 = P(1)` in characteristic 2). -/
noncomputable def ψ : R →+* DualNumber F :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap F (DualNumber F)) 1) (1 + DualNumber.eps) (by
    simp [f, P, eval₂_sub, eval₂_pow, eval₂_C]
    linear_combination (DualNumber.eps_mul_eps (R := F)) + (DualNumber.eps - 1) * dual_two)

/-- `ψ x = 1`. -/
theorem ψ_x : ψ x = 1 := by simp [ψ, x]

/-- `ψ y = 1 + ε`. -/
theorem ψ_y : ψ y = 1 + DualNumber.eps := by simp [ψ, y]

/-- `x + 1` does not divide `y + 1` in `R`: `ψ` sends `x + 1` to `0` and `y + 1` to `ε ≠ 0`. -/
theorem not_dvd : ¬ (x + 1 ∣ y + 1) := by
  intro h
  have h' := map_dvd ψ h
  rw [map_add, map_add, ψ_x, ψ_y, map_one, one_add_one_eq_two, dual_two, zero_dvd_iff] at h'
  have := congrArg TrivSqZeroExt.snd h'
  simp at this

/-- `x + 1 ≠ 0` in `R`: at the point `(0, 1)` of the curve it takes the value `1`. -/
theorem x_add_one_ne_zero : x + 1 ≠ 0 := by
  intro h
  have := congrArg (AdjoinRoot.lift (evalRingHom (0 : F)) (1 : F) (by
    simp [f, P, eval₂_sub, eval₂_pow, eval₂_C])) h
  simp [x] at this

/-- The element `t = (y + 1)/(x + 1)` of the fraction field of `R`. -/
noncomputable abbrev t : FractionRing R :=
  algebraMap R (FractionRing R) (y + 1) / algebraMap R (FractionRing R) (x + 1)

/-- `x + 1` stays nonzero in the fraction field. -/
theorem algebraMap_x_add_one_ne_zero : algebraMap R (FractionRing R) (x + 1) ≠ 0 :=
  (IsFractionRing.injective R (FractionRing R)).ne_iff' (map_zero _) |>.2 x_add_one_ne_zero

/-- `t² = x`. -/
theorem t_sq : t ^ 2 = algebraMap R (FractionRing R) x := by
  rw [t, div_pow, ← map_pow, key, map_mul, map_pow, mul_div_assoc,
    div_self (pow_ne_zero _ algebraMap_x_add_one_ne_zero), mul_one]

/-- `t` is integral over `R`, a root of the monic polynomial `T² − x`. -/
theorem isIntegral_t : IsIntegral R t :=
  ⟨X ^ 2 - C x, by monicity!, by simp [eval₂_sub, t_sq]⟩

/-- `t` does not come from `R`. -/
theorem t_not_mem : ¬ ∃ s : R, algebraMap R (FractionRing R) s = t := by
  rintro ⟨s, hs⟩
  rw [t, eq_div_iff algebraMap_x_add_one_ne_zero, ← map_mul] at hs
  exact not_dvd ⟨s, by rw [← IsFractionRing.injective R (FractionRing R) hs, mul_comm]⟩

/-- The coordinate ring of the curve `y² = x³ + x + 1` over `𝔽₂` is not integrally closed. -/
theorem not_isIntegrallyClosed : ¬ IsIntegrallyClosed R := fun _ ↦
  t_not_mem (IsIntegrallyClosed.isIntegral_iff.1 isIntegral_t)

/-- The assertion of rédaction n° 197, p. 39, fails: over `𝔽₂`, `P = x³ + x + 1` is irreducible,
the curve `y² = P(x)` is integral, and its coordinate ring is not integrally closed. -/
theorem not_page39 : Irreducible P ∧ IsDomain R ∧ ¬ IsIntegrallyClosed R :=
  ⟨P_irreducible, inferInstance, not_isIntegrallyClosed⟩

end Bourbaki.Redaction197
