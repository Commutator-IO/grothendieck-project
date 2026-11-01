import Mathlib

/-!
# Bourbaki, rédaction n° 387 (September 1962): the typed formula for `Card(U/Uⁿ)` fails for `ℚ₂`

Rédaction 387 of the Bourbaki archive (Archives Henri Poincaré, item 942) is Dieudonné's redraft of
*Algèbre commutative*, ch. VI « Valuations ». Its § 9, exercise 3 (p. 67 of the facsimile) gives,
for a locally compact field `K` with group of units `U` of its ring of integers, a formula for the
index of the `n`-th powers, typed as the product `mod_K(n) · Card(ₙU)` of the module of `n` and the
number of `n`-th roots of unity. The standard formula is the quotient,
`[U : Uⁿ] = Card(ₙU) / mod_K(n)` (for `ℚ_p`: Serre, *Cours d'arithmétique*, ch. II; in general:
Neukirch, *Algebraic Number Theory*, ch. II, § 5).

For `K = ℚ₂` and `n = 2` the product is `(1/2) · 2 = 1`, so the typed formula would make every
unit of `ℤ₂` a square; but `-1` is not a square in `ℤ₂`, not even modulo `4`. (The quotient gives
`4`, the true index.)

* `norm_two`: `mod(2) = ‖2‖ = 1/2` in `ℚ₂` (the module of `ℚ₂` is the `2`-adic absolute value);
* `sq_eq_one_iff`: the square roots of `1` in `ℤ₂ˣ` are `±1`, and `1 ≠ -1`, so `Card(₂U) = 2`;
* `not_isSquare_neg_one`: `-1` is not a square in `ℤ₂`, by reduction modulo `4`;
* `typed_formula_fails`: the typed value `mod(2) · Card(₂U)` is `1`, yet `U ≠ U²`.

Whether the printed exercise (Bourbaki, *Algèbre commutative*, ch. VI, 1964) keeps the product has
not been checked.
-/

namespace Bourbaki.Redaction387

/-- The module of `2` in `ℚ₂` is `1/2`. -/
theorem norm_two : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
  have := Padic.norm_p (p := 2)
  simpa [one_div] using this

/-- The square roots of `1` among the units of `ℤ₂` are `1` and `-1`. -/
theorem sq_eq_one_iff (u : ℤ_[2]ˣ) : u ^ 2 = 1 ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro h
    have h' : (u : ℤ_[2]) * u = 1 := by
      simpa [sq] using congrArg (fun v : ℤ_[2]ˣ => (v : ℤ_[2])) h
    rcases mul_self_eq_one_iff.mp h' with h1 | h1
    · exact Or.inl (Units.ext h1)
    · exact Or.inr (Units.ext (by simpa using h1))
  · rintro (rfl | rfl) <;> simp

/-- `1 ≠ -1` in `ℤ₂`, so `ₙU` has exactly two elements for `n = 2`. -/
theorem one_ne_neg_one : (1 : ℤ_[2]ˣ) ≠ -1 := by
  intro h
  have h2 : ((1 : ℤ_[2]ˣ) : ℤ_[2]) = ((-1 : ℤ_[2]ˣ) : ℤ_[2]) := congrArg _ h
  have h3 := congrArg (PadicInt.toZModPow (p := 2) 2) h2
  simp at h3
  revert h3
  decide

/-- `-1` is not a square in `ℤ₂`: modulo `4`, the squares are `0` and `1`, and `-1 = 3`. -/
theorem not_isSquare_neg_one : ¬ IsSquare (-1 : ℤ_[2]) := by
  rintro ⟨x, hx⟩
  have h := congrArg (PadicInt.toZModPow (p := 2) 2) hx
  rw [map_neg, map_one, map_mul] at h
  revert h
  generalize PadicInt.toZModPow (p := 2) 2 x = y
  revert y
  decide

/-- The formula as typed in rédaction 387, `Card(U/U²) = mod(2) · Card(₂U)`, gives `1` for `ℚ₂`,
which would make every unit a square; but the unit `-1` is not a square. -/
theorem typed_formula_fails :
    ‖(2 : ℚ_[2])‖ * 2 = 1 ∧ ∃ u : ℤ_[2]ˣ, ¬ IsSquare u := by
  refine ⟨by rw [norm_two]; norm_num, -1, ?_⟩
  rintro ⟨v, hv⟩
  exact not_isSquare_neg_one ⟨v, by simpa using congrArg (fun w : ℤ_[2]ˣ => (w : ℤ_[2])) hv⟩

end Bourbaki.Redaction387
