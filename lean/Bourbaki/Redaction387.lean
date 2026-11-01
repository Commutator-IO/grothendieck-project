import Mathlib

/-!
# Bourbaki rédaction n° 387: the index of the `n`-th powers among the units of a local field

Rédaction n° 387 of the Bourbaki archive (J. Dieudonné, *Algèbre commutative, chapitre VI,
Valuations*; Archives Henri Poincaré, item
<https://archives-bourbaki.ahp-numerique.fr/items/show/942>), § 9, exercise 3, p. 67, concerns a
locally compact non-discrete field `K`, its group of units `U` (the units of the valuation ring)
and an integer `n ≥ 1`. The typed exercise gives the index `[U : Uⁿ]` as the product of the
module of `n` and of the number of `n`-th roots of unity in `K`. The correct formula divides
instead: `[U : Uⁿ] = Card μₙ(K) / mod(n)`.

The typed form fails already for `K = ℚ₂` and `n = 2`: the module of `2` is `|2|₂ = 1/2`,
`μ₂(ℚ₂) = {±1}` has two elements, and the typed product is `1`, while `[ℤ₂ˣ : (ℤ₂ˣ)²] = 4`. This
file proves that.

* `sq_toZModPow_three_eq_one`: the square of a unit of `ℤ₂` is `≡ 1 (mod 8)`;
* `isSquare_of_toZModPow_three_eq_one`: conversely, by Hensel's lemma, a unit `≡ 1 (mod 8)` is
  a square;
* `squares_eq_ker`: the subgroup of squares of `ℤ₂ˣ` is the kernel of the reduction
  `ℤ₂ˣ → (ℤ/8)ˣ`;
* `index_squares`: `[ℤ₂ˣ : (ℤ₂ˣ)²] = 4`;
* `card_rootsOfUnity_two`, `norm_two`: `Card μ₂(ℚ₂) = 2` and `‖2‖ = 1/2` in `ℚ₂`;
* `sq_eq_one_iff`, `one_ne_neg_one`, `not_isSquare_neg_one`: the square roots of `1` in `ℤ₂ˣ` are
  `±1`, which are distinct, and `-1` is not a square, already modulo `4`;
* `typed_formula_fails`, `corrected_formula_holds`: the typed product `‖2‖ · Card μ₂(ℚ₂)` is
  `1 ≠ 4`, the corrected quotient `Card μ₂(ℚ₂) / ‖2‖` is `4`.

That the module of `ℚ_p` (the factor by which multiplication scales a Haar measure) is the
`p`-adic norm, and that the units of `ℚ₂` in the sense of the exercise are `ℤ₂ˣ`, are classical
and not formalised here; the file works with `‖·‖` and `ℤ_[2]ˣ` directly.
-/

open PadicInt

namespace Bourbaki.Redaction387

/-- The squaring map on the units of `ℤ₂`, as a group homomorphism. -/
noncomputable abbrev sqHom : ℤ_[2]ˣ →* ℤ_[2]ˣ := powMonoidHom 2

/-- The reduction `ℤ₂ˣ → (ℤ/8)ˣ`. -/
noncomputable abbrev red8 : ℤ_[2]ˣ →* (ZMod (2 ^ 3))ˣ := Units.map (toZModPow 3).toMonoidHom

/-- Every unit of `ℤ/8` squares to `1`. -/
theorem sq_eq_one_zmod8 (w : (ZMod (2 ^ 3))ˣ) : w ^ 2 = 1 := by
  revert w
  decide

/-- **Squares are `1` mod 8**: the square of a unit of `ℤ₂` reduces to `1` in `ℤ/8`. -/
theorem sq_toZModPow_three_eq_one (v : ℤ_[2]ˣ) : red8 (v ^ 2) = 1 := by
  rw [map_pow]
  exact sq_eq_one_zmod8 _

/-- The norm of `2` in `ℤ₂` is `1/2`. -/
theorem norm_two_int : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
  have := PadicInt.norm_p (p := 2)
  simpa using this

/-- **Units `≡ 1 (mod 8)` are squares**, by Hensel's lemma applied to `X² − u` at `1`:
`‖1 − u‖ ≤ 1/8 < 1/4 = ‖2‖²`. -/
theorem isSquare_of_toZModPow_three_eq_one (u : ℤ_[2]ˣ) (hu : red8 u = 1) :
    ∃ v : ℤ_[2]ˣ, v ^ 2 = u := by
  -- `u - 1` is divisible by `8`
  have hker : (u : ℤ_[2]) - 1 ∈ RingHom.ker (toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) := by
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
    have := congrArg Units.val hu
    simp only [Units.coe_map, Units.val_one] at this
    exact this
  rw [ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨c, hc⟩ := hker
  have hnorm1 : ‖(u : ℤ_[2]) - 1‖ ≤ 1 / 8 := by
    rw [hc, norm_mul, norm_pow]
    have h2 : ‖((2 : ℕ) : ℤ_[2])‖ = 1 / 2 := by simpa using norm_two_int
    rw [h2]
    have := norm_le_one c
    nlinarith [norm_nonneg c]
  set F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[2]) with hF
  have hFa : F.aeval (1 : ℤ_[2]) = 1 - u := by simp [hF]
  have hF'a : F.derivative.aeval (1 : ℤ_[2]) = 2 := by
    simp [hF, one_add_one_eq_two]
  have hnorm : ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hFa, hF'a, norm_two_int, norm_sub_rev]
    linarith
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  have hz2 : z ^ 2 = u := by
    have : z ^ 2 - u = 0 := by simpa [hF] using hz
    exact sub_eq_zero.mp this
  have hzu : IsUnit z := by
    have : IsUnit (z ^ 2) := hz2 ▸ u.isUnit
    exact (isUnit_pow_iff two_ne_zero).mp this
  refine ⟨hzu.unit, Units.ext ?_⟩
  simp [hz2]

/-- **The squares are the kernel of the reduction mod 8.** -/
theorem squares_eq_ker : sqHom.range = red8.ker := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    exact sq_toZModPow_three_eq_one v
  · intro hu
    obtain ⟨v, hv⟩ := isSquare_of_toZModPow_three_eq_one u hu
    exact ⟨v, hv⟩

/-- The reduction `ℤ₂ˣ → (ℤ/8)ˣ` is surjective (`ℤ₂` is local and `ℤ₂ → ℤ/8` is onto). -/
theorem red8_surjective : Function.Surjective red8 := by
  have hs : Function.Surjective (toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) :=
    ZMod.ringHom_surjective _
  exact IsLocalRing.surjective_units_map_of_local_ringHom _ hs (IsLocalHom.of_surjective _ hs)

/-- **`[ℤ₂ˣ : (ℤ₂ˣ)²] = 4`.** -/
theorem index_squares : sqHom.range.index = 4 := by
  rw [squares_eq_ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr red8_surjective,
    Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  decide

/-- `μ₂(ℚ₂) = {±1}` has two elements. -/
theorem card_rootsOfUnity_two : Nat.card (rootsOfUnity 2 ℚ_[2]) = 2 :=
  (IsPrimitiveRoot.neg_one 0 (by norm_num)).card_rootsOfUnity

/-- The norm of `2` in `ℚ₂` is `1/2`. -/
theorem norm_two : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
  simpa using Padic.norm_p (p := 2)

/-- **The typed formula fails** for `K = ℚ₂`, `n = 2`: the product of the module of `2` and of
the number of square roots of unity is `1`, while the index of the squares is `4`. -/
theorem typed_formula_fails :
    ‖(2 : ℚ_[2])‖ * Nat.card (rootsOfUnity 2 ℚ_[2]) = 1 ∧
      (sqHom.range.index : ℝ) ≠ ‖(2 : ℚ_[2])‖ * Nat.card (rootsOfUnity 2 ℚ_[2]) := by
  rw [norm_two, card_rootsOfUnity_two, index_squares]
  norm_num

/-- **The corrected formula holds** for `K = ℚ₂`, `n = 2`:
`[U : U²] = Card μ₂(ℚ₂) / ‖2‖ = 4`. -/
theorem corrected_formula_holds :
    (sqHom.range.index : ℝ) = Nat.card (rootsOfUnity 2 ℚ_[2]) / ‖(2 : ℚ_[2])‖ := by
  rw [norm_two, card_rootsOfUnity_two, index_squares]
  norm_num

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

end Bourbaki.Redaction387
