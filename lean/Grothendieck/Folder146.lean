import Mathlib

/-!
# Folder 146, page 70: the trivialising exponents of `L₄` and `L` on `M_{0,4}`, `6` and `3`

The modernised reading `transcripts/146/146.modern.tex` (« Les fibrés `L_i` et le groupe de
Picard équivariant », pages 70 to 73) describes the table of page 70: for `n = card I`, the
smallest exponent that makes the line bundles `L_i` (attached to the marked points), and
`L = ⊗ L_i`, trivial compatibly with the symmetric group on `M_{0,I}`; for `n = 4` the table
gives `3` for `L` and `6` for `L_i`. The reading does not verify the table. This file settles the
two entries for `n = 4`; it is the reachable part of finding
`146-equivariant-trivialising-exponents` of `src/content/findings.ts`, which drops if the
`n = 4` values do not check.

The model. `M_{0,4} = U = ℙ¹ ∖ {0, 1, ∞}` with coordinate `λ`, the fourth point moving;
`𝔖_{I∖{4}} = 𝔖₃` permutes `0, 1, ∞` and acts on `U` by the six anharmonic substitutions
(`anh`, composition table `mul`, `mul_group`, `anh_mul`), and on the tangent line `L₄` at the
moving point through the derivative `g′(λ)` (`der`). By the chain rule (`der_mul`),
`g ↦ g′(λ)` is a 1-cocycle of `𝔖₃` with values in the units of `O(U)`; as `Pic(U) = 0`, the
equivariant structures on `L₄^{⊗m}` up to isomorphism are classified by the class of its
`m`-th power, and the exponent of the table is the order of that class.

* `der_pow_six`: `g′(λ)⁶ = h(gλ)/h(λ)` with `h = λ⁴(1 − λ)⁴`, so `L₄^{⊗6}` is equivariantly
  trivial.
* `six_dvd`: if `g′(λ)^m = h(gλ)/h(λ)` for all `g` and `λ ∈ U(K)`, for any nowhere-zero function
  `h`, regular or not, then `6 ∣ m` — over a field with `2 ≠ 0`, `3 ≠ 0` and a root `ζ` of
  `ζ² − ζ + 1`. At a fixed point of `g` the right side is `1`: `λ = −1` is fixed by `1/λ`, where
  `g′ = −1`, and `ζ` is fixed by `1/(1 − λ)`, where `g′ = ζ²`, a primitive cube root of unity.

So the class of `L₄` has order exactly `6`, the value of the table.

The entry `3` for `L = L₁ ⊗ L₂ ⊗ L₃ ⊗ L₄` under `𝔖₄`, page 70, also checks, for the cocycle
`derL g = sgn g · g′(λ)` of `L` (the Klein group acting trivially, see the section on `L`):
* `derL_mul`: it is a 1-cocycle; `derL_pow_three`: its cube is the coboundary of
  `λ²(1 − λ)²`;
* `coboundary_derL_iff`: its `m`-th power is the coboundary of a nowhere-zero function on
  `U(K)` iff `3 ∣ m` (`3 ≠ 0`, a root `ζ` of `ζ² − ζ + 1`, where the factor is `ζ²`).
Page 72 only claims `L^{⊗6} ≃ 1`.

Not formalised: the identification of the equivariant Picard group with `H¹(𝔖₃, O(U)^*)`, the
reduction from `𝔖₄` to `𝔖₃` and the formula `sgn g · g′(λ)` for the action on `L`, and the
queried values for `n = 5, 6`.
-/

namespace Grothendieck.Folder146

/-! ## The anharmonic group -/

/-- Composition table of the six anharmonic substitutions `λ, 1/λ, 1 − λ, λ/(λ − 1),
1/(1 − λ), (λ − 1)/λ`: `mul a b` is `a ∘ b`. -/
def mul (a b : Fin 6) : Fin 6 :=
  ![![0, 1, 2, 3, 4, 5], ![1, 0, 4, 5, 2, 3], ![2, 5, 0, 4, 3, 1], ![3, 4, 5, 0, 1, 2],
    ![4, 3, 1, 2, 5, 0], ![5, 2, 3, 1, 0, 4]] a b

/-- The table is a group with unit `0`, and it is not commutative: it is `𝔖₃`. -/
theorem mul_group : (∀ a b c, mul (mul a b) c = mul a (mul b c)) ∧ (∀ a, mul 0 a = a) ∧
    (∀ a, ∃ b, mul b a = 0) ∧ mul 1 2 ≠ mul 2 1 := by decide

variable {K : Type*} [Field K]

/-- The substitutions. -/
def anh : Fin 6 → K → K
  | 0 => fun x => x
  | 1 => fun x => 1 / x
  | 2 => fun x => 1 - x
  | 3 => fun x => x / (x - 1)
  | 4 => fun x => 1 / (1 - x)
  | 5 => fun x => (x - 1) / x

/-- Their derivatives `g′(λ)`: the action on the tangent line `L₄` at the fourth point. -/
def der : Fin 6 → K → K
  | 0 => fun _ => 1
  | 1 => fun x => -1 / x ^ 2
  | 2 => fun _ => -1
  | 3 => fun x => -1 / (x - 1) ^ 2
  | 4 => fun x => 1 / (1 - x) ^ 2
  | 5 => fun x => 1 / x ^ 2

/-- `U = ℙ¹ ∖ {0, 1, ∞}`. -/
def U (x : K) : Prop := x ≠ 0 ∧ x ≠ 1

/-- The substitutions compose by the table: an action of `𝔖₃` on `U`. -/
theorem anh_mul (a b : Fin 6) {x : K} (hx : U x) : anh (mul a b) x = anh a (anh b x) := by
  obtain ⟨h0, h1⟩ := hx
  have h1' : x - 1 ≠ 0 := sub_ne_zero.2 h1
  have h1'' : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  fin_cases a <;> fin_cases b
  all_goals first
    | (change (1 : K) / x = (1 / (1 - x)) / (1 / (1 - x) - 1)
       rw [div_sub_one h1'', sub_sub_cancel]; field_simp)
    | (change (x - 1) / x = 1 / (1 - 1 / (1 - x))
       rw [one_sub_div h1'', sub_sub_cancel_left]; field_simp; ring)
    | (simp [mul, anh]; field_simp; ring)
    | (simp [mul, anh]; field_simp)
    | simp [mul, anh]

/-- The chain rule `(g ∘ h)′(λ) = g′(h λ) h′(λ)`: `g ↦ g′(λ)` is a 1-cocycle of `𝔖₃` with
values in the units of `O(U)`. -/
theorem der_mul (a b : Fin 6) {x : K} (hx : U x) :
    der (mul a b) x = der a (anh b x) * der b x := by
  obtain ⟨h0, h1⟩ := hx
  have h1' : x - 1 ≠ 0 := sub_ne_zero.2 h1
  have h1'' : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  fin_cases a <;> fin_cases b
  all_goals first
    | (change (-1 : K) / x ^ 2 = -1 / (1 / (1 - x) - 1) ^ 2 * (1 / (1 - x) ^ 2)
       rw [div_sub_one h1'', sub_sub_cancel]; field_simp)
    | (change (1 : K) / x ^ 2 = 1 / (1 - 1 / (1 - x)) ^ 2 * (1 / (1 - x) ^ 2)
       rw [one_sub_div h1'', sub_sub_cancel_left]; field_simp)
    | (simp [mul, anh, der]; field_simp; ring)
    | (simp [mul, anh, der]; field_simp)
    | simp [mul, anh, der]

/-- `h = λ⁴(1 − λ)⁴`. -/
def h6 (x : K) : K := x ^ 4 * (1 - x) ^ 4

/-- `L₄^{⊗6}` is equivariantly trivial: `g′(λ)⁶ = h(gλ)/h(λ)` with `h = λ⁴(1 − λ)⁴`. -/
theorem der_pow_six (a : Fin 6) {x : K} (hx : U x) : der a x ^ 6 = h6 (anh a x) / h6 x := by
  obtain ⟨h0, h1⟩ := hx
  have h1' : x - 1 ≠ 0 := sub_ne_zero.2 h1
  have h1'' : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  fin_cases a <;> simp [anh, der, h6] <;> field_simp <;> ring

/-- The root `ζ` of `ζ² − ζ + 1` is a point of `U` fixed by `1/(1 − λ)`, where the derivative
is `ζ²`. -/
lemma fix_zeta {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0) : U ζ ∧ anh 4 ζ = ζ ∧ der 4 ζ = ζ ^ 2 := by
  have hUζ : U ζ := ⟨fun e => by simp [e] at hζ, fun e => by simp [e] at hζ⟩
  have hfix : 1 / (1 - ζ) = ζ := by
    have : 1 - ζ ≠ 0 := sub_ne_zero.2 (Ne.symm hUζ.2)
    field_simp; linear_combination hζ
  exact ⟨hUζ, hfix, show 1 / (1 - ζ) ^ 2 = ζ ^ 2 by rw [one_div, ← inv_pow, ← one_div, hfix]⟩

/-- `ζ²` is a primitive cube root of unity when `3 ≠ 0`: `(ζ²)^m = 1` forces `3 ∣ m`. -/
lemma three_dvd_of_pow (h3 : (3 : K) ≠ 0) {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0) (m : ℤ)
    (e : (ζ ^ 2) ^ m = 1) : 3 ∣ m := by
  have w1 : ζ ^ 2 ≠ 1 := fun e => h3 (by linear_combination (-1 - ζ) * e + (ζ + 2) * hζ)
  have w3 : (ζ ^ 2) ^ 3 = 1 := by linear_combination (ζ ^ 4 + ζ ^ 3 - ζ - 1) * hζ
  have hw0 : ζ ^ 2 ≠ 0 := pow_ne_zero _ (fix_zeta hζ).1.1
  generalize ζ ^ 2 = w at e w1 w3 hw0
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1 ∨ r = 2) ∧ m = 3 * q + r :=
    ⟨m / 3, m % 3, by omega, by omega⟩
  rw [zpow_add₀ hw0, zpow_mul, show w ^ (3 : ℤ) = 1 by exact_mod_cast w3, one_zpow,
    one_mul] at e
  rcases hr with rfl | rfl | rfl
  · simp
  · exact absurd (by simpa using e) w1
  · rw [pow_succ, show w ^ 2 = 1 by simpa using e, one_mul] at w3
    exact absurd w3 w1

/-- No smaller power is a coboundary, even among all nowhere-zero functions on `U(K)`: if
`g′(λ)^m = h(gλ)/h(λ)` for all `g` and `λ`, then `6 ∣ m`. At `λ = −1`, fixed by `1/λ` with
derivative `−1`, and at a root `ζ` of `ζ² − ζ + 1`, fixed by `1/(1 − λ)` with derivative `ζ²`,
a primitive cube root of unity. -/
theorem six_dvd (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0)
    (m : ℤ) (h : K → K) (hh : ∀ x, U x → h x ≠ 0)
    (hc : ∀ a x, U x → der a x ^ m = h (anh a x) / h x) : 6 ∣ m := by
  have hU1 : U (-1 : K) := ⟨by simp, fun e => h2 (by linear_combination -e)⟩
  have e1' : (-1 : K) ^ m = 1 := by simpa [der, anh, hh _ hU1] using hc 1 (-1) hU1
  have h2m : 2 ∣ m := by
    rcases Int.even_or_odd m with he | ho
    · exact even_iff_two_dvd.1 he
    · rw [ho.neg_one_zpow] at e1'
      exact absurd (by linear_combination -e1') h2
  obtain ⟨hUζ, hfix, hder⟩ := fix_zeta hζ
  have e := hc 4 ζ hUζ
  rw [hder, hfix, div_self (hh _ hUζ)] at e
  have := three_dvd_of_pow h3 hζ m e
  omega

/-! ## The bundle `L = L₁ ⊗ L₂ ⊗ L₃ ⊗ L₄` under `𝔖₄`

On `M_{0,4}`, `g ∈ 𝔖₄` acts on `L` by the product of the derivatives of the induced
automorphism of the fibre at the four marked points. The Klein subgroup acts trivially on `U`
and on `L` (it pairs the points, and the derivatives at the two points of a pair multiply to
`1`), and `𝔖₄/V₄ ≃ 𝔖₃`, the stabiliser of the fourth point. For `g` in it the derivatives at
`0, 1, ∞` multiply to the constant `sgn g` and the one at `λ` is `g′(λ)`, so the cocycle of
`L` is `sgn g · g′(λ)` (`derL`). These identifications, and the injectivity of inflation
`H¹(𝔖₃, ·) → H¹(𝔖₄, ·)` that makes the order under `𝔖₄` the order under `𝔖₃`, are not
formalised. -/

/-- The sign of the six substitutions. -/
def sgn : Fin 6 → K
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | 3 => -1
  | 4 => 1
  | 5 => 1

lemma sgn_mul (a b : Fin 6) : sgn (K := K) (mul a b) = sgn a * sgn b := by
  fin_cases a <;> fin_cases b <;> simp [sgn, mul]

/-- The cocycle of `L = ⊗ L_i`: `sgn g · g′(λ)`. -/
def derL (a : Fin 6) (x : K) : K := sgn a * der a x

/-- `derL` is a 1-cocycle. -/
theorem derL_mul (a b : Fin 6) {x : K} (hx : U x) :
    derL (mul a b) x = derL a (anh b x) * derL b x := by
  simp only [derL, sgn_mul, der_mul a b hx]; ring

/-- `h = λ²(1 − λ)²`. -/
def h3 (x : K) : K := x ^ 2 * (1 - x) ^ 2

/-- `L^{⊗3}` is equivariantly trivial: `(sgn g · g′(λ))³ = h(gλ)/h(λ)` with `h = λ²(1 − λ)²`. -/
theorem derL_pow_three (a : Fin 6) {x : K} (hx : U x) :
    derL a x ^ 3 = h3 (anh a x) / h3 x := by
  obtain ⟨h0, h1⟩ := hx
  have h1' : x - 1 ≠ 0 := sub_ne_zero.2 h1
  have h1'' : 1 - x ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  fin_cases a <;> simp [derL, sgn, anh, der, h3] <;> field_simp <;> ring

/-- The entry « 3 » of page 70 for `L`, `n = 4`: a power `m` of the cocycle of `L` is a
coboundary of a nowhere-zero function on `U(K)` iff `3 ∣ m` (`3 ≠ 0`, `ζ² − ζ + 1 = 0`). At `ζ`,
fixed by `1/(1 − λ)`, the factor is `ζ²`. -/
theorem coboundary_derL_iff (h3K : (3 : K) ≠ 0) {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0) (m : ℤ) :
    (∃ h : K → K, (∀ x, U x → h x ≠ 0) ∧ ∀ a x, U x → derL a x ^ m = h (anh a x) / h x) ↔
      3 ∣ m := by
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨hUζ, hfix, hder⟩ := fix_zeta hζ
    have e := hc 4 ζ hUζ
    rw [derL, hder, hfix, div_self (hh _ hUζ)] at e
    exact three_dvd_of_pow h3K hζ m (by simpa [sgn] using e)
  · rintro ⟨t, rfl⟩
    refine ⟨fun x => h3 x ^ t, fun x ⟨h0, h1⟩ => zpow_ne_zero _ (mul_ne_zero (pow_ne_zero _ h0)
      (pow_ne_zero _ (sub_ne_zero.2 (Ne.symm h1)))), fun a x hx => ?_⟩
    rw [zpow_mul, show derL a x ^ (3 : ℤ) = _ by exact_mod_cast derL_pow_three a hx, div_zpow]

end Grothendieck.Folder146
