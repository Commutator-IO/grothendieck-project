import Mathlib

/-!
# Folder 146, page 70: the trivialising exponents of `L_i` and `L` on `M_{0,4}` and `M_{0,5}`

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
reduction from `𝔖₄` to `𝔖₃` and the formula `sgn g · g′(λ)` for the action on `L`.

The column `n = 5`, queried on the page (« 12 ? » for `L` and for `L_i`), is settled at the
end of the file at the level of cocycles: `L` has order `4` (`coboundary_cL_iff`), `L₅` has
order `12` (`coboundary_c5_iff`). The column `n = 6` (« 20 ? », « 60 ? ») is not formalised.
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

/-! ## The column `n = 5`: `L` has order `4`, `L₅` has order `12`

`M_{0,5}` is the set of `(λ, μ)` with `λ, μ ∉ {0, 1}` and `λ ≠ μ` (`U5`), the five points being
`0, 1, ∞, λ, μ`. The adjacent transpositions `s₁, …, s₄` of the labels act by `act5`, the
substitution obtained by renormalising the permuted points to `0, 1, ∞`, and on the tangent lines
at the marked points by the derivative of that renormalisation: `cL` is the factor on
`L = L₁ ⊗ ⋯ ⊗ L₅` (product of the five derivatives), `c5` the factor on `L₅` under the
stabiliser `𝔖₄` of the fifth point (`s₁, s₂, s₃`). A word in the generators acts by composition
(`wAct`) and carries the factor given by the cocycle rule (`wCoc`). Not formalised: that `act5`,
`cL`, `c5` satisfy the Coxeter relations of `𝔖₅` (checked by computer algebra), so that the
words factor through `𝔖₅`, and the derivation of the factors.

* `cL_pow_four`: `cL⁴` is the coboundary of `(λμ(1 − λ)(1 − μ)(λ − μ))²`;
  `coboundary_cL_iff`: a power `m` of `cL` is a coboundary iff `4 ∣ m` — at `(−1, i)`, fixed by
  the `4`-cycle `s₁s₂s₃`, the factor is `i`.
* `c5_pow_twelve`: `c5¹²` is the coboundary of `μ⁶(1 − μ)⁶(λ − μ)⁶/(λ²(1 − λ)²)`;
  `coboundary_c5_iff`: a power `m` of `c5` is a coboundary iff `12 ∣ m` — the factor is `i` at
  `(−1, i)`, and `ζ²` at `(1 − ζ, ζ)`, fixed by the `3`-cycle `s₁s₂`.
So the entry « 12 ? » for `L_i` checks and the entry « 12 ? » for `L` does not: `L^{⊗12}` is
trivial, but already `L^{⊗4}` is. -/

/-- Composition of a word of substitutions, the last letter acting first. -/
def wAct {ι α : Type*} (act : ι → α → α) : List ι → α → α
  | [] => id
  | i :: w => act i ∘ wAct act w

/-- The factor carried by a word, by the cocycle rule `c(gh)(x) = c(g)(hx) c(h)(x)`. -/
def wCoc {ι α : Type*} (act : ι → α → α) (c : ι → α → K) : List ι → α → K
  | [] => fun _ => 1
  | i :: w => fun x => c i (wAct act w x) * wCoc act c w x

/-- A cocycle whose `m`-th power is a coboundary on the generators is one on all words. -/
lemma wCoc_zpow {ι α : Type*} {act : ι → α → α} {c : ι → α → K} {V : α → Prop} {h : α → K}
    {m : ℤ} (hV : ∀ i x, V x → V (act i x)) (hh : ∀ x, V x → h x ≠ 0)
    (hc : ∀ i x, V x → c i x ^ m = h (act i x) / h x) :
    ∀ w x, V x → wCoc act c w x ^ m = h (wAct act w x) / h x
  | [], x, hx => by simp [wCoc, wAct, hh x hx]
  | i :: w, x, hx => by
    have hw : V (wAct act w x) := by
      induction w with
      | nil => exact hx
      | cons j w ih => exact hV j _ ih
    simp only [wCoc, wAct, Function.comp, mul_zpow, hc i _ hw, wCoc_zpow hV hh hc w x hx]
    field_simp [hh _ hw]

/-- `M_{0,5}`: `λ, μ ∉ {0, 1}`, `λ ≠ μ`. -/
def U5 (p : K × K) : Prop := p.1 ≠ 0 ∧ p.1 ≠ 1 ∧ p.2 ≠ 0 ∧ p.2 ≠ 1 ∧ p.1 ≠ p.2

/-- The adjacent transpositions `s₁, s₂, s₃, s₄` of the five labels. -/
def act5 : Fin 4 → K × K → K × K
  | 0 => fun p => (1 - p.1, 1 - p.2)
  | 1 => fun p => (p.1 / (p.1 - 1), p.2 / (p.2 - 1))
  | 2 => fun p => (1 - p.1, p.2 * (p.1 - 1) / (p.1 - p.2))
  | 3 => fun p => (p.2, p.1)

/-- Their factor on `L = L₁ ⊗ ⋯ ⊗ L₅`. -/
def cL : Fin 4 → K × K → K
  | 0 => fun _ => -1
  | 1 => fun p => -1 / ((p.1 - 1) ^ 2 * (p.2 - 1) ^ 2)
  | 2 => fun p => p.1 * (p.1 - 1) / (p.1 - p.2) ^ 2
  | 3 => fun _ => 1

/-- The factor of `s₁, s₂, s₃` on `L₅`. -/
def c5 : Fin 3 → K × K → K
  | 0 => fun _ => -1
  | 1 => fun p => -1 / (p.2 - 1) ^ 2
  | 2 => fun p => p.1 * (p.1 - 1) / (p.1 - p.2) ^ 2

/-- `s₁, s₂, s₃` as substitutions. -/
def act4 (i : Fin 3) : K × K → K × K := act5 i.castSucc

lemma act5_U5 (i : Fin 4) {p : K × K} (hp : U5 p) : U5 (act5 i p) := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨a0, a1, b0, b1, ab⟩ := hp
  simp only at a0 a1 b0 b1 ab
  have a1' : p1 - 1 ≠ 0 := sub_ne_zero.2 a1
  have b1' : p2 - 1 ≠ 0 := sub_ne_zero.2 b1
  have ab' : p1 - p2 ≠ 0 := sub_ne_zero.2 ab
  have a1'' : 1 - p1 ≠ 0 := sub_ne_zero.2 (Ne.symm a1)
  fin_cases i
  · change U5 (1 - p1, 1 - p2)
    exact ⟨a1'', fun e => a0 (by linear_combination -e), sub_ne_zero.2 (Ne.symm b1),
      fun e => b0 (by linear_combination -e), fun e => ab (by linear_combination -e)⟩
  · change U5 (p1 / (p1 - 1), p2 / (p2 - 1))
    refine ⟨div_ne_zero a0 a1', fun e => ?_, div_ne_zero b0 b1', fun e => ?_, fun e => ?_⟩
    · rw [div_eq_one_iff_eq a1'] at e; exact one_ne_zero (α := K) (by linear_combination e)
    · rw [div_eq_one_iff_eq b1'] at e; exact one_ne_zero (α := K) (by linear_combination e)
    · rw [div_eq_div_iff a1' b1'] at e; exact ab (by linear_combination -e)
  · change U5 (1 - p1, p2 * (p1 - 1) / (p1 - p2))
    refine ⟨a1'', fun e => a0 (by linear_combination -e), div_ne_zero (mul_ne_zero b0 a1') ab',
      fun e => ?_, fun e => ?_⟩
    · rw [div_eq_one_iff_eq ab'] at e; exact mul_ne_zero a0 b1' (by linear_combination e)
    · rw [eq_div_iff ab'] at e; exact mul_ne_zero a1'' a0 (by linear_combination e)
  · exact (⟨b0, b1, a0, a1, Ne.symm ab⟩ : U5 (p2, p1))

/-- `h = (λμ(1 − λ)(1 − μ)(λ − μ))²`. -/
def hL (p : K × K) : K := (p.1 * p.2 * (1 - p.1) * (1 - p.2) * (p.1 - p.2)) ^ 2

/-- `h = μ⁶(1 − μ)⁶(λ − μ)⁶/(λ²(1 − λ)²)`. -/
def h5 (p : K × K) : K := p.2 ^ 6 * (1 - p.2) ^ 6 * (p.1 - p.2) ^ 6 / (p.1 ^ 2 * (1 - p.1) ^ 2)

lemma hL_ne {p : K × K} (hp : U5 p) : hL p ≠ 0 := by
  obtain ⟨a0, a1, b0, b1, ab⟩ := hp
  simp only [hL]
  have := sub_ne_zero.2 (Ne.symm a1); have := sub_ne_zero.2 (Ne.symm b1)
  have := sub_ne_zero.2 ab
  positivity

lemma h5_ne {p : K × K} (hp : U5 p) : h5 p ≠ 0 := by
  obtain ⟨a0, a1, b0, b1, ab⟩ := hp
  simp only [h5]
  have := sub_ne_zero.2 (Ne.symm a1); have := sub_ne_zero.2 (Ne.symm b1)
  have := sub_ne_zero.2 ab
  positivity

/-- `L^{⊗4}` is equivariantly trivial: `cL(s)⁴ = h(sx)/h(x)` on the generators, with
`h = (λμ(1 − λ)(1 − μ)(λ − μ))²`. -/
theorem cL_pow_four (i : Fin 4) {p : K × K} (hp : U5 p) :
    cL i p ^ 4 = hL (act5 i p) / hL p := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨a0, a1, b0, b1, ab⟩ := hp
  simp only at a0 a1 b0 b1 ab
  have a1' : p1 - 1 ≠ 0 := sub_ne_zero.2 a1
  have b1' : p2 - 1 ≠ 0 := sub_ne_zero.2 b1
  have ab' : p1 - p2 ≠ 0 := sub_ne_zero.2 ab
  have a1'' : 1 - p1 ≠ 0 := sub_ne_zero.2 (Ne.symm a1)
  have b1'' : 1 - p2 ≠ 0 := sub_ne_zero.2 (Ne.symm b1)
  fin_cases i <;> simp [cL, act5, hL] <;> field_simp <;> ring

/-- `L₅^{⊗12}` is equivariantly trivial under `𝔖₄`: `c5(s)¹² = h(sx)/h(x)` on the generators,
with `h = μ⁶(1 − μ)⁶(λ − μ)⁶/(λ²(1 − λ)²)`. -/
theorem c5_pow_twelve (i : Fin 3) {p : K × K} (hp : U5 p) :
    c5 i p ^ 12 = h5 (act4 i p) / h5 p := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨a0, a1, b0, b1, ab⟩ := hp
  simp only at a0 a1 b0 b1 ab
  have a1' : p1 - 1 ≠ 0 := sub_ne_zero.2 a1
  have b1' : p2 - 1 ≠ 0 := sub_ne_zero.2 b1
  have ab' : p1 - p2 ≠ 0 := sub_ne_zero.2 ab
  have a1'' : 1 - p1 ≠ 0 := sub_ne_zero.2 (Ne.symm a1)
  have b1'' : 1 - p2 ≠ 0 := sub_ne_zero.2 (Ne.symm b1)
  fin_cases i <;> simp [c5, act4, act5, h5] <;> field_simp <;> ring

/-- `i` is a primitive fourth root of unity when `2 ≠ 0`: `i^m = 1` forces `4 ∣ m`. -/
lemma four_dvd_of_pow (h2 : (2 : K) ≠ 0) {ι : K} (hι : ι ^ 2 = -1) (m : ℤ) (e : ι ^ m = 1) :
    4 ∣ m := by
  have hι0 : ι ≠ 0 := fun h => h2 (by rw [h] at hι; linear_combination 2 * hι)
  have w4 : ι ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((2 * 2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_mul, hι]; norm_num
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) ∧ m = 4 * q + r :=
    ⟨m / 4, m % 4, by omega, by omega⟩
  rw [zpow_add₀ hι0, zpow_mul, w4, one_zpow, one_mul] at e
  rcases hr with rfl | rfl | rfl | rfl
  · simp
  · have : ι = 1 := by simpa using e
    exact absurd (by rw [this] at hι; linear_combination hι) h2
  · have : ι ^ 2 = 1 := by simpa using e
    exact absurd (by linear_combination hι - this) h2
  · have : ι ^ 3 = 1 := by simpa using e
    exact absurd (by linear_combination (1 - ι ^ 2 + ι) * hι + (ι - 1) * this) h2

/-- The point `(−1, i)` of `M_{0,5}` is fixed by the `4`-cycle `s₁s₂s₃`, where the factor on
`L`, and on `L₅`, is `i`. -/
lemma fix_four (h2 : (2 : K) ≠ 0) {ι : K} (hι : ι ^ 2 = -1) :
    U5 ((-1 : K), ι) ∧ wAct act5 [0, 1, 2] ((-1 : K), ι) = (-1, ι) ∧
      wCoc act5 cL [0, 1, 2] ((-1 : K), ι) = ι ∧
      wAct act4 [0, 1, 2] ((-1 : K), ι) = (-1, ι) ∧
      wCoc act4 c5 [0, 1, 2] ((-1 : K), ι) = ι := by
  have hι0 : ι ≠ 0 := fun h => h2 (by rw [h] at hι; linear_combination 2 * hι)
  have hι1 : ι ≠ 1 := fun h => h2 (by rw [h] at hι; linear_combination hι)
  have hιm : ι ≠ -1 := fun h => h2 (by rw [h] at hι; linear_combination hι)
  have hne : (-1 : K) - ι ≠ 0 := fun h => hιm (by linear_combination -h)
  have s2 : act5 2 ((-1 : K), ι) = (2, ι + 1) := by
    change ((1 - -1 : K), ι * (-1 - 1) / (-1 - ι)) = (2, ι + 1)
    rw [show ι * (-1 - 1) / (-1 - ι) = ι + 1 by rw [div_eq_iff hne]; linear_combination hι]
    norm_num
  have s1 : act5 1 ((2 : K), ι + 1) = (2, 1 - ι) := by
    change ((2 : K) / (2 - 1), (ι + 1) / (ι + 1 - 1)) = (2, 1 - ι)
    rw [show (ι + 1) / (ι + 1 - 1) = 1 - ι by
      rw [add_sub_cancel_right, div_eq_iff hι0]; linear_combination hι]
    norm_num
  have s0 : act5 0 ((2 : K), 1 - ι) = (-1, ι) := by
    change ((1 - 2 : K), 1 - (1 - ι)) = (-1, ι)
    exact Prod.ext (by norm_num) (by ring)
  have hv : (-1 : K) * (-1 / ((2 - 1) ^ 2 * (ι + 1 - 1) ^ 2) * (-1 * (-1 - 1) / (-1 - ι) ^ 2 * 1))
      = ι := by
    rw [show (ι + 1 - 1 : K) ^ 2 = -1 by linear_combination hι,
      show (-1 - ι : K) ^ 2 = 2 * ι by linear_combination hι]
    field_simp
    linear_combination -2 * hι
  refine ⟨⟨by norm_num, fun h => h2 (by linear_combination -h), hι0, hι1, fun h => hιm h.symm⟩,
    ?_, ?_, ?_, ?_⟩
  · change act5 0 (act5 1 (act5 2 ((-1 : K), ι))) = _
    rw [s2, s1, s0]
  · change cL 0 (act5 1 (act5 2 ((-1 : K), ι))) * (cL 1 (act5 2 ((-1 : K), ι)) *
      (cL 2 ((-1 : K), ι) * 1)) = ι
    rw [s2, s1]; exact hv
  · change act5 0 (act5 1 (act5 2 ((-1 : K), ι))) = _
    rw [s2, s1, s0]
  · change c5 0 (act5 1 (act5 2 ((-1 : K), ι))) * (c5 1 (act5 2 ((-1 : K), ι)) *
      (c5 2 ((-1 : K), ι) * 1)) = ι
    rw [s2, s1]
    exact (by norm_num : (-1 : K) * (-1 / (ι + 1 - 1) ^ 2 * (-1 * (-1 - 1) / (-1 - ι) ^ 2 * 1))
      = _).trans hv

/-- The point `(1 − ζ, ζ)` of `M_{0,5}` is fixed by the `3`-cycle `s₁s₂`, where the factor on
`L₅` is `ζ²`. -/
lemma fix_three (h3 : (3 : K) ≠ 0) {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0) :
    U5 (1 - ζ, ζ) ∧ wAct act4 [0, 1] (1 - ζ, ζ) = (1 - ζ, ζ) ∧
      wCoc act4 c5 [0, 1] (1 - ζ, ζ) = ζ ^ 2 := by
  obtain ⟨⟨hζ0, hζ1⟩, -, -⟩ := fix_zeta hζ
  have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hζ1'' : 1 - ζ - 1 ≠ 0 := by rw [sub_sub_cancel_left]; exact neg_ne_zero.2 hζ0
  have s1 : act5 1 (1 - ζ, ζ) = (ζ, 1 - ζ) := by
    change ((1 - ζ) / (1 - ζ - 1), ζ / (ζ - 1)) = (ζ, 1 - ζ)
    exact Prod.ext (by rw [div_eq_iff hζ1'']; linear_combination hζ)
      (by rw [div_eq_iff hζ1']; linear_combination hζ)
  refine ⟨⟨fun h => hζ1 (by linear_combination -h), fun h => hζ0 (by linear_combination -h),
    hζ0, hζ1, fun h => h3 (by linear_combination 4 * hζ - (1 - 2 * ζ) * h)⟩, ?_, ?_⟩
  · change act5 0 (act5 1 (1 - ζ, ζ)) = _
    rw [s1]; exact Prod.ext rfl (sub_sub_cancel 1 ζ)
  · change c5 0 (act5 1 (1 - ζ, ζ)) * (c5 1 (1 - ζ, ζ) * 1) = ζ ^ 2
    rw [s1]
    change (-1 : K) * (-1 / (ζ - 1) ^ 2 * 1) = ζ ^ 2
    rw [show (-1 : K) * (-1 / (ζ - 1) ^ 2 * 1) = 1 / (ζ - 1) ^ 2 by ring,
      div_eq_iff (pow_ne_zero 2 hζ1')]
    linear_combination (-(ζ ^ 2 - ζ - 1)) * hζ

/-- The entry « 12 ? » of page 70 for `L`, `n = 5`, does not check: a power `m` of the cocycle
of `L` is the coboundary of a nowhere-zero function on `M_{0,5}(K)` iff `4 ∣ m` (`2 ≠ 0`,
`i² = −1`). -/
theorem coboundary_cL_iff (h2 : (2 : K) ≠ 0) {ι : K} (hι : ι ^ 2 = -1) (m : ℤ) :
    (∃ h : K × K → K, (∀ p, U5 p → h p ≠ 0) ∧
      ∀ w p, U5 p → wCoc act5 cL w p ^ m = h (wAct act5 w p) / h p) ↔ 4 ∣ m := by
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨hU, hfix, hcoc, -, -⟩ := fix_four h2 hι
    have e := hc [0, 1, 2] _ hU
    rw [hfix, hcoc, div_self (hh _ hU)] at e
    exact four_dvd_of_pow h2 hι m e
  · rintro ⟨t, rfl⟩
    refine ⟨fun p => hL p ^ t, fun p hp => zpow_ne_zero _ (hL_ne hp), ?_⟩
    refine wCoc_zpow (V := U5) (h := fun p => hL p ^ t) (fun i p hp => act5_U5 i hp)
      (fun p hp => zpow_ne_zero _ (hL_ne hp)) ?_
    intro i p hp
    rw [zpow_mul, show cL i p ^ (4 : ℤ) = _ by exact_mod_cast cL_pow_four i hp, div_zpow]

/-- The entry « 12 ? » of page 70 for `L_i`, `n = 5`, checks: a power `m` of the cocycle of
`L₅` under `𝔖₄` is the coboundary of a nowhere-zero function on `M_{0,5}(K)` iff `12 ∣ m`
(`2 ≠ 0`, `3 ≠ 0`, `i² = −1`, `ζ² − ζ + 1 = 0`). -/
theorem coboundary_c5_iff (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {ι : K} (hι : ι ^ 2 = -1)
    {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0) (m : ℤ) :
    (∃ h : K × K → K, (∀ p, U5 p → h p ≠ 0) ∧
      ∀ w p, U5 p → wCoc act4 c5 w p ^ m = h (wAct act4 w p) / h p) ↔ 12 ∣ m := by
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨hU, -, -, hfix, hcoc⟩ := fix_four h2 hι
    have e := hc [0, 1, 2] _ hU
    rw [hfix, hcoc, div_self (hh _ hU)] at e
    obtain ⟨hU', hfix', hcoc'⟩ := fix_three h3 hζ
    have e' := hc [0, 1] _ hU'
    rw [hfix', hcoc', div_self (hh _ hU')] at e'
    have := four_dvd_of_pow h2 hι m e
    have := three_dvd_of_pow h3 hζ m e'
    omega
  · rintro ⟨t, rfl⟩
    refine ⟨fun p => h5 p ^ t, fun p hp => zpow_ne_zero _ (h5_ne hp), ?_⟩
    refine wCoc_zpow (V := U5) (h := fun p => h5 p ^ t) (fun i p hp => act5_U5 _ hp)
      (fun p hp => zpow_ne_zero _ (h5_ne hp)) ?_
    intro i p hp
    rw [zpow_mul, show c5 i p ^ (12 : ℤ) = _ by exact_mod_cast c5_pow_twelve i hp, div_zpow]

end Grothendieck.Folder146
