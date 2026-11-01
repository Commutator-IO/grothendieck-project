import Mathlib

/-!
# Bourbaki, rédaction n° 582 (Serre, 1972): two slips, in annex c/ and in the report, p. 18

**Annex c/** of the dossier is § 2 of rédaction 300 (Godement, 1959). For a Galois algebra
`(K', G)` over `K` and a cocycle `α ∈ Z²(G, K'*)`, the crossed product `L(K', G, α)` is
`K' ⊗ K(G)` with `(x ⊗ eₛ)(y ⊗ eₜ) = x · s(y) · α(s, t) ⊗ eₛₜ` (p. 42). In the proof of the
multiplication theorem 2.6.1 (p. 45), the isomorphism `L(K', G, α⁻¹) ≅ L(K', G, α)°` is said to
come from the map `x ⊗ eₛ ↦ s⁻¹(x) ⊗ eₛ⁻¹`. With that product this map is not multiplicative into
the opposite algebra: it would force `α(t⁻¹, s⁻¹) = (st)⁻¹(α(s, t))⁻¹`. The isomorphism holds
(it is the classical `[α⁻¹] = -[α]`), but the map needs the factor `α(s⁻¹, s)⁻¹` on `eₛ⁻¹`.

The smallest case shows it: `K = ℚ`, `K' = ℚ × ℚ`, `G = ℤ/2` acting by the swap `σ`, and the
normalised cocycle with `α(σ, σ) = c` (a cocycle since `σ(c) = c`). An element `a ⊗ e₁ + b ⊗ e_σ`
is the pair `(a, b)`, and the product is
`(a, b)(a', b') = (a a' + c · b σ(b'), a b' + b σ(a'))`.
In `L(α⁻¹)` one has `e_σ² = 1/2` for `c = 2`, while in `L(α)°` one has `e_σ² = 2`.

**Serre's report, p. 18.** The typescript says that `(a, b)₂ + (a', b')₂` is a quaternion class
if and only if `x₁² - a x₂² - b x₃² = y₁² - a' y₂² - b' y₃²` has a nonzero solution. That
equation always has the nonzero solution `x₁ = y₁ = 1`, other coordinates `0`; the criterion
meant (Albert's) concerns the forms on pure quaternions, without the squares `x₁²`, `y₁²`, that
is the isotropy of `⟨a, b, -ab, -a', -b', a'b'⟩`.

* `σ`, `mulL`: the swap of `ℚ × ℚ` and the product of `L(ℚ × ℚ, ℤ/2, α)` with `α(σ, σ) = c`;
* `mulL_assoc`: this product is associative;
* `typedMap`, `typedMap_not_antimul`: the typed map `x ⊗ eₛ ↦ s⁻¹(x) ⊗ eₛ⁻¹` does not send
  the product of `L(α⁻¹)` to the opposite product of `L(α)` for `c = 2`;
* `correctedMap`, `correctedMap_antimul`: with the factor `α(s⁻¹, s)⁻¹` it does, for every
  `c ≠ 0`;
* `typed_form_trivial_solution`: the typed equation of p. 18 has a nonzero solution over any
  field, whatever `a, b, a', b'`.
-/

namespace Bourbaki.Redaction582Annexes

/-- The nontrivial element of `G = ℤ/2`, acting on `K' = ℚ × ℚ` by swapping the factors. -/
def σ (x : ℚ × ℚ) : ℚ × ℚ := x.swap

/-- The product of `L(ℚ × ℚ, ℤ/2, α)` with `α(σ, σ) = c` (and `α = 1` elsewhere), the pair
`(a, b)` standing for `a ⊗ e₁ + b ⊗ e_σ`. -/
def mulL (c : ℚ) (u v : (ℚ × ℚ) × (ℚ × ℚ)) : (ℚ × ℚ) × (ℚ × ℚ) :=
  (u.1 * v.1 + (c, c) * (u.2 * σ v.2), u.1 * v.2 + u.2 * σ v.1)

/-- The crossed-product law is associative (the constant `c` is a cocycle). -/
theorem mulL_assoc (c : ℚ) (u v w : (ℚ × ℚ) × (ℚ × ℚ)) :
    mulL c (mulL c u v) w = mulL c u (mulL c v w) := by
  obtain ⟨⟨a₁, a₂⟩, b₁, b₂⟩ := u
  obtain ⟨⟨a₁', a₂'⟩, b₁', b₂'⟩ := v
  obtain ⟨⟨a₁'', a₂''⟩, b₁'', b₂''⟩ := w
  simp only [mulL, σ, Prod.swap_prod_mk, Prod.mk_mul_mk, Prod.mk_add_mk, Prod.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

/-- The typed map `x ⊗ eₛ ↦ s⁻¹(x) ⊗ eₛ⁻¹`; here `σ⁻¹ = σ`. -/
def typedMap (u : (ℚ × ℚ) × (ℚ × ℚ)) : (ℚ × ℚ) × (ℚ × ℚ) := (u.1, σ u.2)

/-- For `c = 2`, the typed map from `L(α⁻¹)` does not turn the product into the opposite
product of `L(α)`: on `e_σ · e_σ` one side is `1/2` and the other `2`. -/
theorem typedMap_not_antimul :
    ∃ u v, typedMap (mulL 2⁻¹ u v) ≠ mulL 2 (typedMap v) (typedMap u) := by
  refine ⟨((0, 0), (1, 1)), ((0, 0), (1, 1)), fun h => ?_⟩
  have h1 := congrArg (fun w => w.1.1) h
  norm_num [typedMap, mulL, σ] at h1

/-- The corrected map `x ⊗ eₛ ↦ s⁻¹(x) α(s⁻¹, s)⁻¹ ⊗ eₛ⁻¹`. -/
def correctedMap (c : ℚ) (u : (ℚ × ℚ) × (ℚ × ℚ)) : (ℚ × ℚ) × (ℚ × ℚ) :=
  (u.1, (c⁻¹, c⁻¹) * σ u.2)

/-- The corrected map sends the product of `L(α⁻¹)` to the opposite product of `L(α)`. -/
theorem correctedMap_antimul {c : ℚ} (hc : c ≠ 0) (u v : (ℚ × ℚ) × (ℚ × ℚ)) :
    correctedMap c (mulL c⁻¹ u v) = mulL c (correctedMap c v) (correctedMap c u) := by
  obtain ⟨⟨a₁, a₂⟩, b₁, b₂⟩ := u
  obtain ⟨⟨a₁', a₂'⟩, b₁', b₂'⟩ := v
  simp only [correctedMap, mulL, σ, Prod.swap_prod_mk, Prod.mk_mul_mk, Prod.mk_add_mk,
    Prod.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> field_simp <;> ring

/-- The equation typed on p. 18 has the nonzero solution `x = y = (1, 0, 0)` over any field. -/
theorem typed_form_trivial_solution {K : Type*} [Field K] (a b a' b' : K) :
    ∃ x y : Fin 3 → K, x ≠ 0 ∧
      x 0 ^ 2 - a * x 1 ^ 2 - b * x 2 ^ 2 = y 0 ^ 2 - a' * y 1 ^ 2 - b' * y 2 ^ 2 := by
  refine ⟨![1, 0, 0], ![1, 0, 0], fun h => ?_, by simp⟩
  simpa using congrFun h 0

end Bourbaki.Redaction582Annexes
