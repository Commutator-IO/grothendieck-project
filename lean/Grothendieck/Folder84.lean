import Mathlib

/-!
# Folder 84: the product of quadratic algebras, in split coordinates

The modernised reading `transcripts/84/84.modern.tex` (« Le produit contracté,
deviné », pages 62 to 65; « Le cas χ = 2 : involution et coinvariants »,
pages 79 to 87; « Trace et norme de A₁ ⊗ A₂ sur A₁ * A₂ », pages 98 to 106)
states, for quadratic algebras `Aᵢ` with bases `(1, Uᵢ)`,
`Uᵢ² + bᵢUᵢ + cᵢ = 0`:

> `A = A₁ * A₂ ≅ 𝒪[𝒰]/(𝒰² + b𝒰 + c)` with `b = b₁b₂`,
> `c = c₁b₂² + c₂b₁² − 4c₁c₂`, hence `δ = δ₁δ₂` (`δ = b² − 4c`), and
> `i(𝒰) = 2U₁U₂ + b₁U₂ + b₂U₁` in `A₁ ⊗ A₂`; that `i(𝒰)` satisfies the equation
> is the identity of page 64.
>
> **Proposition (page 85).** `E₁ ⊗ E₂ / Im(σ₁ ⊗ σ₂ − id) → E₁ * E₂` is an
> isomorphism iff `2𝒪 + b₁𝒪 + b₂𝒪 = 𝒪` (in bases and splittings).
>
> **Corollaire (page 86).** Under that condition `A₁ * A₂ ≅ (A₁ ⊗ A₂)^{σ₁⊗σ₂}`,
> and conversely if this stays true after every base change.

These are findings `84-product-quadratic-algebras-formula` and
`84-product-coinvariants-one-etale` of `src/content/findings.ts`. Proving them
says only that the claims hold as stated in coordinates; whether they stand in
the literature is a separate question.

What is formalised, over an arbitrary commutative ring `R`, without dividing
by `2`:

* `identity_page64`, the polynomial identity of page 64, and its consequences
  `root_of_roots` (in any commutative ring) and `tensor_root` (in `A₁ ⊗[R] A₂`
  for any `R`-algebras `A₁`, `A₂` with roots `u₁`, `u₂`), together with the
  algebra map `productToTensor : R[𝒰]/(𝒰² + b𝒰 + c) → A₁ ⊗[R] A₂`,
  `𝒰 ↦ 2U₁U₂ + b₁U₂ + b₂U₁`; `disc_mul` is `δ = δ₁δ₂`, and `four_mul_c` the
  relation `4c = b² − δ` of page 63;
* the proposition of page 85 in coordinates (`coinvariants_bijective_iff`):
  `E₁ ⊗ E₂ = R⁴` in the basis `(e₁⊗e₂, e₁⊗x₂, x₁⊗e₂, x₁⊗x₂)`, `σᵢ` the
  matrix of `x ↦ ψ(x)Tᵢ − x` in the basis `(eᵢ, xᵢ)` and `σ₁ ⊗ σ₂` their
  Kronecker product, `E₁ * E₂ = R²` in the basis `(e₁⊗e₂, x₁*x₂)` and
  `E₁ ⊗ E₂ → E₁ * E₂` the map `(x₁ + u₁) ⊗ (x₂ + u₂) ↦ x₁*x₂ + u₁b₂ + u₂b₁ + 2u₁u₂`
  of page 63; the induced map on the coinvariants is bijective iff
  `Ideal.span {2, b₁, b₂} = ⊤`. Both directions hold over `R` itself, with no
  base change;
* the corollary of page 86 in coordinates: `invariants_of_span_eq_top` (the
  map `A → A₁ ⊗ A₂`, `1 ↦ 1`, `𝒰 ↦ 2U₁U₂ + b₁U₂ + b₂U₁`, is injective with
  image the invariants of `σ₁ ⊗ σ₂`), and `invariants_universally_iff`, the
  converse « after every base change »;
* `invariants_not_iff`: the converse needs the base change. Over `ℤ[X]`, with
  `b₁ = X` and `b₂ = 0`, the map `A → (A₁ ⊗ A₂)^{σ₁⊗σ₂}` is an isomorphism,
  though `2, X, 0` generate a proper ideal.
* the theorem of page 48 in the free case (finding
  `84-two-regular-triplet-classification`): `qalg_iso_iff_moves` (over any `R`,
  `R[U]/(U² + bU + c) ≅ R[V]/(V² + b'V + c')` iff `V = εU + t`),
  `qalg_iso_iff_disc` (if `2` is a non-zero-divisor, iff `δ' = ε²δ` and
  `b' ≡ εb mod 2`), `translates_iff` and `translates_unique` (`L` with its basis
  fixed), `lift_indep` and `exists_of_congr` (every `δ ≡ τ² mod 4` occurs, any
  `R`), `int_disc_iff` and `int_qalg_iso_iff` (over `ℤ`), and
  `two_regular_needed` (over `𝔽₂`, `𝔽₂ × 𝔽₂` and `𝔽₄` share `δ` and `T₀`);
* `χ`-split extensions in coordinates (finding
  `84-chi-trivialised-extension-product`): `isChiSplitting_of`,
  `chiSplitting_eq`, `iso_iff` (morphisms are transvections, `b = b' + χw`),
  `prod_change` and `uProd_cocycle` (pages 129 and 131), `prod_comm`,
  `prod_assoc`, `prod_unit`, `chiRel_mul`, `invertible_iff` and
  `span_eq_top_iff_isUnit` (page 79, `L = 𝒪`), `push_pull`,
  `push_pull_square` and `push_pull_unit_iff` (pages 125 to 169: the comparison
  of pushout and pullback needs and uses `γχ = 2`).
-/

universe u

namespace Grothendieck.Folder84

open Polynomial TensorProduct

/-! ## The formula of pages 63, 64 and 89 -/

section Formula

variable {A : Type*} [CommRing A]

/-- The identity of page 64: with `Qᵢ = uᵢ² + bᵢuᵢ + cᵢ` and
`u = u₁b₂ + u₂b₁ + 2u₁u₂`, `u² + bu + c = b₂²Q₁ + b₁²Q₂ + 4(Q₁Q₂ − c₁Q₂ − c₂Q₁)`
for `b = b₁b₂`, `c = c₁b₂² + c₂b₁² − 4c₁c₂`. -/
theorem identity_page64 (b₁ c₁ b₂ c₂ u₁ u₂ : A) :
    (2 * u₁ * u₂ + b₁ * u₂ + b₂ * u₁) ^ 2 + b₁ * b₂ * (2 * u₁ * u₂ + b₁ * u₂ + b₂ * u₁)
        + (c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂)
      = b₂ ^ 2 * (u₁ ^ 2 + b₁ * u₁ + c₁) + b₁ ^ 2 * (u₂ ^ 2 + b₂ * u₂ + c₂)
        + 4 * ((u₁ ^ 2 + b₁ * u₁ + c₁) * (u₂ ^ 2 + b₂ * u₂ + c₂)
          - c₁ * (u₂ ^ 2 + b₂ * u₂ + c₂) - c₂ * (u₁ ^ 2 + b₁ * u₁ + c₁)) := by
  ring

/-- Pages 64 and 102: if `U₁² + b₁U₁ + c₁ = 0` and `U₂² + b₂U₂ + c₂ = 0` in a
commutative ring, then `𝒰 = 2U₁U₂ + b₁U₂ + b₂U₁` satisfies `𝒰² + b𝒰 + c = 0`
with `b = b₁b₂` and `c = c₁b₂² + c₂b₁² − 4c₁c₂`. -/
theorem root_of_roots {b₁ c₁ b₂ c₂ U₁ U₂ : A}
    (h₁ : U₁ ^ 2 + b₁ * U₁ + c₁ = 0) (h₂ : U₂ ^ 2 + b₂ * U₂ + c₂ = 0) :
    (2 * U₁ * U₂ + b₁ * U₂ + b₂ * U₁) ^ 2 + b₁ * b₂ * (2 * U₁ * U₂ + b₁ * U₂ + b₂ * U₁)
      + (c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂) = 0 := by
  rw [identity_page64, h₁, h₂]; ring

/-- Corollary of page 89: `δ = δ₁δ₂`, where `δ = b² − 4c`. -/
theorem disc_mul (b₁ c₁ b₂ c₂ : A) :
    (b₁ * b₂) ^ 2 - 4 * (c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂)
      = (b₁ ^ 2 - 4 * c₁) * (b₂ ^ 2 - 4 * c₂) := by
  ring

/-- Page 63: the first form of the boxed `c`, `c₁δ₂ + c₂δ₁ + 4c₁c₂`, is the
second, `c₁b₂² + c₂b₁² − 4c₁c₂`. -/
theorem c_two_forms (b₁ c₁ b₂ c₂ : A) :
    c₁ * (b₂ ^ 2 - 4 * c₂) + c₂ * (b₁ ^ 2 - 4 * c₁) + 4 * c₁ * c₂
      = c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂ := by
  ring

variable {R : Type*} [CommRing R] {A₁ A₂ : Type*} [CommRing A₁] [CommRing A₂]
  [Algebra R A₁] [Algebra R A₂]

/-- The element `i(𝒰) = 2U₁U₂ + b₁U₂ + b₂U₁` of `A₁ ⊗[R] A₂`, with `U₁ = u₁ ⊗ 1`
and `U₂ = 1 ⊗ u₂`. -/
noncomputable def iU (b₁ b₂ : R) (u₁ : A₁) (u₂ : A₂) : A₁ ⊗[R] A₂ :=
  2 * (u₁ ⊗ₜ 1) * (1 ⊗ₜ u₂) + algebraMap R _ b₁ * (1 ⊗ₜ u₂) + algebraMap R _ b₂ * (u₁ ⊗ₜ 1)

/-- Page 102, in `A₁ ⊗[R] A₂`: the element `i(𝒰)` satisfies
`𝒰² + b₁b₂𝒰 + (c₁b₂² + c₂b₁² − 4c₁c₂) = 0`. -/
theorem tensor_root {b₁ c₁ b₂ c₂ : R} {u₁ : A₁} {u₂ : A₂}
    (h₁ : u₁ ^ 2 + algebraMap R A₁ b₁ * u₁ + algebraMap R A₁ c₁ = 0)
    (h₂ : u₂ ^ 2 + algebraMap R A₂ b₂ * u₂ + algebraMap R A₂ c₂ = 0) :
    iU b₁ b₂ u₁ u₂ ^ 2 + algebraMap R _ (b₁ * b₂) * iU b₁ b₂ u₁ u₂
      + algebraMap R _ (c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂) = 0 := by
  have e₁ := congrArg (Algebra.TensorProduct.includeLeft (R := R) (S := R) (B := A₂)) h₁
  have e₂ := congrArg (Algebra.TensorProduct.includeRight (R := R) (A := A₁)) h₂
  simp only [map_add, map_mul, map_pow, AlgHom.commutes, map_zero,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply] at e₁ e₂
  have := root_of_roots e₁ e₂
  simp only [iU, map_mul, map_sub, map_add, map_pow, map_ofNat]
  linear_combination this

/-- The quadratic polynomial `𝒰² + b𝒰 + c` of the product. -/
noncomputable def prodPoly (b₁ c₁ b₂ c₂ : R) : R[X] :=
  X ^ 2 + C (b₁ * b₂) * X + C (c₁ * b₂ ^ 2 + c₂ * b₁ ^ 2 - 4 * c₁ * c₂)

/-- Pages 98 to 102: the algebra map `i : R[𝒰]/(𝒰² + b𝒰 + c) → A₁ ⊗[R] A₂`,
`𝒰 ↦ 2U₁U₂ + b₁U₂ + b₂U₁`. -/
noncomputable def productToTensor {b₁ c₁ b₂ c₂ : R} {u₁ : A₁} {u₂ : A₂}
    (h₁ : u₁ ^ 2 + algebraMap R A₁ b₁ * u₁ + algebraMap R A₁ c₁ = 0)
    (h₂ : u₂ ^ 2 + algebraMap R A₂ b₂ * u₂ + algebraMap R A₂ c₂ = 0) :
    AdjoinRoot (prodPoly b₁ c₁ b₂ c₂) →ₐ[R] A₁ ⊗[R] A₂ :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _) (iU b₁ b₂ u₁ u₂) (by
    have := tensor_root h₁ h₂
    simp only [prodPoly, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X]
    simpa using this)

theorem productToTensor_root {b₁ c₁ b₂ c₂ : R} {u₁ : A₁} {u₂ : A₂}
    (h₁ : u₁ ^ 2 + algebraMap R A₁ b₁ * u₁ + algebraMap R A₁ c₁ = 0)
    (h₂ : u₂ ^ 2 + algebraMap R A₂ b₂ * u₂ + algebraMap R A₂ c₂ = 0) :
    productToTensor h₁ h₂ (AdjoinRoot.root _) = iU b₁ b₂ u₁ u₂ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

end Formula

/-! ## The proposition of page 85 and the corollary of page 86, in coordinates -/

section Coordinates

variable {R : Type*} [CommRing R]

/-- The condition `2R + b₁R + b₂R = R`, written with coefficients. -/
theorem span_eq_top_iff (b₁ b₂ : R) :
    Ideal.span {2, b₁, b₂} = ⊤ ↔ ∃ g₀ g₁ g₂ : R, 2 * g₀ + b₁ * g₁ + b₂ * g₂ = 1 := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_insert]
  constructor
  · rintro ⟨a, z, hz, e⟩
    obtain ⟨p, q, hpq⟩ := Ideal.mem_span_pair.1 hz
    exact ⟨a, p, q, by rw [e, ← hpq]; ring⟩
  · rintro ⟨g₀, g₁, g₂, e⟩
    exact ⟨g₀, b₁ * g₁ + b₂ * g₂, Ideal.mem_span_pair.2 ⟨g₁, g₂, by ring⟩, by
      rw [← e]; ring⟩

/-- The matrix of `σᵢ : x ↦ ψ(x)Tᵢ − x` in the basis `(eᵢ, xᵢ)` of `Eᵢ`, where
`Tᵢ = 2xᵢ − bᵢeᵢ`: `σᵢ(eᵢ) = −eᵢ`, `σᵢ(xᵢ) = xᵢ − bᵢeᵢ`. -/
def sigmaE (b : R) : Matrix (Fin 2) (Fin 2) R := !![-1, -b; 0, 1]

/-- `σ₁ ⊗ σ₂` on `E₁ ⊗ E₂`, in the basis `(eᵢ ⊗ eⱼ)` indexed by `Fin 2 × Fin 2`
(`0` for `e`, `1` for `x`). -/
def sigmaTensor (b₁ b₂ : R) : (Fin 2 × Fin 2 → R) →ₗ[R] (Fin 2 × Fin 2 → R) :=
  Matrix.mulVecLin (Matrix.kronecker (sigmaE b₁) (sigmaE b₂))

/-- The map `E₁ ⊗ E₂ → E₁ * E₂` of page 63 in coordinates: the coefficient of
`e₁ ⊗ e₂` in the image is `2a + b₂a' + b₁a''` (from `u₁ ⊗ u₂ ↦ 2u₁u₂`,
`u₁ ⊗ x₂ ↦ u₁b₂`, `x₁ ⊗ u₂ ↦ b₁u₂`), that of `x₁ * x₂` is the coefficient of
`x₁ ⊗ x₂`. -/
def starMap (b₁ b₂ : R) : (Fin 2 × Fin 2 → R) →ₗ[R] (Fin 2 → R) where
  toFun v := ![2 * v (0, 0) + b₂ * v (0, 1) + b₁ * v (1, 0), v (1, 1)]
  map_add' v w := by
    funext i; fin_cases i <;> first | (simp; done) | (simp; ring)
  map_smul' r v := by
    funext i; fin_cases i <;> first | (simp; done) | (simp; ring)

lemma sigmaTensor_apply (b₁ b₂ : R) (v : Fin 2 × Fin 2 → R) :
    sigmaTensor b₁ b₂ v (0, 0) = v (0, 0) + b₂ * v (0, 1) + b₁ * v (1, 0) + b₁ * b₂ * v (1, 1) ∧
    sigmaTensor b₁ b₂ v (0, 1) = -v (0, 1) - b₁ * v (1, 1) ∧
    sigmaTensor b₁ b₂ v (1, 0) = -v (1, 0) - b₂ * v (1, 1) ∧
    sigmaTensor b₁ b₂ v (1, 1) = v (1, 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
      | (simp [sigmaTensor, sigmaE, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; done)
      | (simp [sigmaTensor, sigmaE, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; ring)

/-- Page 83: `E₁ ⊗ E₂ → E₁ * E₂` kills `Im(σ₁ ⊗ σ₂ − id)`. -/
theorem range_le_ker (b₁ b₂ : R) :
    LinearMap.range (sigmaTensor b₁ b₂ - LinearMap.id) ≤ LinearMap.ker (starMap b₁ b₂) := by
  rintro _ ⟨v, rfl⟩
  obtain ⟨h0, h1, h2, h3⟩ := sigmaTensor_apply b₁ b₂ v
  simp only [LinearMap.mem_ker, starMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
    LinearMap.id_apply, Pi.sub_apply, h0, h1, h2, h3]
  funext i; fin_cases i <;> first | (simp; done) | (simp; ring)

/-- The induced map `E₁ ⊗ E₂ / Im(σ₁ ⊗ σ₂ − id) → E₁ * E₂`. -/
noncomputable def coinvMap (b₁ b₂ : R) :
    ((Fin 2 × Fin 2 → R) ⧸ LinearMap.range (sigmaTensor b₁ b₂ - LinearMap.id)) →ₗ[R]
      (Fin 2 → R) :=
  (LinearMap.range (sigmaTensor b₁ b₂ - LinearMap.id)).liftQ (starMap b₁ b₂) (range_le_ker b₁ b₂)

/-- Page 85, the inclusion that needs the condition: if `2R + b₁R + b₂R = R`,
the kernel of `E₁ ⊗ E₂ → E₁ * E₂` is in `Im(σ₁ ⊗ σ₂ − id)`. The preimage is
written with the Koszul relations of the unimodular row `(2, b₂, b₁)`. -/
theorem ker_le_range {b₁ b₂ : R} (h : Ideal.span {2, b₁, b₂} = ⊤) :
    LinearMap.ker (starMap b₁ b₂) ≤ LinearMap.range (sigmaTensor b₁ b₂ - LinearMap.id) := by
  obtain ⟨g₀, g₂, g₁, hg⟩ := (span_eq_top_iff b₁ b₂).1 h
  intro v hv
  have hv0 : 2 * v (0, 0) + b₂ * v (0, 1) + b₁ * v (1, 0) = 0 := by
    simpa [starMap] using congrFun hv 0
  have hv3 : v (1, 1) = 0 := by simpa [starMap] using congrFun hv 1
  set a := v (0, 0)
  set a' := v (0, 1)
  set a'' := v (1, 0)
  -- Koszul coefficients for `f = (2, b₂, b₁)`, `g = (g₀, g₁, g₂)`
  set c01 := g₁ * a - g₀ * a'
  set c02 := g₂ * a - g₀ * a''
  set c12 := g₂ * a' - g₁ * a''
  let w : Fin 2 × Fin 2 → R := fun p =>
    if p = (0, 1) then c01 - b₁ * c12 else if p = (1, 0) then c02 else if p = (1, 1) then c12
    else 0
  refine ⟨w, ?_⟩
  obtain ⟨h0, h1, h2, h3⟩ := sigmaTensor_apply b₁ b₂ w
  ext ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · simp only [LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply]
    simp only [Fin.zero_eta, Fin.isValue] at h0 ⊢
    rw [h0]; simp [w]
    linear_combination a * hg - g₀ * hv0
  · simp only [LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply]
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at h1 ⊢
    rw [h1]; simp [w]
    linear_combination a' * hg - g₁ * hv0
  · simp only [LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply]
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at h2 ⊢
    rw [h2]; simp [w]
    linear_combination a'' * hg - g₂ * hv0
  · simp only [LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply]
    simp only [Fin.isValue, Fin.mk_one] at h3 ⊢
    rw [h3]; simp [hv3]

/-- **Proposition (page 85), in coordinates.** The map
`E₁ ⊗ E₂ / Im(σ₁ ⊗ σ₂ − id) → E₁ * E₂` is bijective if and only if
`2R + b₁R + b₂R = R`. -/
theorem coinvariants_bijective_iff (b₁ b₂ : R) :
    Function.Bijective (coinvMap b₁ b₂) ↔ Ideal.span {2, b₁, b₂} = ⊤ := by
  constructor
  · rintro ⟨-, hs⟩
    obtain ⟨q, hq⟩ := hs ![1, 0]
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have e := congrFun hq 0
    simp only [coinvMap, Submodule.liftQ_apply, starMap, LinearMap.coe_mk, AddHom.coe_mk] at e
    simp only [Fin.isValue, Matrix.cons_val_zero] at e
    exact (span_eq_top_iff b₁ b₂).2 ⟨v (0, 0), v (1, 0), v (0, 1), by rw [← e]; ring⟩
  · intro h
    obtain ⟨g₀, g₁, g₂, hg⟩ := (span_eq_top_iff b₁ b₂).1 h
    refine ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ (ker_le_range h)
    · intro y
      refine ⟨Submodule.Quotient.mk (fun p =>
        if p = (0, 0) then y 0 * g₀ else if p = (0, 1) then y 0 * g₂
        else if p = (1, 0) then y 0 * g₁ else y 1), ?_⟩
      simp only [coinvMap, Submodule.liftQ_apply, starMap, LinearMap.coe_mk, AddHom.coe_mk]
      ext i; fin_cases i
      · simp; linear_combination y 0 * hg
      · simp

/-- The map `i : A → A₁ ⊗ A₂` in coordinates: `A` in the basis `(1, 𝒰)`,
`A₁ ⊗ A₂` in the basis `(1, U₁, U₂, U₁U₂)`, indexed by `Fin 2 × Fin 2`
(`(1, 0)` for `U₁`, `(0, 1)` for `U₂`); `1 ↦ 1`, `𝒰 ↦ 2U₁U₂ + b₁U₂ + b₂U₁`. -/
def iMap (b₁ b₂ : R) : (Fin 2 → R) →ₗ[R] (Fin 2 × Fin 2 → R) where
  toFun v p :=
    if p = (0, 0) then v 0 else if p = (1, 0) then b₂ * v 1
    else if p = (0, 1) then b₁ * v 1 else 2 * v 1
  map_add' v w := by
    ext p; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' r v := by
    ext p; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- The matrix of the conjugation `σᵢ(x) = Tr(x) − x` of `Aᵢ` in the basis
`(1, Uᵢ)`: `σᵢ(1) = 1`, `σᵢ(Uᵢ) = −bᵢ − Uᵢ`. -/
def sigmaA (b : R) : Matrix (Fin 2) (Fin 2) R := !![1, -b; 0, -1]

/-- `σ₁ ⊗ σ₂` on `A₁ ⊗ A₂`. -/
def sigmaATensor (b₁ b₂ : R) : (Fin 2 × Fin 2 → R) →ₗ[R] (Fin 2 × Fin 2 → R) :=
  Matrix.mulVecLin (Matrix.kronecker (sigmaA b₁) (sigmaA b₂))

lemma sigmaATensor_apply (b₁ b₂ : R) (v : Fin 2 × Fin 2 → R) :
    sigmaATensor b₁ b₂ v (0, 0) = v (0, 0) - b₂ * v (0, 1) - b₁ * v (1, 0) + b₁ * b₂ * v (1, 1) ∧
    sigmaATensor b₁ b₂ v (0, 1) = -v (0, 1) + b₁ * v (1, 1) ∧
    sigmaATensor b₁ b₂ v (1, 0) = -v (1, 0) + b₂ * v (1, 1) ∧
    sigmaATensor b₁ b₂ v (1, 1) = v (1, 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
      | (simp [sigmaATensor, sigmaA, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; done)
      | (simp [sigmaATensor, sigmaA, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; ring)

/-- `A → (A₁ ⊗ A₂)^{σ₁⊗σ₂}` is an isomorphism: `i` is injective and its image is
the submodule of invariants of `σ₁ ⊗ σ₂`. -/
def InvariantsIso (b₁ b₂ : R) : Prop :=
  Function.Injective (iMap b₁ b₂) ∧
    LinearMap.range (iMap b₁ b₂) = LinearMap.ker (sigmaATensor b₁ b₂ - LinearMap.id)

lemma mem_invariants_iff {b₁ b₂ : R} (v : Fin 2 × Fin 2 → R) :
    v ∈ LinearMap.ker (sigmaATensor b₁ b₂ - LinearMap.id) ↔
      -b₂ * v (0, 1) - b₁ * v (1, 0) + b₁ * b₂ * v (1, 1) = 0 ∧
      2 * v (0, 1) = b₁ * v (1, 1) ∧ 2 * v (1, 0) = b₂ * v (1, 1) := by
  obtain ⟨h0, h1, h2, h3⟩ := sigmaATensor_apply b₁ b₂ v
  rw [LinearMap.mem_ker]
  constructor
  · intro hv
    have e0 := congrFun hv (0, 0)
    have e1 := congrFun hv (0, 1)
    have e2 := congrFun hv (1, 0)
    simp only [LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply, Pi.zero_apply,
      h0, h1, h2] at e0 e1 e2
    refine ⟨by linear_combination e0, by linear_combination -e1, by linear_combination -e2⟩
  · rintro ⟨e0, e1, e2⟩
    ext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp only [LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply, Pi.zero_apply] <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at h0 h1 h2 h3 ⊢
    · rw [h0]; linear_combination e0
    · rw [h1]; linear_combination -e1
    · rw [h2]; linear_combination -e2
    · rw [h3]; ring

lemma iMap_apply (b₁ b₂ : R) (v : Fin 2 → R) :
    iMap b₁ b₂ v (0, 0) = v 0 ∧ iMap b₁ b₂ v (1, 0) = b₂ * v 1 ∧
      iMap b₁ b₂ v (0, 1) = b₁ * v 1 ∧ iMap b₁ b₂ v (1, 1) = 2 * v 1 := by
  simp [iMap]

/-- **Corollaire (page 86), in coordinates.** If `2R + b₁R + b₂R = R`, then
`A → A₁ ⊗ A₂` is injective with image `(A₁ ⊗ A₂)^{σ₁⊗σ₂}`. -/
theorem invariants_of_span_eq_top {b₁ b₂ : R} (h : Ideal.span {2, b₁, b₂} = ⊤) :
    InvariantsIso b₁ b₂ := by
  obtain ⟨g₀, g₁, g₂, hg⟩ := (span_eq_top_iff b₁ b₂).1 h
  refine ⟨?_, ?_⟩
  · intro v w hvw
    have k := fun p => congrFun hvw p
    obtain ⟨a0, a1, a2, a3⟩ := iMap_apply b₁ b₂ v
    obtain ⟨b0, b1, b2, b3⟩ := iMap_apply b₁ b₂ w
    have e0 := k (0, 0); have e1 := k (1, 0); have e2 := k (0, 1); have e3 := k (1, 1)
    rw [a0, b0] at e0; rw [a1, b1] at e1; rw [a2, b2] at e2; rw [a3, b3] at e3
    ext i; fin_cases i
    · exact e0
    · simp only [Fin.mk_one, Fin.isValue]
      linear_combination (w 1 - v 1) * hg + g₀ * e3 + g₁ * e2 + g₂ * e1
  · apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨a0, a1, a2, a3⟩ := iMap_apply b₁ b₂ v
      rw [mem_invariants_iff, a1, a2, a3]
      refine ⟨by ring, by ring, by ring⟩
    · intro v hv
      obtain ⟨e0, e1, e2⟩ := (mem_invariants_iff v).1 hv
      refine ⟨![v (0, 0), v (1, 1) * g₀ + v (0, 1) * g₁ + v (1, 0) * g₂], ?_⟩
      obtain ⟨a0, a1, a2, a3⟩ := iMap_apply b₁ b₂ ![v (0, 0), v (1, 1) * g₀ + v (0, 1) * g₁ + v (1, 0) * g₂]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 a2 a3
      have key : b₁ * v (1, 0) = b₂ * v (0, 1) := by
        linear_combination -e0 - b₂ * e1
      ext ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
      · exact a0
      · rw [a2]; linear_combination v (0, 1) * hg - g₀ * e1 + g₂ * key
      · rw [a1]; linear_combination v (1, 0) * hg - g₀ * e2 - g₁ * key
      · rw [a3]; linear_combination v (1, 1) * hg + g₁ * e1 + g₂ * e2

/-- **Corollaire (page 86), the converse « après tout changement de base ».**
`A → (A₁ ⊗ A₂)^{σ₁⊗σ₂}` is an isomorphism after every base change `R → S` if
and only if `2R + b₁R + b₂R = R`. Base change to `R/(2, b₁, b₂)` is enough. -/
theorem invariants_universally_iff {R : Type u} [CommRing R] (b₁ b₂ : R) :
    (∀ (S : Type u) [CommRing S] (f : R →+* S), InvariantsIso (f b₁) (f b₂)) ↔
      Ideal.span {2, b₁, b₂} = ⊤ := by
  constructor
  · intro H
    by_contra hI
    set I := Ideal.span ({2, b₁, b₂} : Set R)
    have hS : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
    have h2 : (Ideal.Quotient.mk I) 2 = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
    have hb₁ : (Ideal.Quotient.mk I) b₁ = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
    have hb₂ : (Ideal.Quotient.mk I) b₂ = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
    obtain ⟨-, hr⟩ := H (R ⧸ I) (Ideal.Quotient.mk I)
    rw [hb₁, hb₂] at hr
    -- the invariant `U₂` is not in the image
    have hmem : (fun p => if p = ((0 : Fin 2), (1 : Fin 2)) then (1 : R ⧸ I) else 0) ∈
        LinearMap.ker (sigmaATensor (0 : R ⧸ I) 0 - LinearMap.id) := by
      rw [mem_invariants_iff]
      have : (2 : R ⧸ I) = 0 := (map_ofNat (Ideal.Quotient.mk I) 2).symm.trans h2
      simp [this]
    rw [← hr] at hmem
    obtain ⟨v, hv⟩ := hmem
    have e := congrFun hv (0, 1)
    obtain ⟨-, -, a2, -⟩ := iMap_apply (0 : R ⧸ I) 0 v
    rw [a2] at e
    simp at e
  · intro h S _ f
    apply invariants_of_span_eq_top
    obtain ⟨g₀, g₁, g₂, hg⟩ := (span_eq_top_iff b₁ b₂).1 h
    exact (span_eq_top_iff _ _).2 ⟨f g₀, f g₁, f g₂, by
      rw [← map_one f, ← hg]; simp only [map_add, map_mul, map_ofNat]⟩

/-- The converse of page 86 needs the base change: over `ℤ[X]`, with `b₁ = X`
and `b₂ = 0`, `A → (A₁ ⊗ A₂)^{σ₁⊗σ₂}` is an isomorphism, while `2`, `X`, `0`
generate the proper ideal `(2, X)`. -/
lemma two_eq_C : (2 : ℤ[X]) = C 2 := by simp

theorem invariants_not_iff :
    InvariantsIso (X : ℤ[X]) 0 ∧ Ideal.span {(2 : ℤ[X]), X, 0} ≠ ⊤ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v w hvw
    obtain ⟨a0, -, -, a3⟩ := iMap_apply (X : ℤ[X]) 0 v
    obtain ⟨b0, -, -, b3⟩ := iMap_apply (X : ℤ[X]) 0 w
    have e0 := congrFun hvw (0, 0); have e3 := congrFun hvw (1, 1)
    rw [a0, b0] at e0; rw [a3, b3] at e3
    funext i; fin_cases i
    · exact e0
    · exact mul_left_cancel₀ (two_ne_zero : (2 : ℤ[X]) ≠ 0) e3
  · apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨-, a1, a2, a3⟩ := iMap_apply (X : ℤ[X]) 0 v
      rw [mem_invariants_iff, a1, a2, a3]
      refine ⟨by ring, by ring, by ring⟩
    · intro v hv
      obtain ⟨-, e1, e2⟩ := (mem_invariants_iff v).1 hv
      -- `2 v(1,0) = 0`, so `v(1,0) = 0`; `2 v(0,1) = X v(1,1)`, so `2 ∣ v(1,1)`
      have z : v (1, 0) = 0 := by
        rw [zero_mul] at e2; exact (mul_eq_zero.1 e2).resolve_left two_ne_zero
      have hp : Prime (2 : ℤ[X]) := by
        simpa using (Polynomial.prime_C_iff (r := (2 : ℤ))).2 Int.prime_two
      have hd : (2 : ℤ[X]) ∣ X * v (1, 1) := ⟨v (0, 1), e1.symm⟩
      have h2X : ¬ (2 : ℤ[X]) ∣ X := by
        rintro ⟨q, hq⟩
        have := congrArg (fun p => p.coeff 1) hq
        simp only [coeff_X_one] at this
        rw [two_eq_C, coeff_C_mul] at this
        omega
      obtain ⟨μ, hμ⟩ := (hp.dvd_or_dvd hd).resolve_left h2X
      refine ⟨![v (0, 0), μ], ?_⟩
      obtain ⟨a0, a1, a2, a3⟩ := iMap_apply (X : ℤ[X]) 0 ![v (0, 0), μ]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 a2 a3
      funext p; obtain ⟨i, j⟩ := p
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
      · exact a0
      · rw [a2]
        apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ[X]) ≠ 0)
        rw [e1, hμ]; ring
      · simp [a1, z]
      · rw [a3, hμ]
  · intro htop
    obtain ⟨g₀, g₁, g₂, hg⟩ := (span_eq_top_iff (X : ℤ[X]) 0).1 htop
    rw [two_eq_C] at hg
    have := congrArg (fun p : ℤ[X] => p.coeff 0) hg
    simp only [coeff_add, coeff_C_mul, coeff_X_mul_zero, zero_mul, add_zero,
      coeff_one_zero] at this
    omega

end Coordinates

/-! ## The theorem of page 48 in the free case: quadratic algebras and `(δ, T₀)` -/

section TwoRegular

variable {R : Type*} [CommRing R]

/-- The polynomial `U² + bU + c`. -/
noncomputable def qpoly (b c : R) : R[X] := X ^ 2 + C b * X + C c

lemma qpoly_monic (b c : R) : (qpoly b c).Monic := by
  unfold qpoly; monicity!

lemma qpoly_natDegree [Nontrivial R] (b c : R) : (qpoly b c).natDegree = 2 := by
  unfold qpoly; compute_degree!

lemma qpoly_eval₂ {S : Type*} [CommRing S] (f : R →+* S) (x : S) (b c : R) :
    (qpoly b c).eval₂ f x = x ^ 2 + f b * x + f c := by
  simp [qpoly]

/-- The quadratic algebra `R[U]/(U² + bU + c)`. -/
abbrev QAlg (b c : R) := AdjoinRoot (qpoly b c)

lemma root_sq (b c : R) :
    AdjoinRoot.root (qpoly b c) ^ 2 + algebraMap R (QAlg b c) b * AdjoinRoot.root _
      + algebraMap R (QAlg b c) c = 0 := by
  have : AdjoinRoot.mk (qpoly b c) (X ^ 2 + C b * X + C c) = 0 := AdjoinRoot.mk_self
  simpa using this

/-- `(1, U)` is free in `R[U]/(U² + bU + c)`. -/
lemma coords_zero {b c a e : R}
    (h : algebraMap R (QAlg b c) a + algebraMap R (QAlg b c) e * AdjoinRoot.root _ = 0) :
    a = 0 ∧ e = 0 := by
  have hm : AdjoinRoot.mk (qpoly b c) (C e * X + C a) = 0 := by
    rw [← h]; simp [add_comm]
  rw [AdjoinRoot.mk_eq_zero] at hm
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  by_cases hp : C e * X + C a = 0
  · have h0 := congrArg (coeff · 0) hp
    have h1 := congrArg (coeff · 1) hp
    simp at h0 h1
    exact ⟨h0, h1⟩
  · exfalso
    refine (qpoly_monic b c).not_dvd_of_natDegree_lt hp ?_ hm
    rw [qpoly_natDegree]
    exact lt_of_le_of_lt natDegree_linear_le (by norm_num)

/-- `(1, U)` generates `R[U]/(U² + bU + c)`. -/
lemma coords_exist {b c : R} (y : QAlg b c) :
    ∃ a e : R, y = algebraMap R _ a + algebraMap R _ e * AdjoinRoot.root _ := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have h10 : (1 : R) = 0 := Subsingleton.elim _ _
    refine ⟨0, 0, ?_⟩
    have : (1 : QAlg b c) = 0 := by rw [← map_one (algebraMap R (QAlg b c)), h10, map_zero]
    rw [← mul_one y, this]; simp
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  have hm := qpoly_monic b c
  have h1 : qpoly b c ≠ 1 := by
    intro h; have := congrArg natDegree h; rw [qpoly_natDegree] at this; simp at this
  have hq : (p %ₘ qpoly b c).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt p hm h1
    rw [qpoly_natDegree] at this; omega
  refine ⟨(p %ₘ qpoly b c).coeff 0, (p %ₘ qpoly b c).coeff 1, ?_⟩
  have e : AdjoinRoot.mk (qpoly b c) p = AdjoinRoot.mk (qpoly b c) (p %ₘ qpoly b c) := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨p /ₘ qpoly b c, by
      have := modByMonic_add_div p (qpoly b c); linear_combination -this⟩
  rw [e, eq_X_add_C_of_natDegree_le_one hq]
  simp [add_comm]

/-- The change of variables `V = εU + t` of the quadratic data:
`(b, c) ↦ (εb − 2t, ε²c − εbt + t²)`. -/
def Moves (b c b' c' : R) : Prop :=
  ∃ (ε : Rˣ) (t : R), b' = ε * b - 2 * t ∧ c' = ε ^ 2 * c - ε * b * t + t ^ 2

/-- If `(b', c')` comes from `(b, c)` by `V = εU + t`, the algebras are isomorphic. -/
noncomputable def movesHom {b c b' c' : R} (ε : Rˣ) (t : R)
    (hb : b' = ε * b - 2 * t) (hc : c' = ε ^ 2 * c - ε * b * t + t ^ 2) :
    QAlg b' c' →ₐ[R] QAlg b c :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _)
    (algebraMap R _ (ε : R) * AdjoinRoot.root _ + algebraMap R _ t) (by
      have r := root_sq b c
      show (qpoly b' c').eval₂ (algebraMap R (QAlg b c)) _ = 0
      rw [qpoly_eval₂, hb, hc]
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
      linear_combination (algebraMap R (QAlg b c) (ε : R)) ^ 2 * r)

lemma moves_symm {b c b' c' : R} (ε : Rˣ) (t : R)
    (hb : b' = ε * b - 2 * t) (hc : c' = ε ^ 2 * c - ε * b * t + t ^ 2) :
    b = ((ε⁻¹ : Rˣ) : R) * b' - 2 * (-((ε⁻¹ : Rˣ) : R) * t) ∧
      c = ((ε⁻¹ : Rˣ) : R) ^ 2 * c' - ((ε⁻¹ : Rˣ) : R) * b' * (-((ε⁻¹ : Rˣ) : R) * t)
        + (-((ε⁻¹ : Rˣ) : R) * t) ^ 2 := by
  have u : ((ε⁻¹ : Rˣ) : R) * ε = 1 := by simp
  constructor
  · rw [hb]; linear_combination (-b) * u
  · rw [hc, hb]; linear_combination (-c * (((ε⁻¹ : Rˣ) : R) * ε + 1)) * u

/-- **The free case of the classification, any base.** `R[U]/(U² + bU + c)` and
`R[V]/(V² + b'V + c')` are isomorphic `R`-algebras if and only if
`(b', c')` comes from `(b, c)` by a change of variables `V = εU + t`,
`ε` a unit. -/
theorem qalg_iso_iff_moves (b c b' c' : R) :
    Nonempty (QAlg b c ≃ₐ[R] QAlg b' c') ↔ Moves b c b' c' := by
  constructor
  · rintro ⟨φ⟩
    obtain ⟨t, ε, hV⟩ := coords_exist (φ.symm (AdjoinRoot.root (qpoly b' c')))
    obtain ⟨s, η, hU⟩ := coords_exist (φ (AdjoinRoot.root (qpoly b c)))
    -- `ηε = 1`
    have hηε : η * ε = 1 := by
      have e := φ.symm_apply_apply (AdjoinRoot.root (qpoly b c))
      rw [hU, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hV] at e
      have : algebraMap R (QAlg b c) (s + η * t) + algebraMap R (QAlg b c) (η * ε - 1)
          * AdjoinRoot.root _ = 0 := by
        simp only [map_add, map_mul, map_sub, map_one]; linear_combination e
      have := (coords_zero this).2
      linear_combination this
    have key := congrArg φ.symm (root_sq b' c')
    simp only [map_add, map_mul, map_pow, AlgEquiv.commutes, map_zero, hV] at key
    have r := root_sq b c
    have : algebraMap R (QAlg b c) (t ^ 2 + b' * t + c' - ε ^ 2 * c)
        + algebraMap R (QAlg b c) (2 * t * ε + b' * ε - ε ^ 2 * b) * AdjoinRoot.root _ = 0 := by
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
      linear_combination key - (algebraMap R (QAlg b c) ε) ^ 2 * r
    obtain ⟨h0, h1⟩ := coords_zero this
    have hb' : b' = ε * b - 2 * t := by
      linear_combination η * h1 - (2 * t + b' - ε * b) * hηε
    refine ⟨Units.mkOfMulEqOne ε η (by rw [mul_comm]; exact hηε), t, hb', ?_⟩
    simp only [Units.val_mkOfMulEqOne]
    linear_combination h0 - t * hb'
  · rintro ⟨ε, t, hb, hc⟩
    obtain ⟨hb₁, hc₁⟩ := moves_symm ε t hb hc
    refine ⟨AlgEquiv.ofAlgHom (movesHom _ _ hb₁ hc₁) (movesHom ε t hb hc) ?_ ?_⟩
    · apply AdjoinRoot.algHom_ext
      simp only [movesHom, AlgHom.coe_comp, Function.comp_apply, AdjoinRoot.liftAlgHom_root,
        map_add, map_mul, AlgHom.commutes, AlgHom.id_apply]
      rw [← sub_eq_zero]
      have u : ((ε⁻¹ : Rˣ) : R) * ε = 1 := by simp
      have := congrArg (algebraMap R (QAlg b' c')) u
      simp only [map_mul, map_one] at this
      simp only [map_neg]
      linear_combination (AdjoinRoot.root (qpoly b' c') - algebraMap R _ t) * this
    · apply AdjoinRoot.algHom_ext
      simp only [movesHom, AlgHom.coe_comp, Function.comp_apply, AdjoinRoot.liftAlgHom_root,
        map_add, map_mul, AlgHom.commutes, AlgHom.id_apply]
      rw [← sub_eq_zero]
      have u : (ε : R) * ((ε⁻¹ : Rˣ) : R) = 1 := by simp
      have := congrArg (algebraMap R (QAlg b c)) u
      simp only [map_mul, map_one] at this
      simp only [map_neg]
      linear_combination AdjoinRoot.root (qpoly b c) * this

/-- The discriminant `δ = b² − 4c`. -/
def disc (b c : R) : R := b ^ 2 - 4 * c

/-- Page 47: `δ ≡ b² (mod 4)`, over any base. -/
theorem disc_congr (b c : R) : b ^ 2 - disc b c = 4 * c := by unfold disc; ring

/-- Page 47: the congruence `T₀² ≡ δ (mod 4)` does not depend on the lift `τ` of
`T₀ ∈ R/2R`, since `(τ + 2a)² ≡ τ² (mod 4)`. -/
theorem lift_indep (τ a δ : R) (h : ∃ k, τ ^ 2 - δ = 4 * k) :
    ∃ k, (τ + 2 * a) ^ 2 - δ = 4 * k := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + a * τ + a ^ 2, by linear_combination hk⟩

/-- Under `V = εU + t`, `δ' = ε²δ` and `b' ≡ εb (mod 2)`, over any base. -/
theorem moves_invariants {b c b' c' : R} (h : Moves b c b' c') :
    ∃ ε : Rˣ, disc b' c' = (ε : R) ^ 2 * disc b c ∧ ∃ s, b' = ε * b + 2 * s := by
  obtain ⟨ε, t, hb, hc⟩ := h
  exact ⟨ε, by rw [disc, disc, hb, hc]; ring, -t, by rw [hb]; ring⟩

lemma cancel_four (h2 : ∀ x : R, 2 * x = 0 → x = 0) {x y : R} (h : 4 * x = 4 * y) : x = y := by
  rw [← sub_eq_zero]
  apply h2; apply h2
  linear_combination h

/-- **Théorème (page 48), the free affine case.** If `2` is a non-zero-divisor
in `R`, `(b, c)` and `(b', c')` differ by a change of variables `V = εU + t`
if and only if `δ' = ε²δ` and `b' ≡ εb (mod 2)` for some unit `ε`. -/
theorem moves_iff_disc (h2 : ∀ x : R, 2 * x = 0 → x = 0) (b c b' c' : R) :
    Moves b c b' c' ↔
      ∃ ε : Rˣ, disc b' c' = (ε : R) ^ 2 * disc b c ∧ ∃ s, b' = ε * b + 2 * s := by
  refine ⟨moves_invariants, ?_⟩
  rintro ⟨ε, hd, s, hs⟩
  refine ⟨ε, -s, by rw [hs]; ring, cancel_four h2 ?_⟩
  unfold disc at hd
  rw [hs] at hd
  linear_combination -hd

/-- The isomorphism classes of free quadratic algebras over `R`, `2` regular, are
classified by `(δ, b mod 2)` up to `(ε²δ, εb)`. -/
theorem qalg_iso_iff_disc (h2 : ∀ x : R, 2 * x = 0 → x = 0) (b c b' c' : R) :
    Nonempty (QAlg b c ≃ₐ[R] QAlg b' c') ↔
      ∃ ε : Rˣ, disc b' c' = (ε : R) ^ 2 * disc b c ∧ ∃ s, b' = ε * b + 2 * s := by
  rw [qalg_iso_iff_moves, moves_iff_disc h2]

/-- With `L` and its basis fixed (`ε = 1`), the translations `V = U + t`. -/
def Translates (b c b' c' : R) (t : R) : Prop := b' = b - 2 * t ∧ c' = c - b * t + t ^ 2

/-- **Théorème (page 48), with `L` trivialised.** If `2` is regular, a
translation from `(b, c)` to `(b', c')` exists iff `δ' = δ` and
`b' ≡ b (mod 2)`, and it is unique: the groupoid of free quadratic algebras with
`L = R` is equivalent to the discrete set of pairs `(δ, T₀)`. -/
theorem translates_iff (h2 : ∀ x : R, 2 * x = 0 → x = 0) (b c b' c' : R) :
    (∃ t, Translates b c b' c' t) ↔ disc b' c' = disc b c ∧ ∃ s, b' = b + 2 * s := by
  constructor
  · rintro ⟨t, hb, hc⟩
    exact ⟨by rw [disc, disc, hb, hc]; ring, -t, by rw [hb]; ring⟩
  · rintro ⟨hd, s, hs⟩
    refine ⟨-s, by rw [hs]; ring, cancel_four h2 ?_⟩
    unfold disc at hd; rw [hs] at hd
    linear_combination -hd

theorem translates_unique (h2 : ∀ x : R, 2 * x = 0 → x = 0) {b c b' c' t t' : R}
    (h : Translates b c b' c' t) (h' : Translates b c b' c' t') : t = t' := by
  rw [← sub_eq_zero]; apply h2; linear_combination h.1 - h'.1

/-- **Théorème (page 48), essential surjectivity.** Over any base, every `δ` with
a `τ` such that `τ² ≡ δ (mod 4)` is the discriminant of `(τ, c)` for some `c`;
conversely `b² ≡ δ (mod 4)` for every `(b, c)`. -/
theorem exists_of_congr (δ τ : R) (h : ∃ k, τ ^ 2 - δ = 4 * k) :
    ∃ c, disc τ c = δ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by unfold disc; linear_combination hk⟩

/-- Page 53, over `ℤ`: the discriminants are the integers `≡ 0, 1 (mod 4)`. -/
theorem int_disc_iff (δ : ℤ) : (∃ b c : ℤ, disc b c = δ) ↔ δ % 4 = 0 ∨ δ % 4 = 1 := by
  constructor
  · rintro ⟨b, c, rfl⟩
    rcases Int.even_or_odd b with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have e : disc (k + k) c = 4 * (k ^ 2 - c) := by unfold disc; ring
      rw [e]; generalize k ^ 2 - c = m; omega
    · have e : disc (2 * k + 1) c = 4 * (k ^ 2 + k - c) + 1 := by unfold disc; ring
      rw [e]; generalize k ^ 2 + k - c = m; omega
  · rintro (h | h)
    · exact ⟨0, -(δ / 4), by unfold disc; omega⟩
    · exact ⟨1, (1 - δ) / 4, by unfold disc; omega⟩

/-- Page 53, over `ℤ`: `T₀` is determined by `δ`, and two quadratic rings
`ℤ[U]/(U² + bU + c)` are isomorphic iff they have the same discriminant. -/
theorem int_qalg_iso_iff (b c b' c' : ℤ) :
    Nonempty (QAlg b c ≃ₐ[ℤ] QAlg b' c') ↔ disc b c = disc b' c' := by
  have h2 : ∀ x : ℤ, 2 * x = 0 → x = 0 := fun x hx => by omega
  rw [qalg_iso_iff_disc h2]
  constructor
  · rintro ⟨ε, hd, -⟩
    have : (ε : ℤ) ^ 2 = 1 := by rcases Int.units_eq_one_or ε with h | h <;> simp [h]
    rw [hd, this, one_mul]
  · intro hd
    refine ⟨1, by rw [hd]; simp, ?_⟩
    have hev : Even ((b' - b) * (b' + b)) := ⟨2 * (c' - c), by
      unfold disc at hd; linear_combination -hd⟩
    have hsub : Even (b' - b) := by
      rcases Int.even_mul.1 hev with h | h
      · exact h
      · rwa [Int.even_sub, ← Int.even_add]
    obtain ⟨s, hs⟩ := hsub
    exact ⟨s, by simp; linear_combination hs⟩

/-- The hypothesis « 2 regular » is needed: over `𝔽₂`, `(b, c) = (1, 0)` and
`(1, 1)` have the same `δ = 1` and the same `b mod 2`, but `𝔽₂[U]/(U² + U)` and
`𝔽₂[U]/(U² + U + 1)` (that is `𝔽₂ × 𝔽₂` and `𝔽₄`) are not isomorphic. -/
theorem two_regular_needed :
    disc (1 : ZMod 2) 0 = disc (1 : ZMod 2) 1 ∧
      ¬ Nonempty (QAlg (1 : ZMod 2) 0 ≃ₐ[ZMod 2] QAlg (1 : ZMod 2) 1) := by
  refine ⟨by unfold disc; decide, ?_⟩
  rw [qalg_iso_iff_moves]
  rintro ⟨ε, t, -, hc⟩
  have hε : (ε : ZMod 2) = 1 := by
    clear hc
    have := ε.ne_zero
    generalize (ε : ZMod 2) = e at this ⊢
    fin_cases e <;> first | rfl | exact (this rfl).elim
  rw [hε] at hc
  fin_cases t <;> revert hc <;> decide

end TwoRegular

/-! ## `χ`-split extensions and their product, in coordinates -/

section ChiSplit

variable {R : Type*} [CommRing R] (χ : R)
variable {M L : Type*} [AddCommGroup M] [Module R M] [AddCommGroup L] [Module R L]

/-- The `χ`-retraction of `E = M ⊕ L` given by `b : M → L`:
`π(η, ξ) = b(η) + χξ` (pages 77 and 129). -/
def piOf (b : M →ₗ[R] L) : M × L →ₗ[R] L :=
  b ∘ₗ LinearMap.fst R M L + χ • LinearMap.snd R M L

/-- The `χ`-section `ϖ(η) = (χη, −b(η))`. -/
def varpiOf (b : M →ₗ[R] L) : M →ₗ[R] M × L :=
  LinearMap.prod (χ • LinearMap.id) (-b)

/-- A `χ`-scindage `(π, ϖ)` of `0 → L → M ⊕ L → M → 0` (page 169):
`πα = χ`, `ψϖ = χ`, `απ + ϖψ = χ`. -/
structure IsChiSplitting (π : M × L →ₗ[R] L) (ϖ : M →ₗ[R] M × L) : Prop where
  retr : π ∘ₗ LinearMap.inr R M L = χ • LinearMap.id
  sect : LinearMap.fst R M L ∘ₗ ϖ = χ • LinearMap.id
  sum : LinearMap.inr R M L ∘ₗ π + ϖ ∘ₗ LinearMap.fst R M L = χ • LinearMap.id

theorem isChiSplitting_of (b : M →ₗ[R] L) : IsChiSplitting χ (piOf χ b) (varpiOf χ b) where
  retr := by ext; simp [piOf]
  sect := by ext; simp [varpiOf]
  sum := by
    apply LinearMap.prod_ext <;> ext <;> simp [piOf, varpiOf]

/-- Page 129: on a split extension, a `χ`-scindage is determined by
`b = π|_M : M → L`, and it is `(piOf b, varpiOf b)`. -/
theorem chiSplitting_eq {π : M × L →ₗ[R] L} {ϖ : M →ₗ[R] M × L}
    (h : IsChiSplitting χ π ϖ) :
    π = piOf χ (π ∘ₗ LinearMap.inl R M L) ∧ ϖ = varpiOf χ (π ∘ₗ LinearMap.inl R M L) := by
  constructor
  · apply LinearMap.prod_ext
    · ext; simp [piOf]
    · ext ξ
      have := LinearMap.congr_fun h.retr ξ
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.inr_apply] at this
      simp [piOf]
      rw [show ((0 : M), (0 : L)) = 0 from rfl, map_zero, zero_add, this]
  · ext η
    · have := LinearMap.congr_fun h.sect η
      simpa [varpiOf] using this
    · have := congrArg Prod.snd (LinearMap.congr_fun h.sum (η, 0))
      simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.inr_apply, LinearMap.fst_apply, Prod.snd_add, LinearMap.smul_apply,
        LinearMap.id_apply, Prod.smul_snd, smul_zero] at this
      simp [varpiOf]
      linear_combination (norm := module) this

/-- The transvection `(η, ξ) ↦ (η, ξ + w(η))` of `M ⊕ L`. -/
def transv (w : M →ₗ[R] L) : M × L →ₗ[R] M × L :=
  LinearMap.id + LinearMap.inr R M L ∘ₗ w ∘ₗ LinearMap.fst R M L

theorem transv_comp (w w' : M →ₗ[R] L) : transv w ∘ₗ transv w' = transv (w + w') := by
  refine LinearMap.ext fun p => Prod.ext ?_ ?_
  · simp [transv]
  · simp [transv]; abel

/-- A transvection carries the scindage of `b' + χw` to that of `b'`. -/
theorem piOf_comp_transv (b' w : M →ₗ[R] L) :
    piOf χ b' ∘ₗ transv w = piOf χ (b' + χ • w) := by
  apply LinearMap.prod_ext <;> ext <;> simp [piOf, transv]

theorem transv_comp_varpiOf (b' w : M →ₗ[R] L) :
    transv w ∘ₗ varpiOf χ (b' + χ • w) = varpiOf χ b' := by
  ext <;> simp [varpiOf, transv]

/-- **Morphisms in coordinates (pages 77 and 129).** An endomorphism `f` of
`M ⊕ L` inducing the identity on `L` and on `M` carries the scindage of `b` to
that of `b'` if and only if it is a transvection `T_w` with `b = b' + χw`; there
is such an `f` iff `b ≡ b' (mod χ)`. Every such `f` is invertible, `T_w⁻¹ = T_{−w}`. -/
theorem iso_iff (b b' : M →ₗ[R] L) :
    (∃ f : M × L →ₗ[R] M × L, LinearMap.fst R M L ∘ₗ f = LinearMap.fst R M L ∧
        f ∘ₗ LinearMap.inr R M L = LinearMap.inr R M L ∧ piOf χ b' ∘ₗ f = piOf χ b) ↔
      ∃ w : M →ₗ[R] L, b = b' + χ • w := by
  constructor
  · rintro ⟨f, h1, h2, h3⟩
    set w := LinearMap.snd R M L ∘ₗ f ∘ₗ LinearMap.inl R M L with hw
    have hf : f = transv w := by
      refine LinearMap.ext fun p => ?_
      obtain ⟨η, ξ⟩ := p
      have hp : ((η, ξ) : M × L) = (η, 0) + (0, ξ) := by simp
      have h1' := LinearMap.congr_fun h1 (η, 0)
      have h2' := LinearMap.congr_fun h2 ξ
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply,
        LinearMap.inr_apply] at h1' h2'
      rw [hp, map_add, map_add, h2']
      refine Prod.ext ?_ ?_
      · simp [transv, h1']
      · simp [transv, hw]
        rw [show ((0 : M), (0 : L)) = 0 from rfl, map_zero]; rfl
    refine ⟨w, ?_⟩
    have e := h3.symm.trans (by rw [hf, piOf_comp_transv])
    ext η
    have := LinearMap.congr_fun e (η, 0)
    simpa [piOf] using this
  · rintro ⟨w, rfl⟩
    refine ⟨transv w, ?_, ?_, piOf_comp_transv χ b' w⟩
    · ext <;> simp [transv]
    · ext <;> simp [transv]

variable {M₁ M₂ M₃ L₁ L₂ L₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [AddCommGroup M₃] [Module R M₃] [AddCommGroup L₁] [Module R L₁]
  [AddCommGroup L₂] [Module R L₂] [AddCommGroup L₃] [Module R L₃]

/-- The transvection datum of page 129: `u = b₁ ⊗ u₂ + u₁ ⊗ b₂ + χ u₁ ⊗ u₂`. -/
noncomputable def uProd (b₁ u₁ : M₁ →ₗ[R] L₁) (b₂ u₂ : M₂ →ₗ[R] L₂) :
    M₁ ⊗[R] M₂ →ₗ[R] L₁ ⊗[R] L₂ :=
  TensorProduct.map b₁ u₂ + TensorProduct.map u₁ b₂ + χ • TensorProduct.map u₁ u₂

/-- **Page 129.** Changing the scindages, `bᵢ ↦ bᵢ + χuᵢ`, changes the product
datum `b = b₁ ⊗ b₂` by `χu`: `b′₁ ⊗ b′₂ = b₁ ⊗ b₂ + χu`. -/
theorem prod_change (b₁ u₁ : M₁ →ₗ[R] L₁) (b₂ u₂ : M₂ →ₗ[R] L₂) :
    TensorProduct.map (b₁ + χ • u₁) (b₂ + χ • u₂)
      = TensorProduct.map b₁ b₂ + χ • uProd χ b₁ u₁ b₂ u₂ := by
  simp only [uProd, TensorProduct.map_add_left, TensorProduct.map_add_right,
    TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_add]
  abel

/-- **Page 131, the cocycle relation `u″ = u + u′`.** Two successive changes,
`uᵢ` then `u′ᵢ` (the second computed with `b′ᵢ = bᵢ + χuᵢ`), compose to the
change `uᵢ + u′ᵢ`. -/
theorem uProd_cocycle (b₁ u₁ u₁' : M₁ →ₗ[R] L₁) (b₂ u₂ u₂' : M₂ →ₗ[R] L₂) :
    uProd χ b₁ u₁ b₂ u₂ + uProd χ (b₁ + χ • u₁) u₁' (b₂ + χ • u₂) u₂'
      = uProd χ b₁ (u₁ + u₁') b₂ (u₂ + u₂') := by
  simp only [uProd, TensorProduct.map_add_left, TensorProduct.map_add_right,
    TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_add]
  abel

/-- **Page 78, commutativity.** Under `M₁ ⊗ M₂ ≅ M₂ ⊗ M₁` and
`L₁ ⊗ L₂ ≅ L₂ ⊗ L₁`, `b₁ ⊗ b₂` is `b₂ ⊗ b₁`. -/
theorem prod_comm (b₁ : M₁ →ₗ[R] L₁) (b₂ : M₂ →ₗ[R] L₂) :
    (TensorProduct.comm R L₁ L₂).toLinearMap ∘ₗ TensorProduct.map b₁ b₂
      = TensorProduct.map b₂ b₁ ∘ₗ (TensorProduct.comm R M₁ M₂).toLinearMap :=
  (TensorProduct.map_comp_comm_eq b₂ b₁).symm

/-- **Page 78, associativity.** -/
theorem prod_assoc (b₁ : M₁ →ₗ[R] L₁) (b₂ : M₂ →ₗ[R] L₂) (b₃ : M₃ →ₗ[R] L₃) :
    (TensorProduct.assoc R L₁ L₂ L₃).toLinearMap ∘ₗ TensorProduct.map (TensorProduct.map b₁ b₂) b₃
      = TensorProduct.map b₁ (TensorProduct.map b₂ b₃) ∘ₗ
          (TensorProduct.assoc R M₁ M₂ M₃).toLinearMap :=
  (TensorProduct.map_map_comp_assoc_eq b₁ b₂ b₃).symm

/-- **Page 78, unit.** The unit object is `M = L = R` with `b = id`
(`π(u, λ) = λ + χu`); under `R ⊗ M ≅ M`, `R ⊗ L ≅ L`, `id ⊗ b` is `b`. -/
theorem prod_unit (b : M →ₗ[R] L) :
    (TensorProduct.lid R L).toLinearMap ∘ₗ TensorProduct.map LinearMap.id b
      = b ∘ₗ (TensorProduct.lid R M).toLinearMap := by
  ext; simp

/-! ### `M = L = R`: the monoid of classes and its units -/

/-- Two scalar data `b`, `b'` (for `M = L = R`) give isomorphic objects, allowing
an automorphism `ε` of `L = R`: `εb ≡ b' (mod χ)`. -/
def ChiRel (b b' : R) : Prop := ∃ (ε : Rˣ) (w : R), ε * b = b' + χ * w

/-- The product `b = b₁b₂` is compatible with the relation. -/
theorem chiRel_mul {b₁ b₁' b₂ b₂' : R} (h₁ : ChiRel χ b₁ b₁') (h₂ : ChiRel χ b₂ b₂') :
    ChiRel χ (b₁ * b₂) (b₁' * b₂') := by
  obtain ⟨ε₁, w₁, e₁⟩ := h₁
  obtain ⟨ε₂, w₂, e₂⟩ := h₂
  refine ⟨ε₁ * ε₂, b₁' * w₂ + w₁ * b₂' + χ * w₁ * w₂, ?_⟩
  push_cast
  linear_combination (ε₂ * b₂) * e₁ + (b₁' + χ * w₁) * e₂

/-- **Page 79, the invertibility criterion, for `L = 𝒪` trivial.** The class of
`b` is invertible for the product (`bb' ≡ ε (mod χ)` for some `b'`) iff
`T₀ = −b₀` generates `L₀ = R/χR` on `V(χ)`, that is iff `b` and `χ` generate the
unit ideal. -/
theorem invertible_iff (b : R) :
    (∃ b', ChiRel χ (b * b') 1) ↔ Ideal.span {b, χ} = ⊤ := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair]
  constructor
  · rintro ⟨b', ε, w, e⟩
    exact ⟨ε * b', -w, by linear_combination e⟩
  · rintro ⟨g, h, e⟩
    exact ⟨g, 1, -h, by simp; linear_combination e⟩

/-- The same criterion, as the page states it: `b` is a unit in `R/χR`. -/
theorem span_eq_top_iff_isUnit (b : R) :
    Ideal.span {b, χ} = ⊤ ↔ IsUnit (Ideal.Quotient.mk (Ideal.span {χ}) b) := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair, isUnit_iff_exists_inv]
  constructor
  · rintro ⟨g, h, e⟩
    refine ⟨Ideal.Quotient.mk _ g, ?_⟩
    rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq,
      Ideal.mem_span_singleton]
    exact ⟨-h, by linear_combination e⟩
  · rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq,
      Ideal.mem_span_singleton] at hy
    obtain ⟨k, hk⟩ := hy
    exact ⟨g, -k, by linear_combination hk⟩

/-! ### Pushout and pullback products (pages 125, 127, 167 and 169) -/

/-- **Pages 125 and 127.** In coordinates the pullback product carries the
scindage `−b`, `b = b₁ ⊗ b₂`. If `γχ = 2`, the transvection `T_{γb}` carries the
pushout scindage `b` to the pullback scindage `−b`. -/
theorem push_pull {γ : R} (hγ : γ * χ = 2) (b : M →ₗ[R] L) :
    piOf χ (-b) ∘ₗ transv (γ • b) = piOf χ b := by
  rw [piOf_comp_transv, smul_smul, mul_comm, hγ, two_smul]
  congr 1; abel

/-- **Page 125, « commute ! ».** The comparison `T_{γb}` is compatible with the
changes of scindage: for `b ↦ b + χu` on the pushout side and `−b ↦ −b − χu` on
the pullback side, `T_{γb} ∘ T_u = T_{−u} ∘ T_{γ(b + χu)}`. -/
theorem push_pull_square {γ : R} (hγ : γ * χ = 2) (b u : M →ₗ[R] L) :
    transv (γ • b) ∘ₗ transv u = transv (-u) ∘ₗ transv (γ • (b + χ • u)) := by
  rw [transv_comp, transv_comp, smul_add, smul_smul, hγ, two_smul]
  congr 1; abel

/-- The hypothesis `γχ = 2` is necessary: for the unit objects (`M = L = R`,
`b₁ = b₂ = id`, so `b = id`), an isomorphism from the pushout to the pullback
inducing the identity on `L` and `M` exists iff `2 ∈ χR`. -/
theorem push_pull_unit_iff :
    (∃ f : R × R →ₗ[R] R × R, LinearMap.fst R R R ∘ₗ f = LinearMap.fst R R R ∧
        f ∘ₗ LinearMap.inr R R R = LinearMap.inr R R R ∧
        piOf χ (-LinearMap.id) ∘ₗ f = piOf χ LinearMap.id) ↔ ∃ γ : R, γ * χ = 2 := by
  rw [iso_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w 1, ?_⟩
    have := LinearMap.congr_fun hw 1
    simp at this
    linear_combination -this
  · rintro ⟨γ, hγ⟩
    refine ⟨γ • LinearMap.id, ?_⟩
    rw [smul_smul, mul_comm, hγ, two_smul]
    abel

/-- Over `ℤ` with `χ = 4`, there is no such `γ`. -/
theorem no_gamma_four : ¬ ∃ γ : ℤ, γ * 4 = 2 := by
  rintro ⟨γ, h⟩; omega

end ChiSplit

end Grothendieck.Folder84
