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

end Grothendieck.Folder84
