import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# Folder 85: the invariant of a rotation of order 5 (pages 10, 27, 30, 40)

**Partial, and chosen.** The finding `85-a5-pgl2-moduli-spec-z-phi`
(`src/content/findings.ts`) states the theorem of page 40 of the reading
(`transcripts/85/85.modern.tex`):

> For any scheme `S`, the groupoid of pairs `(G, φ)`, `G` a form of `PGL₂` over
> `S` and `φ : 𝔄₅ → G` a monomorphism, is rigid, and `φ ↦ A(φ(π))` (`π` a
> standard 5-cycle) makes its functor of isomorphism classes representable by
> `Spec ℤ[T]/(T² + T − 1)`.

Rigidity, representability and the passage to forms of `PGL₂` are out of
reach here. What this file proves is the computation under the statement:
the value `A(φ(π))` is a root of `T² + T − 1`, and, conversely, a root is
attained.

The invariant. For `PGL₂` the reading (pages 23 and 27) takes
`A(v) = (Tr v)² / det v − 2` for a lift `v ∈ GL₂`. Here `invA g` is this
expression for a `2 × 2` matrix `g` over a commutative ring `R`, with
`Ring.inverse` for the division; it is used only when `det g` is a unit. It
does not depend on the lift (`invA_smul`).

Order 5 on every fibre. For a matrix with invertible determinant, "the image
of `g` in `PGL₂(k(s))` is not `1`, for every point `s`" says that `g 0 1`,
`g 1 0` and `g 0 0 − g 1 1` do not all vanish in any residue field, that is,
that they generate the unit ideal (`NullePartScalaire`). Since 5 is prime,
"of order 5 on every fibre" is then `g⁵` scalar.

* `pow_five_eq`: `g⁵ = x₅ g + y₅` with `x₅ = t⁴ − 3dt² + d²` (Cayley–Hamilton,
  iterated), `t = Tr g`, `d = det g`; `coeff_eq`: `x₅ = d² (A² + A − 1)`.
* `sq_add_sub_of_pow_five` (the finding's computation): `g` nowhere scalar,
  `det g` a unit, `g⁵` scalar ⟹ `A(g)² + A(g) − 1 = 0`. Over any commutative
  ring: no hypothesis on 2, 5, reducedness.
* `pow_five_of_sq_add_sub`: the converse, without the nowhere-scalar hypothesis.
* `invA_sq`: `A(g²) = A(g)² − 2`, hence `A(g²) = −1 − A(g)` for a root
  (`invA_sq_of_root`), the corollary of page 40.
* The model (`sModel`, `pModel`): over any ring with `ζ⁴ + ζ³ + ζ² + ζ + 1 = 0`,
  `s = !![0, −1; 1, 0]` and `p = !![ζ, 1; 0, ζ⁴]` satisfy `s²`, `(sp)³`, `p⁵`
  scalar, all three nowhere scalar, with `A(p) = ζ² + ζ³` a root of
  `T² + T − 1`; `exists_model_adjoinRoot` instantiates it over `ℤ[ζ₅]`. These
  are the relations of the (2, 3, 5) triangle group, which is `𝔄₅`; the
  homomorphism from `𝔄₅` and its injectivity are not formalised.

What the formalisation found: the computation holds over every base, in
characteristics 2, 3 and 5 included; in characteristic 5 the model gives the
unipotent `p` (`ζ = 1`, `A = 2`). The model lives in the split `PGL₂` over
`ℤ[ζ₅]`, not over `ℤ[T]/(T² + T − 1)`: over `ℚ(√5)`, a real field, the split
`PGL₂` contains no `𝔄₅` (the criterion the reading cites from memory), so a
model over `ℤ[φ]` needs a non-split form, which is why the theorem speaks of
forms of `PGL₂`.
-/

namespace Grothendieck.Folder85

open Matrix

variable {R : Type*} [CommRing R]

/-- The invariant `A` of pages 23 and 27 for `PGL₂`: `(Tr g)² / det g − 2`,
for a lift `g ∈ GL₂(R)`. -/
noncomputable def invA (g : Matrix (Fin 2) (Fin 2) R) : R :=
  g.trace ^ 2 * Ring.inverse g.det - 2

/-- `g` is nowhere scalar: its image in `PGL₂(k(s))` is not `1` for any point
`s` of `Spec R`, that is, `b`, `c`, `a − d` generate the unit ideal. -/
def NullePartScalaire (g : Matrix (Fin 2) (Fin 2) R) : Prop :=
  Ideal.span {g 0 1, g 1 0, g 0 0 - g 1 1} = ⊤

theorem nullePartScalaire_of_isUnit (g : Matrix (Fin 2) (Fin 2) R) (hu : IsUnit (g 0 1)) :
    NullePartScalaire g :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) hu

/-- `A` depends only on the image in `PGL₂`: `A(μ g) = A(g)` for a unit `μ`. -/
theorem invA_smul (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det) {μ : R} (hμ : IsUnit μ) :
    invA (μ • g) = invA g := by
  have hd : (μ • g).det = μ ^ 2 * g.det := by simp
  have ht : (μ • g).trace = μ * g.trace := by simp [Matrix.trace_smul]
  have h1 := Ring.inverse_mul_cancel _ (hd ▸ (hμ.pow 2).mul hg)
  have h2 := Ring.inverse_mul_cancel _ hg
  unfold invA
  rw [ht]
  rw [hd] at h1 ⊢
  linear_combination g.trace ^ 2 * (-(μ ^ 2 * Ring.inverse (μ ^ 2 * g.det)) * h2
    + Ring.inverse g.det * h1)

/-- Cayley–Hamilton iterated: `g⁵ = x₅ g + y₅` with `x₅ = t⁴ − 3dt² + d²`. -/
theorem pow_five_eq (g : Matrix (Fin 2) (Fin 2) R) :
    g ^ 5 = (g.trace ^ 4 - 3 * g.det * g.trace ^ 2 + g.det ^ 2) • g
      + (-(g.det) * (g.trace ^ 3 - 2 * g.det * g.trace)) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, trace_fin_two, det_fin_two] <;> ring

/-- `x₅ = d² (A² + A − 1)`. -/
theorem coeff_eq (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det) :
    g.trace ^ 4 - 3 * g.det * g.trace ^ 2 + g.det ^ 2
      = g.det ^ 2 * (invA g ^ 2 + invA g - 1) := by
  have h := Ring.mul_inverse_cancel _ hg
  unfold invA
  linear_combination (-(g.trace ^ 4 * (g.det * Ring.inverse g.det + 1))
    + 3 * g.trace ^ 2 * g.det) * h

/-- **Pages 10, 30, 40.** If `g ∈ GL₂(R)` is nowhere scalar and `g⁵` is scalar
(the image of `g` in `PGL₂` has order 5 on every fibre), then `A(g)` is a root
of `T² + T − 1`. Over any commutative ring. -/
theorem sq_add_sub_of_pow_five (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det)
    (hns : NullePartScalaire g)
    {c : R} (h5 : g ^ 5 = c • (1 : Matrix (Fin 2) (Fin 2) R)) :
    invA g ^ 2 + invA g - 1 = 0 := by
  set x := g.trace ^ 4 - 3 * g.det * g.trace ^ 2 + g.det ^ 2 with hx
  have e := pow_five_eq g
  rw [h5] at e
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have e00 := congrFun (congrFun e 0) 0
  have e11 := congrFun (congrFun e 1) 1
  simp at e01 e10 e00 e11
  have hle : Ideal.span {g 0 1, g 1 0, g 0 0 - g 1 1} ≤
      LinearMap.ker (LinearMap.mul R R x) := by
    rw [Ideal.span_le]
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mul_apply']
    rcases hr with rfl | rfl | rfl
    · linear_combination -e01
    · linear_combination -e10
    · linear_combination e11 - e00
  rw [hns] at hle
  have h1 : x * 1 = 0 := hle Submodule.mem_top
  rw [mul_one, hx, coeff_eq g hg] at h1
  exact ((hg.pow 2).mul_right_eq_zero).1 h1

/-- The converse: if `A(g)² + A(g) − 1 = 0`, then `g⁵` is scalar. No
hypothesis on `g` besides `det g` a unit. -/
theorem pow_five_of_sq_add_sub (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det)
    (hA : invA g ^ 2 + invA g - 1 = 0) :
    g ^ 5 = (-(g.det) * (g.trace ^ 3 - 2 * g.det * g.trace)) •
      (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [pow_five_eq g, coeff_eq g hg, hA]
  simp

/-- `A(g²) = A(g)² − 2` (the polynomial `S₂`). -/
theorem invA_sq (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det) :
    invA (g ^ 2) = invA g ^ 2 - 2 := by
  have ht : (g ^ 2).trace = g.trace ^ 2 - 2 * g.det := by
    simp [sq, trace_fin_two, det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have h := Ring.mul_inverse_cancel _ hg
  unfold invA
  rw [ht, det_pow, ← Ring.inverse_pow]
  linear_combination (-4 * g.trace ^ 2 * Ring.inverse g.det
    + 4 * (g.det * Ring.inverse g.det + 1)) * h

/-- **Corollary of page 40.** For a root, `A(g²) = −1 − A(g)`, the other root. -/
theorem invA_sq_of_root (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det)
    (hA : invA g ^ 2 + invA g - 1 = 0) :
    invA (g ^ 2) = -1 - invA g := by
  rw [invA_sq g hg]; linear_combination hA

section Model

variable (ζ : R)

/-- The involution of the model. -/
def sModel : Matrix (Fin 2) (Fin 2) R := !![0, -1; 1, 0]

/-- The rotation of order 5 of the model. -/
def pModel : Matrix (Fin 2) (Fin 2) R := !![ζ, 1; 0, ζ ^ 4]

theorem sModel_sq : (sModel : Matrix (Fin 2) (Fin 2) R) ^ 2 = (-1 : R) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, sModel, Matrix.mul_apply, Fin.sum_univ_two]

theorem sModel_nullePartScalaire : NullePartScalaire (sModel : Matrix (Fin 2) (Fin 2) R) :=
  nullePartScalaire_of_isUnit _ (by simp [sModel])

theorem pModel_nullePartScalaire : NullePartScalaire (pModel ζ) :=
  nullePartScalaire_of_isUnit _ (by simp [pModel])

variable {ζ} (h : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0)
include h

theorem zeta_pow_five : ζ ^ 5 = 1 := by linear_combination (ζ - 1) * h

theorem det_pModel : (pModel ζ).det = 1 := by
  simp [pModel, det_fin_two]; linear_combination zeta_pow_five h

/-- `A(p) = ζ² + ζ³` (that is `ζ² + ζ⁻²`). -/
theorem invA_pModel : invA (pModel ζ) = ζ ^ 2 + ζ ^ 3 := by
  unfold invA
  rw [det_pModel h, Ring.inverse_one]
  simp [pModel, trace_fin_two]
  linear_combination (2 + ζ ^ 3) * zeta_pow_five h

theorem invA_pModel_root : invA (pModel ζ) ^ 2 + invA (pModel ζ) - 1 = 0 := by
  rw [invA_pModel h]; linear_combination h + (2 + ζ) * zeta_pow_five h

/-- `p⁵` is scalar, by `pow_five_of_sq_add_sub`. -/
theorem pModel_pow_five : ∃ c : R, pModel ζ ^ 5 = c • (1 : Matrix (Fin 2) (Fin 2) R) :=
  ⟨_, pow_five_of_sq_add_sub _ (by rw [det_pModel h]; exact isUnit_one) (invA_pModel_root h)⟩

theorem sp_sq : sModel * pModel ζ * (sModel * pModel ζ) = sModel * pModel ζ - 1 := by
  have h5 := zeta_pow_five h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sModel, pModel, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination h5 | linear_combination -h5

/-- `(sp)³ = −1`: the product `sp` has order 3 in `PGL₂`. -/
theorem sp_cube : (sModel * pModel ζ) ^ 3 = (-1 : R) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  have e := sp_sq h
  set t := sModel * pModel ζ
  calc t ^ 3 = t * (t * t) := by rw [pow_succ, pow_two, mul_assoc]
    _ = t * t - t := by rw [e, mul_sub, mul_one, e]
    _ = (-1 : R) • 1 := by rw [e]; simp

theorem sp_nullePartScalaire : NullePartScalaire (sModel * pModel ζ) := by
  refine nullePartScalaire_of_isUnit _ ?_
  have : (sModel * pModel ζ : Matrix (Fin 2) (Fin 2) R) 0 1 = -ζ ^ 4 := by
    simp [sModel, pModel, Matrix.mul_apply, Fin.sum_univ_two]
  rw [this]
  exact IsUnit.of_mul_eq_one (-ζ) (by linear_combination zeta_pow_five h)

end Model

/-- The model over `ℤ[ζ₅] = ℤ[X]/(X⁴ + X³ + X² + X + 1)`: a rotation `p` of order 5
on every fibre, `s` of order 2, `sp` of order 3, with `A(p)` a root of
`T² + T − 1`. -/
theorem exists_model_adjoinRoot :
    let f : Polynomial ℤ := Polynomial.X ^ 4 + Polynomial.X ^ 3 + Polynomial.X ^ 2
      + Polynomial.X + 1
    let ζ := AdjoinRoot.root f
    (sModel : Matrix (Fin 2) (Fin 2) (AdjoinRoot f)) ^ 2 = (-1 : AdjoinRoot f) • 1 ∧ (sModel * pModel ζ) ^ 3 = (-1 : AdjoinRoot f) • 1 ∧
      (∃ c : AdjoinRoot f, pModel ζ ^ 5 = c • 1) ∧
      NullePartScalaire (sModel : Matrix (Fin 2) (Fin 2) (AdjoinRoot f)) ∧
      NullePartScalaire (pModel ζ) ∧ NullePartScalaire (sModel * pModel ζ) ∧
      invA (pModel ζ) ^ 2 + invA (pModel ζ) - 1 = 0 := by
  intro f ζ
  have h : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by
    have := AdjoinRoot.eval₂_root f
    simpa [f] using this
  exact ⟨sModel_sq, sp_cube h, pModel_pow_five h, sModel_nullePartScalaire,
    pModel_nullePartScalaire ζ, sp_nullePartScalaire h, invA_pModel_root h⟩

end Grothendieck.Folder85
