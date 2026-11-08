import Mathlib

/-!
# Quillen, notebook 1982-7, pp. 33-34: a symmetric matrix with non-positive off-diagonal entries
# and a positive vector `v` with `A v ≥ 0` is positive semidefinite

Daniel Quillen's research notebook 1982-7 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201982/1982-7.pdf>), entry of
June 25, 1982, prepares the Hodge index theorem for surfaces. He wants to see the negativity
of the intersection matrix `(Cᵢ · Cⱼ)` of the exceptional curves of a resolved surface
singularity (Mumford): its off-diagonal entries are `≥ 0` and there is a combination
`D = ∑ nᵢ Cᵢ` with all `nᵢ > 0` and `Cᵢ · D = 0` for all `i`. After a first induction that he
abandons (p. 33), he states on p. 34 the assertion to prove, in our words: *a real symmetric
matrix `A` with off-diagonal entries `≤ 0`, for which some vector `v` with strictly positive
entries has `A v ≥ 0` (non-negative row sums once `v` is normalised to `(1, …, 1)`), is positive
semidefinite.* The page writes the hypothesis as `vᵗ A v ≥ 0`; the proof uses the row sums, that
is `A v ≥ 0`, and with `vᵗ A v ≥ 0` alone the statement is false (`not_posSemidef_example`).

The proof here is not the induction of the page but the identity, for `vᵢ ≠ 0`,

  `xᵗ A x = ∑ᵢ (A v)ᵢ xᵢ² / vᵢ - ½ ∑ᵢ ∑ⱼ Aᵢⱼ vᵢ vⱼ (xᵢ/vᵢ - xⱼ/vⱼ)²`,

in which every term is `≥ 0` under the hypotheses (the diagonal terms of the double sum vanish).

* `quadratic_identity`: the identity, for a symmetric matrix over a field;
* `posSemidef_of_mulVec_nonneg`: **the assertion of p. 34**;
* `quadratic_nonpos_of_mulVec_eq_zero`: the form of p. 33, for the intersection matrix:
  off-diagonal entries `≥ 0` and a positive vector in the kernel give `xᵗ C x ≤ 0`;
* `ratio_eq_of_quadratic_eq_zero`: the equality case: if `A v = 0` and `xᵗ A x = 0`, then
  `xᵢ/vᵢ = xⱼ/vⱼ` whenever `Aᵢⱼ < 0` (so for a connected configuration `x` is a multiple
  of `v`);
* `not_posSemidef_example`: the hypothesis as written on the page, `vᵗ A v ≥ 0`, does not
  suffice: `A = !![4, -1; -1, -1]`, `v = (1, 1)`.
-/

namespace Quillen.Notebook1982_7

open Matrix Finset

variable {n : Type*} [Fintype n]

/-- The identity behind the lemma: for a symmetric matrix `A` and a vector `v` with non-zero
entries, `xᵗ A x = ∑ᵢ (A v)ᵢ xᵢ² / vᵢ - ½ ∑ᵢⱼ Aᵢⱼ vᵢ vⱼ (xᵢ/vᵢ - xⱼ/vⱼ)²`. -/
theorem quadratic_identity {K : Type*} [Field K] (A : Matrix n n K) (hA : A.IsSymm)
    (v : n → K) (hv : ∀ i, v i ≠ 0) (x : n → K) (h2 : (2 : K) ≠ 0) :
    x ⬝ᵥ (A *ᵥ x) =
      ∑ i, (A *ᵥ v) i * x i ^ 2 / v i -
        (∑ i, ∑ j, A i j * v i * v j * (x i / v i - x j / v j) ^ 2) / 2 := by
  -- Write `x i = v i * y i`.
  set y : n → K := fun i => x i / v i with hy
  have hx : ∀ i, x i = v i * y i := fun i => by
    simp only [hy]; field_simp [hv i]
  -- The two "square" halves of the double sum agree, by symmetry of `A`.
  have hswap : ∑ i, ∑ j, A i j * v i * v j * y j ^ 2 =
      ∑ i, ∑ j, A i j * v i * v j * y i ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hA.apply i j]; ring
  have hfirst : ∑ i, (A *ᵥ v) i * x i ^ 2 / v i = ∑ i, ∑ j, A i j * v i * v j * y i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx i, mulVec, dotProduct, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp [hv i]
  have hlhs : x ⬝ᵥ (A *ᵥ x) = ∑ i, ∑ j, A i j * v i * v j * (y i * y j) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hx i, hx j]; ring
  have hsq : ∑ i, ∑ j, A i j * v i * v j * (y i - y j) ^ 2 =
      ∑ i, ∑ j, A i j * v i * v j * y i ^ 2 + ∑ i, ∑ j, A i j * v i * v j * y j ^ 2 -
        2 * ∑ i, ∑ j, A i j * v i * v j * (y i * y j) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hfirst, hlhs]
  change _ = _ - (∑ i, ∑ j, A i j * v i * v j * (y i - y j) ^ 2) / 2
  rw [hsq, hswap]
  field_simp
  ring

/-- **Quillen, notebook 1982-7, p. 34.** A real symmetric matrix whose off-diagonal entries are
`≤ 0`, and for which some vector `v` with strictly positive entries has `A v ≥ 0`, is positive
semidefinite. -/
theorem posSemidef_of_mulVec_nonneg (A : Matrix n n ℝ) (hA : A.IsSymm)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (v : n → ℝ) (hv : ∀ i, 0 < v i)
    (hAv : ∀ i, 0 ≤ (A *ᵥ v) i) : A.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_iff_isSymm.2 hA) fun x => ?_
  rw [star_trivial, quadratic_identity A hA v (fun i => (hv i).ne') x two_ne_zero]
  have h1 : 0 ≤ ∑ i, (A *ᵥ v) i * x i ^ 2 / v i :=
    Finset.sum_nonneg fun i _ => div_nonneg (mul_nonneg (hAv i) (sq_nonneg _)) (hv i).le
  have h2 : ∑ i, ∑ j, A i j * v i * v j * (x i / v i - x j / v j) ^ 2 ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp
    · exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (hoff i j hij) (hv i).le) (hv j).le)
        (sq_nonneg _)
  linarith

/-- **Quillen, notebook 1982-7, p. 33**, the form needed for the intersection matrix of the
exceptional curves: a real symmetric matrix `C` with off-diagonal entries `≥ 0` and a vector
`D` with strictly positive entries such that `C D = 0` (more generally `C D ≤ 0`) is negative
semidefinite. -/
theorem quadratic_nonpos_of_mulVec_eq_zero (C : Matrix n n ℝ) (hC : C.IsSymm)
    (hoff : ∀ i j, i ≠ j → 0 ≤ C i j) (D : n → ℝ) (hD : ∀ i, 0 < D i)
    (hCD : ∀ i, (C *ᵥ D) i ≤ 0) (x : n → ℝ) : x ⬝ᵥ (C *ᵥ x) ≤ 0 := by
  have hneg := posSemidef_of_mulVec_nonneg (-C) (by simpa [IsSymm] using congrArg Neg.neg hC)
    (fun i j hij => by simpa using hoff i j hij) D hD
    (fun i => by simpa [neg_mulVec] using hCD i)
  have := hneg.dotProduct_mulVec_nonneg x
  rw [star_trivial, neg_mulVec, dotProduct_neg] at this
  linarith

/-- The equality case (Zariski's form): if `A v = 0` for a vector `v` with strictly positive
entries, the off-diagonal entries of the symmetric matrix `A` are `≤ 0`, and `xᵗ A x = 0`, then
`xᵢ / vᵢ = xⱼ / vⱼ` whenever `Aᵢⱼ < 0`. -/
theorem ratio_eq_of_quadratic_eq_zero (A : Matrix n n ℝ) (hA : A.IsSymm)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (v : n → ℝ) (hv : ∀ i, 0 < v i)
    (hAv : A *ᵥ v = 0) (x : n → ℝ) (hx : x ⬝ᵥ (A *ᵥ x) = 0) {i j : n} (hij : A i j < 0) :
    x i / v i = x j / v j := by
  rw [quadratic_identity A hA v (fun i => (hv i).ne') x two_ne_zero, hAv] at hx
  simp only [Pi.zero_apply, zero_mul, zero_div, Finset.sum_const_zero, zero_sub,
    neg_eq_zero, div_eq_zero_iff, two_ne_zero, or_false] at hx
  -- Every term of the double sum is `≤ 0`, and the sum is `0`, so each term is `0`.
  have hterm : ∀ k l, A k l * v k * v l * (x k / v k - x l / v l) ^ 2 ≤ 0 := by
    intro k l
    by_cases hkl : k = l
    · subst hkl; simp
    · exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (hoff k l hkl) (hv k).le) (hv l).le)
        (sq_nonneg _)
  have hrow : ∀ k, ∑ l, A k l * v k * v l * (x k / v k - x l / v l) ^ 2 ≤ 0 :=
    fun k => Finset.sum_nonpos fun l _ => hterm k l
  have hrow0 : ∑ l, A i l * v i * v l * (x i / v i - x l / v l) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos fun k _ => hrow k).1 hx i (Finset.mem_univ _)
  have h0 : A i j * v i * v j * (x i / v i - x j / v j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos fun l _ => hterm i l).1 hrow0 j (Finset.mem_univ _)
  have hc : A i j * v i * v j ≠ 0 :=
    mul_ne_zero (mul_ne_zero hij.ne (hv i).ne') (hv j).ne'
  have := (mul_eq_zero.1 h0).resolve_left hc
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

/-- The hypothesis as written on p. 34, `vᵗ A v ≥ 0` for a positive `v`, does not suffice:
`A = !![4, -1; -1, -1]` has off-diagonal entries `≤ 0` and `(1, 1)ᵗ A (1, 1) = 1`, but
`(0, 1)ᵗ A (0, 1) = -1`. -/
theorem not_posSemidef_example :
    let A : Matrix (Fin 2) (Fin 2) ℝ := !![4, -1; -1, -1]
    A.IsSymm ∧ (∀ i j, i ≠ j → A i j ≤ 0) ∧ 0 ≤ ![1, 1] ⬝ᵥ (A *ᵥ ![1, 1]) ∧
      ¬ A.PosSemidef := by
  intro A
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [A]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp [A] at hij ⊢
  · simp [A, dotProduct, mulVec, Fin.sum_univ_two]; norm_num
  · intro h
    have := h.dotProduct_mulVec_nonneg ![0, 1]
    simp [A, dotProduct, mulVec, Fin.sum_univ_two] at this
    norm_num at this

end Quillen.Notebook1982_7
