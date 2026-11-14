import Mathlib

/-!
# Quillen, notebook 1972-mixed: alternating perfect pairings force even dimension

Daniel Quillen's research notebook 1972-mixed (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201972/1972-mixed%20papers.pdf>).

(file « 1972-mixed papers ».)

* p. 41: a nondegenerate alternating bilinear form on a finite-dimensional vector space over a
  field has even dimension (`even_finrank`), in every characteristic, through: an alternating
  matrix of odd size has determinant zero over any commutative ring
  (`det_eq_zero_of_alternating`), proved for the generic alternating matrix over `ℤ[X_{ij}]`,
  where `det = −det` and `ℤ[X]` has no `2`-torsion (`det_generic_eq_zero`).
-/

namespace Quillen.Notebook1972_MixedAlt

open Matrix

/-- The generic alternating matrix over `ℤ[X_{ij}]`. -/
noncomputable def generic (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℤ) :=
  .of fun i j => if i < j then .X (i, j) else if j < i then -.X (j, i) else 0

theorem det_generic_eq_zero {n : ℕ} (hn : Odd n) : (generic n).det = 0 := by
  have h : (generic n)ᵀ = -generic n := by
    refine Matrix.ext fun i j => ?_
    simp only [generic, transpose_apply, of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.not_gt]
    · simp
    · simp [h, h.not_gt]
  have h2 : (2 : MvPolynomial (Fin n × Fin n) ℤ) * (generic n).det = 0 := by
    have := congrArg det h
    rw [det_transpose, det_neg, Fintype.card_fin, hn.neg_one_pow] at this
    linear_combination this
  simpa using h2

/-- An alternating matrix (zero diagonal, `Mᵀ = −M`) of odd size has determinant zero, over any
commutative ring, characteristic `2` included. -/
theorem det_eq_zero_of_alternating {R : Type*} [CommRing R] {n : ℕ} (hn : Odd n)
    (M : Matrix (Fin n) (Fin n) R) (hd : ∀ i, M i i = 0) (hs : ∀ i j, M j i = -M i j) :
    M.det = 0 := by
  let f := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun p : Fin n × Fin n => M p.1 p.2)
  have : (generic n).map f = M := by
    refine Matrix.ext fun i j => ?_
    simp only [map_apply, generic, of_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, f]
    · simp only [lt_irrefl, ite_false, map_zero, hd]
    · simp [h, h.not_gt, f, hs j i]
  rw [← this, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_generic_eq_zero hn, map_zero]

/-- **p. 41.** A nondegenerate alternating bilinear form on a finite-dimensional vector space forces
even dimension. -/
theorem even_finrank {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {B : LinearMap.BilinForm K V} (hB : B.IsAlt) (hn : B.Nondegenerate) :
    Even (Module.finrank K V) := by
  by_contra h
  let b := Module.finBasis K V
  refine ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hn)
    (det_eq_zero_of_alternating (Nat.not_even_iff_odd.1 h) _ (fun i => ?_) fun i j => ?_)
  · simp [LinearMap.BilinForm.toMatrix_apply, hB.self_eq_zero]
  · simp only [LinearMap.BilinForm.toMatrix_apply]; exact (LinearMap.IsAlt.neg hB _ _).symm

end Quillen.Notebook1972_MixedAlt
