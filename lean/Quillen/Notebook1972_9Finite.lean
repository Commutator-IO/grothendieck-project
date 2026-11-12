import Mathlib

/-!
# Quillen, notebook 1972-9, p. 71: `k[t, x]` is finite over `k[t, tx + x^q]`

Daniel Quillen's research notebook 1972-9 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201972/1972-9.pdf>). On p. 71
the family `f + t · id` is proper because `k[t, x]` is finite over the subalgebra generated
by `t` and `y = tx + x^q`.

Here `t = X 0`, `x = X 1` in `MvPolynomial (Fin 2) k`, over any commutative ring `k`:

* `isIntegral_X_one`: `x` is a root of the monic `Z^q + tZ − y` over `k[t, y]` (`q ≥ 2`);
* `finite`: **the statement**, `k[t, x]` is a finite `k[t, tx + x^q]`-module (`q ≥ 2`).

The hypothesis `q ≥ 2` makes the polynomial monic; for `q = 1`, `y = (1 + t)x` and the statement
fails (the fibre at `t = −1`, `y = 0` is `k[x]`), which is not formalised.
-/

namespace Quillen.Notebook1972_9Finite

open MvPolynomial Polynomial

variable (k : Type*) [CommRing k] (q : ℕ)

/-- The subalgebra `k[t, tx + x^q]` of `k[t, x]`. -/
noncomputable abbrev S : Subalgebra k (MvPolynomial (Fin 2) k) :=
  Algebra.adjoin k {MvPolynomial.X 0, MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 1 ^ q}

theorem t_mem : (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ∈ S k q :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

theorem y_mem :
    (MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 1 ^ q : MvPolynomial (Fin 2) k) ∈ S k q :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

/-- `x` is integral over `k[t, tx + x^q]`: a root of `Z^q + tZ − y`. -/
theorem isIntegral_X_one (hq : 2 ≤ q) :
    IsIntegral (S k q) (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) := by
  let t : S k q := ⟨_, t_mem k q⟩
  let y : S k q := ⟨_, y_mem k q⟩
  refine ⟨Polynomial.X ^ q + (Polynomial.C t * Polynomial.X - Polynomial.C y), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    calc (Polynomial.C t * Polynomial.X - Polynomial.C y).degree ≤ (1 : WithBot ℕ) := by
          refine (Polynomial.degree_sub_le _ _).trans (max_le ?_ ?_)
          · exact (Polynomial.degree_C_mul_X_le t)
          · exact Polynomial.degree_C_le.trans (by norm_num)
      _ < (q : WithBot ℕ) := by exact_mod_cast (by omega : 1 < q)
  · simp [t, y, Polynomial.eval₂_sub]

/-- **Notebook 1972-9, p. 71**: `k[t, x]` is finite over `k[t, tx + x^q]`, for `q ≥ 2`. -/
theorem finite (hq : 2 ≤ q) : Module.Finite (S k q) (MvPolynomial (Fin 2) k) := by
  have htop : Algebra.adjoin (S k q) {(MvPolynomial.X 1 : MvPolynomial (Fin 2) k)} = ⊤ := by
    rw [eq_top_iff]
    have h : (⊤ : Subalgebra k (MvPolynomial (Fin 2) k)) ≤
        (Algebra.adjoin (S k q) {(MvPolynomial.X 1 : MvPolynomial (Fin 2) k)}).restrictScalars k := by
      rw [← MvPolynomial.adjoin_range_X, Algebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
      match i with
      | 0 =>
        have := (Algebra.adjoin (S k q)
          {(MvPolynomial.X 1 : MvPolynomial (Fin 2) k)}).algebraMap_mem (⟨_, t_mem k q⟩ : S k q)
        exact this
      | 1 => exact Algebra.subset_adjoin rfl
    intro z _
    exact h trivial
  rw [Module.finite_def, ← Algebra.top_toSubmodule, ← htop]
  exact (isIntegral_X_one k q hq).fg_adjoin_singleton

end Quillen.Notebook1972_9Finite
