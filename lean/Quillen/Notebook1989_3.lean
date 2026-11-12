import Mathlib

/-!
# Quillen, notebook 1989-3: powers of a block matrix with a zero corner; an involution

Daniel Quillen's research notebook 1989-3 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201989/1989-3.pdf>).

* p. 100: for `M = (A B; C 0)` over any ring (rectangular blocks), put `P₀ = 0`, `P₁ = 1`,
  `P_{n+2} = A P_{n+1} + B C P_n` (so `P_{n+1}` is the page's `P_n`, with `P_{−1} = 0`). Then
  `M^{n+1} = (P_{n+2}, P_{n+1} B; C P_{n+1}, C P_n B)` (`fromBlocks_pow_succ`): a
  noncommutative Chebyshev recursion.
* p. 99: if `b`, `c` commute with `z` and `bc = cb = 1 − z²`, then `F = (z b; c −z)` is an
  involution (`involution`).
-/

namespace Quillen.Notebook1989_3

open Matrix

section Block

variable {R : Type*} [Ring R] {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
  [DecidableEq k] (A : Matrix m m R) (B : Matrix m k R) (C : Matrix k m R)

/-- `P₀ = 0`, `P₁ = 1`, `P_{n+2} = A P_{n+1} + B C P_n`. -/
def P : ℕ → Matrix m m R
  | 0 => 0
  | 1 => 1
  | n + 2 => A * P (n + 1) + B * C * P n

/-- **Notebook 1989-3, p. 100**: `(A B; C 0)^{n+1} = (P_{n+2}, P_{n+1} B; C P_{n+1}, C P_n B)`. -/
theorem fromBlocks_pow_succ (n : ℕ) :
    fromBlocks A B C 0 ^ (n + 1) =
      fromBlocks (P A B C (n + 2)) (P A B C (n + 1) * B) (C * P A B C (n + 1))
        (C * P A B C n * B) := by
  induction n with
  | zero => simp [P]
  | succ n ih =>
    rw [pow_succ', ih, fromBlocks_multiply]
    simp only [P, Matrix.zero_mul, add_zero, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

end Block

section Involution

variable {R : Type*} [Ring R]

/-- **Notebook 1989-3, p. 99**: `F = (z b; c −z)` is an involution when `b`, `c` commute with `z`
and `bc = cb = 1 − z²`. -/
theorem involution {z b c : R} (hb : Commute z b) (hc : Commute z c) (hbc : b * c = 1 - z ^ 2)
    (hcb : c * b = 1 - z ^ 2) : !![z, b; c, -z] * !![z, b; c, -z] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hbc, hcb, hb.eq, hc.eq, sq]

end Involution

end Quillen.Notebook1989_3
