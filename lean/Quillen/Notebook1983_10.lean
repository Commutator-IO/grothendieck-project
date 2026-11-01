import Mathlib

/-!
# Quillen, notebook 1983-10, p. 31: odd powers of a difference of two idempotents

Daniel Quillen's research notebook 1983-10 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201983/1983-10.pdf>) works on
index formulas in cyclic cohomology. On p. 31 (his p. 154) he notes that his index formula, in
its Toeplitz and graded forms, is the trace of an odd power of a difference of two idempotents,
and he proposes to look at `tr ((e₁ - e₂) ^ (2n + 1))` and to try to show that it is an integer
independent of `n`. The page states this as a programme; it does not give the identity below.

In finite dimension the answer is an identity, valid over every commutative ring:
`tr ((P - Q) ^ (2k + 1)) = tr P - tr Q` for idempotent square matrices `P`, `Q`. The usual proof
(`A = P - Q` and `B = P + Q - 1` anticommute, `A² + B² = 1`, so `tr (A ^ m B²) = - tr (A ^ m B²)`
for `m` odd) divides by 2. The proof here does not: `C = (P - Q)²` commutes with `P` and `Q`,
`(P - Q) C = (P - Q) - (P Q P - Q P Q)`, and `tr (D P Q P) = tr (D Q P Q)` whenever `D` commutes
with `P` and `Q`.

* `sq_sub_commute_left`, `sq_sub_commute_right`: `(P - Q)²` commutes with `P` and with `Q`;
* `sub_mul_sq_sub`: `(P - Q) (P - Q)² = (P - Q) - (P Q P - Q P Q)`;
* `trace_mul_PQP`: `tr (D P Q P) = tr (D Q P Q)` when `D` commutes with `P` and `Q`;
* `trace_sub_pow_odd`: `tr ((P - Q) ^ (2k + 1)) = tr P - tr Q`, over any commutative ring;
  no hypothesis on 2.
-/

namespace Quillen.Notebook1983_10

open Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- `(P - Q)²` commutes with `P` when `P` and `Q` are idempotent: both products equal
`P - P Q P`. -/
theorem sq_sub_commute_left {P Q : Matrix n n R} (hP : IsIdempotentElem P)
    (hQ : IsIdempotentElem Q) : Commute ((P - Q) ^ 2) P := by
  have hP' : P * P = P := hP
  have hQ' : Q * Q = Q := hQ
  unfold Commute SemiconjBy
  simp only [sq, sub_mul, mul_sub, Matrix.mul_assoc, hP', hQ']
  simp only [← Matrix.mul_assoc, hP']
  abel

/-- `(P - Q)²` commutes with `Q` when `P` and `Q` are idempotent. -/
theorem sq_sub_commute_right {P Q : Matrix n n R} (hP : IsIdempotentElem P)
    (hQ : IsIdempotentElem Q) : Commute ((P - Q) ^ 2) Q := by
  have h := sq_sub_commute_left hQ hP
  rwa [← neg_sub, neg_sq] at h

/-- `(P - Q) (P - Q)² = (P - Q) - (P Q P - Q P Q)` when `P` and `Q` are idempotent. -/
theorem sub_mul_sq_sub {P Q : Matrix n n R} (hP : IsIdempotentElem P)
    (hQ : IsIdempotentElem Q) : (P - Q) * (P - Q) ^ 2 = (P - Q) - (P * Q * P - Q * P * Q) := by
  have hP' : P * P = P := hP
  have hQ' : Q * Q = Q := hQ
  simp only [sq, sub_mul, mul_sub, Matrix.mul_assoc, hP', hQ']
  simp only [← Matrix.mul_assoc, hP', hQ']
  abel

omit [DecidableEq n] in
/-- If `D` commutes with the idempotents `P` and `Q`, then `tr (D P Q P) = tr (D Q P Q)`: both
equal `tr (D P Q)`, by cyclicity of the trace. -/
theorem trace_mul_PQP {P Q D : Matrix n n R} (hP : IsIdempotentElem P)
    (hQ : IsIdempotentElem Q) (hDP : Commute D P) (hDQ : Commute D Q) :
    trace (D * P * Q * P) = trace (D * Q * P * Q) := by
  have hP' : P * P = P := hP
  have hQ' : Q * Q = Q := hQ
  have e1 : trace (D * P * Q * P) = trace (D * P * Q) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hDP.eq, Matrix.mul_assoc D,
      hP']
  have e2 : trace (D * Q * P * Q) = trace (D * Q * P) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hDQ.eq, Matrix.mul_assoc D,
      hQ']
  have e3 : trace (D * Q * P) = trace (D * P * Q) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, ← hDP.eq]
  rw [e1, e2, e3]

/-- **Answer, in finite dimension, to the question of Quillen, notebook 1983-10, p. 31.** For
idempotent square matrices `P` and `Q` over a commutative ring, the trace of every odd power of
`P - Q` is `tr P - tr Q`. No hypothesis on the characteristic. -/
theorem trace_sub_pow_odd {P Q : Matrix n n R} (hP : IsIdempotentElem P)
    (hQ : IsIdempotentElem Q) (k : ℕ) :
    trace ((P - Q) ^ (2 * k + 1)) = trace P - trace Q := by
  have hpow : ∀ k : ℕ, (P - Q) ^ (2 * k + 1) = ((P - Q) ^ 2) ^ k * (P - Q) := by
    intro k; rw [pow_succ, pow_mul]
  induction k with
  | zero => simp [trace_sub]
  | succ k ih =>
    set C := (P - Q) ^ 2
    have hCP : Commute (C ^ k) P := (sq_sub_commute_left hP hQ).pow_left k
    have hCQ : Commute (C ^ k) Q := (sq_sub_commute_right hP hQ).pow_left k
    have step : (P - Q) ^ (2 * (k + 1) + 1)
        = (P - Q) ^ (2 * k + 1) - (C ^ k * P * Q * P - C ^ k * Q * P * Q) := by
      have hc : C * (P - Q) = (P - Q) * C := (Commute.pow_self (P - Q) 2).eq
      rw [hpow, hpow, pow_succ, Matrix.mul_assoc, hc, sub_mul_sq_sub hP hQ]
      simp only [mul_sub, Matrix.mul_assoc]
    rw [step, trace_sub, ih, trace_sub, trace_mul_PQP hP hQ hCP hCQ, sub_self, sub_zero]

end Quillen.Notebook1983_10
