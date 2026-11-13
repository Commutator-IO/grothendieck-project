import Mathlib

/-!
# Quillen, notebook 1988-1, pp. 73–77: the cocycle `tr(x [y, ρ])` attached to an extension

Daniel Quillen's research notebook 1988-1 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201988/1988-1.pdf>) builds, on
pp. 73–77, maps from `Ext` groups to duals of Hochschild homology by the cocycle
`(a₀, …, a_n) ↦ tr_M(a₀ [a₁, h] ⋯ [a_n, h])`, `h` a `k`-linear splitting. For `n = 1` and `A`
commutative, with `ρ` a `k`-linear endomorphism of `M` describing the extension, the cocycle
`φ(x, y) = tr(x [y, ρ])` kills the commutators and gives `Ext¹_A(M, M) → (Ω¹_A)*`: it is a
derivation in its second variable, so `x dy ↦ φ(x, y)` is well defined on `Ω¹_A`, and it does not
change when `ρ` is changed by an `A`-linear endomorphism.

This file proves these identities for matrices (`M = kⁿ`) over a commutative ring `k`, with
`x, y, z` in a commuting family:

* `phi ρ x y = tr(x (y ρ − ρ y))`;
* `phi_mul_right`: **the derivation property** `φ(x, y z) = φ(x y, z) + φ(x z, y)` when `x`
  and `z` commute (the Hochschild cocycle identity for commutative `A`);
* `phi_one`: `φ(x, 1) = 0`;
* `phi_add_of_commute`: **independence of the splitting**: `φ_{ρ + σ} = φ_ρ` when `σ` commutes
  with `y` (an `A`-linear change of `ρ`);
* `phi_antisymm`: `φ(x, y) = −φ(y, x)`.

The `Ext` groups, Kähler differentials and the residue are not formalised.
-/

namespace Quillen.Notebook1988_1Cocycle

open Matrix

variable {n k : Type*} [Fintype n] [CommRing k]

/-- `φ_ρ(x, y) = tr(x [y, ρ])`. -/
def phi (ρ x y : Matrix n n k) : k := trace (x * (y * ρ - ρ * y))

/-- **Quillen, notebook 1988-1, p. 75.** `φ(x, y z) = φ(x y, z) + φ(x z, y)` when `x` and `z`
commute. -/
theorem phi_mul_right (ρ : Matrix n n k) {x y z : Matrix n n k} (hxz : x * z = z * x) :
    phi ρ x (y * z) = phi ρ (x * y) z + phi ρ (x * z) y := by
  have key : ∀ w, trace (x * (w * z)) = trace (x * (z * w)) := fun w => by
    rw [← Matrix.mul_assoc x z, hxz, Matrix.mul_assoc, trace_mul_comm z, Matrix.mul_assoc]
  have h1 := key (y * ρ); have h2 := key (ρ * y)
  simp only [Matrix.mul_assoc] at h1 h2
  simp only [phi, mul_sub, trace_sub, Matrix.mul_assoc]
  rw [h1, h2]
  ring

theorem phi_one [DecidableEq n] (ρ x : Matrix n n k) : phi ρ x 1 = 0 := by
  simp [phi]

/-- **Independence of the splitting.** If `σ` commutes with `y`, then `φ_{ρ+σ}(x, y) = φ_ρ(x, y)`. -/
theorem phi_add_of_commute (ρ σ x y : Matrix n n k) (hσ : y * σ = σ * y) :
    phi (ρ + σ) x y = phi ρ x y := by
  unfold phi
  congr 2
  rw [mul_add, add_mul, hσ]
  abel

/-- `φ(x, y) = −φ(y, x)`: traces of commutators vanish. -/
theorem phi_antisymm (ρ x y : Matrix n n k) : phi ρ x y = -phi ρ y x := by
  have a1 : trace (x * (y * ρ)) = trace (y * (ρ * x)) := by
    rw [trace_mul_comm, Matrix.mul_assoc]
  have a2 : trace (x * (ρ * y)) = trace (y * (x * ρ)) := by
    rw [← Matrix.mul_assoc, trace_mul_comm]
  simp only [phi, mul_sub, trace_sub]
  rw [a1, a2]
  ring

end Quillen.Notebook1988_1Cocycle
