import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Bourbaki, rédaction n° 582 (Serre, June 1972), no. 3: the Schur indices over `ℝ`

Serre's report on the new edition of *Algèbre* VIII defines, for a simple `A`-module `S` with
`D = End(S)` of centre `L`, `[D : L] = e²` (Schur index `e`) and `[L : k] = m`, and gives the example
`k = ℝ`, `k' = ℂ`. The typescript gives `(m, e) = (2, 2)` for both `D = ℂ` and `D = ℍ`; with the
report's own definitions the values are `(m, e) = (2, 1)` for `D = ℂ` (`L = ℂ`) and `(1, 2)` for
`D = ℍ` (`L = ℝ`). This file checks the dimensions that decide it: `[ℂ : ℝ] = 2 = 2 · 1²` and
`[ℍ : ℝ] = 4 = 1 · 2²`. The centres (`ℂ` for `ℂ`, `ℝ` for `ℍ`) are taken as known, not formalised.
-/

open Quaternion

namespace Grothendieck.Bourbaki582

/-- `D = ℂ`: `m = [ℂ : ℝ] = 2` and `e = 1`, since `[D : L] = [ℂ : ℂ] = 1 = 1²`. -/
theorem schur_complex : Module.finrank ℝ ℂ = 2 * 1 ^ 2 := by
  simp [Complex.finrank_real_complex]

/-- `D = ℍ`: with centre `ℝ`, `m = 1` and `[ℍ : ℝ] = 4 = 2²`, so `e = 2`. -/
theorem schur_quaternion : Module.finrank ℝ ℍ[ℝ] = 1 * 2 ^ 2 := by
  simp [Quaternion.finrank_eq_four]

end Grothendieck.Bourbaki582
