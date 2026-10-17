import Mathlib

/-!
# Folder 82, pages 77–78: the conic in characteristic 2 and Frobenius, split case

The modernised reading `transcripts/82/82.modern.tex` (« Caractéristique 2 : le Frobenius »,
pages 77 and 78) takes, over a base where `2 = 0`, the module `g̃` of traceless `2 × 2`
matrices with `φ(u, v) = Tr(uv)`. Since `Tr 1 = 2 = 0`, `𝒪_S · 1 ⊂ g̃` and it is the kernel
of `φ` (58). The morphism (59) sends a Borel, that is an isotropic line `L ⊂ g̃` (an element
of square zero), to its `φ`-orthogonal; every such hyperplane contains `1`, so (59) factors
through `P(g̃/𝒪_S)` (60), and the page states that (60) is the relative Frobenius, not a
monomorphism. The edition checks it in the split case (footnote): with `X̃ = E₁₂`,
`Ỹ = E₂₁`, `H̃ = diag(1, −1)`, the conic `xy = z²` is parametrised by `(s : t) ↦ (s², t², st)`
and the orthogonal of `𝒪(s²X̃ + t²Ỹ + stH̃)` is the hyperplane `t²x + s²y = 0`, which
contains `H̃ = 1` and depends only on `(s² : t²)`.

This is finding `82-char2-conic-frobenius` of `src/content/findings.ts`, in the split case,
over any commutative ring `R` with `2 = 0`, for the coordinates `u = xX̃ + yỸ + zH̃`.

* `coord_mul_self`: `u² = (xy + z²) · 1`, so `u` has square zero iff `xy = z²` in
  characteristic 2: the conic.
* `traceless_iff`: `g̃` is the set of the `coord x y z`.
* `tH_eq_one`, `one_mem_traceless`, `ker_phi` (58): `H̃ = 1`, and `1` spans the kernel of
  `φ` on `g̃`.
* `vst_mul_self`: `s²X̃ + t²Ỹ + stH̃` has square zero, a point of the conic.
* `trace_mul_vst`, `orth_iff`: its orthogonal is `t²x + s²y = 0`, which contains `1`
  (`one_mem_orth`).
* `orth_smul`: it depends only on `(s² : t²)`, so (60) is `(s : t) ↦ (s² : t²)`.
* `not_mono`: over `R = 𝔽₂[ε]/(ε²)` the distinct points `(1 : ε)` and `(1 : 0)` of `P¹(R)`
  have the same orthogonal hyperplane: (60) is not a monomorphism.

The canonical isomorphism (61) `P(g̃/𝒪_S) ≃ X^{(2)}` for a twisted conic over an arbitrary
base is not formalised: mathlib has neither conics over a base nor the relative Frobenius.
-/

open Matrix

namespace Folder82

variable {R : Type*} [CommRing R]

/-- `xX̃ + yỸ + zH̃` with `X̃ = E₁₂`, `Ỹ = E₂₁`, `H̃ = diag(1, −1)`. -/
def coord (x y z : R) : Matrix (Fin 2) (Fin 2) R := !![z, x; y, -z]

/-- `H̃ = diag(1, −1)`. -/
def tH : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]

/-- The generator `s²X̃ + t²Ỹ + stH̃` of the isotropic line of the point `(s : t)`. -/
def vst (s t : R) : Matrix (Fin 2) (Fin 2) R := coord (s ^ 2) (t ^ 2) (s * t)

theorem coord_eq (x y z : R) :
    coord x y z = x • !![0, 1; 0, 0] + y • !![0, 0; 1, 0] + z • tH := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord, tH]

/-- `u² = (xy + z²) · 1`: `u` has square zero iff `xy + z² = 0`. -/
theorem coord_mul_self (x y z : R) :
    coord x y z * coord x y z = (x * y + z ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord] <;> ring

/-- `g̃`, the traceless matrices, are the `coord x y z`. -/
theorem traceless_iff (u : Matrix (Fin 2) (Fin 2) R) :
    u.trace = 0 ↔ ∃ x y z, u = coord x y z := by
  refine ⟨fun h => ⟨u 0 1, u 1 0, u 0 0, ?_⟩, ?_⟩
  · rw [trace_fin_two] at h
    ext i j; fin_cases i <;> fin_cases j <;> simp [coord]; linear_combination h
  · rintro ⟨x, y, z, rfl⟩
    simp [coord, trace_fin_two]

/-- In characteristic 2, `H̃ = 1`. -/
theorem tH_eq_one (h2 : (2 : R) = 0) : (tH : Matrix (Fin 2) (Fin 2) R) = 1 := by
  have : (-1 : R) = 1 := by linear_combination -h2
  ext i j; fin_cases i <;> fin_cases j <;> simp [tH, this]

/-- (58): in characteristic 2, `1 ∈ g̃`. -/
theorem one_mem_traceless (h2 : (2 : R) = 0) : (1 : Matrix (Fin 2) (Fin 2) R).trace = 0 := by
  simp [h2]

/-- (58): in characteristic 2, the kernel of `φ(u, v) = Tr(uv)` on `g̃` is `R · 1`. -/
theorem ker_phi (h2 : (2 : R) = 0) (x y z : R) :
    (∀ v : Matrix (Fin 2) (Fin 2) R, v.trace = 0 → (coord x y z * v).trace = 0) ↔
      ∃ c : R, coord x y z = c • 1 := by
  constructor
  · intro h
    have h1 : y = 0 := by
      simpa [coord, trace_fin_two] using h (coord 1 0 0) (by simp [coord, trace_fin_two])
    have h2' : x = 0 := by
      simpa [coord, trace_fin_two] using h (coord 0 1 0) (by simp [coord, trace_fin_two])
    refine ⟨z, ?_⟩
    have hz : -z = z := by linear_combination (-z) * h2
    ext i j; fin_cases i <;> fin_cases j <;> simp [coord, h1, h2', hz]
  · rintro ⟨c, hc⟩ v hv
    rw [hc, smul_mul_assoc, one_mul, trace_smul, hv, smul_zero]

/-- The point `(s : t)`: `s²X̃ + t²Ỹ + stH̃` has square zero in characteristic 2. -/
theorem vst_mul_self (h2 : (2 : R) = 0) (s t : R) : vst s t * vst s t = 0 := by
  rw [vst, coord_mul_self]
  have : s ^ 2 * t ^ 2 + (s * t) ^ 2 = 2 * (s * t) ^ 2 := by ring
  rw [this, h2, zero_mul, zero_smul]

/-- `φ(u, s²X̃ + t²Ỹ + stH̃) = t²x + s²y` in characteristic 2. -/
theorem trace_mul_vst (h2 : (2 : R) = 0) (x y z s t : R) :
    (coord x y z * vst s t).trace = t ^ 2 * x + s ^ 2 * y := by
  simp only [vst, coord, trace_fin_two, mul_fin_two, of_apply, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one]
  linear_combination (z * s * t) * h2

/-- The orthogonal of the isotropic line of `(s : t)` is the hyperplane `t²x + s²y = 0`. -/
theorem orth_iff (h2 : (2 : R) = 0) (x y z s t : R) :
    (coord x y z * vst s t).trace = 0 ↔ t ^ 2 * x + s ^ 2 * y = 0 := by
  rw [trace_mul_vst h2]

/-- It contains `1 = H̃`, so (59) factors through `P(g̃/𝒪_S)`. -/
theorem one_mem_orth (h2 : (2 : R) = 0) (s t : R) : ((1 : Matrix (Fin 2) (Fin 2) R) *
    vst s t).trace = 0 := by
  rw [← tH_eq_one h2, show (tH : Matrix (Fin 2) (Fin 2) R) = coord 0 0 1 by
    simp [tH, coord], orth_iff h2]
  ring

/-- It depends only on `(s² : t²)`: (60) is `(s : t) ↦ (s² : t²)`. -/
theorem orth_smul (h2 : (2 : R) = 0) {s t s' t' c : R} (hs : s' ^ 2 = c * s ^ 2)
    (ht : t' ^ 2 = c * t ^ 2) (x y z : R) :
    (coord x y z * vst s' t').trace = c * (coord x y z * vst s t).trace := by
  rw [trace_mul_vst h2, trace_mul_vst h2, hs, ht]
  ring

/-- (60) is not a monomorphism: over `𝔽₂[ε]/(ε²)` the points `(1 : ε)` and `(1 : 0)` of
`P¹` are distinct (no unit carries one pair to the other), and their isotropic lines have
the same orthogonal hyperplane. -/
theorem not_mono :
    (¬ ∃ c : (DualNumber (ZMod 2))ˣ,
        (1 : DualNumber (ZMod 2)) = c * 1 ∧ DualNumber.eps = (c : DualNumber (ZMod 2)) * 0) ∧
      ∀ x y z : DualNumber (ZMod 2),
        (coord x y z * vst 1 DualNumber.eps).trace = (coord x y z * vst 1 0).trace := by
  have h2 : (2 : DualNumber (ZMod 2)) = 0 := by
    ext <;> simp <;> rfl
  refine ⟨?_, fun x y z => ?_⟩
  · rintro ⟨c, -, h⟩
    rw [mul_zero] at h
    have := congrArg TrivSqZeroExt.snd h
    simp at this
  · rw [trace_mul_vst h2, trace_mul_vst h2, sq, DualNumber.eps_mul_eps]
    ring

end Folder82
