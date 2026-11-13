import Mathlib

/-!
# Quillen, notebook 1989-2, pp. 28, 30, 84: conjugations in `M₂(A)` and composition of triples

Daniel Quillen's research notebook 1989-2 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201989/1989-2.pdf>).
The identities by which Quillen reduces the action of inner automorphisms on cyclic homology to
elementary matrices, and the category of homotopy equivalences of p. 84, in any ring `A` (not
necessarily commutative).

* p. 28: `u_z(a) = (a, az; 0, 0)` is multiplicative (`uz_mul`) and conjugate to
  `u_0(a) = (a, 0; 0, 0)` by `(1, −z; 0, 1)` (`uz_conj`);
* p. 30: `diag(u, u⁻¹) · diag(a, 0) · diag(u, u⁻¹)⁻¹ = diag(uau⁻¹, 0)` (`diag_conj`), and
  Whitehead's identity `(1, u; 0, 1)(1, 0; −u⁻¹, 1)(1, u; 0, 1) = (0, u; −u⁻¹, 0)`
  (`whitehead`), with `(0, u; −u⁻¹, 0)² = −1` besides;
* p. 84: triples `(u, v, h)` with `vu = 1 + [d, h]` (`dh + hd`) and `u`, `v` commuting with
  `d` compose, `(u, v, h) ∘ (u', v', h') = (u'u, vv', h + vh'u)` (`comp_spec`), and composition
  is associative (`comp_assoc`, Quillen's check) with identity `(1, 1, 0)`.
-/

namespace Quillen.Notebook1989_2Whitehead

open Matrix

variable {A : Type*} [Ring A]

/-- `u_z(a) = (1; 0) a (1, z)`. -/
def uz (z a : A) : Matrix (Fin 2) (Fin 2) A := !![a, a * z; 0, 0]

theorem uz_mul (z a b : A) : uz z a * uz z b = uz z (a * b) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [uz, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

/-- `(1, −z; 0, 1) · (a, 0; 0, 0) · (1, z; 0, 1) = u_z(a)`. -/
theorem uz_conj (z a : A) :
    !![1, -z; 0, 1] * !![a, 0; 0, 0] * !![1, z; 0, 1] = uz z a := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [uz, Matrix.mul_apply, Fin.sum_univ_two]

/-- `diag(u, u⁻¹) · diag(a, 0) · diag(u⁻¹, u) = diag(uau⁻¹, 0)`. -/
theorem diag_conj (u : Aˣ) (a : A) :
    !![(u : A), 0; 0, ((u⁻¹ : Aˣ) : A)] * !![a, 0; 0, 0] * !![((u⁻¹ : Aˣ) : A), 0; 0, (u : A)] =
      !![(u : A) * a * ((u⁻¹ : Aˣ) : A), 0; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

theorem diag_inv (u : Aˣ) :
    !![(u : A), 0; 0, ((u⁻¹ : Aˣ) : A)] * !![((u⁻¹ : Aˣ) : A), 0; 0, (u : A)] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Whitehead's identity** (p. 30): `(1, u; 0, 1)(1, 0; −u⁻¹, 1)(1, u; 0, 1) = (0, u; −u⁻¹, 0)`. -/
theorem whitehead (u : Aˣ) :
    !![1, (u : A); 0, 1] * !![1, 0; -((u⁻¹ : Aˣ) : A), 1] * !![1, (u : A); 0, 1] =
      !![0, (u : A); -((u⁻¹ : Aˣ) : A), 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem whitehead_sq (u : Aˣ) :
    !![0, (u : A); -((u⁻¹ : Aˣ) : A), 0] * !![0, (u : A); -((u⁻¹ : Aˣ) : A), 0] = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ### The category of triples (p. 84) -/

variable (d : A)

/-- `(u, v, h)` is a homotopy equivalence datum for `d`: `u`, `v` commute with `d` and
`vu = 1 + dh + hd`. -/
def IsTriple (u v h : A) : Prop := d * u = u * d ∧ d * v = v * d ∧ v * u = 1 + (d * h + h * d)

/-- The composite of triples: `vv'u'u = 1 + [d, h + vh'u]`. -/
theorem comp_spec {u v h u' v' h' : A} (t : IsTriple d u v h) (t' : IsTriple d u' v' h') :
    IsTriple d (u' * u) (v * v') (h + v * h' * u) := by
  obtain ⟨hu, hv, hvu⟩ := t
  obtain ⟨hu', hv', hvu'⟩ := t'
  refine ⟨?_, ?_, ?_⟩
  · rw [← mul_assoc, hu', mul_assoc, hu, mul_assoc]
  · rw [← mul_assoc, hv, mul_assoc, hv', mul_assoc]
  · have e1 : v * v' * (u' * u) = v * (v' * u') * u := by noncomm_ring
    have e2 : d * (v * h' * u) = v * (d * h') * u := by
      rw [← mul_assoc, ← mul_assoc, hv, mul_assoc v d, mul_assoc]
    have e3 : v * h' * u * d = v * (h' * d) * u := by
      rw [mul_assoc (v * h') u d, ← hu]; noncomm_ring
    rw [e1, hvu', mul_add, add_mul, mul_one, hvu, mul_add d, add_mul _ _ d, e2, e3]
    noncomm_ring

/-- The identity triple `(1, 1, 0)`. -/
theorem id_spec : IsTriple d 1 1 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

/-- **Associativity** (p. 84): `(h + vh'u) + (vv')h''(u'u) = h + v(h' + v'h''u')u`. -/
theorem comp_assoc (u v h u' v' h' h'' : A) :
    (h + v * h' * u) + (v * v') * h'' * (u' * u) = h + v * (h' + v' * h'' * u') * u := by
  noncomm_ring

end Quillen.Notebook1989_2Whitehead
