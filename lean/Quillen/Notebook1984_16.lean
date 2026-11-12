import Mathlib

/-!
# Quillen, notebook 1984-16, pp. 19–20: a homotopy to an invertible operator kills cohomology

Daniel Quillen's research notebook 1984-16 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201984/1984-16.pdf>) shows, on
pp. 19–20, that the Witten cohomology of the `S¹`-invariant forms on a manifold with a free
circle action vanishes: for `d_a = d + a ι_X`, `a ≠ 0`, and a connection form `θ`, the
anticommutator `[d_a, θ] = d_a θ + θ d_a` is multiplication by `dθ + a`, which is invertible
because `dθ` is nilpotent; a contracting homotopy to an invertible operator kills cohomology.

This file proves the algebra, for endomorphisms of a module `M` over a commutative ring `R`:

* `ker_eq_range_of_homotopy`: if `δ² = 0` and `δ K + K δ = u` with `u` invertible and commuting
  with `δ`, then `ker δ = range δ`;
* `ker_eq_range_witten`: **the statement of the page**: if `D² = 0` and `D T + T D = N + a` with
  `N` nilpotent, commuting with `D`, and `a ∈ R` a unit, then `ker D = range D`.

The forms, the circle action and the identity `[d_a, θ] = dθ + a` are not formalised.
-/

namespace Quillen.Notebook1984_16

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A contracting homotopy to an invertible operator commuting with `δ` makes `δ` exact. -/
theorem ker_eq_range_of_homotopy {δ K u : Module.End R M} (hδ : δ * δ = 0)
    (hK : δ * K + K * δ = u) (hu : IsUnit u) (hc : Commute u δ) :
    LinearMap.ker δ = LinearMap.range δ := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨v, rfl⟩ := hu
    have hc' : Commute (↑v⁻¹ : Module.End R M) δ := hc.units_inv_left
    refine ⟨(↑v⁻¹ * K) x, ?_⟩
    have hux : (v : Module.End R M) x = δ (K x) := by
      rw [← hK, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hx, map_zero,
        add_zero]
    calc δ ((↑v⁻¹ * K) x) = (δ * ↑v⁻¹) (K x) := rfl
      _ = (↑v⁻¹ * δ) (K x) := by rw [hc'.eq]
      _ = (↑v⁻¹ : Module.End R M) ((v : Module.End R M) x) := by
        rw [Module.End.mul_apply, hux]
      _ = x := by rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, hδ, LinearMap.zero_apply]

/-- **Quillen, notebook 1984-16, pp. 19–20.** If `D² = 0` and `D T + T D = N + a` with `N`
nilpotent and commuting with `D`, and `a` a unit of `R`, then `ker D = range D`. -/
theorem ker_eq_range_witten {D T N : Module.End R M} {a : R} (hD : D * D = 0)
    (hDT : D * T + T * D = N + algebraMap R (Module.End R M) a) (hN : IsNilpotent N)
    (ha : IsUnit a) (hND : Commute N D) :
    LinearMap.ker D = LinearMap.range D := by
  have hcomm : ∀ X : Module.End R M, Commute (algebraMap R (Module.End R M) a) X :=
    fun X => Algebra.commutes a X
  have hu : IsUnit (N + algebraMap R (Module.End R M) a) :=
    hN.isUnit_add_right_of_commute (ha.map _) (hcomm N).symm
  exact ker_eq_range_of_homotopy hD hDT hu (hND.add_left (hcomm D))

end Quillen.Notebook1984_16
