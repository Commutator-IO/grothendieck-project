import Mathlib

/-!
# Quillen, notebook 1973-8: cancelling a free summand along a unimodular vector

Daniel Quillen's research notebook 1973-8 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201973/1973-8.pdf>).

* p. 27: if `f : A × M ≃ A × M'` and the first coordinate of `f(1, m)` is a unit, then
  `M ≃ M'` (`nonempty_equiv`), by the explicit inverse pair `proj m' ∘ f ∘ inr`,
  `proj m ∘ f⁻¹ ∘ inr` with `proj m (a, n) = n − a m` (`proj_symm_proj`).
-/

namespace Quillen.Notebook1973_8Splitting

variable {A M M' : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup M']
  [Module A M']

/-- The projection `A × M → M` with kernel `A·(1, m)`: `(a, n) ↦ n − a m`. -/
def proj (m : M) : A × M →ₗ[A] M :=
  LinearMap.snd A A M - LinearMap.toSpanSingleton A M m ∘ₗ LinearMap.fst A A M

@[simp] theorem proj_apply (m : M) (x : A × M) : proj m x = x.2 - x.1 • m := rfl

theorem sub_proj (m : M) (x : A × M) : x - (0, proj m x) = x.1 • ((1 : A), m) := by
  ext <;> simp

/-- If `f⁻¹(1, m') ∈ A·(1, m)`, then `proj m ∘ f⁻¹ ∘ inr` is a left inverse of
`proj m' ∘ f ∘ inr`. -/
theorem proj_symm_proj (f : (A × M) ≃ₗ[A] (A × M')) {m : M} {m' : M'} {c : A}
    (hf : f.symm ((1 : A), m') = c • ((1 : A), m)) (n : M) :
    proj m (f.symm (0, proj m' (f (0, n)))) = n := by
  have := congrArg f.symm (sub_proj m' (f (0, n)))
  rw [map_sub, map_smul, LinearEquiv.symm_apply_apply, hf, sub_eq_iff_eq_add] at this
  rw [eq_sub_of_add_eq' this.symm]; simp [smul_smul]

/-- **p. 27.** If `f : A × M ≃ A × M'` and `f(1, m) = (u, m')` with `u` a unit, then `M ≃ M'`. -/
theorem nonempty_equiv (f : (A × M) ≃ₗ[A] (A × M')) (m : M) (hu : IsUnit (f (1, m)).1) :
    Nonempty (M ≃ₗ[A] M') := by
  obtain ⟨u, hu⟩ := hu
  set m' := ((u⁻¹ : Aˣ) : A) • (f (1, m)).2
  have hf : f (1, m) = (u : A) • ((1 : A), m') := by
    ext <;> simp [m', ← hu, smul_smul]
  have hf' : f.symm ((1 : A), m') = ((u⁻¹ : Aˣ) : A) • ((1 : A), m) := by
    rw [f.symm_apply_eq, map_smul, hf, smul_smul]; simp
  exact ⟨.ofLinearMap (proj m' ∘ₗ f.toLinearMap ∘ₗ LinearMap.inr A A M)
    (proj m ∘ₗ f.symm.toLinearMap ∘ₗ LinearMap.inr A A M')
    (LinearMap.ext fun n => proj_symm_proj f.symm (by simpa using hf) n)
    (LinearMap.ext fun n => proj_symm_proj f hf' n)⟩

end Quillen.Notebook1973_8Splitting
