import Mathlib

/-!
# Bourbaki, rédaction n° 461 (February 1966): two misstatements in Chevalley's abelian categories

Rédaction 461 of the Bourbaki archive (Archives Henri Poincaré, item 1036) is Chevalley's draft
« Catégories abéliennes ». Two statements are false as typed; we check them in the abelian
category of `ℤ`-modules, where subobjects are submodules, direct and inverse images are
`Submodule.map` and `Submodule.comap`, and the cokernel of `f` is `M ⧸ range f`.

**Formula (6), p. 97.** For `λ : a → a'` and subobjects `x ⊂ a`, `x' ⊂ a'`, the page types
`λ(λ⁻¹(λ(x))) = λ(x)` and `λ⁻¹(λ(λ⁻¹(x'))) = x'`. The argument of the page gives
`λ⁻¹(λ(λ⁻¹(x'))) = λ⁻¹(x')` for the second.

* `comap_map_comap`: the correct second formula;
* `formula6_fails`: for `λ = 0 : ℤ → ℤ` and `x' = 0`, the left side is `ℤ`.

**Pp. 16–17, after Déf. 3.** The cokernel functors on the category of arrows are said to be
compatible with projective limits (and the kernel functors with inductive limits); the kinds of
limits are swapped. A functor compatible with projective limits preserves monomorphisms, and
the cokernel functor does not: the square from `0 → ℤ` to `id : ℤ → ℤ` has injective
components, but the induced map of cokernels `ℤ → 0` is not injective.

* `cokernel_map_not_injective`: that example.
-/

namespace Bourbaki.Redaction461Slips

section Formula6

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The correct second formula (6): `λ⁻¹(λ(λ⁻¹(x'))) = λ⁻¹(x')`. -/
theorem comap_map_comap (f : M →ₗ[R] N) (x' : Submodule R N) :
    ((x'.comap f).map f).comap f = x'.comap f :=
  le_antisymm (Submodule.comap_mono (Submodule.map_comap_le f x')) (Submodule.le_comap_map f _)

/-- **The typed second formula (6) fails**: for `λ = 0 : ℤ → ℤ` and `x' = 0`,
`λ⁻¹(λ(λ⁻¹(0))) = ℤ ≠ 0`. -/
theorem formula6_fails :
    (((⊥ : Submodule ℤ ℤ).comap (0 : ℤ →ₗ[ℤ] ℤ)).map (0 : ℤ →ₗ[ℤ] ℤ)).comap
      (0 : ℤ →ₗ[ℤ] ℤ) ≠ ⊥ := by
  rw [comap_map_comap]
  intro h
  have : (1 : ℤ) ∈ (⊥ : Submodule ℤ ℤ).comap (0 : ℤ →ₗ[ℤ] ℤ) := by simp
  rw [h, Submodule.mem_bot] at this
  exact one_ne_zero this

end Formula6

section Cokernel

/-- The zero map `0 → ℤ`. -/
abbrev f₀ : (Fin 0 → ℤ) →ₗ[ℤ] ℤ := 0

/-- The map of cokernels `ℤ ⧸ range f₀ → ℤ ⧸ range id` induced by the square with components
`0 → ℤ` (on sources) and `id` (on targets). -/
noncomputable abbrev cokerMap :
    (ℤ ⧸ LinearMap.range f₀) →ₗ[ℤ] (ℤ ⧸ LinearMap.range (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) :=
  (LinearMap.range f₀).mapQ _ LinearMap.id (by rintro _ ⟨y, rfl⟩; exact ⟨0, by simp⟩)

/-- **The cokernel functor does not preserve monomorphisms**: both components of the square are
injective, and the induced map of cokernels is not. -/
theorem cokernel_map_not_injective :
    Function.Injective f₀ ∧ Function.Injective (LinearMap.id : ℤ →ₗ[ℤ] ℤ) ∧
      ¬ Function.Injective cokerMap := by
  refine ⟨fun a b _ => Subsingleton.elim a b, Function.injective_id, fun h => ?_⟩
  have h1 : Submodule.Quotient.mk (p := LinearMap.range f₀) (1 : ℤ) = 0 := by
    apply h
    rw [map_zero, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨1, rfl⟩
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.range_zero, Submodule.mem_bot] at h1
  exact one_ne_zero h1

end Cokernel

end Bourbaki.Redaction461Slips
