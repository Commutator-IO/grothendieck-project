import Mathlib

/-!
# Bourbaki, rédaction n° 397 (April 1963): over a principal ideal ring, divisible means injective

Rédaction n° 397 of the Bourbaki archive (Archives Henri Poincaré, item 948), on injective modules
and duality over a principal ideal domain, proves Baer's criterion (its Prop. 2) and draws from it a
corollary: over a principal ideal domain a module is injective if and only if it is divisible, and,
as a « corollary of the corollary », every quotient of an injective module is injective. The
statements are classical (Lam, *Lectures on Modules and Rings*, § 3); mathlib has Baer's criterion
(`Module.Baer.injective`) and the case of `ℤ` (`Module.Baer.of_divisible`), not the general one.

Divisibility is stated without a new definition: `r • ·` is surjective on `Q` for every `r ≠ 0`.

* `baer_of_divisible`: over a commutative principal ideal ring, a divisible module satisfies Baer's
  criterion (no domain hypothesis is needed for this direction);
* `injective_of_divisible`: hence it is injective;
* `divisible_of_injective`: over a domain, an injective module is divisible;
* `injective_iff_divisible`: the equivalence, over a principal ideal domain;
* `injective_quotient`: a quotient of an injective module over a principal ideal domain is
  injective.
-/

namespace Bourbaki.Redaction397

universe u

variable {R : Type u} [CommRing R] {Q : Type u} [AddCommGroup Q] [Module R Q]

/-- Over a commutative principal ideal ring, a module on which every nonzero `r` acts
surjectively satisfies Baer's criterion: a map from the ideal `(a)` extends by `r ↦ r • q`, where
`a • q` is the image of `a`. -/
theorem baer_of_divisible [IsPrincipalIdealRing R]
    (hQ : ∀ r : R, r ≠ 0 → Function.Surjective (fun q : Q => r • q)) : Module.Baer R Q := by
  intro I g
  obtain ⟨a, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
  by_cases ha : a = 0
  · refine ⟨0, fun x hx => ?_⟩
    subst ha
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    simp only [LinearMap.zero_apply]
    rw [show (⟨0, hx⟩ : Ideal.span ({0} : Set R)) = 0 from rfl, map_zero]
  · obtain ⟨q, hq⟩ := hQ a ha (g ⟨a, Ideal.mem_span_singleton_self a⟩)
    refine ⟨LinearMap.toSpanSingleton R Q q, fun x hx => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    have : (⟨c * a, hx⟩ : Ideal.span ({a} : Set R)) = c • ⟨a, Ideal.mem_span_singleton_self a⟩ :=
      rfl
    simp only [LinearMap.toSpanSingleton_apply, this, map_smul]
    rw [← hq, smul_smul]

/-- Over a commutative principal ideal ring, a divisible module is injective. -/
theorem injective_of_divisible [IsPrincipalIdealRing R]
    (hQ : ∀ r : R, r ≠ 0 → Function.Surjective (fun q : Q => r • q)) : Module.Injective R Q :=
  (baer_of_divisible hQ).injective

/-- Over a domain, an injective module is divisible: the map `r • c ↦ c • q` on the ideal `(r)`
extends to `R`, and the image of `1` is a solution of `r • x = q`. -/
theorem divisible_of_injective [IsDomain R] [Module.Injective R Q] :
    ∀ r : R, r ≠ 0 → Function.Surjective (fun q : Q => r • q) := by
  intro r hr q
  have hB : Module.Baer R Q := Module.Baer.of_injective inferInstance
  let e : R ≃ₗ[R] Ideal.span ({r} : Set R) :=
    LinearEquiv.toSpanNonzeroSingleton R R r hr
  obtain ⟨g', hg'⟩ := hB _ ((LinearMap.toSpanSingleton R Q q).comp e.symm.toLinearMap)
  refine ⟨g' 1, ?_⟩
  have h1 := hg' r (Ideal.mem_span_singleton_self r)
  have he : e 1 = ⟨r, Ideal.mem_span_singleton_self r⟩ := by
    ext; simp [e, LinearEquiv.toSpanNonzeroSingleton]
  have : e.symm ⟨r, Ideal.mem_span_singleton_self r⟩ = 1 := by
    rw [← he, LinearEquiv.symm_apply_apply]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this,
    LinearMap.toSpanSingleton_apply, one_smul] at h1
  simp only
  rw [← h1, ← map_smul, smul_eq_mul, mul_one]

/-- Over a principal ideal domain, injective means divisible. -/
theorem injective_iff_divisible [IsDomain R] [IsPrincipalIdealRing R] :
    Module.Injective R Q ↔ ∀ r : R, r ≠ 0 → Function.Surjective (fun q : Q => r • q) :=
  ⟨fun _ => divisible_of_injective, injective_of_divisible⟩

/-- The « corollary of the corollary » of rédaction 397: over a principal ideal domain, every
quotient of an injective module is injective. -/
theorem injective_quotient [IsDomain R] [IsPrincipalIdealRing R] [Module.Injective R Q]
    (N : Submodule R Q) : Module.Injective R (Q ⧸ N) := by
  refine injective_of_divisible fun r hr x => ?_
  obtain ⟨q, rfl⟩ := N.mkQ_surjective x
  obtain ⟨q', hq'⟩ := divisible_of_injective r hr q
  exact ⟨N.mkQ q', by simp only [← map_smul]; exact congrArg _ hq'⟩

end Bourbaki.Redaction397
