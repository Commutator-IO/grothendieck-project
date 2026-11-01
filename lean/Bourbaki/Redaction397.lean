import Bourbaki.Upstream.InjectiveIffDivisible

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

The proofs are general and live in `Bourbaki/Upstream/InjectiveIffDivisible.lean`
(`Module.Baer.of_smul_surjective`, `Module.injective_of_smul_surjective`,
`Module.Injective.smul_surjective`, `Module.injective_iff_smul_surjective`,
`Module.Injective.quotient`); the names below are kept for the articles that cite them.
-/

namespace Bourbaki.Redaction397

universe u

variable {R : Type u} [CommRing R] {Q : Type u} [AddCommGroup Q] [Module R Q]

/-- Over a commutative principal ideal ring, a divisible module satisfies Baer's criterion. -/
theorem baer_of_divisible [IsPrincipalIdealRing R]
    (hQ : ∀ r : R, r ≠ 0 → Function.Surjective (fun q : Q => r • q)) : Module.Baer R Q :=
  Module.Baer.of_smul_surjective hQ

/-- Over a commutative principal ideal ring, a divisible module is injective. -/
theorem injective_of_divisible [IsPrincipalIdealRing R]
    (hQ : ∀ r : R, r ≠ 0 → Function.Surjective (fun q : Q => r • q)) : Module.Injective R Q :=
  Module.injective_of_smul_surjective hQ

/-- Over a domain, an injective module is divisible. -/
theorem divisible_of_injective [IsDomain R] [Module.Injective R Q] :
    ∀ r : R, r ≠ 0 → Function.Surjective (fun q : Q => r • q) :=
  fun _ hr => Module.Injective.smul_surjective hr

/-- Over a principal ideal domain, injective means divisible. -/
theorem injective_iff_divisible [IsDomain R] [IsPrincipalIdealRing R] :
    Module.Injective R Q ↔ ∀ r : R, r ≠ 0 → Function.Surjective (fun q : Q => r • q) :=
  Module.injective_iff_smul_surjective

/-- The « corollary of the corollary » of rédaction 397: over a principal ideal domain, every
quotient of an injective module is injective. -/
theorem injective_quotient [IsDomain R] [IsPrincipalIdealRing R] [Module.Injective R Q]
    (N : Submodule R Q) : Module.Injective R (Q ⧸ N) :=
  Module.Injective.quotient N

end Bourbaki.Redaction397
