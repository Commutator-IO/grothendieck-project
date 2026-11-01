import Bourbaki.Upstream.FlatAssociatedPrimes

/-!
# Bourbaki, rédaction n° 355 (January 1961): associated primes under a flat extension

Rédaction 355 of the Bourbaki archive (Archives Henri Poincaré, item 913) studies associated primes
under extension of scalars. Its setting is a ring map `A → B` and a `B`-module `F` that is flat
over `A`. Prop. 1, with no noetherian hypothesis: for a prime `p` of `A` and an associated prime
`P` of the `B`-module `F/pF`, the inverse image of `P` in `A` is `p`.

* `mem_smul_top_of_smul_mem`: if `F` is flat over `A`, `p` is prime and `a ∉ p`, then
  `a • x ∈ pF` forces `x ∈ pF` (multiplication by `a` is injective on `F/pF = (A/p) ⊗ F`);
* `comap_eq_of_isAssociatedPrime`: Prop. 1, for any `B`-submodule `N` of `F` whose underlying
  `A`-submodule is `pF` (associated primes taken in mathlib's sense, as radicals of annihilators);
* `smulTop_restrictScalars`: the `B`-submodule `(pB) F` has underlying `A`-submodule `pF`.

The proofs are general and live in `Bourbaki/Upstream/FlatAssociatedPrimes.lean`
(`Module.Flat.mem_smul_top_of_smul_mem`, `Submodule.IsAssociatedPrime.comap_eq_of_flat`,
`Ideal.restrictScalars_map_smul_top`); the names below are kept for the articles that cite them.
-/

namespace Bourbaki.Redaction355

variable {A : Type*} [CommRing A] {F : Type*} [AddCommGroup F] [Module A F]

/-- Multiplication by `a ∉ p` is injective on `F / pF` when `F` is flat. -/
theorem mem_smul_top_of_smul_mem [Module.Flat A F] {p : Ideal A} [p.IsPrime] {a : A}
    (ha : a ∉ p) {x : F} (hx : a • x ∈ p • (⊤ : Submodule A F)) :
    x ∈ p • (⊤ : Submodule A F) :=
  Module.Flat.mem_smul_top_of_smul_mem ha hx

variable {B : Type*} [CommRing B] [Algebra A B] [Module B F] [IsScalarTower A B F]

/-- **Prop. 1.** Let `F` be a `B`-module, flat over `A`, `p` a prime of `A`, and `N` a
`B`-submodule of `F` whose underlying `A`-submodule is `pF`. Every associated prime `P` of the
`B`-module `F/N` lies over `p`. -/
theorem comap_eq_of_isAssociatedPrime [Module.Flat A F] {p : Ideal A} [p.IsPrime]
    {N : Submodule B F} (hN : N.restrictScalars A = p • (⊤ : Submodule A F)) {P : Ideal B}
    (hP : N.IsAssociatedPrime P) : P.comap (algebraMap A B) = p :=
  hP.comap_eq_of_flat hN

/-- The `B`-submodule `(pB) F` has underlying `A`-submodule `pF`, so Prop. 1 applies to the
`B`-module `F / pF`. -/
theorem smulTop_restrictScalars (p : Ideal A) :
    ((p.map (algebraMap A B)) • (⊤ : Submodule B F)).restrictScalars A =
      p • (⊤ : Submodule A F) :=
  Ideal.restrictScalars_map_smul_top p

end Bourbaki.Redaction355
