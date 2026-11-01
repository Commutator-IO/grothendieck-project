import Mathlib

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
-/

open TensorProduct

namespace Bourbaki.Redaction355

variable {A : Type*} [CommRing A] {F : Type*} [AddCommGroup F] [Module A F]

/-- Multiplication by `a ∉ p` is injective on `F / pF` when `F` is flat. -/
theorem mem_smul_top_of_smul_mem [Module.Flat A F] {p : Ideal A} [p.IsPrime] {a : A}
    (ha : a ∉ p) {x : F} (hx : a • x ∈ p • (⊤ : Submodule A F)) :
    x ∈ p • (⊤ : Submodule A F) := by
  set e := quotTensorEquivQuotSMul F p
  -- multiplication by `a` on `A/p` is injective, since `A/p` is a domain
  have hf : Function.Injective (LinearMap.lsmul A (A ⧸ p) a) := by
    intro u v huv
    have h : Ideal.Quotient.mk p a * u = Ideal.Quotient.mk p a * v := by
      simpa [Algebra.smul_def] using huv
    refine mul_left_cancel₀ ?_ h
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hinj : Function.Injective (fun t : (A ⧸ p) ⊗[A] F => a • t) := by
    have := Module.Flat.rTensor_preserves_injective_linearMap (M := F) _ hf
    convert this using 1
    funext t
    induction t using TensorProduct.inductionOn with
    | tmul u y => simp [TensorProduct.smul_tmul']
    | add u v hu hv => simp only [smul_add, map_add] at hu hv ⊢; rw [hu, hv]
  have hx0 : a • (Submodule.Quotient.mk x : F ⧸ p • (⊤ : Submodule A F)) = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact hx
  have key : e.symm (Submodule.Quotient.mk x) = 0 := by
    apply hinj
    simp only [smul_zero]
    rw [← map_smul, hx0, map_zero]
  rw [← Submodule.Quotient.mk_eq_zero, ← e.symm.map_eq_zero_iff]
  exact key

variable {B : Type*} [CommRing B] [Algebra A B] [Module B F] [IsScalarTower A B F]

/-- **Prop. 1.** Let `F` be a `B`-module, flat over `A`, `p` a prime of `A`, and `N` a
`B`-submodule of `F` whose underlying `A`-submodule is `pF`. Every associated prime `P` of the
`B`-module `F/N` lies over `p`. -/
theorem comap_eq_of_isAssociatedPrime [Module.Flat A F] {p : Ideal A} [hp : p.IsPrime]
    {N : Submodule B F} (hN : N.restrictScalars A = p • (⊤ : Submodule A F)) {P : Ideal B}
    (hP : N.IsAssociatedPrime P) : P.comap (algebraMap A B) = p := by
  obtain ⟨hPp, x, rfl⟩ := hP
  have memN : ∀ y : F, y ∈ N ↔ y ∈ p • (⊤ : Submodule A F) := fun y => by
    rw [← hN]; rfl
  ext a
  rw [Ideal.mem_comap, Ideal.mem_radical_iff]
  constructor
  · rintro ⟨n, hn⟩
    rw [Submodule.mem_colon_singleton, ← map_pow, algebraMap_smul, memN] at hn
    by_contra ha
    have hx : x ∈ N :=
      (memN x).2 (mem_smul_top_of_smul_mem (fun h => ha (hp.mem_of_pow_mem n h)) hn)
    apply hPp.ne_top
    rw [Ideal.eq_top_iff_one, Ideal.mem_radical_iff]
    exact ⟨1, by rw [Submodule.mem_colon_singleton, one_pow, one_smul]; exact hx⟩
  · intro ha
    refine ⟨1, ?_⟩
    rw [pow_one, Submodule.mem_colon_singleton, algebraMap_smul, memN]
    exact Submodule.smul_mem_smul ha trivial

/-- The `B`-submodule `(pB) F` has underlying `A`-submodule `pF`, so Prop. 1 applies to the
`B`-module `F / pF`. -/
theorem smulTop_restrictScalars (p : Ideal A) :
    ((p.map (algebraMap A B)) • (⊤ : Submodule B F)).restrictScalars A =
      p • (⊤ : Submodule A F) := by
  rw [Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

end Bourbaki.Redaction355
