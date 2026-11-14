import Mathlib

/-!
# Quillen, notebook 1972-8: `1 − σ` on `k'^×` and weights on `Λ^q`

Daniel Quillen's research notebook 1972-8 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201972/1972-8.pdf>).

* p. 20: for a subfield `k` of a finite field `K`, `|k| = q`, the map `z ↦ σ(z)/z = z^{q−1}`
  of `K^×` (`oneSubFrob`, `oneSubFrob_apply`) has kernel `k^×` (`ker_eq`) of order `q − 1`
  (`card_ker`) and cokernel of order `q − 1` (`index_range`).
* p. 30: multiplication by `λ` on `M` induces multiplication by `λ^q` on `⋀^q M`
  (`exteriorPower_map_smul`).

The orders `denom(B_s/4s)` of the image of `J` listed on p. 12 are proved in
`Quillen.Notebook1972_6.den_bernoulli_div`.
-/

namespace Quillen.Notebook1972_8

variable {K : Type*} [Field K] [Finite K] (k : Subfield K)

/-- `1 − σ` on `K^×`, written multiplicatively: `z ↦ σ(z)/z = z^{q−1}`, `σ` the `q`-Frobenius. -/
noncomputable abbrev oneSubFrob : Kˣ →* Kˣ := powMonoidHom (Nat.card k - 1)

theorem oneSubFrob_apply (z : Kˣ) : (oneSubFrob k z : K) = (z : K) ^ Nat.card k / z := by
  rw [eq_div_iff z.ne_zero, powMonoidHom_apply, Units.val_pow_eq_pow_val, ← pow_succ,
    Nat.sub_add_cancel Nat.card_pos]

theorem card_sub_one_dvd : Nat.card k - 1 ∣ Nat.card Kˣ := by
  have := Fintype.ofFinite K
  have := Fintype.ofFinite k
  rw [Nat.card_units, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := k) (V := K)]
  simpa using Nat.sub_dvd_pow_sub_pow (Fintype.card k) 1 (Module.finrank k K)

/-- **p. 20.** The kernel of `1 − σ` on `K^×` has order `q − 1`. -/
theorem card_ker : Nat.card (oneSubFrob k).ker = Nat.card k - 1 := by
  rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right (card_sub_one_dvd k)]

/-- **p. 20.** The cokernel of `1 − σ` on `K^×` has order `q − 1`. -/
theorem index_range : (oneSubFrob k).range.index = Nat.card k - 1 := by
  rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right (card_sub_one_dvd k)]

/-- **p. 20.** The kernel of `1 − σ` is `k^×`. -/
theorem ker_eq : (oneSubFrob k).ker = (Units.map k.subtype.toMonoidHom).range := by
  have := Fintype.ofFinite k
  have hinj : Function.Injective (Units.map k.subtype.toMonoidHom) := fun a b h =>
    Units.ext (Subtype.ext (by simpa using congrArg Units.val h))
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · rintro _ ⟨a, rfl⟩
    have := FiniteField.pow_card_sub_one_eq_one (a : k) a.ne_zero
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow, Nat.card_eq_fintype_card,
      show a ^ (Fintype.card k - 1) = 1 from Units.ext (by simpa using this), map_one]
  · rw [card_ker, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units]

/-- **p. 30.** Multiplication by `λ` on `M` induces multiplication by `λ^q` on `⋀^q M`. -/
theorem exteriorPower_map_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (q : ℕ) (c : R) : exteriorPower.map q (c • LinearMap.id : M →ₗ[R] M) = c ^ q • LinearMap.id := by
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun m => ?_)
  simpa using (exteriorPower.ιMulti R q).map_smul_univ (fun _ => c) m

open Finset

end Quillen.Notebook1972_8
