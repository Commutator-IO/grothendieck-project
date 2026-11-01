import Mathlib

/-!
# Bourbaki, rédaction n° 380 (April 1962): two misstatements in Koszul's « Algèbres normées »

Rédaction 380 of the Bourbaki archive (Archives Henri Poincaré, item 935) is Koszul's draft of
*Analyse fonctionnelle*, ch. I « Algèbres normées », which became *Théories spectrales*, ch. I
(1967). Two statements are false as typed.

**The pole criterion (§ 2, Prop. 6, p. 40 of the facsimile).** Lemma 5 of the draft says that `λ`
is a pole of order `p` of the resolvent when `(x - λe)^(p-1) e_λ ≠ 0` and `(x - λe)^p e_λ = 0`,
where `e_λ` is the idempotent attached to the isolated point `λ`. Prop. 6 restates it with the
conditions reversed: `(x - λe)^k e_λ = 0` for `k < p` and `≠ 0` for `k = p`. No element satisfies
the reversed condition, since vanishing at `k = p - 1` forces vanishing at `k = p`; as typed,
Prop. 6 would say that the resolvent has no poles at all.

* `reversed_pole_condition_never`: in any ring, for `p ≥ 1`, there are no `a`, `e` with
  `a ^ k * e = 0` for all `k < p` and `a ^ p * e ≠ 0`;
* `pole_condition_example`: the condition of Lemma 5 does hold for `x = 0` in `ℂ`, `λ = 0`,
  `e_λ = 1`, `p = 1` (the resolvent `1/λ` of `0` has a simple pole at `0`).

**The spectrum of an algebra without unit (§ 3, Prop. 16, p. 54).** The draft says that the
spectrum (the space of characters) of a normed algebra without unit is not compact. It can be
empty: in an algebra where every product vanishes, a character `φ` has `φ(x)² = φ(x²) = 0`, so
`φ = 0`, which is excluded.

* `isEmpty_characterSpace_of_mul_self_eq_zero`: if `x * x = 0` for every `x`, the character space
  is empty, hence compact;
* `ZeroMulC`: `ℂ` with the zero product, a nontrivial commutative algebra without unit
  (`not_exists_unit`);
* `compactSpace_characterSpace_zeroMulC`: its character space is empty, hence compact.

Whether the printed *Théories spectrales* (1967) keeps either statement has not been checked.
-/

namespace Bourbaki.Redaction380

section Pole

/-- The pole criterion of Prop. 6, as typed, is never satisfied: if `a ^ (p - 1) * e = 0` then
`a ^ p * e = 0`. -/
theorem reversed_pole_condition_never {R : Type*} [Ring R] (a e : R) {p : ℕ} (hp : 1 ≤ p) :
    ¬ ((∀ k < p, a ^ k * e = 0) ∧ a ^ p * e ≠ 0) := by
  rintro ⟨hlt, hne⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  apply hne
  rw [pow_succ', mul_assoc, hlt q (Nat.lt_succ_self q), mul_zero]

/-- The criterion of Lemma 5 is satisfiable: for `x = 0`, `λ = 0`, `e_λ = 1` and `p = 1`,
`(x - λ)^0 e_λ ≠ 0` and `(x - λ)^1 e_λ = 0`. -/
theorem pole_condition_example :
    (0 - 0 : ℂ) ^ 0 * 1 ≠ 0 ∧ (0 - 0 : ℂ) ^ 1 * 1 = 0 := by
  norm_num

end Pole

section Spectrum

open WeakDual

/-- In an algebra where every square vanishes, there is no character: `φ(x)² = φ(x * x) = 0`. -/
theorem isEmpty_characterSpace_of_mul_self_eq_zero {𝕜 A : Type*} [Field 𝕜] [TopologicalSpace 𝕜]
    [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] [NonUnitalNonAssocSemiring A] [TopologicalSpace A]
    [Module 𝕜 A] (h : ∀ x : A, x * x = 0) : IsEmpty (characterSpace 𝕜 A) := by
  refine ⟨fun φ => φ.prop.1 (ContinuousLinearMap.ext fun x => ?_)⟩
  have hx : φ x * φ x = 0 := by
    rw [← map_mul, h, map_zero]
  exact mul_self_eq_zero.mp hx

/-- `ℂ` with the zero product: a commutative algebra without unit in which every product
vanishes. -/
def ZeroMulC : Type := ℂ

namespace ZeroMulC

instance : NonUnitalCommRing ZeroMulC :=
  { (inferInstance : AddCommGroup ℂ) with
    mul := fun _ _ => (0 : ℂ)
    left_distrib := fun _ _ _ => (add_zero (0 : ℂ)).symm
    right_distrib := fun _ _ _ => (add_zero (0 : ℂ)).symm
    zero_mul := fun _ => rfl
    mul_zero := fun _ => rfl
    mul_assoc := fun _ _ _ => rfl
    mul_comm := fun _ _ => rfl }

instance : Module ℂ ZeroMulC := inferInstanceAs (Module ℂ ℂ)

instance : TopologicalSpace ZeroMulC := inferInstanceAs (TopologicalSpace ℂ)

theorem mul_eq_zero' (x y : ZeroMulC) : x * y = 0 := rfl

/-- `ZeroMulC` is nontrivial and has no unit. -/
theorem not_exists_unit : Nontrivial ZeroMulC ∧ ¬ ∃ e : ZeroMulC, ∀ x, e * x = x := by
  refine ⟨inferInstanceAs (Nontrivial ℂ), fun ⟨e, he⟩ => ?_⟩
  have h1 : (1 : ℂ) = 0 := ((he (1 : ℂ)).symm.trans (mul_eq_zero' e (1 : ℂ))).symm.symm
  exact one_ne_zero h1

end ZeroMulC

/-- The spectrum (character space) of `ZeroMulC` is empty, hence compact: Prop. 16 fails. -/
theorem compactSpace_characterSpace_zeroMulC : IsEmpty (characterSpace ℂ ZeroMulC) ∧
    CompactSpace (characterSpace ℂ ZeroMulC) := by
  have h := isEmpty_characterSpace_of_mul_self_eq_zero (𝕜 := ℂ) (A := ZeroMulC)
    (fun x => ZeroMulC.mul_eq_zero' x x)
  exact ⟨h, inferInstance⟩

end Spectrum

end Bourbaki.Redaction380
