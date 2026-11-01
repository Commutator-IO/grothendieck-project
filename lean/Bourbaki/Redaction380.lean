import Mathlib

/-!
# Bourbaki rédaction n° 380: a reversed pole criterion, and a compact spectrum without unit

Rédaction n° 380 of the Bourbaki archive (J.-L. Koszul, *Analyse fonctionnelle, chapitre I,
Algèbres normées*, April 1962; Archives Henri Poincaré, item
<https://archives-bourbaki.ahp-numerique.fr/items/show/935>) studies normed algebras and their
spectra, the spaces of characters (nonzero continuous multiplicative linear forms) with the weak
topology. On p. 40, Prop. 6 restates the pole criterion of Lemma 5 (`λ` is a pole of order `p`
of the resolvent when `(x - λe)^(p-1) e_λ ≠ 0` and `(x - λe)^p e_λ = 0`) with the conditions reversed:
`(x - λe)^k e_λ = 0` for `k < p` and `≠ 0` for `k = p`. No element satisfies that, since vanishing
at `k = p - 1` forces vanishing at `k = p`.

* `reversed_pole_condition_never`: in any ring, for `p ≥ 1`, there are no `a`, `e` with
  `a ^ k * e = 0` for all `k < p` and `a ^ p * e ≠ 0`;
* `pole_condition_example`: the condition of Lemma 5 holds for `x = 0` in `ℂ`, `λ = 0`,
  `e_λ = 1`, `p = 1`.

On p. 54, Prop. 16 asserts that the spectrum of a normed algebra without unit is not
compact. This is false in general, and this file gives two counterexamples, both complete normed
algebras over `ℂ` without unit.

* `characterSpace_eq_empty_of_mul_self_eq_zero`: if `x * x = 0` for every `x` (over a field, or
  any ring without zero divisors), there is no character at all: a character `φ` would satisfy
  `φ x ^ 2 = φ (x * x) = 0`;
* `ZeroMul`: the space `ℂ` with the zero multiplication, a complete normed non-unital
  `ℂ`-algebra (`ZeroMul.not_exists_one`: it has no unit), with empty, hence compact, spectrum
  (`ZeroMul.isCompact_characterSpace`);
* `characterSpace_prod_eq`: the algebra `ℂ × ZeroMul` (that is, `ℂ ⊕ N` with `N² = 0` and
  `ℂ · N = 0`), complete and without unit (`not_exists_one_prod`), has exactly one character,
  the first projection, so its spectrum is a point, nonempty and compact
  (`isCompact_characterSpace_prod`, `characterSpace_prod_nonempty`);
* `not_prop16`: the statement of Prop. 16, read as « for every complete normed non-unital
  `ℂ`-algebra, the character space is not compact », is false.

What is true is that the spectrum of a commutative Banach algebra is locally compact, and
compact when the algebra has a unit; without a unit, the spectrum with the zero character
added is compact (`WeakDual.CharacterSpace.union_zero_isClosed` in mathlib is the closedness
step). Non-compactness of the spectrum without a unit holds for instance for `C₀(X)` with `X`
locally compact non-compact, which is presumably the case the page has in mind; it is not
formalised here.
-/

open WeakDual

noncomputable section

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


/-- **No characters when every square vanishes.** If `x * x = 0` for every `x ∈ A`, the
character space of `A` is empty. -/
theorem characterSpace_eq_empty_of_mul_self_eq_zero {𝕜 A : Type*} [CommRing 𝕜]
    [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
    [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [Module 𝕜 A]
    (h : ∀ x : A, x * x = 0) : characterSpace 𝕜 A = ∅ := by
  ext φ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hφ, hmul⟩
  apply hφ
  refine DFunLike.ext _ _ fun x => ?_
  have := hmul x x
  rw [h x, map_zero] at this
  exact mul_self_eq_zero.mp this.symm

/-- The space `ℂ` with the zero multiplication. -/
def ZeroMul : Type := ℂ

namespace ZeroMul

instance : NormedAddCommGroup ZeroMul := inferInstanceAs (NormedAddCommGroup ℂ)

instance : NormedSpace ℂ ZeroMul := inferInstanceAs (NormedSpace ℂ ℂ)

instance : CompleteSpace ZeroMul := inferInstanceAs (CompleteSpace ℂ)

/-- The zero multiplication makes `ZeroMul` a non-unital normed ring. -/
instance : NonUnitalNormedRing ZeroMul where
  mul _ _ := 0
  left_distrib _ _ _ := (add_zero 0).symm
  right_distrib _ _ _ := (add_zero 0).symm
  zero_mul _ := rfl
  mul_zero _ := rfl
  mul_assoc _ _ _ := rfl
  dist_eq x y := by rw [dist_eq_norm', sub_eq_neg_add]
  norm_mul_le a b := by
    change ‖(0 : ZeroMul)‖ ≤ ‖a‖ * ‖b‖
    rw [norm_zero]
    positivity

/-- Every product vanishes. -/
theorem mul_eq_zero' (x y : ZeroMul) : x * y = 0 := rfl

instance : IsScalarTower ℂ ZeroMul ZeroMul :=
  ⟨fun _ _ _ => (smul_zero _).symm⟩

instance : SMulCommClass ℂ ZeroMul ZeroMul :=
  ⟨fun _ _ _ => (smul_zero _)⟩

instance : Nontrivial ZeroMul := inferInstanceAs (Nontrivial ℂ)

/-- `ZeroMul` has no unit. -/
theorem not_exists_one : ¬ ∃ e : ZeroMul, ∀ x, e * x = x := by
  rintro ⟨e, he⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : ZeroMul)
  exact hx ((he x).symm.trans (mul_eq_zero' e x))

/-- The character space of `ZeroMul` is empty. -/
theorem characterSpace_eq_empty : characterSpace ℂ ZeroMul = ∅ :=
  characterSpace_eq_empty_of_mul_self_eq_zero fun x => mul_eq_zero' x x

/-- The character space of `ZeroMul` is compact. -/
theorem isCompact_characterSpace : IsCompact (characterSpace ℂ ZeroMul) := by
  rw [characterSpace_eq_empty]
  exact isCompact_empty

end ZeroMul

/-- The algebra `ℂ × ZeroMul` has no unit. -/
theorem not_exists_one_prod : ¬ ∃ e : ℂ × ZeroMul, ∀ x, e * x = x := by
  rintro ⟨e, he⟩
  exact ZeroMul.not_exists_one ⟨e.2, fun x => congrArg Prod.snd (he (0, x))⟩

/-- The first projection `ℂ × ZeroMul → ℂ`, as an element of the weak dual. -/
noncomputable def fstChar : WeakDual ℂ (ℂ × ZeroMul) :=
  ContinuousLinearMap.fst ℂ ℂ ZeroMul

/-- **The spectrum of `ℂ × ZeroMul` is a point**: the only character is the first projection. -/
theorem characterSpace_prod_eq : characterSpace ℂ (ℂ × ZeroMul) = {fstChar} := by
  ext φ
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hφ, hmul⟩
    -- `φ` vanishes on `0 × ZeroMul`
    have h2 : ∀ z : ZeroMul, φ (0, z) = 0 := by
      intro z
      have := hmul (0, z) (0, z)
      have h0 : ((0, z) : ℂ × ZeroMul) * (0, z) = 0 := by
        ext
        · simp
        · exact ZeroMul.mul_eq_zero' z z
      rw [h0, map_zero] at this
      exact mul_self_eq_zero.mp this.symm
    -- `c = φ (1, 0)` is idempotent
    set c := φ (1, 0) with hc
    have hcc : c * c = c := by
      rw [hc, ← hmul]
      congr 1
      ext
      · simp
      · exact ZeroMul.mul_eq_zero' 0 0
    have hval : ∀ p : ℂ × ZeroMul, φ p = p.1 * c := by
      intro p
      have hp : p = p.1 • ((1 : ℂ), (0 : ZeroMul)) + ((0 : ℂ), p.2) := by
        ext <;> simp
      rw [hp, map_add, map_smul, h2, add_zero, smul_eq_mul]
      simp [hc]
    have hc1 : c = 1 := by
      have h01 : c * (c - 1) = 0 := by linear_combination hcc
      rcases mul_eq_zero.mp h01 with h | h
      · exact absurd (DFunLike.ext _ _ fun p => by rw [hval p, h, mul_zero]; rfl) hφ
      · exact sub_eq_zero.mp h
    refine DFunLike.ext _ _ fun p => ?_
    rw [hval p, hc1, mul_one]
    rfl
  · rintro rfl
    refine ⟨fun h => ?_, fun x y => rfl⟩
    have := congrArg (fun f : WeakDual ℂ (ℂ × ZeroMul) => f ((1 : ℂ), (0 : ZeroMul))) h
    change (1 : ℂ) = 0 at this
    exact one_ne_zero this

/-- The spectrum of `ℂ × ZeroMul` is compact. -/
theorem isCompact_characterSpace_prod : IsCompact (characterSpace ℂ (ℂ × ZeroMul)) := by
  rw [characterSpace_prod_eq]
  exact isCompact_singleton

/-- The spectrum of `ℂ × ZeroMul` is nonempty. -/
theorem characterSpace_prod_nonempty : (characterSpace ℂ (ℂ × ZeroMul)).Nonempty := by
  rw [characterSpace_prod_eq]
  exact Set.singleton_nonempty _

/-- **Prop. 16 of p. 54 fails**: there is a complete normed non-unital `ℂ`-algebra whose
character space is nonempty and compact. -/
theorem not_prop16 :
    ¬ ∀ (A : Type) [NonUnitalNormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A]
      [SMulCommClass ℂ A A] [CompleteSpace A], (¬ ∃ e : A, ∀ x, e * x = x) →
        ¬ IsCompact (characterSpace ℂ A) :=
  fun h => h (ℂ × ZeroMul) not_exists_one_prod isCompact_characterSpace_prod

end Bourbaki.Redaction380

end
