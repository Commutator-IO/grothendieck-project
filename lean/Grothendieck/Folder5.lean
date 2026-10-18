import Mathlib

/-!
# Folder 5: the coefficients `qᵢ` of the universal divided-power algebra (page 4)

Finding `5-universal-artinian-pd-normal-form` (`src/content/findings.ts`), on the
reading `transcripts/5/5.modern.tex`. Page 4 presents the universal artinian
local `W(k)`-algebra whose maximal ideal carries divided powers killed in degrees
`≥ p^{ν+1}` as `W[Λ₀, …, Λ_ν]/(Λᵢ^p − qᵢΛ_{i+1}, Λ_ν^p, Λ₀ − p)`, with
`qᵢ = (p^{i+1})!/((p^i)!)^p`; the relation is `γ_{p^i}(x)^p = qᵢ γ_{p^{i+1}}(x)`.

**Partial.** What is proved is the arithmetic of the `qᵢ`, the « Tier 1 piece »
of issue #54:

* `factorial_eq_mul_q`, `q_eq_multinomial`: `((p^i)!)^p · qᵢ = (p^{i+1})!`, so
  `qᵢ` is an integer, the multinomial coefficient of `p` blocks of size `p^i`;
* `padicValNat_q`: for `p` prime, `v_p(qᵢ) = 1`, by Legendre in the form
  `v_p((pm)!) = v_p(m!) + m` and `(p − 1) v_p((p^i)!) = p^i − 1`
  (`sub_one_mul_padicValNat_factorial_pow`);
* `dpow_pow_eq_q`: in any ring with a divided-power ideal (mathlib's
  `DividedPowers`), `γ_{p^i}(x)^p = qᵢ γ_{p^{i+1}}(x)`, the relation of the
  presentation (a specialisation of mathlib's `DividedPowers.prod_dpow`).

Not formalised: the universality of the presentation, the normal form in the
coordinates `Θᵢ = Λᵢ − p^{p^i}/(p^i)!` (pages 5–7), the constant `c(ν)`, the
quotients `W^{(ν,r)}`, the bound of page 8.
-/

namespace Grothendieck.Folder5

open Nat

/-- `qᵢ = (p^{i+1})! / ((p^i)!)^p`. -/
def q (p i : ℕ) : ℕ := (p ^ (i + 1))! / ((p ^ i)!) ^ p

lemma multinomial_spec_pow (p i : ℕ) :
    ((p ^ i)!) ^ p * Nat.multinomial (Finset.range p) (fun _ => p ^ i) = (p ^ (i + 1))! := by
  have h := Nat.multinomial_spec (Finset.range p) (fun _ => p ^ i)
  simp only [Finset.prod_const, Finset.card_range, Finset.sum_const, smul_eq_mul] at h
  rwa [← pow_succ'] at h

/-- `qᵢ` is the multinomial coefficient of `p` blocks of size `p^i`. -/
theorem q_eq_multinomial (p i : ℕ) :
    q p i = Nat.multinomial (Finset.range p) (fun _ => p ^ i) := by
  rw [q, ← multinomial_spec_pow, Nat.mul_div_cancel_left _ (pow_pos (factorial_pos _) _)]

/-- `((p^i)!)^p · qᵢ = (p^{i+1})!`: `qᵢ` is an integer. -/
theorem factorial_eq_mul_q (p i : ℕ) : (p ^ (i + 1))! = ((p ^ i)!) ^ p * q p i := by
  rw [q_eq_multinomial, multinomial_spec_pow]

/-- Legendre for `p^i`: `(p − 1) v_p((p^i)!) = p^i − 1`. -/
theorem sub_one_mul_padicValNat_factorial_pow (p : ℕ) [hp : Fact p.Prime] (i : ℕ) :
    (p - 1) * padicValNat p (p ^ i)! = p ^ i - 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', padicValNat_factorial_mul, mul_add, ih]
    have h1 : 1 ≤ p ^ i := Nat.one_le_pow _ _ hp.out.pos
    have h2 : (p - 1) * p ^ i + p ^ i = p * p ^ i := by
      rw [Nat.sub_one_mul]
      have := Nat.le_mul_of_pos_left (p ^ i) hp.out.pos
      omega
    omega

/-- **`v_p(qᵢ) = 1`.** -/
theorem padicValNat_q (p : ℕ) [hp : Fact p.Prime] (i : ℕ) : padicValNat p (q p i) = 1 := by
  have hA := sub_one_mul_padicValNat_factorial_pow p i
  have hB : padicValNat p (p ^ (i + 1))! = padicValNat p (p ^ i)! + p ^ i := by
    rw [pow_succ']; exact padicValNat_factorial_mul _
  have hfac := factorial_eq_mul_q p i
  have hq0 : q p i ≠ 0 := by
    intro h; rw [h, mul_zero] at hfac; exact factorial_ne_zero _ hfac
  have hv := congrArg (padicValNat p) hfac
  rw [padicValNat.mul (pow_ne_zero _ (factorial_ne_zero _)) hq0,
    padicValNat.pow] at hv
  have h2 : p * padicValNat p (p ^ i)! =
      (p - 1) * padicValNat p (p ^ i)! + padicValNat p (p ^ i)! := by
    rw [Nat.sub_one_mul]
    have := Nat.le_mul_of_pos_left (padicValNat p (p ^ i)!) hp.out.pos
    omega
  have h1 : 1 ≤ p ^ i := Nat.one_le_pow _ _ hp.out.pos
  omega

/-- `γ_m(x)^p` is the multinomial coefficient times `γ_{pm}(x)`. -/
theorem dpow_pow {A : Type*} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {x : A}
    (hx : x ∈ I) (p m : ℕ) :
    hI.dpow m x ^ p =
      (Nat.multinomial (Finset.range p) (fun _ => m) : A) * hI.dpow (p * m) x := by
  have := hI.prod_dpow (s := Finset.range p) (n := fun _ => m) hx
  simpa [Finset.prod_const, Finset.sum_const] using this

/-- **The relation of page 4**: `γ_{p^i}(x)^p = qᵢ γ_{p^{i+1}}(x)`. -/
theorem dpow_pow_eq_q {A : Type*} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {x : A}
    (hx : x ∈ I) (p i : ℕ) : hI.dpow (p ^ i) x ^ p = (q p i : A) * hI.dpow (p ^ (i + 1)) x := by
  rw [dpow_pow hI hx, q_eq_multinomial, ← pow_succ']

end Grothendieck.Folder5
