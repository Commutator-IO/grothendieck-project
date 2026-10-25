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

/-!
## Universality of the presentation (page 4) and the sufficiency half of page 5

Added for issue #89 (finding `5-universal-artinian-pd-normal-form`). Over any domain `W` of
characteristic zero in which the integers prime to `p` are units (`W(k)`, `ℤ_p`; for `ℤ_p` see
`padicInt_isUnit_natCast`):

* `Aν` is `A^{(ν)} = W[Λ₀, …, Λ_ν]/(Λᵢ^p − qᵢΛᵢ₊₁, Λ_ν^p)` and `Wν = A^{(ν)}/(Λ₀ − p)` is the
  page's `W^{(ν)}` (`presentation`: the quotient by all the relations at once);
* `psi_injective`: `Λᵢ ↦ X^{p^i}/(p^i)!` embeds `A^{(ν)}` in `K[X]/(X^{p^{ν+1}})`, `K = Frac W`;
  the box monomials `Λ^a`, `0 ≤ aᵢ < p`, span `A^{(ν)}` (`boxSpan_eq_top`, the carry of page 8)
  and go to nonzero multiples of distinct powers of `X` (`deg_injective`);
* `dpIbar`: hence `(Λ₀, …, Λ_ν)` carries divided powers, those of `x^n/n!` (`psi_hmem`: every
  `γ_k(X)` comes back, by `C(k, p^e) γ_k = γ_{p^e} γ_{k − p^e}` with `C(k, p^e)` prime to `p`,
  `dpow_split`, Lucas);
* `isSubDPIdeal_Kp`, `dpWν`: `(Λ₀ − p) ∩ (Λ) = (Λ₀ − p)(Λ)` is a sub-divided-power ideal, so the
  divided powers pass to `J = (Λ₀, …, Λ_ν) ⊂ W^{(ν)}`, with `γ_{p^i}(p) = Λᵢ` (`dpWν_p`) and
  `γ_n = 0` on `J` for `n ≥ p^{ν+1}` (`dpWν_eq_zero`);
* **`universal`**: `W^{(ν)}` is initial among `W`-algebras with a divided-power ideal `(I, γ)`
  containing `p` with `γ_n(p) = 0` for `n ≥ p^{ν+1}` — locality, artinianity and the residue
  field play no role;
* `p_pow_mul_Θ_mem`, `p_pow_mul_lam_pow_mem`, `p_pow_mem_Kp`: for any `λᵢ ∈ W` with `λ₀ = p`,
  `λᵢ^p = qᵢλᵢ₊₁`, and `Θᵢ = Λᵢ − λᵢ`: `p^iΘᵢ = 0` and `p^ν λ_ν^p = 0` in `W^{(ν)}`, so
  `p^{ν + pm} = 0` when `λ_ν = p^m · unit` (the sufficiency half of the lemma of page 5).

Not formalised: the necessity half of the lemma of page 5 (that conditions a)–b) cut out an
ideal), hence the normal form, the length, the exact order `p^{c(ν)}` of `1`, and the quotients
`W^{(ν,r)}` of page 7.
-/

namespace Grothendieck.Folder5

open Nat MvPolynomial

/-- Lucas: `C(p^e m, p^e) ≡ m [MOD p]`. -/
theorem choose_pow_mul_pow_modEq (p : ℕ) [hp : Fact p.Prime] (e m : ℕ) :
    choose (p ^ e * m) (p ^ e) ≡ m [MOD p] := by
  induction e with
  | zero => simp [Nat.ModEq]
  | succ e ih =>
    refine (Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p)).trans ?_
    have h1 : p ^ (e + 1) * m = p * (p ^ e * m) := by ring
    have h2 : p ^ (e + 1) = p * p ^ e := by ring
    have hp0 : 0 < p := hp.out.pos
    rw [h1, h2, Nat.mul_mod_right, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hp0,
      Nat.mul_div_cancel_left _ hp0, choose_zero_right, one_mul]
    exact ih

/-- Every `k ≠ 0` has a power `p^e ≤ k` with `C(k, p^e)` prime to `p` (take `p^e ∥ k`). -/
theorem exists_pow_le_not_dvd_choose (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hk : k ≠ 0) :
    ∃ e, p ^ e ≤ k ∧ ¬ p ∣ choose k (p ^ e) := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p hp.out.one_lt.ne'
  refine ⟨e, Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hm)), ?_⟩
  rwa [(choose_pow_mul_pow_modEq p e m).dvd_iff dvd_rfl]

/-- In a divided-power ideal, for `k ≠ 0` there are `p^e ≤ k` and `c` prime to `p` with
`C(k, p^e) γ_k(x) = γ_{p^e}(x) γ_{k − p^e}(x)`, `C(k, p^e)` prime to `p`. -/
theorem dpow_split {R : Type*} [CommSemiring R] (p : ℕ) [Fact p.Prime] {I : Ideal R}
    (hI : DividedPowers I) {x : R} (hx : x ∈ I) {k : ℕ} (hk : k ≠ 0) :
    ∃ e, p ^ e ≤ k ∧ ¬ p ∣ choose k (p ^ e) ∧
      (choose k (p ^ e) : R) * hI.dpow k x = hI.dpow (p ^ e) x * hI.dpow (k - p ^ e) x := by
  obtain ⟨e, hle, hnd⟩ := exists_pow_le_not_dvd_choose p hk
  refine ⟨e, hle, hnd, ?_⟩
  rw [hI.mul_dpow hx, Nat.add_sub_cancel' hle]


variable (W : Type*) [CommRing W] (p ν : ℕ)

/-- The relations `Λᵢ^p − qᵢΛᵢ₊₁` (`i < ν`) and `Λ_ν^p`. -/
noncomputable def rel : Ideal (MvPolynomial (Fin (ν + 1)) W) :=
  Ideal.span (Set.range (fun i : Fin ν => X i.castSucc ^ p - (q p i : MvPolynomial _ W) * X i.succ)
    ∪ {X (Fin.last ν) ^ p})

/-- `A^{(ν)} = W[Λ₀, …, Λ_ν]/(Λᵢ^p − qᵢΛᵢ₊₁, Λ_ν^p)`. -/
abbrev Aν := MvPolynomial (Fin (ν + 1)) W ⧸ rel W p ν

/-- The class of `Λᵢ`. -/
noncomputable def Lam (i : Fin (ν + 1)) : Aν W p ν := Ideal.Quotient.mk _ (X i)

theorem Lam_pow_castSucc (i : Fin ν) :
    Lam W p ν i.castSucc ^ p = (q p i : Aν W p ν) * Lam W p ν i.succ := by
  rw [Lam, Lam, ← map_pow, ← map_natCast (Ideal.Quotient.mk (rel W p ν)), ← map_mul,
    Ideal.Quotient.eq]
  exact Ideal.subset_span (Or.inl ⟨i, rfl⟩)

theorem Lam_last_pow : Lam W p ν (Fin.last ν) ^ p = 0 := by
  rw [Lam, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Or.inr rfl)

/-- The monomial `Λ^a`, `a` in the box `0 ≤ aᵢ < p`. -/
noncomputable def mono (a : Fin (ν + 1) → Fin p) : Aν W p ν := ∏ i, Lam W p ν i ^ (a i : ℕ)

theorem mono_eq (a : Fin (ν + 1) → Fin p) (j : Fin (ν + 1)) :
    mono W p ν a = Lam W p ν j ^ (a j : ℕ) *
      ∏ i ∈ Finset.univ.erase j, Lam W p ν i ^ (a i : ℕ) :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

theorem mono_update (a : Fin (ν + 1) → Fin p) (j : Fin (ν + 1)) (v : Fin p) :
    mono W p ν (Function.update a j v) = Lam W p ν j ^ (v : ℕ) *
      ∏ i ∈ Finset.univ.erase j, Lam W p ν i ^ (a i : ℕ) := by
  rw [mono_eq W p ν _ j, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- The `W`-span of the box monomials. -/
noncomputable def boxSpan : Submodule W (Aν W p ν) := Submodule.span W (Set.range (mono W p ν))

/-- The box monomials are stable under multiplication by each `Λⱼ` (carry in base `p`). -/
theorem Lam_mul_mono_mem (j : Fin (ν + 1)) (a : Fin (ν + 1) → Fin p) :
    Lam W p ν j * mono W p ν a ∈ boxSpan W p ν := by
  induction j using Fin.reverseInduction generalizing a with
  | last =>
    rw [mono_eq W p ν a (Fin.last ν), ← mul_assoc, ← _root_.pow_succ']
    by_cases h : (a (Fin.last ν) : ℕ) + 1 < p
    · rw [show (a (Fin.last ν) : ℕ) + 1 = ((⟨_, h⟩ : Fin p) : ℕ) from rfl,
        ← mono_update]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : (a (Fin.last ν) : ℕ) + 1 = p := by have := (a (Fin.last ν)).2; omega
      rw [this, Lam_last_pow, zero_mul]
      exact Submodule.zero_mem _
  | cast i ih =>
    rw [mono_eq W p ν a i.castSucc, ← mul_assoc, ← _root_.pow_succ']
    by_cases h : (a i.castSucc : ℕ) + 1 < p
    · rw [show (a i.castSucc : ℕ) + 1 = ((⟨_, h⟩ : Fin p) : ℕ) from rfl, ← mono_update]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : (a i.castSucc : ℕ) + 1 = p := by have := (a i.castSucc).2; omega
      have hp : 0 < p := by have := (a i.castSucc).2; omega
      have h0 := mono_update W p ν a i.castSucc ⟨0, hp⟩
      simp only [pow_zero, one_mul] at h0
      rw [this, Lam_pow_castSucc, mul_assoc, ← h0, ← nsmul_eq_mul]
      exact Submodule.smul_of_tower_mem _ _ (ih _)

theorem boxSpan_eq_top (hp : 0 < p) : boxSpan W p ν = ⊤ := by
  have hmul : ∀ x ∈ boxSpan W p ν, ∀ j, x * Lam W p ν j ∈ boxSpan W p ν := by
    intro x hx j
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; rw [mul_comm]; exact Lam_mul_mono_mem W p ν j a
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  have h1 : (1 : Aν W p ν) ∈ boxSpan W p ν := by
    have : mono W p ν (fun _ => ⟨0, hp⟩) = 1 := by simp [mono]
    rw [← this]; exact Submodule.subset_span ⟨_, rfl⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using MvPolynomial.induction_on with
  | C w =>
    rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.mkₐ_eq_mk W, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ w h1
  | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | mul_X f j hf => rw [map_mul]; exact hmul _ hf j

section Embedding

variable (K : Type*) [Field K] [CharZero K] [Algebra W K]

/-- `B = K[X]/(X^{p^{ν+1}})`, `K` a field of characteristic zero receiving `W`. -/
abbrev Bν := Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ p ^ (ν + 1)}

/-- The class of `X` in `B`. -/
noncomputable def xb : Bν p ν K := Ideal.Quotient.mk _ Polynomial.X

omit [CharZero K] in
theorem xb_pow_eq_zero {n : ℕ} (hn : p ^ (ν + 1) ≤ n) : xb p ν K ^ n = 0 := by
  rw [xb, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact pow_dvd_pow _ hn

/-- `cᵢ = 1/(p^i)!`. -/
noncomputable def cf (i : ℕ) : K := (((p ^ i)! : ℕ) : K)⁻¹

theorem cf_pow (i : ℕ) : cf p K i ^ p = (q p i : K) * cf p K (i + 1) := by
  have h := congrArg (fun n : ℕ => (n : K)) (factorial_eq_mul_q p i)
  simp only [Nat.cast_mul, Nat.cast_pow] at h
  have h1 : (((p ^ i)! : ℕ) : K) ≠ 0 := by exact_mod_cast (factorial_ne_zero _)
  have h2 : (((p ^ (i + 1))! : ℕ) : K) ≠ 0 := by exact_mod_cast (factorial_ne_zero _)
  have h3 : (q p i : K) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h; exact h2 h
  rw [cf, cf, inv_pow, h]
  field_simp

/-- `ψ₀ : Λᵢ ↦ X^{p^i}/(p^i)!`. -/
noncomputable def psi0 : MvPolynomial (Fin (ν + 1)) W →ₐ[W] Bν p ν K :=
  MvPolynomial.aeval (R := W) (S₁ := Bν p ν K) fun i : Fin (ν + 1) =>
    (algebraMap (K) (Bν p ν K) (cf p K (i : ℕ)) : Bν p ν K) * xb p ν K ^ (p ^ (i : ℕ))

theorem rel_le_ker : rel W p ν ≤ RingHom.ker (psi0 W p ν K) := by
  rw [rel, Ideal.span_le]
  rintro _ (⟨i, rfl⟩ | h)
  · simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, map_pow, map_natCast,
      psi0, aeval_X, Fin.val_castSucc, Fin.val_succ]
    rw [mul_pow, ← pow_mul, ← _root_.pow_succ, ← map_pow, cf_pow, map_mul, map_natCast]
    ring
  · rw [Set.mem_singleton_iff] at h
    subst h
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_pow, psi0, aeval_X, Fin.val_last]
    rw [mul_pow, ← pow_mul, ← _root_.pow_succ, xb_pow_eq_zero p ν K le_rfl, mul_zero]

/-- `ψ : A^{(ν)} → K[X]/(X^{p^{ν+1}})`. -/
noncomputable def psi : Aν W p ν →ₐ[W] Bν p ν K :=
  Ideal.Quotient.liftₐ (rel W p ν) (psi0 W p ν K) fun _ ha => RingHom.mem_ker.mp (rel_le_ker W p ν K ha)

theorem psi_Lam (i : Fin (ν + 1)) :
    psi W p ν K (Lam W p ν i) =
      algebraMap (K) (Bν p ν K) (cf p K i) * xb p ν K ^ (p ^ (i : ℕ)) := by
  change psi0 W p ν K (X i) = _
  simp [psi0]

/-- The degree `Σ aᵢ p^i` of a box monomial. -/
def deg {m : ℕ} (a : Fin m → Fin p) : ℕ := ∑ i, (a i : ℕ) * p ^ (i : ℕ)

theorem deg_lt {m : ℕ} (a : Fin m → Fin p) : deg p a < p ^ m := by
  induction m with
  | zero => simp [deg]
  | succ m ih =>
    have := ih (fun i => a i.succ)
    have h0 := (a 0).2
    simp only [deg, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
      _root_.pow_succ] at this ⊢
    have : ∑ i : Fin m, (a i.succ : ℕ) * (p ^ (i : ℕ) * p) =
        p * ∑ i : Fin m, (a i.succ : ℕ) * p ^ (i : ℕ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    nlinarith

theorem deg_injective {m : ℕ} : Function.Injective (deg p (m := m)) := by
  induction m with
  | zero => intro a b _; funext i; exact i.elim0
  | succ m ih =>
    intro a b h
    have key : ∀ c : Fin (m + 1) → Fin p,
        deg p c = (c 0 : ℕ) + p * deg p (fun i => c i.succ) := by
      intro c
      simp only [deg, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
        _root_.pow_succ, Finset.mul_sum]
      congr 1; exact Finset.sum_congr rfl fun i _ => by ring
    rw [key a, key b] at h
    have ha := (a 0).2
    have hb := (b 0).2
    have h0 : (a 0 : ℕ) = b 0 := by
      have := congrArg (· % p) h
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
    have hp : 0 < p := by omega
    have h1 : deg p (fun i => a i.succ) = deg p (fun i => b i.succ) := by
      rw [h0] at h
      exact Nat.eq_of_mul_eq_mul_left hp (by omega)
    have := ih h1
    funext i
    refine Fin.cases (Fin.ext h0) (fun j => congrFun this j) i

omit [CharZero K] in
theorem algebraMap_Bν (k : K) :
    algebraMap K (Bν p ν K) k = Ideal.Quotient.mk _ (Polynomial.C k) := rfl

theorem psi_mono (a : Fin (ν + 1) → Fin p) :
    psi W p ν K (mono W p ν a) =
      algebraMap K (Bν p ν K) (∏ i : Fin (ν + 1), cf p K (i : ℕ) ^ (a i : ℕ)) * xb p ν K ^ deg p a := by
  simp only [mono, map_prod, map_pow, psi_Lam, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, deg]
  congr 2
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem cf_ne_zero (i : ℕ) : cf p K i ≠ 0 := by
  rw [cf]; exact inv_ne_zero (by exact_mod_cast factorial_ne_zero _)

/-- **`ψ` is injective**: the box monomials `Λ^a` span `A^{(ν)}` and go to nonzero multiples of
the distinct powers `X^{Σ aᵢ p^i}`, `Σ aᵢ p^i < p^{ν+1}`. -/
theorem psi_injective (hinj : Function.Injective (algebraMap W K)) (hp : 0 < p) :
    Function.Injective (psi W p ν K) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx' : x ∈ boxSpan W p ν := by rw [boxSpan_eq_top W p ν hp]; trivial
  obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun W).mp hx'
  set P : Polynomial K := ∑ a, Polynomial.C (algebraMap W K (w a) * ∏ i : Fin (ν + 1), cf p K (i : ℕ) ^ (a i : ℕ)) *
    Polynomial.X ^ deg p a with hP
  have hmk : Ideal.Quotient.mk _ P = psi W p ν K (∑ a, w a • mono W p ν a) := by
    simp only [hP, map_sum, map_mul, map_smul, psi_mono, map_pow]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul K (w a), Algebra.smul_def (R := K) (A := Bν p ν K), xb,
      algebraMap_Bν, algebraMap_Bν]
    ring
  rw [hx, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
    at hmk
  have hw : ∀ b, w b = 0 := by
    intro b
    have h := hmk (deg p b) (deg_lt p b)
    rw [hP, Polynomial.finsetSum_coeff] at h
    simp only [Polynomial.coeff_C_mul_X_pow] at h
    rw [Finset.sum_eq_single b (fun a _ hab => ite_eq_right_iff.mpr fun h' =>
      absurd (deg_injective p h').symm hab) (by simp)] at h
    simp only [ite_true] at h
    have := (mul_eq_zero.mp h).resolve_right
      (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (cf_ne_zero p K (i : ℕ)))
    exact hinj (by rw [this, map_zero])
  simp [hw]

end Embedding

/-- `ofInjective` is compatible with the map. -/
theorem _root_.DividedPowers.ofInjective_dpow_apply {A B : Type*} [CommSemiring A] [CommSemiring B]
    (I : Ideal A) (J : Ideal B) (f : A →+* B) (hf : Function.Injective f)
    (hJ : DividedPowers J) (hIJ : I.map f = J)
    (hmem : ∀ (n : ℕ) {x : A} (_ : x ∈ I), ∃ (y : A) (_ : n ≠ 0 → y ∈ I), f y = hJ.dpow n (f x))
    {n : ℕ} {x : A} (hx : x ∈ I) :
    f ((DividedPowers.ofInjective I J f hf hJ hIJ hmem).dpow n x) = hJ.dpow n (f x) := by
  simp only [DividedPowers.ofInjective, dite_eq_left hx]
  exact (Exists.choose_spec (hmem n hx)).2

section DividedPowers

/-- The ideal `(Λ₀, …, Λ_ν)` of `A^{(ν)}`. -/
noncomputable def Ibar : Ideal (Aν W p ν) := Ideal.span (Set.range (Lam W p ν))

theorem Lam_mem_Ibar (i : Fin (ν + 1)) : Lam W p ν i ∈ Ibar W p ν :=
  Ideal.subset_span ⟨i, rfl⟩

variable (K : Type*) [Field K] [CharZero K] [Algebra W K]

theorem inverse_factorial_Bν (n : ℕ) :
    Ring.inverse ((n ! : ℕ) : Bν p ν K) = algebraMap K (Bν p ν K) ((n ! : K)⁻¹) := by
  have hu : IsUnit ((n ! : ℕ) : Bν p ν K) := by
    rw [← map_natCast (algebraMap K (Bν p ν K))]
    exact (IsUnit.mk0 _ (by exact_mod_cast factorial_ne_zero n)).map _
  have h1 : ((n ! : ℕ) : Bν p ν K) * algebraMap K (Bν p ν K) ((n ! : K)⁻¹) = 1 := by
    rw [← map_natCast (algebraMap K (Bν p ν K)), ← map_mul,
      mul_inv_cancel₀ (by exact_mod_cast factorial_ne_zero n), map_one]
  calc Ring.inverse ((n ! : ℕ) : Bν p ν K)
      = Ring.inverse ((n ! : ℕ) : Bν p ν K) *
          (((n ! : ℕ) : Bν p ν K) * algebraMap K (Bν p ν K) ((n ! : K)⁻¹)) := by
        rw [h1, mul_one]
    _ = _ := Ring.inverse_mul_cancel_left _ _ hu

open Classical in
/-- The divided powers `x^n/n!` on an ideal of the `ℚ`-algebra `B`. -/
noncomputable abbrev ratDP (J : Ideal (Bν p ν K)) : DividedPowers J :=
  DividedPowers.RatAlgebra.dividedPowers J

theorem ratDP_xb {J : Ideal (Bν p ν K)} (hx : xb p ν K ∈ J) (i : ℕ) :
    (ratDP p ν K J).dpow (p ^ i) (xb p ν K) =
      algebraMap K (Bν p ν K) (cf p K i) * xb p ν K ^ (p ^ i) := by
  rw [DividedPowers.RatAlgebra.dpow_apply, ite_eq_left hx, inverse_factorial_Bν, cf]

theorem ratDP_xb_eq_zero {J : Ideal (Bν p ν K)} (hx : xb p ν K ∈ J) {k : ℕ}
    (hk : p ^ (ν + 1) ≤ k) : (ratDP p ν K J).dpow k (xb p ν K) = 0 := by
  rw [DividedPowers.RatAlgebra.dpow_apply, ite_eq_left hx, xb_pow_eq_zero p ν K hk, mul_zero]

theorem xb_mem_map : xb p ν K ∈ (Ibar W p ν).map (psi W p ν K) := by
  have h := Ideal.mem_map_of_mem (psi W p ν K) (Lam_mem_Ibar W p ν 0)
  rwa [psi_Lam, Fin.val_zero, pow_zero, pow_one, cf, pow_zero, factorial_one, Nat.cast_one,
    inv_one, map_one, one_mul] at h

theorem psi_Lam_eq_dpow (i : Fin (ν + 1)) :
    psi W p ν K (Lam W p ν i) =
      (ratDP p ν K ((Ibar W p ν).map (psi W p ν K))).dpow (p ^ (i : ℕ)) (xb p ν K) := by
  rw [ratDP_xb p ν K (xb_mem_map W p ν K), psi_Lam]

variable [Fact p.Prime]

/-- Every `γ_k(X)` of `B` comes from `A^{(ν)}`, from `(Λ)` if `k ≠ 0` (induction on `k`). -/
theorem exists_psi_eq_dpow_xb (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W)) (k : ℕ) :
    ∃ z : Aν W p ν, (k ≠ 0 → z ∈ Ibar W p ν) ∧
      psi W p ν K z = (ratDP p ν K ((Ibar W p ν).map (psi W p ν K))).dpow k (xb p ν K) := by
  set hJ := ratDP p ν K ((Ibar W p ν).map (psi W p ν K))
  have hx := xb_mem_map W p ν K
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k = 0
    · exact ⟨1, fun h => absurd hk h, by rw [hk, hJ.dpow_zero hx, map_one]⟩
    obtain ⟨e, hle, hc, heq⟩ := dpow_split p hJ hx hk
    by_cases he : e ≤ ν
    · have hlt : k - p ^ e < k := Nat.sub_lt (Nat.pos_of_ne_zero hk)
        (pow_pos (Fact.out : p.Prime).pos _)
      obtain ⟨z', -, hz'⟩ := ih _ hlt
      obtain ⟨v, hv⟩ := hW _ hc
      refine ⟨algebraMap W _ ↑v⁻¹ * (Lam W p ν ⟨e, by omega⟩ * z'),
        fun _ => Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Lam_mem_Ibar W p ν _)), ?_⟩
      rw [map_mul, map_mul, AlgHom.commutes, psi_Lam_eq_dpow, hz']
      change _ * (hJ.dpow (p ^ e) _ * _) = _
      rw [← heq, ← map_natCast (algebraMap W (Bν p ν K)), ← hv, ← mul_assoc, ← map_mul,
        Units.inv_mul, map_one, one_mul]
    · refine ⟨0, fun _ => Ideal.zero_mem _, ?_⟩
      rw [map_zero, ratDP_xb_eq_zero p ν K hx]
      exact le_trans (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)) hle

theorem psi_hmem (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W)) (n : ℕ) {x : Aν W p ν}
    (hx : x ∈ Ibar W p ν) : ∃ (y : Aν W p ν) (_ : n ≠ 0 → y ∈ Ibar W p ν),
      (psi W p ν K : Aν W p ν →+* Bν p ν K) y =
        (ratDP p ν K ((Ibar W p ν).map (psi W p ν K))).dpow n
          ((psi W p ν K : Aν W p ν →+* Bν p ν K) x) := by
  set hJ := ratDP p ν K ((Ibar W p ν).map (psi W p ν K))
  have hmap : ∀ y ∈ Ibar W p ν, psi W p ν K y ∈ (Ibar W p ν).map (psi W p ν K) :=
    fun y hy => Ideal.mem_map_of_mem _ hy
  simp only [RingHom.coe_coe]
  induction hx using Submodule.span_induction generalizing n with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨z, hz, hz'⟩ := exists_psi_eq_dpow_xb W p ν K hW (n * p ^ (i : ℕ))
    refine ⟨(uniformBell n (p ^ (i : ℕ)) : Aν W p ν) * z, fun hn => Ideal.mul_mem_left _ _
      (hz (Nat.mul_ne_zero hn (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))), ?_⟩
    rw [psi_Lam_eq_dpow, hJ.dpow_comp (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      (xb_mem_map W p ν K), map_mul, map_natCast, hz']
  | zero =>
    by_cases hn : n = 0
    · exact ⟨1, fun h => absurd hn h, by rw [map_zero, hn, hJ.dpow_zero (Ideal.zero_mem _),
        map_one]⟩
    · exact ⟨0, fun _ => Ideal.zero_mem _, by rw [map_zero, hJ.dpow_eval_zero hn]⟩
  | add x y hx hy ihx ihy =>
    choose fx hfx hfx' using ihx
    choose fy hfy hfy' using ihy
    refine ⟨∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, fx kl.1 * fy kl.2, fun hn => ?_, ?_⟩
    · refine Ideal.sum_mem _ fun kl hkl => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
      by_cases h1 : kl.1 = 0
      · exact Ideal.mul_mem_left _ _ (hfy _ (by omega))
      · exact Ideal.mul_mem_right _ _ (hfx _ h1)
    · rw [map_add, hJ.dpow_add (hmap x hx) (hmap y hy), map_sum]
      exact Finset.sum_congr rfl fun kl _ => by rw [map_mul, hfx', hfy']
  | smul a x hx ihx =>
    obtain ⟨z, hz, hz'⟩ := ihx n
    refine ⟨a ^ n * z, fun hn => Ideal.mul_mem_left _ _ (hz hn), ?_⟩
    rw [smul_eq_mul, map_mul, map_mul, map_pow, hz', hJ.dpow_mul (hmap x hx)]

end DividedPowers

section Universal

variable [IsDomain W] [CharZero W] [Fact p.Prime]

/-- **The divided powers on `(Λ₀, …, Λ_ν) ⊂ A^{(ν)}`**, transported from `X^n/n!` along the
injective `ψ : A^{(ν)} → K[X]/(X^{p^{ν+1}})`, `K = Frac W`. -/
noncomputable def dpIbar (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W)) : DividedPowers (Ibar W p ν) :=
  DividedPowers.ofInjective (Ibar W p ν) ((Ibar W p ν).map (psi W p ν (FractionRing W)))
    (psi W p ν (FractionRing W) : Aν W p ν →+* Bν p ν (FractionRing W))
    (psi_injective W p ν _ (IsFractionRing.injective W _) (Fact.out : p.Prime).pos)
    (ratDP p ν _ _) rfl (psi_hmem W p ν _ hW)

variable (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W))

theorem psi_dpIbar {n : ℕ} {x : Aν W p ν} (hx : x ∈ Ibar W p ν) :
    psi W p ν (FractionRing W) ((dpIbar W p ν hW).dpow n x) =
      (ratDP p ν (FractionRing W) ((Ibar W p ν).map (psi W p ν (FractionRing W)))).dpow n
        (psi W p ν (FractionRing W) x) :=
  DividedPowers.ofInjective_dpow_apply _ _ _ _ _ _ _ hx

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
theorem psi_Lam_zero (K : Type*) [Field K] [CharZero K] [Algebra W K] :
    psi W p ν K (Lam W p ν 0) = xb p ν K := by
  rw [psi_Lam, Fin.val_zero, pow_zero, pow_one, cf, pow_zero, factorial_one, Nat.cast_one,
    inv_one, map_one, one_mul]

/-- `γ_{p^i}(Λ₀) = Λᵢ` in `A^{(ν)}`. -/
theorem dpIbar_Lam_zero (i : Fin (ν + 1)) :
    (dpIbar W p ν hW).dpow (p ^ (i : ℕ)) (Lam W p ν 0) = Lam W p ν i := by
  apply psi_injective W p ν (FractionRing W) (IsFractionRing.injective W _)
    (Fact.out : p.Prime).pos
  rw [psi_dpIbar W p ν hW (Lam_mem_Ibar W p ν 0), psi_Lam_zero, psi_Lam_eq_dpow]

omit [IsDomain W] [CharZero W] in
theorem map_Ibar_le (K : Type*) [Field K] [CharZero K] [Algebra W K] :
    (Ibar W p ν).map (psi W p ν K) ≤ Ideal.span {xb p ν K} := by
  rw [Ibar, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [psi_Lam, ← pow_sub_one_mul (a := xb p ν K) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
    ← mul_assoc]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- The divided powers of `(Λ)` vanish in degrees `≥ p^{ν+1}`. -/
theorem dpIbar_eq_zero {n : ℕ} (hn : p ^ (ν + 1) ≤ n) {x : Aν W p ν} (hx : x ∈ Ibar W p ν) :
    (dpIbar W p ν hW).dpow n x = 0 := by
  apply psi_injective W p ν (FractionRing W) (IsFractionRing.injective W _)
    (Fact.out : p.Prime).pos
  rw [psi_dpIbar W p ν hW hx, map_zero, DividedPowers.RatAlgebra.dpow_apply,
    ite_eq_left (Ideal.mem_map_of_mem _ hx)]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp
    (map_Ibar_le W p ν (FractionRing W) (Ideal.mem_map_of_mem _ hx))
  rw [← ha, mul_pow, xb_pow_eq_zero p ν _ hn, mul_zero, mul_zero]

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
theorem rel_le_ker_constantCoeff (hp : p ≠ 0) :
    rel W p ν ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin (ν + 1)) W →+* W) := by
  rw [rel, Ideal.span_le]
  rintro _ (⟨i, rfl⟩ | h)
  · simp [zero_pow hp]
  · rw [Set.mem_singleton_iff] at h; subst h; simp [zero_pow hp]

/-- The augmentation `ε : A^{(ν)} → W`, `Λᵢ ↦ 0`. -/
noncomputable def eps : Aν W p ν →+* W :=
  Ideal.Quotient.lift (rel W p ν) constantCoeff fun _ ha =>
    RingHom.mem_ker.mp (rel_le_ker_constantCoeff W p ν (Fact.out : p.Prime).ne_zero ha)

omit [IsDomain W] [CharZero W] in
theorem Ibar_le_ker_eps : Ibar W p ν ≤ RingHom.ker (eps W p ν) := by
  rw [Ibar, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simp [eps, Lam]

omit [IsDomain W] [CharZero W] in
theorem mem_Ibar_of_eps {x : Aν W p ν} (hx : eps W p ν x = 0) : x ∈ Ibar W p ν := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hf : constantCoeff f = 0 := hx
  have : f ∈ Ideal.span (X '' Set.univ : Set (MvPolynomial (Fin (ν + 1)) W)) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [MvPolynomial.mem_support_iff, ← constantCoeff_eq, hf] at hm
      exact hm rfl
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
    exact ⟨i, Set.mem_univ _, hi⟩
  have h2 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (rel W p ν)) this
  rwa [Ideal.map_span, Set.image_image, Set.image_univ] at h2

/-- The ideal `(Λ₀ − p)`. -/
noncomputable def Kp : Ideal (Aν W p ν) := Ideal.span {Lam W p ν 0 - (p : Aν W p ν)}

/-- `(Λ₀ − p) ∩ (Λ) = (Λ₀ − p)(Λ)` is a sub-divided-power ideal. -/
theorem isSubDPIdeal_Kp : (dpIbar W p ν hW).IsSubDPIdeal (Kp W p ν ⊓ Ibar W p ν) where
  isSubideal := inf_le_right
  dpow_mem n hn j hj := by
    obtain ⟨hjK, hjI⟩ := hj
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hjK
    have ha : a ∈ Ibar W p ν := by
      apply mem_Ibar_of_eps
      have h := Ibar_le_ker_eps W p ν hjI
      rw [RingHom.mem_ker, map_mul, map_sub, map_natCast] at h
      have h0 : eps W p ν (Lam W p ν 0) = 0 := RingHom.mem_ker.mp
        (Ibar_le_ker_eps W p ν (Lam_mem_Ibar W p ν 0))
      rw [h0, zero_sub, mul_neg, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_right (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    refine ⟨?_, (dpIbar W p ν hW).dpow_mem hn hjI⟩
    rw [mul_comm, (dpIbar W p ν hW).dpow_mul ha, ← Nat.sub_add_cancel (Nat.pos_of_ne_zero hn),
      pow_succ, mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

/-- **`W^{(ν)} = A^{(ν)}/(Λ₀ − p) = W[Λ₀, …, Λ_ν]/(Λᵢ^p − qᵢΛᵢ₊₁, Λ_ν^p, Λ₀ − p)`.** -/
abbrev Wν := Aν W p ν ⧸ Kp W p ν

/-- **The divided powers on `J = (Λ₀, …, Λ_ν) ⊂ W^{(ν)}`**, induced by those of `A^{(ν)}`. -/
noncomputable def dpWν : DividedPowers ((Ibar W p ν).map (Ideal.Quotient.mk (Kp W p ν))) :=
  DividedPowers.Quotient.dividedPowers (dpIbar W p ν hW) (isSubDPIdeal_Kp W p ν hW)

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
theorem mk_Lam_zero : Ideal.Quotient.mk (Kp W p ν) (Lam W p ν 0) = (p : Wν W p ν) := by
  rw [← map_natCast (Ideal.Quotient.mk (Kp W p ν)), Ideal.Quotient.eq]
  exact Ideal.mem_span_singleton_self _

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
theorem p_mem_Jν : (p : Wν W p ν) ∈ (Ibar W p ν).map (Ideal.Quotient.mk (Kp W p ν)) := by
  rw [← mk_Lam_zero]; exact Ideal.mem_map_of_mem _ (Lam_mem_Ibar W p ν 0)

/-- **`γ_{p^i}(p) = Λᵢ` in `W^{(ν)}`**: the `Λᵢ` are the divided powers of `p`. -/
theorem dpWν_p (i : Fin (ν + 1)) :
    (dpWν W p ν hW).dpow (p ^ (i : ℕ)) (p : Wν W p ν) =
      Ideal.Quotient.mk (Kp W p ν) (Lam W p ν i) := by
  rw [← mk_Lam_zero, dpWν, DividedPowers.Quotient.dpow_apply _ _ (Lam_mem_Ibar W p ν 0),
    dpIbar_Lam_zero]

/-- **The divided powers of `W^{(ν)}` are `ν`-nilpotent**: `γ_n(y) = 0` on `J` for
`n ≥ p^{ν+1}`. -/
theorem dpWν_eq_zero {n : ℕ} (hn : p ^ (ν + 1) ≤ n) {y : Wν W p ν} (hy : y ∈ (Ibar W p ν).map (Ideal.Quotient.mk (Kp W p ν))) :
    (dpWν W p ν hW).dpow n y = 0 := by
  obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
  rw [dpWν, DividedPowers.Quotient.dpow_apply _ _ hx, dpIbar_eq_zero W p ν hW hn hx, map_zero]

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
/-- `W^{(ν)}` is the quotient of `W[Λ₀, …, Λ_ν]` by all the relations of page 4 at once. -/
theorem Kp_eq_map : Kp W p ν = (Ideal.span {X 0 - (p : MvPolynomial (Fin (ν + 1)) W)}).map
    (Ideal.Quotient.mkₐ W (rel W p ν)) := by
  rw [Ideal.map_span, Set.image_singleton, map_sub, map_natCast, Kp]
  rfl

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
/-- **The presentation of page 4**: `W^{(ν)} ≃ W[Λ₀, …, Λ_ν]/(Λᵢ^p − qᵢΛᵢ₊₁, Λ_ν^p, Λ₀ − p)`. -/
noncomputable def presentation : Wν W p ν ≃ₐ[W] MvPolynomial (Fin (ν + 1)) W ⧸
    (rel W p ν ⊔ Ideal.span {X 0 - (p : MvPolynomial (Fin (ν + 1)) W)}) :=
  (Ideal.quotientEquivAlgOfEq W (Kp_eq_map W p ν)).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ W _ _)

section Lift

variable {T : Type*} [CommRing T] [Algebra W T] {I : Ideal T} (hI : DividedPowers I)
  (hpI : (p : T) ∈ I) (hnil : ∀ n, p ^ (ν + 1) ≤ n → hI.dpow n (p : T) = 0)

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
include hpI hnil in
theorem rel_le_ker_lift :
    rel W p ν ≤ RingHom.ker (aeval (R := W) fun i : Fin (ν + 1) => hI.dpow (p ^ (i : ℕ)) (p : T)) := by
  rw [rel, Ideal.span_le]
  rintro _ (⟨i, rfl⟩ | h)
  · simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, map_pow, map_natCast,
      aeval_X, Fin.val_castSucc, Fin.val_succ]
    rw [dpow_pow_eq_q hI hpI, sub_self]
  · rw [Set.mem_singleton_iff] at h; subst h
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_pow, aeval_X, Fin.val_last]
    rw [dpow_pow_eq_q hI hpI, hnil _ le_rfl, mul_zero]

/-- `Λᵢ ↦ γ_{p^i}(p)` on `A^{(ν)}`. -/
noncomputable def lift1 : Aν W p ν →ₐ[W] T :=
  Ideal.Quotient.liftₐ (rel W p ν) (aeval fun i : Fin (ν + 1) => hI.dpow (p ^ (i : ℕ)) (p : T))
    fun _ ha => RingHom.mem_ker.mp (rel_le_ker_lift W p ν hI hpI hnil ha)

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
theorem lift1_Lam (i : Fin (ν + 1)) :
    lift1 W p ν hI hpI hnil (Lam W p ν i) = hI.dpow (p ^ (i : ℕ)) (p : T) := by
  change aeval _ (X i) = _
  rw [aeval_X]

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
theorem Kp_le_ker_lift1 : Kp W p ν ≤ RingHom.ker (lift1 W p ν hI hpI hnil) := by
  rw [Kp, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub,
    lift1_Lam, map_natCast, Fin.val_zero, pow_zero, hI.dpow_one hpI, sub_self]

/-- The `W`-algebra map `W^{(ν)} → T`, `Λᵢ ↦ γ_{p^i}(p)`. -/
noncomputable def lift : Wν W p ν →ₐ[W] T :=
  Ideal.Quotient.liftₐ (Kp W p ν) (lift1 W p ν hI hpI hnil)
    fun _ ha => RingHom.mem_ker.mp (Kp_le_ker_lift1 W p ν hI hpI hnil ha)

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
theorem lift_Lam (i : Fin (ν + 1)) :
    lift W p ν hI hpI hnil (Ideal.Quotient.mk _ (Lam W p ν i)) = hI.dpow (p ^ (i : ℕ)) (p : T) :=
  lift1_Lam W p ν hI hpI hnil i

include hW in
theorem lift_dpow_pow (e : ℕ) :
    lift W p ν hI hpI hnil ((dpWν W p ν hW).dpow (p ^ e) (p : Wν W p ν)) =
      hI.dpow (p ^ e) (p : T) := by
  by_cases he : e ≤ ν
  · have := dpWν_p W p ν hW ⟨e, by omega⟩
    simp only at this
    rw [this, lift_Lam]
  · have hle : p ^ (ν + 1) ≤ p ^ e :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
    rw [dpWν_eq_zero W p ν hW hle (p_mem_Jν W p ν), map_zero, hnil _ hle]

include hW in
/-- `f(γ_k(p)) = γ_k(p)` for every `k`, by induction on `k` through `dpow_split`. -/
theorem lift_dpow (k : ℕ) :
    lift W p ν hI hpI hnil ((dpWν W p ν hW).dpow k (p : Wν W p ν)) = hI.dpow k (p : T) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k = 0
    · rw [hk, (dpWν W p ν hW).dpow_zero (p_mem_Jν W p ν), hI.dpow_zero hpI, map_one]
    obtain ⟨e, hle, hc, heq⟩ := dpow_split p (dpWν W p ν hW) (p_mem_Jν W p ν) hk
    have hlt : k - p ^ e < k := Nat.sub_lt (Nat.pos_of_ne_zero hk)
      (pow_pos (Fact.out : p.Prime).pos _)
    have hT : IsUnit (choose k (p ^ e) : T) := by
      rw [← map_natCast (algebraMap W T)]; exact (hW _ hc).map _
    apply hT.mul_left_cancel
    have h2 := congrArg (lift W p ν hI hpI hnil) heq
    rw [map_mul, map_mul, map_natCast, lift_dpow_pow W p ν hW hI hpI hnil, ih _ hlt] at h2
    rw [h2, hI.mul_dpow hpI, Nat.add_sub_cancel' hle]

include hW in
theorem isDPMorphism_lift :
    DividedPowers.IsDPMorphism (dpWν W p ν hW) hI (lift W p ν hI hpI hnil : Wν W p ν →+* T) := by
  have hS : (Ibar W p ν).map (Ideal.Quotient.mk (Kp W p ν)) =
      Ideal.span (Set.range fun i => Ideal.Quotient.mk (Kp W p ν) (Lam W p ν i)) := by
    rw [Ibar, Ideal.map_span, ← Set.range_comp]; rfl
  refine DividedPowers.IsDPMorphism.on_span (dpWν W p ν hW) hI hS ?_ ?_
  · rintro _ ⟨i, rfl⟩
    rw [RingHom.coe_coe, lift_Lam]
    exact hI.dpow_mem (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hpI
  · rintro n _ ⟨i, rfl⟩
    simp only [RingHom.coe_coe]
    rw [lift_Lam, ← dpWν_p W p ν hW, (dpWν W p ν hW).dpow_comp
      (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) (p_mem_Jν W p ν), map_mul, map_natCast,
      lift_dpow W p ν hW, hI.dpow_comp (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hpI]

end Lift

include hW in
/-- **Universality (page 4).** `W^{(ν)}`, with the divided powers `dpWν` on `J = (Λ₀, …, Λ_ν)`,
is initial among `W`-algebras `T` with a divided-power ideal `(I, γ)` such that `p ∈ I` and
`γ_n(p) = 0` for `n ≥ p^{ν+1}`: there is exactly one `W`-algebra map `W^{(ν)} → T` compatible
with the divided powers. -/
theorem universal {T : Type*} [CommRing T] [Algebra W T] {I : Ideal T} (hI : DividedPowers I)
    (hpI : (p : T) ∈ I) (hnil : ∀ n, p ^ (ν + 1) ≤ n → hI.dpow n (p : T) = 0) :
    ∃! f : Wν W p ν →ₐ[W] T,
      DividedPowers.IsDPMorphism (dpWν W p ν hW) hI (f : Wν W p ν →+* T) := by
  refine ⟨lift W p ν hI hpI hnil, isDPMorphism_lift W p ν hW hI hpI hnil, fun g hg => ?_⟩
  refine Ideal.Quotient.algHom_ext W (Ideal.Quotient.algHom_ext W (MvPolynomial.algHom_ext
    fun i => ?_))
  change g (Ideal.Quotient.mk _ (Lam W p ν i)) = lift W p ν hI hpI hnil
    (Ideal.Quotient.mk _ (Lam W p ν i))
  rw [lift_Lam, ← dpWν_p W p ν hW]
  have := hg.map_dpow (n := p ^ (i : ℕ)) (p_mem_Jν W p ν)
  rw [RingHom.coe_coe] at this
  rw [this]
  exact congrArg _ (map_natCast g p)

end Universal

section Sufficiency

/-! ### The sufficiency half of the lemma of page 5

With `λᵢ ∈ W` the usual divided powers of `p` (any family with `λ₀ = p` and
`λᵢ^p = qᵢλᵢ₊₁`, such as `p^{p^i}/(p^i)!` in `W(k)`) and `Θᵢ = Λᵢ − λᵢ`, one has
`p^i Θᵢ = 0` in `W^{(ν)}` and `p^ν λ_ν^p = 0`. -/

variable [Fact p.Prime] (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W)) (lam : ℕ → W)
  (hlam0 : lam 0 = p) (hlam : ∀ i, lam i ^ p = q p i * lam (i + 1))

/-- `Θᵢ = Λᵢ − λᵢ` in `A^{(ν)}`; its image in `W^{(ν)} = A^{(ν)}/(Λ₀ − p)` is the `Θᵢ` of
page 5. -/
noncomputable def Θ (i : Fin (ν + 1)) : Aν W p ν := Lam W p ν i - algebraMap W _ (lam i)

/-- `qᵢ = p · rᵢ` with `rᵢ` prime to `p` (`v_p(qᵢ) = 1`). -/
theorem q_eq_p_mul (i : ℕ) : ∃ r : ℕ, ¬ p ∣ r ∧ q p i = p * r := by
  have hq : q p i ≠ 0 := by
    intro h; have := factorial_eq_mul_q p i; rw [h, mul_zero] at this
    exact factorial_ne_zero _ this
  obtain ⟨r, hr⟩ : p ∣ q p i := by
    have := padicValNat_q p i
    exact dvd_of_one_le_padicValNat (by omega)
  refine ⟨r, fun hd => ?_, hr⟩
  obtain ⟨s, rfl⟩ := hd
  have h2 : p ^ 2 ∣ q p i := ⟨s, by rw [hr]; ring⟩
  have := (padicValNat_dvd_iff_le hq).mp h2
  rw [padicValNat_q] at this
  omega

include hW hlam0 hlam in
/-- **`p^i Θᵢ = 0` in `W^{(ν)}`** (page 6, by induction on `i`): `p^i Θᵢ ∈ (Λ₀ − p)`. -/
theorem p_pow_mul_Θ_mem (i : Fin (ν + 1)) :
    (p : Aν W p ν) ^ (i : ℕ) * Θ W p ν lam i ∈ Kp W p ν := by
  induction i using Fin.induction with
  | zero =>
    rw [Fin.val_zero, pow_zero, one_mul, Θ, show ((0 : Fin (ν + 1)) : ℕ) = 0 from rfl, hlam0,
      map_natCast]
    exact Ideal.mem_span_singleton_self _
  | succ i ih =>
    obtain ⟨r, hr, hq⟩ := q_eq_p_mul p i
    obtain ⟨u, hu⟩ := hW r hr
    -- `Λᵢ^p − λᵢ^p = qᵢ Θᵢ₊₁`, and `Θᵢ` divides it
    have h1 : Lam W p ν i.castSucc ^ p - algebraMap W (Aν W p ν) (lam i) ^ p =
        (q p i : Aν W p ν) * Θ W p ν lam i.succ := by
      rw [Lam_pow_castSucc, Θ, ← map_pow, hlam, map_mul, map_natCast, Fin.val_succ]
      ring
    obtain ⟨S, hS⟩ := sub_dvd_pow_sub_pow (Lam W p ν i.castSucc) (algebraMap W (Aν W p ν) (lam i)) p
    have h2 : (p : Aν W p ν) ^ (i : ℕ) * ((q p i : Aν W p ν) * Θ W p ν lam i.succ) ∈ Kp W p ν := by
      rw [← h1, hS, ← mul_assoc]
      exact Ideal.mul_mem_right _ _ ih
    rw [hq, Nat.cast_mul, ← map_natCast (algebraMap W (Aν W p ν)) r, ← hu] at h2
    have h3 := Ideal.mul_mem_left _ (algebraMap W (Aν W p ν) ↑u⁻¹) h2
    rw [Fin.val_succ, pow_succ]
    convert h3 using 1
    rw [show algebraMap W (Aν W p ν) ↑u⁻¹ * ((p : Aν W p ν) ^ (i : ℕ) *
        ((p : Aν W p ν) * algebraMap W (Aν W p ν) ↑u * Θ W p ν lam i.succ)) =
        algebraMap W (Aν W p ν) (↑u⁻¹ * ↑u) * ((p : Aν W p ν) ^ (i : ℕ) * p *
          Θ W p ν lam i.succ) by rw [map_mul]; ring, Units.inv_mul, map_one, one_mul]

include hW hlam0 hlam in
/-- **`p^ν λ_ν^p = 0` in `W^{(ν)}`** (page 6): `p^ν λ_ν^p ∈ (Λ₀ − p)`. -/
theorem p_pow_mul_lam_pow_mem :
    (p : Aν W p ν) ^ ν * algebraMap W (Aν W p ν) (lam ν) ^ p ∈ Kp W p ν := by
  obtain ⟨S, hS⟩ := sub_dvd_pow_sub_pow (Lam W p ν (Fin.last ν))
    (algebraMap W (Aν W p ν) (lam ν)) p
  have h := p_pow_mul_Θ_mem W p ν hW lam hlam0 hlam (Fin.last ν)
  rw [Fin.val_last] at h
  have h2 := Ideal.mul_mem_right (-S) _ h
  convert h2 using 1
  have hL := Lam_last_pow W p ν
  rw [Θ, Fin.val_last]
  linear_combination (-(p : Aν W p ν) ^ ν) * hS + (p : Aν W p ν) ^ ν * hL

include hW hlam0 hlam in
/-- If `λ_ν = p^m u`, `u` a unit, then `p^{ν + pm} = 0` in `W^{(ν)}`; for the usual
`λ_ν = p^{p^ν}/(p^ν)!`, `m = p^ν − (p^ν − 1)/(p − 1)` and `ν + pm = c(ν)`. -/
theorem p_pow_mem_Kp {m : ℕ} {u : W} (hu : IsUnit u) (hm : lam ν = p ^ m * u) :
    (p : Aν W p ν) ^ (ν + p * m) ∈ Kp W p ν := by
  have h := p_pow_mul_lam_pow_mem W p ν hW lam hlam0 hlam
  obtain ⟨v, rfl⟩ := hu
  have h3 := Ideal.mul_mem_left _ (algebraMap W (Aν W p ν) (↑v⁻¹ ^ p)) h
  convert h3 using 1
  have hv : algebraMap W (Aν W p ν) ↑v⁻¹ * algebraMap W (Aν W p ν) ↑v = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [hm]
  simp only [map_mul, map_pow, map_natCast]
  rw [show algebraMap W (Aν W p ν) ↑v⁻¹ ^ p * ((p : Aν W p ν) ^ ν *
      ((p : Aν W p ν) ^ m * algebraMap W (Aν W p ν) ↑v) ^ p) =
      (algebraMap W (Aν W p ν) ↑v⁻¹ * algebraMap W (Aν W p ν) ↑v) ^ p *
        (p : Aν W p ν) ^ (ν + p * m) by ring, hv, one_pow, one_mul]

end Sufficiency

/-- The hypotheses hold for `W = ℤ_p` (`k = 𝔽_p`): integers prime to `p` are units. -/
theorem padicInt_isUnit_natCast [Fact p.Prime] (n : ℕ) (hn : ¬ p ∣ n) : IsUnit (n : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hn ?_)
  have := (PadicInt.norm_int_lt_one_iff_dvd (p := p) n).mp (by exact_mod_cast h)
  exact_mod_cast this

end Grothendieck.Folder5
