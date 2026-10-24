import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Folder 160, pages 7–9 and 13–15: the Moore determinant and the Dickson coefficients

The modernised reading `transcripts/160/160.modern.tex` defines, for a locally free `E` of
rank `n` with `u : E^{(p)} ⥲ E` (an étale `𝔽_p`-local system) and `ξ` a section of `Ě`,

> `Δₙ^E(ξ) = ξ ∧ ξ^{(p)} ∧ ⋯ ∧ ξ^{(p^{n-1})}`, soit une application polynomiale, homogène de
> degré `(pⁿ − 1)/(p − 1)`, `Δₙ^E : V(E) → V(ΛⁿE)`. … Sur [le complémentaire de son diviseur
> des zéros], `ξ, ξ^{(p)}, …, ξ^{(p^{n-1})}` forment une base de `Ě`, et l'on peut écrire
> `ξ^{(pⁿ)} + A^E_{n-1}(ξ) ξ^{(p^{n-1})} + ⋯ + A^E_0(ξ) ξ = 0`, ce qui définit des fonctions
> `A^E_i` uniquement déterminées. Comme dans le cas absolu, elles s'étendent à `V(E)` tout
> entier, … et l'on a encore `A^E_0 = (±1)(Δₙ^E)^{p-1}`.

This is finding `160-relative-moore-determinant`, in coordinates: `E` trivialised with `u` the
identity, so that `ξ ∈ Sⁿ` for an `𝔽_p`-algebra `S` and `ξ^{(p^i)} = (ξ_k^{p^i})_k`; the
Moore determinant is then `det(ξ_j^{p^i})` (pages 7–9, the absolute case).

* `moore_smul`, `moore_smul'`: `Δₙ(cξ) = c^{(pⁿ−1)/(p−1)} Δₙ(ξ)` over any commutative ring.
* `D_eq_C_mul_P`, `roots_D`: over `K = 𝔽_p[X₁, …, Xₙ]`,
  `D(T) = Δ_{n+1}(T, X₁, …, Xₙ) = (−1)ⁿ Δₙ · ∏_{λ ∈ 𝔽_pⁿ} (T − λ · X)`, with `Δₙ ≠ 0`
  (`Δ_ne_zero`, by induction through `D`): the factorisation the reading gives for the
  divisibility `Δ_i = A_i Δₙ` that page 9 asserts.
* `dickson_relation`: the `A_i ∈ 𝔽_p[X]` (coefficients of `∏ (T − λ · X)`) satisfy
  `X_k^{pⁿ} + Σ A_i X_k^{p^i} = 0`; `A_zero`: `A₀ = (−1)ⁿ Δₙ^{p−1}`.
* `dickson_relation_eval`, `dickson_unique`, `A_zero_eval`: for every `𝔽_p`-algebra `S` and
  `ξ ∈ Sⁿ` the relation holds with the `A_i(ξ)`, and where `Δₙ(ξ)` is invertible they are its
  only coefficients: the `A_i^E` extend from the complement of the zero divisor of `Δₙ` to
  all of `V(E)`, and `A₀ = (−1)ⁿ Δₙ^{p−1}` everywhere.

* `corollaire_page13_faux` (finding `160-special-linear-structures-sign`): the Corollary of
  page 13, trivialisations of `ΛⁿM` « ↔ » `(p − 1)`-th roots of `a₀`, fails for `p` and `n`
  odd: over `𝔽₃`, `M = 𝔽₃ = Ker(x³ − x)`, `a₀ = −1` has no square root while `Λ¹M` has two
  trivialisations.
* `moore_act`, `moore_pow_sub_one`, `moore_act_surj`, `moore_act_eq_iff`: the corrected form
  over a field `K` of characteristic `p`: `Δₙ(g · e) = det g · Δₙ(e)` for `g` over `𝔽_p`,
  `Δₙ(e)` is a `(p − 1)`-th root of `(−1)ⁿ a₀`, every such root is a `Δₙ(g · e)`, and
  `Δₙ(g · e) = Δₙ(h · e)` iff `det g = det h`: the trivialisations correspond to the roots of
  `(−1)ⁿ a₀`, with fibres the `SLₙ(𝔽_p)`-orbits.

**What the formalisation finds.** The statement holds in coordinates, with the sign `(−1)ⁿ`
that page and reading leave as `±`. The extension rests on the factorisation of `D(T)`, which
needs only that the `p^n` forms `λ · X` are distinct roots of a polynomial of degree `pⁿ` with
leading coefficient `±Δₙ ≠ 0`; the factorisation of page 7 with its constant `c` is not
needed. Not formalised: the relative version for a non-trivial `(E, u)` (the reduction to the
trivial local system is étale-local), the trivialisation `(ΛⁿĚ)^{⊗(p−1)} ≅ 𝒪_S` by `Λⁿǔ`,
and Dickson's theorem (pages 9–12).
-/

open Matrix Polynomial

namespace Grothendieck.Folder160

variable {R : Type*} [CommRing R] (p : ℕ)

/-- The Moore matrix `(ξ_j^{p^i})`. -/
def mooreMat {n : ℕ} (ξ : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  of fun i j => ξ j ^ p ^ (i : ℕ)

/-- The Moore determinant `Δₙ(ξ) = det(ξ_j^{p^i})`. -/
def moore {n : ℕ} (ξ : Fin n → R) : R := (mooreMat p ξ).det

/-- `Δₙ(cξ) = c^{1 + p + ⋯ + p^{n-1}} Δₙ(ξ)`, over any commutative ring. -/
theorem moore_smul {n : ℕ} (c : R) (ξ : Fin n → R) :
    moore p (c • ξ) = c ^ (∑ i ∈ Finset.range n, p ^ i) * moore p ξ := by
  have : mooreMat p (c • ξ) = of fun (i j : Fin n) => c ^ p ^ (i : ℕ) * mooreMat p ξ i j := by
    ext i j; simp [mooreMat, mul_pow]
  rw [moore, this, det_mul_column, ← Finset.prod_pow_eq_pow_sum, ← Fin.prod_univ_eq_prod_range]
  rfl

/-- **Homogeneity of degree `(pⁿ − 1)/(p − 1)`.** -/
theorem moore_smul' (hp : 2 ≤ p) {n : ℕ} (c : R) (ξ : Fin n → R) :
    moore p (c • ξ) = c ^ ((p ^ n - 1) / (p - 1)) * moore p ξ := by
  rw [moore_smul, Nat.geomSum_eq hp]

theorem map_moore {S : Type*} [CommRing S] (f : R →+* S) {n : ℕ} (ξ : Fin n → R) :
    f (moore p ξ) = moore p (f ∘ ξ) := by
  rw [moore, RingHom.map_det]
  congr 1
  ext i j; simp [mooreMat]

/-! ### The universal case: Moore determinants over `𝔽_p[X₁, …, Xₙ]` -/

variable [hp : Fact p.Prime]

/-- `Δₙ(X₁, …, Xₙ) ∈ 𝔽_p[X₁, …, Xₙ]`. -/
noncomputable def Δ (n : ℕ) : MvPolynomial (Fin n) (ZMod p) := moore p MvPolynomial.X

/-- `D(T) = Δ_{n+1}(T, X₁, …, Xₙ)`, a polynomial in `T` over `𝔽_p[X₁, …, Xₙ]`. -/
noncomputable def D (n : ℕ) : (MvPolynomial (Fin n) (ZMod p))[X] :=
  moore p (Fin.cons Polynomial.X fun k => Polynomial.C (MvPolynomial.X k))

/-- The minors of the expansion of `D` along its first column. -/
noncomputable def minor (n : ℕ) (i : Fin (n + 1)) : MvPolynomial (Fin n) (ZMod p) :=
  (of fun (r : Fin n) (k : Fin n) => (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod p)) ^
    p ^ ((i.succAbove r : Fin (n + 1)) : ℕ)).det

theorem D_eq (n : ℕ) : D p n = ∑ i : Fin (n + 1),
    Polynomial.C ((-1) ^ (i : ℕ) * minor p n i) * Polynomial.X ^ p ^ (i : ℕ) := by
  rw [D, moore, det_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : (mooreMat p (Fin.cons (Polynomial.X : (MvPolynomial (Fin n) (ZMod p))[X])
      fun k => Polynomial.C (MvPolynomial.X k))).submatrix i.succAbove Fin.succ =
      (Polynomial.C : MvPolynomial (Fin n) (ZMod p) →+* _).mapMatrix
        (of fun (r : Fin n) (k : Fin n) => (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod p)) ^
          p ^ ((i.succAbove r : Fin (n + 1)) : ℕ)) := by
    ext r k; simp [mooreMat]
  rw [hsub, ← RingHom.map_det, minor]
  simp only [mooreMat, of_apply, Fin.cons_zero, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_1]
  ring

theorem pow_injective : Function.Injective fun i : ℕ => p ^ i :=
  Nat.pow_right_injective hp.out.two_le

theorem coeff_D (n : ℕ) (i : Fin (n + 1)) :
    (D p n).coeff (p ^ (i : ℕ)) = (-1) ^ (i : ℕ) * minor p n i := by
  rw [D_eq, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [ite_eq_right]
    intro h
    exact hj (Fin.ext (pow_injective p h).symm)
  · simp

theorem coeff_D_of_ne (n : ℕ) (m : ℕ) (hm : ∀ i : Fin (n + 1), m ≠ p ^ (i : ℕ)) :
    (D p n).coeff m = 0 := by
  rw [D_eq, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  exact Finset.sum_eq_zero fun i _ => ite_eq_right (hm i)

theorem minor_last (n : ℕ) : minor p n (Fin.last n) = Δ p n := by
  simp only [minor, Fin.succAbove_last, Fin.val_castSucc]
  rfl

theorem minor_zero (n : ℕ) : minor p n 0 = Δ p n ^ p := by
  rw [Δ, moore, ← frobenius_def (R := MvPolynomial (Fin n) (ZMod p)) p, RingHom.map_det, minor]
  congr 1
  ext r k
  simp [mooreMat, pow_succ, pow_mul, frobenius_def]

theorem natDegree_D_le (n : ℕ) : (D p n).natDegree ≤ p ^ n := by
  rw [D_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.pow_le_pow_right hp.out.pos (Nat.lt_succ_iff.1 i.2)

theorem finSuccEquiv_Δ (n : ℕ) :
    MvPolynomial.finSuccEquiv (ZMod p) n (Δ p (n + 1)) = D p n := by
  rw [Δ, D]
  have := map_moore p (MvPolynomial.finSuccEquiv (ZMod p) n).toRingEquiv.toRingHom
    (MvPolynomial.X : Fin (n + 1) → _)
  simp only [RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe] at this
  rw [this]
  congr 1
  ext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [MvPolynomial.finSuccEquiv_X_zero,
    MvPolynomial.finSuccEquiv_X_succ]

/-- `Δₙ ≠ 0` in `𝔽_p[X₁, …, Xₙ]`. -/
theorem Δ_ne_zero (n : ℕ) : Δ p n ≠ 0 := by
  induction n with
  | zero => simp [Δ, moore]
  | succ n ih =>
    intro h
    have h1 := congrArg (MvPolynomial.finSuccEquiv (ZMod p) n) h
    rw [finSuccEquiv_Δ, map_zero] at h1
    have := coeff_D p n (Fin.last n)
    rw [h1, Polynomial.coeff_zero, minor_last] at this
    exact ih (by simpa using this.symm)

/-- The linear form `λ · X = Σ λ_k X_k`. -/
noncomputable def lin {n : ℕ} (l : Fin n → ZMod p) : MvPolynomial (Fin n) (ZMod p) :=
  ∑ k, MvPolynomial.C (l k) * MvPolynomial.X k

theorem lin_injective (n : ℕ) : Function.Injective (lin p (n := n)) := by
  intro l l' h
  ext k
  have := congrArg (MvPolynomial.eval (Pi.single k 1)) h
  simpa [lin, Pi.single_apply] using this

theorem natDegree_D (n : ℕ) : (D p n).natDegree = p ^ n := by
  refine le_antisymm (natDegree_D_le p n) (Polynomial.le_natDegree_of_ne_zero ?_)
  have := coeff_D p n (Fin.last n)
  simp only [Fin.val_last] at this
  rw [this, minor_last]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (Δ_ne_zero p n)

theorem leadingCoeff_D (n : ℕ) : (D p n).leadingCoeff = (-1) ^ n * Δ p n := by
  rw [Polynomial.leadingCoeff, natDegree_D]
  have := coeff_D p n (Fin.last n)
  simp only [Fin.val_last] at this
  rw [this, minor_last]

/-- Each `λ · X` is a root of `D`: the first column becomes a combination of the others. -/
theorem D_eval_lin {n : ℕ} (l : Fin n → ZMod p) : (D p n).eval (lin p l) = 0 := by
  rw [D, ← Polynomial.coe_evalRingHom, map_moore]
  rw [moore, ← exists_mulVec_eq_zero_iff]
  refine ⟨Fin.cons (-1) fun k => MvPolynomial.C (l k), fun h => ?_, ?_⟩
  · have := congrFun h 0
    simp at this
  · ext i
    simp only [mulVec, dotProduct, Fin.sum_univ_succ, mooreMat, of_apply, Function.comp_apply,
      Fin.cons_zero, Fin.cons_succ, Polynomial.coe_evalRingHom, Polynomial.eval_X,
      Polynomial.eval_C, Pi.zero_apply]
    rw [lin, sum_pow_char_pow]
    simp only [mul_pow, ← map_pow, ZMod.pow_card_pow]
    simp [mul_comm]

/-- The roots of `D` are the `p^n` forms `λ · X`. -/
theorem roots_D (n : ℕ) :
    (D p n).roots = (Finset.univ.image (lin p (n := n))).val := by
  symm
  apply Multiset.eq_of_le_of_card_le
  · rw [Multiset.le_iff_subset (Finset.nodup _)]
    intro x hx
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hx
    rw [Polynomial.mem_roots]
    · exact D_eval_lin p l
    · intro h
      have := natDegree_D p n
      rw [h, Polynomial.natDegree_zero] at this
      exact pow_ne_zero _ hp.out.ne_zero this.symm
  · rw [Finset.card_val, Finset.card_image_of_injective _ (lin_injective p n)]
    simp only [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    exact (Polynomial.card_roots' _).trans (natDegree_D p n).le

/-- `P(T) = ∏_{λ ∈ 𝔽_p^n} (T − λ · X) = D(T)/((−1)ⁿ Δₙ)`. -/
noncomputable def P (n : ℕ) : (MvPolynomial (Fin n) (ZMod p))[X] :=
  ((D p n).roots.map fun a => Polynomial.X - Polynomial.C a).prod

theorem card_roots_D (n : ℕ) : Multiset.card (D p n).roots = (D p n).natDegree := by
  rw [roots_D, natDegree_D, Finset.card_val, Finset.card_image_of_injective _ (lin_injective p n)]
  simp

theorem D_eq_C_mul_P (n : ℕ) : D p n = Polynomial.C ((-1) ^ n * Δ p n) * P p n := by
  rw [← leadingCoeff_D, P, Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_D p n)]

theorem P_monic (n : ℕ) : (P p n).Monic :=
  Polynomial.monic_multiset_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a

theorem natDegree_P (n : ℕ) : (P p n).natDegree = p ^ n := by
  rw [P, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, card_roots_D, natDegree_D]

theorem lc_ne_zero (n : ℕ) : ((-1) ^ n * Δ p n : MvPolynomial (Fin n) (ZMod p)) ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (Δ_ne_zero p n)

/-- The Dickson coefficients `A_i`, polynomials in `X₁, …, Xₙ`. -/
noncomputable def A (n i : ℕ) : MvPolynomial (Fin n) (ZMod p) := (P p n).coeff (p ^ i)

theorem coeff_P_of_ne (n m : ℕ) (hm : ∀ i : Fin (n + 1), m ≠ p ^ (i : ℕ)) :
    (P p n).coeff m = 0 := by
  have h := coeff_D_of_ne p n m hm
  rw [D_eq_C_mul_P, Polynomial.coeff_C_mul] at h
  exact (mul_eq_zero.1 h).resolve_left (lc_ne_zero p n)

theorem lc_mul_A (n : ℕ) (i : Fin (n + 1)) :
    (-1) ^ n * Δ p n * A p n i = (-1) ^ (i : ℕ) * minor p n i := by
  rw [A, ← Polynomial.coeff_C_mul, ← D_eq_C_mul_P, coeff_D]

theorem A_top (n : ℕ) : A p n n = 1 := by
  rw [A, ← natDegree_P]; exact P_monic p n

theorem eval_P {n : ℕ} (x : MvPolynomial (Fin n) (ZMod p)) :
    (P p n).eval x = ∑ i : Fin (n + 1), A p n i * x ^ p ^ (i : ℕ) := by
  rw [Polynomial.eval_eq_sum_range' (n := p ^ n + 1) (by rw [natDegree_P]; omega)]
  have hsub : Finset.univ.image (fun i : Fin (n + 1) => p ^ (i : ℕ)) ⊆
      Finset.range (p ^ n + 1) := by
    intro m hm
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hm
    exact Finset.mem_range.2 (Nat.lt_succ_of_le
      (Nat.pow_le_pow_right hp.out.pos (Nat.lt_succ_iff.1 i.2)))
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · rfl
  · intro i _ j _ h; exact Fin.ext (pow_injective p h)
  · intro m _ hm
    rw [coeff_P_of_ne p n m fun i h => hm (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h.symm⟩),
      zero_mul]

theorem lin_single {n : ℕ} (k : Fin n) : lin p (Pi.single k 1) = MvPolynomial.X k := by
  simp [lin, Pi.single_apply]

/-- **The Dickson relation**: `X_k^{pⁿ} + A_{n-1} X_k^{p^{n-1}} + ⋯ + A₀ X_k = 0`. -/
theorem dickson_relation {n : ℕ} (k : Fin n) :
    (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod p)) ^ p ^ n +
      ∑ i : Fin n, A p n i * MvPolynomial.X k ^ p ^ (i : ℕ) = 0 := by
  have h := D_eval_lin p (Pi.single k 1)
  rw [D_eq_C_mul_P, Polynomial.eval_mul, Polynomial.eval_C, lin_single] at h
  have h' := (mul_eq_zero.1 h).resolve_left (lc_ne_zero p n)
  rw [eval_P, Fin.sum_univ_castSucc] at h'
  simp only [Fin.val_castSucc, Fin.val_last, A_top, one_mul] at h'
  rw [add_comm]; exact h'

/-- **`A₀ = (−1)ⁿ Δₙ^{p−1}`.** -/
theorem A_zero (n : ℕ) : A p n 0 = (-1) ^ n * Δ p n ^ (p - 1) := by
  have h := lc_mul_A p n 0
  simp only [Fin.val_zero, pow_zero, one_mul, minor_zero] at h
  have hp1 : Δ p n ^ p = Δ p n ^ (p - 1) * Δ p n := by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
  apply mul_left_cancel₀ (lc_ne_zero p n)
  rw [h, hp1]
  rw [show (-1 : MvPolynomial (Fin n) (ZMod p)) ^ n * Δ p n * ((-1) ^ n * Δ p n ^ (p - 1)) =
    ((-1) ^ n * (-1) ^ n) * (Δ p n ^ (p - 1) * Δ p n) by ring, ← mul_pow]
  simp

/-! ### Over an `𝔽_p`-algebra, `E` trivialised -/

variable {S : Type*} [CommRing S] [Algebra (ZMod p) S]

/-- The `A_i(ξ)` are defined for every `ξ ∈ V(E)`, not only where `Δₙ(ξ)` is invertible: the
Dickson relation holds at every point. -/
theorem dickson_relation_eval {n : ℕ} (ξ : Fin n → S) (k : Fin n) :
    ξ k ^ p ^ n + ∑ i : Fin n, MvPolynomial.aeval ξ (A p n i) * ξ k ^ p ^ (i : ℕ) = 0 := by
  simpa using congrArg (MvPolynomial.aeval ξ) (dickson_relation p k)

/-- **Where `Δₙ(ξ)` is invertible, the coefficients of the relation are unique, and are the
values of the polynomials `A_i`**: the `A_i^E` of the complement of the zero divisor of `Δₙ`
extend to all of `V(E)`. -/
theorem dickson_unique {n : ℕ} (ξ : Fin n → S) (hξ : IsUnit (moore p ξ)) (a : Fin n → S)
    (ha : ∀ k, ξ k ^ p ^ n + ∑ i : Fin n, a i * ξ k ^ p ^ (i : ℕ) = 0) :
    a = fun i : Fin n => MvPolynomial.aeval ξ (A p n i) := by
  set v : Fin n → S := fun i => a i - MvPolynomial.aeval ξ (A p n i)
  have hv : v ᵥ* mooreMat p ξ = 0 := by
    ext k
    have h1 := ha k
    have h2 := dickson_relation_eval p ξ k
    simp only [vecMul, dotProduct, mooreMat, of_apply, v, sub_mul, Finset.sum_sub_distrib,
      Pi.zero_apply]
    linear_combination h1 - h2
  have : v = 0 := by
    rw [← vecMul_one v, ← mul_nonsing_inv (mooreMat p ξ) hξ, ← vecMul_vecMul, hv, zero_vecMul]
  funext i
  exact sub_eq_zero.1 (congrFun this i)

theorem A_zero_eval {n : ℕ} (ξ : Fin n → S) :
    MvPolynomial.aeval ξ (A p n 0) = (-1) ^ n * moore p ξ ^ (p - 1) := by
  rw [A_zero, map_mul, map_pow, map_pow, map_neg, map_one, Δ]
  congr 2
  have := map_moore p (MvPolynomial.aeval (R := ZMod p) ξ).toRingHom
    (MvPolynomial.X : Fin n → MvPolynomial (Fin n) (ZMod p))
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this]; congr 1; ext k; simp

/-! ### Page 13: the sign in the Corollary -/

/-- **The Corollary of page 13 fails as stated.** Over `𝔽₃`, with `n = 1` and `M = 𝔽₃`, the
kernel of `x³ − x`, one has `a₀ = A₀(1) = −1`, which has no square root in `𝔽₃`, while
`Λ¹M = M` has two trivialisations (its two nonzero elements). -/
theorem corollaire_page13_faux :
    MvPolynomial.aeval (fun _ : Fin 1 => (1 : ZMod 3)) (A 3 1 0) = -1 ∧
      (¬ ∃ y : ZMod 3, y ^ (3 - 1) = -1) ∧ Fintype.card {t : ZMod 3 // t ≠ 0} = 2 := by
  refine ⟨?_, by decide, by decide⟩
  rw [A_zero_eval]
  simp [moore, mooreMat, det_unique]

/-- `g · e`, with `(g · e)_j = Σ_k g_{jk} e_k`, for a matrix `g` over `𝔽_p`. -/
def act {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod p)) (e : Fin n → S) : Fin n → S :=
  fun j => ∑ k, algebraMap (ZMod p) S (g j k) * e k

/-- **`Δₙ(g · e) = det g · Δₙ(e)`**: the coefficients of `g` are fixed by the Frobenius, so the
Moore matrix of `g · e` is that of `e` times `gᵀ`. -/
theorem moore_act [CharP S p] {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod p)) (e : Fin n → S) :
    moore p (act p g e) = algebraMap (ZMod p) S g.det * moore p e := by
  have h : mooreMat p (act p g e) = mooreMat p e * (g.map (algebraMap (ZMod p) S))ᵀ := by
    ext i j
    simp only [mooreMat, act, of_apply, mul_apply, transpose_apply, map_apply]
    rw [sum_pow_char_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, ← map_pow, ZMod.pow_card_pow, mul_comm]
  rw [moore, h, det_mul, det_transpose, RingHom.map_det, RingHom.mapMatrix_apply, mul_comm, moore]

/-- `Δₙ(e)` is a `(p − 1)`-th root of `(−1)ⁿ a₀`, `a₀ = A₀(e)`. -/
theorem moore_pow_sub_one {n : ℕ} (e : Fin n → S) :
    moore p e ^ (p - 1) = (-1) ^ n * MvPolynomial.aeval e (A p n 0) := by
  rw [A_zero_eval, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

variable {K : Type*} [Field K] [Algebra (ZMod p) K]

/-- In a field of characteristic `p`, the solutions of `c^p = c` are the elements of `𝔽_p`. -/
theorem eq_algebraMap_of_pow_eq (c : K) (hc : c ^ p = c) :
    ∃ a : ZMod p, algebraMap (ZMod p) K a = c := by
  classical
  by_contra h
  simp only [not_exists] at h
  have hQ : (X ^ p - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hp.out.one_lt
  have hroot : ∀ x : K, x ^ p = x → x ∈ (X ^ p - X : K[X]).roots := fun x hx => by
    rw [mem_roots hQ, IsRoot.def, eval_sub, eval_pow, eval_X, hx, sub_self]
  set s : Finset K := insert c (Finset.univ.image (algebraMap (ZMod p) K))
  have hs : s.val ≤ (X ^ p - X : K[X]).roots := by
    rw [Multiset.le_iff_subset s.nodup]
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hroot _ hc
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
      exact hroot _ (by rw [← map_pow, ZMod.pow_card])
  have hcard : s.card = p + 1 := by
    rw [Finset.card_insert_of_notMem (by simp [h]),
      Finset.card_image_of_injective _ (algebraMap (ZMod p) K).injective, Finset.card_univ,
      ZMod.card]
  have := (Multiset.card_le_card hs).trans (card_roots' _)
  rw [Finset.card_val, hcard, FiniteField.X_pow_card_sub_X_natDegree_eq K hp.out.one_lt] at this
  omega

/-- **The corrected Corollary, over a field.** For `e ∈ Kⁿ` with `Δₙ(e) ≠ 0` (a basis of an
`n`-dimensional `𝔽_p`-subspace `M ⊂ K`), every `(p − 1)`-th root of `(−1)ⁿ a₀` is `Δₙ(g · e)`
for some `g ∈ GLₙ(𝔽_p)`. -/
theorem moore_act_surj {n : ℕ} (hn : 0 < n) (e : Fin n → K) (he : moore p e ≠ 0) (y : K)
    (hy : y ^ (p - 1) = (-1) ^ n * MvPolynomial.aeval e (A p n 0)) :
    ∃ g : Matrix (Fin n) (Fin n) (ZMod p), IsUnit g.det ∧ moore p (act p g e) = y := by
  have := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  rw [← moore_pow_sub_one] at hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hp1] at hy
    exact he ((pow_eq_zero_iff hp1).1 hy.symm)
  set c := y / moore p e with hcdef
  have hc1 : c ^ (p - 1) = 1 := by rw [div_pow, hy, div_self (pow_ne_zero _ he)]
  have hc : c ^ p = c := by
    rw [← Nat.sub_add_cancel hp.out.one_le, pow_succ, hc1, one_mul]
  obtain ⟨a, ha⟩ := eq_algebraMap_of_pow_eq p c hc
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact div_ne_zero hy0 he ha.symm
  have hdet : (diagonal (Function.update 1 (⟨0, hn⟩ : Fin n) a)).det = a := by
    rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  refine ⟨diagonal (Function.update 1 (⟨0, hn⟩ : Fin n) a), by rw [hdet]; exact ha0.isUnit, ?_⟩
  rw [moore_act, hdet, ha, hcdef, div_mul_cancel₀ _ he]

/-- **The fibres are the `SLₙ(𝔽_p)`-orbits**: `Δₙ(g · e) = Δₙ(h · e)` iff `det g = det h`. -/
theorem moore_act_eq_iff {n : ℕ} (e : Fin n → K) (he : moore p e ≠ 0)
    (g h : Matrix (Fin n) (Fin n) (ZMod p)) :
    moore p (act p g e) = moore p (act p h e) ↔ g.det = h.det := by
  have := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  rw [moore_act, moore_act, mul_left_inj' he, (algebraMap (ZMod p) K).injective.eq_iff]

end Grothendieck.Folder160
