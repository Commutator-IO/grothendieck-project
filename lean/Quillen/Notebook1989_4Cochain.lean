import Mathlib

/-!
# Quillen, notebook 1989-4, pp. 70-71: `(bs + sb)ψ = ψ − ψ^λ`

Daniel Quillen's research notebook 1989-4 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201989/1989-4.pdf>).

On Hochschild cochains `ψ : A^{n+1} → M` of a unital algebra, with
`(sψ)(a₁, …, aₙ) = ψ(1, a₁, …, aₙ)`, `b = b' + (−1)^{m}·(crossover)`, and the cyclic operator
`ψ^λ(a₀, …, aₙ) = (−1)^{n−1}ψ(1, aₙa₀, a₁, …, aₙ₋₁) + (−1)ⁿψ(aₙ, a₀, …, aₙ₋₁)`, the page proves
`(bs + sb)ψ = ψ − ψ^λ` (p. 71, boxed): `ψ ↦ ψ^λ` is homotopic to the identity on the
Hochschild complex.

Here (`bs_add_sb`): `A` is any monoid (only `1` and the product enter), `M` any additive group,
cochains are functions `(Fin m → A) → M`, inner faces are `Fin.contractNth`; `n = k + 1 ≥ 1`.
Also `b's + sb' = 1` (`b'_s_add_s_b'`). Neither needs `ψ` normalised.

Correction: the intermediate box of p. 70 gives the two crossover terms with the signs
`(−1)^{n+1}` and `(−1)ⁿ`; the lines above it (and p. 71) give `(−1)ⁿ` and `(−1)^{n+1}`, which is
what holds and what makes `ψ − ψ^λ` come out. The slip may be the transcription's.
-/

namespace Quillen.Notebook1989_4Cochain

open Fin

variable {A : Type*} [Monoid A] {M : Type*} [AddCommGroup M]

/-- Cochains with `m` arguments. -/
abbrev C (A M : Type*) (m : ℕ) := (Fin m → A) → M

/-- `(sψ)(a₁, …, aₘ) = ψ(1, a₁, …, aₘ)`. -/
def s {m : ℕ} (ψ : C A M (m + 1)) : C A M m := fun a => ψ (cons 1 a)

/-- `(b'φ)(a₀, …, aₖ₊₁) = Σ_{i ≤ k} (−1)ⁱ φ(…, aᵢaᵢ₊₁, …)`. -/
def b' {k : ℕ} (φ : C A M (k + 1)) : C A M (k + 2) := fun a =>
  ∑ i : Fin (k + 1), (-1 : ℤ) ^ (i : ℕ) • φ (contractNth i.castSucc (· * ·) a)

/-- `(aₖ₊₁a₀, a₁, …, aₖ)`. -/
def cyc {k : ℕ} (a : Fin (k + 2) → A) : Fin (k + 1) → A :=
  cons (a (last (k + 1)) * a 0) fun j : Fin k => a j.succ.castSucc

/-- The Hochschild coboundary `b = b' + (−1)^{k+1}·(crossover)`. -/
def b {k : ℕ} (φ : C A M (k + 1)) : C A M (k + 2) := fun a =>
  b' φ a + (-1 : ℤ) ^ (k + 1) • φ (cyc a)

/-- `ψ^λ(a₀, …, aₙ) = (−1)^{n−1}ψ(1, aₙa₀, a₁, …) + (−1)ⁿψ(aₙ, a₀, …, aₙ₋₁)`, `n = k + 1`. -/
def lam {k : ℕ} (ψ : C A M (k + 2)) : C A M (k + 2) := fun a =>
  (-1 : ℤ) ^ k • ψ (cons 1 (cyc a)) + (-1 : ℤ) ^ (k + 1) • ψ (cons (a (last (k + 1))) (init a))

theorem contractNth_succ_cons {α : Type*} {n : ℕ} (op : α → α → α) (j : Fin (n + 1)) (x : α)
    (g : Fin (n + 1) → α) : contractNth j.succ op (cons x g) = cons x (contractNth j op g) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · rw [contractNth_apply_of_lt _ _ _ _ (by simp)]; simp
  · simp only [contractNth, cons_succ, val_succ, Nat.add_lt_add_iff_right,
      Nat.add_right_cancel_iff]
    split_ifs <;> simp

theorem contractNth_zero_cons_one {n : ℕ} (a : Fin (n + 1) → A) :
    contractNth 0 (· * ·) (cons (1 : A) a) = a := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · rw [contractNth_apply_of_eq _ _ _ _ rfl]; simp
  · rw [contractNth_apply_of_gt _ _ _ _ (by simp)]; simp

/-- `(sb'ψ)(a) = ψ(a) − (b'sψ)(a)`. -/
theorem s_b' {k : ℕ} (ψ : C A M (k + 2)) (a : Fin (k + 2) → A) :
    s (b' ψ) a = ψ a - b' (s ψ) a := by
  simp only [s, b']
  rw [Fin.sum_univ_succ]
  simp only [val_zero, pow_zero, one_smul, castSucc_zero, contractNth_zero_cons_one, val_succ,
    pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, ← succ_castSucc,
    contractNth_succ_cons]
  abel

/-- `b's + sb' = 1`. -/
theorem b'_s_add_s_b' {k : ℕ} (ψ : C A M (k + 2)) (a : Fin (k + 2) → A) :
    b' (s ψ) a + s (b' ψ) a = ψ a := by
  rw [s_b']; abel

theorem cyc_cons_one {k : ℕ} (a : Fin (k + 2) → A) :
    cyc (cons (1 : A) a) = cons (a (last (k + 1))) (init a) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [cyc, cons_zero, mul_one]
    rw [← succ_last, cons_succ]
  · simp [cyc, init]

/-- **Notebook 1989-4, p. 71** (boxed): `(bs + sb)ψ = ψ − ψ^λ`. -/
theorem bs_add_sb {k : ℕ} (ψ : C A M (k + 2)) (a : Fin (k + 2) → A) :
    b (s ψ) a + s (b ψ) a = ψ a - lam ψ a := by
  have h1 : b (s ψ) a = b' (s ψ) a + (-1 : ℤ) ^ (k + 1) • ψ (cons 1 (cyc a)) := rfl
  have h2 : s (b ψ) a = s (b' ψ) a + (-1 : ℤ) ^ (k + 2) • ψ (cons (a (last (k + 1))) (init a)) := by
    simp only [s, b, cyc_cons_one]
  rw [h1, h2, s_b', lam]
  simp only [pow_succ, mul_neg_one, neg_smul, neg_neg]
  abel

end Quillen.Notebook1989_4Cochain
