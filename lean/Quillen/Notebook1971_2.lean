import Mathlib

/-!
# Quillen, notebook 1971-2, p. 12: an automorphism killed locally by `(ψ - p) ⋯ (ψ - pⁿ)` makes the group uniquely `p`-divisible

Daniel Quillen's research notebook 1971-2 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201971/1971-2.pdf>) proves, on
p. 12 (February 3, 1971), that the higher `K`-groups of a perfect ring of characteristic `p` are
uniquely `p`-divisible. The Frobenius induces the Adams operation `Ψ^p`, an automorphism, and
every `x` is killed by `(Ψ^p − p) ⋯ (Ψ^p − pⁿ)` for some `n` (a fact the page takes as known).
With `F_n` the elements killed by this product, `Ψ^p = pⁿ` on `F_n / F_{n−1}`, so each quotient is
uniquely `p`-divisible because `Ψ^p` is an automorphism, and so is the union.

This file proves the algebraic part of the argument, for an abelian group `M`, an automorphism
`ψ` (given with its inverse `ψ'`) and any natural number `p`:

* `P ψ p n = (ψ − p) ⋯ (ψ − pⁿ)`, as an element of the ring `Module.End ℤ M`;
* `bijOn_ker`: multiplication by `p` maps the kernel `F_n` of `P ψ p n` bijectively onto
  itself, by induction on `n` (the page's step on `F_n / F_{n−1}`, done inside `F_n`);
* `bijective_nsmul`: **the statement of the page**: if every element is killed by some
  `P ψ p n`, then `x ↦ p x` is bijective on `M`.

The `K`-theoretic input (that `Ψ^p` is the Frobenius and the local nilpotence of the product)
is not formalised.
-/

namespace Quillen.Notebook1971_2

variable {M : Type*} [AddCommGroup M]

/-- `P ψ p n = (ψ - p) (ψ - p²) ⋯ (ψ - pⁿ)`. -/
def P (ψ : Module.End ℤ M) (p : ℕ) : ℕ → Module.End ℤ M
  | 0 => 1
  | n + 1 => P ψ p n * (ψ - (p : Module.End ℤ M) ^ (n + 1))

variable {ψ ψ' : Module.End ℤ M} {p : ℕ}

theorem commute_P {f : Module.End ℤ M} (hf : Commute f ψ) (n : ℕ) : Commute f (P ψ p n) := by
  induction n with
  | zero => exact Commute.one_right f
  | succ n ih => exact ih.mul_right (hf.sub_right ((Nat.cast_commute p f).symm.pow_right _))

theorem natCast_pow_apply (k n : ℕ) (x : M) :
    ((n : Module.End ℤ M) ^ k) x = n ^ k • x := by
  rw [← Nat.cast_pow, Module.End.natCast_apply]

theorem P_succ_apply (n : ℕ) (x : M) :
    P ψ p (n + 1) x = P ψ p n ((ψ - (p : Module.End ℤ M) ^ (n + 1)) x) := rfl

theorem P_succ_eq_zero {n : ℕ} {x : M} (hx : P ψ p n x = 0) : P ψ p (n + 1) x = 0 := by
  have hc : Commute (ψ - (p : Module.End ℤ M) ^ (n + 1)) (P ψ p n) :=
    commute_P ((Commute.refl ψ).sub_left ((Nat.cast_commute p ψ).pow_left _)) n
  have : P ψ p (n + 1) = (ψ - (p : Module.End ℤ M) ^ (n + 1)) * P ψ p n := hc.symm.eq
  rw [this, Module.End.mul_apply, hx, map_zero]

/-- Surjectivity of `p` on a subset stable under `nsmul` gives surjectivity of every power. -/
theorem exists_pow_nsmul {S : Set M} (hS : ∀ x ∈ S, ∃ z ∈ S, p • z = x) (k : ℕ) :
    ∀ x ∈ S, ∃ z ∈ S, p ^ k • z = x := by
  induction k with
  | zero => exact fun x hx => ⟨x, hx, by simp⟩
  | succ k ih =>
    intro x hx
    obtain ⟨y, hy, rfl⟩ := ih x hx
    obtain ⟨z, hz, rfl⟩ := hS y hy
    exact ⟨z, hz, by rw [smul_smul, ← pow_succ]⟩

/-- Multiplication by `p` maps `F_n = ker P ψ p n` bijectively onto itself. -/
theorem bijOn_ker (h1 : ψ * ψ' = 1) (h2 : ψ' * ψ = 1) (n : ℕ) :
    (∀ x, P ψ p n x = 0 → p • x = 0 → x = 0) ∧
      (∀ x, P ψ p n x = 0 → ∃ z, P ψ p n z = 0 ∧ p • z = x) := by
  have hψ' : Commute ψ' ψ := h2.trans h1.symm
  have inv : ∀ x, ψ' (ψ x) = x := fun x => by
    rw [← Module.End.mul_apply, h2, Module.End.one_apply]
  induction n with
  | zero =>
    refine ⟨fun x hx _ => hx, fun x hx => ⟨0, map_zero _, ?_⟩⟩
    rw [smul_zero]; exact hx.symm
  | succ n ih =>
    obtain ⟨ihi, ihs⟩ := ih
    set c : Module.End ℤ M := (p : Module.End ℤ M) ^ (n + 1)
    have hc : ∀ x, c x = p ^ (n + 1) • x := natCast_pow_apply _ _
    constructor
    · intro x hx hpx
      have hy : (ψ - c) x = 0 := by
        refine ihi _ hx ?_
        rw [← map_nsmul, hpx, map_zero]
      have hψx : ψ x = 0 := by
        rw [LinearMap.sub_apply, sub_eq_zero, hc, pow_succ, ← smul_smul, hpx,
          smul_zero] at hy
        exact hy
      rw [← inv x, hψx, map_zero]
    · intro x hx
      obtain ⟨w, hw, hw'⟩ := exists_pow_nsmul (S := {z | P ψ p n z = 0})
        (fun y hy => ihs y hy) (n + 1) ((ψ - c) x) hx
      have hψx : ψ x = p ^ (n + 1) • (x + w) := by
        rw [smul_add, hw', LinearMap.sub_apply, hc]; abel
      refine ⟨ψ' (p ^ n • (x + w)), ?_, ?_⟩
      · rw [← Module.End.mul_apply, (commute_P hψ' (n + 1)).symm.eq, Module.End.mul_apply,
          map_nsmul, map_add, hx, P_succ_eq_zero hw, add_zero, smul_zero, map_zero]
      · rw [← map_nsmul, smul_smul, ← pow_succ', ← hψx, inv]

/-- **Quillen, notebook 1971-2, p. 12.** Let `ψ` be an automorphism of an abelian group `M`
such that every `x` is killed by `(ψ - p) (ψ - p²) ⋯ (ψ - pⁿ)` for some `n`. Then `M` is uniquely
`p`-divisible. -/
theorem bijective_nsmul (h1 : ψ * ψ' = 1) (h2 : ψ' * ψ = 1)
    (hloc : ∀ x : M, ∃ n, P ψ p n x = 0) :
    Function.Bijective fun x : M => p • x := by
  constructor
  · intro x y hxy
    have hxy' : p • (x - y) = 0 := by simp only at hxy; rw [smul_sub, hxy, sub_self]
    obtain ⟨n, hn⟩ := hloc (x - y)
    exact sub_eq_zero.mp ((bijOn_ker h1 h2 n).1 _ hn hxy')
  · intro x
    obtain ⟨n, hn⟩ := hloc x
    obtain ⟨z, -, hz⟩ := (bijOn_ker h1 h2 n).2 x hn
    exact ⟨z, hz⟩

end Quillen.Notebook1971_2
