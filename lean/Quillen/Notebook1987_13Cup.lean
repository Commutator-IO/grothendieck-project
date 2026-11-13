import Mathlib

/-!
# Quillen, notebook 1987-13, pp. 71-74: the cup product of Hochschild cochains

Daniel Quillen's research notebook 1987-13 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201987/1987-13.pdf>),
pp. 71-74. For Hochschild cochains of an associative ring `A` with values in `A`, the cup
product `(φ ∪ ψ)(a₀, …, a_{p+q−1}) = φ(a₀, …, a_{p−1}) ψ(a_p, …, a_{p+q−1})` satisfies the
Leibniz rule `b(φ ∪ ψ) = bφ ∪ ψ + (−1)^p φ ∪ bψ` (`coboundary_cup`, p. 72, boxed); then, for a
derivation `X`, `f = X ∘ X` has `f(a₁a₂) = f(a₁)a₂ + 2X(a₁)X(a₂) + a₁f(a₂)`, so
`X ∪ X = −½ bf` (`cup_self_eq`, p. 73); for `X = [c, ·]` inner, `s(a) = a + h c Y(a)` is a
homomorphism into the deformation `a₁ * a₂ = a₁a₂ + h X(a₁)Y(a₂)` (`inner_section`, p. 73);
and `s(a) = a + h XY(a)` gives the coboundary `−(Xa₁Ya₂ + Ya₁Xa₂)` (`section_XY`, p. 74).

*The model.* A `p`-cochain is a function `φ : (ℕ → A) → A` that depends only on the first `p`
terms of the sequence (`DependsOn p φ`); this is the same as a function of `p`-tuples, and lets
the shift `a ↦ (a_p, a_{p+1}, …)` and the contraction `a ↦ (a₀, …, a_i a_{i+1}, …)` be stated
without arithmetic on `Fin`. The coboundary is
`(bφ)(a) = a₀ φ(a₁, …) + Σ_{i<p} (−1)^{i+1} φ(…, a_i a_{i+1}, …) + (−1)^{p+1} φ(a) a_p`. No
linearity is needed: the Leibniz rule holds for arbitrary functions.
-/

namespace Quillen.Notebook1987_13Cup

open Finset

variable {A : Type*} [Ring A]

/-- The shift `(a_n, a_{n+1}, …)`. -/
def shift (n : ℕ) (a : ℕ → A) : ℕ → A := fun j => a (j + n)

/-- The contraction of `a_i` and `a_{i+1}`: `(a₀, …, a_{i−1}, a_i a_{i+1}, a_{i+2}, …)`. -/
def merge (i : ℕ) (a : ℕ → A) : ℕ → A :=
  fun j => if j < i then a j else if j = i then a i * a (i + 1) else a (j + 1)

/-- `φ` is a `p`-cochain: it depends only on `a₀, …, a_{p−1}`. -/
def DependsOn (p : ℕ) (φ : (ℕ → A) → A) : Prop :=
  ∀ a a' : ℕ → A, (∀ j < p, a j = a' j) → φ a = φ a'

/-- The Hochschild coboundary of a `p`-cochain. -/
def b (p : ℕ) (φ : (ℕ → A) → A) : (ℕ → A) → A := fun a =>
  a 0 * φ (shift 1 a) + ∑ i ∈ range p, ((-1 : ℤ) ^ (i + 1)) • φ (merge i a) +
    ((-1 : ℤ) ^ (p + 1)) • (φ a * a p)

/-- The cup product of a `p`-cochain and a cochain. -/
def cup (p : ℕ) (φ ψ : (ℕ → A) → A) : (ℕ → A) → A := fun a => φ a * ψ (shift p a)

omit [Ring A] in
theorem shift_shift (m n : ℕ) (a : ℕ → A) : shift m (shift n a) = shift (m + n) a := by
  funext j; simp only [shift]; congr 1; omega

theorem shift_merge_of_lt {i p : ℕ} (h : i < p) (a : ℕ → A) :
    shift p (merge i a) = shift (p + 1) a := by
  funext j
  simp only [shift, merge]
  split_ifs <;> first | omega | rfl

theorem shift_merge_add (p k : ℕ) (a : ℕ → A) :
    shift p (merge (p + k) a) = merge k (shift p a) := by
  funext j
  simp only [shift, merge]
  split_ifs <;> first | omega | (congr 1; omega) | (congr 2 <;> omega)

theorem merge_apply_of_lt {i j : ℕ} (h : j < i) (a : ℕ → A) : merge i a j = a j := by
  simp [merge, h]

/-- **The Leibniz rule for the cup product** (p. 72): for a `p`-cochain `φ` and any `ψ`,
`b(φ ∪ ψ) = bφ ∪ ψ + (−1)^p φ ∪ bψ`, where `φ ∪ ψ` is a `(p + q)`-cochain. -/
theorem coboundary_cup (p q : ℕ) (φ ψ : (ℕ → A) → A) (hφ : DependsOn p φ) (a : ℕ → A) :
    b (p + q) (cup p φ ψ) a =
      cup (p + 1) (b p φ) ψ a + ((-1 : ℤ) ^ p) • cup p φ (b q ψ) a := by
  simp only [b, cup]
  rw [sum_range_add]
  -- the terms contracting inside the block of `φ`
  have h1 : ∀ i ∈ range p, ((-1 : ℤ) ^ (i + 1)) • (φ (merge i a) * ψ (shift p (merge i a))) =
      ((-1 : ℤ) ^ (i + 1)) • φ (merge i a) * ψ (shift (p + 1) a) := fun i hi => by
    rw [shift_merge_of_lt (mem_range.mp hi), smul_mul_assoc]
  -- the terms contracting inside the block of `ψ`
  have h2 : ∀ k ∈ range q, ((-1 : ℤ) ^ (p + k + 1)) •
      (φ (merge (p + k) a) * ψ (shift p (merge (p + k) a))) =
      ((-1 : ℤ) ^ p) • (φ a * ((-1 : ℤ) ^ (k + 1)) • ψ (merge k (shift p a))) := fun k _ => by
    rw [shift_merge_add, hφ (merge (p + k) a) a fun j hj => merge_apply_of_lt (by omega) a,
      mul_smul_comm, smul_smul, ← pow_add, add_assoc]
  rw [sum_congr rfl h1, sum_congr rfl h2, shift_shift, shift_shift 1 p, add_comm 1 p]
  have h4 : shift p a q = a (p + q) := by simp [shift, add_comm]
  have h5 : shift p a 0 = a p := by simp [shift]
  rw [h4, h5]
  simp only [add_mul, mul_add, smul_add, sum_mul, mul_sum, smul_sum, mul_assoc, smul_mul_assoc,
    mul_smul_comm, smul_smul, ← pow_add]
  have e1 : (-1 : ℤ) ^ (p + q + 1) = (-1) ^ (p + (q + 1)) := by ring
  have e2 : (-1 : ℤ) ^ (p + 1) = -(-1) ^ p := by ring
  rw [e1, e2, neg_smul]
  abel

/-- A derivation of the (noncommutative) ring `A` into itself. -/
structure IsDerivation (X : A → A) : Prop where
  map_add : ∀ a b, X (a + b) = X a + X b
  leibniz : ∀ a b, X (a * b) = X a * b + a * X b

/-- For `f = X ∘ X`, `f(a₁a₂) = f(a₁)a₂ + 2X(a₁)X(a₂) + a₁f(a₂)` (p. 73). -/
theorem sq_derivation_mul {X : A → A} (hX : IsDerivation X) (a₁ a₂ : A) :
    X (X (a₁ * a₂)) = X (X a₁) * a₂ + 2 * (X a₁ * X a₂) + a₁ * X (X a₂) := by
  rw [hX.leibniz, hX.map_add, hX.leibniz, hX.leibniz]
  noncomm_ring

/-- `X ∪ X = −½ b(X ∘ X)` for a derivation `X`, when `2` is invertible (p. 73):
`X(a₁)X(a₂) = −½ (a₁f(a₂) − f(a₁a₂) + f(a₁)a₂)`. -/
theorem cup_self_eq {X : A → A} (hX : IsDerivation X) {t : A} (ht : t * 2 = 1) (a₁ a₂ : A) :
    X a₁ * X a₂ = -t * (a₁ * X (X a₂) - X (X (a₁ * a₂)) + X (X a₁) * a₂) := by
  rw [sq_derivation_mul hX, show a₁ * X (X a₂) - (X (X a₁) * a₂ + 2 * (X a₁ * X a₂) +
      a₁ * X (X a₂)) + X (X a₁) * a₂ = -(2 * (X a₁ * X a₂)) by noncomm_ring,
    neg_mul_neg, ← mul_assoc, ht, one_mul]

/-- For `X = [c, ·]` inner and `Y` a derivation, `s(a) = a + h c Y(a)` is a homomorphism into
the deformation `a₁ * a₂ = a₁a₂ + h X(a₁) Y(a₂)` of `A[h]/h²` (p. 73): the `h`-component of
`s(a₁) * s(a₂)` is `c Y(a₁a₂)`. -/
theorem inner_section {Y : A → A} (hY : IsDerivation Y) (c a₁ a₂ : A) :
    a₁ * (c * Y a₂) + c * Y a₁ * a₂ + (c * a₁ - a₁ * c) * Y a₂ = c * Y (a₁ * a₂) := by
  rw [hY.leibniz]
  noncomm_ring

/-- For derivations `X`, `Y`, the section `s(a) = a + h XY(a)` of the trivial deformation gives
the cocycle `s(a₁)s(a₂) − s(a₁a₂) = −h(Xa₁Ya₂ + Ya₁Xa₂)` (p. 74). -/
theorem section_XY {X Y : A → A} (hX : IsDerivation X) (hY : IsDerivation Y) (a₁ a₂ : A) :
    a₁ * X (Y a₂) + X (Y a₁) * a₂ - X (Y (a₁ * a₂)) = -(X a₁ * Y a₂ + Y a₁ * X a₂) := by
  rw [hY.leibniz, hX.map_add, hX.leibniz, hX.leibniz]
  noncomm_ring

/-- The cup product of two derivations is a `2`-cocycle (p. 73): a derivation is a `1`-cocycle,
`bX = 0`, so `b(X ∪ Y) = 0` by the Leibniz rule. -/
theorem coboundary_cup_derivations {X Y : A → A} (hX : IsDerivation X) (hY : IsDerivation Y)
    (a : ℕ → A) : b 2 (cup 1 (fun a => X (a 0)) (fun a => Y (a 0))) a = 0 := by
  have hb : ∀ (Z : A → A), IsDerivation Z → ∀ a : ℕ → A, b 1 (fun a => Z (a 0)) a = 0 := by
    intro Z hZ a
    simp only [b, shift, merge, sum_range_one]
    simp [hZ.leibniz]
  rw [show (2 : ℕ) = 1 + 1 from rfl, coboundary_cup 1 1 _ _ (fun a a' h => by rw [h 0 one_pos]) a]
  simp only [cup, hb X hX, hb Y hY, zero_mul, mul_zero, smul_zero, add_zero]

end Quillen.Notebook1987_13Cup
