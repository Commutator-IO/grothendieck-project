import Mathlib

/-!
# Quillen, notebook 1989-2, pp. 94-95: the cyclic bar construction of a group

Daniel Quillen's research notebook 1989-2 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201989/1989-2.pdf>).

The cyclic bar construction of a group `G` has `n`-simplices `G^{n+1}`, faces
`dᵢ(g₀, …, gₙ) = (…, gᵢgᵢ₊₁, …)` for `i < n` and `dₙ(g₀, …, gₙ) = (gₙg₀, g₁, …, gₙ₋₁)`. The page
compares it with `G × Gⁿ`, faces `d₀(x, g) = (g₁⁻¹xg₁, g₂, …)`, `dᵢ` multiplying `gᵢgᵢ₊₁`,
`dₙ` dropping `gₙ`, through `Φ(x, g₁, …, gₙ) = ((g₁⋯gₙ)⁻¹x, g₁, …, gₙ)`, and checks that `Φ` is
an isomorphism of simplicial sets. Here: `Φ` is a bijection (`Φ_bijective`) and commutes with
every face (`Φ_face_zero`, `Φ_face_inner`, `Φ_face_last`). The simplicial identities and the
degeneracies are not formalised; tuples are `Fin n → G`, products `Fin.partialProd`, inner
faces `Fin.contractNth`.
-/

namespace Quillen.Notebook1989_2Simplicial

open Fin

variable {G : Type*} [Group G]

/-- The total product `g₁⋯gₙ`. -/
def tot {n : ℕ} (g : Fin n → G) : G := partialProd g (last n)

theorem tot_succ {n : ℕ} (g : Fin (n + 1) → G) : tot g = g 0 * tot (tail g) := by
  rw [tot, ← succ_last, partialProd_succ']; rfl

theorem tot_succ' {n : ℕ} (g : Fin (n + 1) → G) : tot g = tot (init g) * g (last n) := by
  rw [tot, ← succ_last, partialProd_succ, tot, partialProd_init]

theorem tot_contractNth {n : ℕ} (j : Fin n) (g : Fin (n + 1) → G) :
    tot (contractNth j.castSucc (· * ·) g) = tot g := by
  rw [tot, partialProd_contractNth, Function.comp_apply, tot,
    succAbove_of_le_castSucc _ _ (le_castSucc_iff.mpr (by simp [Fin.lt_def])),
    succ_last]

/-- `Φ(x, g₁, …, gₙ) = ((g₁⋯gₙ)⁻¹x, g₁, …, gₙ)`. -/
def Φ {n : ℕ} (xg : G × (Fin n → G)) : Fin (n + 1) → G := cons ((tot xg.2)⁻¹ * xg.1) xg.2

/-- The inverse of `Φ`. -/
def Ψ {n : ℕ} (y : Fin (n + 1) → G) : G × (Fin n → G) := (tot (tail y) * y 0, tail y)

theorem Ψ_Φ {n : ℕ} (xg : G × (Fin n → G)) : Ψ (Φ xg) = xg := by
  simp [Ψ, Φ]

theorem Φ_Ψ {n : ℕ} (y : Fin (n + 1) → G) : Φ (Ψ y) = y := by
  simp [Ψ, Φ]

theorem Φ_bijective (n : ℕ) : Function.Bijective (Φ : G × (Fin n → G) → Fin (n + 1) → G) :=
  Function.bijective_iff_has_inverse.mpr ⟨Ψ, Ψ_Φ, Φ_Ψ⟩

/-! Faces of `G × Gⁿ` (from `n + 1` to `n`). -/

/-- `d₀(x, g) = (g₁⁻¹xg₁, g₂, …, gₙ₊₁)`. -/
def faceZero {n : ℕ} (xg : G × (Fin (n + 1) → G)) : G × (Fin n → G) :=
  ((xg.2 0)⁻¹ * xg.1 * xg.2 0, tail xg.2)

/-- `dⱼ₊₁(x, g) = (x, g₁, …, gⱼ₊₁gⱼ₊₂, …)`, for `j < n`. -/
def faceInner {n : ℕ} (j : Fin n) (xg : G × (Fin (n + 1) → G)) : G × (Fin n → G) :=
  (xg.1, contractNth j.castSucc (· * ·) xg.2)

/-- `dₙ₊₁(x, g) = (x, g₁, …, gₙ)`. -/
def faceLast {n : ℕ} (xg : G × (Fin (n + 1) → G)) : G × (Fin n → G) := (xg.1, init xg.2)

/-- The last face of the cyclic bar construction, `(g₀, …, gₙ₊₁) ↦ (gₙ₊₁g₀, g₁, …, gₙ)`. -/
def cycLast {n : ℕ} (y : Fin (n + 2) → G) : Fin (n + 1) → G :=
  cons (y (last (n + 1)) * y 0) fun j : Fin n => y j.succ.castSucc

/-- **Notebook 1989-2, p. 94**: `Φ d₀ = d₀ Φ`. -/
theorem Φ_face_zero {n : ℕ} (xg : G × (Fin (n + 1) → G)) :
    Φ (faceZero xg) = contractNth 0 (· * ·) (Φ xg) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · rw [contractNth_apply_of_eq _ _ _ _ rfl]
    simp [Φ, faceZero, tot_succ xg.2, mul_assoc]
  · rw [contractNth_apply_of_gt _ _ _ _ (by simp)]
    simp [Φ, faceZero, tail]

/-- `contractNth` at `j + 1` of a `cons` is the `cons` of `contractNth` at `j`. -/
theorem contractNth_succ_cons {n : ℕ} (j : Fin (n + 1)) (a : G) (g : Fin (n + 1) → G) :
    contractNth j.succ (· * ·) (cons a g) = cons a (contractNth j (· * ·) g) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · rw [contractNth_apply_of_lt _ _ _ _ (by simp)]; simp
  · simp only [contractNth, cons_succ, val_succ, Nat.add_lt_add_iff_right,
      Nat.add_right_cancel_iff]
    split_ifs <;> simp

/-- **Notebook 1989-2, p. 95**: `Φ dᵢ = dᵢ Φ` for the inner faces. -/
theorem Φ_face_inner {n : ℕ} (j : Fin n) (xg : G × (Fin (n + 1) → G)) :
    Φ (faceInner j xg) = contractNth j.castSucc.succ (· * ·) (Φ xg) := by
  rw [Φ, Φ, contractNth_succ_cons, faceInner, tot_contractNth]

/-- **Notebook 1989-2, p. 95**: `Φ dₙ = dₙ Φ`. -/
theorem Φ_face_last {n : ℕ} (xg : G × (Fin (n + 1) → G)) :
    Φ (faceLast xg) = cycLast (Φ xg) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp only [Φ, faceLast, cycLast, cons_zero]
    rw [← succ_last, cons_succ, tot_succ' xg.2]
    group
  · simp [Φ, faceLast, cycLast, init]

end Quillen.Notebook1989_2Simplicial
