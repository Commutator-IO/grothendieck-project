import Quillen.Notebook1968_15

/-!
# Quillen, notebook 1968-16: the Whitehead lemma

Daniel Quillen's notebook 1968-16 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201968/1968-16.pdf>), § 2 « The
K-theory associated to a ring », uses on p. 2 that the elementary subgroup `E(A)` is normal in
`GL(A)`, so that `K₁ A = GL(A)/E(A)` coincides with Bass's. Both facts rest on the Whitehead lemma
(Milnor, *Introduction to Algebraic K-Theory*, Lemma 3.1): for `θ` invertible, the block matrix
`diag(θ, θ⁻¹)` is a product of elementary matrices. Hence a commutator `[θ, η]` of `GL n A`,
placed in the corner of `GL (n ⊕ n) A`, is elementary.

The ring `A` is any ring with unit. With the notations of `Quillen.Notebook1968_15`:

* `upper`, `lower`: the block unipotent matrices `[[1, B], [0, 1]]` and `[[1, 0], [C, 1]]`, as units;
* `upper_mem_elementary`, `lower_mem_elementary`: they lie in `E(n ⊕ n, A)`, as products of
  elementary matrices, one for each entry;
* `exists_mem_elementary_diag`: for `θ` a unit, `diag(θ, θ⁻¹) ∈ E(n ⊕ n, A)` (the Whitehead lemma),
  from `[[1, θ], [0, 1]] [[1, 0], [-θ⁻¹, 1]] [[1, θ], [0, 1]] = [[0, θ], [-θ⁻¹, 0]]`;
* `exists_mem_elementary_commutator`: for `θ, η` units, `diag(θ η θ⁻¹ η⁻¹, 1) ∈ E(n ⊕ n, A)`.

Not proved: the normality of `E(A)` in `GL(A)` and `E(A) = [GL(A), GL(A)]` at the stable level,
which need the direct limit over `n`.
-/

namespace Quillen.Notebook1968_16

open Matrix Quillen.Notebook1968_15

variable {n : Type*} [DecidableEq n] [Fintype n] {A : Type*} [Ring A]

/-- The unipotent block matrix `[[1, B], [0, 1]]`, a unit with inverse `[[1, -B], [0, 1]]`. -/
def upper (B : Matrix n n A) : (Matrix (n ⊕ n) (n ⊕ n) A)ˣ where
  val := fromBlocks 1 B 0 1
  inv := fromBlocks 1 (-B) 0 1
  val_inv := by simp [fromBlocks_multiply, ← fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, ← fromBlocks_one]

/-- The unipotent block matrix `[[1, 0], [C, 1]]`, a unit with inverse `[[1, 0], [-C, 1]]`. -/
def lower (C : Matrix n n A) : (Matrix (n ⊕ n) (n ⊕ n) A)ˣ where
  val := fromBlocks 1 0 C 1
  inv := fromBlocks 1 0 (-C) 1
  val_inv := by simp [fromBlocks_multiply, ← fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, ← fromBlocks_one]

@[simp] theorem upper_val (B : Matrix n n A) :
    ((upper B : (Matrix (n ⊕ n) (n ⊕ n) A)ˣ) : Matrix (n ⊕ n) (n ⊕ n) A) = fromBlocks 1 B 0 1 :=
  rfl

@[simp] theorem lower_val (C : Matrix n n A) :
    ((lower C : (Matrix (n ⊕ n) (n ⊕ n) A)ˣ) : Matrix (n ⊕ n) (n ⊕ n) A) = fromBlocks 1 0 C 1 :=
  rfl

theorem upper_add (B C : Matrix n n A) : upper (B + C) = upper B * upper C := by
  ext : 1; simp [fromBlocks_multiply, add_comm]

theorem lower_add (B C : Matrix n n A) : lower (B + C) = lower B * lower C := by
  ext : 1; simp [fromBlocks_multiply, add_comm]

theorem upper_single (i j : n) (a : A) :
    upper (single i j a) =
      transvectionUnit (Sum.inl_ne_inr : (Sum.inl i : n ⊕ n) ≠ Sum.inr j) a := by
  ext : 1
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [fromBlocks, single_apply, one_apply, eq_comm]

theorem lower_single (i j : n) (a : A) :
    lower (single i j a) =
      transvectionUnit (Sum.inr_ne_inl : (Sum.inr i : n ⊕ n) ≠ Sum.inl j) a := by
  ext : 1
  ext p q
  rcases p with p | p <;> rcases q with q | q <;>
    simp [fromBlocks, single_apply, one_apply, eq_comm]

theorem upper_zero : upper (0 : Matrix n n A) = 1 := by
  ext : 1; simp [← fromBlocks_one]

theorem lower_zero : lower (0 : Matrix n n A) = 1 := by
  ext : 1; simp [← fromBlocks_one]

theorem upper_sum_mem {ι : Type*} (s : Finset ι) (f : ι → Matrix n n A)
    (hf : ∀ i, upper (f i) ∈ elementary (n ⊕ n) A) :
    upper (∑ i ∈ s, f i) ∈ elementary (n ⊕ n) A := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, upper_zero]; exact one_mem _
  | insert i s hi ih => rw [Finset.sum_insert hi, upper_add]; exact mul_mem (hf i) ih

theorem lower_sum_mem {ι : Type*} (s : Finset ι) (f : ι → Matrix n n A)
    (hf : ∀ i, lower (f i) ∈ elementary (n ⊕ n) A) :
    lower (∑ i ∈ s, f i) ∈ elementary (n ⊕ n) A := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, lower_zero]; exact one_mem _
  | insert i s hi ih => rw [Finset.sum_insert hi, lower_add]; exact mul_mem (hf i) ih

/-- `[[1, B], [0, 1]]` is elementary: it is the product of the `1 + B_ij e_{i, n+j}`. -/
theorem upper_mem_elementary (B : Matrix n n A) : upper B ∈ elementary (n ⊕ n) A := by
  rw [matrix_eq_sum_single B]
  exact upper_sum_mem _ _ fun i => upper_sum_mem _ _ fun j => by
    rw [upper_single]; exact Subgroup.subset_closure ⟨_, _, _, _, rfl⟩

/-- `[[1, 0], [C, 1]]` is elementary. -/
theorem lower_mem_elementary (C : Matrix n n A) : lower C ∈ elementary (n ⊕ n) A := by
  rw [matrix_eq_sum_single C]
  exact lower_sum_mem _ _ fun i => lower_sum_mem _ _ fun j => by
    rw [lower_single]; exact Subgroup.subset_closure ⟨_, _, _, _, rfl⟩

/-- `[[1, θ], [0, 1]] [[1, 0], [-θ⁻¹, 1]] [[1, θ], [0, 1]] = [[0, θ], [-θ⁻¹, 0]]` for a unit
`θ`. -/
theorem upper_lower_upper (θ : (Matrix n n A)ˣ) :
    ((upper (θ : Matrix n n A) * lower (-(θ⁻¹ : (Matrix n n A)ˣ) : Matrix n n A) *
      upper (θ : Matrix n n A) : (Matrix (n ⊕ n) (n ⊕ n) A)ˣ) : Matrix _ _ A) =
      fromBlocks 0 (θ : Matrix n n A) (-(θ⁻¹ : (Matrix n n A)ˣ) : Matrix n n A) 0 := by
  simp [fromBlocks_multiply]

/-- **The Whitehead lemma.** For a unit `θ` of `Matrix n n A`, `diag(θ, θ⁻¹)` is elementary in
`GL (n ⊕ n) A`: it is `[[0, θ], [-θ⁻¹, 0]] [[0, -1], [1, 0]]`, two products of block unipotent
matrices. -/
theorem exists_mem_elementary_diag (θ : (Matrix n n A)ˣ) :
    ∃ g ∈ elementary (n ⊕ n) A, (g : Matrix (n ⊕ n) (n ⊕ n) A) =
      fromBlocks (θ : Matrix n n A) 0 0 ((θ⁻¹ : (Matrix n n A)ˣ) : Matrix n n A) := by
  let w : (Matrix n n A)ˣ → (Matrix (n ⊕ n) (n ⊕ n) A)ˣ := fun u =>
    upper (u : Matrix n n A) * lower (-(u⁻¹ : (Matrix n n A)ˣ) : Matrix n n A) *
      upper (u : Matrix n n A)
  have hw : ∀ u, w u ∈ elementary (n ⊕ n) A := fun u =>
    mul_mem (mul_mem (upper_mem_elementary _) (lower_mem_elementary _)) (upper_mem_elementary _)
  refine ⟨w θ * w (-1), mul_mem (hw θ) (hw (-1)), ?_⟩
  rw [Units.val_mul, upper_lower_upper, upper_lower_upper]
  simp [fromBlocks_multiply]

/-- Commutators are elementary in the corner: for units `θ, η` of `Matrix n n A`,
`diag(θ η θ⁻¹ η⁻¹, 1)` lies in `E(n ⊕ n, A)`, as `diag(θ, θ⁻¹) diag(η, η⁻¹) diag((ηθ)⁻¹, ηθ)`. -/
theorem exists_mem_elementary_commutator (θ η : (Matrix n n A)ˣ) :
    ∃ g ∈ elementary (n ⊕ n) A, (g : Matrix (n ⊕ n) (n ⊕ n) A) =
      fromBlocks ((θ * η * θ⁻¹ * η⁻¹ : (Matrix n n A)ˣ) : Matrix n n A) 0 0 1 := by
  obtain ⟨g₁, hg₁, e₁⟩ := exists_mem_elementary_diag θ
  obtain ⟨g₂, hg₂, e₂⟩ := exists_mem_elementary_diag η
  obtain ⟨g₃, hg₃, e₃⟩ := exists_mem_elementary_diag (η * θ)⁻¹
  refine ⟨g₁ * g₂ * g₃, mul_mem (mul_mem hg₁ hg₂) hg₃, ?_⟩
  rw [Units.val_mul, Units.val_mul, e₁, e₂, e₃]
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, inv_inv]
  congr 1
  · simp [_root_.mul_inv_rev, mul_assoc]
  · rw [← Units.val_mul, ← Units.val_mul]
    simp [mul_assoc]

end Quillen.Notebook1968_16
