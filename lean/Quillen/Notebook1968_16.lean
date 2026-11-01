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

* `upper`, `lower`: the block unipotent matrices `[[1, B], [0, 1]]` and `[[1, 0], [C, 1]]`, as
  units;
* `upper_mem_elementary`, `lower_mem_elementary`: they lie in `E(n ⊕ n, A)`, as products of
  elementary matrices, one for each entry;
* `exists_mem_elementary_diag`: for `θ` a unit, `diag(θ, θ⁻¹) ∈ E(n ⊕ n, A)` (the Whitehead lemma),
  from `[[1, θ], [0, 1]] [[1, 0], [-θ⁻¹, 1]] [[1, θ], [0, 1]] = [[0, θ], [-θ⁻¹, 0]]`;
* `exists_mem_elementary_commutator`: for `θ, η` units, `diag(θ η θ⁻¹ η⁻¹, 1) ∈ E(n ⊕ n, A)`.

Not proved: the normality of `E(A)` in `GL(A)` and `E(A) = [GL(A), GL(A)]` at the stable level,
which need the direct limit over `n`.

The proofs are general and live in `Quillen.Upstream.MatrixElementarySubgroup`
(`Matrix.blockUpperUnit`, `Matrix.blockLowerUnit`,
`Matrix.exists_mem_elementarySubgroup_fromBlocks_inv`, …); the declarations below keep the names
of this page.
-/

namespace Quillen.Notebook1968_16

open Matrix hiding transvectionUnit
open Quillen.Notebook1968_15

variable {n : Type*} [DecidableEq n] [Fintype n] {A : Type*} [Ring A]

/-- The unipotent block matrix `[[1, B], [0, 1]]`, a unit with inverse `[[1, -B], [0, 1]]`. -/
abbrev upper (B : Matrix n n A) : (Matrix (n ⊕ n) (n ⊕ n) A)ˣ := blockUpperUnit B

/-- The unipotent block matrix `[[1, 0], [C, 1]]`, a unit with inverse `[[1, 0], [-C, 1]]`. -/
abbrev lower (C : Matrix n n A) : (Matrix (n ⊕ n) (n ⊕ n) A)ˣ := blockLowerUnit C

@[simp] theorem upper_val (B : Matrix n n A) :
    ((upper B : (Matrix (n ⊕ n) (n ⊕ n) A)ˣ) : Matrix (n ⊕ n) (n ⊕ n) A) = fromBlocks 1 B 0 1 :=
  rfl

@[simp] theorem lower_val (C : Matrix n n A) :
    ((lower C : (Matrix (n ⊕ n) (n ⊕ n) A)ˣ) : Matrix (n ⊕ n) (n ⊕ n) A) = fromBlocks 1 0 C 1 :=
  rfl

theorem upper_add (B C : Matrix n n A) : upper (B + C) = upper B * upper C :=
  blockUpperUnit_add B C

theorem lower_add (B C : Matrix n n A) : lower (B + C) = lower B * lower C :=
  blockLowerUnit_add B C

theorem upper_single (i j : n) (a : A) :
    upper (single i j a) =
      transvectionUnit (Sum.inl_ne_inr : (Sum.inl i : n ⊕ n) ≠ Sum.inr j) a :=
  blockUpperUnit_single i j a

theorem lower_single (i j : n) (a : A) :
    lower (single i j a) =
      transvectionUnit (Sum.inr_ne_inl : (Sum.inr i : n ⊕ n) ≠ Sum.inl j) a :=
  blockLowerUnit_single i j a

theorem upper_zero : upper (0 : Matrix n n A) = 1 := blockUpperUnit_zero

theorem lower_zero : lower (0 : Matrix n n A) = 1 := blockLowerUnit_zero

theorem upper_sum_mem {ι : Type*} (s : Finset ι) (f : ι → Matrix n n A)
    (hf : ∀ i, upper (f i) ∈ elementary (n ⊕ n) A) :
    upper (∑ i ∈ s, f i) ∈ elementary (n ⊕ n) A :=
  blockUpperUnit_sum_mem_elementarySubgroup s f hf

theorem lower_sum_mem {ι : Type*} (s : Finset ι) (f : ι → Matrix n n A)
    (hf : ∀ i, lower (f i) ∈ elementary (n ⊕ n) A) :
    lower (∑ i ∈ s, f i) ∈ elementary (n ⊕ n) A :=
  blockLowerUnit_sum_mem_elementarySubgroup s f hf

/-- `[[1, B], [0, 1]]` is elementary: it is the product of the `1 + B_ij e_{i, n+j}`. -/
theorem upper_mem_elementary (B : Matrix n n A) : upper B ∈ elementary (n ⊕ n) A :=
  blockUpperUnit_mem_elementarySubgroup B

/-- `[[1, 0], [C, 1]]` is elementary. -/
theorem lower_mem_elementary (C : Matrix n n A) : lower C ∈ elementary (n ⊕ n) A :=
  blockLowerUnit_mem_elementarySubgroup C

/-- `[[1, θ], [0, 1]] [[1, 0], [-θ⁻¹, 1]] [[1, θ], [0, 1]] = [[0, θ], [-θ⁻¹, 0]]` for a unit
`θ`. -/
theorem upper_lower_upper (θ : (Matrix n n A)ˣ) :
    ((upper (θ : Matrix n n A) * lower (-(θ⁻¹ : (Matrix n n A)ˣ) : Matrix n n A) *
      upper (θ : Matrix n n A) : (Matrix (n ⊕ n) (n ⊕ n) A)ˣ) : Matrix _ _ A) =
      fromBlocks 0 (θ : Matrix n n A) (-(θ⁻¹ : (Matrix n n A)ˣ) : Matrix n n A) 0 :=
  blockUpperUnit_mul_blockLowerUnit_mul_blockUpperUnit θ

/-- **The Whitehead lemma.** For a unit `θ` of `Matrix n n A`, `diag(θ, θ⁻¹)` is elementary in
`GL (n ⊕ n) A`: it is `[[0, θ], [-θ⁻¹, 0]] [[0, -1], [1, 0]]`, two products of block unipotent
matrices. -/
theorem exists_mem_elementary_diag (θ : (Matrix n n A)ˣ) :
    ∃ g ∈ elementary (n ⊕ n) A, (g : Matrix (n ⊕ n) (n ⊕ n) A) =
      fromBlocks (θ : Matrix n n A) 0 0 ((θ⁻¹ : (Matrix n n A)ˣ) : Matrix n n A) :=
  exists_mem_elementarySubgroup_fromBlocks_inv θ

/-- Commutators are elementary in the corner: for units `θ, η` of `Matrix n n A`,
`diag(θ η θ⁻¹ η⁻¹, 1)` lies in `E(n ⊕ n, A)`, as `diag(θ, θ⁻¹) diag(η, η⁻¹) diag((ηθ)⁻¹, ηθ)`. -/
theorem exists_mem_elementary_commutator (θ η : (Matrix n n A)ˣ) :
    ∃ g ∈ elementary (n ⊕ n) A, (g : Matrix (n ⊕ n) (n ⊕ n) A) =
      fromBlocks ((θ * η * θ⁻¹ * η⁻¹ : (Matrix n n A)ˣ) : Matrix n n A) 0 0 1 :=
  exists_mem_elementarySubgroup_fromBlocks_commutator θ η

end Quillen.Notebook1968_16
