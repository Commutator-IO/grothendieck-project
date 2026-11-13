import Mathlib

/-!
# Quillen, notebooks 1971-2 (p. 14) and 1975-10 (p. 7): `Σ_{n−1}` is its own normalizer in `Σ_n`

Daniel Quillen's research notebook 1971-2 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201971/1971-2.pdf>) proves, on
p. 14, that the transfer from `Σ_{mℓ+1}` to `Σ_{mℓ}` is an isomorphism on homology with
coefficients in the sign representation mod `ℓ`. The double-coset argument needs that no `x`
outside `H = Σ_{n−1}` normalizes `H`, « as `Σ_{n−1}` is its own normalizer in `Σ_n` ». The same
fact opens p. 7 of notebook 1975-10
(<https://www.claymath.org/library/Quillen/Working_papers/quillen%201975/1975-10.pdf>), for the
universal `Σ_n`-space with orbit types `Σ_n` and `Σ_n / Σ_{n−1}`.

This file proves it for the permutations of any finite type `α` with at least three elements,
`Σ_{n−1}` being the stabilizer of a point:

* `stabilizer_conj`: `g Stab(a) g⁻¹ = Stab(g a)`, in the form used below;
* `normalizer_stabilizer`: **the statement of both pages**: the normalizer of the stabilizer of
  `a` is the stabilizer of `a`, when `3 ≤ |α|`;
* `normalizer_stabilizer_two`: for `|α| = 2` the stabilizer is trivial and its normalizer is the
  whole group, so the bound, implicit on the pages, is needed.
-/

namespace Quillen.Notebook1971_2Normalizer

open Equiv MulAction

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem mem_stabilizer_iff' {a : α} {h : Perm α} : h ∈ stabilizer (Perm α) a ↔ h a = a :=
  mem_stabilizer_iff

/-- **Quillen, notebook 1971-2, p. 14; notebook 1975-10, p. 7.** For `|α| ≥ 3`, the stabilizer
of a point `a` in the symmetric group of `α` is its own normalizer. -/
theorem normalizer_stabilizer [Fintype α] (h3 : 3 ≤ Fintype.card α) (a : α) :
    Subgroup.normalizer (stabilizer (Perm α) a : Set (Perm α)) = stabilizer (Perm α) a := by
  refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
  rw [mem_stabilizer_iff']
  by_contra hga
  have haa' : a ≠ g⁻¹ a := fun h => hga (Perm.eq_inv_iff_eq.1 h)
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {a, g⁻¹ a}) (t := .univ)
    (by have := Finset.card_le_two (a := a) (b := g⁻¹ a); rw [Finset.card_univ]; omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  have := (Subgroup.mem_normalizer_iff.1 hg _).1
    (mem_stabilizer_iff'.2 (swap_apply_of_ne_of_ne haa' (Ne.symm hc.1)))
  simp only [mem_stabilizer_iff', Perm.coe_mul, Function.comp_apply, swap_apply_left] at this
  exact hc.2 (Perm.eq_inv_iff_eq.2 this)

/-- For two letters the bound fails: the stabilizer of a point of `Fin 2` is trivial, so its
normalizer is everything, and contains the transposition, which moves the point. -/
theorem normalizer_stabilizer_two :
    swap (0 : Fin 2) 1 ∈
        Subgroup.normalizer (stabilizer (Perm (Fin 2)) (0 : Fin 2) : Set (Perm (Fin 2))) ∧
      swap (0 : Fin 2) 1 ∉ stabilizer (Perm (Fin 2)) (0 : Fin 2) := by
  refine ⟨Subgroup.mem_normalizer_iff.2 fun h => ?_, by rw [mem_stabilizer_iff']; decide⟩
  simp only [mem_stabilizer_iff']
  fin_cases h <;> decide

end Quillen.Notebook1971_2Normalizer
