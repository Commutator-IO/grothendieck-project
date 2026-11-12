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
  rw [Subgroup.mem_normalizer_iff] at hg
  rw [mem_stabilizer_iff']
  by_contra hga
  set a' := g⁻¹ a with ha'
  have haa' : a ≠ a' := by
    intro h
    apply hga
    calc g a = g a' := by rw [← h]
      _ = a := by simp [ha']
  obtain ⟨c, hc⟩ : ∃ c, c ∉ ({a, a'} : Finset α) := by
    by_contra! h
    have : Finset.univ ⊆ ({a, a'} : Finset α) := fun x _ => h x
    have := Finset.card_le_card this
    rw [Finset.card_univ] at this
    have := Finset.card_le_two (a := a) (b := a')
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  have hh : swap a' c ∈ stabilizer (Perm α) a := by
    rw [mem_stabilizer_iff', swap_apply_of_ne_of_ne haa' (Ne.symm hc.1)]
  have := (hg _).mp hh
  rw [mem_stabilizer_iff'] at this
  simp only [Perm.coe_mul, Function.comp_apply] at this
  rw [← ha', swap_apply_left] at this
  apply hc.2
  rw [ha', ← this]; simp

/-- For two letters the bound fails: the stabilizer of a point of `Fin 2` is trivial, so its
normalizer is everything, and contains the transposition, which moves the point. -/
theorem normalizer_stabilizer_two :
    swap (0 : Fin 2) 1 ∈
        Subgroup.normalizer (stabilizer (Perm (Fin 2)) (0 : Fin 2) : Set (Perm (Fin 2))) ∧
      swap (0 : Fin 2) 1 ∉ stabilizer (Perm (Fin 2)) (0 : Fin 2) := by
  constructor
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [mem_stabilizer_iff']
    fin_cases h <;> decide
  · rw [mem_stabilizer_iff']; decide

end Quillen.Notebook1971_2Normalizer
