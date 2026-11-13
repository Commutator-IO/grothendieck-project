import Mathlib

/-!
# Quillen, notebook 1971-12, p. 19: a ring is not a finite union of cosets of ideals with infinite quotients

Daniel Quillen's research notebook 1971-12 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201971/1971-12.pdf>) proves, on
pp. 17–20, that a closed subset of small dimension can be avoided by a section, choosing the
coordinates one at a time. On p. 19 (the special case where all residue fields of the
commutative ring `A` are infinite) the choice of the next coordinate reduces to the claim that
`A` is not a finite union `⋃ (a_i + q_i)` of cosets of prime ideals. He proves the claim by
reducing to maximal ideals and the Chinese remainder theorem.

This file proves the claim, from B. H. Neumann's lemma on coset coverings (in mathlib:
`AddSubgroup.exists_finiteIndex_of_leftCoset_cover`), in a slightly more general form:

* `not_cover_of_infinite`: in any ring, if every quotient `A ⧸ I_i` is infinite, some `x` lies
  in none of the cosets `a_i + I_i` (a finite family);
* `not_cover`: **the claim of the page**: in a commutative ring all of whose residue fields
  `A ⧸ m` (`m` maximal) are infinite, a finite family of cosets `a_i + q_i` of proper ideals
  (prime ones, on the page) does not cover `A`.

The page's own route (reduce to maximal `q_i`, then the Chinese remainder theorem) is not
followed; the reduction to Neumann's lemma uses the hypothesis on residue fields only to see
that each `A ⧸ q_i` is infinite.
-/

namespace Quillen.Notebook1971_12Cover

open scoped Pointwise

/-- In any ring, a finite family of cosets `a_i + I_i` of left ideals with infinite quotients
does not cover the ring. -/
theorem not_cover_of_infinite {A ι : Type*} [Ring A] (s : Finset ι) (a : ι → A)
    (I : ι → Ideal A) (hI : ∀ i ∈ s, Infinite (A ⧸ I i)) :
    ∃ x : A, ∀ i ∈ s, x - a i ∉ I i := by
  by_contra! h
  have hcov : ⋃ i ∈ s, a i +ᵥ ((I i).toAddSubgroup : Set A) = Set.univ :=
    Set.eq_univ_of_forall fun x => by
      obtain ⟨i, hi, hx⟩ := h x
      exact Set.mem_iUnion₂.mpr ⟨i, hi, by simpa [mem_leftAddCoset_iff, neg_add_eq_sub] using hx⟩
  obtain ⟨i, hi, hfin⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcov
  exact @not_finite _ (hI i hi) AddSubgroup.finite_quotient_of_finiteIndex

/-- **Quillen, notebook 1971-12, p. 19.** Let `A` be a commutative ring whose residue fields
`A ⧸ m` at maximal ideals are all infinite. Then `A` is not a finite union of cosets
`a_i + q_i` of proper ideals `q_i`: some `x` lies in none of them. -/
theorem not_cover {A ι : Type*} [CommRing A]
    (hA : ∀ m : Ideal A, m.IsMaximal → Infinite (A ⧸ m))
    (s : Finset ι) (a : ι → A) (q : ι → Ideal A) (hq : ∀ i ∈ s, q i ≠ ⊤) :
    ∃ x : A, ∀ i ∈ s, x - a i ∉ q i := by
  refine not_cover_of_infinite s a q fun i hi => ?_
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal (q i) (hq i hi)
  exact @Infinite.of_surjective _ _ (hA m hm) _ (Ideal.Quotient.factor_surjective hqm)

end Quillen.Notebook1971_12Cover
