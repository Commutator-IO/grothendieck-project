import Mathlib

/-!
# Quillen, notebook 1991-4, p. 20: `J ∩ K = J K + K J` for comaximal two-sided ideals

Daniel Quillen's research notebook 1991-4 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201991/1991-4.pdf>) computes,
on p. 20 (his p. 424), the kernel `I` of a surjection from a tensor algebra onto a product of two
algebras, as an intersection of two two-sided ideals whose sum is the whole ring. He recalls
there that for two-sided ideals `J`, `K` of a ring `R` with `J + K = R` one has
`J ∩ K = J K + K J`; the ring is not commutative, so the two products differ.

This file proves the recalled statement, in any ring (semiring, in fact), by writing
`x = x j + x k` for `x` in `J ∩ K` and `1 = j + k`.

* `inf_eq_mul_sup_mul`: **the statement of the page**;
* `inf_eq_mul_of_comm`: in a commutative ring it is the usual `J ∩ K = J K`.
-/

namespace Quillen.Notebook1991_4

variable {R : Type*} [Semiring R]

/-- **Quillen, notebook 1991-4, p. 20.** For two-sided ideals `J`, `K` of a ring with
`J + K = R`, the intersection `J ∩ K` is `J K + K J`. -/
theorem inf_eq_mul_sup_mul (J K : Ideal R) [J.IsTwoSided] [K.IsTwoSided] (h : J ⊔ K = ⊤) :
    J ⊓ K = J * K ⊔ K * J := by
  refine le_antisymm (fun x hx => ?_) (sup_le (le_inf Ideal.mul_le_left Ideal.mul_le_right)
    (le_inf Ideal.mul_le_right Ideal.mul_le_left))
  obtain ⟨j, hj, k, hk, hjk⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp h)
  exact Submodule.mem_sup.2 ⟨_, Ideal.mul_mem_mul hx.1 hk, _, Ideal.mul_mem_mul hx.2 hj,
    by rw [← mul_add, add_comm, hjk, mul_one]⟩

/-- In a commutative ring the two products agree, and the statement is the usual
`J ∩ K = J K` for comaximal ideals. -/
theorem inf_eq_mul_of_comm {R : Type*} [CommSemiring R] (J K : Ideal R) (h : J ⊔ K = ⊤) :
    J ⊓ K = J * K := by
  rw [inf_eq_mul_sup_mul J K h, mul_comm K J, sup_idem]

end Quillen.Notebook1991_4
