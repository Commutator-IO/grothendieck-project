import Mathlib

/-!
# Quillen, notebook 1970-1, pp. 11, 15–16: the polynomial of a finite additive subgroup is additive

Daniel Quillen's research notebook 1970-1 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201970/1970-1.pdf>) studies the
mod 2 homology of the symmetric groups through the Dickson invariants. The Stiefel–Whitney
classes `w_{2^a − 2^i}` of the regular representation of `(ℤ/2)^a` appear as the coefficients of
`∏_{v ∈ V} (X − v)`, `V` the dual of `(ℤ/2)^a`, and the page uses that this product is a
`2`-polynomial `∑ w_{2^a − 2^i} X^{2^i}`: an additive function of `X`
(the operation `Γ(e(L)) = ∑ w_{2^a − 2^i} e(L)^{2^i}` of p. 16).

This file proves the additivity, for any finite additive subgroup `V` of any field `K`:

* `subgroupPoly V = ∏_{v ∈ V} (X − v)`, monic of degree `|V|` (`subgroupPoly_monic`,
  `natDegree_subgroupPoly`);
* `subgroupPoly_comp_X_add_C`: translating by an element of `V` does not change it;
* `subgroupPoly_add`: **the statement used on the page**: `P_V(x + y) = P_V(x) + P_V(y)` for all
  `x, y ∈ K`.

The proof is the classical one: for fixed `x`, `P_V(Y + x) − P_V(Y) − P_V(x)` has degree
`< |V|` and vanishes on `V`. No hypothesis on the characteristic is needed (in characteristic
`0` the only finite additive subgroup is `0`). The description of the coefficients as
`p`-power monomials is not formalised.
-/

namespace Quillen.Notebook1970_1

open Polynomial

variable {K : Type*} [Field K] (V : AddSubgroup K) [Fintype V]

/-- `P_V = ∏_{v ∈ V} (X − v)`. -/
noncomputable def subgroupPoly : K[X] := ∏ v : V, (X - C (v : K))

theorem subgroupPoly_monic : (subgroupPoly V).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem natDegree_subgroupPoly : (subgroupPoly V).natDegree = Fintype.card V := by
  rw [subgroupPoly, natDegree_prod_of_monic _ _ fun v _ => monic_X_sub_C _]
  simp

theorem eval_subgroupPoly_of_mem {v : K} (hv : v ∈ V) : (subgroupPoly V).eval v = 0 := by
  rw [subgroupPoly, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ ⟨v, hv⟩) (by simp)

/-- Translating by an element of `V` permutes the roots: `P_V(X + v) = P_V(X)`. -/
theorem subgroupPoly_comp_X_add_C {v : K} (hv : v ∈ V) :
    (subgroupPoly V).comp (X + C v) = subgroupPoly V := by
  rw [subgroupPoly, prod_comp]
  simp only [sub_comp, X_comp, C_comp]
  refine Fintype.prod_equiv (Equiv.subRight ⟨v, hv⟩) _ _ fun w => ?_
  simp only [Equiv.subRight_apply, AddSubgroup.coe_sub, map_sub]
  ring

/-- **Quillen, notebook 1970-1, pp. 11, 15–16.** For a finite additive subgroup `V` of a field,
`P_V(x + y) = P_V(x) + P_V(y)`. -/
theorem subgroupPoly_add (x y : K) :
    (subgroupPoly V).eval (x + y) = (subgroupPoly V).eval x + (subgroupPoly V).eval y := by
  have hP := subgroupPoly_monic V
  have hcard : 0 < Fintype.card V := Fintype.card_pos
  have hm : ((subgroupPoly V).comp (X + C x)).Monic := hP.comp_X_add_C x
  have hdeg : ((subgroupPoly V).comp (X + C x) - subgroupPoly V -
      C ((subgroupPoly V).eval x)).degree <
      (Finset.univ.map (Function.Embedding.subtype (· ∈ V))).card := by
    rw [Finset.card_map, Finset.card_univ]
    have h1 : ((subgroupPoly V).comp (X + C x) - subgroupPoly V).degree < Fintype.card V := by
      by_cases h0 : (subgroupPoly V).comp (X + C x) - subgroupPoly V = 0
      · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
      · have hd : ((subgroupPoly V).comp (X + C x)).degree = (subgroupPoly V).degree := by
          rw [degree_eq_natDegree hm.ne_zero, degree_eq_natDegree hP.ne_zero,
            natDegree_comp, natDegree_X_add_C, mul_one]
        have := degree_sub_lt_left hd hm.ne_zero (by rw [hm.leadingCoeff, hP.leadingCoeff])
        rwa [hd, degree_eq_natDegree hP.ne_zero, natDegree_subgroupPoly] at this
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt h1 ?_)
    exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hcard)
  have hR := eq_zero_of_degree_lt_of_eval_finset_eq_zero _ hdeg fun v hv => by
    obtain ⟨⟨w, hw⟩, -, rfl⟩ := Finset.mem_map.mp hv
    have := congrArg (eval x) (subgroupPoly_comp_X_add_C V hw)
    simp only [eval_comp, Polynomial.eval_add, eval_X, eval_C] at this
    simp only [Function.Embedding.coe_subtype, eval_sub, eval_C, eval_comp, Polynomial.eval_add,
      eval_X]
    rw [add_comm w x, this, eval_subgroupPoly_of_mem V hw]
    ring
  have := congrArg (eval y) hR
  simp only [eval_sub, eval_comp, Polynomial.eval_add, eval_X, eval_C, eval_zero] at this
  rw [add_comm x y]
  linear_combination this

end Quillen.Notebook1970_1
