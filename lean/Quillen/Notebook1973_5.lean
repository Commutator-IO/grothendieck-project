import Mathlib

/-!
# Quillen, notebook 1973-5, pp. 28–29: a partial order is the intersection of its linear extensions

Daniel Quillen's research notebook 1973-5 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201973/1973-5.pdf>), in notes of
October 9, 1973 on the Wagoner and Volodin constructions of algebraic `K`-theory, compares the
subgroups of `GL_n(A)` obtained as finite intersections of conjugates `π U π⁻¹` of the upper
unitriangular group by permutation matrices. On p. 28 he proves, in our words: if `≤` is a
partial order on a set `X` and `y ≰ x`, then adding all pairs `(u, v)` with `u ≤ x` and `y ≤ v`
gives again a partial order; hence (Zorn) every partial order is refined by a linear order, and
every partial order is the intersection of the linear orders refining it. On p. 29 he applies it
to matrices: for a partial order `R` on `{1, …, n}`, the matrices whose entry `(i, j)` vanishes
unless `i R j` form a subring `M_R`, `M_{⋂ R_ν} = ⋂ M_{R_ν}`, so every `M_R` is an intersection
of conjugates of the triangular subring.

* `adjoin`, `isPartialOrder_adjoin`: the enlarged relation of p. 28 and the case analysis showing
  that it is a partial order;
* `exists_linear_not_rel`: if `¬ r y x`, some linear order containing `r` has `¬ s y x`
  (the extension itself is mathlib's `extend_partialOrder`);
* `rel_iff_forall_linear`: `r a b` holds iff `s a b` holds for every linear order `s ⊇ r`;
* `matSupp`, `matSubring`: the matrices supported on a relation, a subring when the relation is
  reflexive and transitive;
* `matSupp_eq_iInter`: for a partial order `R`, `M_R = ⋂ M_s` over the linear orders `s ⊇ R`.
  For a linear order `s` on `Fin n`, `M_s` is the conjugate of the upper triangular matrices by
  the permutation sorting `s`; this identification is not formalised here.
-/

namespace Quillen.Notebook1973_5

variable {α : Type*}

/-- The relation of p. 28: `r` together with all pairs `(u, v)` with `r u x` and `r y v`. -/
def adjoin (r : α → α → Prop) (x y : α) : α → α → Prop := fun u v => r u v ∨ (r u x ∧ r y v)

theorem le_adjoin (r : α → α → Prop) (x y : α) : r ≤ adjoin r x y := fun _ _ h => Or.inl h

theorem adjoin_self (r : α → α → Prop) [Std.Refl r] (x y : α) : adjoin r x y x y :=
  Or.inr ⟨refl x, refl y⟩

/-- **Quillen, notebook 1973-5, p. 28.** If `r` is a partial order and `¬ r y x`, the relation
`adjoin r x y` is again a partial order (transitivity in four cases, antisymmetry in four cases;
every mixed case would force `r y x`). -/
theorem isPartialOrder_adjoin (r : α → α → Prop) [IsPartialOrder α r] {x y : α} (h : ¬ r y x) :
    IsPartialOrder α (adjoin r x y) where
  refl a := Or.inl (refl a)
  trans a b c := by
    rintro (hab | ⟨hax, hyb⟩) (hbc | ⟨hbx, hyc⟩)
    · exact Or.inl (_root_.trans hab hbc)
    · exact Or.inr ⟨_root_.trans hab hbx, hyc⟩
    · exact Or.inr ⟨hax, _root_.trans hyb hbc⟩
    · exact (h (_root_.trans hyb hbx)).elim
  antisymm a b := by
    rintro (hab | ⟨hax, hyb⟩) (hba | ⟨hbx, hya⟩)
    · exact antisymm hab hba
    · exact (h (_root_.trans hya (_root_.trans hab hbx))).elim
    · exact (h (_root_.trans hyb (_root_.trans hba hax))).elim
    · exact (h (_root_.trans hyb hbx)).elim

/-- **Quillen, notebook 1973-5, p. 28.** If `¬ r y x`, there is a linear order `s` containing `r`
with `¬ s y x`. -/
theorem exists_linear_not_rel (r : α → α → Prop) [IsPartialOrder α r] {x y : α} (h : ¬ r y x) :
    ∃ s : α → α → Prop, IsLinearOrder α s ∧ r ≤ s ∧ ¬ s y x := by
  have := isPartialOrder_adjoin r h
  obtain ⟨s, hs, hle⟩ := extend_partialOrder (adjoin r x y)
  refine ⟨s, hs, (le_adjoin r x y).trans hle, fun hyx => ?_⟩
  exact h (antisymm (hle x y (adjoin_self r x y)) hyx ▸ refl x)

/-- **Quillen, notebook 1973-5, p. 28.** Every partial order is the intersection of the linear
orders refining it. -/
theorem rel_iff_forall_linear (r : α → α → Prop) [IsPartialOrder α r] (a b : α) :
    r a b ↔ ∀ s : α → α → Prop, IsLinearOrder α s → r ≤ s → s a b := by
  refine ⟨fun hab s _ hrs => hrs a b hab, fun H => ?_⟩
  by_contra hab
  obtain ⟨s, hs, hrs, hba⟩ := exists_linear_not_rel r hab
  exact hba (H s hs hrs)

/-! ### Matrices supported on a relation (p. 29) -/

variable {n : Type*} {A : Type*} [Ring A]

/-- The matrices whose entry `(i, j)` vanishes unless `R i j`: the set `M_R` of p. 29. -/
def matSupp (R : n → n → Prop) : Set (Matrix n n A) := {M | ∀ i j, M i j ≠ 0 → R i j}

/-- **Quillen, notebook 1973-5, p. 29.** For a reflexive and transitive relation `R`, the
matrices supported on `R` form a subring. -/
def matSubring [Fintype n] [DecidableEq n] (R : n → n → Prop) [Std.Refl R] [IsTrans n R] :
    Subring (Matrix n n A) where
  carrier := matSupp R
  mul_mem' {M N} hM hN i j hij := by
    by_contra hR
    apply hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : R i k
    · have hkj : ¬ R k j := fun hkj => hR (_root_.trans hik hkj)
      rw [not_not.1 (mt (hN k j) hkj), mul_zero]
    · rw [not_not.1 (mt (hM i k) hik), zero_mul]
  one_mem' i j hij := by
    by_cases h : i = j
    · exact h ▸ refl i
    · exact (hij (Matrix.one_apply_ne h)).elim
  add_mem' {M N} hM hN i j hij := by
    by_contra hR
    exact hij (by rw [Matrix.add_apply, not_not.1 (mt (hM i j) hR), not_not.1 (mt (hN i j) hR),
      add_zero])
  zero_mem' i j hij := (hij rfl).elim
  neg_mem' {M} hM i j hij := hM i j (fun h => hij (by rw [Matrix.neg_apply, h, neg_zero]))

/-- `M_{⋂ R_ν} = ⋂ M_{R_ν}` (p. 29), for any family of relations. -/
theorem matSupp_iInf {κ : Sort*} (R : κ → n → n → Prop) :
    matSupp (A := A) (fun i j => ∀ ν, R ν i j) = ⋂ ν, matSupp (R ν) := by
  ext M
  simp only [matSupp, Set.mem_ofPred_eq, Set.mem_iInter]
  exact ⟨fun h ν i j hij => h i j hij ν, fun h i j hij ν => h ν i j hij⟩

/-- **Quillen, notebook 1973-5, p. 29.** For a partial order `R`, the matrices supported on `R`
are the matrices supported on every linear order refining `R`. -/
theorem matSupp_eq_iInter (R : n → n → Prop) [IsPartialOrder n R] :
    matSupp (A := A) R =
      ⋂ s : {s : n → n → Prop // IsLinearOrder n s ∧ R ≤ s}, matSupp s.1 := by
  rw [← matSupp_iInf]
  congr 1
  funext i j
  rw [rel_iff_forall_linear R i j]
  exact propext ⟨fun h s => h s.1 s.2.1 s.2.2, fun h s hs hRs => h ⟨s, hs, hRs⟩⟩

end Quillen.Notebook1973_5
