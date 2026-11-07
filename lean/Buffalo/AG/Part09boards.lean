import Buffalo.AG.Part09

/-!
# Buffalo, algebraic geometry, part 09: blackboard items

The board items of `vuys5SNs2eQ` (from 4:22:15) and `3ULFIl_2Wis` (5:30:39–6:57:40) that no index
entry of part 09 covers. The status of every checked item is in
`docs/buffalo-ag/lean/Part09-boards.json`.
-/

open CategoryTheory Limits

namespace Buffalo.AG.Part09

/-- vuys5SNs2eQ-17546 board, item 19779 [m] (Nullstellensatz, Zariski's lemma) For `A` of finite
type over a field `k` and `𝔪` a maximal ideal, the residue field `k'' = A/𝔪` is finite over `k`. -/
theorem board_19779 (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (m : Ideal A) [m.IsMaximal] : Module.Finite k (A ⧸ m) := by
  let := Ideal.Quotient.field m
  exact finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)

/-- 3ULFIl_2Wis-19834 board, item 21027 [p] The double arrow `S'' ⇉ S'` is universal: two
`S`-morphisms `u, v : T → S'` factor uniquely through `S'' = S' ×_S S'`. -/
theorem board_21027 {C : Type*} [Category C] {S S' T : C} (g : S' ⟶ S)
    [HasPullback g g] (u v : T ⟶ S') (h : u ≫ g = v ≫ g) :
    ∃! w : T ⟶ pullback g g,
      w ≫ pullback.fst g g = u ∧
        w ≫ pullback.snd g g = v :=
  ⟨pullback.lift u v h, ⟨by simp, by simp⟩, fun w ⟨h₁, h₂⟩ =>
    pullback.hom_ext (by simp [h₁]) (by simp [h₂])⟩

end Buffalo.AG.Part09
