import Mathlib

/-!
# Quillen, notebook 1972-8: the `2 × m` chessboard complex

Daniel Quillen's research notebook 1972-8 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201972/1972-8.pdf>).

* p. 47: the graph on `{1, 2} × C`, `|C| = m`, joining `(i, c)` and `(j, c')` iff `i ≠ j` and
  `c ≠ c'` (`chess`), is `(m − 1)`-regular with `m(m − 1)` edges (`degree_chess`,
  `card_edgeFinset_chess`), disconnected for `m = 2` (`not_connected_chess_two`) and connected
  for `m ≥ 3` (`connected_chess`); so for `m = 3` it is one hexagon, a single circle.
-/

namespace Quillen.Notebook1972_8Chess

open Finset

/-- The `2 × m` chessboard complex of p. 47 (a graph): vertices `(i, c)`, `i ∈ {1, 2}`, `c ∈ C`;
`(i, c)` and `(j, c')` span an edge iff `i ≠ j` and `c ≠ c'`. -/
def chess (m : ℕ) : SimpleGraph (Fin 2 × Fin m) where
  Adj x y := x.1 ≠ y.1 ∧ x.2 ≠ y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (m : ℕ) : DecidableRel (chess m).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem degree_chess (m : ℕ) (x : Fin 2 × Fin m) : (chess m).degree x = m - 1 := by
  classical
  have : (chess m).neighborFinset x = ({x.1}ᶜ : Finset (Fin 2)) ×ˢ ({x.2}ᶜ : Finset (Fin m)) := by
    ext y; rw [SimpleGraph.mem_neighborFinset]; simp [chess, ne_comm]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, this, Finset.card_product]
  simp [Finset.card_compl]

/-- The graph has `m(m − 1)` edges. -/
theorem card_edgeFinset_chess (m : ℕ) : #(chess m).edgeFinset = m * (m - 1) := by
  have := (chess m).sum_degrees_eq_twice_card_edges
  simp only [degree_chess, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    smul_eq_mul] at this
  rw [← Nat.mul_left_cancel_iff two_pos]; linarith

/-- For `|C| = 2` it is disconnected. -/
theorem not_connected_chess_two : ¬(chess 2).Connected := by
  intro h
  have key : ∀ {x y}, (chess 2).Reachable x y → (x.1 : ℕ) + x.2 ≡ y.1 + y.2 [MOD 2] := by
    rintro x y ⟨p⟩
    induction p with
    | nil => rfl
    | cons ha _ ih =>
      refine Nat.ModEq.trans ?_ ih
      obtain ⟨h1, h2⟩ := ha
      revert h1 h2; rename_i a b _ _; rcases a with ⟨i, c⟩; rcases b with ⟨j, d⟩
      fin_cases i <;> fin_cases j <;> fin_cases c <;> fin_cases d <;> decide
  exact absurd (key (h.preconnected (0, 0) (0, 1))) (by decide)

/-- For `|C| ≥ 3` it is connected. -/
theorem connected_chess {m : ℕ} (hm : 3 ≤ m) : (chess m).Connected := by
  have h0 : ∀ c c' : Fin m, (chess m).Reachable (0, c) (0, c') := fun c c' => by
    obtain ⟨d, hd, hd'⟩ : ∃ d : Fin m, d ≠ c ∧ d ≠ c' := by
      by_contra! h
      have : (Finset.univ : Finset (Fin m)) ⊆ {c, c'} := fun d _ => by
        by_cases hdc : d = c
        · simp [hdc]
        · simp [h d hdc]
      have := Finset.card_le_card this
      simp at this; have := Finset.card_le_two (a := c) (b := c'); omega
    exact (SimpleGraph.Adj.reachable (show (chess m).Adj (0, c) (1, d) from ⟨zero_ne_one, hd.symm⟩)).trans
      (SimpleGraph.Adj.reachable ⟨one_ne_zero, hd'⟩)
  have h1 : ∀ c, (chess m).Reachable (1, c) (0, ⟨if c.1 = 0 then 1 else 0, by split_ifs <;> omega⟩) :=
    fun c => SimpleGraph.Adj.reachable ⟨one_ne_zero, fun h => by
      have := congrArg Fin.val h; dsimp at this; split_ifs at this <;> omega⟩
  have hx : ∀ x : Fin 2 × Fin m, (chess m).Reachable x (0, ⟨0, by omega⟩) := by
    rintro ⟨i, c⟩
    fin_cases i
    · exact h0 _ _
    · exact (h1 c).trans (h0 _ _)
  have : Nonempty (Fin 2 × Fin m) := ⟨(0, ⟨0, by omega⟩)⟩
  exact ⟨fun x y => (hx x).trans (hx y).symm⟩

end Quillen.Notebook1972_8Chess
