import Mathlib

/-!
# Buffalo, topos theory, part 4: claims of the blackboards not covered by an index entry

Items of `public/buffalo-boards/PqCQM3Pcl6Q-*.json` (3:23:52–9:02:23) that make a mathematical
claim not already formalised by an entry of `docs/buffalo-topos/lean/Part04.json`. The status of
every board item is in `docs/buffalo-topos/lean/Part04-boards.json`.
-/

universe v u

open CategoryTheory

namespace Buffalo.Topos.Part04.Boards

/-- Board PqCQM3Pcl6Q-24609, t = 26619: in a preordered (thin) category every morphism is a
monomorphism. -/
theorem thin_mono {C : Type u} [Category.{v} C] [Quiver.IsThin C] {X Y : C} (f : X ⟶ Y) :
    Mono f :=
  ⟨fun g h _ => Subsingleton.elim g h⟩

/-- Board PqCQM3Pcl6Q-24609, t = 26619: the converse fails, so « every morphism is a
monomorphism » does not characterise preordered categories: the group `ℤ` as a one-object
category has all its morphisms monomorphisms but two distinct endomorphisms. -/
theorem allMono_not_thin :
    (∀ (X Y : SingleObj (Multiplicative ℤ)) (f : X ⟶ Y), Mono f) ∧
      ¬ Quiver.IsThin (SingleObj (Multiplicative ℤ)) := by
  refine ⟨fun _ _ f => inferInstance, fun h => ?_⟩
  have := (h (SingleObj.star _) (SingleObj.star _)).elim
    (1 : Multiplicative ℤ) (Multiplicative.ofAdd (1 : ℤ))
  have h2 := congrArg Multiplicative.toAdd this
  simp at h2

end Buffalo.Topos.Part04.Boards
