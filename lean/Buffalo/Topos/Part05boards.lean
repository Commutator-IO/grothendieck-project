import Mathlib

/-!
# Buffalo, topos theory, part 5: claims of the blackboards not covered by an index entry

Items of `public/buffalo-boards/PqCQM3Pcl6Q-32543.json`, `PqCQM3Pcl6Q-35544.json` (9:02:23–10:14:40)
and `public/buffalo-boards/4gynb9uTEE4-*.json` (0:00:01–4:14:00) that make a mathematical claim not
already formalised by an entry of `docs/buffalo-topos/lean/Part05.json`. The status of every board
item is in `docs/buffalo-topos/lean/Part05-boards.json`.
-/

universe u

open CategoryTheory Limits

namespace Buffalo.Topos.Part05.Boards

/-- Board 4gynb9uTEE4-12717, t = 12950 (« the saturation `Σ̃` is never small »): false as stated.
`Prop` is a small category with all small limits, so every class of its arrows, in particular a
saturated one, is small. (`Σ̃` contains all isomorphisms, so it is not small as soon as the
category is not essentially small.) -/
theorem prop_hasLimits : HasLimits Prop := inferInstance

theorem prop_arrows_small : Small.{0} (Σ X Y : Prop, X ⟶ Y) := inferInstance

/-- Board 4gynb9uTEE4-12717, t = 13705–13769: the distributive law `X ∩ ⋃ Yᵢ = ⋃ (X ∩ Yᵢ)` holds
in every complete Boolean algebra (indeed every frame), so together with complements it
axiomatizes complete Boolean algebras, not the complete atomic ones (`𝒫(E)`), which need complete
distributivity. -/
theorem inf_iSup_complete {α : Type u} [CompleteBooleanAlgebra α] {ι : Type*} (x : α)
    (y : ι → α) : x ⊓ ⨆ i, y i = ⨆ i, x ⊓ y i :=
  inf_iSup_eq x y

/-- ... complete distributivity holds in `𝒫(E)` (every complete atomic Boolean algebra is
completely distributive). -/
theorem set_completelyDistrib (E : Type u) : Nonempty (CompletelyDistribLattice (Set E)) :=
  ⟨inferInstance⟩

end Buffalo.Topos.Part05.Boards
