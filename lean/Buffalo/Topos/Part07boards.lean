import Buffalo.Topos.Part07a

/-!
# Buffalo, topos theory, part 7: blackboard items not covered by an index entry

Board items of video `ORG14LNb5gE` (20167–22980) on the canonical topology and the comparison
lemma. Statuses in `docs/buffalo-topos/lean/Part07-boards.json`.
-/

universe u v

open CategoryTheory Limits GrothendieckTopology

namespace Buffalo.Topos.Part07

/-- Board ORG14LNb5gE-20167 (5:37:50) Representables are sheaves iff the topology is coarser than the
canonical topology. -/
theorem subcanonical_iff_le_canonical {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    J.Subcanonical ↔ J ≤ Sheaf.canonicalTopology C :=
  ⟨fun _ => J.le_canonical, fun h => Subcanonical.of_le h⟩

/-- Board ORG14LNb5gE-20167 (5:38:35) For a subcanonical topology, `C → C̃` is fully faithful. -/
noncomputable def subcanonical_yoneda_fullyFaithful {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [J.Subcanonical] : J.yoneda.FullyFaithful :=
  J.yonedaFullyFaithful

end Buffalo.Topos.Part07
