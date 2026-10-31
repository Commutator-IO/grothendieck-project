import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.Abel

/-!
# Bourbaki, rédaction n° 596 (Verdier–Bass, May 1974), § 10, Prop. 3 a): every class is a difference

Section 10 of rédaction 596 (« Groupes et anneaux de Grothendieck », Fonds Boutet de Monvel)
defines the Grothendieck group `K(C)` of an additive set `C` of classes of `A`-modules as the free
abelian group on `C` modulo the relations `[E] = [E'] + [E'']` of the short exact sequences. Its
Prop. 3 a) states that every `x ∈ K(C)` is `[E] − [F]` for two modules `E`, `F` of type `C`; the
proof writes `x` as a sum of generators and their opposites and collects each side into a direct
sum, since `[E ⊕ F] = [E] + [F]`.

The argument uses only two facts: `cl(E) ↦ [E]` is additive from the monoid of classes under `⊕`,
and its image generates `K(C)`. `diff_of_closure` proves the statement in that generality, for any
additive map from a commutative monoid whose image generates an abelian group; Prop. 3 a) is the
case `M` = the classes of `C` under `⊕`, `G = K(C)`. The modules and exact sequences themselves
are not formalised. `grothendieckAddGroup_diff` is the case of the group completion of `M`, where
the image of `M` generates by construction.
-/

namespace Grothendieck.Bourbaki596

open Algebra

/-- Prop. 3 a) of rédaction 596, abstracted: if the image of an additive map `f : M → G` generates
the abelian group `G`, every element of `G` is `f a − f b`. -/
theorem diff_of_closure {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (f : M →+ G)
    (hf : AddSubgroup.closure (Set.range f) = ⊤) (x : G) : ∃ a b : M, x = f a - f b := by
  have hx : x ∈ AddSubgroup.closure (Set.range f) := hf ▸ AddSubgroup.mem_top x
  induction hx using AddSubgroup.closure_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact ⟨a, 0, by simp⟩
  | zero => exact ⟨0, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, d, rfl⟩ := hz
    exact ⟨a + c, b + d, by simp only [map_add]; abel⟩
  | neg y _ hy =>
    obtain ⟨a, b, rfl⟩ := hy
    exact ⟨b, a, by simp⟩

/-- The same for the Grothendieck group (group completion) of a commutative monoid. -/
theorem grothendieckAddGroup_diff {M : Type*} [AddCommMonoid M] (x : GrothendieckAddGroup M) :
    ∃ a b : M, x = GrothendieckAddGroup.of a - GrothendieckAddGroup.of b := by
  induction x using AddLocalization.induction_on with
  | H y =>
    obtain ⟨a, ⟨b, hb⟩⟩ := y
    refine ⟨a, b, ?_⟩
    simp only [GrothendieckAddGroup.of, AddSubmonoid.LocalizationMap.toAddMonoidHom_apply,
      ← AddLocalization.mk_zero_eq_addMonoidOf_mk, GrothendieckAddGroup.mk_sub_mk]
    congr 1 <;> simp

end Grothendieck.Bourbaki596
