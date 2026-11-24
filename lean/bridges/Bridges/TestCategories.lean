/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Bridges.Combinatorics
public import Bridges.Monoids
public import Bridges.Preorders
public import LeanPool.ToposTheoreticBridges.DeMorgan
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Sites.Closed

/-!
# The De Morgan arch and test categories

Grothendieck's criterion (*Pursuing Stacks*; Maltsiniotis, *La théorie de l'homotopie de
Grothendieck*, Th. 6.6; Cisinski, Astérisque 308, Th. 4.1.19) reads the local test categories
on the Lawvere object `L` of `Cᵒᵖ ⥤ Type`, the presheaf of sieves (`Functor.sieves C` in
Mathlib): `C` is a local test category iff every category of elements of `a × L` is aspherical,
and a weak test category needs the category of elements of `L` to be aspherical. Every
aspherical category is connected, for any fundamental localizer except the two coarse ones
(Cisinski, Prop. 9.3.2). This file proves the connectedness part, which is all the obstruction
uses:

* `rightOreCondition_iff_pullback_ne_bot`: `C` satisfies the right Ore condition iff pulling
  back along any arrow never empties a nonempty sieve; in other words, iff the empty sieves
  form a direct summand of `L`;
* `not_isPreconnected_elements`: then, for any presheaf `G` over `L` with a section over the
  empty sieve and one over a nonempty sieve, the category of elements of `G` is not connected;
* `not_isConnected_elements_sieves`, `not_isConnected_elements_yonedaProdSieves`: so for a
  nonempty `C` with the right Ore condition, neither the category of elements of `L` nor that of
  any `a × L` is connected; hence `C` is neither a weak test category nor a local test category
  (the step from connectedness to asphericity is the paper's, not formalised here);
* `not_isConnected_elements_sieves_of_isDeMorganTopos`: the same, read through the De Morgan
  arch of lean-pool, when the presheaf topos is De Morgan;
* `not_isConnected_elements_sieves_simplexCategory_op`: a category with an initial object
  satisfies the right Ore condition (`rightOreCondition_of_isInitial`, in `Combinatorics.lean`),
  and so does `Δᵒᵖ`, whose
  presheaves are the cosimplicial sets (folder 108, p. 2, question 6: « `Δ°` est-elle une
  catégorie test ? non »).
* `not_isConnected_elements_sieves_preorder`, `not_isConnected_elements_sieves_linearOrder`,
  `not_isConnected_elements_sieves_int`, `not_isConnected_elements_sieves_multiplicative_nat`:
  decks with the Ore condition but no object whose slice is the point, such as `ℤ` and the
  monoid `ℕ`;
* `not_isDeMorganTopos_of_isConnected_elements_sieves`: read the other way, a category whose
  Lawvere object has connected elements, as a weak test category does, has a presheaf topos that
  is not De Morgan.
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory Opposite

universe u

variable {C : Type u} [SmallCategory C]

/-- A sieve is nonempty iff it contains an arrow. -/
theorem sieve_ne_bot_iff {X : C} (S : Sieve X) : S ≠ ⊥ ↔ ∃ (Y : C) (f : Y ⟶ X), S f := by
  refine ⟨fun hS => ?_, fun ⟨Y, f, hf⟩ he => by simp [he] at hf⟩
  by_contra! hn
  exact hS (Sieve.ext fun Y f => by simpa using hn Y f)

/-- **Ore condition and the empty sieve.** `C` satisfies the right Ore condition iff the pullback
of a nonempty sieve along any arrow is nonempty. -/
theorem rightOreCondition_iff_pullback_ne_bot :
    GrothendieckTopology.RightOreCondition C ↔
      ∀ {X Y : C} (S : Sieve X) (f : Y ⟶ X), S ≠ ⊥ → S.pullback f ≠ ⊥ := by
  refine ⟨fun h X Y S f hS => ?_, fun h X Y Z f g => ?_⟩
  · obtain ⟨Z, g, hg⟩ := (sieve_ne_bot_iff S).1 hS
    obtain ⟨W, k, l, hkl⟩ := h f g
    exact (sieve_ne_bot_iff _).2 ⟨W, k, by simpa [hkl] using S.downward_closed hg l⟩
  · obtain ⟨W, k, _, l, _, ⟨⟩, hm⟩ := (sieve_ne_bot_iff _).1 <|
      h (Sieve.generate (Presieve.singleton g)) f <|
        (sieve_ne_bot_iff _).2 ⟨Z, g, Sieve.le_generate _ _ _ (Presieve.singleton_self g)⟩
    exact ⟨W, k, l, hm.symm⟩

/-- Under the right Ore condition, a sieve pulls back to the empty sieve only if it is empty. -/
theorem pullback_eq_bot_iff (h : GrothendieckTopology.RightOreCondition C) {X Y : C}
    (f : Y ⟶ X) (S : Sieve X) : S.pullback f = ⊥ ↔ S = ⊥ :=
  ⟨fun he => by_contra fun hS => rightOreCondition_iff_pullback_ne_bot.1 h S f hS he,
    fun he => he ▸ Sieve.pullback_bot f⟩

/-- **The obstruction.** Under the right Ore condition, let `G` be a presheaf over the Lawvere
object `L` (`Functor.sieves C`) with a section over the empty sieve and a section over a nonempty
sieve. Then the category of elements of `G` is not connected: being over the empty sieve is
invariant along every arrow of `G.Elements`. -/
theorem not_isPreconnected_elements (h : GrothendieckTopology.RightOreCondition C)
    {G : Cᵒᵖ ⥤ Type u} (π : G ⟶ Functor.sieves C) (x y : G.Elements)
    (hx : π.app x.obj x.val = (⊥ : Sieve x.obj.unop))
    (hy : π.app y.obj y.val ≠ (⊥ : Sieve y.obj.unop)) : ¬ IsPreconnected G.Elements := by
  intro _
  have key := constant_of_preserves_morphisms
    (fun e : G.Elements => π.app e.obj e.val = (⊥ : Sieve e.obj.unop)) fun _ _ f => by
      rw [← f.map_val, NatTrans.naturality_apply]
      exact propext (pullback_eq_bot_iff h f.hom.unop _).symm
  exact hy ((key x y).mp hx)

/-- The empty sieve and the maximal sieve differ. -/
theorem top_ne_bot_sieve (X : C) : (⊤ : Sieve X) ≠ ⊥ :=
  (sieve_ne_bot_iff _).2 ⟨X, 𝟙 X, trivial⟩

/-- **Lawvere object.** For a nonempty `C` with the right Ore condition, the category of
elements of the Lawvere object `L` is not connected; so `L` is not aspherical and `C` is not a
weak test category. -/
theorem not_isConnected_elements_sieves [Nonempty C]
    (h : GrothendieckTopology.RightOreCondition C) : ¬ IsConnected (Functor.sieves C).Elements :=
  fun _ => let X := Classical.arbitrary C
    not_isPreconnected_elements h (𝟙 _) (.mk (obj := op X) (⊥ : Sieve X))
      (.mk (obj := op X) (⊤ : Sieve X)) rfl (top_ne_bot_sieve X) inferInstance

/-- The presheaf `a × L`, product of the representable presheaf of `a` and of the Lawvere
object. -/
@[simps]
def yonedaProdSieves (a : C) : Cᵒᵖ ⥤ Type u where
  obj X := (X.unop ⟶ a) × Sieve X.unop
  map f := ↾fun p => (f.unop ≫ p.1, p.2.pullback f.unop)

/-- The projection `a × L ⟶ L`. -/
@[simps]
def yonedaProdSievesSnd (a : C) : yonedaProdSieves a ⟶ Functor.sieves C where
  app X := ↾Prod.snd

/-- **Local test categories.** For `C` with the right Ore condition and any object `a`, the
category of elements of `a × L` is not connected; so `L` is not locally aspherical and `C` is
not a local test category. -/
theorem not_isConnected_elements_yonedaProdSieves
    (h : GrothendieckTopology.RightOreCondition C) (a : C) :
    ¬ IsConnected (yonedaProdSieves a).Elements := fun _ =>
  not_isPreconnected_elements h (yonedaProdSievesSnd a) (.mk (obj := op a) (𝟙 a, ⊥))
    (.mk (obj := op a) (𝟙 a, ⊤)) rfl (top_ne_bot_sieve a) inferInstance

/-- **The De Morgan arch reads the obstruction.** If the presheaf topos of a nonempty `C` is
De Morgan, the category of elements of its Lawvere object is not connected. -/
theorem not_isConnected_elements_sieves_of_isDeMorganTopos [Nonempty C]
    (h : IsDeMorganTopos (Cᵒᵖ ⥤ Type u)) : ¬ IsConnected (Functor.sieves C).Elements :=
  not_isConnected_elements_sieves ((isDeMorganTopos_presheaf_iff_rightOreCondition C).1 h)

/-- **Folder 108, p. 2, question 6.** `Δᵒᵖ` has an initial object, `⦋0⦌`, so the category of
elements of its Lawvere object is not connected: `Δᵒᵖ` is neither a weak test category nor a
local test category. -/
theorem not_isConnected_elements_sieves_simplexCategory_op :
    ¬ IsConnected (Functor.sieves SimplexCategoryᵒᵖ).Elements :=
  have : Nonempty SimplexCategoryᵒᵖ := ⟨op (SimplexCategory.mk 0)⟩
  not_isConnected_elements_sieves (rightOreCondition_of_isInitial SimplexCategory.isTerminalZero.op)

/-- For a monoid in which any two elements have a common right multiple (a commutative monoid,
a group, a monoid with zero), the category of elements of the Lawvere object of right `M`-sets
is not connected. -/
theorem not_isConnected_elements_sieves_singleObj (M : Type) [Monoid M]
    (h : ∀ a b : M, ∃ c d : M, a * c = b * d) :
    ¬ IsConnected (Functor.sieves (SingleObj M)).Elements :=
  have : Nonempty (SingleObj M) := ⟨SingleObj.star M⟩
  not_isConnected_elements_sieves (rightOreCondition_singleObj_iff.2 h)

/-- **Ore orders.** In a nonempty preorder in which any two elements below a common element have
a common lower bound, the category of elements of the Lawvere object is not connected: the
preorder is neither a weak test category nor a local test category, even when it has no minimal
element, so that no slice is the point. -/
theorem not_isConnected_elements_sieves_preorder (P : Type u) [Preorder P] [Nonempty P]
    (h : ∀ x y z : P, y ≤ x → z ≤ x → ∃ w, w ≤ y ∧ w ≤ z) :
    ¬ IsConnected (Functor.sieves P).Elements :=
  not_isConnected_elements_sieves ((rightOreCondition_preorder_iff P).2 h)

/-- A nonempty total order, such as `ℤ`, `ℚ` or `ℝ`, is neither a weak test category nor a local
test category. -/
theorem not_isConnected_elements_sieves_linearOrder (P : Type u) [LinearOrder P] [Nonempty P] :
    ¬ IsConnected (Functor.sieves P).Elements :=
  not_isConnected_elements_sieves_preorder P fun _ y z _ _ =>
    ⟨min y z, min_le_left y z, min_le_right y z⟩

/-- `ℤ`, which has no minimal element. -/
theorem not_isConnected_elements_sieves_int : ¬ IsConnected (Functor.sieves ℤ).Elements :=
  not_isConnected_elements_sieves_linearOrder ℤ

/-- The monoid `ℕ`, whose presheaves are the sets with an endomorphism. -/
theorem not_isConnected_elements_sieves_multiplicative_nat :
    ¬ IsConnected (Functor.sieves (SingleObj (Multiplicative ℕ))).Elements :=
  not_isConnected_elements_sieves_singleObj _ fun a b => ⟨b, a, mul_comm a b⟩

/-- **Test categories are not De Morgan.** If the category of elements of the Lawvere object of
a nonempty `C` is connected, as it is for a weak test category, then the presheaf topos of `C`
is not De Morgan. -/
theorem not_isDeMorganTopos_of_isConnected_elements_sieves [Nonempty C]
    (h : IsConnected (Functor.sieves C).Elements) : ¬ IsDeMorganTopos (Cᵒᵖ ⥤ Type u) :=
  fun hD => not_isConnected_elements_sieves_of_isDeMorganTopos hD h

end LeanPool.ToposTheoreticBridges.Examples
