/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Bridges.FiniteMonoids
public import Bridges.QuiversDeMorgan
public import Bridges.TestCategories
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.Data.Fintype.Pigeonhole

/-!
# Test categories, axiomatically

Mathlib has neither the weak equivalences of small categories nor Grothendieck's test notions, so
this file states them as in *Pursuing Stacks* and in Cisinski, *Les préfaisceaux comme modèles des
types d'homotopie* (Astérisque 308), on top of an abstract class `W` of functors:

* `FundamentalLocalizer`: Grothendieck's axioms (Cisinski, Déf. 3.3.2): `W` is weakly saturated
  (identities, two out of three, retracts), contains `A ⥤ e` for `A` with a terminal object, and
  satisfies the relative Theorem A;
* `iStar A C`: the presheaf `a ↦ (A/a ⥤ C)`, Grothendieck's `i_A^*(C)`;
* `IsWeakTest`, `IsLocalTest` (Cisinski, Déf. 4.1.8 and 4.1.12): `A/i_A^*(C)` is aspherical for
  every `C` with a terminal object; every slice `A/a` is a weak test category.

The one property of `W` used below is `AsphericalConnected`: an aspherical category is connected.
It holds when `W` induces bijections on `π₀`, which is the case of every fundamental localizer
except the two coarse ones (Cisinski, Prop. 9.3.2, not formalised), in particular of the usual
weak equivalences (whose definition, through the nerve, Mathlib lacks).

Main results:

* `not_isWeakTest`, `not_isLocalTest`: a nonempty category with the right Ore condition is neither
  a weak test category nor a local test category. With `C = ULift Bool` (the category `Δ₁`), the
  functors `A/a ⥤ Δ₁` that are constant at the top form a union of components of the category of
  elements of `i_A^*(Δ₁)`: the Ore condition lets a value `⊥` travel along every arrow;
* `not_isWeakTest_of_isDeMorganTopos`, `not_isDeMorganTopos_of_isWeakTest`,
  `not_isDeMorganTopos_over_of_isLocalTest`: the same through the De Morgan arch, and backwards;
* corollaries: `Δᵒᵖ` (folder 108, p. 2, question 6), groupoids, preorders with down-directed
  principal down-sets and total orders (`ℤ`), monoids with common right multiples (`ℕ`), finite
  monoids with a single minimal right ideal (through `FiniteMonoids.lean`), free categories
  on quivers with at most one arrow into each vertex, and preorders with a minimal element (local
  test only);
* `exists_source_of_acyclic`, `not_isLocalTest_paths_of_acyclic`: a finite nonempty quiver without
  cycles has a source, the slice of the free category over it is the point
  (`rightOreCondition_over_paths_of_source`), so the free category is not a local test category;
* `not_isPreconnected_zigZagProd`, `not_isAspherical_zigZagProd` (folder 118, p. 36): the product
  of the zigzags `Zₙ`, each connected, is not connected, hence not aspherical. That each `Zₙ` is
  aspherical is not formalised.
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace LeanPool.ToposTheoreticBridges.Examples

universe u

/-- **Fundamental localizer** (Grothendieck; Cisinski, Déf. 3.3.2), on the small categories of
the universe `u`: a class of functors, weakly saturated, containing `A ⥤ e` when `A` has a terminal
object, and satisfying the relative Theorem A. -/
structure FundamentalLocalizer where
  W : ∀ {A B : Type u} [SmallCategory A] [SmallCategory B], (A ⥤ B) → Prop
  id_mem : ∀ (A : Type u) [SmallCategory A], W (𝟭 A)
  comp_mem : ∀ {A B C : Type u} [SmallCategory A] [SmallCategory B] [SmallCategory C]
    (f : A ⥤ B) (g : B ⥤ C), W f → W g → W (f ⋙ g)
  of_comp_left : ∀ {A B C : Type u} [SmallCategory A] [SmallCategory B] [SmallCategory C]
    (f : A ⥤ B) (g : B ⥤ C), W f → W (f ⋙ g) → W g
  of_comp_right : ∀ {A B C : Type u} [SmallCategory A] [SmallCategory B] [SmallCategory C]
    (f : A ⥤ B) (g : B ⥤ C), W g → W (f ⋙ g) → W f
  of_retract : ∀ {A B : Type u} [SmallCategory A] [SmallCategory B] (i : A ⥤ B) (r : B ⥤ A),
    i ⋙ r = 𝟭 A → W (r ⋙ i) → W r
  star_mem_of_hasTerminal : ∀ (A : Type u) [SmallCategory A] [HasTerminal A],
    W (Functor.star A : A ⥤ Discrete PUnit.{u + 1})
  mem_of_costructuredArrow : ∀ {A B C : Type u} [SmallCategory A] [SmallCategory B]
    [SmallCategory C] (f : A ⥤ B) (g : B ⥤ C), (∀ c, W (CostructuredArrow.pre f g c)) → W f

namespace FundamentalLocalizer

variable (L : FundamentalLocalizer.{u})

/-- A small category is aspherical when its functor to the point is in `W`. -/
def IsAspherical (A : Type u) [SmallCategory A] : Prop :=
  L.W (Functor.star A : A ⥤ Discrete PUnit.{u + 1})

/-- Every aspherical category is connected. This holds for a fundamental localizer contained in
the `π₀`-equivalences, that is, for every one but the two coarse ones (Cisinski, Prop. 9.3.2). -/
def AsphericalConnected : Prop :=
  ∀ (A : Type u) [SmallCategory A], L.IsAspherical A → IsConnected A

end FundamentalLocalizer

variable (A : Type u) [SmallCategory A]

/-- `Over.map (𝟙 X)` is the identity functor, as an equality. -/
theorem over_map_id_eq (X : A) : Over.map (𝟙 X) = 𝟭 _ :=
  congrArg Cat.Hom.toFunctor ((Over.mapFunctor A).map_id X)

/-- `Over.map` is strictly functorial. -/
theorem over_map_comp_eq {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Over.map (f ≫ g) = Over.map f ⋙ Over.map g :=
  congrArg Cat.Hom.toFunctor ((Over.mapFunctor A).map_comp f g)

/-- Grothendieck's `i_A^*(C)`: the presheaf `a ↦ (A/a ⥤ C)` on `A`. -/
@[simps]
def iStar (C : Type u) [SmallCategory C] : Aᵒᵖ ⥤ Type u where
  obj a := Over a.unop ⥤ C
  map f := ↾fun F => Over.map f.unop ⋙ F
  map_id a := by ext F; simp [over_map_id_eq]; rfl
  map_comp f g := by ext F; simp [over_map_comp_eq, Functor.assoc]

/-- **Weak test category** (Cisinski, Déf. 4.1.8): for every small category `C` with a
terminal object, the category of elements `A/i_A^*(C)` is aspherical. -/
def IsWeakTest (L : FundamentalLocalizer.{u}) : Prop :=
  ∀ (C : Type u) [SmallCategory C] [HasTerminal C], L.IsAspherical (iStar A C).Elementsᵒᵖ

/-- **Local test category** (Cisinski, Déf. 4.1.12): every slice `A/a` is a weak test
category. -/
def IsLocalTest (L : FundamentalLocalizer.{u}) : Prop :=
  ∀ a : A, IsWeakTest (Over a) L

variable {A}

/-- The right Ore condition passes to the slices. -/
theorem rightOreCondition_over (h : GrothendieckTopology.RightOreCondition A) (a : A) :
    GrothendieckTopology.RightOreCondition (Over a) := fun f g => by
  obtain ⟨W, k, l, hkl⟩ := h f.left g.left
  refine ⟨Over.mk (k ≫ _), Over.homMk k, Over.homMk l ?_, Over.OverMorphism.ext hkl⟩
  change l ≫ _ = k ≫ _
  rw [← Over.w g, ← Over.w f, ← Category.assoc, ← hkl, Category.assoc]

/-- **The De Morgan obstruction.** A nonempty category with the right Ore condition is not a weak
test category. -/
theorem not_isWeakTest {L : FundamentalLocalizer.{u}} (hL : L.AsphericalConnected) [Nonempty A]
    (h : GrothendieckTopology.RightOreCondition A) : ¬ IsWeakTest A L := by
  intro hw
  have := hL _ (hw (ULift.{u} Bool))
  have : IsConnected (iStar A (ULift.{u} Bool)).Elements := isConnected_of_isConnected_op
  let a := Classical.arbitrary A
  let P : (iStar A (ULift.{u} Bool)).Elements → Prop := fun e => ∀ x, e.val.obj x = ⊤
  have key := constant_of_preserves_morphisms P (fun e e' f => by
    obtain ⟨φ, hφ⟩ := f
    refine propext ⟨fun he y => ?_, fun he' x => ?_⟩
    · exact hφ ▸ he _
    · obtain ⟨W, k, l, hkl⟩ := h φ.unop x.hom
      have hk := he' (Over.mk k)
      rw [← hφ] at hk
      have hle := leOfHom (e.val.map (Over.homMk l hkl.symm : Over.mk (k ≫ φ.unop) ⟶ x))
      exact top_le_iff.1 (hk.symm.trans_le hle))
    (.mk (obj := op a) ((Functor.const _).obj ⊤)) (.mk (obj := op a) ((Functor.const _).obj ⊥))
  exact bot_ne_top ((key.mp fun _ => rfl) (Over.mk (𝟙 a)))

/-- If some slice `A/a` satisfies the right Ore condition, `A` is not a local test category. -/
theorem not_isLocalTest_of_over {L : FundamentalLocalizer.{u}} (hL : L.AsphericalConnected)
    (a : A) (h : GrothendieckTopology.RightOreCondition (Over a)) : ¬ IsLocalTest A L := fun hl =>
  have : Nonempty (Over a) := ⟨Over.mk (𝟙 a)⟩
  not_isWeakTest hL h (hl a)

/-- A nonempty category with the right Ore condition is not a local test category. -/
theorem not_isLocalTest {L : FundamentalLocalizer.{u}} (hL : L.AsphericalConnected) [Nonempty A]
    (h : GrothendieckTopology.RightOreCondition A) : ¬ IsLocalTest A L :=
  not_isLocalTest_of_over hL (Classical.arbitrary A) (rightOreCondition_over h _)

/-- Both conclusions together. -/
theorem not_isWeakTest_and_not_isLocalTest {L : FundamentalLocalizer.{u}}
    (hL : L.AsphericalConnected) [Nonempty A] (h : GrothendieckTopology.RightOreCondition A) :
    ¬ IsWeakTest A L ∧ ¬ IsLocalTest A L :=
  ⟨not_isWeakTest hL h, not_isLocalTest hL h⟩

/-- **Through the De Morgan arch.** A nonempty category whose presheaf topos is De Morgan is
neither a weak nor a local test category. -/
theorem not_isWeakTest_of_isDeMorganTopos {L : FundamentalLocalizer.{u}}
    (hL : L.AsphericalConnected) [Nonempty A] (h : IsDeMorganTopos (Aᵒᵖ ⥤ Type u)) :
    ¬ IsWeakTest A L ∧ ¬ IsLocalTest A L :=
  not_isWeakTest_and_not_isLocalTest hL ((isDeMorganTopos_presheaf_iff_rightOreCondition A).1 h)

/-- **Backwards.** The presheaf topos of a nonempty weak test category is not De Morgan. -/
theorem not_isDeMorganTopos_of_isWeakTest {L : FundamentalLocalizer.{u}}
    (hL : L.AsphericalConnected) [Nonempty A] (h : IsWeakTest A L) :
    ¬ IsDeMorganTopos (Aᵒᵖ ⥤ Type u) :=
  fun hD => (not_isWeakTest_of_isDeMorganTopos hL hD).1 h

/-- For a local test category, no slice topos `Â/a ≃ (A/a)^` is De Morgan. -/
theorem not_isDeMorganTopos_over_of_isLocalTest {L : FundamentalLocalizer.{u}}
    (hL : L.AsphericalConnected) (h : IsLocalTest A L) (a : A) :
    ¬ IsDeMorganTopos ((Over a)ᵒᵖ ⥤ Type u) :=
  have : Nonempty (Over a) := ⟨Over.mk (𝟙 a)⟩
  not_isDeMorganTopos_of_isWeakTest hL (h a)

/-- A groupoid satisfies the right Ore condition. -/
theorem rightOreCondition_of_groupoid (G : Type*) [Groupoid G] :
    GrothendieckTopology.RightOreCondition G :=
  fun f g => ⟨_, 𝟙 _, f ≫ Groupoid.inv g, by simp⟩

/-- A nonempty groupoid is neither a weak nor a local test category. -/
theorem not_isTest_groupoid {L : FundamentalLocalizer.{u}} (hL : L.AsphericalConnected)
    (G : Type u) [Groupoid.{u} G] [Nonempty G] : ¬ IsWeakTest G L ∧ ¬ IsLocalTest G L :=
  not_isWeakTest_and_not_isLocalTest hL (rightOreCondition_of_groupoid G)

/-- **Folder 108, p. 2, question 6.** `Δᵒᵖ`, which has the initial object `⦋0⦌`, is neither a
weak nor a local test category. -/
theorem not_isTest_simplexCategory_op {L : FundamentalLocalizer.{0}}
    (hL : L.AsphericalConnected) :
    ¬ IsWeakTest SimplexCategoryᵒᵖ L ∧ ¬ IsLocalTest SimplexCategoryᵒᵖ L :=
  have : Nonempty SimplexCategoryᵒᵖ := ⟨op (SimplexCategory.mk 0)⟩
  not_isWeakTest_and_not_isLocalTest hL
    (rightOreCondition_of_isInitial SimplexCategory.isTerminalZero.op)

/-- A nonempty preorder whose principal down-sets are down-directed is neither a weak nor a local
test category. -/
theorem not_isTest_preorder {L : FundamentalLocalizer.{u}} (hL : L.AsphericalConnected)
    (P : Type u) [Preorder P] [Nonempty P]
    (h : ∀ x y z : P, y ≤ x → z ≤ x → ∃ w, w ≤ y ∧ w ≤ z) :
    ¬ IsWeakTest P L ∧ ¬ IsLocalTest P L :=
  not_isWeakTest_and_not_isLocalTest hL ((rightOreCondition_preorder_iff P).2 h)

/-- A nonempty total order is neither a weak nor a local test category. -/
theorem not_isTest_linearOrder {L : FundamentalLocalizer.{u}} (hL : L.AsphericalConnected)
    (P : Type u) [LinearOrder P] [Nonempty P] : ¬ IsWeakTest P L ∧ ¬ IsLocalTest P L :=
  not_isTest_preorder hL P fun _ y z _ _ => ⟨min y z, min_le_left y z, min_le_right y z⟩

/-- `ℤ`, which has no minimal element. -/
theorem not_isTest_int {L : FundamentalLocalizer.{0}} (hL : L.AsphericalConnected) :
    ¬ IsWeakTest ℤ L ∧ ¬ IsLocalTest ℤ L :=
  not_isTest_linearOrder hL ℤ

/-- A preorder with a minimal element is not a local test category: the slice over it
satisfies the right Ore condition. -/
theorem not_isLocalTest_of_minimal {L : FundamentalLocalizer.{u}} (hL : L.AsphericalConnected)
    {P : Type u} [Preorder P] (m : P) (hm : ∀ x, x ≤ m → m ≤ x) : ¬ IsLocalTest P L :=
  not_isLocalTest_of_over hL m fun {_ Y Z} _ _ =>
    ⟨Y, 𝟙 Y, Over.homMk (homOfLE ((Y.hom.le.trans (hm _ Z.hom.le)))) (Subsingleton.elim _ _),
      Over.OverMorphism.ext (Subsingleton.elim _ _)⟩

/-- A monoid in which any two elements have a common right multiple is neither a weak nor a
local test category. -/
theorem not_isTest_singleObj {L : FundamentalLocalizer.{0}} (hL : L.AsphericalConnected)
    (M : Type) [Monoid M] (h : ∀ a b : M, ∃ c d : M, a * c = b * d) :
    ¬ IsWeakTest (SingleObj M) L ∧ ¬ IsLocalTest (SingleObj M) L :=
  have : Nonempty (SingleObj M) := ⟨SingleObj.star M⟩
  not_isWeakTest_and_not_isLocalTest hL (rightOreCondition_singleObj_iff.2 h)

/-- The monoid `ℕ`, whose presheaves are the sets with an endomorphism. -/
theorem not_isTest_multiplicative_nat {L : FundamentalLocalizer.{0}}
    (hL : L.AsphericalConnected) :
    ¬ IsWeakTest (SingleObj (Multiplicative ℕ)) L ∧
      ¬ IsLocalTest (SingleObj (Multiplicative ℕ)) L :=
  not_isTest_singleObj hL _ fun a b => ⟨b, a, mul_comm a b⟩

/-- **Free categories.** The free category on a nonempty quiver with at most one arrow into each
vertex is neither a weak nor a local test category. -/
theorem not_isTest_paths {L : FundamentalLocalizer.{u + 1}} (hL : L.AsphericalConnected)
    (Q : Type (u + 1)) [Quiver.{u + 1} Q] [Nonempty Q]
    (hQ : ∀ v : Q, Subsingleton (Σ w : Q, w ⟶ v)) :
    ¬ IsWeakTest (Paths Q) L ∧ ¬ IsLocalTest (Paths Q) L :=
  have : Nonempty (Paths Q) := ‹Nonempty Q›
  not_isWeakTest_and_not_isLocalTest hL ((rightOreCondition_paths_iff Q).2 hQ)


/-- A finite monoid with a single minimal right ideal is neither a weak nor a local test
category (the Ore condition through `forall_exists_mul_eq_mul_iff_existsUnique_minimal`). -/
theorem not_isTest_finite_monoid {L : FundamentalLocalizer.{0}} (hL : L.AsphericalConnected)
    (M : Type) [Monoid M] [Finite M] (h : ∃! I : Set M, Minimal IsRightIdeal I) :
    ¬ IsWeakTest (SingleObj M) L ∧ ¬ IsLocalTest (SingleObj M) L :=
  not_isTest_singleObj hL M (forall_exists_mul_eq_mul_iff_existsUnique_minimal.2 h)

section Acyclic

open Quiver

variable {Q : Type (u + 1)} [Quiver.{u + 1} Q]

/-- Two paths of length zero with the same ends are equal. -/
theorem path_eq_of_length_eq_zero {a b : Q} (p q : Path a b) (hp : p.length = 0)
    (hq : q.length = 0) : p = q := by
  cases p with
  | nil => cases q with
    | nil => rfl
    | cons q e => simp at hq
  | cons p e => simp at hp

/-- A path into a vertex that receives no arrow has length zero. -/
theorem path_length_eq_zero_of_source {v : Q} (hv : ∀ w, IsEmpty (w ⟶ v)) {a b : Q}
    (p : Path a b) (hb : b = v) : p.length = 0 := by
  cases p with
  | nil => rfl
  | cons p e => subst hb; exact (hv _).elim e

/-- A path into a vertex that receives no arrow starts at that vertex. -/
theorem eq_of_path_of_source {v : Q} (hv : ∀ w, IsEmpty (w ⟶ v)) {a b : Q} (p : Path a b)
    (hb : b = v) : a = b := by
  cases p with
  | nil => rfl
  | cons p e => subst hb; exact (hv _).elim e

/-- A vertex of `Q`, as an object of the free category. -/
def toPaths (v : Q) : Paths Q := v

/-- **Sources.** In the free category on a quiver, the slice over a vertex that receives no
arrow satisfies the right Ore condition: it is equivalent to the point. -/
theorem rightOreCondition_over_paths_of_source (v : Q) (hv : ∀ w, IsEmpty (w ⟶ v)) :
    GrothendieckTopology.RightOreCondition (Over (toPaths v)) := by
  have hsub : ∀ {a : Paths Q} (p q : a ⟶ toPaths v), p = q := fun p q =>
    path_eq_of_length_eq_zero p q (path_length_eq_zero_of_source hv p rfl)
      (path_length_eq_zero_of_source hv q rfl)
  have hleft : ∀ {Y X : Over (toPaths v)} (f f' : Y ⟶ X), f = f' := fun {Y X} f f' => by
    have hl : ∀ g : Y ⟶ X, Path.length (V := Q) g.left = 0 := fun g => by
      have hw : Path.comp (V := Q) g.left X.hom = Y.hom := Over.w g
      have := congrArg Path.length hw
      have h0 := path_length_eq_zero_of_source hv (Y.hom : Path (V := Q) Y.left v) rfl
      have hc : (Path.comp (V := Q) g.left X.hom).length =
          Path.length (V := Q) g.left + Path.length (V := Q) X.hom := Path.length_comp _ _
      omega
    exact Over.OverMorphism.ext (path_eq_of_length_eq_zero _ _ (hl f) (hl f'))
  intro X Y Z f g
  have hY := eq_of_path_of_source hv (Y.hom : Path (V := Q) Y.left v) rfl
  have hZ := eq_of_path_of_source hv (Z.hom : Path (V := Q) Z.left v) rfl
  exact ⟨Y, 𝟙 Y, Over.homMk (eqToHom (hY.trans hZ.symm)) (hsub _ _), hleft _ _⟩

/-- In the free category on a quiver, a vertex that receives no arrow makes the slice over it
satisfy the right Ore condition, so the free category is not a local test category. -/
theorem not_isLocalTest_paths_of_source {L : FundamentalLocalizer.{u + 1}}
    (hL : L.AsphericalConnected) (v : Q) (hv : ∀ w, IsEmpty (w ⟶ v)) :
    ¬ IsLocalTest (Paths Q) L :=
  not_isLocalTest_of_over hL _ (rightOreCondition_over_paths_of_source v hv)

/-- A path that ends where it starts is a cycle; under acyclicity it is trivial. -/
theorem path_length_eq_zero_of_acyclic (hac : ∀ (v : Q) (p : Path v v), p.length = 0)
    {a b : Q} (p : Path a b) (h : a = b) : p.length = 0 := by
  subst h
  exact hac _ p

/-- **Finite acyclic quivers have a source.** -/
theorem exists_source_of_acyclic [Finite Q] [Nonempty Q]
    (hac : ∀ (v : Q) (p : Path v v), p.length = 0) : ∃ v : Q, ∀ w, IsEmpty (w ⟶ v) := by
  by_contra! h
  choose pred e using fun x : Q => (h x)
  let arr : ∀ x : Q, pred x ⟶ x := fun x => Classical.choice (e x)
  let seq : ℕ → Q := fun n => Nat.rec (Classical.arbitrary Q) (fun _ x => pred x) n
  let down : ∀ i k, Path (seq (i + k)) (seq i) := fun i k =>
    Nat.rec (motive := fun k => Path (seq (i + k)) (seq i)) Path.nil
      (fun k p => (arr (seq (i + k))).toPath.comp p) k
  have hlen : ∀ i k, (down i k).length = k := fun i k => by
    induction k with
    | zero => rfl
    | succ k ih =>
      change ((arr (seq (i + k))).toPath.comp (down i k)).length = k + 1
      rw [Path.length_comp, Path.length_toPath, ih]
      omega
  obtain ⟨x, y, hxy, hseq⟩ := Finite.exists_ne_map_eq_of_infinite seq
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · have := path_length_eq_zero_of_acyclic hac (down x (y - x))
      (by rw [Nat.add_sub_cancel' hlt.le]; exact hseq.symm)
    rw [hlen] at this
    omega
  · have := path_length_eq_zero_of_acyclic hac (down y (x - y))
      (by rw [Nat.add_sub_cancel' hlt.le]; exact hseq)
    rw [hlen] at this
    omega

/-- **Finite acyclic free categories.** The free category on a finite nonempty quiver without
cycles is not a local test category: the quiver has a source, and the slice over it is the
point. -/
theorem not_isLocalTest_paths_of_acyclic {L : FundamentalLocalizer.{u + 1}}
    (hL : L.AsphericalConnected) [Finite Q] [Nonempty Q]
    (hac : ∀ (v : Q) (p : Path v v), p.length = 0) : ¬ IsLocalTest (Paths Q) L :=
  let ⟨v, hv⟩ := exists_source_of_acyclic hac
  not_isLocalTest_paths_of_source hL v hv

end Acyclic

section ZigZag

/-- The zigzag `0 → 1 ← 2 → 3 ← ⋯` on `n + 1` objects: the arrows go from an even object to the
adjacent odd ones. -/
def ZigZag (n : ℕ) : Type := Fin (n + 1)

/-- The order of the zigzag: `i ≤ j` iff `i = j`, or `i` is even and `j` is adjacent to it. -/
instance (n : ℕ) : PartialOrder (ZigZag n) where
  le i j := i = j ∨ (Fin.val (n := n + 1) i % 2 = 0 ∧
    (Fin.val (n := n + 1) j = Fin.val (n := n + 1) i + 1 ∨
      Fin.val (n := n + 1) j + 1 = Fin.val (n := n + 1) i))
  le_refl _ := Or.inl rfl
  le_trans i j k hij hjk := by
    rcases hij with rfl | hij
    · exact hjk
    · rcases hjk with rfl | hjk
      · exact Or.inr hij
      · omega
  le_antisymm i j hij hji := by
    rcases hij with h | hij
    · exact h
    · rcases hji with h | hji
      · exact h.symm
      · omega

/-- An object of the zigzag. -/
def ZigZag.mk {n : ℕ} (m : ℕ) (h : m < n + 1) : ZigZag n := (⟨m, h⟩ : Fin (n + 1))

/-- The order of the zigzag. -/
theorem ZigZag.le_iff {n : ℕ} {i j : ZigZag n} : i ≤ j ↔ i = j ∨ (Fin.val (n := n + 1) i % 2 = 0 ∧
    (Fin.val (n := n + 1) j = Fin.val (n := n + 1) i + 1 ∨
      Fin.val (n := n + 1) j + 1 = Fin.val (n := n + 1) i)) := Iff.rfl

/-- Comparable objects of a zigzag are adjacent. -/
theorem ZigZag.val_le_of_le {n : ℕ} {i j : ZigZag n} (h : i ≤ j) :
    Fin.val (n := n + 1) j ≤ Fin.val (n := n + 1) i + 1 ∧
      Fin.val (n := n + 1) i ≤ Fin.val (n := n + 1) j + 1 := by
  rcases h with rfl | h
  · omega
  · omega

/-- Each zigzag is connected. -/
instance (n : ℕ) : IsConnected (ZigZag n) := by
  have key : ∀ m (hm : m < n + 1), Zigzag (ZigZag.mk 0 (by omega)) (ZigZag.mk m hm) := by
    intro m
    induction m with
    | zero => exact fun _ => Relation.ReflTransGen.refl
    | succ m ih =>
      intro hm
      refine (ih (by omega)).trans ?_
      rcases Nat.mod_two_eq_zero_or_one m with he | ho
      · exact Zigzag.of_hom (homOfLE (ZigZag.le_iff.2 (Or.inr ⟨he, Or.inl rfl⟩) :
          ZigZag.mk m (by omega) ≤ ZigZag.mk (m + 1) hm))
      · exact Zigzag.of_inv (homOfLE (ZigZag.le_iff.2 (Or.inr ⟨by simp [ZigZag.mk]; omega,
          Or.inr rfl⟩) : ZigZag.mk (m + 1) hm ≤ ZigZag.mk m (by omega)))
  have : Nonempty (ZigZag n) := ⟨ZigZag.mk 0 (by omega)⟩
  exact zigzag_isConnected fun a b =>
    (key _ (Fin.isLt (n := n + 1) a)).symm.trans (key _ (Fin.isLt (n := n + 1) b))

/-- The product category `∏ₙ Zₙ` (`CategoryTheory.pi`). -/
def ZigZagProd : Type := ∀ n, ZigZag n

instance : SmallCategory ZigZagProd := CategoryTheory.pi fun n => ZigZag n

/-- **Folder 118, p. 36.** The product of the zigzags is not connected, although each is: the
objects whose coordinates are bounded form a union of components. -/
theorem not_isPreconnected_zigZagProd : ¬ IsPreconnected ZigZagProd := by
  intro _
  let B : ZigZagProd → Prop := fun x => ∃ N, ∀ n, Fin.val (n := n + 1) (x n) ≤ N
  have key := constant_of_preserves_morphisms B (fun x y f => propext
    ⟨fun ⟨N, hN⟩ => ⟨N + 1, fun n => by have := ZigZag.val_le_of_le (f n).le; have := hN n; omega⟩,
     fun ⟨N, hN⟩ => ⟨N + 1, fun n => by have := ZigZag.val_le_of_le (f n).le; have := hN n; omega⟩⟩)
    (fun n => (⟨0, by omega⟩ : Fin (n + 1))) (fun n => Fin.last n)
  obtain ⟨N, hN⟩ := key.mp ⟨0, fun n => le_rfl⟩
  have := hN (N + 1)
  simp [Fin.val_last] at this

/-- For a fundamental localizer whose aspherical categories are connected, the product of the
zigzags is not aspherical. -/
theorem not_isAspherical_zigZagProd {L : FundamentalLocalizer.{0}}
    (hL : L.AsphericalConnected) : ¬ L.IsAspherical ZigZagProd :=
  fun h => not_isPreconnected_zigZagProd (hL _ h).toIsPreconnected

end ZigZag

end LeanPool.ToposTheoreticBridges.Examples
