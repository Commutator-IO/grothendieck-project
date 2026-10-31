import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Whiskering

/-!
# Bourbaki, rédaction n° 448 (Chevalley, 1965), Remark p. 20: free objects over a diagram

Rédaction 448, « Foncteurs adjoints. Limites », considers a functor `F : Y ⥤ X`, a diagram
`D : I ⥤ X` and the functor `F_* : (I ⥤ Y) ⥤ (I ⥤ X)` of composition with `F`. The corollary
to its Proposition 4 says that if `(E, φ)` is a free (resp. cofree) object over `D` relative to
`F_*`, and if every `D(i)` has a free (resp. cofree) object over it relative to `F`, then each
`(E(i), φ(i))` is free (resp. cofree) over `D(i)`: free objects over a diagram are computed
pointwise. The Remark of p. 20 asks whether the hypothesis on the `D(i)` can be dropped, and
leaves the question as an exercise for the congress.

The answer is no. Take for `Y` the category with one object and one arrow, `X = Type`, `F`
the functor picking a one-point type, `I` the walking arrow `0 → 1` (here `Fin 2`, as
`ComposableArrows Type 1`) and `D` the map from a point to `Bool` with value `true`.
A cofree object over a diagram `G` relative to `F_*` is a family of points of `G` compatible
with the arrows, unique; for `D` there is exactly one, since the point `D(0)` fixes it. A cofree
object over `Bool` relative to `F` would be a unique point of `Bool`, and there are two. So
`D` has a cofree object relative to `F_*`, whose value at `1` is not cofree over `D(1)`.
Reversing the arrows of `Type` gives the same failure for free objects, which is the case the
Remark states.

This is a special case of the folklore that limits in a functor category need not be computed
pointwise when the target lacks them (nLab, *functor category*): with `Y` the terminal category,
a cofree object over `D` relative to `F_*` is a limit of a diagram built from `D`. The
counterexample above is for a general `F_*`, as in the rédaction.

Cofree objects over `T` relative to `S` are the terminal objects of Mathlib's
`CostructuredArrow S T`, free objects the initial objects of `StructuredArrow T S`.

**What is proved.**
* `evalCostructuredArrow`, `evalStructuredArrow`: the value `(E(i), φ(i))` at `i` of an object
  `(E, φ)` over `D` relative to `F_*`.
* `isTerminalCofree`: the costructured arrow `cofree` is cofree over `D` relative to `F_*`.
* `isEmpty_isTerminal_one`: there is no cofree object over `D(1)` relative to `F`.
* `cofree_not_pointwise`: **the answer to the Remark, rédaction n° 448, p. 20, for cofree
  objects.** Some diagram has a cofree object relative to `F_*` whose value at `1` is not cofree
  over `D(1)`; in fact no cofree object over `D` has a cofree value at `1`.
* `isInitialFree`, `isEmpty_isInitial_zero`, `free_not_pointwise`: the same for free objects,
  with `X = Typeᵒᵖ` and the value at `0`.

**Not formalised.** The corollary to Proposition 4 itself (the pointwise statement under the
hypothesis on the `D(i)`).
-/

namespace Grothendieck.Bourbaki448

open CategoryTheory Limits Functor Opposite

section Eval

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
  {I : Type u₃} [Category.{v₃} I] {F : Y ⥤ X} {D : I ⥤ X}

/-- The value at `i` of an object `(E, φ : F_* E ⟶ D)` over `D` relative to `F_*`: the object
`(E(i), φ(i))` over `D(i)` relative to `F`. -/
abbrev evalCostructuredArrow (E : CostructuredArrow ((whiskeringRight I Y X).obj F) D) (i : I) :
    CostructuredArrow F (D.obj i) :=
  CostructuredArrow.mk (E.hom.app i)

/-- The value at `i` of an object `(E, φ : D ⟶ F_* E)` under `D` relative to `F_*`: the object
`(E(i), φ(i))` under `D(i)` relative to `F`. -/
abbrev evalStructuredArrow (E : StructuredArrow D ((whiskeringRight I Y X).obj F)) (i : I) :
    StructuredArrow (D.obj i) F :=
  StructuredArrow.mk (E.hom.app i)

end Eval

/-- Natural transformations between functors to the category with one object and one arrow are
all equal. -/
instance {I : Type} [Category I] (A B : I ⥤ Discrete PUnit.{1}) : Subsingleton (A ⟶ B) :=
  ⟨fun _ _ => by ext; exact Subsingleton.elim _ _⟩

/-- The natural transformation between two functors to the category with one object. -/
def toPUnit {I : Type} [Category I] (A B : I ⥤ Discrete PUnit.{1}) : A ⟶ B where
  app _ := Discrete.eqToHom (Subsingleton.elim _ _)
  naturality _ _ _ := Subsingleton.elim _ _

section Cofree

/-- The functor from the category with one object to `Type` picking a one-point type. -/
abbrev pt : Discrete PUnit.{1} ⥤ Type := (Functor.const _).obj PUnit.{1}

/-- The map from a point to `Bool` with value `true`. -/
def toTrue : PUnit.{1} ⟶ Bool := TypeCat.ofHom fun _ => true

/-- The diagram `D`: the walking arrow `0 → 1` sent to the map from a point to `Bool`. -/
abbrev D : Fin 2 ⥤ Type := ComposableArrows.mk₁ toTrue

/-- Every natural transformation `F_* E ⟶ D` has value `true` at `1`. -/
theorem app_one_apply (E : Fin 2 ⥤ Discrete PUnit.{1})
    (α : ((whiskeringRight (Fin 2) _ Type).obj pt).obj E ⟶ D) (x : PUnit.{1}) :
    α.app 1 x = true := by
  have h := α.naturality (homOfLE (by decide : (0 : Fin 2) ≤ 1))
  have h' := congrArg (fun f => f x) h
  simpa [toTrue] using h'

/-- There is at most one natural transformation `F_* E ⟶ D`. -/
theorem hom_ext_D (E : Fin 2 ⥤ Discrete PUnit.{1})
    (α β : ((whiskeringRight (Fin 2) _ Type).obj pt).obj E ⟶ D) : α = β := by
  refine NatTrans.ext (funext fun i => ?_)
  fin_cases i
  · ext x
    exact Subsingleton.elim (α := PUnit.{1}) _ _
  · ext x
    exact (app_one_apply E α x).trans (app_one_apply E β x).symm

/-- The cofree object over `D` relative to `F_*`: the constant functor, with the identity of the
point at `0` and `toTrue` at `1`. -/
def cofree : CostructuredArrow ((whiskeringRight (Fin 2) _ Type).obj pt) D :=
  CostructuredArrow.mk (Y := (Functor.const (Fin 2)).obj ⟨PUnit.unit⟩)
    (ComposableArrows.homMk₁ (𝟙 PUnit.{1}) toTrue (by ext; rfl))

/-- `cofree` is cofree over `D` relative to `F_*`, that is, terminal among the objects over
`D`. -/
def isTerminalCofree : IsTerminal cofree :=
  IsTerminal.ofUniqueHom
    (fun _ => CostructuredArrow.homMk (toPUnit _ _) (hom_ext_D _ _ _))
    (fun _ _ => CostructuredArrow.hom_ext _ _ (Subsingleton.elim _ _))

/-- There is no cofree object over `D(1) = Bool` relative to `F`: two maps from a point to
`Bool` would both factor through it. -/
theorem isEmpty_isTerminal_one (Z : CostructuredArrow pt (D.obj 1)) : IsEmpty (IsTerminal Z) := by
  refine ⟨fun h => ?_⟩
  have key : ∀ b : Bool, Z.hom PUnit.unit = b := fun b => by
    let W : CostructuredArrow pt (D.obj 1) :=
      CostructuredArrow.mk (Y := ⟨PUnit.unit⟩) (TypeCat.ofHom fun _ : PUnit.{1} => b)
    have hw := congrArg (fun f => f PUnit.unit) (CostructuredArrow.w (h.from W))
    simpa [W] using hw
  exact Bool.false_ne_true ((key false).symm.trans (key true))

/-- **The answer to the Remark, rédaction n° 448, p. 20, for cofree objects.** There is a cofree
object over `D` relative to `F_*`, and none has a value at `1` that is cofree over `D(1)`
relative to `F`. -/
theorem cofree_not_pointwise :
    Nonempty (IsTerminal cofree) ∧
      ∀ E : CostructuredArrow ((whiskeringRight (Fin 2) _ Type).obj pt) D,
        IsEmpty (IsTerminal (evalCostructuredArrow E 1)) :=
  ⟨⟨isTerminalCofree⟩, fun _ => isEmpty_isTerminal_one _⟩

end Cofree

section Free

/-- The functor from the category with one object to `Typeᵒᵖ` picking a one-point type. -/
abbrev ptOp : Discrete PUnit.{1} ⥤ Typeᵒᵖ := (Functor.const _).obj (op PUnit.{1})

/-- The diagram `D'` in `Typeᵒᵖ`: the walking arrow `0 → 1` sent to the opposite of the map from
a point to `Bool`, so that `D'(0) = Bool` and `D'(1)` is a point. -/
abbrev D' : Fin 2 ⥤ Typeᵒᵖ := ComposableArrows.mk₁ toTrue.op

/-- Every natural transformation `D' ⟶ F_* E` has value `true` at `0`. -/
theorem app_zero_unop_apply (E : Fin 2 ⥤ Discrete PUnit.{1})
    (α : D' ⟶ ((whiskeringRight (Fin 2) _ Typeᵒᵖ).obj ptOp).obj E) (x : PUnit.{1}) :
    (α.app 0).unop x = true := by
  have h := congrArg Quiver.Hom.unop (α.naturality (homOfLE (by decide : (0 : Fin 2) ≤ 1)))
  have h' := congrArg (fun f => f x) h
  simpa [toTrue] using h'.symm

/-- There is at most one natural transformation `D' ⟶ F_* E`. -/
theorem hom_ext_D' (E : Fin 2 ⥤ Discrete PUnit.{1})
    (α β : D' ⟶ ((whiskeringRight (Fin 2) _ Typeᵒᵖ).obj ptOp).obj E) : α = β := by
  refine NatTrans.ext (funext fun i => Quiver.Hom.unop_inj ?_)
  fin_cases i
  · ext x
    exact (app_zero_unop_apply E α x).trans (app_zero_unop_apply E β x).symm
  · ext x
    exact Subsingleton.elim (α := PUnit.{1}) _ _

/-- The free object over `D'` relative to `F_*`: the constant functor, with `toTrue` at `0` and
the identity of the point at `1`. -/
def free : StructuredArrow D' ((whiskeringRight (Fin 2) _ Typeᵒᵖ).obj ptOp) :=
  StructuredArrow.mk (Y := (Functor.const (Fin 2)).obj ⟨PUnit.unit⟩)
    (ComposableArrows.homMk₁ toTrue.op (𝟙 (op PUnit.{1})) (by simp))

/-- `free` is free over `D'` relative to `F_*`, that is, initial among the objects under `D'`. -/
def isInitialFree : IsInitial free :=
  IsInitial.ofUniqueHom
    (fun _ => StructuredArrow.homMk (toPUnit _ _) (hom_ext_D' _ _ _))
    (fun _ _ => StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _))

/-- There is no free object over `D'(0) = Bool` relative to `F` in `Typeᵒᵖ`: two maps from a
point to `Bool` would both factor through it. -/
theorem isEmpty_isInitial_zero (Z : StructuredArrow (D'.obj 0) ptOp) :
    IsEmpty (IsInitial Z) := by
  refine ⟨fun h => ?_⟩
  have key : ∀ b : Bool, Z.hom.unop PUnit.unit = b := fun b => by
    let W : StructuredArrow (D'.obj 0) ptOp :=
      StructuredArrow.mk (Y := ⟨PUnit.unit⟩) (TypeCat.ofHom fun _ : PUnit.{1} => b).op
    have hw := congrArg (fun f => f.unop PUnit.unit) (StructuredArrow.w (h.to W))
    simpa [W] using hw
  exact Bool.false_ne_true ((key false).symm.trans (key true))

/-- **The answer to the Remark, rédaction n° 448, p. 20, for free objects.** There is a free
object over `D'` relative to `F_*`, and none has a value at `0` that is free over `D'(0)`
relative to `F`. -/
theorem free_not_pointwise :
    Nonempty (IsInitial free) ∧
      ∀ E : StructuredArrow D' ((whiskeringRight (Fin 2) _ Typeᵒᵖ).obj ptOp),
        IsEmpty (IsInitial (evalStructuredArrow E 0)) :=
  ⟨⟨isInitialFree⟩, fun _ => isEmpty_isInitial_zero _⟩

end Free

end Grothendieck.Bourbaki448
