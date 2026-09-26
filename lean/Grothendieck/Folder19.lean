import Mathlib.CategoryTheory.Monad.Comonadicity
import Mathlib.CategoryTheory.Limits.Pi
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu

/-!
# Folder 19: the comonadicity theorem (page 4) and Gabriel–Popescu (pages 14–15)

Issue #26 lists folder 19 in tier 2: « Comonadicity and Gabriel–Popescu ». Only
those two statements of `transcripts/19/19.modern.tex` are formalised here.

## Théorème 1.12 (page 4)

> **Théorème.** Soit `f ⊣ g` une adjonction, `φ = fg`, et `h` le foncteur de
> comparaison.
> a) Si les noyaux de doubles flèches existent dans `A` et si `f` y commute,
>    alors `h` est essentiellement surjectif.
> b) `h` est une équivalence si et seulement si `f` est conservatif et si, pour
>    toute double flèche `(u,v)` de `A` telle que `Ker(f(u), f(v))` existe,
>    `Ker(u,v)` existe et `f` y commute.
>
> La restriction portée en marge — il suffit de considérer les doubles flèches
> `(u,v)` dont l'image par `f` a un noyau — est la condition que le manuscrit
> appelle *condition C*. [Footnote:] Les doubles flèches dont `f` voit le noyau
> sont, dans le vocabulaire d'aujourd'hui, les paires `f`-scindées.

`h` is mathlib's `Comonad.comparison adj`, and condition C is `ConditionC` below.

* `theoreme_a` — a), in the margin's weaker form (condition C instead of all
  equalizers), and `theoreme_a'` in the form of the text. True as stated.
* `theoreme_b_suffisance` — the « il suffit » of b). True as stated; it is an
  application of mathlib's Beck theorem
  `Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms`.
* `theoreme_b_necessite_fausse` — **the « il faut » of b) is false.** A
  comonadic `f` need not satisfy condition C. Counterexample, with `B = Bool → Type`
  (pairs of sets `(X, Y)`) and `A` the full subcategory of pairs with
  `Y ≠ ∅ ⇒ X ≠ ∅`: the inclusion `f` is coreflective (right adjoint
  `(X, Y) ↦ (X, Y if X ≠ ∅ else ∅)`), hence comonadic; but the pair
  `(*, *) ⇉ (Bool, *)` given by `x ↦ true` and `x ↦ false` has equalizer `(∅, *)`
  in `B`, which is not in `A`, so `f` does not commute with the equalizer taken
  in `A` (which is `(∅, ∅)`).
* `beck_iff` — the correct statement: `h` is an equivalence iff `f` is
  conservative and, for every **`f`-split** pair (one whose image has a *split*
  equalizer), `Ker(u,v)` exists and `f` commutes with it. From mathlib.

So the reading faithfully reproduces the manuscript (the transcription, page 4,
has « il faut et il suffit » and the margin's condition C), and the footnote's
gloss is where the error sits: a pair « dont `f` voit le noyau » is not an
`f`-split pair. Every `f`-split pair has an equalizer in `B`, so condition C is
*stronger* than Beck's condition: sufficient, not necessary. The same applies
to the « Conclusion » of pages 4–6 (adjunctions with `f` conservative and
condition C ↔ comonads): the comonads so obtained are only those whose forgetful
functor satisfies condition C, and the counterexample above is one that does not;
with Beck's condition in place of C the correspondence is right.

## Gabriel–Popescu (pages 14–15)

> Le foncteur `Hom_C(U, -) : C → Mod_R` est pleinement fidèle, et son adjoint à
> gauche `- ⊗_R U` est exact : c'est le théorème de Gabriel–Popescu.

(`C` a Grothendieck category, `U` a generator, `R = End_C(U)`, modules on the
right.) This is in mathlib (`IsGrothendieckAbelian.GabrielPopescu.full`,
`…preservesFiniteLimits`, and `isSeparator_iff_faithful_preadditiveCoyonedaObj`);
`gabriel_popescu` restates it in the reading's form. A generator is mathlib's
*separator*, and right `R`-modules are `ModuleCat Rᵐᵒᵖ`. The reading's further
claim — the functor is an equivalence iff `U` is moreover small projective
(Morita) — and the manuscript's original claim of an equivalence for a bare
generator are not formalised here.

What this certifies is that the reading holds together, not that it is what the
pages say (issue #26).
-/

namespace Grothendieck.Folder19

open CategoryTheory Limits

universe v u₁ u₂

section Comonadicite

variable {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
variable {f : A ⥤ B} {g : B ⥤ A} (adj : f ⊣ g)

/-- **Condition C** (margin of page 4): for every pair `(u, v)` of `A` such that
`Ker(f u, f v)` exists, `Ker(u, v)` exists and `f` commutes with it. -/
def ConditionC (f : A ⥤ B) : Prop :=
  ∀ ⦃X Y : A⦄ (u v : X ⟶ Y), HasEqualizer (f.map u) (f.map v) →
    HasEqualizer u v ∧ PreservesLimit (parallelPair u v) f

open Comonad ComonadicityInternal in
/-- **Théorème 1.12 a)**, in the margin's form: under condition C the comparison
functor `h : A → φ-Coalg` is essentially surjective. -/
theorem theoreme_a (hC : ConditionC f) : (Comonad.comparison adj).EssSurj := by
  have hE : ∀ X : adj.toComonad.Coalgebra,
      HasEqualizer (g.map X.a) (adj.unit.app (g.obj X.A)) := fun X =>
    (hC _ _ inferInstance).1
  have hP : ∀ X : adj.toComonad.Coalgebra,
      PreservesLimit (parallelPair (g.map X.a) (adj.unit.app (g.obj X.A))) f := fun X =>
    (hC _ _ inferInstance).2
  have : ∀ X : Coalgebra adj.toComonad, IsIso ((comparisonAdjunction adj).counit.app X) := by
    intro X
    apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Comonad.forget adj.toComonad) ?_ _
    change IsIso ((comparisonAdjunction adj).counit.app X).f
    rw [comparisonAdjunction_counit_f]
    change IsIso (IsLimit.conePointUniqueUpToIso (beckEqualizer X)
      (counitLimitOfPreservesEqualizer X)).inv
    exact (IsLimit.conePointUniqueUpToIso _ _).isIso_inv
  exact ⟨fun X => ⟨_, ⟨asIso ((comparisonAdjunction adj).counit.app X)⟩⟩⟩

/-- **Théorème 1.12 a)**, as the text states it: if the equalizers of pairs exist
in `A` and `f` commutes with them, `h` is essentially surjective. -/
theorem theoreme_a' [HasEqualizers A] [PreservesLimitsOfShape WalkingParallelPair f] :
    (Comonad.comparison adj).EssSurj :=
  theoreme_a adj fun _ _ _ _ _ => ⟨inferInstance, inferInstance⟩

/-- **Théorème 1.12 b), sufficiency.** If `f` is conservative and satisfies
condition C, the comparison functor is an equivalence. -/
theorem theoreme_b_suffisance [f.ReflectsIsomorphisms] (hC : ConditionC f) :
    (Comonad.comparison adj).IsEquivalence := by
  have : Comonad.HasEqualizerOfIsCosplitPair f := ⟨fun u v _ => (hC u v inferInstance).1⟩
  have : Comonad.PreservesLimitOfIsCosplitPair f := ⟨fun u v _ => (hC u v inferInstance).2⟩
  exact (Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms adj).eqv

/-- **Beck's theorem, precise form** (the necessary and sufficient condition the
reading's b) should carry): the comparison functor is an equivalence iff `f` is
conservative and, for every `f`-split pair `(u, v)` — one whose image has a
*split* equalizer — `Ker(u, v)` exists and `f` commutes with it. -/
theorem beck_iff : (Comonad.comparison adj).IsEquivalence ↔
    f.ReflectsIsomorphisms ∧ ∀ ⦃X Y : A⦄ (u v : X ⟶ Y), f.IsCosplitPair u v →
      HasEqualizer u v ∧ PreservesLimit (parallelPair u v) f := by
  constructor
  · intro h
    let _ : ComonadicLeftAdjoint f := ⟨g, adj, h⟩
    refine ⟨⟨fun {X Y} φ hφ => ?_⟩, fun X Y u v _ => ?_⟩
    · have : IsIso ((Comonad.comparison adj).map φ) := by
        have : IsIso ((Comonad.forget adj.toComonad).map ((Comonad.comparison adj).map φ)) := hφ
        exact isIso_of_reflects_iso _ (Comonad.forget adj.toComonad)
      exact isIso_of_fully_faithful (Comonad.comparison adj) φ
    have := Comonad.createsFSplitEqualizersOfComonadic (F := f) u v
    have : HasLimit (parallelPair u v ⋙ f) := by
      rw [hasLimit_iff_of_iso (diagramIsoParallelPair _)]
      exact inferInstanceAs <| HasEqualizer (f.map u) (f.map v)
    have : HasEqualizer u v := hasLimit_of_created (parallelPair u v) f
    exact ⟨this, inferInstance⟩
  · rintro ⟨_, hC⟩
    have : Comonad.HasEqualizerOfIsCosplitPair f := ⟨fun u v _ => (hC u v inferInstance).1⟩
    have : Comonad.PreservesLimitOfIsCosplitPair f := ⟨fun u v _ => (hC u v inferInstance).2⟩
    exact (Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms adj).eqv

end Comonadicite

section ContreExemple

/-- An object `(X, Y)` of `Bool → Type`: `X` at `true`, `Y` at `false`. -/
def mkObj (X Y : Type) : Bool → Type
  | true => X
  | false => Y

/-- Pairs `(X, Y)` with `Y → Nonempty X`: if `Y` is inhabited, so is `X`. -/
def P : ObjectProperty (Bool → Type) := fun Z => Z false → Nonempty (Z true)

/-- The coreflection `(X, Y) ↦ (X, {y : Y // Nonempty X})`. -/
def Robj (Z : Bool → Type) : P.FullSubcategory :=
  ⟨mkObj (Z true) {_y : Z false // Nonempty (Z true)}, fun y => y.2⟩

/-- The hom-set bijection of the coreflection. -/
def e (X : P.FullSubcategory) (Z : Bool → Type) : (P.ι.obj X ⟶ Z) ≃ (X ⟶ Robj Z) where
  toFun φ := P.homMk fun b => match b with
    | true => φ true
    | false => TypeCat.ofHom fun q => ⟨φ false q, (X.property q).map (φ true)⟩
  invFun ψ := fun b => match b with
    | true => ψ.hom true
    | false => ψ.hom false ≫ TypeCat.ofHom Subtype.val
  left_inv φ := by
    funext b; cases b <;> rfl
  right_inv ψ := by
    apply ObjectProperty.hom_ext; funext b; cases b <;> rfl

/-- `P ↪ (Bool → Type)` is left adjoint to `(X, Y) ↦ (X, {y : Y // Nonempty X})`. -/
def adjP : P.ι ⊣ Adjunction.rightAdjointOfEquiv e (by
    intro X' X Y f g; apply ObjectProperty.hom_ext; funext b; cases b <;> rfl) :=
  Adjunction.adjunctionOfEquivRight _ _

/-- The inclusion of `P` is coreflective. -/
instance : Coreflective P.ι where
  R := _
  adj := adjP

/-- The inclusion `P ↪ (Bool → Type)` is comonadic (it is coreflective). -/
theorem comonadique : (Comonad.comparison adjP).IsEquivalence :=
  (comonadicOfCoreflective (R := P.ι)).eqv

/-- `(*, *)` -/
def S0 : P.FullSubcategory := ⟨mkObj PUnit PUnit, fun _ => ⟨PUnit.unit⟩⟩
/-- `(Bool, *)` -/
def T0 : P.FullSubcategory := ⟨mkObj Bool PUnit, fun _ => ⟨true⟩⟩
/-- `((↦ true), id)` -/
def u0 : S0 ⟶ T0 := P.homMk fun b => match b with
  | true => TypeCat.ofHom fun _ => true
  | false => 𝟙 _
/-- `((↦ false), id)` -/
def v0 : S0 ⟶ T0 := P.homMk fun b => match b with
  | true => TypeCat.ofHom fun _ => false
  | false => 𝟙 _

/-- The inclusion `P ↪ (Bool → Type)` does **not** satisfy condition C: for
`u, v : (*, *) ⇉ (Bool, *)`, `(u, v) = ((↦ true), id), ((↦ false), id)`, the
equalizer of `f u, f v` in `Bool → Type` is `(∅, *)`; an equalizer in `P`, if
`f` commuted with it, would have `*` on its `false` side, hence (being in `P`) a
point on its `true` side — which `u` and `v` send to `true ≠ false`. -/
theorem non_conditionC : ¬ ConditionC P.ι := by
  intro hC
  have : HasEqualizer (P.ι.map u0) (P.ι.map v0) := pi.hasLimit_of_hasLimit_comp_eval
  obtain ⟨_, _⟩ := hC u0 v0 this
  -- the fork `(∅, *) → (*, *)` of `Bool → Type`
  let K : Fork (P.ι.map u0) (P.ι.map v0) := Fork.ofι (P := mkObj PEmpty PUnit)
    (fun b => match b with
      | true => TypeCat.ofHom PEmpty.elim
      | false => 𝟙 _) (by
        funext b; cases b
        · rfl
        · ext x; cases x)
  let l := (isLimitOfHasEqualizerOfPreservesLimit P.ι u0 v0).lift K
  obtain ⟨x⟩ := (equalizer u0 v0).property (l false PUnit.unit)
  have h := congrArg (fun φ : equalizer u0 v0 ⟶ T0 => (φ.hom true) x) (equalizer.condition u0 v0)
  have h' : true = false := h
  exact Bool.noConfusion h'

/-- **Théorème 1.12 b), necessity: false as stated.** Here is an adjunction
`f ⊣ g` whose comparison functor is an equivalence, and yet `f` does not satisfy
condition C. The correct necessary condition is the one of `beck_iff`, on
`f`-split pairs only. -/
theorem theoreme_b_necessite_fausse :
    (Comonad.comparison adjP).IsEquivalence ∧ ¬ ConditionC P.ι :=
  ⟨comonadique, non_conditionC⟩

end ContreExemple

section GabrielPopescu

/-- **Pages 14–15, as corrected by the reading.** Let `C` be a Grothendieck
category with a generator `U` (mathlib: a *separator*), `R = End(U)`. Then
`Hom_C(U, -) : C → Mod_R` (right `R`-modules, i.e. modules over `Rᵐᵒᵖ`) is fully
faithful, and its left adjoint `- ⊗_R U` is exact. This is mathlib's
Gabriel–Popescu theorem. -/
theorem gabriel_popescu {C : Type u₁} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] (U : C) (hU : IsSeparator U) :
    (preadditiveCoyonedaObj U).Full ∧ (preadditiveCoyonedaObj U).Faithful ∧
      PreservesFiniteLimits (IsGrothendieckAbelian.tensorObj U) ∧
      PreservesFiniteColimits (IsGrothendieckAbelian.tensorObj U) :=
  ⟨IsGrothendieckAbelian.GabrielPopescu.full U hU,
    (isSeparator_iff_faithful_preadditiveCoyonedaObj U).1 hU,
    IsGrothendieckAbelian.GabrielPopescu.preservesFiniteLimits U hU, inferInstance⟩

end GabrielPopescu

end Grothendieck.Folder19
