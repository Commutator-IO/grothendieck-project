import Mathlib.CategoryTheory.Monad.Comonadicity
import Mathlib.CategoryTheory.Limits.Pi
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Folder 19: the comonadicity theorem (page 4), the comonad over a product base
# (pages 7–11) and Gabriel–Popescu (pages 14–15)

Issue #26 lists folder 19 in tier 2: « Comonadicity and Gabriel–Popescu ». Those
two statements of `transcripts/19/19.modern.tex` are formalised here, and the
finding `19-comonad-matrix-product-base` (pages 7–11).

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

## A product base: the matrix of the `φ_ji` (pages 7–11)

> Le reste du texte examine ce que devient tout ceci quand `B = ∏_{i ∈ I} B_i`. […]
> En posant `φ_ji = f_j g_i : B_i → B_j` et en supposant que les `f_j` commutent
> aux produits indexés par `I` — ce qui est automatique si `I` est fini, ou si les
> `f_j` sont exacts — on obtient `pr_j φ((X_i)) = ∏_i φ_ji(X_i)`. […] une famille
> `λ_kji : φ_ki → φ_kj φ_ji`, obtenue en insérant l'unité `id → g_j f_j` au milieu.
> […] pour `i = j = k` on retrouve la comultiplication de `φ_i`, et les cas où
> deux des trois indices coïncident sont dégénérés. […] Deux facteurs, `g'`, `g''`
> pleinement fidèles : deux foncteurs croisés `φ' : B'' → B'`, `φ'' : B' → B''`,
> deux flèches `λ' : id → φ'φ''`, `λ'' : id → φ''φ'`, avec
> `φ(X', X'') = (X' × φ'(X''), φ''(X') × X'')`.

Setting: adjunctions `f_i ⊣ g_i`, `f_i : A → B_i`, and `A` with `I`-indexed products.
* `adjPi` — (3.4): `f = (f_i) ⊣ g`, `g((X_i)) = ∏ g_i(X_i)`.
* `matrice` — (3.6): if `f_j` commutes with `I`-indexed products, `pr_j φ((X_i))` is
  the product of the `φ_ji(X_i)`, with projections `f_j(pr_i)`. True as stated.
* `counit_matrice`, `comult_matrice` — (3.9): `ᾱ_k = α_k(X_k) ∘ pr_k` and
  `λ̄_kji = λ_kji(X_i) ∘ pr_i`; no hypothesis needed. `comult_unique`: under the
  hypothesis of `matrice`, these entries determine the comultiplication.
* `lam_diag` — the margin of page 8: `λ_iii` is the comultiplication of `φ_i`.
* `lam_isIso_left`, `lam_isIso_right` — the degenerate cases: if the `g` are fully
  faithful, `λ_kki` and `λ_kjj` are isomorphisms.
* `lamUnit`, `lam_eq_counit_comp_lamUnit` — (3.11 b), (3.14): `λ_iji` is the unit
  `λ' : id → φ_ij φ_ji` after the isomorphism `φ_ii ≅ id`.
* `deuxFacteurs_left`, `deuxFacteurs_right` — (3.12)–(3.14) for `I = WalkingPair`:
  `pr' φ(X', X'') = X' × φ'(X'')` and `pr'' φ(X', X'') = φ''(X') × X''`.
* `matrice_fini_fausse` — **« ou I fini » is false**: a left adjoint need not
  commute with finite products. With `I = Bool`, `A = B_i = Type`,
  `f_i = Bool × -` (left adjoint to `Bool → -`), `X_i = *`: `pr_j φ(X)` has two
  elements and `∏_i φ_ji(X_i)` four. The phrase is on the page (« p. ex. `f_j`
  exacts ; ou `I` fini », transcription page 7); the exactness alternative is right.

The coassociativity relations between the `λ_kji`, which the page does not write,
and the description of `A` by quadruples `(X', X'', u', u'')` (pages 9–10), are not
formalised.

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

universe w v u₁ u₂

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

section BaseProduit

variable {I : Type w} {A : Type u₁} [Category.{v} A] {B : I → Type u₂} [∀ i, Category.{v} (B i)]
variable (f : ∀ i, A ⥤ B i) (g : ∀ i, B i ⥤ A) (adj : ∀ i, f i ⊣ g i)

/-- (3.4) The right adjoint over the product base, `g((Xᵢ)) = ∏ᵢ gᵢ(Xᵢ)`. -/
noncomputable abbrev gPi [HasProductsOfShape I A] : (∀ i, B i) ⥤ A where
  obj X := ∏ᶜ fun i => (g i).obj (X i)
  map φ := Limits.Pi.map fun i => (g i).map (φ i)

variable [HasProductsOfShape I A]

/-- (3.4) `f = (fᵢ) : A → ∏ Bᵢ` is left adjoint to `g = ∏ gᵢ`. -/
noncomputable def adjPi : Functor.pi' f ⊣ gPi g := Adjunction.mkOfHomEquiv
  { homEquiv := fun Y X =>
      { toFun := fun φ => Limits.Pi.lift fun i => (adj i).homEquiv _ _ (φ i)
        invFun := fun ψ i => ((adj i).homEquiv _ _).symm (ψ ≫ Limits.Pi.π _ i)
        left_inv := fun φ => by
          funext i
          simp only [Limits.Pi.lift_π]
          exact Equiv.symm_apply_apply _ _
        right_inv := fun ψ => by
          refine Limits.Pi.hom_ext _ _ fun i => ?_
          simp only [Limits.Pi.lift_π]
          exact Equiv.apply_symm_apply _ _ }
    homEquiv_naturality_left_symm := fun h ψ => by
      funext i
      change ((adj i).homEquiv _ _).symm ((h ≫ ψ) ≫ Limits.Pi.π _ i) =
        (f i).map h ≫ ((adj i).homEquiv _ _).symm (ψ ≫ Limits.Pi.π _ i)
      rw [Category.assoc]
      exact (adj i).homEquiv_naturality_left_symm _ _
    homEquiv_naturality_right := fun φ ψ => by
      refine Limits.Pi.hom_ext _ _ fun i => ?_
      change (Limits.Pi.lift fun i => (adj i).homEquiv _ _ ((φ ≫ ψ) i)) ≫ Limits.Pi.π _ i =
        ((Limits.Pi.lift fun i => (adj i).homEquiv _ _ (φ i)) ≫
          Limits.Pi.map (fun i => (g i).map (ψ i))) ≫ Limits.Pi.π _ i
      rw [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_π, Limits.Pi.lift_π_assoc]
      exact (adj i).homEquiv_naturality_right _ _ }

@[reassoc (attr := simp)]
theorem adjPi_unit_π (Y : A) (j : I) :
    (adjPi f g adj).unit.app Y ≫ Limits.Pi.π _ j = (adj j).unit.app Y := by
  change (Limits.Pi.lift fun i => (adj i).homEquiv _ _ (𝟙 ((f i).obj Y))) ≫ Limits.Pi.π _ j = _
  rw [Limits.Pi.lift_π]
  exact (adj j).homEquiv_id Y

theorem adjPi_counit (X : ∀ i, B i) (j : I) :
    (adjPi f g adj).counit.app X j =
      (f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) j) ≫ (adj j).counit.app (X j) := by
  change ((adj j).homEquiv ((gPi g).obj X) (X j)).symm
    (𝟙 ((gPi g).obj X) ≫ Limits.Pi.π (fun i => (g i).obj (X i)) j) = _
  rw [Category.id_comp]
  exact (adj j).homEquiv_counit _ _ _

/-- (3.6) The entry `φ_ji = f_j g_i : B_i → B_j` of the matrix. -/
abbrev phi (j i : I) : B i ⥤ B j := g i ⋙ f j

/-- (3.10) `λ_kji : φ_ki → φ_kj φ_ji`, the unit `id → g_j f_j` inserted in the middle of
`f_k g_i`. -/
@[simps]
def lam (k j i : I) : phi f g k i ⟶ phi f g j i ⋙ phi f g k j where
  app X := (f k).map ((adj j).unit.app ((g i).obj X))
  naturality X Y h := by
    simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp]
    congr 1
    exact (adj j).unit.naturality ((g i).map h)

/-- (3.5)–(3.6) **The matrix.** If `f_j` commutes with `I`-indexed products, the
`j`-th component of `φ((Xᵢ))` is the product of the `φ_ji(Xᵢ)`, with projections
`f_j(prᵢ)`. -/
noncomputable def matrice (X : ∀ i, B i) (j : I) [PreservesLimitsOfShape (Discrete I) (f j)] :
    IsLimit (Fan.mk ((adjPi f g adj).toComonad.obj X j)
      fun i => (f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)) :=
  (isLimitMapConeFanMkEquiv (f j) _ _) (isLimitOfPreserves (f j) (productIsProduct _))

/-- (3.9), first line: the counit of `φ` is diagonal, `ᾱ_k = α_k(X_k) ∘ pr_k`. -/
theorem counit_matrice (X : ∀ i, B i) (k : I) :
    (adjPi f g adj).toComonad.ε.app X k =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) k) ≫ (adj k).counit.app (X k) :=
  adjPi_counit f g adj X k

/-- (3.9), second line: the `(k, j, i)` entry of the comultiplication of `φ` is
`λ̄_kji = λ_kji(Xᵢ) ∘ prᵢ`. -/
theorem comult_matrice (X : ∀ i, B i) (k j i : I) :
    (adjPi f g adj).toComonad.δ.app X k ≫
        (f k).map (Limits.Pi.π _ j ≫ (g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i))) =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) i) ≫ (lam f g adj k j i).app (X i) := by
  have h1 := adjPi_unit_π_assoc f g adj ((gPi g).obj X) j
    ((g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))
  have h2 := (adj j).unit.naturality (Limits.Pi.π (fun i => (g i).obj (X i)) i)
  have h3 := congrArg (f k).map (h1.trans h2.symm)
  exact (((f k).map_comp _ _).symm.trans h3).trans ((f k).map_comp _ _)

/-- **The comultiplication is the family `λ_kji`.** If the `f_j` commute with
`I`-indexed products, a morphism `(φX)_k → (φ²X)_k` with the entries `λ̄_kji` of
`comult_matrice` is the `k`-th component of the comultiplication. -/
theorem comult_unique [∀ j, PreservesLimitsOfShape (Discrete I) (f j)] (X : ∀ i, B i) (k : I)
    (t : (adjPi f g adj).toComonad.obj X k ⟶
      ((adjPi f g adj).toComonad.obj ((adjPi f g adj).toComonad.obj X)) k)
    (ht : ∀ j i, t ≫
        (f k).map (Limits.Pi.π _ j ≫ (g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i))) =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) i) ≫ (lam f g adj k j i).app (X i)) :
    t = (adjPi f g adj).toComonad.δ.app X k := by
  have hk := (isLimitMapConeFanMkEquiv (f k) _ _)
    (isLimitOfPreserves (f k) (productIsProduct
      (fun j => (g j).obj ((f j).obj ((gPi g).obj X)))))
  refine Fan.IsLimit.hom_ext hk _ _ fun j => ?_
  have : PreservesLimitsOfShape (Discrete I) (g j) := (adj j).rightAdjoint_preservesLimits.1
  have hj := (isLimitMapConeFanMkEquiv (f j ⋙ g j ⋙ f k) _ _)
    (isLimitOfPreserves (f j ⋙ g j ⋙ f k) (productIsProduct (fun i => (g i).obj (X i))))
  refine Fan.IsLimit.hom_ext hj _ _ fun i => ?_
  have e := (ht j i).trans (comult_matrice f g adj X k j i).symm
  have e' : t ≫ ((f k).map (Limits.Pi.π
        (fun j => (g j).obj ((f j).obj ((gPi g).obj X))) j) ≫
        (f k).map ((g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))) =
      (adjPi f g adj).toComonad.δ.app X k ≫ ((f k).map (Limits.Pi.π
        (fun j => (g j).obj ((f j).obj ((gPi g).obj X))) j) ≫
        (f k).map ((g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))) := by
    exact (congrArg (t ≫ ·) ((f k).map_comp _ _).symm).trans
      (e.trans (congrArg (_ ≫ ·) ((f k).map_comp _ _)))
  exact (Category.assoc _ _ _).trans (e'.trans (Category.assoc _ _ _).symm)

omit [HasProductsOfShape I A] in
/-- Marginal note of page 8: for `i = j = k`, `λ_kji` is the comultiplication `λ_i`
of the comonad `φ_i = f_i g_i`. -/
theorem lam_diag (i : I) : lam f g adj i i i = (adj i).toComonad.δ := by
  ext X
  rfl

section PleinementFideles

omit [HasProductsOfShape I A] in
/-- If `g_i` is fully faithful, the diagonal entry `φ_ii = f_i g_i` is the identity
(through the counit). -/
noncomputable def diagIso (i : I) [(g i).Full] [(g i).Faithful] : phi f g i i ≅ 𝟭 (B i) :=
  asIso (adj i).counit

omit [HasProductsOfShape I A] in
/-- Pages 8–9, the degenerate cases `k = j`: if `g_k` is fully faithful,
`λ_kki : φ_ki → φ_kk φ_ki` is an isomorphism. -/
theorem lam_isIso_left (k i : I) [(g k).Full] [(g k).Faithful] :
    IsIso (lam f g adj k k i) := by
  have : ∀ X, IsIso ((lam f g adj k k i).app X) := fun X =>
    NatIso.isIso_app_of_isIso (Functor.whiskerRight (adj k).unit (f k)) ((g i).obj X)
  exact NatIso.isIso_of_isIso_app _

omit [HasProductsOfShape I A] in
/-- Pages 8–9, the degenerate cases `j = i`: if `g_j` is fully faithful,
`λ_kjj : φ_kj → φ_kj φ_jj` is an isomorphism. -/
theorem lam_isIso_right (k j : I) [(g j).Full] [(g j).Faithful] :
    IsIso (lam f g adj k j j) := by
  have : ∀ X, IsIso ((lam f g adj k j j).app X) := fun X => by
    have := NatIso.isIso_app_of_isIso (Functor.whiskerLeft (g j) (adj j).unit) X
    exact Functor.map_isIso (f k) ((adj j).unit.app ((g j).obj X))
  exact NatIso.isIso_of_isIso_app _

omit [HasProductsOfShape I A] in
/-- (3.11 b), (3.14) The unit `λ' : id_{B_i} → φ_ij φ_ji` (`i ≠ j`) when `g_i` is
fully faithful: `λ_iji` read through `φ_ii ≅ id`. -/
noncomputable def lamUnit (i j : I) [(g i).Full] [(g i).Faithful] :
    𝟭 (B i) ⟶ phi f g j i ⋙ phi f g i j :=
  (diagIso f g adj i).inv ≫ lam f g adj i j i

omit [HasProductsOfShape I A] in
/-- `λ_iji = λ' ∘ α_i`: the entry `(i, j, i)` is the unit `λ'` after the counit
`φ_ii → id`. -/
theorem lam_eq_counit_comp_lamUnit (i j : I) [(g i).Full] [(g i).Faithful] :
    lam f g adj i j i = (adj i).counit ≫ lamUnit f g adj i j := by
  simp [lamUnit, diagIso]

end PleinementFideles

end BaseProduit

section DeuxFacteurs

variable {C : Type u₁} [Category.{v} C]

/-- The family `(a, b)` on the two indices of `WalkingPair`. -/
def famPair {F : WalkingPair → C} {T : C} (a : T ⟶ F .left) (b : T ⟶ F .right) :
    ∀ j, T ⟶ F j
  | .left => a
  | .right => b

/-- A fan over `WalkingPair` that is a limit, with its first leg corrected by an
isomorphism, is a binary product. -/
def binaryFanOfFanLeft {F : WalkingPair → C} {P : C} (p : ∀ j, P ⟶ F j)
    (h : IsLimit (Fan.mk P p)) {Y : C} (e : F .left ≅ Y) :
    IsLimit (BinaryFan.mk (p .left ≫ e.hom) (p .right)) :=
  BinaryFan.IsLimit.mk _
    (fun {T} a b => (Fan.IsLimit.lift h (famPair (a ≫ e.inv) b) : T ⟶ P))
    (fun {T} a b => show Fan.IsLimit.lift h (famPair (a ≫ e.inv) b) ≫ p .left ≫ e.hom = a by
      have h1 : Fan.IsLimit.lift h (famPair (a ≫ e.inv) b) ≫ p .left = a ≫ e.inv :=
        Fan.IsLimit.fac h _ .left
      rw [reassoc_of% h1]; simp)
    (fun {T} a b => show Fan.IsLimit.lift h (famPair (a ≫ e.inv) b) ≫ p .right = b from
      Fan.IsLimit.fac h _ .right)
    (fun {T} a b (m : T ⟶ P) (ha : m ≫ p .left ≫ e.hom = a) (hb : m ≫ p .right = b) => by
      refine Fan.IsLimit.hom_ext h _ _ fun j => ?_
      show m ≫ p j = Fan.IsLimit.lift h (famPair (a ≫ e.inv) b) ≫ p j
      have h1 : Fan.IsLimit.lift h (famPair (a ≫ e.inv) b) ≫ p j = famPair (a ≫ e.inv) b j :=
        Fan.IsLimit.fac h _ j
      rw [h1]
      cases j
      · simp [famPair, ← ha]
      · simpa [famPair] using hb)

/-- The same, with the second leg corrected. -/
def binaryFanOfFanRight {F : WalkingPair → C} {P : C} (p : ∀ j, P ⟶ F j)
    (h : IsLimit (Fan.mk P p)) {Y : C} (e : F .right ≅ Y) :
    IsLimit (BinaryFan.mk (p .left) (p .right ≫ e.hom)) :=
  BinaryFan.IsLimit.mk _
    (fun {T} a b => (Fan.IsLimit.lift h (famPair a (b ≫ e.inv)) : T ⟶ P))
    (fun {T} a b => show Fan.IsLimit.lift h (famPair a (b ≫ e.inv)) ≫ p .left = a from
      Fan.IsLimit.fac h _ .left)
    (fun {T} a b => show Fan.IsLimit.lift h (famPair a (b ≫ e.inv)) ≫ p .right ≫ e.hom = b by
      have h1 : Fan.IsLimit.lift h (famPair a (b ≫ e.inv)) ≫ p .right = b ≫ e.inv :=
        Fan.IsLimit.fac h _ .right
      rw [reassoc_of% h1]; simp)
    (fun {T} a b (m : T ⟶ P) (ha : m ≫ p .left = a) (hb : m ≫ p .right ≫ e.hom = b) => by
      refine Fan.IsLimit.hom_ext h _ _ fun j => ?_
      show m ≫ p j = Fan.IsLimit.lift h (famPair a (b ≫ e.inv)) ≫ p j
      have h1 : Fan.IsLimit.lift h (famPair a (b ≫ e.inv)) ≫ p j = famPair a (b ≫ e.inv) j :=
        Fan.IsLimit.fac h _ j
      rw [h1]
      cases j
      · simpa [famPair] using ha
      · simp [famPair, ← hb])

variable {A : Type u₁} [Category.{v} A] {B : WalkingPair → Type u₂} [∀ i, Category.{v} (B i)]
variable (f : ∀ i, A ⥤ B i) (g : ∀ i, B i ⥤ A) (adj : ∀ i, f i ⊣ g i)
variable [HasProductsOfShape WalkingPair A]

/-- (3.12)–(3.14), first factor. With `g'` fully faithful and `f'` commuting with
binary products, `pr' φ(X', X'') = X' × φ'(X'')`, `φ' = f' g''`. -/
noncomputable def deuxFacteurs_left (X : ∀ i, B i) [(g .left).Full] [(g .left).Faithful]
    [PreservesLimitsOfShape (Discrete WalkingPair) (f .left)] :
    IsLimit (BinaryFan.mk
      ((f .left).map (Limits.Pi.π (fun i => (g i).obj (X i)) .left) ≫
        (adj .left).counit.app (X .left))
      ((f .left).map (Limits.Pi.π (fun i => (g i).obj (X i)) .right) :
        (adjPi f g adj).toComonad.obj X .left ⟶ (phi f g .left .right).obj (X .right))) :=
  binaryFanOfFanLeft _ (matrice f g adj X .left) (asIso ((adj .left).counit.app (X .left)))

/-- (3.12)–(3.14), second factor: `pr'' φ(X', X'') = φ''(X') × X''`, `φ'' = f'' g'`. -/
noncomputable def deuxFacteurs_right (X : ∀ i, B i) [(g .right).Full] [(g .right).Faithful]
    [PreservesLimitsOfShape (Discrete WalkingPair) (f .right)] :
    IsLimit (BinaryFan.mk
      ((f .right).map (Limits.Pi.π (fun i => (g i).obj (X i)) .left) :
        (adjPi f g adj).toComonad.obj X .right ⟶ (phi f g .right .left).obj (X .left))
      ((f .right).map (Limits.Pi.π (fun i => (g i).obj (X i)) .right) ≫
        (adj .right).counit.app (X .right))) :=
  binaryFanOfFanRight _ (matrice f g adj X .right) (asIso ((adj .right).counit.app (X .right)))

end DeuxFacteurs

section ContreExempleFini

/-- `Y ↦ Bool × Y`. -/
def Fb : Type ⥤ Type where
  obj Y := Bool × Y
  map h := TypeCat.ofHom (Prod.map id h)

/-- `X ↦ (Bool → X)`. -/
def Gb : Type ⥤ Type where
  obj X := Bool → X
  map h := TypeCat.ofHom fun u b => h (u b)

/-- `Bool × - ⊣ (Bool → -)`. -/
def adjB : Fb ⊣ Gb := Adjunction.mkOfHomEquiv
  { homEquiv := fun _ _ =>
      { toFun := fun φ => TypeCat.ofHom fun y b => φ (b, y)
        invFun := fun ψ => TypeCat.ofHom fun p => ψ p.2 p.1
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    homEquiv_naturality_left_symm := fun _ _ => rfl
    homEquiv_naturality_right := fun _ _ => rfl }

/-- **Page 7, « ou I fini »: false.** With `I = Bool`, `A = B_i = Set` and
`f_i = Bool × -` (left adjoint of `Bool → -`), `pr_j φ((Xᵢ))` is not a product of the
`φ_ji(Xᵢ)`: for `Xᵢ = *` the first has two elements, the second four. The finite
products of `I` are not automatically preserved by the left adjoints `f_j`. -/
theorem matrice_fini_fausse :
    ¬ Nonempty ((adjPi (B := fun _ : Bool => Type) (fun _ => Fb) (fun _ => Gb)
        (fun _ => adjB)).toComonad.obj (fun _ => PUnit) true ≅
      ∏ᶜ fun i : Bool => (phi (B := fun _ : Bool => Type) (fun _ => Fb) (fun _ => Gb)
        true i).obj PUnit) := by
  rintro ⟨e⟩
  have h := Nat.card_congr e.toEquiv
  have h1 : Nat.card ((adjPi (B := fun _ : Bool => Type) (fun _ => Fb) (fun _ => Gb)
      (fun _ => adjB)).toComonad.obj (fun _ => PUnit) true) = 2 := by
    change Nat.card (Bool × ∏ᶜ fun _ : Bool => (Bool → PUnit)) = 2
    rw [Nat.card_prod, Nat.card_congr (Types.productIso _).toEquiv]
    simp
  have h2 : Nat.card (∏ᶜ fun i : Bool => (phi (B := fun _ : Bool => Type) (fun _ => Fb)
      (fun _ => Gb) true i).obj PUnit) = 4 := by
    change Nat.card (∏ᶜ fun _ : Bool => Bool × (Bool → PUnit)) = 4
    rw [Nat.card_congr (Types.productIso _).toEquiv]
    simp
  omega

end ContreExempleFini


end Grothendieck.Folder19
