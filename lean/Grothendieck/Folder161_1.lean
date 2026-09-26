import Mathlib.CategoryTheory.Localization.Bousfield
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Tactic.TFAE

/-!
# Folder 161-1: the fixed part of an adjunction, idempotent adjunctions, local objects

The modernised reading `transcripts/161-1/161-1.modern.tex` (manuscript pages 3–7)
states, for an adjunction `u ⊣ v` between `E` and `F`, unit `η`, counit `ε`:

> **(1)** Pour une sous-catégorie pleine `E' ⊂ E`,
> `u|E'` pl. fidèle et `vu(E') ⊂ Ē'` ⟺ `∀ Y ∈ E', η_Y : Y ⥲ vu(Y)`.
>
> Le manuscrit se demande en marge si la seconde condition de (1) est vraiment
> nécessaire — « donner un exemple montrant que cette condition n'est pas
> surabondante, avec `E'` réduit à un élément ». Elle l'est : la pleine fidélité
> de `u|E'` ne force pas `vu` à ramener `E'` dans `Ē'`.

> **Adjonctions idempotentes** (page 5) : `ηv : v ⥲ vuv`, et de même
> `εu : uvu ⥲ u` … Fait aujourd'hui classique : chacune des quatre conditions
> (`ηv`, `vε`, `εu`, `uη` inversible) implique les trois autres, de sorte que
> les paires du manuscrit sont redondantes.

> **Objets locaux** (pages 6–7) : `α : E₁ → E` pleinement fidèle d'adjoint à
> gauche `α'`, `Σ` la classe des flèches que `α'` inverse. La page vérifie que
> `(f : X → Y) ∈ Σ ⟺ Hom_E(Y, αZ₁) ≃ Hom_E(X, αZ₁)` pour tout `Z₁ ∈ E₁`, et
> conclut « Or c'est vrai sauf erreur… » : un objet `Σ`-local est dans l'image
> essentielle de `α`.

What is proved here, all as the reading states it:

* `condition1` — the equivalence (1), for any full subcategory given by an
  `ObjectProperty`, with `Ē'` its closure under isomorphism.
* `condition1_non_surabondante` — the example the margin asks for, with `E'`
  reduced to one object: `E = Type`, `F` the one-point category, `u` the unique
  functor, `v` picking the one-point set, `E' = {∅}`. Then `u|E'` is fully
  faithful but `vu(∅) = *` is not isomorphic to `∅`. So the reading's answer
  « Elle l'est » is right, and this is a witness.
* `idempotent_tfae` — the four conditions `ηv`, `vε`, `εu`, `uη` invertible are
  equivalent, which is the footnote's claim; hence the manuscript's paired
  condition 2 is equivalent to either half (`condition2_iff`).
* `sigma_iff` — the page-7 check that `f ∈ Σ` iff `f` is bijective on maps into
  every `αZ₁`. This one is in mathlib, as `ObjectProperty.isLocal_iff_isIso_map`.
* `local_mem_essImage` and `local_iff_mem_essImage` — « Or c'est vrai » : the
  `Σ`-local objects are exactly the essential image of `α`.

**What the formalisation finds.** Nothing false and no missing hypothesis. The
equivalence (1) needs nothing beyond the adjunction; the idempotence conditions
are redundant exactly as the footnote says; the local-object statement holds for
an arbitrary reflective subcategory. The rest of the folder (the free symmetric
monoidal category, the sign `ε(L)` of Picard categories, the Kan-extension and
Giraud material of pages 15–19, and the fixed-point equivalence `E₀ ≃ F₀` of
page 4) is not formalised here.

What this certifies is that the reading holds together, not that it is what the
pages say (issue #26).
-/

namespace Grothendieck.Folder161_1

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {E : Type u₁} [Category.{v₁} E] {F : Type u₂} [Category.{v₂} F]
  {u : E ⥤ F} {v : F ⥤ E} (adj : u ⊣ v)

/-- Composing `u.map` with the adjunction bijection gives `f ↦ f ≫ η_Y`: this is
the page's « n'est autre que `Hom(X, η_Y)` ». -/
theorem map_bijective_iff (X Y : E) :
    Function.Bijective (u.map : (X ⟶ Y) → (u.obj X ⟶ u.obj Y)) ↔
      Function.Bijective (fun f : X ⟶ Y => f ≫ adj.unit.app Y) := by
  have : (fun f : X ⟶ Y => f ≫ adj.unit.app Y) = (adj.homEquiv X (u.obj Y)) ∘ u.map := by
    funext f
    simp [Adjunction.homEquiv_unit]
  rw [this, Equiv.comp_bijective]

/-- **(1).** For a full subcategory `E'` of `E` (given by the property `P`):
`u` is fully faithful on `E'` and `vu` sends `E'` into its isomorphism closure
if and only if `η_Y` is an isomorphism for every `Y ∈ E'`. -/
theorem condition1 (P : ObjectProperty E) :
    ((∀ X Y, P X → P Y → Function.Bijective (u.map : (X ⟶ Y) → (u.obj X ⟶ u.obj Y))) ∧
        ∀ Y, P Y → P.isoClosure (v.obj (u.obj Y))) ↔
      ∀ Y, P Y → IsIso (adj.unit.app Y) := by
  constructor
  · rintro ⟨hff, hvu⟩ Y hY
    obtain ⟨Z, hZ, ⟨e⟩⟩ := hvu Y hY
    have bZ := (map_bijective_iff adj Z Y).1 (hff Z Y hZ hY)
    have bY := (map_bijective_iff adj Y Y).1 (hff Y Y hY hY)
    -- A section `g` of `η_Y`, through `Z ≅ vu(Y)`.
    obtain ⟨g, hg⟩ := bZ.2 e.inv
    have hg' : g ≫ adj.unit.app Y = e.inv := hg
    refine ⟨e.hom ≫ g, ?_, ?_⟩
    · apply bY.1
      show (adj.unit.app Y ≫ e.hom ≫ g) ≫ adj.unit.app Y = 𝟙 Y ≫ adj.unit.app Y
      rw [Category.assoc, Category.assoc, hg', e.hom_inv_id]
      simp
    · rw [Category.assoc, hg', e.hom_inv_id]
      rfl
  · intro h
    refine ⟨fun X Y _ hY => ?_, fun Y hY => ⟨Y, hY, ⟨(have := h Y hY; asIso (adj.unit.app Y)).symm⟩⟩⟩
    rw [map_bijective_iff adj]
    have := h Y hY
    exact (asIso (adj.unit.app Y)).homToEquiv.bijective

section Example

/-- The unique functor from `Type` to the one-point category. -/
def toPoint : Type ⥤ Discrete PUnit.{1} := (Functor.const Type).obj ⟨PUnit.unit⟩

/-- The functor picking the one-point set. -/
def fromPoint : Discrete PUnit.{1} ⥤ Type := (Functor.const (Discrete PUnit.{1})).obj PUnit

/-- `toPoint ⊣ fromPoint`: the one-point set is terminal. -/
def adjPoint : toPoint ⊣ fromPoint where
  unit := { app := fun _ => TypeCat.ofHom fun _ => PUnit.unit }
  counit := { app := fun _ => 𝟙 _ }

/-- **The margin's example**, with `E'` reduced to one object, `∅`. `u` is fully
faithful on `{∅}`, but `vu(∅)` is not isomorphic to `∅`, and `η_∅` is not an
isomorphism: the second condition of (1) is not superfluous. -/
theorem condition1_non_surabondante :
    Function.Bijective (toPoint.map : (Empty ⟶ Empty) → (toPoint.obj Empty ⟶ toPoint.obj Empty)) ∧
      ¬ (ObjectProperty.isoClosure (· = Empty)) (fromPoint.obj (toPoint.obj Empty)) ∧
      ¬ IsIso (adjPoint.unit.app Empty) := by
  refine ⟨⟨fun f g _ => by ext (x : Empty); exact x.elim, fun _ => ⟨𝟙 _, Subsingleton.elim _ _⟩⟩,
    ?_, ?_⟩
  · rintro ⟨Y, rfl, ⟨e⟩⟩
    exact (e.hom PUnit.unit).elim
  · intro h
    exact ((inv (adjPoint.unit.app Empty)) PUnit.unit).elim

end Example

section Idempotent

/-- An endomorphism equal to the identity is an isomorphism. -/
theorem isIso_of_eq_id {C : Type*} [Category C] {X : C} {f : X ⟶ X} (h : f = 𝟙 X) :
    IsIso f :=
  h ▸ inferInstance

/-- **Idempotent adjunctions.** The four conditions `ηv`, `vε`, `εu`, `uη`
invertible are equivalent. -/
theorem idempotent_tfae :
    List.TFAE [∀ P, IsIso (adj.unit.app (v.obj P)), ∀ P, IsIso (v.map (adj.counit.app P)),
      ∀ X, IsIso (adj.counit.app (u.obj X)), ∀ X, IsIso (u.map (adj.unit.app X))] := by
  tfae_have 1 ↔ 2 := by
    refine ⟨fun h P => ?_, fun h P => ?_⟩ <;>
    · have := isIso_of_eq_id (adj.right_triangle_components P)
      have := h P
      first
        | exact IsIso.of_isIso_comp_left (adj.unit.app (v.obj P)) (v.map (adj.counit.app P))
        | exact IsIso.of_isIso_comp_right (adj.unit.app (v.obj P)) (v.map (adj.counit.app P))
  tfae_have 3 ↔ 4 := by
    refine ⟨fun h X => ?_, fun h X => ?_⟩ <;>
    · have := isIso_of_eq_id (adj.left_triangle_components X)
      have := h X
      first
        | exact IsIso.of_isIso_comp_right (u.map (adj.unit.app X)) (adj.counit.app (u.obj X))
        | exact IsIso.of_isIso_comp_left (u.map (adj.unit.app X)) (adj.counit.app (u.obj X))
  tfae_have 1 → 3 := by
    intro h X
    -- `vuη_X = η_{vuX}`: both are sections of the isomorphism `vε_{uX}`.
    have hvε : IsIso (v.map (adj.counit.app (u.obj X))) := by
      have := isIso_of_eq_id (adj.right_triangle_components (u.obj X))
      have := h (u.obj X)
      exact IsIso.of_isIso_comp_left (adj.unit.app _) _
    have key : v.map (u.map (adj.unit.app X)) = adj.unit.app (v.obj (u.obj X)) := by
      rw [← cancel_mono (v.map (adj.counit.app (u.obj X))), ← Functor.map_comp]
      simp
    refine ⟨u.map (adj.unit.app X), ?_, adj.left_triangle_components X⟩
    have nat := adj.counit.naturality (u.map (adj.unit.app X))
    dsimp at nat
    rw [← nat, key]
    simp
  tfae_have 3 → 1 := by
    intro h P
    -- `uvε_P = ε_{uvP}`: both are retractions of the isomorphism `uη_{vP}`.
    have huη : IsIso (u.map (adj.unit.app (v.obj P))) := by
      have := isIso_of_eq_id (adj.left_triangle_components (v.obj P))
      have := h (v.obj P)
      exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
    have key : u.map (v.map (adj.counit.app P)) = adj.counit.app (u.obj (v.obj P)) := by
      rw [← cancel_epi (u.map (adj.unit.app (v.obj P))), ← Functor.map_comp]
      simp
    refine ⟨v.map (adj.counit.app P), adj.right_triangle_components P, ?_⟩
    have nat := adj.unit.naturality (v.map (adj.counit.app P))
    dsimp at nat
    rw [nat, key]
    simp
  tfae_finish

/-- The manuscript's condition 2, `ηv` and `εu` both invertible, is equivalent to
its first half alone: the pair is redundant. -/
theorem condition2_iff :
    ((∀ P, IsIso (adj.unit.app (v.obj P))) ∧ ∀ X, IsIso (adj.counit.app (u.obj X))) ↔
      ∀ P, IsIso (adj.unit.app (v.obj P)) :=
  ⟨And.left, fun h => ⟨h, ((idempotent_tfae adj).out 0 2).1 h⟩⟩

end Idempotent

section Local

/-! ### Reflective subcategories and local objects (pages 6–7)

`α : E₁ ⥤ E` fully faithful with left adjoint `α'`. `Σ` is the class of arrows
that `α'` inverts. -/

variable {E₁ : Type u₂} [Category.{v₂} E₁] {α : E₁ ⥤ E} {α' : E ⥤ E₁} (adj' : α' ⊣ α)
  [α.Full] [α.Faithful]

/-- The class `Σ` of arrows inverted by the reflector. -/
def Sigma' : MorphismProperty E := fun _ _ f => IsIso (α'.map f)

include adj'

/-- **Page 7.** `f ∈ Σ` if and only if `Hom(Y, αZ₁) → Hom(X, αZ₁)` is bijective
for every `Z₁ ∈ E₁`. (mathlib: `ObjectProperty.isLocal_iff_isIso_map`.) -/
theorem sigma_iff {X Y : E} (f : X ⟶ Y) :
    Sigma' (α' := α') f ↔
      ∀ Z₁ : E₁, Function.Bijective (fun g : Y ⟶ α.obj Z₁ => f ≫ g) := by
  rw [Sigma', ← ObjectProperty.isLocal_iff_isIso_map adj' f]
  exact ⟨fun h Z₁ => h _ ⟨Z₁, rfl⟩, fun h _ ⟨Z₁, hZ⟩ => hZ ▸ h Z₁⟩

/-- **« Or c'est vrai sauf erreur… »** A `Σ`-local object is in the essential
image of `α`. -/
theorem local_mem_essImage {ξ : E} (hξ : (Sigma' (α' := α')).isLocal ξ) : α.essImage ξ := by
  let η := adj'.unit.app ξ
  have hη : Sigma' (α' := α') η :=
    (ObjectProperty.isLocal_iff_isIso_map adj' η).1 (ObjectProperty.isLocal_adj_unit_app adj' ξ)
  -- `η` has a retraction `r`, because `ξ` is local …
  obtain ⟨r, hr⟩ := (hξ η hη).2 (𝟙 ξ)
  have hr' : η ≫ r = 𝟙 ξ := hr
  -- … and `r` is also a section, because `α α' ξ` is local for `η`.
  have hrη : r ≫ η = 𝟙 _ := by
    apply (ObjectProperty.isLocal_adj_unit_app adj' ξ _ ⟨α'.obj ξ, rfl⟩).1
    show η ≫ r ≫ η = η ≫ 𝟙 _
    rw [← Category.assoc, hr']
    simp
  exact ⟨α'.obj ξ, ⟨{ hom := r, inv := η, hom_inv_id := hrη, inv_hom_id := hr' }⟩⟩

/-- The `Σ`-local objects are exactly the essential image of `α`. -/
theorem local_iff_mem_essImage (ξ : E) :
    (Sigma' (α' := α')).isLocal ξ ↔ α.essImage ξ := by
  refine ⟨local_mem_essImage adj', ?_⟩
  rintro ⟨Z₁, ⟨e⟩⟩
  have : (Sigma' (α' := α')).isLocal (α.obj Z₁) := fun X Y f hf => (sigma_iff adj' f).1 hf Z₁
  exact (Sigma' (α' := α')).isLocal.prop_of_iso e this

end Local

end Grothendieck.Folder161_1
