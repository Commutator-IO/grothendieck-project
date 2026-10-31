import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Bourbaki, rédaction n° 438 (Chevalley, 1965), Lemma 1, p. 35: one triangle identity suffices

Rédaction 438, « Catégories fibrées », needs an adjunction in the proof of its Proposition 1 and
isolates the step as Lemma 1 (pp. 35–36). There are two functors `R : C' → C`, `S : C → C'` and
two natural transformations, a counit `R ∘ S → Id` and a unit `Id → S ∘ R`. One triangle
identity is assumed, and of the other composite `S → S` only that it is an automorphism; the
conclusion is that the unit and counit are those of an adjunction, so that this automorphism is
in fact the identity. The rédaction proves it by comparing the two maps between hom-sets that
the unit and counit induce.

Here `F : C ⥤ D` plays `R` and `G : D ⥤ C` plays `S`, with `η : 𝟭 C ⟶ F ⋙ G` and
`ε : G ⋙ F ⟶ 𝟭 D`. The proof below is shorter than the rédaction's: by naturality of `η` and
`ε`, and the triangle identity that holds, the composite `η (G Y) ≫ G.map (ε Y)` is idempotent,
and an invertible idempotent is the identity. The statement is probably Johnstone, *Sketches of
an Elephant*, Lemma A1.1.1 (not checked against the book).

**What is proved.**
* `eq_id_of_isIso_of_idem`: an idempotent isomorphism is the identity.
* `rightTriangle_of_leftTriangle`: **Lemma 1, rédaction n° 438, p. 35.** If
  `F.map (η X) ≫ ε (F X) = 𝟙` for every `X` and `η (G Y) ≫ G.map (ε Y)` is an isomorphism for
  every `Y`, then `η (G Y) ≫ G.map (ε Y) = 𝟙`.
* `leftTriangle_of_rightTriangle`: the dual, with the roles of the two triangle identities
  exchanged.
* `adjunctionOfLeftTriangle`, `adjunctionOfRightTriangle`: the corresponding adjunctions
  `F ⊣ G` with unit `η` and counit `ε`, built with `Adjunction.mkOfUnitCounit`.

**Not formalised.** Proposition 1 of the rédaction (fibred categories and the canonical fibre
product), for which the lemma is a step.
-/

namespace Grothendieck.Bourbaki438

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- An idempotent isomorphism is the identity. -/
theorem eq_id_of_isIso_of_idem {X : C} (e : X ⟶ X) [IsIso e] (h : e ≫ e = e) : e = 𝟙 X := by
  simpa using h =≫ inv e

variable {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D)

/-- Under the left triangle identity, the right triangle composite `η (G Y) ≫ G.map (ε Y)` is
idempotent. -/
theorem rightComposite_idem (hl : ∀ X : C, F.map (η.app X) ≫ ε.app (F.obj X) = 𝟙 (F.obj X))
    (Y : D) :
    (η.app (G.obj Y) ≫ G.map (ε.app Y)) ≫ (η.app (G.obj Y) ≫ G.map (ε.app Y)) =
      η.app (G.obj Y) ≫ G.map (ε.app Y) := by
  have h1 := η.naturality (G.map (ε.app Y))
  have h2 := η.naturality (η.app (G.obj Y))
  have h3 := ε.naturality (ε.app Y)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h1 h2 h3
  calc (η.app (G.obj Y) ≫ G.map (ε.app Y)) ≫ (η.app (G.obj Y) ≫ G.map (ε.app Y))
      = η.app (G.obj Y) ≫ (G.map (ε.app Y) ≫ η.app (G.obj Y)) ≫ G.map (ε.app Y) := by
        simp only [Category.assoc]
    _ = η.app (G.obj Y) ≫ (η.app (G.obj (F.obj (G.obj Y))) ≫
          G.map (F.map (G.map (ε.app Y)))) ≫ G.map (ε.app Y) := by rw [h1]
    _ = (η.app (G.obj Y) ≫ η.app (G.obj (F.obj (G.obj Y)))) ≫
          G.map (F.map (G.map (ε.app Y)) ≫ ε.app Y) := by
        simp only [Category.assoc, Functor.map_comp]
    _ = (η.app (G.obj Y) ≫ G.map (F.map (η.app (G.obj Y)))) ≫
          G.map (ε.app (F.obj (G.obj Y)) ≫ ε.app Y) := by rw [h2, h3]
    _ = η.app (G.obj Y) ≫ G.map ((F.map (η.app (G.obj Y)) ≫ ε.app (F.obj (G.obj Y))) ≫
          ε.app Y) := by
        simp only [Category.assoc, Functor.map_comp]
    _ = η.app (G.obj Y) ≫ G.map (ε.app Y) := by rw [hl, Category.id_comp]

/-- **Lemma 1, rédaction n° 438, p. 35.** If the left triangle identity holds and every right
triangle composite `η (G Y) ≫ G.map (ε Y)` is an isomorphism, then that composite is the
identity. -/
theorem rightTriangle_of_leftTriangle
    (hl : ∀ X : C, F.map (η.app X) ≫ ε.app (F.obj X) = 𝟙 (F.obj X))
    (hr : ∀ Y : D, IsIso (η.app (G.obj Y) ≫ G.map (ε.app Y))) (Y : D) :
    η.app (G.obj Y) ≫ G.map (ε.app Y) = 𝟙 (G.obj Y) :=
  eq_id_of_isIso_of_idem _ (rightComposite_idem η ε hl Y)

/-- Under the right triangle identity, the left triangle composite `F.map (η X) ≫ ε (F X)` is
idempotent. -/
theorem leftComposite_idem (hr : ∀ Y : D, η.app (G.obj Y) ≫ G.map (ε.app Y) = 𝟙 (G.obj Y))
    (X : C) :
    (F.map (η.app X) ≫ ε.app (F.obj X)) ≫ (F.map (η.app X) ≫ ε.app (F.obj X)) =
      F.map (η.app X) ≫ ε.app (F.obj X) := by
  have h1 := ε.naturality (F.map (η.app X))
  have h2 := ε.naturality (ε.app (F.obj X))
  have h3 := η.naturality (η.app X)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at h1 h2 h3
  calc (F.map (η.app X) ≫ ε.app (F.obj X)) ≫ (F.map (η.app X) ≫ ε.app (F.obj X))
      = F.map (η.app X) ≫ (ε.app (F.obj X) ≫ F.map (η.app X)) ≫ ε.app (F.obj X) := by
        simp only [Category.assoc]
    _ = F.map (η.app X) ≫ (F.map (G.map (F.map (η.app X))) ≫
          ε.app (F.obj (G.obj (F.obj X)))) ≫ ε.app (F.obj X) := by rw [h1]
    _ = F.map (η.app X ≫ G.map (F.map (η.app X))) ≫
          (ε.app (F.obj (G.obj (F.obj X))) ≫ ε.app (F.obj X)) := by
        simp only [Category.assoc, Functor.map_comp]
    _ = F.map (η.app X ≫ η.app (G.obj (F.obj X))) ≫
          (F.map (G.map (ε.app (F.obj X))) ≫ ε.app (F.obj X)) := by rw [h3, h2]
    _ = F.map (η.app X ≫ (η.app (G.obj (F.obj X)) ≫ G.map (ε.app (F.obj X)))) ≫
          ε.app (F.obj X) := by
        simp only [Category.assoc, Functor.map_comp]
    _ = F.map (η.app X) ≫ ε.app (F.obj X) := by rw [hr]; simp

/-- The dual of Lemma 1: if the right triangle identity holds and every left triangle composite
`F.map (η X) ≫ ε (F X)` is an isomorphism, then that composite is the identity. -/
theorem leftTriangle_of_rightTriangle
    (hr : ∀ Y : D, η.app (G.obj Y) ≫ G.map (ε.app Y) = 𝟙 (G.obj Y))
    (hl : ∀ X : C, IsIso (F.map (η.app X) ≫ ε.app (F.obj X))) (X : C) :
    F.map (η.app X) ≫ ε.app (F.obj X) = 𝟙 (F.obj X) :=
  eq_id_of_isIso_of_idem _ (leftComposite_idem η ε hr X)

/-- **Lemma 1, rédaction n° 438, p. 35, as an adjunction.** The left triangle identity together
with the invertibility of the right triangle composites makes `(η, ε)` the unit and counit of
an adjunction `F ⊣ G`. -/
@[simps! unit counit]
def adjunctionOfLeftTriangle
    (hl : ∀ X : C, F.map (η.app X) ≫ ε.app (F.obj X) = 𝟙 (F.obj X))
    (hr : ∀ Y : D, IsIso (η.app (G.obj Y) ≫ G.map (ε.app Y))) : F ⊣ G :=
  Adjunction.mkOfUnitCounit
    { unit := η
      counit := ε
      left_triangle := by ext X; simpa using hl X
      right_triangle := by ext Y; simpa using rightTriangle_of_leftTriangle η ε hl hr Y }

/-- The dual: the right triangle identity together with the invertibility of the left triangle
composites makes `(η, ε)` the unit and counit of an adjunction `F ⊣ G`. -/
@[simps! unit counit]
def adjunctionOfRightTriangle
    (hr : ∀ Y : D, η.app (G.obj Y) ≫ G.map (ε.app Y) = 𝟙 (G.obj Y))
    (hl : ∀ X : C, IsIso (F.map (η.app X) ≫ ε.app (F.obj X))) : F ⊣ G :=
  Adjunction.mkOfUnitCounit
    { unit := η
      counit := ε
      left_triangle := by ext X; simpa using leftTriangle_of_rightTriangle η ε hr hl X
      right_triangle := by ext Y; simpa using hr Y }

end Grothendieck.Bourbaki438
