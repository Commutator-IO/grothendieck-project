import Mathlib

/-!
# Folder 137, pages 74–83: polynomial categories and `⊗`-pd-categories

The modernised reading `transcripts/137/137.modern.tex` (« Catégories polynomiales »,
pages 74 to 85) defines a *polynomial category* `𝐏`: a category with the same objects as
a wide subcategory `𝐏₁` of maps « of degree one », with `𝐏(X, Y) = ⊕ₙ 𝐏ₙ(X, Y)`, degrees
multiplying under composition (axiom e)), composition additive in the outer variable
only. Where `Y ↦ 𝐏ₙ(X, Y)` is representable on `𝐏₁` it defines `Γⁿ X` with a universal
`γₙ : X → Γⁿ X` of degree `n` (pp. 77–78), and the factorisation of `γ_p ∘ γ_q` through
`Γ^{pq} X` gives `α_{p,q} : Γ^{pq} → Γ^p Γ^q`, associative (the square of p. 80) and
unital for `Γ¹ = id`. Conversely (pp. 81–83), from `(Γ*, α)` on an additive `𝐏₁` one
sets `𝐏_p(X, Y) = Hom(Γ^p X, Y)` with `g ∘ f = g ∘ Γ^q(f) ∘ α_{q,p}`, and page 83 says
« Les deux notions sont donc équivalentes », without proof (finding
`137-polynomial-categories-pd-tensor-categories`).

What is formalised is the core of that equivalence, the part that carries the inverse
`𝐏_p(X, Y) = Hom(Γ^p X, Y)` and the composition rule, for any degree-one category `C`
(no additivity, no tensor product needed):

* `PDCategory C`: functors `Γⁿ : C ⥤ C`, natural `α_{p,q} : Γ^{pq} → Γ^p ∘ Γ^q`, an
  isomorphism `ε : Γ¹ ≅ id` (the page's `Γ¹ = id`), the unit conditions (**) and the
  associativity square of p. 80 — a comonad graded by the monoid `(ℕ, ·)`. Indices are
  carried with an equation `p * q = n`, so that no cast appears.
* `PolynomialCategory C`: sets `𝐏ₙ(X, Y)`, composition of degree `q * p`, identities of
  degree one, associativity, and an identification `ι : (X ⟶ Y) ≃ 𝐏₁(X, Y)` compatible
  with composition; `Representation`: objects `Γⁿ X` and `γₙ` representing `𝐏ₙ(X, -)`
  on `C`.
* `PDCategory.toPoly` (pp. 81–82): the composition `g ∘ Γ^q(f) ∘ α_{q,p}` is
  associative and unital, additive in `g` when `C` is preadditive (`toPoly_comp_add`),
  and `PDCategory.representation`: `𝐏ₙ(X, -)` is represented by `Γⁿ X`, `γₙ = id`.
* `Representation.toPD` (pp. 77–80): from a polynomial category with representable
  degrees, `Γⁿ` is a functor, `α_{p,q}` is natural, `Γ¹ ≅ id`, and (**) and the square
  of p. 80 hold.
* The two passages are inverse: `toPD_representation_Γ_map`, `toPD_representation_α`,
  `toPD_representation_ε` recover `Γ`, `α`, `ε` on the nose; `toPDToPolyIso` is an
  isomorphism of polynomial categories `𝐏_p(X, Y) ≃ Hom(Γ^p X, Y)`, `φ ↦ φ ∘ γ_p`,
  compatible with composition, identities and degree-one maps.

Not formalised: the products and the additivity of `𝐏` (axioms a)–c)), the
multidegree decompositions and homogeneity under scalars (d)), f), g) and the half
`𝟏 ≅ Γ^q(𝟏)` of (***), the tensor product, strictness, the exponential formula
`Γ*(X ⊕ Y) ≅ Γ*X ⊗ Γ*Y`, and the example of `k`-modules (Roby). Proving the statement
says only that it holds as formalised; whether it is in the literature is a separate
question.
-/

namespace Grothendieck.Folder137

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- A `⊗-pd`-category without its tensor product (pp. 80–82): functors `Γⁿ`, maps
`α_{p,q} : Γ^{pq} → Γ^p Γ^q` with the associativity square of p. 80, and the unit
conditions (**) for `Γ¹ ≅ id`. -/
structure PDCategory (C : Type u) [Category.{v} C] where
  Γ : ℕ → C ⥤ C
  α : ∀ p q n : ℕ, p * q = n → (Γ n ⟶ Γ q ⋙ Γ p)
  ε : Γ 1 ≅ 𝟭 C
  α_one_left : ∀ (q : ℕ) (X : C),
    (α 1 q q (one_mul q)).app X ≫ ε.hom.app ((Γ q).obj X) = 𝟙 _
  α_one_right : ∀ (q : ℕ) (X : C),
    (α q 1 q (mul_one q)).app X ≫ (Γ q).map (ε.hom.app X) = 𝟙 _
  α_assoc : ∀ (p q r m l n : ℕ) (hm : q * r = m) (hl : p * q = l) (h₁ : p * m = n)
    (h₂ : l * r = n) (X : C),
    (α p m n h₁).app X ≫ (Γ p).map ((α q r m hm).app X) =
      (α l r n h₂).app X ≫ (α p q l hl).app ((Γ r).obj X)

/-- The composition structure of a polynomial category (pp. 74–76): degrees multiply
under composition (axiom e)), with `C` as its subcategory of degree-one maps. The
composite of `f ∈ 𝐏_p(X, Y)` and `g ∈ 𝐏_q(Y, Z)` has degree `q * p`. -/
structure PolynomialCategory (C : Type u) [Category.{v} C] where
  Hom : ℕ → C → C → Type v
  comp : ∀ {p q n : ℕ} {X Y Z : C}, Hom p X Y → Hom q Y Z → q * p = n → Hom n X Z
  id : ∀ X : C, Hom 1 X X
  id_comp : ∀ {q : ℕ} {X Y : C} (g : Hom q X Y), comp (id X) g (mul_one q) = g
  comp_id : ∀ {p : ℕ} {X Y : C} (f : Hom p X Y), comp f (id Y) (one_mul p) = f
  assoc : ∀ {p q r m l n : ℕ} {W X Y Z : C} (f : Hom p W X) (g : Hom q X Y) (k : Hom r Y Z)
    (hm : r * q = m) (hl : q * p = l) (h₁ : m * p = n) (h₂ : r * l = n),
    comp (comp f g hl) k h₂ = comp f (comp g k hm) h₁
  ι : ∀ {X Y : C}, (X ⟶ Y) ≃ Hom 1 X Y
  ι_id : ∀ X : C, ι (𝟙 X) = id X
  ι_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), ι (f ≫ g) = comp (ι f) (ι g) (mul_one 1)

namespace PDCategory

variable (G : PDCategory C)

@[reassoc]
lemma α_one_left' (q : ℕ) (X : C) (h : 1 * q = q) :
    (G.α 1 q q h).app X ≫ G.ε.hom.app ((G.Γ q).obj X) = 𝟙 _ := G.α_one_left q X

@[reassoc]
lemma α_one_right' (q : ℕ) (X : C) (h : q * 1 = q) :
    (G.α q 1 q h).app X ≫ (G.Γ q).map (G.ε.hom.app X) = 𝟙 _ := G.α_one_right q X

@[reassoc]
lemma α_assoc' (p q r m l n : ℕ) (hm : q * r = m) (hl : p * q = l) (h₁ : p * m = n)
    (h₂ : l * r = n) (X : C) :
    (G.α p m n h₁).app X ≫ (G.Γ p).map ((G.α q r m hm).app X) =
      (G.α l r n h₂).app X ≫ (G.α p q l hl).app ((G.Γ r).obj X) :=
  G.α_assoc p q r m l n hm hl h₁ h₂ X

/-- The polynomial category of a `⊗-pd`-category (pp. 81–82): `𝐏_p(X, Y) = Hom(Γ^p X, Y)`,
`g ∘ f = g ∘ Γ^q(f) ∘ α_{q,p}`, identity `ε : Γ¹ X → X`. -/
def toPoly : PolynomialCategory C where
  Hom p X Y := (G.Γ p).obj X ⟶ Y
  comp {p q n X Y Z} f g h := (G.α q p n h).app X ≫ (G.Γ q).map f ≫ g
  id X := G.ε.hom.app X
  id_comp {q X Y} g := by rw [G.α_one_right'_assoc]
  comp_id {p X Y} f := by
    have := G.ε.hom.naturality f
    simp only [Functor.id_map] at this
    rw [this, G.α_one_left'_assoc]
  assoc {p q r m l n W X Y Z} f g k hm hl h₁ h₂ := by
    simp only [Functor.map_comp, Category.assoc]
    have nat := (G.α r q m hm).naturality f
    simp only [Functor.comp_map] at nat
    rw [reassoc_of% nat, ← G.α_assoc'_assoc r q p l m n hl hm h₂ h₁]
  ι {X Y} :=
    { toFun := fun f => G.ε.hom.app X ≫ f
      invFun := fun g => G.ε.inv.app X ≫ g
      left_inv := fun f => by simp
      right_inv := fun g => by simp }
  ι_id X := by simp
  ι_comp {X Y Z} f g := by
    simp only [Equiv.coe_fn_mk, Functor.map_comp, Category.assoc]
    have n1 := G.ε.hom.naturality f
    have n2 := G.ε.hom.naturality (G.ε.hom.app X)
    simp only [Functor.id_map] at n1 n2
    rw [reassoc_of% n1, reassoc_of% n2, G.α_one_left'_assoc]

end PDCategory


namespace PolynomialCategory

variable (P : PolynomialCategory C)

/-- Associativity with the inner degree `m` prescribed. -/
lemma assoc' {p q r m l n : ℕ} {W X Y Z : C} (f : P.Hom p W X) (g : P.Hom q X Y)
    (k : P.Hom r Y Z) (hm : r * q = m) {hl : q * p = l} {h₂ : r * l = n} :
    P.comp (P.comp f g hl) k h₂ = P.comp f (P.comp g k hm) (by subst hl h₂ hm; ring) :=
  P.assoc f g k hm hl _ h₂

/-- Associativity, right to left, with the inner degree `l` prescribed. -/
lemma assoc'' {p q r m l n : ℕ} {W X Y Z : C} (f : P.Hom p W X) (g : P.Hom q X Y)
    (k : P.Hom r Y Z) (hl : q * p = l) {hm : r * q = m} {h₁ : m * p = n} :
    P.comp f (P.comp g k hm) h₁ = P.comp (P.comp f g hl) k (by subst hm h₁ hl; ring) :=
  (P.assoc f g k hm hl h₁ _).symm

lemma comp_id' {p : ℕ} {X Y : C} (f : P.Hom p X Y) (h : 1 * p = p) :
    P.comp f (P.id Y) h = f := P.comp_id f

lemma id_comp' {q : ℕ} {X Y : C} (g : P.Hom q X Y) (h : q * 1 = q) :
    P.comp (P.id X) g h = g := P.id_comp g

lemma ι_comp' {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : 1 * 1 = 1) :
    P.comp (P.ι f) (P.ι g) h = P.ι (f ≫ g) := (P.ι_comp f g).symm

/-- Representability of `P_n(X, -)` on the degree-one maps: an object `Γⁿ X` and a
universal map `γₙ : X → Γⁿ X` of degree `n` (pp. 77–78). -/
structure Representation (P : PolynomialCategory C) where
  obj : ℕ → C → C
  γ : ∀ (n : ℕ) (X : C), P.Hom n X (obj n X)
  bij : ∀ (n : ℕ) (X Y : C),
    Function.Bijective (fun φ : obj n X ⟶ Y => P.comp (γ n X) (P.ι φ) (one_mul n))

namespace Representation

variable {P} (R : P.Representation)

/-- `Hom(Γⁿ X, Y) ≃ P_n(X, Y)`, `φ ↦ φ ∘ γₙ`. -/
noncomputable def rep (n : ℕ) (X Y : C) : (R.obj n X ⟶ Y) ≃ P.Hom n X Y :=
  Equiv.ofBijective _ (R.bij n X Y)

lemma rep_apply {n : ℕ} {X Y : C} (φ : R.obj n X ⟶ Y) :
    R.rep n X Y φ = P.comp (R.γ n X) (P.ι φ) (one_mul n) := rfl

lemma rep_comp {n : ℕ} {X Y Z : C} (φ : R.obj n X ⟶ Y) (ψ : Y ⟶ Z) :
    R.rep n X Z (φ ≫ ψ) = P.comp (R.rep n X Y φ) (P.ι ψ) (one_mul n) := by
  simp only [rep_apply, P.ι_comp]
  rw [P.assoc' _ _ _ (mul_one 1)]

lemma rep_id (n : ℕ) (X : C) : R.rep n X _ (𝟙 _) = R.γ n X := by
  rw [rep_apply, P.ι_id, P.comp_id]

lemma rep_symm_apply {n : ℕ} {X Y : C} (a : P.Hom n X Y) :
    R.rep n X Y ((R.rep n X Y).symm a) = a := Equiv.apply_symm_apply _ a

lemma hom_ext {n : ℕ} {X Y : C} {φ ψ : R.obj n X ⟶ Y}
    (h : R.rep n X Y φ = R.rep n X Y ψ) : φ = ψ := (R.rep n X Y).injective h

/-- `Γⁿ` on degree-one maps: `Γⁿ(f)` corresponds to `γₙ ∘ f`. -/
noncomputable def map (n : ℕ) {X X' : C} (f : X ⟶ X') : R.obj n X ⟶ R.obj n X' :=
  (R.rep n X _).symm (P.comp (P.ι f) (R.γ n X') (mul_one n))

lemma rep_map (n : ℕ) {X X' : C} (f : X ⟶ X') :
    R.rep n X _ (R.map n f) = P.comp (P.ι f) (R.γ n X') (mul_one n) := rep_symm_apply _ _

/-- The functor `Γⁿ : P₁ → P₁`. -/
noncomputable def functor (n : ℕ) : C ⥤ C where
  obj := R.obj n
  map f := R.map n f
  map_id X := by
    apply R.hom_ext
    rw [rep_map, rep_id, P.ι_id, P.id_comp]
  map_comp {X Y Z} f g := by
    apply R.hom_ext
    rw [rep_map, rep_comp, rep_map, P.assoc' _ _ _ (one_mul n), ← rep_apply, rep_map,
      P.assoc'' _ _ _ (mul_one 1), P.ι_comp' f g]

/-- `α_{p,q} : Γ^{pq} X → Γ^p Γ^q X` corresponds to `γ_p ∘ γ_q` (p. 80). -/
noncomputable def αApp (p q n : ℕ) (h : p * q = n) (X : C) :
    R.obj n X ⟶ R.obj p (R.obj q X) :=
  (R.rep n X _).symm (P.comp (R.γ q X) (R.γ p (R.obj q X)) h)

lemma rep_αApp (p q n : ℕ) (h : p * q = n) (X : C) :
    R.rep n X _ (R.αApp p q n h X) = P.comp (R.γ q X) (R.γ p (R.obj q X)) h :=
  rep_symm_apply _ _

/-- The counit `Γ¹ X → X` corresponds to the identity of `X`. -/
noncomputable def εHom (X : C) : R.obj 1 X ⟶ X := (R.rep 1 X X).symm (P.id X)

lemma rep_εHom (X : C) : R.rep 1 X X (R.εHom X) = P.id X := rep_symm_apply _ _

lemma map_αApp (p q n : ℕ) (h : p * q = n) {X X' : C} (f : X ⟶ X') :
    R.map n f ≫ R.αApp p q n h X' = R.αApp p q n h X ≫ R.map p (R.map q f) := by
  apply R.hom_ext
  rw [rep_comp, rep_map, P.assoc' _ _ _ (one_mul n), ← rep_apply, rep_αApp,
    rep_comp, rep_αApp, P.assoc' _ _ _ (one_mul p), ← rep_apply, rep_map,
    P.assoc'' _ _ _ (one_mul q), ← rep_apply, rep_map, P.assoc' _ _ _ h]

lemma εHom_inv (X : C) : R.εHom X ≫ P.ι.symm (R.γ 1 X) = 𝟙 _ := by
  apply R.hom_ext
  rw [rep_comp, rep_εHom, Equiv.apply_symm_apply, P.id_comp, rep_id]

lemma inv_εHom (X : C) : P.ι.symm (R.γ 1 X) ≫ R.εHom X = 𝟙 _ := by
  apply P.ι.injective
  rw [P.ι_comp, Equiv.apply_symm_apply, ← rep_apply, rep_εHom, P.ι_id]

lemma map_εHom {X X' : C} (f : X ⟶ X') : R.map 1 f ≫ R.εHom X' = R.εHom X ≫ f := by
  apply R.hom_ext
  rw [rep_comp, rep_map, P.assoc' _ _ _ (mul_one 1), ← rep_apply, rep_εHom,
    P.comp_id' _ (mul_one 1), rep_comp, rep_εHom, P.id_comp]

lemma αApp_one_left (q : ℕ) (X : C) (h : 1 * q = q) :
    R.αApp 1 q q h X ≫ R.εHom (R.obj q X) = 𝟙 _ := by
  apply R.hom_ext
  rw [rep_comp, rep_αApp, P.assoc' _ _ _ (mul_one 1), ← rep_apply, rep_εHom,
    P.comp_id' _ (one_mul q), rep_id]

lemma αApp_one_right (q : ℕ) (X : C) (h : q * 1 = q) :
    R.αApp q 1 q h X ≫ R.map q (R.εHom X) = 𝟙 _ := by
  apply R.hom_ext
  rw [rep_comp, rep_αApp, P.assoc' _ _ _ (one_mul q), ← rep_apply, rep_map,
    P.assoc'' _ _ _ (mul_one 1), ← rep_apply, rep_εHom, P.id_comp, rep_id]

lemma αApp_assoc (p q r m l n : ℕ) (hm : q * r = m) (hl : p * q = l) (h₁ : p * m = n)
    (h₂ : l * r = n) (X : C) :
    R.αApp p m n h₁ X ≫ R.map p (R.αApp q r m hm X) =
      R.αApp l r n h₂ X ≫ R.αApp p q l hl (R.obj r X) := by
  apply R.hom_ext
  rw [rep_comp, rep_αApp, P.assoc' _ _ _ (one_mul p), ← rep_apply, rep_map,
    P.assoc'' _ _ _ (one_mul m), ← rep_apply, rep_αApp, rep_comp, rep_αApp,
    P.assoc' _ _ _ (one_mul l), ← rep_apply, rep_αApp, P.assoc' _ _ _ hl]

/-- `α_{p,q}` as a natural transformation `Γ^{pq} → Γ^p ∘ Γ^q`. -/
noncomputable def α (p q n : ℕ) (h : p * q = n) : R.functor n ⟶ R.functor q ⋙ R.functor p where
  app X := R.αApp p q n h X
  naturality {_ _} f := R.map_αApp p q n h f

/-- The counit `Γ¹ ≅ id`: `Γ¹ X` represents `P₁(X, -) = Hom(X, -)`. -/
noncomputable def ε : R.functor 1 ≅ 𝟭 C :=
  NatIso.ofComponents
    (fun X =>
      { hom := R.εHom X
        inv := P.ι.symm (R.γ 1 X)
        hom_inv_id := R.εHom_inv X
        inv_hom_id := R.inv_εHom X })
    (fun f => R.map_εHom f)

/-- The `⊗-pd`-structure (without `⊗`) of a polynomial category with representable
degrees: the functors `Γⁿ`, the maps `α_{p,q}` and the unit conditions (pp. 77–80). -/
noncomputable def toPD : PDCategory C where
  Γ := R.functor
  α := R.α
  ε := R.ε
  α_one_left q X := R.αApp_one_left q X _
  α_one_right q X := R.αApp_one_right q X _
  α_assoc p q r m l n hm hl h₁ h₂ X := R.αApp_assoc p q r m l n hm hl h₁ h₂ X

end Representation

end PolynomialCategory

/-- The trivial model: every `Γⁿ` the identity, every `α_{p,q}` the identity; then
`𝐏ₙ(X, Y) = Hom(X, Y)` for every `n`. It shows the axioms are consistent. -/
def PDCategory.trivial (C : Type u) [Category.{v} C] : PDCategory C where
  Γ _ := 𝟭 C
  α _ _ _ _ := 𝟙 (𝟭 C)
  ε := Iso.refl _
  α_one_left _ _ := by simp
  α_one_right _ _ := by simp
  α_assoc _ _ _ _ _ _ _ _ _ _ _ := by simp

/-! ### The two passages are inverse to each other -/

/-- An isomorphism of polynomial categories on the same degree-one category:
bijections of each `P_n(X, Y)` compatible with composition, identities and the
degree-one maps. -/
structure PolynomialCategory.Iso (P Q : PolynomialCategory C) where
  e : ∀ (n : ℕ) (X Y : C), P.Hom n X Y ≃ Q.Hom n X Y
  map_comp : ∀ {p q n : ℕ} {X Y Z : C} (f : P.Hom p X Y) (g : P.Hom q Y Z) (h : q * p = n),
    e n X Z (P.comp f g h) = Q.comp (e p X Y f) (e q Y Z g) h
  map_id : ∀ X : C, e 1 X X (P.id X) = Q.id X
  map_ι : ∀ {X Y : C} (f : X ⟶ Y), e 1 X Y (P.ι f) = Q.ι f

namespace PDCategory

variable (G : PDCategory C)

lemma toPoly_comp {p q n : ℕ} {X Y Z : C} (f : (G.Γ p).obj X ⟶ Y) (g : (G.Γ q).obj Y ⟶ Z)
    (h : q * p = n) :
    G.toPoly.comp (X := X) f g h = (G.α q p n h).app X ≫ (G.Γ q).map f ≫ g := rfl

/-- Composition `g ∘ f = g ∘ Γ^q(f) ∘ α_{q,p}` is additive in the outer variable `g`
(p. 82), when the degree-one category is additive. -/
lemma toPoly_comp_add [Preadditive C] {p q n : ℕ} {X Y Z : C} (f : (G.Γ p).obj X ⟶ Y)
    (g g' : (G.Γ q).obj Y ⟶ Z) (h : q * p = n) :
    G.toPoly.comp (X := X) f (g + g') h =
      (G.α q p n h).app X ≫ (G.Γ q).map f ≫ g + (G.α q p n h).app X ≫ (G.Γ q).map f ≫ g' := by
  simp only [toPoly_comp, Preadditive.comp_add]
  rfl

/-- In the polynomial category of a `⊗-pd`-category, `P_n(X, -)` is represented on the
degree-one maps by `Γⁿ X`, with universal map `γₙ = id_{Γⁿ X}` (p. 82: `𝐏_p(X, Y) =
Hom(Γ^p X, Y)`). -/
def representation : G.toPoly.Representation where
  obj n X := (G.Γ n).obj X
  γ n X := 𝟙 ((G.Γ n).obj X)
  bij n X Y := by
    have e : ∀ φ : (G.Γ n).obj X ⟶ Y,
        G.toPoly.comp (X := X) (𝟙 _) (G.toPoly.ι φ) (one_mul n) = φ := fun φ => by
      change (G.α 1 n n _).app X ≫ (G.Γ 1).map (𝟙 _) ≫ G.ε.hom.app _ ≫ φ = φ
      simp [G.α_one_left'_assoc]
    exact ⟨fun a b hab => (e a).symm.trans (hab.trans (e b)), fun b => ⟨b, e b⟩⟩

lemma representation_rep {n : ℕ} {X Y : C} (φ : (G.Γ n).obj X ⟶ Y) :
    G.representation.rep n X Y φ = φ := by
  change (G.α 1 n n _).app X ≫ (G.Γ 1).map (𝟙 _) ≫ G.ε.hom.app _ ≫ φ = φ
  simp [G.α_one_left'_assoc]

/-- Round trip `⊗-pd → polynomial → ⊗-pd`: the functors `Γⁿ` are recovered. -/
theorem toPD_representation_Γ_map (n : ℕ) {X X' : C} (f : X ⟶ X') :
    (G.representation.toPD.Γ n).map f = (G.Γ n).map f := by
  apply G.representation.hom_ext
  change G.representation.rep n X _ (G.representation.map n f) =
    G.representation.rep n X _ ((G.Γ n).map f)
  rw [G.representation.rep_map, representation_rep]
  change (G.α n 1 n _).app X ≫ (G.Γ n).map (G.ε.hom.app X ≫ f) ≫ 𝟙 _ = _
  rw [Category.comp_id, Functor.map_comp, G.α_one_right'_assoc]

/-- Round trip: the maps `α_{p,q}` are recovered. -/
theorem toPD_representation_α (p q n : ℕ) (h : p * q = n) (X : C) :
    (G.representation.toPD.α p q n h).app X = (G.α p q n h).app X := by
  apply G.representation.hom_ext
  change G.representation.rep n X _ (G.representation.αApp p q n h X) =
    G.representation.rep n X _ ((G.α p q n h).app X)
  rw [G.representation.rep_αApp, representation_rep]
  change (G.α p q n h).app X ≫ (G.Γ p).map (𝟙 _) ≫ 𝟙 _ = _
  simp

/-- Round trip: the counit `Γ¹ ≅ id` is recovered. -/
theorem toPD_representation_ε (X : C) :
    G.representation.toPD.ε.hom.app X = G.ε.hom.app X := by
  apply G.representation.hom_ext
  change G.representation.rep 1 X X (G.representation.εHom X) =
    G.representation.rep 1 X X (G.ε.hom.app X)
  rw [G.representation.rep_εHom, representation_rep]
  rfl

end PDCategory

namespace PolynomialCategory.Representation

variable {P : PolynomialCategory C} (R : P.Representation)

lemma toPD_toPoly_comp {p q n : ℕ} {X Y Z : C} (f : R.obj p X ⟶ Y) (g : R.obj q Y ⟶ Z)
    (h : q * p = n) :
    R.rep n X Z (R.toPD.toPoly.comp (X := X) f g h) = P.comp (R.rep p X Y f) (R.rep q Y Z g) h := by
  change R.rep n X Z (R.αApp q p n h X ≫ R.map q f ≫ g) = _
  rw [← Category.assoc, rep_comp, rep_comp, rep_αApp, P.assoc' _ _ _ (one_mul q),
    ← rep_apply, rep_map, P.assoc'' _ _ _ (one_mul p), ← rep_apply,
    P.assoc' _ _ _ (one_mul q), ← rep_apply]

/-- Round trip `polynomial → ⊗-pd → polynomial`: the polynomial category built from
`(Γ, α, ε)` by `𝐏_p(X, Y) = Hom(Γ^p X, Y)` and `g ∘ f = g ∘ Γ^q(f) ∘ α_{q,p}` is
isomorphic to the one we started from, by `φ ↦ φ ∘ γ_p`. -/
noncomputable def toPDToPolyIso : R.toPD.toPoly.Iso P where
  e n X Y := R.rep n X Y
  map_comp f g h := R.toPD_toPoly_comp f g h
  map_id X := R.rep_εHom X
  map_ι {X Y} f := by
    change R.rep 1 X Y (R.εHom X ≫ f) = _
    rw [rep_comp, rep_εHom, P.id_comp]

end PolynomialCategory.Representation

end Grothendieck.Folder137
