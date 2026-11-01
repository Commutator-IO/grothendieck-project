import Mathlib

/-!
# Bourbaki, rédaction n° 461 (February 1966): three propositions of Chevalley's abelian categories

Rédaction 461 of the Bourbaki archive (Archives Henri Poincaré, item 1036) is Chevalley's draft
« Catégories abéliennes ». This file checks two of its propositions and states the definition
behind a third.

**§ 1, Proposition 24 (pp. 43–44).** A category with a zero object and binary biproducts (the
page's « sous-additive » categories; the hom-sets are then commutative monoids, Mathlib's
`CategoryTheory.SemiadditiveOfBinaryBiproducts.addCommMonoidHomOfHasBinaryBiproducts`) in which
every morphism that is both a weak monomorphism and a weak epimorphism (zero kernel and zero
cokernel, in the sense `g ≫ f = 0 → g = 0` and `f ≫ g = 0 → g = 0`) is invertible is
additive. The page applies the hypothesis to the shear map `(x, y) ↦ (x, x + y)` of `X ⊞ X`,
writes the inverse as a matrix and reads off an additive inverse of the identity of `X`.

* `shear`, `inl_comp_shear`, `inr_comp_shear`, `lift_comp_shear`, `shear_comp_desc`: the shear
  map and how it acts on lifts and descents;
* `shear_weakMono`, `shear_weakEpi`: it has zero kernel and zero cokernel;
* `exists_add_id_eq_zero_of_isIso`: if it is invertible, `𝟙 X` has an additive inverse;
* `WeakMonoEpiInvertible`: the hypothesis of the proposition;
* `exists_add_eq_zero`: under it every morphism has an additive inverse;
* `preadditive`, `preadditive_add`: the resulting preadditive structure, whose addition is the
  one given by the biproducts.

**§ 2, first Proposition 41 (pp. 105–106).** In a commutative diagram with two rows
`a₀ ⟶ b₀ ⟶ c₀` and `a₁ ⟶ b₁ ⟶ c₁` of an abelian category, if the left vertical map is an
epimorphism, the right square is cartesian, the top composite is zero and the bottom row is
exact, then the top row is exact. The page assumes the category equivalent to one « à
fracteurs » and argues with subobjects; its Remark 1 notes that the assumption always holds
(Proposition 43), so it is dropped here, and the proof chases elements up to refinements
(Mathlib's `CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements`). The number 41 is
used twice on the typescript; this is the first one.

* `exact_top_row`: the proposition.

**§ 2, Definition 4 (pp. 78–79).** A « catégorie abélienne à fracteurs » is an abelian category
with two classes `J`, `Q` of monomorphisms and epimorphisms in which every subobject and every
quotient has exactly one representative in the class, both classes contain the identities and
are closed under composition, and pullbacks of an injection along a surjection are strictly
unique. Axiom Fr 5 is transcribed as typed: the uniqueness clause does not ask the square to
commute, and a second clause says that any such pair forms a cartesian square. Lemma 1 (p. 79)
uses the uniqueness clause in exactly this form. Proposition 43 (pp. 109–117), that every
abelian category is equivalent to one with fracteurs, is not formalised, and no model of the
structure is constructed here.

* `Fracteurs`: Definition 4;
* `Fracteurs.J_eq`, `Fracteurs.Q_eq`: Lemma 1, two injections (surjections) with the same
  source and target are equal.
-/

open CategoryTheory Limits

namespace Bourbaki.Redaction461Props

section SubAdditive

open SemiadditiveOfBinaryBiproducts

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

attribute [local instance] addCommMonoidHomOfHasBinaryBiproducts

/-- The shear map `(x, y) ↦ (x, x + y)` of `X ⊞ X`, the matrix `(1 0; 1 1)` of the page. -/
noncomputable def shear (X : C) : X ⊞ X ⟶ X ⊞ X :=
  biprod.lift biprod.fst (biprod.desc (𝟙 X) (𝟙 X))

theorem lift_comp_shear {Z X : C} (g₁ g₂ : Z ⟶ X) :
    biprod.lift g₁ g₂ ≫ shear X = biprod.lift g₁ (g₁ + g₂) := by
  ext
  · simp [shear]
  · simp [shear, add_eq_left_addition]

theorem inl_comp_shear (X : C) : biprod.inl ≫ shear X = biprod.lift (𝟙 X) (𝟙 X) := by
  ext <;> simp [shear]

theorem inr_comp_shear (X : C) : biprod.inr ≫ shear X = biprod.inr := by
  ext <;> simp [shear]

theorem shear_comp_desc {X Z : C} (h₁ h₂ : X ⟶ Z) :
    shear X ≫ biprod.desc h₁ h₂ = biprod.desc (h₁ + h₂) h₂ := by
  ext
  · rw [← Category.assoc, inl_comp_shear, biprod.inl_desc, add_eq_right_addition]
  · rw [← Category.assoc, inr_comp_shear, biprod.inr_desc, biprod.inr_desc]

theorem shear_weakMono (X : C) ⦃Z : C⦄ (g : Z ⟶ X ⊞ X) (hg : g ≫ shear X = 0) : g = 0 := by
  have e : g = biprod.lift (g ≫ biprod.fst) (g ≫ biprod.snd) := by ext <;> simp
  rw [e] at hg ⊢
  rw [lift_comp_shear] at hg
  have h₁ := congrArg (· ≫ biprod.fst) hg
  have h₂ := congrArg (· ≫ biprod.snd) hg
  simp only [biprod.lift_fst, biprod.lift_snd, zero_comp] at h₁ h₂
  rw [h₁, zero_add] at h₂
  ext <;> simp [h₁, h₂]

theorem shear_weakEpi (X : C) ⦃Z : C⦄ (h : X ⊞ X ⟶ Z) (hh : shear X ≫ h = 0) : h = 0 := by
  have e : h = biprod.desc (biprod.inl ≫ h) (biprod.inr ≫ h) := by ext <;> simp
  rw [e] at hh ⊢
  rw [shear_comp_desc] at hh
  have h₁ := congrArg (biprod.inl ≫ ·) hh
  have h₂ := congrArg (biprod.inr ≫ ·) hh
  simp only [biprod.inl_desc, biprod.inr_desc, comp_zero] at h₁ h₂
  rw [h₂, add_zero] at h₁
  ext <;> simp [h₁, h₂]

theorem exists_add_id_eq_zero_of_isIso (X : C) [IsIso (shear X)] : ∃ g : X ⟶ X, 𝟙 X + g = 0 := by
  refine ⟨biprod.inl ≫ inv (shear X) ≫ biprod.snd, ?_⟩
  have e : biprod.inl ≫ inv (shear X) = biprod.lift (biprod.inl ≫ inv (shear X) ≫ biprod.fst)
      (biprod.inl ≫ inv (shear X) ≫ biprod.snd) := by ext <;> simp
  have h := congrArg (· ≫ shear X) e
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, lift_comp_shear] at h
  have h₁ := congrArg (· ≫ biprod.fst) h
  have h₂ := congrArg (· ≫ biprod.snd) h
  simp only [biprod.inl_fst, biprod.inl_snd, biprod.lift_fst, biprod.lift_snd] at h₁ h₂
  rw [← h₁] at h₂
  exact h₂.symm

/-- Chevalley's hypothesis: a morphism with zero kernel and zero cokernel is invertible. -/
def WeakMonoEpiInvertible (C : Type*) [Category C] [HasZeroMorphisms C] : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ ⦃Z : C⦄ (g : Z ⟶ X), g ≫ f = 0 → g = 0) →
    (∀ ⦃Z : C⦄ (g : Y ⟶ Z), f ≫ g = 0 → g = 0) → IsIso f

theorem exists_add_eq_zero (H : WeakMonoEpiInvertible C) {X Y : C} (f : X ⟶ Y) :
    ∃ g : X ⟶ Y, f + g = 0 := by
  have := H (shear X) (shear_weakMono X) (shear_weakEpi X)
  obtain ⟨g, hg⟩ := exists_add_id_eq_zero_of_isIso X
  refine ⟨g ≫ f, ?_⟩
  have := congrArg (· ≫ f) hg
  simpa [add_comp] using this

/-- **Proposition 24** in its structural form: under Chevalley's hypothesis, the commutative
monoid structure on the hom-sets given by the biproducts is that of a preadditive category. -/
@[instance_reducible]
noncomputable def preadditive (H : WeakMonoEpiInvertible C) : Preadditive C where
  homGroup X Y :=
    letI : Neg (X ⟶ Y) := ⟨fun f => (exists_add_eq_zero H f).choose⟩
    { AddGroup.ofLeftAxioms add_assoc zero_add fun f => by
        rw [add_comm]
        exact (exists_add_eq_zero H f).choose_spec with
      add_comm := add_comm }
  add_comp _ _ _ _ _ _ := add_comp _ _ _
  comp_add _ _ _ _ _ _ := comp_add _ _ _

/-- The addition of `preadditive H` is the one given by the biproducts. -/
theorem preadditive_add (H : WeakMonoEpiInvertible C) {X Y : C} (f g : X ⟶ Y) :
    @HAdd.hAdd (X ⟶ Y) (X ⟶ Y) (X ⟶ Y)
      (@instHAdd _ (@Preadditive.homGroup C _ (preadditive H) X Y).toAdd) f g = f + g :=
  rfl

end SubAdditive

section FirstProp41

variable {C : Type*} [Category C] [Abelian C]

/-- **First Proposition 41** (pp. 105–106). In a commutative diagram
```
 a₀ ──φ₀──▶ b₀ ──ξ₀──▶ c₀
 │α         │β         │γ
 ▼          ▼          ▼
 a₁ ──φ₁──▶ b₁ ──ξ₁──▶ c₁
```
with `α` epi, the right square cartesian, `φ₀ ≫ ξ₀ = 0` and the bottom row exact, the top row
is exact. -/
theorem exact_top_row {a₀ b₀ c₀ a₁ b₁ c₁ : C} {φ₀ : a₀ ⟶ b₀} {ξ₀ : b₀ ⟶ c₀}
    {φ₁ : a₁ ⟶ b₁} {ξ₁ : b₁ ⟶ c₁} {α : a₀ ⟶ a₁} {β : b₀ ⟶ b₁} {γ : c₀ ⟶ c₁}
    (wl : φ₀ ≫ β = α ≫ φ₁) (hI : IsPullback ξ₀ β γ ξ₁) [Epi α] (h₀ : φ₀ ≫ ξ₀ = 0)
    (h₁ : φ₁ ≫ ξ₁ = 0) (hex : (ShortComplex.mk φ₁ ξ₁ h₁).Exact) :
    (ShortComplex.mk φ₀ ξ₀ h₀).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  dsimp at x hx ⊢
  have hxβ : (x ≫ β) ≫ ξ₁ = 0 := by
    rw [Category.assoc, ← hI.w, ← Category.assoc, hx, zero_comp]
  obtain ⟨A₁, π₁, _, y, hy⟩ := hex.exact_up_to_refinements (x ≫ β) hxβ
  obtain ⟨A₂, π₂, _, z, hz⟩ := surjective_up_to_refinements_of_epi α y
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, z, ?_⟩
  dsimp at hy ⊢
  apply hI.hom_ext
  · simp [hx, h₀]
  · simp only [Category.assoc]
    rw [hy, reassoc_of% hz, wl]

end FirstProp41

section Fracteurs

/-- **Definition 4** (pp. 78–79), as typed: a *catégorie abélienne à fracteurs* is an abelian
category with classes `J` of monomorphisms (*injections*) and `Q` of epimorphisms
(*surjections*) such that (Fr 2) identities are in both; (Fr 3) every monomorphism (resp.
epimorphism) becomes an injection (resp. surjection) after composing with exactly one
isomorphism into its source (resp. out of its target); (Fr 4) `J` and `Q` are closed under
composition; (Fr 5) for an injection `μ : z ⟶ y` and a surjection `χ : x ⟶ y` there is exactly
one pair (injection into `x`, surjection into `z`) with a common source, and any such pair
forms a cartesian square over `(χ, μ)`. -/
structure Fracteurs (C : Type*) [Category C] [Abelian C] where
  /-- The injections. -/
  J : MorphismProperty C
  /-- The surjections. -/
  Q : MorphismProperty C
  mono_of_J : ∀ ⦃a b : C⦄ (f : a ⟶ b), J f → Mono f
  epi_of_Q : ∀ ⦃a b : C⦄ (f : a ⟶ b), Q f → Epi f
  id_J : ∀ a : C, J (𝟙 a)
  id_Q : ∀ a : C, Q (𝟙 a)
  J_rep : ∀ ⦃a b : C⦄ (f : a ⟶ b), Mono f → ∃! e : Σ w : C, w ≅ a, J (e.2.hom ≫ f)
  Q_rep : ∀ ⦃a b : C⦄ (f : a ⟶ b), Epi f → ∃! e : Σ w : C, b ≅ w, Q (f ≫ e.2.hom)
  J_comp : ∀ ⦃a b c : C⦄ (f : a ⟶ b) (g : b ⟶ c), J f → J g → J (f ≫ g)
  Q_comp : ∀ ⦃a b c : C⦄ (f : a ⟶ b) (g : b ⟶ c), Q f → Q g → Q (f ≫ g)
  pullback_unique : ∀ ⦃x y z : C⦄ (μ : z ⟶ y) (χ : x ⟶ y), J μ → Q χ →
    ∃! p : Σ w : C, (w ⟶ x) × (w ⟶ z), J p.2.1 ∧ Q p.2.2
  isPullback : ∀ ⦃w x y z : C⦄ (μ : z ⟶ y) (χ : x ⟶ y) (μ' : w ⟶ x) (χ' : w ⟶ z), J μ → Q χ →
    J μ' → Q χ' → IsPullback μ' χ' χ μ

variable {C : Type*} [Category C] [Abelian C]

/-- **Lemma 1** (p. 79), for injections: two injections with the same source and target are
equal. -/
theorem Fracteurs.J_eq (F : Fracteurs C) {a b : C} (f g : a ⟶ b) (hf : F.J f) (hg : F.J g) :
    f = g := by
  obtain ⟨p, -, hp⟩ := F.pullback_unique f (𝟙 b) hf (F.id_Q b)
  have e₁ := hp ⟨a, f, 𝟙 a⟩ ⟨hf, F.id_Q a⟩
  have e₂ := hp ⟨a, g, 𝟙 a⟩ ⟨hg, F.id_Q a⟩
  have := e₁.trans e₂.symm
  simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at this
  exact this.1

/-- **Lemma 1** (p. 79), for surjections: two surjections with the same source and target are
equal. -/
theorem Fracteurs.Q_eq (F : Fracteurs C) {a b : C} (f g : a ⟶ b) (hf : F.Q f) (hg : F.Q g) :
    f = g := by
  obtain ⟨p, -, hp⟩ := F.pullback_unique (𝟙 b) f (F.id_J b) hf
  have e₁ := hp ⟨a, 𝟙 a, f⟩ ⟨F.id_J a, hf⟩
  have e₂ := hp ⟨a, 𝟙 a, g⟩ ⟨F.id_J a, hg⟩
  have := e₁.trans e₂.symm
  simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at this
  exact this

end Fracteurs

end Bourbaki.Redaction461Props
