import Mathlib

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
