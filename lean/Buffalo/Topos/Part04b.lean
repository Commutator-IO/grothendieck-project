import Mathlib

/-!
# Buffalo, topos theory, part 4b: exactness properties, 2-fibre products, algebraic theories

Entries of `docs/buffalo-topos/index.tex` from « Algebraic structures and exactness properties »
to « Theories as 2-fibred categories over `Cat_D` » (video `PqCQM3Pcl6Q`, 5:14:17–8:58:56). The
status of each entry is in `docs/buffalo-topos/lean/Part04.json`.

The 2-category `Cat_D` is not in Mathlib. We model the part of it the entries use: a pair
`D = (D', D'')` of families of small diagram shapes, the categories having limits of type `D'` and
colimits of type `D''`, the functors preserving them (`IsDFunctor`), exactness properties
`(I, Σ)`, 2-sums, envelopes and localizations by their (2-)universal properties against one
target category at a time.
-/

universe w v u v₁ u₁ v₂ u₂

open CategoryTheory Limits

namespace Buffalo.Topos.Part04

noncomputable section

/-! ## Algebraic structures and exactness properties -/

/-- PqCQM3Pcl6Q-18971 (5:16:11) [ex] In `Set`, filtering colimits commute with finite limits. -/
theorem filtered_colimit_commutes_finite_limit {J K : Type v} [SmallCategory J] [SmallCategory K]
    [FinCategory J] [IsFiltered K] (F : J × K ⥤ Type v) :
    IsIso (colimitLimitToLimitColimit F) :=
  inferInstance

/-- A family of diagram types: an index set and, for each index, a small category. -/
structure DiagramTypes where
  /-- The indices. -/
  ι : Type
  /-- The shape of each diagram type. -/
  shape : ι → Type
  /-- Each shape is a small category. -/
  [cat : ∀ i, SmallCategory (shape i)]

attribute [instance] DiagramTypes.cat

/-- `D = (D', D'')`: the types of inverse limits and of direct limits. -/
structure DSpec where
  /-- `D'`, the inverse limits. -/
  lim : DiagramTypes
  /-- `D''`, the direct limits. -/
  colim : DiagramTypes

variable (D : DSpec)

/-- PqCQM3Pcl6Q-19319 (5:21:59) [def] The objects of `Cat_D`: categories with limits of type `D'`
and colimits of type `D''`. -/
def HasD (C : Type u) [Category.{v} C] : Prop :=
  (∀ i, HasLimitsOfShape (D.lim.shape i) C) ∧ (∀ j, HasColimitsOfShape (D.colim.shape j) C)

/-- PqCQM3Pcl6Q-19319 (5:21:59) [def] The 1-morphisms of `Cat_D`: functors commuting with the
limits of type `D'` and the colimits of type `D''` (2-morphisms: all natural transformations). -/
def IsDFunctor {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] (F : A ⥤ B) :
    Prop :=
  (∀ i, PreservesLimitsOfShape (D.lim.shape i) F) ∧
    (∀ j, PreservesColimitsOfShape (D.colim.shape j) F)

theorem IsDFunctor.comp {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {E : Type u} [Category.{v} E] {F : A ⥤ B} {G : B ⥤ E} (hF : IsDFunctor D F)
    (hG : IsDFunctor D G) : IsDFunctor D (F ⋙ G) :=
  ⟨fun i => by have := hF.1 i; have := hG.1 i; infer_instance,
    fun j => by have := hF.2 j; have := hG.2 j; infer_instance⟩

/-- PqCQM3Pcl6Q-19493 (5:24:53) [def] `C` has the exactness property `(I, Σ)` if every
`D`-functor `I → C` inverts the arrows of `Σ`. -/
def SatisfiesExactness (I : Type u₁) [Category.{v₁} I] (Sig : MorphismProperty I)
    (C : Type u₂) [Category.{v₂} C] : Prop :=
  ∀ φ : I ⥤ C, IsDFunctor D φ → ∀ ⦃a b : I⦄ (s : a ⟶ b), Sig s → IsIso (φ.map s)

/-- PqCQM3Pcl6Q-20033 (5:33:53) [def] A 2-sum of the `I_λ`, tested against one category `C`:
`Hom_D(I, C) → ∏_λ Hom_D(I_λ, C)` is essentially surjective and fully faithful. -/
structure IsTwoSumFor {Λ : Type w} (I : Λ → Type u₁) [∀ l, Category.{v₁} (I l)]
    (S : Type u₁) [Category.{v₁} S] (ι : ∀ l, I l ⥤ S) (C : Type u₂) [Category.{v₂} C] :
    Prop where
  /-- Every family of `D`-functors `I_λ → C` extends to a `D`-functor `I → C`. -/
  ess : ∀ ψ : ∀ l, I l ⥤ C, (∀ l, IsDFunctor D (ψ l)) →
    ∃ φ : S ⥤ C, IsDFunctor D φ ∧ ∀ l, Nonempty (ι l ⋙ φ ≅ ψ l)
  /-- Natural transformations are determined by, and glue from, their restrictions. -/
  ff : ∀ φ φ' : S ⥤ C, IsDFunctor D φ → IsDFunctor D φ' →
    Function.Bijective (fun (t : φ ⟶ φ') l => Functor.whiskerLeft (ι l) t)

/-- PqCQM3Pcl6Q-20146 (5:35:46) [prop], the direction that always holds: with `Σ` the union of
the images of the `Σ_λ`, a category satisfying every `(I_λ, Σ_λ)` satisfies `(I, Σ)`. -/
theorem satisfiesExactness_twoSum_of_forall {Λ : Type w} (I : Λ → Type u₁)
    [∀ l, Category.{v₁} (I l)] (S : Type u₁) [Category.{v₁} S] (ι : ∀ l, I l ⥤ S)
    (hι : ∀ l, IsDFunctor D (ι l)) (Sig : ∀ l, MorphismProperty (I l))
    (C : Type u₂) [Category.{v₂} C]
    (h : ∀ l, SatisfiesExactness D (I l) (Sig l) C) :
    SatisfiesExactness D S (fun _ _ s => ∃ l, (Sig l).map (ι l) s) C := by
  intro φ hφ a b s ⟨l, a', b', t, ht, ⟨e⟩⟩
  have h1 : IsIso ((ι l ⋙ φ).map t) := h l _ ((hι l).comp D hφ) t ht
  exact ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff (φ.mapArrow.mapIso e)).1 h1

/-- PqCQM3Pcl6Q-20146 (5:35:46) [prop], the converse, under the hypothesis the entry omits: if
`I` is a 2-sum of the `I_λ` (for `C`) and every `I_μ` admits at least one `D`-functor to `C`, a
category satisfying `(I, Σ)` satisfies every `(I_λ, Σ_λ)`. -/
theorem forall_of_satisfiesExactness_twoSum {Λ : Type w} (I : Λ → Type u₁)
    [∀ l, Category.{v₁} (I l)] (S : Type u₁) [Category.{v₁} S] (ι : ∀ l, I l ⥤ S)
    (Sig : ∀ l, MorphismProperty (I l)) (C : Type u₂) [Category.{v₂} C]
    (hS : IsTwoSumFor D I S ι C) (hne : ∀ l, ∃ ψ : I l ⥤ C, IsDFunctor D ψ)
    (h : SatisfiesExactness D S (fun _ _ s => ∃ l, (Sig l).map (ι l) s) C) (l : Λ) :
    SatisfiesExactness D (I l) (Sig l) C := by
  classical
  intro ψ hψ a b t ht
  choose χ hχ using hne
  let ψ' : ∀ m, I m ⥤ C := Function.update χ l ψ
  have hψ' : ∀ m, IsDFunctor D (ψ' m) := by
    intro m
    by_cases hm : m = l
    · subst hm; simpa [ψ'] using hψ
    · simpa [ψ', Function.update_of_ne hm] using hχ m
  obtain ⟨φ, hφ, he⟩ := hS.ess ψ' hψ'
  obtain ⟨e⟩ := he l
  have h1 : IsIso (φ.map ((ι l).map t)) :=
    h φ hφ _ ⟨l, MorphismProperty.map_mem_map _ _ _ ht⟩
  have h2 : IsIso ((ι l ⋙ φ).map t) := h1
  have h3 : IsIso ((ψ' l).map t) := (NatIso.isIso_map_iff e t).1 h2
  have e2 : ψ' l = ψ := Function.update_self l ψ χ
  rw [e2] at h3
  exact h3

/-- PqCQM3Pcl6Q-20146 (5:35:46) [prop], why the hypothesis is needed: when `D` contains the empty
limit and the empty colimit, a `D`-functor from the one-point category to `C` is an object both
initial and terminal, and `Set` has none. So `Set` satisfies vacuously every exactness property
`(I, Σ)` whose `I` is a 2-sum having the point as a summand, without satisfying the other
summand's. -/
theorem no_initial_terminal_set : ¬ ∃ X : Type u, Nonempty (IsInitial X) ∧ Nonempty (IsTerminal X) := by
  rintro ⟨X, ⟨hi⟩, ⟨ht⟩⟩
  have x : X := ht.from PUnit.{u + 1} PUnit.unit
  exact (hi.to PEmpty.{u + 1} x).elim

/-- PqCQM3Pcl6Q-20502 (5:41:42) [def] `j : J → E` is a `D`-envelope of `J` (tested against `C`):
`E ∈ Cat_D`, and composition with `j` from `Hom_D(E, C)` to `Hom(J, C)` is essentially
surjective and fully faithful. -/
structure IsDEnvelopeFor {J : Type u₁} [Category.{v₁} J] {E : Type u₁} [Category.{v₁} E]
    (j : J ⥤ E) (C : Type u₂) [Category.{v₂} C] : Prop where
  /-- Every functor `J → C` extends to a `D`-functor `E → C`. -/
  ess : ∀ ψ : J ⥤ C, ∃ φ : E ⥤ C, IsDFunctor D φ ∧ Nonempty (j ⋙ φ ≅ ψ)
  /-- Natural transformations between `D`-functors are determined by their restrictions. -/
  ff : ∀ φ φ' : E ⥤ C, IsDFunctor D φ → IsDFunctor D φ' →
    Function.Bijective (fun t : φ ⟶ φ' => Functor.whiskerLeft j t)

/-! ## 2-fibre products of categories -/

/-- The naive fibre product of `f : X → S` and `g : Y → S` (objects with equal images). -/
def NaiveFibreObj {X S Y : Type*} [Category X] [Category S] [Category Y] (f : X ⥤ S)
    (g : Y ⥤ S) : Type _ :=
  {p : X × Y // f.obj p.1 = g.obj p.2}

/-- PqCQM3Pcl6Q-20801 (5:46:41) [cex] The naive fibre product is not invariant under equivalence:
`S` the indiscrete category on two objects (equivalent to the point), `X = Y` the point, `f`, `g`
picking the two objects. The naive fibre product of `f, f` is non-empty, that of `f, g` is
empty, although `f ≅ g` (so the two cospans are equivalent). -/
theorem naiveFibre_not_invariant :
    let f : Discrete PUnit.{1} ⥤ Codiscrete Bool := (Functor.const _).obj ⟨false⟩
    let g : Discrete PUnit.{1} ⥤ Codiscrete Bool := (Functor.const _).obj ⟨true⟩
    Nonempty (f ≅ g) ∧ Nonempty (NaiveFibreObj f f) ∧ IsEmpty (NaiveFibreObj f g) := by
  refine ⟨⟨NatIso.ofComponents (fun _ => ⟨⟨⟩, ⟨⟩, rfl, rfl⟩) (fun _ => rfl)⟩,
    ⟨⟨(⟨⟨⟩⟩, ⟨⟨⟩⟩), rfl⟩⟩, ⟨fun p => ?_⟩⟩
  have := congrArg Codiscrete.as p.2
  exact Bool.noConfusion this

/-- PqCQM3Pcl6Q-21085 (5:51:25) [def] The 2-fibre product: Mathlib's categorical pullback, with
objects `(x, y, α : f x ≅ g y)`. -/
example {X S Y : Type*} [Category X] [Category S] [Category Y] (f : X ⥤ S) (g : Y ⥤ S)
    (p : CategoricalPullback f g) : f.obj p.fst ≅ g.obj p.snd :=
  p.iso

/-- PqCQM3Pcl6Q-21085 (5:51:25) [prop], essential surjectivity of the naive fibre product: if `f`
lifts isomorphisms (as a fibred category does, by Cartesian lifts), every object `(x, y, α)` of
the 2-fibre product is isomorphic to one with `f x' = g y` and `α` an identity. -/
theorem twoFibre_iso_strict {X S Y : Type*} [Category X] [Category S] [Category Y] (f : X ⥤ S)
    (g : Y ⥤ S)
    (hf : ∀ (x : X) (s : S) (e : f.obj x ≅ s), ∃ (x' : X) (e' : x ≅ x') (h : f.obj x' = s),
      f.map e'.hom ≫ eqToHom h = e.hom)
    (p : CategoricalPullback f g) :
    ∃ (q : CategoricalPullback f g) (h : f.obj q.fst = g.obj q.snd),
      q.iso = eqToIso h ∧ Nonempty (p ≅ q) := by
  obtain ⟨x', e', h, he⟩ := hf p.fst _ p.iso
  refine ⟨⟨x', p.snd, eqToIso h⟩, h, rfl, ⟨CategoricalPullback.mkIso e' (Iso.refl _) ?_⟩⟩
  simp [he]

/-- PqCQM3Pcl6Q-21261 (5:54:21) [prop] The 2-fibre product is 2-universal:
`Hom(C, X ×²_S Y) ≃ Hom(C, X) ×²_{Hom(C,S)} Hom(C, Y)` (Mathlib's
`CategoricalPullback.functorEquiv`). -/
example {X S Y : Type*} [Category X] [Category S] [Category Y] (f : X ⥤ S) (g : Y ⥤ S)
    (C : Type*) [Category C] :
    (C ⥤ CategoricalPullback f g) ≌ CategoricalPullback.CatCommSqOver f g C :=
  CategoricalPullback.functorEquiv f g C

/-- PqCQM3Pcl6Q-21549 (5:59:09) [def] Pseudo-functors `I → Cat` (composition up to coherent
isomorphism): Mathlib's `Pseudofunctor`, with `I` viewed as a locally discrete bicategory. -/
example (I : Type) [Category I] : Type _ := Pseudofunctor (LocallyDiscrete I) Cat

/-! ## Envelopes, localization and a worked exactness property -/

/-- PqCQM3Pcl6Q-22260 (6:11:00) [ex] Sums are universal in `Set`: for `X = ∐ x_α` and any
`X' → X`, `X'` is the sum of the `X'_α = x_α ×_X X'`. -/
def sums_universal {A : Type u} (x : A → Type u) {X' : Type u} (f : X' → Σ a, x a) :
    X' ≃ Σ a, {y : X' // (f y).1 = a} :=
  (Equiv.sigmaFiberEquiv fun y => (f y).1).symm

/-- PqCQM3Pcl6Q-22849 (6:20:49) [def] `L : J → J'` is a `D`-localization of `J` at `Σ` (tested
against `C`): `L` is a `D`-functor inverting `Σ`, and composition with `L` from `Hom_D(J', C)` to
the `D`-functors inverting `Σ` is essentially surjective and fully faithful. -/
structure IsDLocalizationFor {J : Type u₁} [Category.{v₁} J] {J' : Type u₁} [Category.{v₁} J']
    (L : J ⥤ J') (Sig : MorphismProperty J) (C : Type u₂) [Category.{v₂} C] : Prop where
  isD : IsDFunctor D L
  inverts : Sig.IsInvertedBy L
  ess : ∀ ψ : J ⥤ C, IsDFunctor D ψ → Sig.IsInvertedBy ψ →
    ∃ φ : J' ⥤ C, IsDFunctor D φ ∧ Nonempty (L ⋙ φ ≅ ψ)
  ff : ∀ φ φ' : J' ⥤ C, IsDFunctor D φ → IsDFunctor D φ' →
    Function.Bijective (fun t : φ ⟶ φ' => Functor.whiskerLeft L t)

/-- An exactness property `(I, Σ)`. -/
structure ExactnessProperty where
  /-- The category `I`. -/
  I : Type
  /-- `I` is a small category. -/
  [cat : SmallCategory I]
  /-- The arrows to be inverted. -/
  Sig : MorphismProperty I

attribute [instance] ExactnessProperty.cat

/-- PqCQM3Pcl6Q-23931 (6:38:51) [def] `Cat_{D,η}`: the categories of `Cat_D` satisfying every
exactness property of `η` (a full sub-2-category, same functors). -/
def InCatDEta (η : Set ExactnessProperty) (C : Type u) [Category.{v} C] : Prop :=
  HasD D C ∧ ∀ e ∈ η, SatisfiesExactness D e.I e.Sig C

/-- PqCQM3Pcl6Q-24399 (6:46:39) [ex] A monoidal (for instance finite-product-preserving) functor
sends group objects to group objects: Mathlib's `Functor.mapGrp`. -/
example {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C] {E : Type u₂}
    [Category.{v₂} E] [CartesianMonoidalCategory E] (F : C ⥤ E) [F.Monoidal] :
    Grp C ⥤ Grp E :=
  F.mapGrp

/-- PqCQM3Pcl6Q-24458 (6:47:38) [prop], in `Set`: `P` with a `G`-action is a torsor (non-empty,
free and transitive) iff `G × P → P × P`, `(g, p) ↦ (g p, p)` is bijective and `P → 1` is
surjective. -/
theorem torsor_iff_shear {G P : Type*} [Group G] [MulAction G P] :
    (Function.Bijective (fun q : G × P => (q.1 • q.2, q.2)) ∧ Nonempty P) ↔
      (Nonempty P ∧ MulAction.IsPretransitive G P ∧ ∀ (g : G) (p : P), g • p = p → g = 1) := by
  constructor
  · rintro ⟨⟨hi, hs⟩, hP⟩
    refine ⟨hP, ⟨fun x y => ?_⟩, fun g p hg => ?_⟩
    · obtain ⟨⟨g, p⟩, h⟩ := hs (y, x)
      simp only [Prod.mk.injEq] at h
      exact ⟨g, h.2 ▸ h.1⟩
    · have := @hi (g, p) (1, p) (by simp [hg])
      exact (Prod.mk.inj this).1
  · rintro ⟨hP, htr, hfree⟩
    refine ⟨⟨fun ⟨g, p⟩ ⟨g', p'⟩ h => ?_, fun ⟨a, b⟩ => ?_⟩, hP⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      have : (g'⁻¹ * g) • p = p := by rw [mul_smul, h1, inv_smul_smul]
      have := hfree _ p this
      rw [inv_mul_eq_one] at this
      rw [this]
    · obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G b a
      exact ⟨(g, b), by simp [hg]⟩

/-- PqCQM3Pcl6Q-24514 (6:48:34) [prop] `P → Q` is a monomorphism iff the square with `P = P ×_Q P`
is Cartesian, an epimorphism iff the dual square is co-Cartesian. -/
theorem mono_epi_squares {C : Type u} [Category.{v} C] {P Q : C} (f : P ⟶ Q) :
    (Mono f ↔ IsPullback (𝟙 P) (𝟙 P) f f) ∧ (Epi f ↔ IsPushout f f (𝟙 Q) (𝟙 Q)) :=
  ⟨mono_iff_isPullback f, epi_iff_isPushout f⟩

/-! ## Limits and colimits in `Cat_D`; examples of `D` -/

/-- PqCQM3Pcl6Q-25333 (7:02:13) [prop], products: limits in a product of categories exist and are
computed componentwise. -/
theorem pi_hasLimitsOfShape {Λ : Type v} (C : Λ → Type u) [∀ l, Category.{v} (C l)]
    (K : Type v) [Category.{v} K] [∀ l, HasLimitsOfShape K (C l)] :
    HasLimitsOfShape K (∀ l, C l) :=
  ⟨fun _ => pi.hasLimit_of_hasLimit_comp_eval⟩

/-- PqCQM3Pcl6Q-26391 (7:19:51) [ex] Finite inverse limits and left exact functors: left exact
functors compose. -/
example {A B E : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} E] (F : A ⥤ B)
    (G : B ⥤ E) [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    PreservesFiniteLimits (F ⋙ G) :=
  inferInstance

/-- PqCQM3Pcl6Q-26447 (7:20:47) [ex] Arbitrary inverse limits: the embedding `C → Ĉ` preserves
them (each `Hom(X, -)` does). -/
example {C : Type u} [Category.{v} C] (X : Cᵒᵖ) : PreservesLimits (coyoneda.obj X) :=
  inferInstance

/-- PqCQM3Pcl6Q-26619 (7:23:39) [ex] Preordered categories: at most one arrow between two
objects. -/
example (α : Type u) [Preorder α] (a b : α) : Subsingleton (a ⟶ b) :=
  inferInstance

/-- PqCQM3Pcl6Q-26729 (7:25:29) [ex] Semi-additive categories: with a zero object and binary
biproducts (`X ⊔ Y ≅ X × Y`), the Hom-sets are commutative monoids. -/
example {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C] (X Y : C) :
    AddCommMonoid (X ⟶ Y) :=
  SemiadditiveOfBinaryBiproducts.addCommMonoidHomOfHasBinaryBiproducts X Y

/-- PqCQM3Pcl6Q-26785 (7:26:25) [ex] Abelian categories with exact functors (the universal abelian
category on one object is not in Mathlib). -/
example {A B : Type u} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B] :
    Category (A ⥤ₑ B) :=
  inferInstance

/-- PqCQM3Pcl6Q-26843 (7:27:23) [ex] Abelian categories with exact filtering colimits (AB5). -/
example (A : Type u) [Category.{v} A] [Abelian A] [HasFilteredColimits A] : Prop := AB5 A

/-- PqCQM3Pcl6Q-26908 (7:28:28) [ex] Finite inverse and direct limits, with exact functors. -/
example {A B : Type u} [Category.{v} A] [Category.{v} B] (F : A ⥤ B) [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : A ⥤ₑ B :=
  ExactFunctor.of F

/-- PqCQM3Pcl6Q-27254 (7:34:14) [ex] Ordered sets with finite lower bounds and arbitrary upper
bounds in which finite lower bounds distribute over arbitrary upper bounds: frames, with frame
homomorphisms. -/
theorem frame_distrib {α : Type u} [Order.Frame α] (a : α) (s : Set α) :
    a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  inf_sSup_eq

example (α β : Type u) [Order.Frame α] [Order.Frame β] : Type u := FrameHom α β

/-! ## Base objects and the rules for algebraic theories -/

/-- PqCQM3Pcl6Q-29754 (8:15:54) [ex] A group is commutative iff `G → G^ab` is an isomorphism. -/
theorem abelianization_bijective_iff (G : Type u) [Group G] :
    Function.Bijective (Abelianization.of : G →* Abelianization G) ↔ ∀ a b : G, a * b = b * a := by
  constructor
  · intro h a b
    apply h.1
    rw [map_mul, map_mul, mul_comm]
  · intro h
    refine ⟨?_, fun x => ?_⟩
    · rw [← MonoidHom.ker_eq_bot_iff, Abelianization.ker_of, commutator_def,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _ y _
      exact h y x
    · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨g, rfl⟩

/-- PqCQM3Pcl6Q-29812 (8:16:52) [prop] An arrow is a monomorphism iff its diagonal is an
isomorphism, and two parallel arrows are equal iff their equalizer is an isomorphism. -/
theorem mono_iff_diagonal_equal_iff_equalizer {C : Type u} [Category.{v} C] {X Y : C}
    (f : X ⟶ Y) [HasPullback f f] (g h : X ⟶ Y) [HasEqualizer g h] :
    (IsIso (pullback.diagonal f) ↔ Mono f) ∧ (IsIso (equalizer.ι g h) ↔ g = h) :=
  ⟨pullback.isIso_diagonal_iff f, ⟨fun _ => eq_of_epi_equalizer, fun hgh => equalizer.ι_of_eq hgh⟩⟩

/-! ## Theories as 2-fibred categories -/

/-- PqCQM3Pcl6Q-31476 (8:44:36) [ex] A monoid is a group iff the shear map `(x, y) ↦ (x, xy)` of
`M × M` is bijective. -/
theorem monoid_isGroup_iff_shear (M : Type u) [Monoid M] :
    Function.Bijective (fun q : M × M => (q.1, q.1 * q.2)) ↔ ∀ x : M, IsUnit x := by
  constructor
  · rintro ⟨-, hs⟩
    have rinv : ∀ x : M, ∃ y, x * y = 1 := fun x => by
      obtain ⟨⟨a, y⟩, h⟩ := hs (x, 1)
      simp only [Prod.mk.injEq] at h
      exact ⟨y, h.1 ▸ h.2⟩
    intro x
    obtain ⟨y, hy⟩ := rinv x
    obtain ⟨z, hz⟩ := rinv y
    have hxz : x = z := by rw [← mul_one x, ← hz, ← mul_assoc, hy, one_mul]
    exact ⟨⟨x, y, hy, by rw [hxz, hz]⟩, rfl⟩
  · intro hu
    refine ⟨fun ⟨a, b⟩ ⟨a', b'⟩ h => ?_, fun ⟨a, b⟩ => ?_⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      rw [(hu a).mul_left_cancel h2]
    · obtain ⟨u, rfl⟩ := hu a
      exact ⟨(u, ↑u⁻¹ * b), by simp⟩

/-- PqCQM3Pcl6Q-32336 (8:58:56) [cex], the half « connectedness of the spectrum is expressible »:
`Spec R` is connected iff `R ≠ 0` and its only idempotents are `0` and `1` (equations). -/
theorem primeSpectrum_connected_iff (R : Type u) [CommRing R] :
    ConnectedSpace (PrimeSpectrum R) ↔
      Nontrivial R ∧ ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [connectedSpace_iff_clopen, PrimeSpectrum.nonempty_iff_nontrivial]
  refine and_congr_right fun _ => ⟨fun h e he => ?_, fun h s hs => ?_⟩
  · rcases h _ ((PrimeSpectrum.isClopen_iff (s := (PrimeSpectrum.basicOpen e : Set _))).2
      ⟨e, he, rfl⟩) with h0 | h1
    · left
      have : PrimeSpectrum.basicOpen e = ⊥ := by ext1; exact h0
      exact he.eq_zero_of_isNilpotent ((PrimeSpectrum.basicOpen_eq_bot_iff e).1 this)
    · right
      have htop : PrimeSpectrum.basicOpen e = ⊤ := by ext1; exact h1
      have hmul : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
      have hbot : PrimeSpectrum.basicOpen (1 - e) = ⊥ := by
        have := PrimeSpectrum.basicOpen_mul e (1 - e)
        rw [hmul, PrimeSpectrum.basicOpen_zero, htop, top_inf_eq] at this
        exact this.symm
      have := he.one_sub.eq_zero_of_isNilpotent ((PrimeSpectrum.basicOpen_eq_bot_iff _).1 hbot)
      exact (sub_eq_zero.1 this).symm
  · obtain ⟨e, he, rfl⟩ := (PrimeSpectrum.isClopen_iff).1 hs
    rcases h e he with rfl | rfl
    · left; simp
    · right; simp

end

end Buffalo.Topos.Part04
