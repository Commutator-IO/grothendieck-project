import Mathlib

/-!
# Buffalo, topos theory, part 5b: strict cogeneration, accessibility, representability (2 July 1973)

Entries of `docs/buffalo-topos/index.tex` lines 713–766 (video `4gynb9uTEE4`, 0:04:18–1:51:31):
algebraic theories and strict cogeneration, accessible functors, representability and adjoints on
accessible categories, morphisms of algebraic theories. The status of each entry is in
`docs/buffalo-topos/lean/Part05.json`.

Accessible categories and functors are Mathlib's `IsAccessibleCategory` and `Functor.IsAccessible`
(Adámek–Rosický, with regular cardinals `κ`); Grothendieck's `π`-accessibility (SGA 4 I 9, filtered
preorders « dominating `π` ») is the `κ = π⁺` case.

One entry was found false as stated: 4gynb9uTEE4-648 (« strict cogeneration is transitive »),
retracted by the lecturer himself on 10 July (3:39:45); `not_transitive` gives a five-element
lattice where it fails.
-/

universe w v u v' u'

open CategoryTheory Limits Opposite

namespace Buffalo.Topos.Part05

noncomputable section

/-! ## Localization in `Δ` adds no objects -/

/-- 4gynb9uTEE4-258 (0:04:18) [prop] The localization `C → C[Σ⁻¹]` is bijective on objects
(Mathlib's Gabriel–Zisman construction, `Localization.Construction.objEquiv`); in `Δ` the
localization is computed in `Cat` (4gynb9uTEE4-11886). -/
theorem localization_surjective_obj {C : Type u} [Category.{v} C] (W : MorphismProperty C)
    (Y : W.Localization) : ∃ X : C, W.Q.obj X = Y := by
  obtain ⟨X, rfl⟩ := (Localization.Construction.objEquiv W).surjective Y
  exact ⟨X, rfl⟩

/-! ## Strictly generating subcategories -/

/-- 4gynb9uTEE4-386 (0:06:26) [def] `J ⊂ E` is strictly generating if every object of `E` is a
colimit of a (small) diagram of objects of `J`. -/
def IsStrictlyGenerating {E : Type u} [Category.{v} E] (J : ObjectProperty E) : Prop :=
  ∀ X : E, ∃ (K : Type v) (_ : SmallCategory K) (F : K ⥤ E) (c : Cocone F),
    (∀ k, J (F.obj k)) ∧ Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ X)

/-- The representable presheaves. -/
def representables (J : Type u) [SmallCategory J] : ObjectProperty (Jᵒᵖ ⥤ Type u) :=
  fun P => ∃ j : J, Nonempty (yoneda.obj j ≅ P)

/-- Example of 4gynb9uTEE4-386, and 4gynb9uTEE4-321 dually (`I` cogenerates its envelope
`Hom(I, Set)ᵒᵖ`, which is the case `J = Iᵒᵖ`): `J` is strictly generating in `Ĵ`, every presheaf
being the colimit of the representables over it (`Presheaf.isColimitTautologicalCocone`). -/
theorem representables_isStrictlyGenerating (J : Type u) [SmallCategory J] :
    IsStrictlyGenerating (representables J) := fun P =>
  ⟨CostructuredArrow yoneda P, inferInstance, CostructuredArrow.proj yoneda P ⋙ yoneda,
    Presheaf.tautologicalCocone P, fun k => ⟨k.left, ⟨Iso.refl _⟩⟩,
    ⟨Presheaf.isColimitTautologicalCocone P⟩, ⟨Iso.refl _⟩⟩

/-! ## Strict cogeneration is not transitive

In a preorder a limit of a diagram is a meet of its objects, so for `X ⊆ Y` the subset `X` is
strictly cogenerating in `Y` when every `y ∈ Y` is, in `Y`, the meet of the elements of `X` above
it. -/

/-- `X` strictly cogenerates `Y` (preorder version): each `y ∈ Y` is the greatest element of `Y`
below all the `x ∈ X` that lie above `y`. -/
def IsStrictlyCogenerating {α : Type*} [Preorder α] (X Y : Set α) : Prop :=
  X ⊆ Y ∧ ∀ y ∈ Y, IsGreatest {z | z ∈ Y ∧ ∀ x ∈ X, y ≤ x → z ≤ x} y

/-- A five-element lattice `bot < c < a₁, a₂ < top`. -/
inductive P5
  | bot | c | a₁ | a₂ | top
  deriving DecidableEq

namespace P5

instance : Fintype P5 := ⟨{bot, c, a₁, a₂, top}, fun x => by cases x <;> decide⟩

/-- The order of `P5`. -/
def leB : P5 → P5 → Bool
  | bot, _ => true
  | c, bot => false
  | c, _ => true
  | a₁, a₁ => true
  | a₁, top => true
  | a₂, a₂ => true
  | a₂, top => true
  | top, top => true
  | _, _ => false

instance : PartialOrder P5 where
  le x y := leB x y = true
  le_refl x := by cases x <;> rfl
  le_trans x y z := by cases x <;> cases y <;> cases z <;> decide
  le_antisymm x y := by cases x <;> cases y <;> decide

instance : DecidableRel (α := P5) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (leB x y = true))

end P5

open P5 in
/-- 4gynb9uTEE4-648 (0:10:48) [prop, false] « Strict cogeneration is transitive » fails:
in `P5`, `{a₁, a₂}` strictly cogenerates `{a₁, a₂, bot}` (where `bot` is the meet of `a₁, a₂`),
which strictly cogenerates `P5`, but `{a₁, a₂}` does not strictly cogenerate `P5` (there the
meet of `a₁, a₂` is `c`). The mechanism of 4gynb9uTEE4-13185: a limit in the intermediate
category need not be one in the big category. -/
theorem not_transitive :
    IsStrictlyCogenerating {x : P5 | x = a₁ ∨ x = a₂} {x | x = a₁ ∨ x = a₂ ∨ x = bot} ∧
    IsStrictlyCogenerating {x : P5 | x = a₁ ∨ x = a₂ ∨ x = bot} Set.univ ∧
    ¬ IsStrictlyCogenerating {x : P5 | x = a₁ ∨ x = a₂} Set.univ := by
  simp only [IsStrictlyCogenerating, IsGreatest, upperBounds, Set.mem_ofPred_eq, Set.subset_def,
    Set.mem_univ, true_and, forall_const]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> decide

/-! ## Realizations in sets -/

/-- 4gynb9uTEE4-1845 (0:30:45) [prop, partial] If `R` is complete, well-powered and has a small
coseparating set (as a small strictly cogenerating subcategory gives), every functor `R → Set`
commuting with limits is corepresentable, so `T(Set) = Hom_Δ(R, Set) ≃ Rᵒᵖ` (special adjoint
functor theorem, `isRightAdjoint_of_preservesLimits_of_isCoseparating`). -/
theorem corepresentable_of_isCoseparating {R : Type u} [Category.{w} R] [HasLimitsOfSize.{w, w} R]
    [WellPowered.{w} R] {P : ObjectProperty R} [ObjectProperty.Small.{w} P]
    (hP : P.IsCoseparating) (F : R ⥤ Type w) [PreservesLimitsOfSize.{w, w} F] :
    F.IsCorepresentable := by
  have := isRightAdjoint_of_preservesLimits_of_isCoseparating hP F
  let adj := Adjunction.ofIsRightAdjoint F
  exact ((adj.corepresentableBy PUnit).ofIso
    (Functor.isoWhiskerLeft F Coyoneda.punitIso ≪≫ F.rightUnitor)).isCorepresentable

/-- 4gynb9uTEE4-2233 (0:37:13) [ex] For groups, the universal object `ℤ` is a cogroup of `Gr`:
the comultiplication `ℤ → ℤ * ℤ`, `x ↦ x₁ x₂`, induces on `Hom(ℤ, G) ≃ G` the multiplication. -/
def comul : Multiplicative ℤ →* Monoid.Coprod (Multiplicative ℤ) (Multiplicative ℤ) :=
  zpowersHom _ (Monoid.Coprod.inl (Multiplicative.ofAdd 1) *
    Monoid.Coprod.inr (Multiplicative.ofAdd 1))

theorem comul_induces_mul {G : Type*} [Group G] (f g : Multiplicative ℤ →* G) :
    Monoid.Coprod.lift f g (comul (Multiplicative.ofAdd 1)) =
      f (Multiplicative.ofAdd 1) * g (Multiplicative.ofAdd 1) := by
  simp [comul]

/-- `Hom(ℤ, G) ≃ G`, `φ ↦ φ(1)`. -/
def homZ_equiv (G : Type*) [Group G] : G ≃ (Multiplicative ℤ →* G) := zpowersHom G

/-- 4gynb9uTEE4-2681 (0:44:41) [def] The envelope of `C` under limits of type `D'`: the closure of
`C` in `C̃` under these limits (Mathlib `ObjectProperty.limitsClosure`). -/
abbrev envelopeUnder {E : Type u} [Category.{v} E] (P : ObjectProperty E) {α : Type w}
    (J : α → Type w) [∀ a, Category.{w} (J a)] : ObjectProperty E :=
  P.limitsClosure J

/-- 4gynb9uTEE4-2746 (0:45:46) [ex, partial] On categories with finite products the theory of
groups is represented by the f.g. free groups in `Grᵒᵖ`: `Hom(F_n, G) ≃ Gⁿ`, so `F_n` is the
`n`-th power of `F_1` in `Grᵒᵖ`. -/
def freeGroup_hom_equiv (n : ℕ) (G : Type*) [Group G] : (Fin n → G) ≃ (FreeGroup (Fin n) →* G) :=
  FreeGroup.lift

/-! ## Accessible functors -/

/-- 4gynb9uTEE4-3135 (0:52:15) [prop, partial] The cardinal identity: `(2^λ)^{π₀} = 2^λ` for
`λ ≥ π₀ ≥ 1` with `λ` infinite. -/
theorem two_pow_pow (lam π₀ : Cardinal.{u}) (hl : Cardinal.aleph0 ≤ lam) (h0 : π₀ ≠ 0)
    (h : π₀ ≤ lam) : ((2 : Cardinal.{u}) ^ lam) ^ π₀ = 2 ^ lam := by
  rw [← Cardinal.power_mul, Cardinal.mul_eq_left hl h h0]

/-- 4gynb9uTEE4-3263 (0:54:23) [prop] An accessible functor between accessible categories is
`κ`-accessible and preserves `κ`-presentable objects for a suitable `κ` (the uniformization
theorem, `IsCardinalAccessibleCategory.uniformization`). -/
theorem accessible_uniformization {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} D] (F : C ⥤ D)
    [Functor.IsAccessible.{w} F] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory C κ ∧ IsCardinalAccessibleCategory D κ ∧
      F.IsCardinalAccessible κ ∧ F.PreservesCardinalPresentable κ :=
  IsCardinalAccessibleCategory.uniformization F

/-- 4gynb9uTEE4-3398 (0:56:38) [prop] For `i : C ↪ E` fully faithful and `E'` with the needed
colimits, the restriction `i^*` has a left adjoint `i_!` (left Kan extension, `lanAdjunction`)... -/
def lan_adjunction {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]
    {H : Type*} [Category H] (i : C ⥤ E) [∀ F : C ⥤ H, i.HasPointwiseLeftKanExtension F] :
    i.lan ⊣ (Functor.whiskeringLeft C E H).obj i :=
  i.lanAdjunction H

/-- ... which is fully faithful (its unit is an isomorphism). -/
def lan_fullyFaithful {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]
    {H : Type*} [Category H] (i : C ⥤ E) [i.Full] [i.Faithful]
    [∀ F : C ⥤ H, i.HasPointwiseLeftKanExtension F] :
    (i.lan (H := H)).FullyFaithful :=
  (i.lanAdjunction H).fullyFaithfulLOfIsIsoUnit

/-- 4gynb9uTEE4-3586 (0:59:46) [prop, partial] The case `π = ℵ₀`: if `C` has finite colimits,
`Ind(C)` has all (small) colimits (Mathlib instance). -/
theorem ind_hasColimits (C : Type u) [SmallCategory C] [HasFiniteColimits C] :
    HasColimits (Ind C) :=
  inferInstance

/-! ## Representability and accessible categories -/

/-- 4gynb9uTEE4-4186 (1:09:46) [prop, partial] A representable presheaf sends colimits to
limits. -/
theorem representable_preservesLimits {E : Type u} [Category.{v} E] (X : E) :
    PreservesLimits (yoneda.obj X) :=
  inferInstance

/-- 4gynb9uTEE4-4249 (1:10:49) [prop] On a complete accessible category (e.g. a cocomplete one,
hence locally presentable), a functor `F : E → Set` is corepresentable iff it commutes with
limits and is accessible (general adjoint functor theorem with
`SolutionSetCondition.of_isCardinalAccessible`; every object is presentable). -/
theorem corepresentable_iff {E : Type u'} [Category.{u} E] [IsAccessibleCategory.{u} E]
    [HasLimitsOfSize.{u, u} E] (F : E ⥤ Type u) :
    F.IsCorepresentable ↔ PreservesLimitsOfSize.{u, u} F ∧ Functor.IsAccessible.{u} F := by
  constructor
  · intro h
    let e : coyoneda.obj (op F.coreprX) ≅ F := F.coreprW
    refine ⟨preservesLimits_of_natIso e, ?_⟩
    obtain ⟨κ, hκ, _⟩ := (inferInstance : IsPresentable.{u} F.coreprX).exists_cardinal
    have := Functor.isCardinalAccessible_of_natIso e κ
    exact Functor.isAccessible_of_isCardinalAccessible F κ
  · rintro ⟨h₁, h₂⟩
    have := isRightAdjoint_of_preservesLimits_of_solutionSetCondition F
      (SolutionSetCondition.of_isCardinalAccessible F)
    let adj := Adjunction.ofIsRightAdjoint F
    exact ((adj.corepresentableBy PUnit).ofIso
      (Functor.isoWhiskerLeft F Coyoneda.punitIso ≪≫ F.rightUnitor)).isCorepresentable

/-- 4gynb9uTEE4-4454 (1:14:14) [prop, partial] Between complete accessible categories, a functor
commuting with limits and accessible has a left adjoint (general adjoint functor theorem). -/
theorem isRightAdjoint_of_accessible {C : Type u'} [Category.{u} C] {D : Type*} [Category.{u} D]
    [IsAccessibleCategory.{u} C] [IsAccessibleCategory.{u} D] [HasLimitsOfSize.{u, u} C]
    (F : C ⥤ D) [PreservesLimitsOfSize.{u, u} F] [Functor.IsAccessible.{u} F] :
    F.IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_solutionSetCondition F
    (SolutionSetCondition.of_isCardinalAccessible F)

/-- ... and conversely a right adjoint commutes with limits (and a left adjoint with colimits). -/
theorem preservesLimits_of_isRightAdjoint {C : Type u'} [Category.{u} C] {D : Type*}
    [Category.{u} D] (F : C ⥤ D) [F.IsRightAdjoint] : PreservesLimitsOfSize.{u, u} F :=
  inferInstance

/-! ## Morphisms of algebraic theories -/

/-- 4gynb9uTEE4-5529 (1:32:09) [ex] In the coproduct `C ⊕ D` of two nonempty categories there is
no initial object... -/
theorem sum_no_initial {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
    (c : C) (d : D) (X : C ⊕ D) : IsInitial X → False := by
  intro h
  rcases X with X | X
  · exact hom_inl_inr_false (f := h.to (Sum.inr d))
  · exact hom_inr_inl_false (f := h.to (Sum.inl c))

/-- ... nor a coproduct of an object of `C` and one of `D`: no object receives arrows from
both. -/
theorem sum_no_cocone {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
    (c : C) (d : D) (X : C ⊕ D) (f : Sum.inl c ⟶ X) (g : Sum.inr d ⟶ X) : False := by
  rcases X with X | X
  · exact hom_inr_inl_false (f := g)
  · exact hom_inl_inr_false (f := f)

/-- 4gynb9uTEE4-6306 (1:45:06) [prop, partial] Example of a free structure: the free group
functor is left adjoint to the forgetful functor `Gr → Set` (`GrpCat.adj`). -/
def freeGroup_adj : GrpCat.free ⊣ forget GrpCat.{u} := GrpCat.adj

/-- 4gynb9uTEE4-6434 (1:47:14) [prop] If a fully faithful functor admits a left adjoint, this
adjoint is a localization (`Adjunction.isLocalization'`, at the arrows it inverts). -/
theorem leftAdjoint_isLocalization {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Full] [G.Faithful] :
    F.IsLocalization ((MorphismProperty.isomorphisms D).inverseImage F) :=
  adj.isLocalization

end

end Buffalo.Topos.Part05
