import Buffalo.Topos.Part01b

/-!
# Buffalo, topos theory, part 1d: algebraic structures on objects of a category (11 May 1973)

Entries of `docs/buffalo-topos/index.tex` of the section « Algebraic structures on objects of a
category » (video `URU5jgTvjhU`, 4:59:30–5:34:24). The status of each entry is in
`docs/buffalo-topos/lean/Part01.json`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TensorProduct

namespace Buffalo.Topos.Part01

noncomputable section

section Laws

variable {C : Type*} [Category C] [HasBinaryProducts C]

/-- URU5jgTvjhU-17970 (4:59:30) [def] A composition law `m : E × E → E` is commutative if it is
unchanged by the symmetry of `E × E` ... -/
def IsCommLaw {E : C} (m : E ⨯ E ⟶ E) : Prop :=
  (prod.braiding E E).hom ≫ m = m

/-- URU5jgTvjhU-17970 (4:59:30) [def] ... and associative if `(ab)c = a(bc)` as arrows
`(E × E) × E → E`. -/
def IsAssocLaw {E : C} (m : E ⨯ E ⟶ E) : Prop :=
  (prod.associator E E E).hom ≫ prod.map (𝟙 E) m ≫ m = prod.map m (𝟙 E) ≫ m

/-- URU5jgTvjhU-18102 (5:01:42) [def] A left unit is `e : 1 → E` such that
`E ≃ 1 × E → E × E → E` is the identity. -/
def IsLeftUnit [HasTerminal C] {E : C} (m : E ⨯ E ⟶ E) (e : ⊤_ C ⟶ E) : Prop :=
  prod.lift (terminal.from E) (𝟙 E) ≫ prod.map e (𝟙 E) ≫ m = 𝟙 E

/-- URU5jgTvjhU-18295 (5:04:55) [prop] Via Yoneda, a law `E × E → E` is equivalent to laws on the
sets `Hom(Z, E)`, functorial in `Z`. -/
def lawEquiv (E : C) :
    (E ⨯ E ⟶ E) ≃ { μ : ∀ Z : C, (Z ⟶ E) → (Z ⟶ E) → (Z ⟶ E) //
      ∀ (Z Z' : C) (h : Z' ⟶ Z) (a b : Z ⟶ E), μ Z' (h ≫ a) (h ≫ b) = h ≫ μ Z a b } where
  toFun m := ⟨fun _ a b => prod.lift a b ≫ m, fun Z Z' h a b => by
    change prod.lift (h ≫ a) (h ≫ b) ≫ m = h ≫ prod.lift a b ≫ m
    rw [← prod.comp_lift, Category.assoc]⟩
  invFun μ := μ.1 (E ⨯ E) prod.fst prod.snd
  left_inv m := by simp
  right_inv μ := by
    apply Subtype.ext
    funext Z a b
    change prod.lift a b ≫ μ.1 (E ⨯ E) prod.fst prod.snd = μ.1 Z a b
    rw [← μ.2 _ _ (prod.lift a b), prod.lift_fst, prod.lift_snd]

end Laws

/-- URU5jgTvjhU-18427 (5:07:07) [def] and URU5jgTvjhU-19406 (5:23:26) [prop] An algebraic structure
(here a group) on an object is Mathlib's `Grp C`; a functor commuting with finite products sends
group objects to group objects. -/
def mapGrpOfPreserves {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
    [CartesianMonoidalCategory D] (F : C ⥤ D) [PreservesFiniteProducts F] : Grp C ⥤ Grp D :=
  letI := Functor.Monoidal.ofChosenFiniteProducts F
  F.mapGrp

section Internal

variable {C : Type*} [Category C] [HasPullbacks C]

/-- URU5jgTvjhU-18687 (5:11:27) [prop] and URU5jgTvjhU-18814 (5:13:34) [def] A category internal
to `C`: objects `D₀`, arrows `D₁`, source and target `D₁ ⇉ D₀`, units `D₀ → D₁`, and composition
`D₁ ×_{D₀} D₁ → D₁` (pairs `(f, g)` with `t f = s g`), the axioms being equalities of arrows out of
fibre products. -/
structure InternalCategory where
  /-- Objects. -/
  D₀ : C
  /-- Arrows. -/
  D₁ : C
  /-- Source. -/
  s : D₁ ⟶ D₀
  /-- Target. -/
  t : D₁ ⟶ D₀
  /-- Units. -/
  e : D₀ ⟶ D₁
  /-- Composition. -/
  comp : pullback t s ⟶ D₁
  e_s : e ≫ s = 𝟙 D₀
  e_t : e ≫ t = 𝟙 D₀
  comp_s : comp ≫ s = pullback.fst t s ≫ s
  comp_t : comp ≫ t = pullback.snd t s ≫ t
  id_comp : pullback.lift (s ≫ e) (𝟙 D₁) (by simp [Category.assoc, e_t]) ≫ comp = 𝟙 D₁
  comp_id : pullback.lift (𝟙 D₁) (t ≫ e) (by simp [Category.assoc, e_s]) ≫ comp = 𝟙 D₁
  assoc :
    pullback.lift (pullback.fst _ _ ≫ comp) (pullback.snd (pullback.snd t s ≫ t) s)
        (by rw [Category.assoc, comp_t]; exact pullback.condition) ≫ comp =
      pullback.lift (pullback.fst _ _ ≫ pullback.fst t s)
        (pullback.lift (pullback.fst _ _ ≫ pullback.snd t s)
          (pullback.snd (pullback.snd t s ≫ t) s)
          (by rw [Category.assoc]; exact pullback.condition) ≫ comp)
        (by
          simp only [Category.assoc, comp_s, pullback.lift_fst_assoc]
          rw [pullback.condition (f := t) (g := s)]) ≫ comp

end Internal

/-- URU5jgTvjhU-18881 (5:14:41) [prop] The Yoneda embedding `C → Ĉ` commutes with limits but not
with colimits: for `C = Set`, the image of the initial set `∅` is not initial in `Ĉ`
(`Hom(∅, ∅)` is not empty). -/
theorem yoneda_limits_not_colimits :
    Nonempty (PreservesLimits (yoneda : Type u ⥤ _)) ∧
      ¬ Nonempty (IsInitial (yoneda.obj PEmpty.{u + 1})) := by
  refine ⟨⟨inferInstance⟩, fun ⟨h⟩ => ?_⟩
  exact ((h.to ((Functor.const _).obj PEmpty.{u + 1})).app (op PEmpty) (𝟙 PEmpty)).elim

variable {X : TopCat.{u}}

/-- URU5jgTvjhU-19073 (5:17:53) [def] A sheaf of groups is a presheaf of groups whose composite with
the forgetful functor is a sheaf. -/
theorem grp_isSheaf_iff (F : X.Presheaf GrpCat.{u}) :
    F.IsSheaf ↔ TopCat.Presheaf.IsSheaf (F ⋙ forget GrpCat.{u}) :=
  TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget GrpCat.{u}) F

/-- URU5jgTvjhU-19532 (5:25:32) [prop] The stalks of a presheaf of rings are rings, and the
underlying set of the stalk is the stalk of the underlying presheaf of sets (the forgetful functor
commutes with filtered colimits). (For groups Mathlib has no colimits in `GrpCat` at this revision.) -/
def ring_stalk (F : X.Presheaf CommRingCat.{u}) (x : X) :
    (forget CommRingCat.{u}).obj (F.stalk x) ≅
      TopCat.Presheaf.stalk (F ⋙ forget CommRingCat.{u}) x :=
  preservesColimitIso (forget CommRingCat.{u}) ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ F)

/-- URU5jgTvjhU-19665 (5:27:45) [def] For a `k`-coalgebra `A`, an `A`-comodule is a `k`-module `M`
with `M → M ⊗ A` coassociative and counital. -/
structure Comodule (k A M : Type*) [CommRing k] [AddCommGroup A] [Module k A] [Coalgebra k A]
    [AddCommGroup M] [Module k M] where
  /-- The coaction. -/
  coact : M →ₗ[k] M ⊗[k] A
  coassoc : (TensorProduct.assoc k M A A).toLinearMap ∘ₗ coact.rTensor A ∘ₗ coact =
    (Coalgebra.comul (R := k) (A := A)).lTensor M ∘ₗ coact
  counit : (TensorProduct.rid k M).toLinearMap ∘ₗ (Coalgebra.counit (R := k) (A := A)).lTensor M ∘ₗ
    coact = LinearMap.id

/-- URU5jgTvjhU-20064 (5:34:24) [def] `E` is a torsor under `G` if `E ≠ ∅` and `G` acts simply
transitively on `E` (the definition of 9213). -/
theorem isTorsor_iff (G E : Type*) [Group G] [MulAction G E] :
    IsTorsor G E ↔ Nonempty E ∧ ∀ x y : E, ∃! g : G, g • x = y := by
  rw [IsTorsor, isSimplyTransitive_iff, and_comm]
  refine and_congr_left' ⟨fun h => ?_, fun ⟨x⟩ _ => ⟨x, rfl⟩⟩
  obtain ⟨x, -⟩ := h PUnit.unit
  exact ⟨x⟩

end

end Buffalo.Topos.Part01
