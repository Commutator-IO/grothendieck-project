import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Bourbaki, rédaction n° 469 (Deligne, 1966), errata p. 52: the constant functor creates limits

Rédaction 469, « Catégories abéliennes », proves on p. 23 (Th. 4) that a functor category
`C ⥤ A` inherits the structure of `A`; the errata of p. 52 repair the converse with a lemma on
the constant-diagram functor `Functor.const C : A ⥤ (C ⥤ A)`. For `C` nonempty, it does not only
preserve the limits that exist in `A` (Mathlib's `preservesLimits_const`): a limit in `C ⥤ A` of
a diagram of constant functors `F ⋙ const C` already gives a limit of `F` in `A`, at every object
of `C`, and the limit functor is constant. The corollary: `A` has whatever `C ⥤ A` has among
limits, colimits, a zero object, and the abelian property.

The proof does not use that limits in `C ⥤ A` are pointwise, which fails in general when `A`
lacks limits. Let `L` be a limit of `F ⋙ const C` with projections `π`. For each `d : C`, the
cone `π(d) : L(d) → F` induces `u_d : const L(d) ⟶ L`. The components `(u_d)_d` form an
endomorphism of `L` (naturality follows from `u_{d'} ∘ const L(f) = u_d`) compatible with `π`,
hence the identity. A map `v : X → L(d)` compatible with the cone is then recovered as the
component at `d` of the morphism `u_d ∘ const v`, which is fixed by the cone; this gives the
uniqueness that pointwise evaluation alone would not.

**What is proved.**
* `reflectsIsomorphisms_const` (instance): for `C` nonempty, `const C` reflects isomorphisms
  (faithfulness is Mathlib's instance in `Functor/Const.lean`).
* `isLimitEvalCone`: if `c` is a limit cone of `F ⋙ const C`, its evaluation at any `d : C` is a
  limit cone of `F`; `isColimitEvalCocone` is the dual.
* `isIso_pt_map`: the point of such a limit cone is a functor sending every arrow to an
  isomorphism (it is constant up to isomorphism).
* `createsLimitsOfSize_const`, `createsColimitsOfSize_const` (instances): **the lemma of the
  errata.** For `C` nonempty, `const C` creates all limits and colimits.
* `hasLimitsOfShape_of_functorCategory`, `hasColimitsOfShape_of_functorCategory`,
  `hasFiniteLimits_of_functorCategory`, `hasFiniteColimits_of_functorCategory`: limits of a shape
  in `C ⥤ A` give limits of that shape in `A`.
* `hasZeroObject_of_functorCategory`: **the corollary for zero objects.** If `C ⥤ A` has a zero
  object, so has `A`.
* `abelianOfFunctorCategory`: **the corollary for abelian categories,** for `A` preadditive:
  if `C ⥤ A`, with its pointwise preadditive structure, has finite limits and colimits and its
  coimage-image comparisons are isomorphisms (Stacks 0109, that is, `C ⥤ A` is abelian), then
  `A` is abelian.

**Not formalised.** The abelian corollary takes the preadditive structure of `A` as given; the
step that recovers it (addition of morphisms from biproducts and a zero object transferred from
`C ⥤ A`, then negatives) is not done. Th. 4 itself (the direct statement, `C ⥤ A` abelian when
`A` is) is Mathlib's `functorCategoryAbelian`.
-/

namespace Grothendieck.Bourbaki469

open CategoryTheory Limits Functor

universe w w' v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A]
variable {J : Type w} [Category.{w'} J] {F : J ⥤ A}

/-- For `C` nonempty, the constant-diagram functor reflects isomorphisms: the inverse of `f` is
the component, at any object, of the inverse of `const f`. -/
instance reflectsIsomorphisms_const [Nonempty C] :
    (const C : A ⥤ C ⥤ A).ReflectsIsomorphisms where
  reflects f _ :=
    (inferInstance : IsIso (((const C).map f).app (Classical.arbitrary C)))

/-- The evaluation at `d : C` of a cone over a diagram of constant functors, as a cone over the
diagram in `A`. -/
@[simps]
def evalCone (c : Cone (F ⋙ const C)) (d : C) : Cone F where
  pt := c.pt.obj d
  π :=
    { app j := (c.π.app j).app d
      naturality j j' f := by
        have := congrArg (NatTrans.app · d) (c.w f)
        simpa using this.symm }

/-- The dual: the evaluation at `d : C` of a cocone over a diagram of constant functors. -/
@[simps]
def evalCocone (c : Cocone (F ⋙ const C)) (d : C) : Cocone F where
  pt := c.pt.obj d
  ι :=
    { app j := (c.ι.app j).app d
      naturality j j' f := by
        have := congrArg (NatTrans.app · d) (c.w f)
        simpa using this }

section Limits

variable {c : Cone (F ⋙ const C)} (hc : IsLimit c)

/-- The morphism `const L(d) ⟶ L` induced by the cone `π(d) : L(d) → F`. -/
noncomputable def u (d : C) : (const C).obj (c.pt.obj d) ⟶ c.pt :=
  hc.lift ((const C).mapCone (evalCone c d))

@[reassoc (attr := simp)]
theorem u_π (d : C) (j : J) : u hc d ≫ c.π.app j = (const C).map ((c.π.app j).app d) :=
  hc.fac _ j

/-- `u_{d'} ∘ const L(f) = u_d` for `f : d ⟶ d'`. -/
theorem const_map_comp_u {d d' : C} (f : d ⟶ d') :
    (const C).map (c.pt.map f) ≫ u hc d' = u hc d := by
  refine hc.hom_ext fun j => ?_
  rw [Category.assoc, u_π, u_π, ← Functor.map_comp]
  congr 1
  simp

/-- The diagonal components of the `u_d` are identities. -/
theorem u_app_self (d : C) : (u hc d).app d = 𝟙 _ := by
  let w : c.pt ⟶ c.pt :=
    { app d := (u hc d).app d
      naturality d d' f := by
        have h1 := congrArg (NatTrans.app · d') (const_map_comp_u hc f)
        have h2 := (u hc d).naturality f
        simp only [NatTrans.comp_app, const_map_app] at h1
        simp only [const_obj_obj, const_obj_map, Category.id_comp] at h2
        rw [h1, h2] }
  have hw : w = 𝟙 _ := hc.hom_ext fun j => by
    ext d
    rw [NatTrans.comp_app, Category.id_comp]
    exact (NatTrans.comp_app (u hc d) (c.π.app j) d).symm.trans
      (congrArg (NatTrans.app · d) (u_π hc d j))
  exact congrArg (NatTrans.app · d) hw

include hc in
/-- The projections `π(d) : L(d) → F` are jointly monomorphic. -/
theorem hom_ext_eval (d : C) {X : A} {m m' : X ⟶ c.pt.obj d}
    (h : ∀ j, m ≫ (c.π.app j).app d = m' ≫ (c.π.app j).app d) : m = m' := by
  have key : (const C).map m ≫ u hc d = (const C).map m' ≫ u hc d :=
    hc.hom_ext fun j => by
      rw [Category.assoc, Category.assoc, u_π, ← Functor.map_comp, ← Functor.map_comp, h]
  have := congrArg (NatTrans.app · d) key
  simpa [u_app_self] using this

include hc in
/-- **The lemma of the errata.** The evaluation at any `d : C` of a limit cone of
`F ⋙ const C` is a limit cone of `F`. -/
noncomputable def isLimitEvalCone (d : C) : IsLimit (evalCone c d) where
  lift s := (hc.lift ((const C).mapCone s)).app d
  fac s j :=
    (NatTrans.comp_app _ _ _).symm.trans (congrArg (NatTrans.app · d) (hc.fac _ j))
  uniq s m hm := hom_ext_eval hc d fun j => by
    have e : (hc.lift ((const C).mapCone s)).app d ≫ (c.π.app j).app d = s.π.app j :=
      (NatTrans.comp_app _ _ _).symm.trans
        (congrArg (NatTrans.app · d) (hc.fac ((const C).mapCone s) j))
    exact (hm j).trans e.symm

include hc in
/-- The point of a limit cone of `F ⋙ const C` sends every arrow to an isomorphism: it is
constant up to isomorphism. -/
theorem isIso_pt_map {d d' : C} (f : d ⟶ d') : IsIso (c.pt.map f) := by
  have h : c.pt.map f = ((isLimitEvalCone hc d').conePointUniqueUpToIso
      (isLimitEvalCone hc d)).inv := by
    refine hom_ext_eval hc d' fun j => ?_
    have h1 := IsLimit.conePointUniqueUpToIso_inv_comp (isLimitEvalCone hc d')
      (isLimitEvalCone hc d) j
    have h2 := (c.π.app j).naturality f
    have h3 : ((F ⋙ const C).obj j).map f = 𝟙 _ := rfl
    rw [h3, Category.comp_id] at h2
    exact h2.trans h1.symm
  rw [h]
  exact Iso.isIso_inv _

end Limits

section Colimits

variable {c : Cocone (F ⋙ const C)} (hc : IsColimit c)

/-- The morphism `L ⟶ const L(d)` induced by the cocone `ι(d) : F → L(d)`. -/
noncomputable def v (d : C) : c.pt ⟶ (const C).obj (c.pt.obj d) :=
  hc.desc ((const C).mapCocone (evalCocone c d))

@[reassoc (attr := simp)]
theorem ι_v (d : C) (j : J) : c.ι.app j ≫ v hc d = (const C).map ((c.ι.app j).app d) :=
  hc.fac _ j

/-- `const L(f) ∘ v_d = v_{d'}` for `f : d ⟶ d'`. -/
theorem v_comp_const_map {d d' : C} (f : d ⟶ d') :
    v hc d ≫ (const C).map (c.pt.map f) = v hc d' := by
  refine hc.hom_ext fun j => ?_
  rw [ι_v_assoc, ι_v, ← Functor.map_comp]
  congr 1
  have := (c.ι.app j).naturality f
  simpa using this.symm

/-- The diagonal components of the `v_d` are identities. -/
theorem v_app_self (d : C) : (v hc d).app d = 𝟙 _ := by
  let w : c.pt ⟶ c.pt :=
    { app d := (v hc d).app d
      naturality d d' f := by
        have h1 := congrArg (NatTrans.app · d) (v_comp_const_map hc f)
        have h2 := (v hc d').naturality f
        simp only [NatTrans.comp_app, const_map_app] at h1
        simp only [const_obj_obj, const_obj_map, Category.comp_id] at h2
        rw [h2, ← h1] }
  have hw : w = 𝟙 _ := hc.hom_ext fun j => by
    ext d
    rw [NatTrans.comp_app, Category.comp_id]
    exact (NatTrans.comp_app (c.ι.app j) (v hc d) d).symm.trans
      (congrArg (NatTrans.app · d) (ι_v hc d j))
  exact congrArg (NatTrans.app · d) hw

include hc in
/-- The coprojections `ι(d) : F → L(d)` are jointly epimorphic. -/
theorem hom_ext_eval' (d : C) {X : A} {m m' : c.pt.obj d ⟶ X}
    (h : ∀ j, (c.ι.app j).app d ≫ m = (c.ι.app j).app d ≫ m') : m = m' := by
  have key : v hc d ≫ (const C).map m = v hc d ≫ (const C).map m' :=
    hc.hom_ext fun j => by
      rw [ι_v_assoc, ι_v_assoc, ← Functor.map_comp, ← Functor.map_comp, h]
  have := congrArg (NatTrans.app · d) key
  simpa [v_app_self] using this

include hc in
/-- The dual lemma: the evaluation at any `d : C` of a colimit cocone of `F ⋙ const C` is a
colimit cocone of `F`. -/
noncomputable def isColimitEvalCocone (d : C) : IsColimit (evalCocone c d) where
  desc s := (hc.desc ((const C).mapCocone s)).app d
  fac s j :=
    (NatTrans.comp_app _ _ _).symm.trans (congrArg (NatTrans.app · d) (hc.fac _ j))
  uniq s m hm := hom_ext_eval' hc d fun j => by
    have e : (c.ι.app j).app d ≫ (hc.desc ((const C).mapCocone s)).app d = s.ι.app j :=
      (NatTrans.comp_app _ _ _).symm.trans
        (congrArg (NatTrans.app · d) (hc.fac ((const C).mapCocone s) j))
    exact (hm j).trans e.symm

end Colimits

variable (C A) in
/-- **The lemma of the errata, rédaction n° 469, p. 52.** For `C` nonempty, the constant-diagram
functor `A ⥤ (C ⥤ A)` creates all limits. -/
noncomputable instance createsLimitsOfSize_const [Nonempty C] :
    CreatesLimitsOfSize.{w, w'} (const C : A ⥤ C ⥤ A) where
  CreatesLimitsOfShape :=
    { CreatesLimit := createsLimitOfReflectsIso fun c t =>
        { liftedCone := evalCone c (Classical.arbitrary C)
          validLift := (isLimitOfPreserves (const C)
            (isLimitEvalCone t (Classical.arbitrary C))).uniqueUpToIso t
          makesLimit := isLimitEvalCone t (Classical.arbitrary C) } }

variable (C A) in
/-- The dual: for `C` nonempty, the constant-diagram functor creates all colimits. -/
noncomputable instance createsColimitsOfSize_const [Nonempty C] :
    CreatesColimitsOfSize.{w, w'} (const C : A ⥤ C ⥤ A) where
  CreatesColimitsOfShape :=
    { CreatesColimit := createsColimitOfReflectsIso fun c t =>
        { liftedCocone := evalCocone c (Classical.arbitrary C)
          validLift := (isColimitOfPreserves (const C)
            (isColimitEvalCocone t (Classical.arbitrary C))).uniqueUpToIso t
          makesColimit := isColimitEvalCocone t (Classical.arbitrary C) } }

variable (C) in
/-- If `C` is nonempty and `C ⥤ A` has limits of shape `J`, so has `A`. -/
theorem hasLimitsOfShape_of_functorCategory [Nonempty C] [HasLimitsOfShape J (C ⥤ A)] :
    HasLimitsOfShape J A :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (const C : A ⥤ C ⥤ A)

variable (C) in
/-- If `C` is nonempty and `C ⥤ A` has colimits of shape `J`, so has `A`. -/
theorem hasColimitsOfShape_of_functorCategory [Nonempty C] [HasColimitsOfShape J (C ⥤ A)] :
    HasColimitsOfShape J A :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (const C : A ⥤ C ⥤ A)

variable (C) in
/-- If `C` is nonempty and `C ⥤ A` has finite limits, so has `A`. -/
theorem hasFiniteLimits_of_functorCategory [Nonempty C] [HasFiniteLimits (C ⥤ A)] :
    HasFiniteLimits A :=
  ⟨fun _ _ _ => hasLimitsOfShape_of_functorCategory C⟩

variable (C) in
/-- If `C` is nonempty and `C ⥤ A` has finite colimits, so has `A`. -/
theorem hasFiniteColimits_of_functorCategory [Nonempty C] [HasFiniteColimits (C ⥤ A)] :
    HasFiniteColimits A :=
  ⟨fun _ _ _ => hasColimitsOfShape_of_functorCategory C⟩

variable (C) in
/-- **The corollary for zero objects.** If `C` is nonempty and `C ⥤ A` has a zero object, so
has `A`: the value at any object of a zero object of `C ⥤ A` is a zero object of `A`. -/
theorem hasZeroObject_of_functorCategory [Nonempty C] [HasZeroObject (C ⥤ A)] :
    HasZeroObject A := by
  obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := C ⥤ A)
  let d := Classical.arbitrary C
  let E := Functor.empty.{0} A
  let c : Cone (E ⋙ const C) := { pt := Z, π := { app j := j.as.elim, naturality j := j.as.elim } }
  let c' : Cocone (E ⋙ const C) :=
    { pt := Z, ι := { app j := j.as.elim, naturality j := j.as.elim } }
  have ht : IsTerminal (Z.obj d) :=
    isLimitEquivIsTerminalOfIsEmpty A _
      (isLimitEvalCone ((isLimitEquivIsTerminalOfIsEmpty (C ⥤ A) c).symm hZ.isTerminal) d)
  have hi : IsInitial (Z.obj d) :=
    isColimitEquivIsInitialOfIsEmpty A _
      (isColimitEvalCocone ((isColimitEquivIsInitialOfIsEmpty (C ⥤ A) c').symm hZ.isInitial) d)
  exact ⟨⟨Z.obj d, ⟨fun Y => ⟨⟨⟨hi.to Y⟩, fun _ => hi.hom_ext _ _⟩⟩,
    fun Y => ⟨⟨⟨ht.from Y⟩, fun _ => ht.hom_ext _ _⟩⟩⟩⟩⟩

/-- **The corollary for abelian categories.** Let `A` be preadditive and `C` nonempty. If the
functor category `C ⥤ A`, with its pointwise preadditive structure, has finite limits and finite
colimits and all its coimage-image comparisons are isomorphisms (that is, `C ⥤ A` is abelian),
then `A` is abelian. -/
@[instance_reducible]
noncomputable def abelianOfFunctorCategory [Preadditive A] [Nonempty C]
    [HasFiniteLimits (C ⥤ A)] [HasFiniteColimits (C ⥤ A)]
    (h : ∀ {G H : C ⥤ A} (α : G ⟶ H), IsIso (Abelian.coimageImageComparison α)) :
    Abelian A := by
  haveI := hasFiniteLimits_of_functorCategory (A := A) C
  haveI := hasFiniteColimits_of_functorCategory (A := A) C
  haveI : (const C : A ⥤ C ⥤ A).PreservesZeroMorphisms := ⟨fun _ _ => by ext; simp⟩
  have : ∀ {X Y : A} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    have := h ((const C).map f)
    have : IsIso ((const C).map (Abelian.coimageImageComparison f)) := by
      rw [Arrow.isIso_iff_isIso_of_isIso
        (Abelian.PreservesCoimageImageComparison.iso (const C) f).hom]
      infer_instance
    exact isIso_of_reflects_iso _ (const C)
  exact Abelian.ofCoimageImageComparisonIsIso

end Grothendieck.Bourbaki469
