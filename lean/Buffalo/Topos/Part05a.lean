import Mathlib

/-!
# Buffalo, topos theory, part 5a: adding arrows, combining theories, additive categories (late June 1973)

Entries of `docs/buffalo-topos/index.tex` lines 679–712 (video `PqCQM3Pcl6Q`, 9:02:23–10:12:40):
rule 3 (adding arrows) and rule 4 (combining theories), the limits of the faithfulness criterion
for generating families, and additive categories as an exactness property. The status of each
entry is in `docs/buffalo-topos/lean/Part05.json`.

Mathlib has no 2-category `Cat_D` of categories with limits of type `D`, no `D`-envelopes and no
2-representable theories `T_R = Hom_D(R, -)`; the statements below are the faithful special cases
it carries: `D = ∅` (bare categories, where envelopes are free categories, quotients and
Gabriel–Zisman localizations), and the exactness facts behind each step.
-/

universe w v u v' u'

open CategoryTheory Limits

namespace Buffalo.Topos.Part05

noncomputable section

/-! ## Adding arrows -/

/-- PqCQM3Pcl6Q-32543 (9:02:23) [ex] Extra structure on a group `G` by adding an arrow between
constructions on `G`, e.g. a map `G^ab → G × G` (here in sets). -/
structure GroupWithArrow where
  /-- the underlying set -/
  G : Type u
  [grp : Group G]
  /-- the added arrow -/
  arrow : Abelianization G → G × G

/-- ... or a map `G³ → G⁴`. -/
structure GroupWithArrow' where
  /-- the underlying set -/
  G : Type u
  [grp : Group G]
  /-- the added arrow -/
  arrow : G × G × G → G × G × G × G

/-- Every group carries such structures (e.g. the trivial arrow): adding an arrow is adding data,
not imposing a condition. -/
def GroupWithArrow.trivial (G : Type u) [Group G] : GroupWithArrow.{u} := ⟨G, fun _ => 1⟩

/-- PqCQM3Pcl6Q-32664 (9:04:24) [prop] Adding arrows `H` to the empty structure on objects:
for `D = ∅` the theory « objects `F(i)` and arrows `F(h)` » is represented by the free category
on the quiver `(I, H)`: functors out of it are exactly the prefunctors (`Quiv.adj`). -/
def freeCategory_represents (Q : Quiv.{max u v, u}) (C : Cat.{max u v, u}) :
    (Cat.free.obj Q ⟶ C) ≃ (Q ⟶ Quiv.forget.obj C) :=
  Quiv.adj.homEquiv Q C

/-! ## Combining theories -/

/-- PqCQM3Pcl6Q-33138 (9:12:18) [def] Rule 4: the product of two theories is represented by the
2-sum of the representing categories; for `D = ∅`, functors out of a sum are pairs of functors
(`Sum.functorEquiv`). -/
def sum_represents_product (A A' B : Type u) [Category.{v} A] [Category.{v} A'] [Category.{v} B] :
    (A ⊕ A' ⥤ B) ≌ (A ⥤ B) × (A' ⥤ B) :=
  Sum.functorEquiv A A' B

/-- PqCQM3Pcl6Q-33551 (9:19:11) [ex] A ring is a Lie ring under the commutator bracket
(`LieRing.ofAssociativeRing`, `Ring.lie_def`). -/
theorem ring_lie_bracket (A : Type*) [Ring A] (x y : A) : ⁅x, y⁆ = x * y - y * x :=
  Ring.lie_def x y

/-- PqCQM3Pcl6Q-34019 (9:26:59) [prop] For `D = ∅`: a small category `R` is recovered from the
empty structure on `Ob R` by adding its arrows as formal arrows (the path category) and imposing
that composites be respected (`quotientPathsEquiv`). -/
def quotientPaths_equiv (R : Type u) [Category.{v} R] :
    Quotient (pathsHomRel R) ≌ R :=
  quotientPathsEquiv R

/-! ## Making arrows equal -/

/-- PqCQM3Pcl6Q-34369 (9:32:49) [prop] For `D = ∅`, making given pairs of arrows equal is solved
by the quotient category (`CategoryTheory.Quotient.lift`). -/
def quotient_lift {C : Type u} [Category.{v} C] (r : HomRel C) {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂) :
    Quotient r ⥤ D :=
  CategoryTheory.Quotient.lift r F H

/-- ... and in the presence of equalizers it reduces to inverting arrows: a functor preserving the
equalizer of `f, g` makes `f` and `g` equal iff it inverts `Ker(f, g) → X` (also
4gynb9uTEE4-11824). -/
theorem map_eq_iff_isIso_map_ι {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {X Y : C} (f g : X ⟶ Y) [HasEqualizer f g] (F : C ⥤ D)
    [PreservesLimit (parallelPair f g) F] :
    F.map f = F.map g ↔ IsIso (F.map (equalizer.ι f g)) := by
  constructor
  · intro h
    have hl := (isLimitMapConeForkEquiv F (equalizer.condition f g))
      (isLimitOfPreserves F (equalizerIsEqualizer f g))
    exact isIso_limit_cone_parallelPair_of_eq h hl
  · intro h
    rw [← cancel_epi (F.map (equalizer.ι f g)), ← F.map_comp, ← F.map_comp, equalizer.condition]

/-! ## Generating families: limits of the criterion -/

/-- In a preorder, `x` with both projections the identity is a product of `x` with itself. -/
def preorderBinaryFanIsLimit {R : Type u} [Preorder R] (x : R) :
    IsLimit (BinaryFan.mk (𝟙 x) (𝟙 x)) :=
  BinaryFan.IsLimit.mk _ (fun f _ => f) (fun _ _ => Subsingleton.elim _ _)
    (fun _ _ => Subsingleton.elim _ _) (fun _ _ _ _ _ => Subsingleton.elim _ _)

/-- A functor out of a preorder preserving binary products takes subterminal values: any two
arrows into `G(x)` are equal. -/
theorem eq_of_preservesBinaryProducts {R : Type u} [Preorder R] {C : Type u'} [Category.{v'} C]
    (G : R ⥤ C) [PreservesLimitsOfShape (Discrete WalkingPair) G] (x : R) {Z : C}
    (a b : Z ⟶ G.obj x) : a = b := by
  have hl := (isLimitMapConeBinaryFanEquiv G (𝟙 x) (𝟙 x))
    (isLimitOfPreserves G (preorderBinaryFanIsLimit x))
  obtain ⟨l, hl₁, hl₂⟩ := BinaryFan.IsLimit.lift' hl a b
  rw [← hl₁, ← hl₂]
  simp

/-- PqCQM3Pcl6Q-35544 (9:52:24) [prop] If `R` is a lattice (indeed any preorder) and the functors
preserve the finite meets, then `Hom_D(R, C)` is a preordered category: between two such functors
there is at most one natural transformation. -/
theorem natTrans_subsingleton {R : Type u} [Preorder R] {C : Type u'} [Category.{v'} C]
    (F G : R ⥤ C) [PreservesLimitsOfShape (Discrete WalkingPair) G] :
    Subsingleton (F ⟶ G) :=
  ⟨fun _ _ => NatTrans.ext (funext fun x => eq_of_preservesBinaryProducts G x _ _)⟩

/-- ... so every functor out of such a category is faithful: the faithfulness condition on `I`
is empty (also PqCQM3Pcl6Q-35722 and 4gynb9uTEE4-7434). -/
theorem faithful_of_subsingleton_hom {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (h : ∀ X Y : A, Subsingleton (X ⟶ Y)) (Φ : A ⥤ B) : Φ.Faithful :=
  ⟨fun {X Y} _ _ _ => (h X Y).elim _ _⟩

/-! ## Additive categories as an exactness property -/

/-- PqCQM3Pcl6Q-36352 (10:05:52) [def] Semi-additive: zero object (initial = final) and binary
biproducts (`X ⊔ Y → X × Y` an isomorphism); in Mathlib, `HasZeroObject` and
`HasBinaryBiproducts`, the biproduct being both a product and a coproduct. -/
def biprodIsLimit {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    (X Y : C) : IsLimit (BinaryFan.mk (biprod.fst : X ⊞ Y ⟶ X) biprod.snd) :=
  BinaryBiproduct.isLimit X Y

/-- ... and a coproduct. -/
def biprodIsColimit {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    (X Y : C) : IsColimit (BinaryCofan.mk (biprod.inl : X ⟶ X ⊞ Y) biprod.inr) :=
  BinaryBiproduct.isColimit X Y

section Semiadditive

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

attribute [local instance] SemiadditiveOfBinaryBiproducts.addCommMonoidHomOfHasBinaryBiproducts

/-- PqCQM3Pcl6Q-36465 (10:07:45) [prop] In a semi-additive category the Hom-sets are commutative
monoids (Eckmann–Hilton, `SemiadditiveOfBinaryBiproducts.addCommMonoidHomOfHasBinaryBiproducts`),
composition being biadditive. -/
theorem hom_add_comm (X Y : C) (f g : X ⟶ Y) : f + g = g + f := add_comm f g

theorem hom_add_comp {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫ h :=
  SemiadditiveOfBinaryBiproducts.add_comp f g h

theorem hom_comp_add {X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫ h :=
  SemiadditiveOfBinaryBiproducts.comp_add f g h

/-- The shear map `(x, y) ↦ (x, x + y)` of `X ⊞ X`. -/
def shear (X : C) : X ⊞ X ⟶ X ⊞ X := biprod.lift biprod.fst (biprod.fst + biprod.snd)

/-- PqCQM3Pcl6Q-36577 (10:09:37) [prop] « The monoid `X` is a group » is an exactness property:
the shear map `(x, y) ↦ (x, x + y)` of `X ⊞ X` is an isomorphism iff `𝟙 X` has an opposite
(equivalently every `Hom(Y, X)` is a group, `f ↦ f ≫ n` being the negation). -/
theorem isIso_shear_iff (X : C) : IsIso (shear X) ↔ ∃ n : X ⟶ X, 𝟙 X + n = 0 := by
  constructor
  · intro h
    refine ⟨biprod.inl ≫ inv (shear X) ≫ biprod.snd, ?_⟩
    have e₁ : inv (shear X) ≫ biprod.fst = biprod.fst := by
      rw [IsIso.inv_comp_eq]; simp [shear]
    have e₂ : inv (shear X) ≫ (biprod.fst + biprod.snd) = biprod.snd := by
      rw [IsIso.inv_comp_eq]; simp [shear]
    have h₁ : biprod.inl ≫ inv (shear X) ≫ biprod.fst = 𝟙 X := by rw [e₁]; simp
    have h₂ : biprod.inl ≫ inv (shear X) ≫ (biprod.fst + biprod.snd) = 0 := by rw [e₂]; simp
    rw [hom_comp_add, hom_comp_add, h₁] at h₂
    exact h₂
  · rintro ⟨n, hn⟩
    let t : X ⊞ X ⟶ X ⊞ X := biprod.lift biprod.fst (biprod.fst ≫ n + biprod.snd)
    have key : biprod.fst + biprod.fst ≫ n = (0 : X ⊞ X ⟶ X) := by
      rw [← Category.comp_id (biprod.fst : X ⊞ X ⟶ X), Category.assoc, Category.id_comp,
        ← hom_comp_add, hn, comp_zero]
    refine ⟨t, ?_, ?_⟩
    · apply biprod.hom_ext
      · simp [shear, t]
      · simp only [shear, t, Category.assoc, biprod.lift_snd, Category.id_comp]
        rw [hom_comp_add, ← Category.assoc, biprod.lift_fst, biprod.lift_snd, ← add_assoc,
          add_comm (biprod.fst ≫ n), key, zero_add]
    · apply biprod.hom_ext
      · simp [shear, t]
      · simp only [shear, t, Category.assoc, biprod.lift_snd, Category.id_comp]
        rw [hom_comp_add, biprod.lift_fst, biprod.lift_snd, ← add_assoc, key, zero_add]

end Semiadditive

/-- The same exactness property in sets: a monoid is a group iff its shear map
`(x, y) ↦ (x, x y)` is bijective. -/
theorem monoid_shear_bijective_iff (M : Type u) [Monoid M] :
    Function.Bijective (fun p : M × M => (p.1, p.1 * p.2)) ↔ ∀ x : M, IsUnit x := by
  constructor
  · intro h x
    obtain ⟨⟨a, b⟩, hab⟩ := h.2 (x, 1)
    simp only [Prod.mk.injEq] at hab
    obtain ⟨rfl, hb⟩ := hab
    obtain ⟨⟨c, d⟩, hcd⟩ := h.2 (b, 1)
    simp only [Prod.mk.injEq] at hcd
    obtain ⟨rfl, hd⟩ := hcd
    -- `a b = 1` and `b d = 1`, so `a = d` and `b` is the inverse of `a`.
    have had : a = d := by
      calc a = a * (c * d) := by rw [hd, mul_one]
        _ = (a * c) * d := (mul_assoc _ _ _).symm
        _ = d := by rw [hb, one_mul]
    subst had
    exact ⟨⟨a, c, hb, hd⟩, rfl⟩
  · intro h
    refine ⟨fun p q hpq => ?_, fun q => ?_⟩
    · simp only [Prod.mk.injEq] at hpq
      obtain ⟨h₁, h₂⟩ := hpq
      rw [h₁] at h₂
      exact Prod.ext h₁ ((h q.1).mul_left_cancel h₂)
    · obtain ⟨u, hu⟩ := h q.1
      refine ⟨(q.1, ↑u⁻¹ * q.2), ?_⟩
      refine Prod.ext rfl ?_
      simp [← hu, ← mul_assoc]

end

end Buffalo.Topos.Part05
