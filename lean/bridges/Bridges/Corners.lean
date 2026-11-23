/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.DeMorgan
public import Bridges.EssentialPoints

import Bridges.Monoids

/-!
# Corners of monoids

For an idempotent `e` of a monoid `M`, the corner `eMe` is the monoid `CornerMonoid e he` of the
elements `x` with `e * x = x = x * e`, with unit `e`. If `1` factors through `e`, that is
`r * e * s = 1` for some `r s : M`, then `M` and `eMe` are Morita equivalent: their Karoubi
envelopes are equivalent (`karoubiCornerEquiv`), the functor sending the object of
`SingleObj (eMe)` to the idempotent `e` being fully faithful, and every idempotent `p` of `M`
being a retract of `e`, through `e * s * p` and `p * r * e`.

* `forall_exists_mul_eq_mul_iff_cornerMonoid`: then `M` has common right multiples,
  `∀ a b, ∃ c d, a * c = b * d`, iff `eMe` has. The direct algebraic proof: common right
  multiples in `M` give common right multiples `e * c * e`, `e * d * e` in `eMe`; conversely, a
  common right multiple of `e * s * a * r * e` and `e * s * b * r * e` in `eMe`, multiplied on
  the left by `r`, gives one of `a` and `b`;
* `moritaEquivalentCat_cornerMonoid`, `rightOreCondition_singleObj_iff_cornerMonoid`: the same
  equivalence read through the bridge `rightOreCondition_iff_of_moritaEquivalentCat`, and
  `isDeMorganTopos_singleObj_iff_cornerMonoid` for the topoi of right sets;
* `forall_isUnit_iff_cornerMonoid`: the Morita invariance of groupoids gives, in the same way,
  that `M` is a group iff `eMe` is.
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory Idempotents

section Corner

variable {M : Type} [Monoid M] {e : M} (he : IsIdempotentElem e)

/-- The corner monoid `eMe` of an idempotent `e`: the elements `x` with `e * x = x` and
`x * e = x`, with unit `e`. -/
structure CornerMonoid (e : M) (he : IsIdempotentElem e) : Type where
  /-- The underlying element of `M`. -/
  val : M
  mul_left : e * val = val
  mul_right : val * e = val

variable {he} in
@[ext]
theorem CornerMonoid.ext {x y : CornerMonoid e he} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance : Monoid (CornerMonoid e he) where
  mul x y := ⟨x.val * y.val, by rw [← mul_assoc, x.mul_left], by rw [mul_assoc, y.mul_right]⟩
  one := ⟨e, he.eq, he.eq⟩
  mul_assoc x y z := CornerMonoid.ext (mul_assoc x.val y.val z.val)
  one_mul x := CornerMonoid.ext x.mul_left
  mul_one x := CornerMonoid.ext x.mul_right

namespace CornerMonoid

variable {he}

@[simp]
theorem val_mul (x y : CornerMonoid e he) : (x * y).val = x.val * y.val :=
  rfl

@[simp]
theorem val_one : (1 : CornerMonoid e he).val = e :=
  rfl

variable (he) in
/-- The element `e * z * e` of the corner monoid. -/
def mk' (z : M) : CornerMonoid e he :=
  ⟨e * z * e, by rw [← mul_assoc, ← mul_assoc, he.eq], by rw [mul_assoc, he.eq]⟩

@[simp]
theorem val_mk' (z : M) : (mk' he z).val = e * z * e :=
  rfl

/-- An element `x` of the corner monoid satisfies `e * x * e = x`. -/
theorem mul_val_mul (x : CornerMonoid e he) : e * x.val * e = x.val := by
  rw [x.mul_left, x.mul_right]

end CornerMonoid

/-- The functor sending the object of `SingleObj (eMe)` to the idempotent `e`, as an object of the
Karoubi envelope of `SingleObj M`. -/
def cornerFunctor : SingleObj (CornerMonoid e he) ⥤ Karoubi (SingleObj M) where
  obj _ := karoubiMk e he
  map x := ⟨x.val, CornerMonoid.mul_val_mul x⟩
  map_id _ := Karoubi.hom_ext _ _ rfl
  map_comp _ _ := Karoubi.hom_ext _ _ rfl

instance : (cornerFunctor he).Faithful where
  map_injective h := CornerMonoid.ext (congrArg Karoubi.Hom.f h)

instance : (cornerFunctor he).Full where
  map_surjective φ := by
    have h : e * φ.f * e = φ.f := φ.comm
    refine ⟨⟨φ.f, ?_, ?_⟩, Karoubi.hom_ext _ _ rfl⟩
    · rw [← h, ← mul_assoc, ← mul_assoc, he.eq]
    · rw [← h, mul_assoc, he.eq]

/-- An idempotent `p` satisfies `p * (p * x) = p * x`. -/
theorem mul_self_mul {N : Type} [Monoid N] {p : N} (hp : p * p = p) (x : N) :
    p * (p * x) = p * x := by
  rw [← mul_assoc, hp]

variable {r s : M}

/-- **Corners.** If `r * e * s = 1`, the monoid `M` has common right multiples iff its corner
`eMe` has. -/
theorem forall_exists_mul_eq_mul_iff_cornerMonoid (hrs : r * e * s = 1) :
    (∀ a b : M, ∃ c d : M, a * c = b * d) ↔
      ∀ x y : CornerMonoid e he, ∃ u v : CornerMonoid e he, x * u = y * v := by
  constructor
  · intro h x y
    obtain ⟨c, d, hcd⟩ := h x.val y.val
    refine ⟨CornerMonoid.mk' he c, CornerMonoid.mk' he d, CornerMonoid.ext ?_⟩
    simp only [CornerMonoid.val_mul, CornerMonoid.val_mk', ← mul_assoc, x.mul_right, y.mul_right,
      hcd]
  · intro h a b
    obtain ⟨u, v, huv⟩ := h (CornerMonoid.mk' he (s * a * r)) (CornerMonoid.mk' he (s * b * r))
    refine ⟨r * e * u.val, r * e * v.val, ?_⟩
    have key := congrArg (r * ·) (congrArg CornerMonoid.val huv)
    simp only [CornerMonoid.val_mul, CornerMonoid.val_mk', ← mul_assoc, hrs, one_mul] at key
    simpa only [← mul_assoc] using key

/-- Every object of the Karoubi envelope of `SingleObj M` is a retract of the idempotent `e`, as
`r * e * s = 1`. -/
def retractCorner (hrs : r * e * s = 1) (P : Karoubi (SingleObj M)) :
    Retract P ((cornerFunctor he).obj (SingleObj.star _)) where
  i := ⟨e * s * P.p, by
    change e * (e * s * P.p) * P.p = e * s * P.p
    have hp : P.p * P.p = P.p := P.idem
    simp only [mul_assoc, mul_self_mul he.eq, hp]⟩
  r := ⟨P.p * r * e, by
    change P.p * (P.p * r * e) * e = P.p * r * e
    simp only [mul_assoc, mul_self_mul P.idem, he.eq]⟩
  retract := by
    apply Karoubi.hom_ext
    change P.p * r * e * (e * s * P.p) = P.p
    have hp : P.p * P.p = P.p := P.idem
    calc P.p * r * e * (e * s * P.p) = P.p * (r * (e * e) * s) * P.p := by
          simp only [mul_assoc]
      _ = P.p := by rw [he.eq, hrs, mul_one, hp]

/-- If `r * e * s = 1`, the Karoubi envelopes of `SingleObj (eMe)` and `SingleObj M` are
equivalent. -/
noncomputable def karoubiCornerEquiv (hrs : r * e * s = 1) :
    Karoubi (SingleObj (CornerMonoid e he)) ≌ Karoubi (SingleObj M) :=
  karoubiEquivOfRetract (cornerFunctor he) fun P => ⟨SingleObj.star _, ⟨retractCorner he hrs P⟩⟩

/-- If `r * e * s = 1`, the monoids `eMe` and `M` are Morita equivalent: their topoi of right
sets are equivalent. -/
theorem moritaEquivalentCat_cornerMonoid (hrs : r * e * s = 1) :
    MoritaEquivalentCat (SingleObj (CornerMonoid e he)) (SingleObj M) := by
  rw [moritaEquivalentCat_iff_karoubi]
  exact ⟨karoubiCornerEquiv he hrs⟩

/-- **Corners through the Ore bridge.** If `r * e * s = 1`, `SingleObj M` satisfies the right
Ore condition iff `SingleObj (eMe)` does, by Morita invariance. -/
theorem rightOreCondition_singleObj_iff_cornerMonoid (hrs : r * e * s = 1) :
    GrothendieckTopology.RightOreCondition (SingleObj M) ↔
      GrothendieckTopology.RightOreCondition (SingleObj (CornerMonoid e he)) :=
  (rightOreCondition_iff_of_moritaEquivalentCat (moritaEquivalentCat_cornerMonoid he hrs)).symm

/-- If `r * e * s = 1`, the topos of right `M`-sets is De Morgan iff the topos of right
`eMe`-sets is. -/
theorem isDeMorganTopos_singleObj_iff_cornerMonoid (hrs : r * e * s = 1) :
    IsDeMorganTopos ((SingleObj M)ᵒᵖ ⥤ Type) ↔
      IsDeMorganTopos ((SingleObj (CornerMonoid e he))ᵒᵖ ⥤ Type) := by
  rw [isDeMorganTopos_presheaf_iff_rightOreCondition,
    isDeMorganTopos_presheaf_iff_rightOreCondition]
  exact rightOreCondition_singleObj_iff_cornerMonoid he hrs

/-- **Corners and groups.** If `r * e * s = 1`, the monoid `M` is a group iff its corner `eMe`
is, by Morita invariance of groupoids. -/
theorem forall_isUnit_iff_cornerMonoid (hrs : r * e * s = 1) :
    (∀ m : M, IsUnit m) ↔ ∀ x : CornerMonoid e he, IsUnit x := by
  rw [← isGroupoid_singleObj_iff, ← isGroupoid_singleObj_iff]
  exact (isGroupoid_iff_of_moritaEquivalentCat (moritaEquivalentCat_cornerMonoid he hrs)).symm

end Corner

end LeanPool.ToposTheoreticBridges.Examples
