/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.EssentialPoints
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Essential points of the topos of `M`-sets

For a monoid `M`, the bridge `essentialPointEquivKaroubiOp` identifies the essential points of
the topos `(SingleObj M)ᵒᵖ ⥤ Type` of right `M`-sets with the opposite of the Karoubi envelope of
`SingleObj M`. An object of `Karoubi (SingleObj M)` is an idempotent `e` of `M`
(`karoubiMk`, `karoubiMk_eta`), and a morphism `e ⟶ f` is an `a : M` with `f * a * e = a`
(composition in `SingleObj M` is `g ≫ h = h * g`). Hence:

* `nonempty_karoubiMk_iso_iff`, `nonempty_essentialPoint_iso_iff`: the essential points attached
  to idempotents `e` and `f` are isomorphic iff there are `a b : M` with `f * a * e = a`,
  `e * b * f = b`, `b * a = e` and `a * b = f`;
* `exists_iso_essentialPoint`: every essential point is isomorphic to one attached to an
  idempotent;
* `essentialPointEndMulEquiv`: the endomorphisms of the point attached to `1` form the monoid
  `Mᵐᵒᵖ`; for a group `G`, every essential point is isomorphic to it
  (`nonempty_essentialPoint_iso_of_group`), and its endomorphism monoid is `G`;
* `essentialPointClassesEquivFin`: for the monoid of `n × n` matrices over a field, the
  isomorphism classes of essential points are in bijection with `{0, …, n}`, by the rank of the
  idempotent (`karoubiRel_iff_rank_eq`).
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory Opposite Idempotents

section Monoid

variable {M : Type} [Monoid M]

/-- The object of the Karoubi envelope of `SingleObj M` given by an idempotent of `M`. -/
def karoubiMk (e : M) (he : IsIdempotentElem e) : Karoubi (SingleObj M) :=
  ⟨SingleObj.star M, e, he⟩

/-- Every object of the Karoubi envelope of `SingleObj M` comes from an idempotent of `M`. -/
theorem karoubiMk_eta (P : Karoubi (SingleObj M)) : karoubiMk P.p P.idem = P := by
  obtain ⟨⟨⟩, p, hp⟩ := P
  rfl

/-- The relation between idempotents `e`, `f` of `M` saying that `e` and `f` give isomorphic
objects of the Karoubi envelope. -/
def KaroubiRel (e f : M) : Prop :=
  ∃ a b : M, f * a * e = a ∧ e * b * f = b ∧ b * a = e ∧ a * b = f

/-- `KaroubiRel` is symmetric. -/
theorem KaroubiRel.symm {e f : M} (h : KaroubiRel e f) : KaroubiRel f e := by
  obtain ⟨a, b, ha, hb, hba, hab⟩ := h
  exact ⟨b, a, hb, ha, hab, hba⟩

/-- Two idempotents give isomorphic objects of the Karoubi envelope of `SingleObj M` iff they
are related by `KaroubiRel`. -/
theorem nonempty_karoubiMk_iso_iff {e f : M} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) :
    Nonempty (karoubiMk e he ≅ karoubiMk f hf) ↔ KaroubiRel e f := by
  constructor
  · rintro ⟨i⟩
    refine ⟨i.hom.f, i.inv.f, i.hom.comm, i.inv.comm, ?_, ?_⟩
    · exact congrArg Karoubi.Hom.f i.hom_inv_id
    · exact congrArg Karoubi.Hom.f i.inv_hom_id
  · rintro ⟨a, b, ha, hb, hba, hab⟩
    exact ⟨{ hom := ⟨a, ha⟩
             inv := ⟨b, hb⟩
             hom_inv_id := Karoubi.hom_ext _ _ hba
             inv_hom_id := Karoubi.hom_ext _ _ hab }⟩

/-- The essential point of the topos of right `M`-sets attached to an idempotent `e` of `M`. -/
noncomputable def essentialPoint (e : M) (he : IsIdempotentElem e) :
    EssentialPoint.{0} ((SingleObj M)ᵒᵖ ⥤ Type) :=
  (essentialPointEquivKaroubiOp (SingleObj M)).inverse.obj (op (karoubiMk e he))

/-- **Essential points of `M`-sets.** The essential points attached to idempotents `e` and `f`
are isomorphic iff there are `a b : M` with `f * a * e = a`, `e * b * f = b`, `b * a = e` and
`a * b = f`. -/
theorem nonempty_essentialPoint_iso_iff {e f : M} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) :
    Nonempty (essentialPoint e he ≅ essentialPoint f hf) ↔
      ∃ a b : M, f * a * e = a ∧ e * b * f = b ∧ b * a = e ∧ a * b = f := by
  change _ ↔ KaroubiRel e f
  rw [← nonempty_karoubiMk_iso_iff he hf]
  let E := essentialPointEquivKaroubiOp (SingleObj M)
  constructor
  · rintro ⟨i⟩
    exact ⟨(E.fullyFaithfulInverse.isoEquiv.symm i).unop.symm⟩
  · rintro ⟨i⟩
    exact ⟨E.fullyFaithfulInverse.isoEquiv i.symm.op⟩

/-- Every essential point of the topos of right `M`-sets is isomorphic to the point attached to
an idempotent of `M`. -/
theorem exists_iso_essentialPoint (p : EssentialPoint.{0} ((SingleObj M)ᵒᵖ ⥤ Type)) :
    ∃ (e : M) (he : IsIdempotentElem e), Nonempty (p ≅ essentialPoint e he) := by
  let E := essentialPointEquivKaroubiOp (SingleObj M)
  let P := (E.functor.obj p).unop
  refine ⟨P.p, P.idem, ⟨E.unitIso.app p ≪≫ E.inverse.mapIso (eqToIso ?_)⟩⟩
  rw [karoubiMk_eta]

/-- The endomorphisms of the object `1` of the Karoubi envelope, in the opposite category, form
the monoid `Mᵐᵒᵖ`. -/
def karoubiOneOpEndMulEquiv :
    End (op (karoubiMk (1 : M) IsIdempotentElem.one)) ≃* Mᵐᵒᵖ where
  toFun φ := MulOpposite.op φ.asHom.unop.f
  invFun m := End.of (Quiver.Hom.op ⟨m.unop, by simp [SingleObj.comp_as_mul, karoubiMk]⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The endomorphisms of the essential point attached to `1` form the monoid `Mᵐᵒᵖ`. -/
noncomputable def essentialPointEndMulEquiv :
    End (essentialPoint (1 : M) IsIdempotentElem.one) ≃* Mᵐᵒᵖ :=
  ((essentialPointEquivKaroubiOp (SingleObj M)).fullyFaithfulInverse.mulEquivEnd _).symm.trans
    karoubiOneOpEndMulEquiv

end Monoid

section Group

variable {G : Type} [Group G]

/-- For a group `G`, all essential points of the topos of `G`-sets are isomorphic. -/
theorem nonempty_essentialPoint_iso_of_group
    (p q : EssentialPoint.{0} ((SingleObj G)ᵒᵖ ⥤ Type)) : Nonempty (p ≅ q) := by
  obtain ⟨e, he, ⟨i⟩⟩ := exists_iso_essentialPoint p
  obtain ⟨f, hf, ⟨j⟩⟩ := exists_iso_essentialPoint q
  obtain rfl := IsIdempotentElem.iff_eq_one.1 he
  obtain rfl := IsIdempotentElem.iff_eq_one.1 hf
  exact ⟨i ≪≫ j.symm⟩

/-- For a group `G`, the endomorphisms of the essential point of the topos of `G`-sets form the
group `G`. -/
noncomputable def essentialPointEndMulEquivOfGroup :
    End (essentialPoint (1 : G) IsIdempotentElem.one) ≃* G :=
  essentialPointEndMulEquiv.trans (MulEquiv.inv' G).symm

end Group

section Matrix

variable {K : Type} [Field K] {n : ℕ}

open Module

/-- A vector in the range of an idempotent linear map is fixed by it. -/
theorem LinearMap.apply_of_mem_range_of_comp_self {V : Type} [AddCommGroup V] [Module K V]
    {E : V →ₗ[K] V} (hE : E ∘ₗ E = E) {y : V} (hy : y ∈ LinearMap.range E) : E y = y := by
  obtain ⟨z, rfl⟩ := hy
  exact LinearMap.congr_fun hE z

/-- Two idempotent linear maps whose ranges are isomorphic are related by `KaroubiRel`, in the
monoid of endomorphisms. -/
theorem exists_karoubiRel_linearMap {V : Type} [AddCommGroup V] [Module K V]
    {E F : V →ₗ[K] V} (hE : E ∘ₗ E = E) (hF : F ∘ₗ F = F)
    (φ : LinearMap.range E ≃ₗ[K] LinearMap.range F) :
    F ∘ₗ ((LinearMap.range F).subtype ∘ₗ φ.toLinearMap ∘ₗ E.rangeRestrict) ∘ₗ E =
        (LinearMap.range F).subtype ∘ₗ φ.toLinearMap ∘ₗ E.rangeRestrict ∧
      ((LinearMap.range E).subtype ∘ₗ φ.symm.toLinearMap ∘ₗ F.rangeRestrict) ∘ₗ
        ((LinearMap.range F).subtype ∘ₗ φ.toLinearMap ∘ₗ E.rangeRestrict) = E := by
  constructor
  · ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearEquiv.coe_coe]
    rw [LinearMap.apply_of_mem_range_of_comp_self hF (φ _).2]
    congr 2
    exact Subtype.ext (LinearMap.congr_fun hE v)
  · ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearEquiv.coe_coe]
    have : F.rangeRestrict ((φ (E.rangeRestrict v)) : V) = φ (E.rangeRestrict v) :=
      Subtype.ext (LinearMap.apply_of_mem_range_of_comp_self hF (φ _).2)
    rw [this, LinearEquiv.symm_apply_apply]
    rfl

/-- **Idempotent matrices.** Two idempotent `n × n` matrices over a field are related by
`KaroubiRel` iff they have the same rank. -/
theorem karoubiRel_iff_rank_eq {e f : Matrix (Fin n) (Fin n) K} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) : KaroubiRel e f ↔ e.rank = f.rank := by
  constructor
  · rintro ⟨a, b, ha, hb, hba, hab⟩
    apply le_antisymm
    · calc e.rank = (b * a).rank := by rw [hba]
        _ ≤ a.rank := Matrix.rank_mul_le_right _ _
        _ = (f * a * e).rank := by rw [ha]
        _ ≤ (f * a).rank := Matrix.rank_mul_le_left _ _
        _ ≤ f.rank := Matrix.rank_mul_le_left _ _
    · calc f.rank = (a * b).rank := by rw [hab]
        _ ≤ b.rank := Matrix.rank_mul_le_right _ _
        _ = (e * b * f).rank := by rw [hb]
        _ ≤ (e * b).rank := Matrix.rank_mul_le_left _ _
        _ ≤ e.rank := Matrix.rank_mul_le_left _ _
  · intro h
    let E := Matrix.toLin' e
    let F := Matrix.toLin' f
    have hE : E ∘ₗ E = E := by rw [← Matrix.toLin'_mul, he.eq]
    have hF : F ∘ₗ F = F := by rw [← Matrix.toLin'_mul, hf.eq]
    rw [Matrix.rank, Matrix.rank, ← Matrix.toLin'_apply', ← Matrix.toLin'_apply'] at h
    let φ : LinearMap.range E ≃ₗ[K] LinearMap.range F := LinearEquiv.ofFinrankEq _ _ h
    obtain ⟨ha, hba⟩ := exists_karoubiRel_linearMap hE hF φ
    obtain ⟨hb, hab⟩ := exists_karoubiRel_linearMap hF hE φ.symm
    rw [LinearEquiv.symm_symm] at hab
    refine ⟨LinearMap.toMatrix' ((LinearMap.range F).subtype ∘ₗ φ.toLinearMap ∘ₗ
      E.rangeRestrict), LinearMap.toMatrix' ((LinearMap.range E).subtype ∘ₗ
      φ.symm.toLinearMap ∘ₗ F.rangeRestrict), ?_, ?_, ?_, ?_⟩ <;>
    apply Matrix.toLin'.injective <;>
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix'] <;>
    assumption

/-- The diagonal idempotent matrix of rank `r`, with `r` ones on the diagonal. -/
def diagonalIdempotent (n r : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal fun i => if (i : ℕ) < r then 1 else 0

/-- The diagonal matrix with `r` ones is idempotent. -/
theorem isIdempotentElem_diagonalIdempotent (r : ℕ) :
    IsIdempotentElem (diagonalIdempotent (K := K) n r) := by
  unfold IsIdempotentElem diagonalIdempotent
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/-- The diagonal matrix with `r ≤ n` ones has rank `r`. -/
theorem rank_diagonalIdempotent {r : ℕ} (hr : r ≤ n) :
    (diagonalIdempotent (K := K) n r).rank = r := by
  classical
  rw [diagonalIdempotent, Matrix.rank_diagonal]
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
  rw [Fintype.card_subtype, Fin.card_filter_val_lt, min_eq_right hr]

/-- The rank of the idempotent attached to a point, chosen by `exists_iso_essentialPoint`. -/
noncomputable def essentialPointRank
    (p : EssentialPoint.{0} ((SingleObj (Matrix (Fin n) (Fin n) K))ᵒᵖ ⥤ Type)) : ℕ :=
  (Classical.choose (exists_iso_essentialPoint p)).rank

/-- The essential points attached to two idempotent matrices are isomorphic iff the matrices
have the same rank. -/
theorem nonempty_iso_essentialPoint_iff_rank_eq {e f : Matrix (Fin n) (Fin n) K}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    Nonempty (essentialPoint e he ≅ essentialPoint f hf) ↔ e.rank = f.rank := by
  rw [nonempty_essentialPoint_iso_iff]
  exact karoubiRel_iff_rank_eq he hf

/-- Two essential points of the topos of matrix-sets are isomorphic iff their ranks agree. -/
theorem nonempty_iso_iff_essentialPointRank_eq
    (p q : EssentialPoint.{0} ((SingleObj (Matrix (Fin n) (Fin n) K))ᵒᵖ ⥤ Type)) :
    Nonempty (p ≅ q) ↔ essentialPointRank p = essentialPointRank q := by
  obtain ⟨he, ⟨i⟩⟩ := Classical.choose_spec (exists_iso_essentialPoint p)
  obtain ⟨hf, ⟨j⟩⟩ := Classical.choose_spec (exists_iso_essentialPoint q)
  rw [essentialPointRank, essentialPointRank, ← nonempty_iso_essentialPoint_iff_rank_eq he hf]
  exact ⟨fun ⟨k⟩ => ⟨i.symm ≪≫ k ≪≫ j⟩, fun ⟨k⟩ => ⟨i ≪≫ k ≪≫ j.symm⟩⟩

/-- The rank of the point attached to an idempotent matrix is the rank of the matrix. -/
theorem essentialPointRank_essentialPoint {e : Matrix (Fin n) (Fin n) K}
    (he : IsIdempotentElem e) : essentialPointRank (essentialPoint e he) = e.rank := by
  obtain ⟨hf, ⟨j⟩⟩ := Classical.choose_spec (exists_iso_essentialPoint (essentialPoint e he))
  exact ((nonempty_iso_essentialPoint_iff_rank_eq he hf).1 ⟨j⟩).symm

/-- **Essential points of the topos of matrix-sets.** For the multiplicative monoid of `n × n`
matrices over a field, the isomorphism classes of essential points of the topos of right sets
are in bijection with `{0, …, n}`, by the rank of the corresponding idempotent matrix. -/
noncomputable def essentialPointClassesEquivFin (K : Type) [Field K] (n : ℕ) :
    Quotient (isIsomorphicSetoid
      (EssentialPoint.{0} ((SingleObj (Matrix (Fin n) (Fin n) K))ᵒᵖ ⥤ Type))) ≃ Fin (n + 1) :=
  Equiv.ofBijective
    (Quotient.lift (fun p => ⟨essentialPointRank p, Nat.lt_succ_of_le
        (Matrix.rank_le_card_width _ |>.trans_eq (Fintype.card_fin n))⟩)
      fun p q h => Fin.ext ((nonempty_iso_iff_essentialPointRank_eq p q).1 h))
    ⟨fun x y => Quotient.inductionOn₂ x y fun p q h =>
        Quotient.sound ((nonempty_iso_iff_essentialPointRank_eq p q).2 (congrArg Fin.val h)),
      fun r => by
        refine ⟨⟦essentialPoint _ (isIdempotentElem_diagonalIdempotent (K := K) (n := n) r)⟧,
          Fin.ext ?_⟩
        change essentialPointRank _ = _
        rw [essentialPointRank_essentialPoint, rank_diagonalIdempotent (Nat.lt_succ_iff.1 r.2)]⟩

end Matrix

end LeanPool.ToposTheoreticBridges.Examples
