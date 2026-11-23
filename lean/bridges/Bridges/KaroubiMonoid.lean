/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Bridges.EssentialPoints

/-!
# Idempotent maps of a set and the Karoubi envelope of `Function.End α`

An object of the Karoubi envelope of `SingleObj M` is an idempotent `e` of `M` (`karoubiMk`), and
two idempotents give isomorphic objects iff they are related by `KaroubiRel`: there are
`a b : M` with `f * a * e = a`, `e * b * f = b`, `b * a = e` and `a * b = f`
(`nonempty_karoubiMk_iso_iff`, with composition `g ≫ h = h * g` in `SingleObj M`). The essential
points of the topos of right `M`-sets are classified in the same way
(`nonempty_essentialPoint_iso_iff`).

For the monoid `Function.End α` of maps `α → α`, with `f * g = f ∘ g`:

* `karoubiRel_iff_nonempty_equiv_range`: two idempotent maps `e`, `f` are related by
  `KaroubiRel` iff their images are in bijection. An idempotent map fixes its image
  (`apply_of_mem_range`), `a` restricts to a bijection from the image of `e` to the image of
  `f` with inverse `b`, and conversely a bijection `φ` gives `a = φ ∘ e` and `b = φ⁻¹ ∘ f`;
* `nonempty_karoubiMk_iso_iff_card_eq`, `nonempty_essentialPoint_iso_iff_card_eq`: for
  `α = Fin n`, two idempotent maps give isomorphic objects of the Karoubi envelope, or isomorphic
  essential points of the topos of right `Function.End (Fin n)`-sets, iff their images have the
  same cardinality;
* `karoubiClassesEquivFin`: the isomorphism classes of the Karoubi envelope of
  `SingleObj (Function.End (Fin (n + 1)))` are in bijection with `Fin (n + 1)`, by one less than
  the cardinality of the image, realised by the idempotent `x ↦ min x k`.
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory Idempotents

section End

variable {α : Type} {e f : Function.End α}

/-- An idempotent map fixes the points of its image. -/
theorem apply_of_mem_range (he : IsIdempotentElem e) {x : α} (hx : x ∈ Set.range e) :
    e x = x := by
  obtain ⟨y, rfl⟩ := hx
  exact congrFun he.eq y

/-- The corestriction of a map to its image. -/
def toRange (e : Function.End α) (x : α) : Set.range e :=
  ⟨e x, x, rfl⟩

theorem toRange_coe (he : IsIdempotentElem e) (z : Set.range e) : toRange e z = z :=
  Subtype.ext (apply_of_mem_range he z.2)

theorem toRange_apply (he : IsIdempotentElem e) (x : α) : toRange e (e x) = toRange e x :=
  Subtype.ext (congrFun he.eq x)

/-- The map `φ ∘ e` attached to a bijection `φ` from the image of `e` to the image of `f`. -/
def rangeMap (φ : Set.range e ≃ Set.range f) : Function.End α :=
  fun x => φ (toRange e x)

theorem rangeMap_spec (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (φ : Set.range e ≃ Set.range f) :
    f * rangeMap φ * e = rangeMap φ ∧ rangeMap φ.symm * rangeMap φ = e := by
  constructor
  · funext x
    change f (φ (toRange e (e x))) = φ (toRange e x)
    rw [toRange_apply he]
    exact apply_of_mem_range hf (φ _).2
  · funext x
    change (φ.symm (toRange f (φ (toRange e x))) : α) = e x
    rw [toRange_coe hf, Equiv.symm_apply_apply]
    rfl

/-- **Idempotent maps.** Two idempotent maps `e`, `f : α → α` are related by `KaroubiRel` in
`Function.End α` iff their images are in bijection. -/
theorem karoubiRel_iff_nonempty_equiv_range (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) : KaroubiRel e f ↔ Nonempty (Set.range e ≃ Set.range f) := by
  constructor
  · rintro ⟨a, b, ha, hb, hba, hab⟩
    refine ⟨{ toFun := fun x => ⟨a x, a (e x), congrFun ha x⟩
              invFun := fun y => ⟨b y, b (f y), congrFun hb y⟩
              left_inv := fun x => Subtype.ext ?_
              right_inv := fun y => Subtype.ext ?_ }⟩
    · exact (congrFun hba x.1).trans (apply_of_mem_range he x.2)
    · exact (congrFun hab y.1).trans (apply_of_mem_range hf y.2)
  · rintro ⟨φ⟩
    obtain ⟨ha, hba⟩ := rangeMap_spec he hf φ
    obtain ⟨hb, hab⟩ := rangeMap_spec hf he φ.symm
    exact ⟨rangeMap φ, rangeMap φ.symm, ha, hb, hba, hab⟩

/-- Two idempotent maps give isomorphic objects of the Karoubi envelope of
`SingleObj (Function.End α)` iff their images are in bijection. -/
theorem nonempty_karoubiMk_iso_iff_nonempty_equiv (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) :
    Nonempty (karoubiMk e he ≅ karoubiMk f hf) ↔ Nonempty (Set.range e ≃ Set.range f) :=
  (nonempty_karoubiMk_iso_iff he hf).trans (karoubiRel_iff_nonempty_equiv_range he hf)

end End

section Fin

variable {n : ℕ} {e f : Function.End (Fin n)}

/-- **Karoubi envelope of `Function.End (Fin n)`.** Two idempotent maps `e`, `f` of `Fin n` give
isomorphic objects of the Karoubi envelope iff their images have the same cardinality. -/
theorem nonempty_karoubiMk_iso_iff_card_eq (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    Nonempty (karoubiMk e he ≅ karoubiMk f hf) ↔
      Nat.card (Set.range e) = Nat.card (Set.range f) :=
  (nonempty_karoubiMk_iso_iff_nonempty_equiv he hf).trans Finite.card_eq.symm

/-- **Essential points of `Function.End (Fin n)`-sets.** The essential points of the topos of
right `Function.End (Fin n)`-sets attached to idempotent maps `e`, `f` are isomorphic iff their
images have the same cardinality. -/
theorem nonempty_essentialPoint_iso_iff_card_eq (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) :
    Nonempty (essentialPoint e he ≅ essentialPoint f hf) ↔
      Nat.card (Set.range e) = Nat.card (Set.range f) := by
  rw [nonempty_essentialPoint_iso_iff]
  exact (karoubiRel_iff_nonempty_equiv_range he hf).trans Finite.card_eq.symm

end Fin

section Classes

variable {n : ℕ}

/-- The idempotent map `x ↦ min x k` of `Fin (n + 1)`, with image `{0, …, k}`. -/
def truncation (k : Fin (n + 1)) : Function.End (Fin (n + 1)) :=
  fun x => min x k

theorem isIdempotentElem_truncation (k : Fin (n + 1)) : IsIdempotentElem (truncation k) := by
  funext x
  exact min_eq_left (min_le_right x k)

/-- The image of `x ↦ min x k` is in bijection with `Fin (k + 1)`. -/
def rangeTruncationEquiv (k : Fin (n + 1)) : Set.range (truncation k) ≃ Fin (k + 1) where
  toFun y := ⟨y.1, by
    obtain ⟨x, hx⟩ := y.2
    have : y.1 ≤ k := hx ▸ min_le_right x k
    exact Nat.lt_succ_of_le this⟩
  invFun i := ⟨⟨i, by omega⟩, ⟨i, by omega⟩, min_eq_left (by
    change (i : ℕ) ≤ k
    omega)⟩
  left_inv y := Subtype.ext (Fin.ext rfl)
  right_inv i := Fin.ext rfl

theorem card_range_truncation (k : Fin (n + 1)) :
    Nat.card (Set.range (truncation k)) = k + 1 := by
  rw [Nat.card_congr (rangeTruncationEquiv k), Nat.card_fin]

/-- The cardinality of the image of the idempotent of an object of the Karoubi envelope. -/
noncomputable def karoubiRank (P : Karoubi (SingleObj (Function.End (Fin (n + 1))))) : ℕ :=
  Nat.card (Set.range (show Function.End (Fin (n + 1)) from P.p))

theorem one_le_karoubiRank (P : Karoubi (SingleObj (Function.End (Fin (n + 1))))) :
    1 ≤ karoubiRank P := by
  unfold karoubiRank
  have : Nonempty (Set.range (show Function.End (Fin (n + 1)) from P.p)) := ⟨toRange _ 0⟩
  exact Nat.card_pos

theorem karoubiRank_le (P : Karoubi (SingleObj (Function.End (Fin (n + 1))))) :
    karoubiRank P ≤ n + 1 := by
  unfold karoubiRank
  exact (Finite.card_subtype_le _).trans_eq (Nat.card_fin _)

theorem nonempty_iso_iff_karoubiRank_eq (P Q : Karoubi (SingleObj (Function.End (Fin (n + 1))))) :
    Nonempty (P ≅ Q) ↔ karoubiRank P = karoubiRank Q := by
  rw [← karoubiMk_eta P, ← karoubiMk_eta Q]
  exact nonempty_karoubiMk_iso_iff_card_eq P.idem Q.idem

/-- **Classes of the Karoubi envelope of `Function.End (Fin (n + 1))`.** The isomorphism classes
of idempotent maps of a set with `n + 1` elements are in bijection with `Fin (n + 1)`, by one less
than the cardinality of the image. -/
noncomputable def karoubiClassesEquivFin (n : ℕ) :
    Quotient (isIsomorphicSetoid (Karoubi (SingleObj (Function.End (Fin (n + 1)))))) ≃
      Fin (n + 1) :=
  Equiv.ofBijective
    (Quotient.lift (fun P => ⟨karoubiRank P - 1, by have := karoubiRank_le P; omega⟩)
      fun P Q h => Fin.ext (by
        change karoubiRank P - 1 = karoubiRank Q - 1
        rw [(nonempty_iso_iff_karoubiRank_eq P Q).1 h]))
    ⟨fun x y => Quotient.inductionOn₂ x y fun P Q h => by
        have h' : karoubiRank P - 1 = karoubiRank Q - 1 := congrArg Fin.val h
        have := one_le_karoubiRank P
        have := one_le_karoubiRank Q
        exact Quotient.sound ((nonempty_iso_iff_karoubiRank_eq P Q).2 (by omega)),
      fun k => ⟨⟦karoubiMk (truncation k) (isIdempotentElem_truncation k)⟧, Fin.ext (by
        change Nat.card (Set.range (truncation k)) - 1 = k
        rw [card_range_truncation]
        omega)⟩⟩

end Classes

end LeanPool.ToposTheoreticBridges.Examples
