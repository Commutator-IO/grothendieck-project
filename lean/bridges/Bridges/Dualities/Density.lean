/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.Atoms
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Birkhoff
public import Mathlib.Data.Finset.Union
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.UpperLower.Principal

/-!
# The Comparison Lemma for preorders, and Lindenbaum–Tarski duality as one of its readings

Caramello derives the Stone-type dualities from one statement (*A topos-theoretic approach to
Stone-type dualities*, arXiv:1103.3493, Theorem 10.13(i), the Comparison Lemma for preorders):
if `D` is a dense part of a preorder `C` with a coverage `J`, the `J`-ideals of `C` correspond
to the ideals of the coverage that `J` induces on `D`. A duality is then a choice of `C`, `J`
and `D`, and two readings of the two sides.

Here a coverage is given by covering sieves: `covers a` is a set of lower sets below `a`,
stable under restriction. A `J`-ideal is a lower set that contains every element covered by a
sieve inside it. The frame structure of the ideals, and the toposes of sheaves of which they are
the subterminal objects, are not formalised; the order isomorphism is.

* `PreorderCoverage.densityOrderIso`: the Comparison Lemma.
* `birkhoffOrderIso`: Birkhoff's representation of a finite distributive lattice, from the
  coherent coverage (finite joins) and the sup-irreducible elements; it agrees with Mathlib's
  `OrderIso.lowerSetSupIrred` (`birkhoffOrderIso_apply`).
* `orderIsoSupercompact`: preorders and Alexandrov locales. With the trivial coverage the ideals
  are the lower sets, and a partial order is recovered from them through an invariant, as the
  supercompact elements, which are the principal lower sets.
* `orderIsoCompactIdeal`: the localic half of Stone duality for distributive lattices. With the
  coherent coverage, a distributive lattice is recovered from its frame of ideals (the Stone
  locale) as its compact elements, which are the principal ideals.
* `completeAtomicBooleanAlgebraOrderIsoSetAtoms`: Lindenbaum–Tarski duality, obtained by taking
  for `C` a complete atomic Boolean algebra with its canonical coverage, for `D` its atoms, and
  reading the two sides: the `J`-ideals of `C` are its principal ideals, and the induced
  coverage on the atoms is trivial, so its ideals are all the sets of atoms.
-/

@[expose] public section

namespace Bridges.Dualities

open Set

/-- A coverage on a preorder, by covering sieves: each covering sieve of `a` is a lower set
below `a`, and a covering sieve of `a` restricts to a covering sieve of every `b ≤ a`. -/
structure PreorderCoverage (α : Type*) [Preorder α] where
  /-- The covering sieves of each element. -/
  covers : α → Set (Set α)
  isLowerSet_of_mem : ∀ {a S}, S ∈ covers a → IsLowerSet S
  le_of_mem : ∀ {a S}, S ∈ covers a → ∀ b ∈ S, b ≤ a
  stable : ∀ {a S}, S ∈ covers a → ∀ {b}, b ≤ a → ∃ T ∈ covers b, ∀ t ∈ T, ∃ s ∈ S, t ≤ s

namespace PreorderCoverage

variable {α : Type*} [Preorder α] (J : PreorderCoverage α)

/-- A `J`-ideal: a lower set containing every element that one of its covering sieves inside the
set covers. -/
def IsIdeal (I : Set α) : Prop :=
  IsLowerSet I ∧ ∀ a, ∀ S ∈ J.covers a, S ⊆ I → a ∈ I

/-- The `J`-ideals, ordered by inclusion. -/
abbrev Ideal : Type _ := {I : Set α // J.IsIdeal I}

instance : PartialOrder J.Ideal := Subtype.partialOrder _

/-- `D` is dense: every element is covered by the sieve of elements below some element of `D`
below it. -/
def Dense (D : Set α) : Prop :=
  ∀ c, {x | ∃ d ∈ D, x ≤ d ∧ d ≤ c} ∈ J.covers c

/-- The coverage induced on a part `D`: the traces on `D` of the covering sieves. -/
def restrict (D : Set α) : PreorderCoverage D where
  covers d := {R | ∃ T ∈ J.covers (d : α), R = Subtype.val ⁻¹' T}
  isLowerSet_of_mem := by
    rintro d R ⟨T, hT, rfl⟩ x y hxy hy
    exact J.isLowerSet_of_mem hT hxy hy
  le_of_mem := by
    rintro d R ⟨T, hT, rfl⟩ x hx
    exact J.le_of_mem hT _ hx
  stable := by
    rintro d R ⟨T, hT, rfl⟩ e hed
    obtain ⟨T', hT', h⟩ := J.stable hT hed
    refine ⟨_, ⟨T', hT', rfl⟩, fun t ht => ?_⟩
    obtain ⟨s, hs, hts⟩ := h t ht
    exact ⟨t, J.isLowerSet_of_mem hT hts hs, le_rfl⟩

variable {J}

/-- The smallest `J`-ideal containing a set. -/
def closure (A : Set α) : Set α :=
  ⋂₀ {I | J.IsIdeal I ∧ A ⊆ I}

theorem subset_closure (A : Set α) : A ⊆ closure (J := J) A :=
  fun _ ha => mem_sInter.2 fun _ hI => hI.2 ha

theorem closure_subset {A I : Set α} (hI : J.IsIdeal I) (h : A ⊆ I) : closure (J := J) A ⊆ I :=
  fun _ hx => mem_sInter.1 hx _ ⟨hI, h⟩

theorem isIdeal_closure (A : Set α) : J.IsIdeal (closure (J := J) A) := by
  refine ⟨fun x y hxy hy => mem_sInter.2 fun I hI => hI.1.1 hxy (mem_sInter.1 hy I hI),
    fun a S hS hSc => mem_sInter.2 fun I hI => hI.1.2 a S hS fun s hs => ?_⟩
  exact mem_sInter.1 (hSc hs) I hI

variable {D : Set α}

theorem isIdeal_preimage (hD : J.Dense D) {I : Set α} (hI : J.IsIdeal I) :
    (J.restrict D).IsIdeal (Subtype.val ⁻¹' I) := by
  refine ⟨fun x y hxy hy => hI.1 hxy hy, ?_⟩
  rintro d R ⟨T, hT, rfl⟩ hRI
  refine hI.2 d T hT fun t ht => hI.2 t _ (hD t) ?_
  rintro x ⟨e, he, hxe, het⟩
  exact hI.1 hxe (hRI (show (⟨e, he⟩ : D) ∈ Subtype.val ⁻¹' T from
    J.isLowerSet_of_mem hT het ht))

theorem preimage_closure_image {I' : Set D} (hI' : (J.restrict D).IsIdeal I') :
    Subtype.val ⁻¹' closure (J := J) (Subtype.val '' I') = I' := by
  refine Subset.antisymm ?_ fun x hx => subset_closure _ ⟨x, hx, rfl⟩
  -- the elements all of whose lower bounds in `D` lie in `I'` form a `J`-ideal
  let K : Set α := {c | ∀ x : D, (x : α) ≤ c → x ∈ I'}
  have hK : J.IsIdeal K := by
    refine ⟨fun c c' hcc' hc x hx => hc x (hx.trans hcc'), fun a S hS hSK x hxa => ?_⟩
    obtain ⟨T, hT, h⟩ := J.stable hS hxa
    refine hI'.2 x _ ⟨T, hT, rfl⟩ fun t ht => ?_
    obtain ⟨s, hs, hts⟩ := h t ht
    exact hSK hs t hts
  have hsub : Subtype.val '' I' ⊆ K := by
    rintro _ ⟨y, hy, rfl⟩ x hxy
    exact hI'.1 hxy hy
  intro x hx
  exact closure_subset hK hsub hx x le_rfl

theorem closure_image_preimage (hD : J.Dense D) {I : Set α} (hI : J.IsIdeal I) :
    closure (J := J) (Subtype.val '' (Subtype.val ⁻¹' I : Set D)) = I := by
  refine Subset.antisymm (closure_subset hI (image_preimage_subset _ _)) fun c hc => ?_
  refine (isIdeal_closure _).2 c _ (hD c) ?_
  rintro x ⟨d, hd, hxd, hdc⟩
  exact (isIdeal_closure _).1 hxd (subset_closure _ ⟨⟨d, hd⟩, hI.1 hdc hc, rfl⟩)

/-- **The Comparison Lemma for preorders** (Caramello, arXiv:1103.3493, Theorem 10.13(i)): for a
dense part `D`, intersecting with `D` is an order isomorphism from the `J`-ideals to the ideals of
the induced coverage, with inverse the `J`-closure. -/
def densityOrderIso (hD : J.Dense D) : J.Ideal ≃o (J.restrict D).Ideal where
  toFun I := ⟨Subtype.val ⁻¹' I.1, isIdeal_preimage hD I.2⟩
  invFun I' := ⟨closure (Subtype.val '' I'.1), isIdeal_closure _⟩
  left_inv I := Subtype.ext (closure_image_preimage hD I.2)
  right_inv I' := Subtype.ext (preimage_closure_image I'.2)
  map_rel_iff' {I₁ I₂} := by
    constructor
    · intro h c hc
      have h' : (Subtype.val ⁻¹' I₁.1 : Set D) ⊆ Subtype.val ⁻¹' I₂.1 := h
      rw [← closure_image_preimage hD I₂.2]
      rw [← closure_image_preimage hD I₁.2] at hc
      exact closure_subset (isIdeal_closure _)
        (by rintro _ ⟨x, hx, rfl⟩; exact subset_closure _ ⟨x, h' hx, rfl⟩) hc
    · intro h x hx
      exact h hx

end PreorderCoverage

/-! ## Lindenbaum–Tarski duality as a reading of the Comparison Lemma -/

section LindenbaumTarski

open PreorderCoverage

variable (B : Type*) [CompleteAtomicBooleanAlgebra B]

/-- The canonical coverage of a frame: a lower set below `a` covers `a` when its join is `a`. -/
def canonicalCoverage : PreorderCoverage B where
  covers a := {S | IsLowerSet S ∧ (∀ b ∈ S, b ≤ a) ∧ sSup S = a}
  isLowerSet_of_mem hS := hS.1
  le_of_mem hS := hS.2.1
  stable := by
    rintro a S ⟨hS, hSa, hsup⟩ b hba
    refine ⟨{x | x ≤ b ∧ ∃ s ∈ S, x ≤ s}, ⟨fun x y hxy hy => ⟨hxy.trans hy.1, ?_⟩,
      fun x hx => hx.1, le_antisymm (sSup_le fun x hx => hx.1) ?_⟩, fun t ht => ht.2⟩
    · obtain ⟨s, hs, hys⟩ := hy.2
      exact ⟨s, hs, hxy.trans hys⟩
    · calc b = b ⊓ sSup S := by rw [hsup, inf_eq_left.2 hba]
        _ = ⨆ s ∈ S, b ⊓ s := inf_sSup_eq
        _ ≤ _ := iSup₂_le fun s hs => le_sSup
          (show b ⊓ s ∈ {x | x ≤ b ∧ ∃ s ∈ S, x ≤ s} from ⟨inf_le_left, s, hs, inf_le_right⟩)

/-- First reading: the canonical ideals are the principal ideals. -/
def canonicalIdealOrderIso : B ≃o (canonicalCoverage B).Ideal where
  toFun a := ⟨Iic a, fun x y hxy hy => hxy.trans hy, fun b S hS hSa =>
    hS.2.2 ▸ sSup_le fun s hs => hSa hs⟩
  invFun I := sSup I.1
  left_inv a := csSup_Iic
  right_inv I := by
    refine Subtype.ext (Subset.antisymm (fun x hx => ?_) fun x hx => le_sSup hx)
    have : sSup I.1 ∈ I.1 :=
      I.2.2 _ I.1 ⟨I.2.1, fun b hb => le_sSup hb, rfl⟩ le_rfl
    exact I.2.1 hx this
  map_rel_iff' {a b} := ⟨fun h => h (le_refl a), fun h x hx => le_trans hx h⟩

/-- The atoms are dense for the canonical coverage (`B` is atomistic). -/
theorem dense_atoms : (canonicalCoverage B).Dense {a : B | IsAtom a} := by
  intro c
  refine ⟨fun x y hxy hy => ?_, fun x ⟨d, _, hxd, hdc⟩ => hxd.trans hdc, ?_⟩
  · obtain ⟨d, hd, hyd, hdc⟩ := hy
    exact ⟨d, hd, hxy.trans hyd, hdc⟩
  · refine le_antisymm (sSup_le fun x ⟨d, _, hxd, hdc⟩ => hxd.trans hdc) ?_
    obtain ⟨s, hsc, hs⟩ := eq_sSup_atoms c
    calc c = sSup s := hsc
      _ ≤ _ := sSup_le_sSup fun a ha =>
        (show a ∈ {x | ∃ d ∈ {a : B | IsAtom a}, x ≤ d ∧ d ≤ c} from
          ⟨a, hs a ha, le_rfl, (le_sSup ha).trans_eq hsc.symm⟩)

/-- Second reading: on the atoms, the induced coverage is trivial, so every set of atoms is an
ideal. -/
def atomIdealOrderIso :
    ((canonicalCoverage B).restrict {a : B | IsAtom a}).Ideal ≃o Set {a : B // IsAtom a} where
  toFun I := I.1
  invFun I := ⟨I, fun x y hxy hy => by
      have : (y : B) = x := (x.2.le_iff.1 hxy).resolve_left y.2.1
      exact Subtype.ext this ▸ hy,
    fun d R ⟨T, ⟨hT, hTd, hsup⟩, hR⟩ hRI => by
      subst hR
      by_contra hd
      have hsub : T ⊆ {⊥} := fun t ht => by
        rcases d.2.le_iff.1 (hTd t ht) with h | h
        · exact h
        · exact absurd (hRI (show (d : B) ∈ T by rw [← h]; exact ht)) hd
      exact d.2.1 (le_bot_iff.1 (hsup ▸ sSup_le fun t ht => (hsub ht).le))⟩
  left_inv I := rfl
  right_inv I := rfl
  map_rel_iff' := Iff.rfl

/-- **Lindenbaum–Tarski duality**, read off the Comparison Lemma: a complete atomic Boolean
algebra is isomorphic to the power set of its atoms. -/
noncomputable def completeAtomicBooleanAlgebraOrderIsoSetAtoms : B ≃o Set {a : B // IsAtom a} :=
  (canonicalIdealOrderIso B).trans
    (((canonicalCoverage B).densityOrderIso (dense_atoms B)).trans (atomIdealOrderIso B))

/-- The isomorphism sends an element to the atoms below it, as in the usual statement. -/
theorem completeAtomicBooleanAlgebraOrderIsoSetAtoms_apply (a : B) :
    completeAtomicBooleanAlgebraOrderIsoSetAtoms B a = {x : {a : B // IsAtom a} | (x : B) ≤ a} :=
  rfl

end LindenbaumTarski

/-! ## Birkhoff's representation as a reading of the Comparison Lemma -/

section Birkhoff

open PreorderCoverage

variable (L : Type*) [DistribLattice L] [OrderBot L]

/-- The coherent coverage: a lower set below `a` covers `a` when a finite part of it has join
`a`. -/
def coherentCoverage : PreorderCoverage L where
  covers a := {S | IsLowerSet S ∧ (∀ b ∈ S, b ≤ a) ∧ ∃ F : Finset L, ↑F ⊆ S ∧ F.sup id = a}
  isLowerSet_of_mem hS := hS.1
  le_of_mem hS := hS.2.1
  stable := by
    classical
    rintro a S ⟨hS, hSa, F, hFS, hF⟩ b hba
    refine ⟨{x | x ≤ b ∧ ∃ s ∈ S, x ≤ s}, ⟨fun x y hxy hy => ⟨hxy.trans hy.1, ?_⟩,
      fun x hx => hx.1, F.image (b ⊓ ·), ?_, ?_⟩, fun t ht => ht.2⟩
    · obtain ⟨s, hs, hys⟩ := hy.2
      exact ⟨s, hs, hxy.trans hys⟩
    · intro x hx
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      exact ⟨inf_le_left, f, hFS hf, inf_le_right⟩
    · rw [Finset.sup_image]
      calc F.sup (id ∘ (b ⊓ ·)) = b ⊓ F.sup id := (Finset.sup_inf_distrib_left F id b).symm
        _ = b := by rw [hF, inf_eq_left.2 hba]

variable [Finite L]

/-- First reading: on a finite lattice, the coherent ideals are the principal ideals. -/
noncomputable def coherentIdealOrderIso : L ≃o (coherentCoverage L).Ideal where
  toFun a := ⟨Iic a, fun x y hxy hy => hxy.trans hy, fun b S ⟨_, _, F, hFS, hF⟩ hSa =>
    hF ▸ Finset.sup_le fun f hf => hSa (hFS hf)⟩
  invFun I := (Set.toFinite I.1).toFinset.sup id
  left_inv a := le_antisymm (Finset.sup_le fun b hb => by simpa using hb)
    (Finset.le_sup (f := id) ((Set.Finite.mem_toFinset _).2 (le_refl a)))
  right_inv I := by
    have hmem : (Set.toFinite I.1).toFinset.sup id ∈ I.1 :=
      I.2.2 _ I.1 ⟨I.2.1, fun b hb => Finset.le_sup (f := id) ((Set.Finite.mem_toFinset _).2 hb),
        (Set.toFinite I.1).toFinset, by simp, rfl⟩ le_rfl
    exact Subtype.ext (Subset.antisymm (fun x hx => I.2.1 hx hmem)
      fun x hx => Finset.le_sup (f := id) ((Set.Finite.mem_toFinset _).2 hx))
  map_rel_iff' {a b} := ⟨fun h => h (le_refl a), fun h x hx => le_trans hx h⟩

/-- The sup-irreducible elements are dense for the coherent coverage. -/
theorem dense_supIrred : (coherentCoverage L).Dense {a : L | SupIrred a} := by
  intro c
  obtain ⟨F, hF, hirr⟩ := exists_supIrred_decomposition c
  refine ⟨fun x y hxy hy => ?_, fun x ⟨d, _, hxd, hdc⟩ => hxd.trans hdc, F, fun b hb =>
    ⟨b, hirr hb, le_rfl, hF ▸ Finset.le_sup (f := id) hb⟩, hF⟩
  obtain ⟨d, hd, hyd, hdc⟩ := hy
  exact ⟨d, hd, hxy.trans hyd, hdc⟩

/-- Second reading: on the sup-irreducible elements the induced coverage is trivial, so its
ideals are the lower sets. -/
def supIrredIdealOrderIso :
    ((coherentCoverage L).restrict {a : L | SupIrred a}).Ideal ≃o LowerSet {a : L // SupIrred a}
    where
  toFun I := ⟨I.1, I.2.1⟩
  invFun I := ⟨(I : Set {a : L // SupIrred a}), I.lower,
    fun d R ⟨T, ⟨_, _, F, hFT, hF⟩, hR⟩ hRI => by
      subst hR
      obtain ⟨i, hi, hid⟩ := d.2.finset_sup_eq hF
      exact hRI (show (d : L) ∈ T from hid ▸ hFT hi)⟩
  left_inv I := rfl
  right_inv I := rfl
  map_rel_iff' := Iff.rfl

/-- **Birkhoff's representation theorem**, read off the Comparison Lemma: a finite distributive
lattice is isomorphic to the lattice of lower sets of its sup-irreducible elements. -/
noncomputable def birkhoffOrderIso : L ≃o LowerSet {a : L // SupIrred a} :=
  (coherentIdealOrderIso L).trans
    (((coherentCoverage L).densityOrderIso (dense_supIrred L)).trans (supIrredIdealOrderIso L))

/-- The machine's output is Mathlib's statement. -/
theorem birkhoffOrderIso_apply [Fintype L] [DecidablePred (SupIrred (α := L))] (a : L) :
    birkhoffOrderIso L a = OrderIso.lowerSetSupIrred a :=
  SetLike.coe_injective rfl

end Birkhoff

/-! ## Stone duality for distributive lattices, localic half -/

section Stone

open PreorderCoverage

variable (D : Type*) [DistribLattice D] [OrderBot D]

variable {D} in
/-- The coherent closure, described: the elements below a finite join of elements of `A`. -/
theorem closure_coherent_eq (A : Set D) :
    closure (J := coherentCoverage D) A = {x | ∃ F : Finset D, ↑F ⊆ A ∧ x ≤ F.sup id} := by
  classical
  apply Subset.antisymm
  · refine closure_subset ⟨fun x y hxy ⟨F, hF, hx⟩ => ⟨F, hF, hxy.trans hx⟩, ?_⟩
      fun a ha => ⟨{a}, by simpa using ha, by simp⟩
    rintro a S ⟨_, _, G, hGS, rfl⟩ hSK
    choose! F hFA hle using fun g (hg : g ∈ G) => hSK (hGS hg)
    refine ⟨G.biUnion F, fun x hx => ?_, Finset.sup_le fun g hg => (hle g hg).trans ?_⟩
    · obtain ⟨g, hg, hx⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hx)
      exact hFA g hg hx
    · exact Finset.sup_mono (Finset.subset_biUnion_of_mem F hg)
  · rintro x ⟨F, hF, hx⟩
    have hsup : F.sup id ∈ closure (J := coherentCoverage D) A := by
      refine (isIdeal_closure A).2 _ {y | y ≤ F.sup id ∧ ∃ f ∈ F, y ≤ f}
        ⟨fun y z hzy hy => ⟨hzy.trans hy.1, ?_⟩, fun y hy => hy.1, F,
          fun f hf => ⟨Finset.le_sup (f := id) hf, f, hf, le_rfl⟩, rfl⟩ ?_
      · obtain ⟨f, hf, hyf⟩ := hy.2
        exact ⟨f, hf, hzy.trans hyf⟩
      · rintro y ⟨_, f, hf, hyf⟩
        exact (isIdeal_closure A).1 hyf (subset_closure A (hF hf))
    exact (isIdeal_closure A).1 hx hsup

/-- A coherent ideal is compact when, whenever it lies in the ideal generated by a family of
ideals, it lies in the ideal generated by finitely many of them. -/
def IsCompactIdeal (I : (coherentCoverage D).Ideal) : Prop :=
  ∀ 𝒮 : Set (coherentCoverage D).Ideal,
    I.1 ⊆ closure (J := coherentCoverage D) (⋃ S ∈ 𝒮, S.1) →
      ∃ 𝒯 : Finset (coherentCoverage D).Ideal, ↑𝒯 ⊆ 𝒮 ∧
        I.1 ⊆ closure (J := coherentCoverage D) (⋃ S ∈ 𝒯, S.1)

/-- The principal coherent ideal of an element. -/
def principalIdeal (a : D) : (coherentCoverage D).Ideal :=
  ⟨Iic a, fun _ _ hxy hy => hxy.trans hy, fun _ _ ⟨_, _, _, hFS, hF⟩ hSa =>
    hF ▸ Finset.sup_le fun _ hf => hSa (hFS hf)⟩

variable {D} in
/-- The compact coherent ideals are the principal ones. -/
theorem isCompactIdeal_iff (I : (coherentCoverage D).Ideal) :
    IsCompactIdeal D I ↔ ∃ a, I = principalIdeal D a := by
  classical
  have : Nonempty D := ⟨⊥⟩
  have : Nonempty (coherentCoverage D).Ideal := ⟨principalIdeal D ⊥⟩
  constructor
  · intro hI
    obtain ⟨𝒯, h𝒯, hsub⟩ := hI (principalIdeal D '' I.1) fun x hx =>
      subset_closure _ (mem_biUnion (mem_image_of_mem _ hx) (show x ∈ Iic x from le_rfl))
    -- each member of 𝒯 is the principal ideal of an element of I
    choose! c hcI hc using fun S (hS : S ∈ 𝒯) => h𝒯 hS
    refine ⟨𝒯.sup c, Subtype.ext (Subset.antisymm (fun x hx => ?_) fun x hx => ?_)⟩
    · rw [closure_coherent_eq] at hsub
      obtain ⟨F, hF, hxF⟩ := hsub hx
      refine hxF.trans (Finset.sup_le fun f hf => ?_)
      obtain ⟨S, hS, hfS⟩ := mem_iUnion₂.1 (hF hf)
      rw [← hc S hS] at hfS
      exact (show f ≤ c S from hfS).trans (Finset.le_sup (f := c) hS)
    · refine I.2.1 hx (I.2.2 _ {y | y ≤ 𝒯.sup c ∧ ∃ S ∈ 𝒯, y ≤ c S}
        ⟨fun y z hzy hy => ⟨hzy.trans hy.1, ?_⟩, fun y hy => hy.1, 𝒯.image c, ?_, ?_⟩ ?_)
      · obtain ⟨S, hS, hyS⟩ := hy.2
        exact ⟨S, hS, hzy.trans hyS⟩
      · intro y hy
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
        exact ⟨Finset.le_sup (f := c) hS, S, hS, le_rfl⟩
      · rw [Finset.sup_image]
        rfl
      · rintro y ⟨_, S, hS, hyS⟩
        exact I.2.1 hyS (hcI S hS)
  · rintro ⟨a, rfl⟩ 𝒮 h𝒮
    have ha := h𝒮 (show a ∈ Iic a from le_rfl)
    rw [closure_coherent_eq] at ha
    obtain ⟨F, hF, haF⟩ := ha
    choose! S hS hfS using fun f (hf : f ∈ F) => mem_iUnion₂.1 (hF hf)
    refine ⟨F.image S, fun T hT => ?_, fun x hx => ?_⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hT)
      exact hS f hf
    · rw [closure_coherent_eq]
      refine ⟨F, fun f hf => mem_iUnion₂.2 ⟨S f, ?_, hfS f hf⟩, (show x ≤ a from hx).trans haF⟩
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem S hf)

/-- **Stone duality, localic half**, read off the coherent coverage: a distributive lattice with a
least element is the poset of compact elements of its frame of coherent ideals. -/
noncomputable def orderIsoCompactIdeal : D ≃o {I : (coherentCoverage D).Ideal // IsCompactIdeal D I}
    where
  toFun a := ⟨principalIdeal D a, (isCompactIdeal_iff _).2 ⟨a, rfl⟩⟩
  invFun I := ((isCompactIdeal_iff I.1).1 I.2).choose
  left_inv a := Set.Iic_inj.1 (congrArg Subtype.val ((isCompactIdeal_iff (principalIdeal D a)).1
    ((isCompactIdeal_iff _).2 ⟨a, rfl⟩)).choose_spec).symm
  right_inv I := Subtype.ext ((isCompactIdeal_iff I.1).1 I.2).choose_spec.symm
  map_rel_iff' {a b} := by
    change Iic a ⊆ Iic b ↔ a ≤ b
    exact ⟨fun h => h le_rfl, fun h x hx => le_trans hx h⟩

end Stone

/-! ## Preorders and Alexandrov locales: recovering the structure through an invariant -/

section Alexandrov

open PreorderCoverage

variable (P : Type*) [PartialOrder P]

/-- The trivial coverage: only the principal sieve covers. -/
def trivialCoverage : PreorderCoverage P where
  covers a := {Iic a}
  isLowerSet_of_mem := by
    rintro a S rfl x y hxy hy
    exact hxy.trans hy
  le_of_mem := by
    rintro a S rfl b hb
    exact hb
  stable := by
    rintro a S rfl b hba
    exact ⟨Iic b, rfl, fun t ht => ⟨t, ht.trans hba, le_rfl⟩⟩

/-- First reading: the ideals of the trivial coverage are the lower sets, the opens of the
Alexandrov topology. -/
def trivialIdealOrderIso : (trivialCoverage P).Ideal ≃o LowerSet P where
  toFun I := ⟨I.1, I.2.1⟩
  invFun I := ⟨I, I.lower, by
    rintro a S rfl hS
    exact hS le_rfl⟩
  left_inv I := rfl
  right_inv I := rfl
  map_rel_iff' := Iff.rfl

/-- An element `x` of a complete lattice is supercompact when it lies below an element of every
family whose join it lies below. -/
def IsSupercompact {L : Type*} [CompleteLattice L] (x : L) : Prop :=
  ∀ S : Set L, x ≤ sSup S → ∃ s ∈ S, x ≤ s

/-- The supercompact lower sets are the principal ones. -/
theorem isSupercompact_iff (x : LowerSet P) : IsSupercompact x ↔ ∃ p, x = LowerSet.Iic p := by
  constructor
  · intro hx
    obtain ⟨s, ⟨p, hp, rfl⟩, hxs⟩ := hx (LowerSet.Iic '' (x : Set P)) fun q hq =>
      LowerSet.mem_sSup_iff.2 ⟨LowerSet.Iic q, ⟨q, hq, rfl⟩, le_rfl⟩
    exact ⟨p, le_antisymm hxs (LowerSet.Iic_le.2 hp)⟩
  · rintro ⟨p, rfl⟩ S hS
    obtain ⟨s, hs, hps⟩ := LowerSet.mem_sSup_iff.1 (LowerSet.Iic_le.1 hS)
    exact ⟨s, hs, LowerSet.Iic_le.2 hps⟩

theorem isSupercompact_Iic (p : P) : IsSupercompact (LowerSet.Iic p) :=
  (isSupercompact_iff P _).2 ⟨p, rfl⟩

/-- Second reading, the recovery: a partial order is the poset of supercompact elements of the
frame of its lower sets, which `trivialIdealOrderIso` identifies with the ideals of the trivial
coverage. -/
noncomputable def orderIsoSupercompact : P ≃o {x : LowerSet P // IsSupercompact x} where
  toFun p := ⟨LowerSet.Iic p, isSupercompact_Iic P p⟩
  invFun x := ((isSupercompact_iff P _).1 x.2).choose
  left_inv p :=
    (LowerSet.Iic_inj.1 ((isSupercompact_iff P _).1 (isSupercompact_Iic P p)).choose_spec).symm
  right_inv x := Subtype.ext ((isSupercompact_iff P _).1 x.2).choose_spec.symm
  map_rel_iff' {p q} := by
    change LowerSet.Iic p ≤ LowerSet.Iic q ↔ p ≤ q
    simp

end Alexandrov

end Bridges.Dualities
