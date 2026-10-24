import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.LocallyClosed

/-!
# Folder 161-3: the topos of a product, the converse on pages 10–11

Issue #26 lists folder 161-3 (2-products of topoi, the topos of a product of
spaces). Of the folder, only the covering argument of pages 10–11 is formalised
here, as the reading `transcripts/161-3/161-3.modern.tex` gives it
(« Le sens réciproque »).

* **The statement.** « Supposons que toute partie localement fermée non vide de
  `X` possède un point admettant, dans elle, un voisinage relatif
  quasi-compact. » Then `Top(X × Y) → Top(X) × Top(Y)` is an equivalence, for
  every space `Y`. The hypothesis is `HypG X`; no separation, sobriety or
  hypothesis on `Y` is assumed.
* **The model.** The page works with the « S » of the 2-product: a set of pairs
  `(U, V)` of opens of `X` and `Y`, stable under shrinking and under unions in
  each variable separately (`CIdeal`), and the theorem amounts to saying that
  such an `S` contains every rectangle `U × V` covered by its own rectangles.
  That is `covering`, proved by the page's maximality argument: `U'` the
  largest open of `U` with `(U', V) ∈ S`, a point of `U \ U'` with a
  quasi-compact neighbourhood `T`, the tube lemma over `T`
  (`IsCompact.induction_on`) for each `y ∈ V`, then a union over `y`. The step
  the page leaves out, `U'' ⊆ U' ∪ ⋃ Uᵢ`, is the last case split of the proof.
* **The bijection.** Every open `W` of `X × Y` gives the `CIdeal` `rect W` of
  the rectangles inside it, and `W` is the union of these rectangles
  (`iUnion_rect`, no hypothesis); under `HypG X`, every `CIdeal` is
  `rect` of the union of its rectangles (`eq_rect`). So the opens of `X × Y`
  and the `CIdeal`s correspond one to one.

**What the formalisation finds.** Nothing false: the argument holds as the
reading completes it, for arbitrary `X` and `Y`.

**Not formalised.** The dictionary from `CIdeal`s to the frame coproduct of the
open-set frames of `X` and `Y` (the elements of the coproduct are the
`CIdeal`s), and from there to the 2-product `Top(X) × Top(Y)` as the sheaves
on that frame: mathlib has neither frame coproducts nor 2-products of topoi.
Nor the rest of the folder (pages 3–8 on the 2-product as an intersection of
subtopoi, pages 11–14 on infinite products).

What this certifies is that the reading holds together, not that it is what the
pages say (issue #26).
-/

namespace Grothendieck.Folder161_3

open TopologicalSpace Set

/-- The page's hypothesis: every nonempty locally closed `Z ⊆ X` has a point `x`
with a quasi-compact neighbourhood `T` in `Z`, i.e. `O ∩ Z ⊆ T ⊆ Z` for an
open `O ∋ x`. -/
def HypG (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ Z : Set X, IsLocallyClosed Z → Z.Nonempty →
    ∃ x ∈ Z, ∃ T ⊆ Z, IsCompact T ∧ ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ O ∩ Z ⊆ T

/-- A set of pairs of opens, stable under shrinking and under arbitrary unions in
each variable: an element of the frame coproduct of `Opens X` and `Opens Y`, the
« S » of the page. -/
structure CIdeal (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  carrier : Set (Opens X × Opens Y)
  mono : ∀ {U U' V V'}, (U, V) ∈ carrier → U' ≤ U → V' ≤ V → (U', V') ∈ carrier
  sSup_left : ∀ (s : Set (Opens X)) V,
    (∀ U ∈ s, (U, V) ∈ carrier) → (sSup s, V) ∈ carrier
  sSup_right : ∀ U (s : Set (Opens Y)),
    (∀ V ∈ s, (U, V) ∈ carrier) → (U, sSup s) ∈ carrier

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace CIdeal

variable (S : CIdeal X Y)

lemma sup_left {U U' V} (h : (U, V) ∈ S.carrier) (h' : (U', V) ∈ S.carrier) :
    (U ⊔ U', V) ∈ S.carrier := by
  simpa [sSup_pair] using S.sSup_left {U, U'} V (by simp [h, h'])

lemma bot_top : (⊥, ⊤) ∈ S.carrier := by simpa using S.sSup_left ∅ ⊤ (by simp)

end CIdeal

/-- Pages 10–11: under `HypG X`, a `CIdeal` contains every rectangle covered by
its own rectangles. -/
theorem covering (hG : HypG X) (S : CIdeal X Y) (U : Opens X) (V : Opens Y)
    (h : (U : Set X) ×ˢ (V : Set Y) ⊆ ⋃ p ∈ S.carrier, (p.1 : Set X) ×ˢ (p.2 : Set Y)) :
    (U, V) ∈ S.carrier := by
  set U' := sSup {W | W ≤ U ∧ (W, V) ∈ S.carrier}
  have hU' : (U', V) ∈ S.carrier := S.sSup_left _ V fun W hW => hW.2
  suffices U ≤ U' from S.mono hU' this le_rfl
  by_contra hne
  obtain ⟨x, ⟨hxU, hxU'⟩, T, hTZ, hT, O, hO, hxO, hOT⟩ :=
    hG ((U : Set X) \ U') ⟨U, (U' : Set X)ᶜ, U.2, U'.2.isClosed_compl, sdiff_eq _ _⟩
      (sdiff_nonempty.2 hne)
  let U'' : Opens X := ⟨O ∩ U, hO.inter U.2⟩
  have key : (U' ⊔ U'', V) ∈ S.carrier := by
    refine S.mono (S.sSup_right _ {W | (U' ⊔ U'', W) ∈ S.carrier} fun W hW => hW) le_rfl ?_
    intro y hy
    obtain ⟨A, B, hAB, hyB, hTA⟩ : ∃ A B, (A, B) ∈ S.carrier ∧ y ∈ B ∧ T ⊆ A := by
      refine hT.induction_on (p := fun s => ∃ A B, (A, B) ∈ S.carrier ∧ y ∈ B ∧ s ⊆ A)
        ⟨⊥, ⊤, S.bot_top, trivial, empty_subset _⟩ ?_ ?_ ?_
      · exact fun s t hst ⟨A, B, h1, h2, h3⟩ => ⟨A, B, h1, h2, hst.trans h3⟩
      · rintro s t ⟨A, B, h1, h2, h3⟩ ⟨A', B', h1', h2', h3'⟩
        exact ⟨A ⊔ A', B ⊓ B', S.sup_left (S.mono h1 le_rfl inf_le_left)
          (S.mono h1' le_rfl inf_le_right), ⟨h2, h2'⟩, union_subset_union h3 h3'⟩
      · intro t ht
        obtain ⟨A, hA, B, hAB, hyB⟩ := by simpa using h (mk_mem_prod (hTZ ht).1 hy)
        exact ⟨A, mem_nhdsWithin_of_mem_nhds (A.2.mem_nhds hA), A, B, hAB, hyB, subset_rfl⟩
    refine Opens.mem_sSup.2 ⟨B ⊓ V, ?_, hyB, hy⟩
    refine S.mono (S.sup_left (S.mono hU' le_rfl inf_le_right) (S.mono hAB le_rfl inf_le_left))
      ?_ le_rfl
    rintro z (hz | ⟨hzO, hzU⟩)
    exacts [Or.inl hz, (em _).imp_right fun hz' => hTA (hOT ⟨hzO, hzU, hz'⟩)]
  have : U'' ≤ U' := le_sSup ⟨fun z hz => hz.2, S.mono key le_sup_right le_rfl⟩
  exact hxU' (this ⟨hxO, hxU⟩)

/-- The rectangles contained in `W ⊆ X × Y`. -/
def rect (W : Set (X × Y)) : CIdeal X Y where
  carrier := {p | (p.1 : Set X) ×ˢ (p.2 : Set Y) ⊆ W}
  mono h hU hV := (prod_mono hU hV).trans h
  sSup_left s V hs := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨U, hU, hxU⟩ := Opens.mem_sSup.1 hx
    exact hs U hU ⟨hxU, hy⟩
  sSup_right U s hs := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨V, hV, hyV⟩ := Opens.mem_sSup.1 hy
    exact hs V hV ⟨hx, hyV⟩

/-- An open `W` is the union of the rectangles inside it. -/
theorem iUnion_rect {W : Set (X × Y)} (hW : IsOpen W) :
    ⋃ p ∈ (rect W).carrier, (p.1 : Set X) ×ˢ (p.2 : Set Y) = W := by
  refine subset_antisymm (iUnion₂_subset fun p hp => hp) fun ⟨x, y⟩ hxy => ?_
  obtain ⟨u, v, hu, hv, hx, hy, huv⟩ := isOpen_prod_iff.1 hW x y hxy
  exact mem_biUnion (x := ((⟨u, hu⟩ : Opens X), (⟨v, hv⟩ : Opens Y)))
    (show _ ∈ (rect W).carrier from huv) ⟨hx, hy⟩

/-- Under `HypG X`, every `CIdeal` is `rect` of the union of its rectangles. -/
theorem eq_rect (hG : HypG X) (S : CIdeal X Y) :
    S.carrier = (rect (⋃ p ∈ S.carrier, (p.1 : Set X) ×ˢ (p.2 : Set Y))).carrier :=
  subset_antisymm (fun _ hp => subset_biUnion_of_mem (u := fun p : Opens X × Opens Y =>
    (p.1 : Set X) ×ˢ (p.2 : Set Y)) hp) fun p hp => covering hG S p.1 p.2 hp

end Grothendieck.Folder161_3
