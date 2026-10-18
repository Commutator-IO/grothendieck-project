import Mathlib

/-!
# Bourbaki rédaction n° 288: the exponential law for compact convergence

Rédaction n° 288 (1958) of the Bourbaki archive is a counter-draft for chapter X of
*Topologie générale* (Archives Henri Poincaré, item
<https://archives-bourbaki.ahp-numerique.fr/items/show/689>). On PDF pp. 32–33, Grothendieck,
rédaction n° 288, states Cor. 2: for `F` locally compact and `E` Hausdorff, the natural bijection
`C(E × F, G) → C(E, C(F, G))` is a homeomorphism for the topologies of compact convergence; a
typed N.B. suspects that it fails when `E` is not Hausdorff.

mathlib (`Mathlib/Topology/CompactOpen.lean`) has currying for all spaces, the continuity of
`ContinuousMap.curry` under `LocallyCompactSpace (X × Y)`, the continuity of
`ContinuousMap.uncurry` under `LocallyCompactSpace X` and `LocallyCompactSpace Y`, and
`Homeomorph.curry` under both of these. It has nothing for `X` Hausdorff and not locally compact,
such as `ℚ`.

The proof needs one property of `X`, `CompactsLocallyCompact X`: every point of a compact set `K`
has arbitrarily small neighbourhoods within `K` that are compact. It holds when `X` is locally
compact and when `X` is `R1Space` (preregular), hence when `X` is Hausdorff.

* `continuous_curry`: currying is continuous under `CompactsLocallyCompact X`, with no hypothesis
  on `Y` or `Z`;
* `continuous_uncurry`: uncurrying is continuous under `CompactsLocallyCompact X` and
  `LocallyCompactSpace Y`;
* `curryHomeomorph`, `curryHomeomorphOfR1`: the homeomorphism `C(X × Y, Z) ≃ₜ C(X, C(Y, Z))`,
  which gives Cor. 2 with `E` preregular and `F` locally compact in mathlib's sense (no
  Hausdorff hypothesis on `F`).

Both continuity proofs cover a compact set by finitely many pieces through
`IsCompact.induction_on`; the page uses `E` Hausdorff at the same place, to cover a compact
`M ⊆ E × F` by compact rectangles. In mathlib a compact set need not be Hausdorff; in Bourbaki
« compact » includes Hausdorff, so the compact-open topology only sees Hausdorff compact sets,
which always satisfy the property above, but the projection on `E` of such a compact subset of
`E × F` need not be Hausdorff when `E` is not. Whether Cor. 2 holds for every `E` is not decided
here, in either convention.
-/

open Set Filter Topology

namespace Grothendieck.Bourbaki288

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Points of a compact subset `K` of `X` have arbitrarily small neighbourhoods within `K`
that are compact in `X`. -/
def CompactsLocallyCompact (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ K : Set X, IsCompact K → ∀ x ∈ K, ∀ V ∈ 𝓝 x, ∃ C, IsCompact C ∧ C ⊆ V ∧ C ∈ 𝓝[K] x

theorem compactsLocallyCompact_of_locallyCompactSpace [LocallyCompactSpace X] :
    CompactsLocallyCompact X := fun _ _ _ _ _ hV ↦
  let ⟨C, hCx, hCV, hC⟩ := local_compact_nhds hV
  ⟨C, hC, hCV, mem_nhdsWithin_of_mem_nhds hCx⟩

theorem compactsLocallyCompact_of_r1Space [R1Space X] : CompactsLocallyCompact X := by
  intro K hK x hx V hV
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨L, hLx, hL, hLV⟩ := exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds
    (x := (⟨x, hx⟩ : K)) continuous_subtype_val hV isCompact_univ univ_mem
  exact ⟨_, hL.image continuous_subtype_val, image_subset_iff.2 hLV,
    nhdsWithin_eq_map_subtype_coe hx ▸ image_mem_map hLx⟩

/-- Currying is continuous for the compact-open topologies when compact subsets of `X` are
locally compact in the above sense; nothing is assumed on `Y` or `Z`. -/
theorem continuous_curry (hX : CompactsLocallyCompact X) :
    Continuous (ContinuousMap.curry : C(X × Y, Z) → C(X, C(Y, Z))) := by
  refine continuous_iff_continuousAt.2 fun f ↦ ContinuousMap.tendsto_nhds_compactOpen.2 ?_
  intro K hK W hW hfW
  refine hK.induction_on (p := fun S ↦ ∀ᶠ f' in 𝓝 f, MapsTo (ContinuousMap.curry f') S W)
    (.of_forall fun _ ↦ mapsTo_empty _ _) (fun s t hst h ↦ h.mono fun _ h ↦ h.mono_left hst)
    (fun s t hs ht ↦ (hs.and ht).mono fun _ h ↦ h.1.union h.2) fun x hx ↦ ?_
  have key : Tendsto (fun p : C(X × Y, Z) × X ↦ ContinuousMap.curry p.1 p.2)
      (𝓝 f ×ˢ 𝓝[K] x) (𝓝 (ContinuousMap.curry f x)) := by
    refine ContinuousMap.tendsto_nhds_compactOpen.2 fun L hL U hU hxL ↦ ?_
    have hV : ∀ᶠ x' in 𝓝 x, ∀ y ∈ L, f (x', y) ∈ U :=
      hL.eventually_forall_of_forall_eventually fun y hy ↦
        f.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds (hxL hy))
    obtain ⟨C, hC, hCV, hCx⟩ := hX K hK x hx _ hV
    exact ((ContinuousMap.eventually_mapsTo (hC.prod hL) hU fun p hp ↦ hCV hp.1 p.2 hp.2).prod_mk
      hCx).mono fun p hp y hy ↦ hp.1 ⟨hp.2, hy⟩
  obtain ⟨pa, hpa, pb, hpb, h⟩ := eventually_prod_iff.1 (key.eventually (hW.mem_nhds (hfW hx)))
  exact ⟨_, hpb, hpa.mono fun _ ha _ hb ↦ h ha hb⟩

/-- Uncurrying is continuous for the compact-open topologies when `Y` is locally compact and
compact subsets of `X` are locally compact in the above sense. -/
theorem continuous_uncurry [LocallyCompactSpace Y] (hX : CompactsLocallyCompact X) :
    Continuous (ContinuousMap.uncurry : C(X, C(Y, Z)) → C(X × Y, Z)) := by
  refine continuous_iff_continuousAt.2 fun g ↦ ContinuousMap.tendsto_nhds_compactOpen.2 ?_
  intro M hM U hU hgU
  refine hM.induction_on (p := fun S ↦ ∀ᶠ g' in 𝓝 g, MapsTo (ContinuousMap.uncurry g') S U)
    (.of_forall fun _ ↦ mapsTo_empty _ _) (fun s t hst h ↦ h.mono fun _ h ↦ h.mono_left hst)
    (fun s t hs ht ↦ (hs.and ht).mono fun _ h ↦ h.1.union h.2) fun ⟨x, y⟩ hm ↦ ?_
  obtain ⟨L, hLy, hL, hLU⟩ := exists_mem_nhds_isCompact_mapsTo (g x).continuous
    (hU.mem_nhds (hgU hm))
  obtain ⟨C, hC, hCV, hCx⟩ := hX _ (hM.image continuous_fst) x (mem_image_of_mem _ hm) _
    (g.continuous.continuousAt.preimage_mem_nhds
      (ContinuousMap.eventually_mapsTo (U := U) hL hU hLU))
  refine ⟨C ×ˢ L, ?_, (ContinuousMap.eventually_mapsTo hC
    (ContinuousMap.isOpen_setOfPred_mapsTo hL hU) hCV).mono fun g' h p hp ↦ h hp.1 hp.2⟩
  have : M ⊆ (Prod.fst '' M) ×ˢ univ := fun p hp ↦ ⟨mem_image_of_mem Prod.fst hp, mem_univ _⟩
  refine nhdsWithin_mono _ this ?_
  rw [nhdsWithin_prod_eq, nhdsWithin_univ]
  exact prod_mem_prod hCx hLy

/-- **The exponential law** (Grothendieck, rédaction n° 288, Cor. 2, for `X` Hausdorff and `Y`
locally compact Hausdorff): currying is a homeomorphism `C(X × Y, Z) ≃ₜ C(X, C(Y, Z))` for the
compact-open topologies, as soon as `Y` is locally compact and compact subsets of `X` are locally
compact in the above sense. -/
def curryHomeomorph [LocallyCompactSpace Y] (hX : CompactsLocallyCompact X) :
    C(X × Y, Z) ≃ₜ C(X, C(Y, Z)) where
  toFun := ContinuousMap.curry
  invFun := ContinuousMap.uncurry
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_curry hX
  continuous_invFun := continuous_uncurry hX

/-- Cor. 2 of rédaction n° 288 in mathlib's conventions, with `X` only preregular (`R1Space`),
which covers the Hausdorff case. -/
def curryHomeomorphOfR1 [R1Space X] [LocallyCompactSpace Y] : C(X × Y, Z) ≃ₜ C(X, C(Y, Z)) :=
  curryHomeomorph compactsLocallyCompact_of_r1Space

@[simp]
theorem coe_curryHomeomorph [LocallyCompactSpace Y] (hX : CompactsLocallyCompact X) :
    ⇑(curryHomeomorph hX : C(X × Y, Z) ≃ₜ C(X, C(Y, Z))) = ContinuousMap.curry := rfl

/-- The Hausdorff case, as on the page. -/
example [T2Space X] [LocallyCompactSpace Y] : C(X × Y, Z) ≃ₜ C(X, C(Y, Z)) :=
  curryHomeomorphOfR1

end Grothendieck.Bourbaki288
