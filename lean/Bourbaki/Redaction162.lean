import Mathlib

/-!
# Bourbaki rédaction n° 162: `C¹` maps in equal dimension send meagre sets to meagre sets

Rédaction n° 162 of the Bourbaki archive (J. Dieudonné, *Variétés différentiables, chapitre I,
différentielles (état 3)*, 1952; Archives Henri Poincaré, item
<https://archives-bourbaki.ahp-numerique.fr/items/show/573>) proves, on p. 88, two
propositions about a continuously differentiable map `θ` from an open subset `A` of `ℝⁿ` to
`ℝⁿ`. Prop. 2: the image of the set of points of `A` where the jacobian of `θ` vanishes is
meagre, a countable union of compact null sets. Prop. 3: the image under `θ` of any meagre
subset of `A` is a meagre subset of `ℝⁿ`. The proof splits a nowhere dense compact set into its
critical part, whose image is a compact null set, and its regular part, covered by finitely
many open sets on which `θ` is a homeomorphism onto an open set.

Both statements are true, and are proved here for a finite-dimensional real normed space `E`
in place of `ℝⁿ`. Equal dimension is essential: in the last section, the first projection
`ℝ × ℝ → ℝ`, a smooth map, sends the nowhere dense line `ℝ × {0}` onto `ℝ`, which is not
meagre.

* `isNowhereDense_image_critical`: for a compact `C ⊆ A`, the image of the critical points
  lying in `C` is nowhere dense (compact and of Haar measure zero, by the fixed-dimension
  Sard lemma `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`);
* `isMeagre_image_critical`: Prop. 2, the image of the critical set is meagre;
* `exists_nhds_isMeagre_image`: near a regular point, `θ` sends meagre sets to meagre sets
  (inverse function theorem, `HasStrictFDerivAt.toOpenPartialHomeomorph`);
* `isMeagre_image`: Prop. 3;
* `not_isMeagre_fst_image`: the first projection `ℝ × ℝ → ℝ` sends a nowhere dense set to a
  non-meagre set, so Prop. 3 fails between spaces of different dimensions.
-/

open Set Filter Topology MeasureTheory

noncomputable section

namespace Bourbaki.Redaction162

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {A : Set E} {f : E → E}

/-- The critical points of `f`: those where the determinant of the derivative vanishes. -/
def critical (f : E → E) : Set E := {x | (fderiv ℝ f x).det = 0}

/-- For a `C¹` map on an open set `A` and a compact `C ⊆ A`, the image of the critical points
lying in `C` is nowhere dense. -/
theorem isNowhereDense_image_critical (hA : IsOpen A) (hf : ContDiffOn ℝ 1 f A) {C : Set E}
    (hC : IsCompact C) (hCA : C ⊆ A) : IsNowhereDense (f '' (C ∩ critical f)) := by
  borelize E
  have hdiff : ∀ x ∈ A, DifferentiableAt ℝ f x := fun x hx =>
    (hf.contDiffAt (hA.mem_nhds hx)).differentiableAt one_ne_zero
  have hdet : ContinuousOn (fun x => (fderiv ℝ f x).det) A :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hA le_rfl)
  have hclosed : IsClosed (C ∩ critical f) :=
    (hdet.mono hCA).preimage_isClosed_of_isClosed hC.isClosed isClosed_singleton
  have hcpt : IsCompact (f '' (C ∩ critical f)) :=
    (hC.of_isClosed_subset hclosed inter_subset_left).image_of_continuousOn
      (hf.continuousOn.mono (inter_subset_left.trans hCA))
  have hnull : (Measure.addHaar : Measure E) (f '' (C ∩ critical f)) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero Measure.addHaar
      (fun x hx => (hdiff x (hCA hx.1)).hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx.2)
  exact IsNowhereDense.of_isClosed_null (μ := Measure.addHaar) hcpt.isClosed hnull

/-- Prop. 2: for a `C¹` map on an open set `A`, the image of the critical points in `A` is
meagre. -/
theorem isMeagre_image_critical (hA : IsOpen A) (hf : ContDiffOn ℝ 1 f A) :
    IsMeagre (f '' (A ∩ critical f)) := by
  have hball : ∀ x, ∃ r : ℝ, x ∈ A → 0 < r ∧ Metric.closedBall x r ⊆ A := by
    intro x
    by_cases hx : x ∈ A
    · obtain ⟨r, hr, hrA⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hA.mem_nhds hx)
      exact ⟨r, fun _ => ⟨hr, hrA⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose r hr using hball
  obtain ⟨t, htA, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := A) (f := fun x => Metric.closedBall x (r x))
    fun x hx => mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x (hr x hx).1)
  refine (isMeagre_biUnion htc fun x hx =>
    (isNowhereDense_image_critical hA hf (isCompact_closedBall x (r x))
      (hr x (htA hx)).2).isMeagre).mono ?_
  rintro _ ⟨y, ⟨hyA, hyc⟩, rfl⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hcover hyA)
  exact mem_iUnion₂.2 ⟨x, hx, y, ⟨hyx, hyc⟩, rfl⟩

/-- Near a regular point of a `C¹` map, the image of a meagre set is meagre. -/
theorem exists_nhds_isMeagre_image (hA : IsOpen A) (hf : ContDiffOn ℝ 1 f A) {x : E}
    (hx : x ∈ A) (hreg : (fderiv ℝ f x).det ≠ 0) :
    ∃ U ∈ 𝓝 x, ∀ B : Set E, IsMeagre B → IsMeagre (f '' (B ∩ U)) := by
  set L := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hreg
  have hstrict : HasStrictFDerivAt f (L : E →L[ℝ] E) x := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hf.contDiffAt (hA.mem_nhds hx)).hasStrictFDerivAt one_ne_zero
  set e := hstrict.toOpenPartialHomeomorph f
  refine ⟨e.source, e.open_source.mem_nhds hstrict.mem_toOpenPartialHomeomorph_source,
    fun B hB => ?_⟩
  have hB' : IsMeagre ((Subtype.val : e.source → E) ⁻¹' B) :=
    hB.preimage_of_isOpenMap continuous_subtype_val e.open_source.isOpenMap_subtype_val
  have himg := e.isOpenEmbedding_restrict.isInducing.isMeagre_image hB'
  convert himg using 1
  ext z
  constructor
  · rintro ⟨y, ⟨hyB, hys⟩, rfl⟩
    exact ⟨⟨y, hys⟩, hyB, rfl⟩
  · rintro ⟨⟨y, hys⟩, hyB, rfl⟩
    exact ⟨y, ⟨hyB, hys⟩, rfl⟩

/-- Prop. 3: a `C¹` map from an open subset `A` of `E` to `E` sends meagre subsets of `A` to
meagre subsets of `E`. (Since `A` is open, a subset of `A` is meagre in `A` exactly when it is
meagre in `E`.) -/
theorem isMeagre_image (hA : IsOpen A) (hf : ContDiffOn ℝ 1 f A) {B : Set E} (hBA : B ⊆ A)
    (hB : IsMeagre B) : IsMeagre (f '' B) := by
  have hloc : ∀ x, ∃ U : Set E, x ∈ A → (fderiv ℝ f x).det ≠ 0 →
      U ∈ 𝓝 x ∧ IsMeagre (f '' (B ∩ U)) := by
    intro x
    by_cases h : x ∈ A ∧ (fderiv ℝ f x).det ≠ 0
    · obtain ⟨U, hU, hUB⟩ := exists_nhds_isMeagre_image hA hf h.1 h.2
      exact ⟨U, fun _ _ => ⟨hU, hUB B hB⟩⟩
    · exact ⟨univ, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose U hU using hloc
  set R := A \ critical f
  obtain ⟨t, htR, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := R)
    (f := U) fun x hx => mem_nhdsWithin_of_mem_nhds (hU x hx.1 hx.2).1
  have hreg : IsMeagre (⋃ x ∈ t, f '' (B ∩ U x)) :=
    isMeagre_biUnion htc fun x hx => (hU x (htR hx).1 (htR hx).2).2
  refine ((isMeagre_image_critical hA hf).union hreg).mono ?_
  rintro _ ⟨y, hyB, rfl⟩
  by_cases hyc : y ∈ critical f
  · exact Or.inl ⟨y, ⟨hBA hyB, hyc⟩, rfl⟩
  · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hcover ⟨hBA hyB, hyc⟩)
    exact Or.inr (mem_iUnion₂.2 ⟨x, hx, y, ⟨hyB, hyx⟩, rfl⟩)

/-- Equal dimension is needed: the first projection `ℝ × ℝ → ℝ`, of class `C^n` for every
`n`, sends the nowhere dense line `ℝ × {0}` onto `ℝ`, which is not meagre. -/
theorem not_isMeagre_fst_image :
    (∀ n : WithTop ℕ∞, ContDiff ℝ n (Prod.fst : ℝ × ℝ → ℝ)) ∧
      IsNowhereDense (univ ×ˢ {0} : Set (ℝ × ℝ)) ∧
      ¬ IsMeagre (Prod.fst '' (univ ×ˢ {0} : Set (ℝ × ℝ))) := by
  refine ⟨fun n => contDiff_fst, ?_, ?_⟩
  · rw [(isClosed_univ.prod isClosed_singleton).isNowhereDense_iff, interior_prod_eq,
      interior_singleton, prod_empty]
  · rw [fst_image_prod _ (singleton_nonempty _)]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty

end Bourbaki.Redaction162
