import Bourbaki.Upstream.ContDiffIsMeagreImage

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

The general statements live in `Bourbaki/Upstream/ContDiffIsMeagreImage.lean`
(`ContDiffOn.isNowhereDense_image_inter_det_fderiv_eq_zero`,
`ContDiffOn.isMeagre_image_inter_det_fderiv_eq_zero`, `ContDiffOn.exists_mem_nhds_isMeagre_image`,
`ContDiffOn.isMeagre_image`, with the critical set written `{x | (fderiv ℝ f x).det = 0}`); the
names below are kept for the articles that cite them. The counterexample stays here.
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
    (hC : IsCompact C) (hCA : C ⊆ A) : IsNowhereDense (f '' (C ∩ critical f)) :=
  hf.isNowhereDense_image_inter_det_fderiv_eq_zero hA hC hCA

/-- Prop. 2: for a `C¹` map on an open set `A`, the image of the critical points in `A` is
meagre. -/
theorem isMeagre_image_critical (hA : IsOpen A) (hf : ContDiffOn ℝ 1 f A) :
    IsMeagre (f '' (A ∩ critical f)) :=
  hf.isMeagre_image_inter_det_fderiv_eq_zero hA

/-- Near a regular point of a `C¹` map, the image of a meagre set is meagre. -/
theorem exists_nhds_isMeagre_image (hA : IsOpen A) (hf : ContDiffOn ℝ 1 f A) {x : E}
    (hx : x ∈ A) (hreg : (fderiv ℝ f x).det ≠ 0) :
    ∃ U ∈ 𝓝 x, ∀ B : Set E, IsMeagre B → IsMeagre (f '' (B ∩ U)) :=
  hf.exists_mem_nhds_isMeagre_image hA hx hreg

/-- Prop. 3: a `C¹` map from an open subset `A` of `E` to `E` sends meagre subsets of `A` to
meagre subsets of `E`. (Since `A` is open, a subset of `A` is meagre in `A` exactly when it is
meagre in `E`.) -/
theorem isMeagre_image (hA : IsOpen A) (hf : ContDiffOn ℝ 1 f A) {B : Set E} (hBA : B ⊆ A)
    (hB : IsMeagre B) : IsMeagre (f '' B) :=
  hf.isMeagre_image hA hBA hB

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
