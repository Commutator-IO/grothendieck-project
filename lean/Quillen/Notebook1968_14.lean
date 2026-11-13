import Mathlib

/-!
# Quillen, notebook 1968-14, pp. 27–28: maps whose preimages of closed sets away from `A` are compact

Daniel Quillen's research notebook 1968-14 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201968/1968-14.pdf>) sets up, in
December 1968, a bordism description of homology relative to a closed subset `A` of a manifold
`X`: the cycles are maps `f : V → X \ A` such that `f⁻¹ B` is compact for every closed `B ⊆ X`
disjoint from `A`. On p. 26 he notes that for `X` compact this is the same as `f` being proper.
On p. 27 he proves a proposition on inductive limits over the compact subsets of `A`, and the
heart of the proof is that such an `f` has `closure (f V) ∩ A` compact: otherwise a discrete
sequence in it, approached by values `f xₙ` with `xₙ` leaving an exhaustion of `V` by compact
sets, gives a closed set `B` disjoint from `A` with `f⁻¹ B` not compact. The remark at the top of
p. 28 records, in our words, that the condition is equivalent to: `f` is proper as a map to
`X \ A`, and the closure of `f V` in `X` is compact.

This file proves that equivalence, for any metrizable space `X`, any subset `A` (closed or not),
any topological space `V` and any continuous `f : V → X` avoiding `A`. Local compactness of `X`,
σ-compactness of `V` (the exhaustion on the page) and closedness of `A` are not needed: the proof
uses sequences of values of `f` instead of an exhaustion of `V`.

* `exists_mapClusterPt`: under the condition, every sequence `f ∘ v` has a cluster point in `X`;
* `isCompact_closure_range`: under the condition, `closure (range f)` is compact;
* `isProperMap_codRestrict`: under the condition, `f` is proper as a map to `Aᶜ`;
* `isCompact_preimage_of_isProperMap`: the converse;
* `preimage_compact_iff`: the equivalence of the remark on p. 28.
-/

open Filter Topology Set

namespace Quillen.Notebook1968_14

variable {X V : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
  [TopologicalSpace V] {A : Set X} {f : V → X}

/-- In a T1 space, a point of the closure of the range of a sequence that is not itself a value
of the sequence is a cluster point of the sequence. -/
theorem mapClusterPt_of_mem_closure_range {u : ℕ → X} {y : X} (hy : y ∈ closure (range u))
    (hy' : y ∉ range u) : MapClusterPt y atTop u := by
  refine mapClusterPt_iff_frequently.2 fun s hs => frequently_atTop.2 fun N => ?_
  have hfin : IsClosed (u '' Iio N) := ((finite_Iio N).image u).isClosed
  have hyN : y ∉ u '' Iio N := fun h => hy' (image_subset_range _ _ h)
  have ht : s ∩ (u '' Iio N)ᶜ ∈ 𝓝 y := inter_mem hs (hfin.isOpen_compl.mem_nhds hyN)
  obtain ⟨_, ⟨hzs, hzN⟩, ⟨n, rfl⟩⟩ := mem_closure_iff_nhds.mp hy _ ht
  exact ⟨n, not_lt.1 fun hn => hzN ⟨n, hn, rfl⟩, hzs⟩

/-- If `f⁻¹ B` is compact for every closed `B` disjoint from `A`, then for every sequence `v`
in `V` the sequence `f ∘ v` has a cluster point in `X`. Otherwise its set of values is closed,
discrete and disjoint from `A`, and its preimage, compact, would give a cluster point of `v`. -/
theorem exists_mapClusterPt (hf : Continuous f) (hfA : ∀ v, f v ∉ A)
    (h : ∀ B, IsClosed B → Disjoint B A → IsCompact (f ⁻¹' B)) (v : ℕ → V) :
    ∃ y, MapClusterPt y atTop (f ∘ v) := by
  by_contra! hno
  have hB : IsClosed (range (f ∘ v)) := isClosed_of_closure_subset fun y hy =>
    of_not_not fun hy' => hno y (mapClusterPt_of_mem_closure_range hy hy')
  have hBA : Disjoint (range (f ∘ v)) A := Set.disjoint_left.2 (by rintro _ ⟨n, rfl⟩; exact hfA _)
  have hle : map v atTop ≤ 𝓟 (f ⁻¹' range (f ∘ v)) :=
    le_principal_iff.mpr (Filter.mem_map.mpr (Eventually.of_forall fun n => ⟨n, rfl⟩))
  obtain ⟨w, -, hw⟩ := h _ hB hBA hle
  exact hno _ (MapClusterPt.continuousAt_comp hf.continuousAt hw)

/-- If `f⁻¹ B` is compact for every closed `B` disjoint from `A`, then the closure of the image
of `f` is compact. -/
theorem isCompact_closure_range (hf : Continuous f) (hfA : ∀ v, f v ∉ A)
    (h : ∀ B, IsClosed B → Disjoint B A → IsCompact (f ⁻¹' B)) :
    IsCompact (closure (range f)) := by
  let _ := TopologicalSpace.metrizableSpaceMetric X
  refine IsSeqCompact.isCompact fun z hz => ?_
  -- Approach each `z n` by a value `f (v n)` within `1 / (n + 1)`.
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  choose x hx hdist using fun n => Metric.mem_closure_iff.mp (hz n) _ (hpos n)
  choose v hv using hx
  obtain ⟨y, hy⟩ := exists_mapClusterPt hf hfA h v
  obtain ⟨φ, hφ, hlim⟩ := Filter.subseq_tendsto_of_neBot hy
  have hxv : ∀ n, x n = f (v n) := fun n => (hv n).symm
  have hlim' : Tendsto (z ∘ φ) atTop (𝓝 y) := by
    refine hlim.congr_dist ?_
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat)
    have hk : (k : ℝ) ≤ φ k := by exact_mod_cast hφ.id_le k
    calc dist ((f ∘ v) (φ k)) ((z ∘ φ) k) = dist (z (φ k)) (x (φ k)) := by
          simp [hxv, dist_comm]
      _ ≤ 1 / ((φ k : ℝ) + 1) := (hdist (φ k)).le
      _ ≤ 1 / ((k : ℝ) + 1) := by gcongr
  exact ⟨y, mem_closure_of_tendsto hlim (Eventually.of_forall fun k => ⟨v (φ k), rfl⟩), φ, hφ,
    hlim'⟩

/-- If `f⁻¹ B` is compact for every closed `B` disjoint from `A`, then `f` is proper as a map to
`Aᶜ`. -/
theorem isProperMap_codRestrict (hf : Continuous f) (hfA : ∀ v, f v ∉ A)
    (h : ∀ B, IsClosed B → Disjoint B A → IsCompact (f ⁻¹' B)) :
    IsProperMap (codRestrict f Aᶜ hfA) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hf.codRestrict hfA, fun K hK => ?_⟩
  have hK' : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
  have hdisj : Disjoint (Subtype.val '' K) A :=
    Set.disjoint_left.2 (by rintro _ ⟨y, -, rfl⟩; exact y.2)
  have heq : codRestrict f Aᶜ hfA ⁻¹' K = f ⁻¹' (Subtype.val '' K) := by
    ext w
    exact ⟨fun hw => ⟨_, hw, rfl⟩,
      fun ⟨y, hy, hyw⟩ => by rwa [mem_preimage, ← (Subtype.ext hyw : y = codRestrict f Aᶜ hfA w)]⟩
  rw [heq]
  exact h _ hK'.isClosed hdisj

/-- Conversely, if `f` is proper as a map to `Aᶜ` and `closure (range f)` is compact, then
`f⁻¹ B` is compact for every closed `B` disjoint from `A`: it is the preimage of the compact set
`B ∩ closure (range f)`, which lies in `Aᶜ`. No hypothesis on `X` beyond the topology is used. -/
theorem isCompact_preimage_of_isProperMap {X : Type*} [TopologicalSpace X] {A : Set X}
    {f : V → X} (hfA : ∀ v, f v ∉ A) (hp : IsProperMap (codRestrict f Aᶜ hfA))
    (hc : IsCompact (closure (range f))) (B : Set X) (hB : IsClosed B) (hBA : Disjoint B A) :
    IsCompact (f ⁻¹' B) := by
  set K : Set (Aᶜ : Set X) := Subtype.val ⁻¹' (B ∩ closure (range f))
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
    have : Aᶜ ∩ (B ∩ closure (range f)) = B ∩ closure (range f) :=
      inter_eq_right.mpr fun x hx => Set.disjoint_left.mp hBA hx.1
    rw [this]
    exact hc.inter_left hB
  have heq : f ⁻¹' B = codRestrict f Aᶜ hfA ⁻¹' K := by
    ext w
    simp only [K, mem_preimage, val_codRestrict_apply, mem_inter_iff, iff_self_and]
    exact fun _ => subset_closure (mem_range_self w)
  rw [heq]
  exact hp.isCompact_preimage hK

/-- **Quillen, notebook 1968-14, p. 28** (the remark after the proposition of p. 27). Let `X` be
a metrizable space, `A ⊆ X` and `f : V → X` a continuous map with values in `X \ A`. Then
`f⁻¹ B` is compact for every closed `B ⊆ X` disjoint from `A` if and only if `f` is proper as a
map to `X \ A` and the closure of `f V` in `X` is compact. -/
theorem preimage_compact_iff (hf : Continuous f) (hfA : ∀ v, f v ∉ A) :
    (∀ B, IsClosed B → Disjoint B A → IsCompact (f ⁻¹' B)) ↔
      IsProperMap (codRestrict f Aᶜ hfA) ∧ IsCompact (closure (range f)) :=
  ⟨fun h => ⟨isProperMap_codRestrict hf hfA h, isCompact_closure_range hf hfA h⟩,
    fun h => isCompact_preimage_of_isProperMap hfA h.1 h.2⟩

end Quillen.Notebook1968_14
