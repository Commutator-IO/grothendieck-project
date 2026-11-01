import Mathlib

/-!
# Bourbaki rédaction n° 334: a Frobenius-twisted action with zero infinitesimal action

Rédaction n° 334 of the Bourbaki archive (C. Chevalley, *Les espaces fibrés géométriques*,
1960; Archives Henri Poincaré, Fonds Pierre Cartier, PCR 032) works with analytic manifolds
and Lie groups over a complete valued field `K`. In § 1 (pp. 5–8 of the facsimile), a Lie group
`G` acting analytically on `V` acts « effectivement » when every map `h : T → G` from a manifold
`T` such that `(t, x) ↦ h(t) · x` is analytic is itself analytic. The rédaction then claims that
the infinitesimal action `ξ : 𝔤 → Vect(V)` is injective, also in characteristic `p > 0`. The
proof there replaces the analytic structure of `G` by a coarser one `G'` whose functions are
killed by the right-invariant fields of `ker ξ`, with local charts in which `r` coordinates are
replaced by their `p`-th powers, asserted to be homeomorphisms onto open sets of `Kⁿ`.

That step needs `K` perfect. When `K` is imperfect (every local field `F_q((π))` is), the image
`Kᵖ` of Frobenius has empty interior, and the claim itself fails: `K` acting on `K` by
`s · x = x + sᵖ` is a faithful analytic action with zero infinitesimal action, and it is
effective in the strong sense above, because a `Kᵖ`-valued analytic function is the `p`-th power
of an analytic function. This file proves the one-variable facts behind that counterexample.

* `act_add`, `act_injective`: `s · x = x + sᵖ` is an action of `(K, +)`, injective in `s`;
* `hasDerivAt_act`: its derivative in `s` vanishes everywhere, so `ξ = 0`;
* `isClosed_range_pow`: in a complete normed field of characteristic `p`, `Kᵖ` is closed;
* `interior_range_pow_eq_empty`: if `Kᵖ ≠ K`, then `Kᵖ` has empty interior (the chart of the
  rédaction cannot have open image);
* `hasDerivAt_eq_zero_of_mem_range_pow`: if `Kᵖ` is closed and `π ∉ Kᵖ`, a function with
  values in `Kᵖ` has derivative `0` wherever it is differentiable; this is the first step in
  proving that `t ↦ h(t)ᵖ` analytic forces `h` analytic.

The second step of the strong effectivity (identifying the coefficients of a `Kᵖ`-valued power
series as `p`-th powers, using a `Kᵖ`-basis of `K`) is done by hand in the accompanying notes,
not here: analytic functions over a general nontrivially normed field are thin in mathlib.
-/

open Filter Topology

noncomputable section

namespace Bourbaki.Redaction334

variable {K : Type*} (p : ℕ)

section Algebra

variable [CommRing K] [CharP K p] [Fact p.Prime]

/-- The twisted translation `s · x = x + sᵖ` is an action of the additive group. -/
theorem act_add (s t x : K) : x + (s + t) ^ p = (x + t ^ p) + s ^ p := by
  rw [add_pow_char]; ring

/-- The action is faithful on a reduced ring: `sᵖ = tᵖ` forces `s = t`. -/
theorem act_injective [IsReduced K] {s t : K} (h : ∀ x : K, x + s ^ p = x + t ^ p) : s = t :=
  frobenius_inj K p (by simpa [frobenius_def] using h 0)

end Algebra

variable [NontriviallyNormedField K] [CharP K p] [hp : Fact p.Prime]

omit hp in
/-- The derivative of `s ↦ x + sᵖ` is `p sᵖ⁻¹ = 0`: the infinitesimal action is zero. -/
theorem hasDerivAt_act (x s : K) : HasDerivAt (fun s => x + s ^ p) 0 s := by
  have h := (hasDerivAt_pow p s).const_add x
  simpa [CharP.cast_eq_zero] using h

/-- Two `p`-th powers differ by a `p`-th power. -/
theorem sub_mem_range_pow {a b : K} (ha : a ∈ Set.range (· ^ p : K → K))
    (hb : b ∈ Set.range (· ^ p : K → K)) : a - b ∈ Set.range (· ^ p : K → K) := by
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨d, rfl⟩ := hb
  exact ⟨c - d, sub_pow_char c d⟩

/-- In a complete normed field of characteristic `p`, the subfield `Kᵖ` is closed. -/
theorem isClosed_range_pow [CompleteSpace K] : IsClosed (Set.range (· ^ p : K → K)) := by
  have hp0 : 0 < p := hp.out.pos
  refine isClosed_iff_clusterPt.2 fun y hy => ?_
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (mem_closure_iff_clusterPt.2 hy)
  choose c hc using hu
  have hcau : CauchySeq c := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq (ε ^ p) (pow_pos hε p)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hN m hm n hn
    rw [dist_eq_norm, ← hc m, ← hc n, ← sub_pow_char, norm_pow] at h
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ p hε.le h
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨z, tendsto_nhds_unique ((hz.pow p).congr fun n => ?_) hlim⟩
  exact hc n

/-- If `Kᵖ ≠ K`, then `Kᵖ` has empty interior. -/
theorem interior_range_pow_eq_empty {π : K} (hπ : π ∉ Set.range (· ^ p : K → K)) :
    interior (Set.range (· ^ p : K → K)) = ∅ := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  by_contra hne
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior a ha
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K (max 1 (‖π‖ / r))
  have hc1 : 1 < ‖c‖ := lt_of_le_of_lt (le_max_left _ _) hc
  have hc0 : c ≠ 0 := norm_pos_iff.1 (lt_trans one_pos hc1)
  have hcp : ‖c‖ ≤ ‖c‖ ^ p := le_self_pow₀ hc1.le (by omega)
  have hmem : a + π / c ^ p ∈ Set.range (· ^ p : K → K) := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_div, norm_pow,
      div_lt_iff₀ (pow_pos (lt_trans one_pos hc1) p)]
    have : ‖π‖ / r < ‖c‖ ^ p := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hc) hcp
    rwa [div_lt_iff₀ hr, mul_comm] at this
  have ha' : a ∈ Set.range (· ^ p : K → K) := interior_subset ha
  obtain ⟨e, he⟩ := sub_mem_range_pow p hmem ha'
  apply hπ
  refine ⟨c * e, ?_⟩
  simp only at he ⊢
  rw [mul_pow, he, add_sub_cancel_left, mul_div_cancel₀ _ (pow_ne_zero p hc0)]

/-- If `Kᵖ` is closed and `π ∉ Kᵖ`, a `Kᵖ`-valued function has zero derivative wherever it is
differentiable: the difference quotients along `cᵖ` lie in `Kᵖ`, those along `π cᵖ` in
`π⁻¹ Kᵖ`, and these two closed sets meet only in `0`. -/
theorem hasDerivAt_eq_zero_of_mem_range_pow (hS : IsClosed (Set.range (· ^ p : K → K)))
    {π : K} (hπ : π ∉ Set.range (· ^ p : K → K)) {g : K → K}
    (hg : ∀ y, g y ∈ Set.range (· ^ p : K → K)) {t d : K} (hd : HasDerivAt g d t) : d = 0 := by
  set S := Set.range (· ^ p : K → K) with hSdef
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hπ0 : π ≠ 0 := fun h => hπ ⟨0, by simp [h, zero_pow hp0]⟩
  have hslope := hd.tendsto_slope
  -- along `t + (a c)ᵖ`, for a fixed `a ≠ 0`
  have key : ∀ a : K, a ≠ 0 →
      Tendsto (fun c : K => slope g t (t + a * c ^ p)) (𝓝[≠] 0) (𝓝 d) := by
    intro a ha
    refine hslope.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun c : K => t + a * c ^ p) (𝓝 0) (𝓝 (t + a * 0 ^ p)) :=
        (continuous_const.add (continuous_const.mul (continuous_pow p))).tendsto 0
      simpa [zero_pow hp0] using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      simp [ha, pow_ne_zero p (show c ≠ 0 from hc)]
  have hval : ∀ a c : K, a ≠ 0 → c ≠ 0 →
      a * slope g t (t + a * c ^ p) ∈ S := by
    intro a c ha hc
    obtain ⟨e, he⟩ := sub_mem_range_pow p (hg (t + a * c ^ p)) (hg t)
    refine ⟨e / c, ?_⟩
    simp only at he ⊢
    rw [slope_def_field, add_sub_cancel_left, div_pow, he]
    field_simp
  have hmem : ∀ a : K, a ≠ 0 → a * d ∈ S := by
    intro a ha
    refine hS.mem_of_tendsto (((key a ha).const_mul a)) ?_
    filter_upwards [self_mem_nhdsWithin] with c hc using hval a c ha hc
  obtain ⟨u, hu⟩ := hmem 1 one_ne_zero
  obtain ⟨v, hv⟩ := hmem π hπ0
  by_contra hd0
  apply hπ
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp [zero_pow hp0] at hu
    exact hd0 hu.symm
  refine ⟨v / u, ?_⟩
  simp only at hu hv ⊢
  rw [div_pow, hu, hv, one_mul, mul_div_cancel_right₀ _ hd0]

end Bourbaki.Redaction334
