import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval

/-!
# Bourbaki, rédaction n° 205, « Topologie élémentaire, ch. III » (état 1), exercise 2, p. 45

Exercise 2 of the list closing rédaction 205 (rédaction n° 205, p. 45) characterises coverings of a
connected, locally connected base `X` (satisfying a condition named (RU)): a map `p : Y → X` would
be a covering as soon as its fibres are discrete and every continuous map from the square `I²` to
`X` lifts continuously, and uniquely once the lift of one point is chosen. As written, this is
false, already over `X = [0, 1]`, which is connected, locally connected and contractible.

**The counterexample.** Let `Y ⊆ [0, 1] × ℝ × ℝ` be the union of the segment `{(x, 0, 0)}` and,
for `n ≥ 1`, of the graphs `{(x, |n x - 1|, 1/n)}`, and let `p` be the first projection. In Lean,
sheet `n` is the graph of `x ↦ (height n x, n⁻¹)`, where `height 0 = 0` and `(0 : ℝ)⁻¹ = 0`, so
that sheet `0` is the segment. Every sheet is the image of a continuous section of `p`, and a point
of `Y` is determined by its first and last coordinates. The last coordinate (the *level*) is a
continuous function on `Y` with countably many values, hence constant on every connected set: a
lift of a map from a connected space stays on one sheet, which gives existence and uniqueness of
lifts. But the sheet `0` is not open in `Y`: the points `(1/n, 0, 1/n)` of sheet `n` and
`(1/n, 0, 0)` of sheet `0` have the same image and both tend to `(0, 0, 0)`, so `p` is not
injective on any neighbourhood of that point.

**What is proved.**
* `not_isLocallyInjective_proj`, `not_isLocalHomeomorph_proj`, `not_isCoveringMap_proj`: `p` is
  not locally injective at `(0, 0, 0)`, hence neither a local homeomorphism nor a covering map.
* `discreteTopology_fiber`: every fibre `p⁻¹(x)` is discrete.
* `existsUnique_lift`: for any preconnected space `Z`, any continuous `f : Z → [0, 1]`, any
  `z₀ : Z` and any `y₀` over `f z₀`, there is a unique continuous lift `F : Z → Y` of `f` with
  `F z₀ = y₀`. `existsUnique_lift_square` and `existsUnique_lift_path` are the cases `Z = I²`
  (the exercise's condition 2) and `Z = I`.
* `level_eq_of_isPreconnected`: the lemma behind uniqueness, that a continuous real function with
  countable range on a preconnected space is constant.

Hence the space `Y` satisfies conditions 1) and 2) of the exercise without being a covering. The
corrected statement asks in addition that `p` be a local homeomorphism (which the exercise's own
parenthetical example assumes), or that `Y` be locally connected; it is textbook (Spanier,
*Algebraic Topology*, ch. 2, § 4; locator unchecked). Mathlib has the lifting side in
`Mathlib/Topology/Homotopy/Lifting.lean`: homotopy lifting for a separated local homeomorphism
(`IsLocalHomeomorph.monodromy_theorem`) and path lifting for a covering map
(`IsCoveringMap.liftPath`, `IsCoveringMap.existsUnique_continuousMap_lifts`).

**Not formalised.** The condition (RU) of the rédaction is not stated; `[0, 1]` satisfies any
reasonable reading of it (it is contractible and has a basis of contractible open sets). The
corrected characterisation itself is not proved.
-/

namespace Bourbaki.Redaction205

open Set Filter Topology unitInterval

/-- The second coordinate of sheet `n` over `x`: `0` on sheet `0`, `|n x - 1|` on sheet `n ≥ 1`. -/
noncomputable def height (n : ℕ) (x : ℝ) : ℝ := if n = 0 then 0 else |n * x - 1|

/-- Each height function is continuous. -/
theorem continuous_height (n : ℕ) : Continuous (height n) := by
  unfold height
  split_ifs <;> fun_prop

/-- The point of sheet `n` over `x`: `(x, height n x, n⁻¹)`, with `(0 : ℝ)⁻¹ = 0`. -/
noncomputable def sheetPt (n : ℕ) (x : I) : I × ℝ × ℝ := (x, height n x, (n : ℝ)⁻¹)

/-- The total space `Y`, the union of all the sheets. -/
def Y : Set (I × ℝ × ℝ) := {q | ∃ n : ℕ, sheetPt n q.1 = q}

/-- The projection `p : Y → [0, 1]`, the first coordinate. -/
def proj (y : Y) : I := y.1.1

/-- The level of a point of `Y`, its last coordinate: `n⁻¹` on sheet `n`. -/
def level (y : Y) : ℝ := y.1.2.2

/-- The projection is continuous. -/
theorem continuous_proj : Continuous proj := by unfold proj; fun_prop

/-- The level is continuous. -/
theorem continuous_level : Continuous level := by unfold level; fun_prop

/-- Sheet `n` as a continuous section of `p`. -/
noncomputable def sheet (n : ℕ) : C(I, Y) where
  toFun x := ⟨sheetPt n x, n, rfl⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    unfold sheetPt
    have := continuous_height n
    fun_prop

/-- Sheet `n` is a section of `p`. -/
@[simp] theorem proj_sheet (n : ℕ) (x : I) : proj (sheet n x) = x := rfl

/-- Sheet `n` lies at level `n⁻¹`. -/
@[simp] theorem level_sheet (n : ℕ) (x : I) : level (sheet n x) = (n : ℝ)⁻¹ := rfl

/-- Every point of `Y` lies on some sheet. -/
theorem exists_eq_sheet (y : Y) : ∃ n : ℕ, y = sheet n (proj y) := by
  obtain ⟨n, hn⟩ := y.2
  exact ⟨n, Subtype.ext hn.symm⟩

/-- A point of `Y` is determined by its projection and its level. -/
theorem eq_of_proj_eq_of_level_eq {y z : Y} (hp : proj y = proj z) (hl : level y = level z) :
    y = z := by
  obtain ⟨m, hm⟩ := exists_eq_sheet y
  obtain ⟨n, hn⟩ := exists_eq_sheet z
  have hmn : m = n := by
    have h1 := congrArg level hm
    have h2 := congrArg level hn
    rw [level_sheet] at h1 h2
    exact_mod_cast inv_inj.mp (h1.symm.trans (hl.trans h2))
  rw [hm, hn, hmn, hp]

/-! ### `p` is not a covering map -/

/-- The abscissa `1 / (n + 1)`. -/
noncomputable def xn (n : ℕ) : I :=
  ⟨1 / ((n : ℝ) + 1), by positivity,
    (div_le_one (by positivity)).2 (by linarith [n.cast_nonneg (α := ℝ)])⟩

/-- The point `(1/(n+1), 0, 1/(n+1))` of sheet `n + 1`. -/
noncomputable def a (n : ℕ) : Y := sheet (n + 1) (xn n)

/-- The point `(1/(n+1), 0, 0)` of sheet `0`. -/
noncomputable def b (n : ℕ) : Y := sheet 0 (xn n)

/-- The abscissae `1 / (n + 1)` tend to `0`. -/
theorem tendsto_xn : Tendsto xn atTop (𝓝 0) := by
  rw [tendsto_subtype_rng]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The coordinates of `a n`: its height is `|(n + 1) / (n + 1) - 1| = 0`. -/
theorem coe_a (n : ℕ) : (a n : I × ℝ × ℝ) = (xn n, 0, (xn n : ℝ)) := by
  have h : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp [a, sheet, sheetPt, height, xn, h]

/-- The coordinates of `b n`. -/
theorem coe_b (n : ℕ) : (b n : I × ℝ × ℝ) = (xn n, 0, 0) := by
  simp [b, sheet, sheetPt, height]

/-- The point `(0, 0, 0)` is the point of sheet `0` over `0`. -/
theorem coe_sheet_zero_zero : (sheet 0 0 : I × ℝ × ℝ) = (0, 0, 0) := by
  simp [sheet, sheetPt, height]

/-- The points `a n` of the sheets `n + 1` tend to `(0, 0, 0)`. -/
theorem tendsto_a : Tendsto a atTop (𝓝 (sheet 0 0)) := by
  rw [tendsto_subtype_rng, coe_sheet_zero_zero]
  simp_rw [coe_a]
  refine tendsto_xn.prodMk_nhds (tendsto_const_nhds.prodMk_nhds ?_)
  exact (continuous_subtype_val.tendsto _).comp tendsto_xn

/-- The points `b n` of sheet `0` tend to `(0, 0, 0)`. -/
theorem tendsto_b : Tendsto b atTop (𝓝 (sheet 0 0)) := by
  rw [tendsto_subtype_rng, coe_sheet_zero_zero]
  simp_rw [coe_b]
  exact tendsto_xn.prodMk_nhds tendsto_const_nhds

/-- `a n` and `b n` lie over the same point but at different levels. -/
theorem a_ne_b (n : ℕ) : a n ≠ b n := by
  intro h
  have := congrArg level h
  simp only [a, b, level_sheet, Nat.cast_zero, inv_zero] at this
  exact (inv_ne_zero (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)) this

/-- The projection is not injective on any neighbourhood of `(0, 0, 0)`. -/
theorem not_isLocallyInjective_proj : ¬ IsLocallyInjective proj := by
  intro h
  obtain ⟨U, hU, h0, hinj⟩ := h (sheet 0 0)
  have ha := tendsto_a.eventually (hU.mem_nhds h0)
  have hb := tendsto_b.eventually (hU.mem_nhds h0)
  obtain ⟨n, han, hbn⟩ := (ha.and hb).exists
  exact a_ne_b n (hinj han hbn rfl)

/-- The projection is not a local homeomorphism. -/
theorem not_isLocalHomeomorph_proj : ¬ IsLocalHomeomorph proj :=
  fun h => not_isLocallyInjective_proj h.isLocallyInjective

/-- **The counterexample, first half** (rédaction n° 205, p. 45, exercise 2). The projection
`p : Y → [0, 1]` is not a covering map. -/
theorem not_isCoveringMap_proj : ¬ IsCoveringMap proj :=
  fun h => not_isLocalHomeomorph_proj h.isLocalHomeomorph

/-! ### The fibres are discrete -/

/-- In the fibre over `x`, the point of sheet `n` has an open neighbourhood in `[0, 1] × ℝ × ℝ`
containing no other point of the fibre. -/
theorem isolated (n : ℕ) (x : I) :
    ∃ W : Set (I × ℝ × ℝ), IsOpen W ∧ sheetPt n x ∈ W ∧ ∀ m, sheetPt m x ∈ W → m = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases eq_or_ne (x : ℝ) 0 with hx | hx
    · refine ⟨{q | q.2.1 < 1 / 2}, isOpen_lt (by fun_prop) continuous_const, ?_, ?_⟩
      · simp [sheetPt, height]
      · intro m hm
        by_contra h
        simp [sheetPt, height, h, hx] at hm
        norm_num at hm
    · have hx0 : 0 < (x : ℝ) := lt_of_le_of_ne x.2.1 (Ne.symm hx)
      refine ⟨{q | q.2.1 < 1 / 2} ∩ {q | 3 * q.2.2 < 2 * (x : ℝ)},
        (isOpen_lt (by fun_prop) continuous_const).inter
          (isOpen_lt (by fun_prop) continuous_const), ?_, ?_⟩
      · simp [sheetPt, height, hx0]
      · intro m ⟨h1, h2⟩
        by_contra h
        have hm0 : (0 : ℝ) < m := by positivity
        simp only [sheetPt, height, h, ite_false, mem_ofPred_eq] at h1 h2
        have h3 := mul_lt_mul_of_pos_right h2 hm0
        rw [mul_assoc, inv_mul_cancel₀ hm0.ne', mul_one] at h3
        have h4 := (abs_lt.mp h1).2
        nlinarith
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    refine ⟨{q | q.2.2 ∈ Ioo ((n : ℝ) + 1)⁻¹ ((n : ℝ) - 1 / 2)⁻¹},
      isOpen_Ioo.preimage (by fun_prop), ?_, ?_⟩
    · constructor
      · exact (inv_lt_inv₀ (by positivity) (by positivity)).2 (by linarith)
      · exact (inv_lt_inv₀ (by positivity) (by linarith)).2 (by linarith)
    · intro m ⟨h1, h2⟩
      simp only [sheetPt] at h1 h2
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [Nat.cast_zero, inv_zero] at h1
        exact absurd h1 (not_lt.2 (by positivity))
      · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
        have h1' := (inv_lt_inv₀ (by positivity) hm0).1 h1
        have h2' := (inv_lt_inv₀ hm0 (by linarith)).1 h2
        have e1 : m < n + 1 := by exact_mod_cast h1'
        have e2 : n < m + 1 := by
          have : (n : ℝ) < m + 1 := by linarith
          exact_mod_cast this
        omega

/-- **The counterexample, condition 1)** (rédaction n° 205, p. 45, exercise 2). Every fibre of
`p` is discrete. -/
theorem discreteTopology_fiber (x : I) : DiscreteTopology (proj ⁻¹' {x}) := by
  rw [discreteTopology_iff_singleton_mem_nhds]
  rintro ⟨y, hy⟩
  have hy' : proj y = x := hy
  obtain ⟨n, hn⟩ := exists_eq_sheet y
  obtain ⟨W, hW, hnW, hWn⟩ := isolated n x
  have hc : Continuous fun z : proj ⁻¹' {x} => ((z : Y) : I × ℝ × ℝ) := by fun_prop
  refine Filter.mem_of_superset ((hW.preimage hc).mem_nhds ?_) ?_
  · change ((y : I × ℝ × ℝ)) ∈ W
    rw [hn, hy']
    exact hnW
  · rintro ⟨z, hz⟩ hzW
    have hz' : proj z = x := hz
    obtain ⟨m, hm⟩ := exists_eq_sheet z
    change ((z : I × ℝ × ℝ)) ∈ W at hzW
    rw [hm, hz'] at hzW
    have hmn := hWn m hzW
    refine Subtype.ext ?_
    change z = y
    rw [hm, hn, hz', hy', hmn]

/-! ### Unique lifting from connected spaces -/

/-- A continuous real function with countable range on a preconnected space is constant. -/
theorem level_eq_of_isPreconnected {Z : Type*} [TopologicalSpace Z] [PreconnectedSpace Z]
    {g : Z → ℝ} (hg : Continuous g) (hc : (range g).Countable) (z z' : Z) : g z = g z' := by
  have key : ∀ u v : Z, g u ≤ g v → g u = g v := fun u v huv => by
    have hsub : Icc (g u) (g v) ⊆ range g :=
      (isPreconnected_range hg).Icc_subset (mem_range_self u) (mem_range_self v)
    exact le_antisymm huv (Cardinal.Real.Icc_countable_iff.1 (hc.mono hsub))
  rcases le_total (g z) (g z') with h | h
  · exact key z z' h
  · exact (key z' z h).symm

/-- **The counterexample, condition 2)** (rédaction n° 205, p. 45, exercise 2). Over any
preconnected space `Z`, a continuous map `f : Z → [0, 1]` has a unique continuous lift through `p`
taking a prescribed value `y₀` over `f z₀` at `z₀`. -/
theorem existsUnique_lift {Z : Type*} [TopologicalSpace Z] [PreconnectedSpace Z] (f : C(Z, I))
    {z₀ : Z} {y₀ : Y} (h : proj y₀ = f z₀) :
    ∃! F : C(Z, Y), proj ∘ F = f ∧ F z₀ = y₀ := by
  obtain ⟨n, hn⟩ := exists_eq_sheet y₀
  refine ⟨(sheet n).comp f, ⟨rfl, ?_⟩, ?_⟩
  · change sheet n (f z₀) = y₀
    rw [← h, ← hn]
  · rintro G ⟨hG, hG₀⟩
    ext1 z
    apply eq_of_proj_eq_of_level_eq ((congrFun hG z).trans (proj_sheet n (f z)).symm)
    have hc : (range (level ∘ G)).Countable := by
      refine (countable_range fun m : ℕ => (m : ℝ)⁻¹).mono ?_
      rintro _ ⟨w, rfl⟩
      obtain ⟨m, hm⟩ := exists_eq_sheet (G w)
      exact ⟨m, by rw [Function.comp_apply, hm, level_sheet]⟩
    have := level_eq_of_isPreconnected (continuous_level.comp G.continuous) hc z z₀
    simp only [Function.comp_apply, hG₀] at this
    rw [this, hn]
    rfl

/-- The case of the square `I²`, as in condition 2) of the exercise. -/
theorem existsUnique_lift_square (f : C(I × I, I)) {y₀ : Y} (h : proj y₀ = f (0, 0)) :
    ∃! F : C(I × I, Y), proj ∘ F = f ∧ F (0, 0) = y₀ :=
  existsUnique_lift f h

/-- The case of paths. -/
theorem existsUnique_lift_path (f : C(I, I)) {y₀ : Y} (h : proj y₀ = f 0) :
    ∃! F : C(I, Y), proj ∘ F = f ∧ F 0 = y₀ :=
  existsUnique_lift f h

end Bourbaki.Redaction205
