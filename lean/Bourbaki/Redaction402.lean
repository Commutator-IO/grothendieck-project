import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Instances.RatLemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Connected.Clopen

/-!
# Bourbaki, rédaction n° 402 (Koszul, 1964), § 5 n° 1: localizable distances

Rédaction 402, « Géométrie différentielle. Ch. II : Géodésiques », opens its § 5 (rédaction
n° 402, p. 10 of the typescript) with chains: for a neighbourhood `W` of the diagonal of `X × X`,
a `W`-chain from `a` to `b` is a finite sequence `a = x₀, …, xₙ = b` with every pair
`(xᵢ, xᵢ₊₁)` in `W`, and its length for a distance `d` is `∑ d(xᵢ, xᵢ₊₁)`. Definition 1 calls
a distance *localizable* if, for every neighbourhood `W` of the diagonal, `d(a, b)` is the
infimum of the lengths of the `W`-chains from `a` to `b`. Proposition 1 (p. 11) says that two
localizable distances on a connected space agreeing on a neighbourhood of the diagonal are equal;
Proposition 2 (p. 11) that for `a ∈ A` and `b ∉ A`, `d(a, b)` is the infimum of
`d(a, c) + d(c, b)` over the frontier of `A`, with three corollaries.

Since a chain is never shorter than the distance of its ends (triangle inequality), the infimum
condition is stated here as: for every `δ > 0` there is a `W`-chain of length `< d(a, b) + δ`.
This form keeps the existence of chains, which the infimum over an empty set in `ℝ` would hide.

The rédaction quantifies over all neighbourhoods of the diagonal, not only the uniform ones
`{d < ε}`; the proof of Proposition 2 uses a non-uniform one (built from the interior of `A`, the
exterior of `A` and a thickening of its frontier). A handwritten note on the facing page (p. 74 of
the scan) suggests the `ε`-chain form instead. The two are not equivalent: `ℚ` is
`ε`-localizable (chains along an arithmetic progression) but not localizable, since localizable
spaces are connected, and Proposition 2 fails on `ℚ` (`not_exists_mem_frontier_rat`). With the
neighbourhood form, the connectedness hypothesis of the rédaction is a consequence
(`Localizable.preconnectedSpace`) and is not needed in the statements below.

**What is proved.**
* `IsLocalizable d` (for a function `d : X → X → ℝ` on a topological space) and
  `Localizable X` (for the distance of a pseudometric space): Definition 1.
* `eq_of_isLocalizable`: **Proposition 1**, for two functions satisfying the polygon inequality,
  localizable and equal on a neighbourhood of the diagonal: they are equal.
  `PseudoMetricSpace.eq_of_localizable`: the same for two pseudometric structures on one type
  inducing a given topology (the conclusion is equality of the structures);
  `PseudoMetricSpace.eq_of_localizable_of_lt`: when they agree wherever the first is `< r`.
* `Localizable.exists_mem_frontier`: **Proposition 2, the core**: for `a ∈ A`, `b ∉ A` and
  `ε > 0` there is `c` in the frontier of `A` with `d(a, c) + d(c, b) < d(a, b) + ε`.
  `Localizable.dist_eq_iInf_frontier`: **Proposition 2** as an infimum over the frontier.
* `Localizable.infDist_add_infDist_le`: **Corollary 1**, `d(a, F) + d(F, b) ≤ d(a, b)`.
* `Localizable.frontier_ball`: **Corollary 2**, the frontier of the open ball of radius `r > 0`
  is the sphere; `Localizable.closure_ball`: its closure is the closed ball.
* `Localizable.exists_dist_eq_sub`: **Corollary 3**, if the closed ball of centre `a` and
  radius `r > 0` is compact and `d(a, b) ≥ r`, some `c` has `d(a, c) = r` and
  `d(c, b) = d(a, b) - r`.
* `Localizable.preconnectedSpace`: a localizable space is connected (or empty).
* `EpsLocalizable`, `Localizable.epsLocalizable`, `epsLocalizable_rat`, `not_localizable_rat`,
  `not_exists_mem_frontier_rat`: the `ε`-chain variant is strictly weaker.

**Not formalised.** The use of § 5 in the rest of the chapter (the distance of a Riemannian
manifold is localizable). In the literature, localizable distances in the neighbourhood form are
close to length (intrinsic) metrics, for which Burago–Burago–Ivanov, *A Course in Metric
Geometry*, § 2.4, gives the approximate-midpoint characterisation; the chain form above, for
non-complete spaces, was not checked against it. Mathlib has no length-space API (a search for
length spaces, intrinsic metrics and midpoint properties found none).
-/

namespace Bourbaki.Redaction402

open Set Filter Topology Metric Finset

variable {X : Type*}

/-- A chain from `a` to `b` with `n` steps, each step in `W`. -/
def IsChain (W : Set (X × X)) (a b : X) (n : ℕ) (x : ℕ → X) : Prop :=
  x 0 = a ∧ x n = b ∧ ∀ i < n, (x i, x (i + 1)) ∈ W

/-- Definition 1 for a function `d`: for every neighbourhood `W` of the diagonal, `d a b` is
the infimum of the lengths of the `W`-chains from `a` to `b` (stated as: chains of length
`< d a b + δ` exist for every `δ > 0`). -/
def IsLocalizable [TopologicalSpace X] (d : X → X → ℝ) : Prop :=
  ∀ W ∈ 𝓝ˢ (diagonal X), ∀ a b : X, ∀ δ > 0, ∃ n x, IsChain W a b n x ∧
    ∑ i ∈ range n, d (x i) (x (i + 1)) < d a b + δ

/-- Definition 1: the distance of a pseudometric space is localizable. -/
def Localizable (X : Type*) [PseudoMetricSpace X] : Prop :=
  IsLocalizable (X := X) dist

/-- **Proposition 1** (rédaction n° 402, p. 11), for functions: two localizable functions
satisfying the polygon inequality and equal on a neighbourhood of the diagonal are equal. -/
theorem eq_of_isLocalizable [TopologicalSpace X] {d₁ d₂ : X → X → ℝ}
    (p₁ : ∀ (x : ℕ → X) n, d₁ (x 0) (x n) ≤ ∑ i ∈ range n, d₁ (x i) (x (i + 1)))
    (p₂ : ∀ (x : ℕ → X) n, d₂ (x 0) (x n) ≤ ∑ i ∈ range n, d₂ (x i) (x (i + 1)))
    (h₁ : IsLocalizable d₁) (h₂ : IsLocalizable d₂) {W : Set (X × X)}
    (hW : W ∈ 𝓝ˢ (diagonal X)) (h : ∀ p ∈ W, d₁ p.1 p.2 = d₂ p.1 p.2) : d₁ = d₂ := by
  have key : ∀ {d d' : X → X → ℝ},
      (∀ (x : ℕ → X) n, d (x 0) (x n) ≤ ∑ i ∈ range n, d (x i) (x (i + 1))) →
      IsLocalizable d' → (∀ p ∈ W, d p.1 p.2 = d' p.1 p.2) → ∀ a b, d a b ≤ d' a b := by
    intro d d' p hl hdd a b
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    obtain ⟨n, x, ⟨h0, hn, hx⟩, hlen⟩ := hl W hW a b δ hδ
    calc d a b = d (x 0) (x n) := by rw [h0, hn]
      _ ≤ ∑ i ∈ range n, d (x i) (x (i + 1)) := p x n
      _ = ∑ i ∈ range n, d' (x i) (x (i + 1)) :=
          Finset.sum_congr rfl fun i hi => hdd _ (hx i (Finset.mem_range.1 hi))
      _ < d' a b + δ := hlen
  funext a b
  exact le_antisymm (key p₁ h₂ h a b) (key p₂ h₁ (fun p hp => (h p hp).symm) a b)

/-- **Proposition 1** (rédaction n° 402, p. 11): two pseudometric structures on `X`, both
inducing the topology of `X` and both localizable, which have the same distance on a
neighbourhood of the diagonal, are equal. -/
theorem PseudoMetricSpace.eq_of_localizable [t : TopologicalSpace X]
    (m₁ m₂ : PseudoMetricSpace X) (ht₁ : m₁.toUniformSpace.toTopologicalSpace = t)
    (ht₂ : m₂.toUniformSpace.toTopologicalSpace = t) (h₁ : @Localizable X m₁)
    (h₂ : @Localizable X m₂) {W : Set (X × X)} (hW : W ∈ 𝓝ˢ (diagonal X))
    (h : ∀ p ∈ W, m₁.dist p.1 p.2 = m₂.dist p.1 p.2) : m₁ = m₂ := by
  subst ht₁
  unfold Localizable at h₁ h₂
  rw [ht₂] at h₂
  refine PseudoMetricSpace.ext (congrArg Dist.mk ?_)
  exact @eq_of_isLocalizable X m₁.toUniformSpace.toTopologicalSpace _ _
    (fun x n => @dist_le_range_sum_dist X m₁ x n)
    (fun x n => @dist_le_range_sum_dist X m₂ x n) h₁ h₂ W hW h

/-- In a pseudometric space, `{d < r}` is a neighbourhood of the diagonal for `r > 0`. -/
theorem setOf_dist_lt_mem_nhdsSet [PseudoMetricSpace X] {r : ℝ} (hr : 0 < r) :
    {p : X × X | dist p.1 p.2 < r} ∈ 𝓝ˢ (diagonal X) :=
  (isOpen_lt continuous_dist continuous_const).mem_nhdsSet.2 fun p hp => by
    simp only [mem_diagonal_iff] at hp
    simp [hp, hr]

/-- **Proposition 1**, uniform form: two localizable pseudometric structures inducing the
topology of `X` and agreeing wherever the first is `< r`, for some `r > 0`, are equal. -/
theorem PseudoMetricSpace.eq_of_localizable_of_lt [t : TopologicalSpace X]
    (m₁ m₂ : PseudoMetricSpace X) (ht₁ : m₁.toUniformSpace.toTopologicalSpace = t)
    (ht₂ : m₂.toUniformSpace.toTopologicalSpace = t) (h₁ : @Localizable X m₁)
    (h₂ : @Localizable X m₂) {r : ℝ} (hr : 0 < r)
    (h : ∀ a b, m₁.dist a b < r → m₁.dist a b = m₂.dist a b) : m₁ = m₂ := by
  refine PseudoMetricSpace.eq_of_localizable m₁ m₂ ht₁ ht₂ h₁ h₂ ?_ fun p hp => h _ _ hp
  subst ht₁
  exact @setOf_dist_lt_mem_nhdsSet X m₁ r hr

section Prop2

variable [PseudoMetricSpace X]

/-- **Proposition 2, the core** (rédaction n° 402, p. 11): in a localizable space, for `a ∈ A`,
`b ∉ A` and `ε > 0`, some `c` in the frontier of `A` has `d(a, c) + d(c, b) < d(a, b) + ε`. The
chain used is a `W`-chain for `W` the union of `Å × Å`, `V × V` and `(X ∖ Ā) × (X ∖ Ā)`, where
`V` is the `ε/3`-thickening of the frontier: it must pass through `V`. -/
theorem Localizable.exists_mem_frontier (hX : Localizable X) {A : Set X} {a b : X}
    (ha : a ∈ A) (hb : b ∉ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ c ∈ frontier A, dist a c + dist c b < dist a b + ε := by
  by_cases haF : a ∈ frontier A
  · exact ⟨a, haF, by simp [hε]⟩
  by_cases hbF : b ∈ frontier A
  · exact ⟨b, hbF, by simp [hε]⟩
  have ha' : a ∈ interior A := by
    have h := subset_closure ha
    rw [closure_eq_interior_union_frontier] at h
    exact h.resolve_right haF
  have hb' : b ∉ closure A := by
    rw [closure_eq_self_union_frontier]
    rintro (h | h)
    exacts [hb h, hbF h]
  set V := thickening (ε / 3) (frontier A)
  set W : Set (X × X) := interior A ×ˢ interior A ∪ V ×ˢ V ∪ (closure A)ᶜ ×ˢ (closure A)ᶜ
  have hWo : IsOpen W :=
    ((isOpen_interior.prod isOpen_interior).union (isOpen_thickening.prod isOpen_thickening)).union
      (isClosed_closure.isOpen_compl.prod isClosed_closure.isOpen_compl)
  have hWd : diagonal X ⊆ W := by
    rintro ⟨x, y⟩ hxy
    simp only [mem_diagonal_iff] at hxy
    subst hxy
    by_cases hi : x ∈ interior A
    · exact Or.inl (Or.inl ⟨hi, hi⟩)
    by_cases hf : x ∈ frontier A
    · have := self_subset_thickening (by positivity : 0 < ε / 3) (frontier A) hf
      exact Or.inl (Or.inr ⟨this, this⟩)
    have hc : x ∉ closure A := by
      rw [closure_eq_interior_union_frontier]
      rintro (h | h)
      exacts [hi h, hf h]
    exact Or.inr ⟨hc, hc⟩
  obtain ⟨n, x, ⟨h0, hn, hx⟩, hlen⟩ :=
    hX W (hWo.mem_nhdsSet.2 hWd) a b (ε / 3) (by positivity)
  have hV : ∃ i ≤ n, x i ∈ V := by
    by_contra hcon
    push Not at hcon
    have hint : ∀ i ≤ n, x i ∈ interior A := by
      intro i
      induction i with
      | zero => intro _; rw [h0]; exact ha'
      | succ i ih =>
        intro hi
        have hxi := ih (by omega)
        rcases hx i (by omega) with (⟨_, h⟩ | ⟨h, _⟩) | ⟨h, _⟩
        · exact h
        · exact absurd h (hcon i (by omega))
        · exact absurd (interior_subset_closure hxi) h
    exact hb (interior_subset (hn ▸ hint n le_rfl))
  obtain ⟨i, hin, hiV⟩ := hV
  obtain ⟨c, hcF, hc⟩ := mem_thickening_iff.1 hiV
  refine ⟨c, hcF, ?_⟩
  have h1 : dist (x 0) (x i) ≤ ∑ j ∈ range i, dist (x j) (x (j + 1)) :=
    dist_le_range_sum_dist x i
  have h2 : dist (x i) (x n) ≤ ∑ j ∈ Finset.Ico i n, dist (x j) (x (j + 1)) :=
    dist_le_Ico_sum_dist x hin
  have h3 := Finset.sum_range_add_sum_Ico (fun j => dist (x j) (x (j + 1))) hin
  rw [h0] at h1
  rw [hn] at h2
  have t1 := dist_triangle a (x i) c
  have t2 := dist_triangle c (x i) b
  rw [dist_comm c (x i)] at t2
  linarith

/-- **Proposition 2** (rédaction n° 402, p. 11): in a localizable space, for `a ∈ A` and
`b ∉ A`, `d(a, b)` is the infimum of `d(a, c) + d(c, b)` over the frontier of `A`. -/
theorem Localizable.dist_eq_iInf_frontier (hX : Localizable X) {A : Set X} {a b : X}
    (ha : a ∈ A) (hb : b ∉ A) :
    dist a b = ⨅ c : frontier A, dist a c + dist (c : X) b := by
  obtain ⟨c₀, hc₀, -⟩ := hX.exists_mem_frontier ha hb one_pos
  have : Nonempty (frontier A) := ⟨⟨c₀, hc₀⟩⟩
  refine le_antisymm (le_ciInf fun c => dist_triangle _ _ _) ?_
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨c, hc, hlt⟩ := hX.exists_mem_frontier ha hb hε
  exact lt_of_le_of_lt (ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; positivity⟩ ⟨c, hc⟩) hlt

/-- **Corollary 1** (rédaction n° 402, p. 11): with `F` the frontier of `A`, `a ∈ A`, `b ∉ A`,
`d(a, F) + d(F, b) ≤ d(a, b)`. -/
theorem Localizable.infDist_add_infDist_le (hX : Localizable X) {A : Set X} {a b : X}
    (ha : a ∈ A) (hb : b ∉ A) :
    infDist a (frontier A) + infDist b (frontier A) ≤ dist a b := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨c, hc, hlt⟩ := hX.exists_mem_frontier ha hb hε
  have := infDist_le_dist_of_mem (x := a) hc
  have := infDist_le_dist_of_mem (x := b) hc
  rw [dist_comm b c] at this
  linarith

/-- **Corollary 2** (rédaction n° 402, p. 11): in a localizable space, the frontier of the open
ball of centre `a` and radius `r > 0` is the sphere. -/
theorem Localizable.frontier_ball (hX : Localizable X) (a : X) {r : ℝ} (hr : 0 < r) :
    frontier (ball a r) = sphere a r := by
  refine subset_antisymm frontier_ball_subset_sphere fun b hb => ?_
  rw [mem_sphere] at hb
  have ha : a ∈ ball a r := mem_ball_self hr
  have hb' : b ∉ ball a r := by simp [mem_ball, hb]
  rw [← isClosed_frontier.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨c, hc, hlt⟩ := hX.exists_mem_frontier ha hb' hε
  have hcs : dist c a = r := frontier_ball_subset_sphere hc
  refine ⟨c, hc, ?_⟩
  rw [dist_comm a c, hcs, dist_comm a b, hb] at hlt
  rw [dist_comm]
  linarith

/-- In a localizable space, the closure of the open ball of radius `r > 0` is the closed ball
(a consequence of Corollary 2). -/
theorem Localizable.closure_ball (hX : Localizable X) (a : X) {r : ℝ} (hr : 0 < r) :
    closure (ball a r) = closedBall a r := by
  rw [closure_eq_self_union_frontier, hX.frontier_ball a hr, ball_union_sphere]

/-- **Corollary 3** (rédaction n° 402, p. 11): in a localizable space, if the closed ball of
centre `a` and radius `r > 0` is compact and `d(a, b) ≥ r`, some `c` has `d(a, c) = r` and
`d(c, b) = d(a, b) - r`. -/
theorem Localizable.exists_dist_eq_sub (hX : Localizable X) {a b : X} {r : ℝ} (hr : 0 < r)
    (hK : IsCompact (closedBall a r)) (hab : r ≤ dist a b) :
    ∃ c, dist a c = r ∧ dist c b = dist a b - r := by
  have ha : a ∈ ball a r := mem_ball_self hr
  have hb : b ∉ ball a r := by rw [mem_ball, dist_comm]; linarith
  have hsub : frontier (ball a r) ⊆ closedBall a r :=
    frontier_ball_subset_sphere.trans sphere_subset_closedBall
  have hF : IsCompact (frontier (ball a r)) := hK.of_isClosed_subset isClosed_frontier hsub
  obtain ⟨c₀, hc₀, -⟩ := hX.exists_mem_frontier ha hb one_pos
  obtain ⟨c, hc, hmin⟩ := hF.exists_isMinOn ⟨c₀, hc₀⟩
    (continuous_id.dist continuous_const).continuousOn
  have hca : dist a c = r := by rw [dist_comm]; exact frontier_ball_subset_sphere hc
  refine ⟨c, hca, le_antisymm ?_ ?_⟩
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨y, hy, hlt⟩ := hX.exists_mem_frontier ha hb hε
    have hya : dist a y = r := by rw [dist_comm]; exact frontier_ball_subset_sphere hy
    have := hmin hy
    simp only [mem_ofPred_eq, id] at this
    linarith
  · linarith [dist_triangle a c b]

/-- A space in which every pair `a ∈ s`, `b ∉ s` gives a point of the frontier of `s` is
connected (or empty): the frontier of a clopen set is empty. -/
theorem preconnectedSpace_of_exists_mem_frontier
    (h : ∀ (s : Set X) (a b : X), a ∈ s → b ∉ s → (frontier s).Nonempty) :
    PreconnectedSpace X := by
  refine preconnectedSpace_iff_clopen.2 fun s hs => ?_
  by_contra hne
  push Not at hne
  obtain ⟨a, ha⟩ := hne.1
  obtain ⟨b, hb⟩ := (ne_univ_iff_exists_notMem s).1 hne.2
  obtain ⟨c, hc⟩ := h s a b ha hb
  rw [hs.frontier_eq] at hc
  exact hc

/-- A localizable space is connected (or empty), so the connectedness hypothesis of
Propositions 1 and 2 is automatic for the neighbourhood form of Definition 1. -/
theorem Localizable.preconnectedSpace (hX : Localizable X) : PreconnectedSpace X :=
  preconnectedSpace_of_exists_mem_frontier fun _ _ _ ha hb =>
    let ⟨c, hc, _⟩ := hX.exists_mem_frontier ha hb one_pos
    ⟨c, hc⟩

/-- The `ε`-chain variant of Definition 1 (suggested by the handwritten note facing p. 10):
only the neighbourhoods `{d < ε}` of the diagonal are used. -/
def EpsLocalizable (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ ε > 0, ∀ a b : X, ∀ δ > 0, ∃ n x, IsChain {p : X × X | dist p.1 p.2 < ε} a b n x ∧
    ∑ i ∈ range n, dist (x i) (x (i + 1)) < dist a b + δ

/-- A localizable space is `ε`-localizable. -/
theorem Localizable.epsLocalizable (hX : Localizable X) : EpsLocalizable X :=
  fun _ hε => hX _ (setOf_dist_lt_mem_nhdsSet hε)

end Prop2

/-- `ℚ` is `ε`-localizable: the arithmetic progression from `a` to `b` in `n` steps has length
exactly `d(a, b)` and steps `d(a, b) / n`. -/
theorem epsLocalizable_rat : EpsLocalizable ℚ := by
  intro ε hε a b δ hδ
  obtain ⟨n, hn⟩ := exists_nat_gt (|(b : ℝ) - a| / ε)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hn0' : (n : ℚ) ≠ 0 := by exact_mod_cast hn0.ne'
  have step : ∀ i : ℕ, dist (a + i * ((b - a) / n)) (a + (i + 1 : ℕ) * ((b - a) / n)) =
      |(b : ℝ) - a| / n := by
    intro i
    rw [Rat.dist_eq]
    push_cast
    rw [show (a : ℝ) + i * ((b - a) / n) - (a + (i + 1) * ((b - a) / n)) = -((b - a) / n) by
      ring, abs_neg, abs_div, abs_of_pos hn0]
  refine ⟨n, fun i => a + i * ((b - a) / n), ⟨by simp, by field_simp; ring, ?_⟩, ?_⟩
  · intro i _
    simp only [mem_ofPred_eq]
    rw [step, div_lt_iff₀ hn0]
    rwa [div_lt_iff₀ hε, mul_comm] at hn
  · simp only [step, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hn0.ne', Rat.dist_eq, abs_sub_comm]
    linarith

/-- `ℚ` is not localizable: it is not connected. -/
theorem not_localizable_rat : ¬ Localizable ℚ := fun h => by
  have := h.preconnectedSpace
  have h01 : (0 : ℚ) = 1 :=
    (isPreconnected_univ.subsingleton : (univ : Set ℚ).Subsingleton) trivial trivial
  exact zero_ne_one h01

/-- Proposition 2 fails for the `ε`-chain variant: on `ℚ`, which is `ε`-localizable, some
`a ∈ A`, `b ∉ A` have no point of the frontier of `A` at all (`A` clopen). -/
theorem not_exists_mem_frontier_rat :
    ¬ ∀ (A : Set ℚ) (a b : ℚ), a ∈ A → b ∉ A → (frontier A).Nonempty := fun h => by
  have := preconnectedSpace_of_exists_mem_frontier h
  have h01 : (0 : ℚ) = 1 :=
    (isPreconnected_univ.subsingleton : (univ : Set ℚ).Subsingleton) trivial trivial
  exact zero_ne_one h01

end Bourbaki.Redaction402
