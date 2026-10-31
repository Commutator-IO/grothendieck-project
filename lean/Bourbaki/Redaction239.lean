import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Order.ProjIcc

/-!
# Bourbaki, rédaction n° 239 (Dieudonné, 1956), p. 86: a soft sheaf which is not fine

Rédaction 239, « Livre VII. Topologie préhomologique. Ch. I. Faisceaux (état 2) », defines soft
(« mou ») sheaves in § 4 n° 3 (p. 78) by local extension of sections from closed sets, and fine
(« fin ») sheaves of modules in § 4 n° 6 (p. 85) by the condition that, over a basis of opens,
for `F` closed and `V` an open neighbourhood of `F`, some endomorphism of the sheaf is the
identity near `F` and zero near the complement of `V`. Proposition 4 (p. 85–86) proves that a
fine sheaf is soft; the rédactor then says (p. 86) that he cannot prove the converse, finds it
doubtful, and has no counterexample either.

The converse is false. On `X = [0, 1]`, the sheaf `𝓕` of continuous maps to the circle
(`U ↦ C(U, 𝕋)`, a sheaf of abelian groups, written multiplicatively) is soft but not fine, as a
sheaf of `ℤ`-modules (equivalently, of modules over the constant sheaf `ℤ`).

* Not fine: an endomorphism `φ` of `𝓕` sends the constant section `-1`, of order 2, to a
  continuous map `X → 𝕋` of square `1`, hence with values in `{±1}`, hence constant since `X` is
  connected; if `φ` is the identity near a point and zero near another, this constant is `-1`
  at the first and `1` at the second. This works over any connected space.
* Soft: a continuous map `f` from an open neighbourhood `U` of a closed `K ⊆ [0, 1]` to `𝕋`
  agrees near `K` with a global one. Cut `[0, 1]` into `M` intervals of length `1/M`, fine
  enough that every interval meeting the `1/M`-thickening of `K` lies in `U` and that `f`
  varies by less than `1` on it. The global map is `f(0) · exp(i L)` with
  `L = ∑ᵢ Δᵢ`: on a good interval, `Δᵢ(t)` is the argument of `f(t)/f(xᵢ)` (`t` clamped to the
  interval), continuous because the ratio stays in the right half-plane; on another interval it
  turns linearly by the argument of `f(xᵢ₊₁)/f(xᵢ)`. The product telescopes, and on every good
  interval the result is `f`. No covering-space theory is used.

The rédaction's question is recorded as open by the congress (Tribu 41). MathOverflow question
423444 (2022) asks for an example of a soft sheaf that is not fine and had no answer when looked
at; the example may well be folklore, or an exercise in Godement (II.3.7) or Bredon (II.9),
which were not checked.

**What is proved.**
* `Opens.res`, `not_exists_endomorphism`: **not fine**, over any preconnected space `X`: no
  family of group endomorphisms `φ_U` of `C(U, 𝕋)`, natural in the open `U`, is the identity on
  an open neighbourhood of a point `p` and trivial on an open neighbourhood of a point `q`.
* `not_fine_unitInterval`: the case of `[0, 1]` with `F = {0}` and `V = [0, 1)`, the instance
  of the rédaction's condition that fails.
* `exists_eqOn_nhds`: **soft**, for every closed `K ⊆ [0, 1]` and every map `f : [0, 1] → 𝕋`
  continuous on an open `U ⊇ K`, a continuous `g : [0, 1] → 𝕋` equals `f` on an open
  neighbourhood of `K`. `exists_eqOn_nhds'`: the same with `f : C(U, 𝕋)`.

**Not formalised.** The sheaf `U ↦ C(U, 𝕋)` is not built as a Mathlib `Sheaf`, and the
rédaction's definitions of soft and fine sheaves (with their bases of paracompact opens and
families `ψ(U)` of closed sets) are not formalised; the two theorems are the concrete content of
the two properties for this sheaf. Proposition 4 itself (fine implies soft) is not formalised.
-/

namespace Bourbaki.Redaction239

open Set Topology Metric Finset

section NotFine

variable {X : Type*} [TopologicalSpace X]

/-- The restriction `C(U, 𝕋) → C(V, 𝕋)` for opens `V ≤ U`. -/
noncomputable def Opens.res {U V : TopologicalSpace.Opens X} (h : V ≤ U) (f : C(U, Circle)) :
    C(V, Circle) :=
  f.comp ⟨Set.inclusion h, continuous_inclusion h⟩

/-- **Not fine** (against rédaction n° 239, p. 86): over a preconnected space, no family of
group endomorphisms of `U ↦ C(U, 𝕋)`, natural for restrictions, is the identity on an open
neighbourhood `U₀` of a point and trivial on an open neighbourhood `U₁` of another. -/
theorem not_exists_endomorphism [PreconnectedSpace X]
    (φ : ∀ U : TopologicalSpace.Opens X, C(U, Circle) →* C(U, Circle))
    (hφ : ∀ (U V : TopologicalSpace.Opens X) (h : V ≤ U) (f : C(U, Circle)),
      φ V (Opens.res h f) = Opens.res h (φ U f))
    {U₀ U₁ : TopologicalSpace.Opens X} {p q : X} (hp : p ∈ U₀) (hq : q ∈ U₁)
    (h₀ : ∀ f, φ U₀ f = f) (h₁ : ∀ f, φ U₁ f = 1) : False := by
  let m : C((⊤ : TopologicalSpace.Opens X), Circle) := ContinuousMap.const _ (-1)
  have hm : m * m = 1 := by ext; simp [m]
  let g : X → Circle := fun x => φ ⊤ m ⟨x, trivial⟩
  have hg : Continuous g := (φ ⊤ m).continuous.comp (continuous_id.subtype_mk _)
  have hsq : ∀ x, g x = 1 ∨ g x = -1 := by
    intro x
    have h := congrArg (fun k : C((⊤ : TopologicalSpace.Opens X), Circle) => (k ⟨x, trivial⟩ : ℂ))
      (show φ ⊤ m * φ ⊤ m = 1 by rw [← map_mul, hm, map_one])
    simp only [ContinuousMap.mul_apply, Circle.coe_mul, ContinuousMap.one_apply,
      Circle.coe_one] at h
    rcases mul_self_eq_one_iff.1 h with h | h
    · exact Or.inl (Circle.ext (by simpa using h))
    · exact Or.inr (Circle.ext (by simpa using h))
  have hp' : g p = -1 := by
    have := congrArg (fun k : C(U₀, Circle) => k ⟨p, hp⟩) (hφ ⊤ U₀ le_top m)
    simp only [h₀] at this
    simpa [Opens.res, m] using this.symm
  have hq' : g q = 1 := by
    have := congrArg (fun k : C(U₁, Circle) => k ⟨q, hq⟩) (hφ ⊤ U₁ le_top m)
    simp only [h₁] at this
    simpa [Opens.res, m] using this.symm
  have hS : IsClopen {x | g x = 1} := by
    refine ⟨isClosed_eq hg continuous_const, ?_⟩
    have : {x | g x = 1} = g ⁻¹' ball 1 1 := by
      ext x
      rcases hsq x with h | h
      · simp [h]
      · simp only [mem_ofPred_eq, h, Set.mem_preimage, mem_ball]
        constructor
        · intro h'; exact absurd h' (Circle.neg_ne_self 1)
        · intro h'
          exfalso
          have h'' : dist ((-1 : Circle) : ℂ) ((1 : Circle) : ℂ) < 1 := h'
          rw [Circle.coe_neg, Circle.coe_one, dist_eq_norm] at h''
          norm_num at h''
    rw [this]
    exact isOpen_ball.preimage hg
  rcases isClopen_iff.1 hS with h | h
  · exact (h ▸ hq' : q ∈ (∅ : Set X))
  · have : p ∈ {x | g x = 1} := h ▸ mem_univ p
    exact Circle.neg_ne_self 1 (hp'.symm.trans this)

/-- **The instance of the rédaction's condition that fails** on `[0, 1]` (rédaction n° 239,
p. 85–86): for `F = {0}` and `V = [0, 1)`, no endomorphism of `U ↦ C(U, 𝕋)` is the identity on
a neighbourhood of `F` and zero on a neighbourhood of the complement `{1}` of `V`. So this soft
sheaf is not fine. -/
theorem not_fine_unitInterval
    (φ : ∀ U : TopologicalSpace.Opens unitInterval, C(U, Circle) →* C(U, Circle))
    (hφ : ∀ (U V : TopologicalSpace.Opens unitInterval) (h : V ≤ U) (f : C(U, Circle)),
      φ V (Opens.res h f) = Opens.res h (φ U f))
    {U₀ U₁ : TopologicalSpace.Opens unitInterval} (h0 : (0 : unitInterval) ∈ U₀)
    (h1 : (1 : unitInterval) ∈ U₁) (h₀ : ∀ f, φ U₀ f = f) (h₁ : ∀ f, φ U₁ f = 1) : False :=
  not_exists_endomorphism φ hφ h0 h1 h₀ h₁

end NotFine

section Soft

open unitInterval

variable (U : Set I) (f : I → Circle) (M : ℕ)

/-- The clamping of `t` to the `i`-th interval `[i/M, (i+1)/M]`, as a real number. -/
noncomputable def clampR (i : ℕ) (t : ℝ) : ℝ := max (i / M) (min ((i + 1) / M) t)

/-- The clamping of `t` to the `i`-th interval, as a point of `[0, 1]`. -/
noncomputable def clamp (i : ℕ) (t : ℝ) : I := Set.projIcc 0 1 zero_le_one (clampR M i t)

/-- The `j`-th grid point `j/M`, as a point of `[0, 1]`. -/
noncomputable def grid (j : ℕ) : I := Set.projIcc 0 1 zero_le_one (j / M)

/-- The `i`-th interval is good: it lies in `U` and `f` varies there by less than `1`. -/
def Good (i : ℕ) : Prop :=
  ∀ t : ℝ, clamp M i t ∈ U ∧ ‖((f (clamp M i t) / f (grid M i) : Circle) : ℂ) - 1‖ < 1

open Classical in
/-- The increment of the argument on the `i`-th interval. -/
noncomputable def incr (i : ℕ) (t : ℝ) : ℝ :=
  if Good U f M i then Complex.arg ((f (clamp M i t) / f (grid M i) : Circle) : ℂ)
  else (M * (clampR M i t - i / M)) * Complex.arg ((f (grid M (i + 1)) / f (grid M i) : Circle) : ℂ)

/-- The clamping is continuous. -/
theorem continuous_clampR (i : ℕ) : Continuous (clampR M i) := by
  unfold clampR; fun_prop

/-- The clamping into `[0, 1]` is continuous. -/
theorem continuous_clamp (i : ℕ) : Continuous (clamp M i) :=
  continuous_projIcc.comp (continuous_clampR M i)

/-- Each increment is continuous: on a good interval, the ratio stays in the slit plane where
the argument is continuous. -/
theorem continuous_incr (hf : ContinuousOn f U) (i : ℕ) : Continuous (incr U f M i) := by
  unfold incr
  split_ifs with hg
  · have hc : Continuous fun t => f (clamp M i t) :=
      hf.comp_continuous (continuous_clamp M i) fun t => (hg t).1
    have hc' : Continuous fun t => ((f (clamp M i t) / f (grid M i) : Circle) : ℂ) :=
      continuous_subtype_val.comp (hc.div_const _)
    refine continuous_iff_continuousAt.2 fun t => ?_
    refine (Complex.continuousAt_arg ?_).comp hc'.continuousAt
    have := Complex.mem_slitPlane_of_norm_lt_one (hg t).2
    rwa [add_sub_cancel] at this
  · exact ((continuous_const.mul ((continuous_clampR M i).sub continuous_const)).mul
      continuous_const)

/-- Past the `i`-th interval, the clamping is its right end. -/
theorem clampR_of_le {i : ℕ} {t : ℝ} (ht : (i + 1 : ℝ) / M ≤ t) :
    clampR M i t = (i + 1 : ℝ) / M := by
  unfold clampR
  rw [min_eq_left ht, max_eq_right]
  gcongr; linarith

/-- Before the `i`-th interval, the clamping is its left end. -/
theorem clampR_of_ge {i : ℕ} {t : ℝ} (ht : t ≤ (i : ℝ) / M) :
    clampR M i t = (i : ℝ) / M := by
  unfold clampR
  apply max_eq_left
  exact (min_le_right _ _).trans ht

/-- Past the `i`-th interval, the increment exponentiates to `f(xᵢ₊₁) / f(xᵢ)`. -/
theorem exp_incr_of_le (hM : 0 < M) {i : ℕ} {t : ℝ} (ht : (i + 1 : ℝ) / M ≤ t) :
    Circle.exp (incr U f M i t) = f (grid M (i + 1)) / f (grid M i) := by
  have hc : clamp M i t = grid M (i + 1) := by
    simp only [clamp, grid, clampR_of_le M ht]; push_cast; rfl
  unfold incr
  split_ifs
  · rw [hc, Circle.exp_arg]
  · rw [clampR_of_le M ht]
    have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [show (M : ℝ) * ((i + 1) / M - i / M) = 1 by field_simp; ring, one_mul, Circle.exp_arg]

/-- Before the `i`-th interval, the increment exponentiates to `1`. -/
theorem exp_incr_of_ge {i : ℕ} {t : ℝ} (ht : t ≤ (i : ℝ) / M) :
    Circle.exp (incr U f M i t) = 1 := by
  have hc : clamp M i t = grid M i := by simp only [clamp, grid, clampR_of_ge M ht]
  unfold incr
  split_ifs
  · rw [hc, div_self', Circle.coe_one, Complex.arg_one, Circle.exp_zero]
  · rw [clampR_of_ge M ht, sub_self, mul_zero, zero_mul, Circle.exp_zero]

/-- On a good interval, the increment exponentiates to `f(t) / f(xᵢ)`, `t` clamped. -/
theorem exp_incr_self {i : ℕ} (hi : Good U f M i) (t : ℝ) :
    Circle.exp (incr U f M i t) = f (clamp M i t) / f (grid M i) := by
  unfold incr
  rw [ite_eq_left hi, Circle.exp_arg]

/-- The telescoping identity: on the good interval `k`, the partial sums of the increments
exponentiate to `f(grid n) / f(0)` before `k` and to `f(t) / f(0)` from `k` on. -/
theorem exp_sum_incr (hM : 0 < M) {k : ℕ} (hk : Good U f M k) {t : ℝ}
    (ht₁ : (k : ℝ) / M ≤ t) (ht₂ : t ≤ (k + 1 : ℝ) / M) (n : ℕ) :
    Circle.exp (∑ i ∈ range n, incr U f M i t) =
      if n ≤ k then f (grid M n) / f (grid M 0) else f (clamp M k t) / f (grid M 0) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Circle.exp_add, ih]
    rcases lt_trichotomy n k with h | rfl | h
    · rw [ite_eq_left h.le, ite_eq_left (show n + 1 ≤ k by omega), exp_incr_of_le U f M hM]
      · rw [mul_comm, div_mul_div_cancel]
      · refine le_trans ?_ ht₁
        gcongr
        exact_mod_cast h
    · rw [ite_eq_left le_rfl, ite_eq_right (by omega), exp_incr_self U f M hk, mul_comm,
        div_mul_div_cancel]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), exp_incr_of_ge U f M, mul_one]
      refine ht₂.trans ?_
      gcongr
      exact_mod_cast h

/-- The global map `f(0) · exp(i ∑ Δᵢ)`. -/
noncomputable def globalMap (hf : ContinuousOn f U) : C(I, Circle) where
  toFun y := f (grid M 0) * Circle.exp (∑ i ∈ range M, incr U f M i y)
  continuous_toFun := continuous_const.mul (Circle.exp.continuous.comp
    (continuous_finsetSum _ fun i _ => (continuous_incr U f M hf i).comp continuous_subtype_val))

/-- For `k < M`, the clamping to the `k`-th interval stays in `[0, 1]`. -/
theorem coe_clamp {k : ℕ} (hk : k < M) (t : ℝ) : (clamp M k t : ℝ) = clampR M k t := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have h1 : (0 : ℝ) ≤ k / M := by positivity
  have h2 : (k + 1 : ℝ) / M ≤ 1 := by
    rw [div_le_one hM]; exact_mod_cast hk
  have : clampR M k t ∈ Icc (0 : ℝ) 1 := by
    unfold clampR
    constructor
    · exact h1.trans (le_max_left _ _)
    · refine max_le ?_ ((min_le_left _ _).trans h2)
      exact le_trans (by gcongr; linarith) h2
  simp only [clamp, Set.projIcc_of_mem _ this]

/-- The clamping lies in the `k`-th interval. -/
theorem clampR_mem {k : ℕ} (hM : 0 < M) (t : ℝ) :
    (k : ℝ) / M ≤ clampR M k t ∧ clampR M k t ≤ (k + 1 : ℝ) / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  unfold clampR
  refine ⟨le_max_left _ _, max_le (by gcongr; linarith) (min_le_left _ _)⟩

/-- Every point of `[0, 1]` lies in one of the `M` intervals. -/
theorem exists_interval (hM : 0 < M) (y : I) :
    ∃ k < M, (k : ℝ) / M ≤ y ∧ (y : ℝ) ≤ (k + 1 : ℝ) / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rcases lt_or_eq_of_le y.2.2 with hy | hy
  · refine ⟨⌊(M : ℝ) * y⌋₊, ?_, ?_, ?_⟩
    · rw [Nat.floor_lt (by have := y.2.1; positivity)]
      calc (M : ℝ) * y < M * 1 := by gcongr
        _ = M := mul_one _
    · rw [div_le_iff₀ hM', mul_comm]
      exact Nat.floor_le (by have := y.2.1; positivity)
    · rw [le_div_iff₀ hM', mul_comm]
      exact (Nat.lt_floor_add_one _).le
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
    refine ⟨m, Nat.lt_succ_self m, ?_, ?_⟩
    · rw [hy, div_le_one hM']; push_cast; linarith
    · rw [hy]; push_cast; rw [div_self (by positivity)]

/-- **Soft** (against rédaction n° 239, p. 86): for `K ⊆ [0, 1]` closed and `f : [0, 1] → 𝕋`
continuous on an open `U ⊇ K`, some continuous `g : [0, 1] → 𝕋` equals `f` on an open
neighbourhood of `K`. -/
theorem exists_eqOn_nhds {K : Set I} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContinuousOn f U) : ∃ g : C(I, Circle), ∃ V, IsOpen V ∧ K ⊆ V ∧ EqOn g f V := by
  obtain ⟨δ, hδ, hδU⟩ := hK.isCompact.exists_cthickening_subset_open hU hKU
  have hC : IsCompact (cthickening δ K) := isClosed_cthickening.isCompact
  obtain ⟨η, hη, hfη⟩ := Metric.uniformContinuousOn_iff.1
    (hC.uniformContinuousOn_of_continuous (hf.mono hδU)) 1 one_pos
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / min (δ / 2) (η / 2))
  have hmin : 0 < min (δ / 2) (η / 2) := lt_min (by positivity) (by positivity)
  have hM0 : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hM0' : 0 < M := by exact_mod_cast hM0
  have hMinv : 1 / (M : ℝ) < min (δ / 2) (η / 2) := by
    rw [div_lt_iff₀ hM0, mul_comm, ← div_lt_iff₀ hmin]; exact hM
  have hMδ : 1 / (M : ℝ) < δ / 2 := hMinv.trans_le (min_le_left _ _)
  have hMη : 1 / (M : ℝ) < η / 2 := hMinv.trans_le (min_le_right _ _)
  refine ⟨globalMap U f M hf, thickening (1 / M) K, isOpen_thickening,
    self_subset_thickening (by positivity) K, fun y hy => ?_⟩
  obtain ⟨w, hwK, hyw⟩ := mem_thickening_iff.1 hy
  obtain ⟨k, hk, hk₁, hk₂⟩ := exists_interval M hM0' y
  -- every point of the `k`-th interval lies within `1/M` of `y`
  have hnear : ∀ t : ℝ, dist (clamp M k t) y ≤ 1 / M := by
    intro t
    rw [Subtype.dist_eq, coe_clamp M hk, Real.dist_eq, abs_le]
    obtain ⟨c₁, c₂⟩ := clampR_mem M hM0' (k := k) t
    have : (k + 1 : ℝ) / M - k / M = 1 / M := by field_simp; ring
    constructor <;> linarith
  have hgrid : grid M k = clamp M k (k / M) := by
    simp only [grid, clamp, clampR_of_ge M le_rfl]
  have hinC : ∀ t : ℝ, clamp M k t ∈ cthickening δ K := by
    intro t
    refine thickening_subset_cthickening δ K (mem_thickening_iff.2 ⟨w, hwK, ?_⟩)
    linarith [dist_triangle (clamp M k t) y w, hnear t]
  have hgood : Good U f M k := by
    intro t
    refine ⟨hδU (hinC t), ?_⟩
    have hd : dist (clamp M k t) (grid M k) < η := by
      rw [hgrid]
      have := dist_triangle (clamp M k t) y (clamp M k (k / M))
      rw [dist_comm y] at this
      linarith [hnear t, hnear (k / M)]
    have h : ‖(f (clamp M k t) : ℂ) - f (grid M k)‖ < 1 := by
      rw [← dist_eq_norm]; exact hfη _ (hinC t) _ (hgrid ▸ hinC (k / M)) hd
    rw [Circle.coe_div, div_sub_one (Circle.coe_ne_zero _), norm_div, Circle.norm_coe, div_one]
    exact h
  have hy' : clamp M k y = y := by
    apply Subtype.ext
    rw [coe_clamp M hk]
    unfold clampR
    rw [min_eq_right hk₂, max_eq_right hk₁]
  show f (grid M 0) * Circle.exp (∑ i ∈ range M, incr U f M i y) = f y
  rw [exp_sum_incr U f M hM0' hgood hk₁ hk₂, ite_eq_right (by omega), hy', mul_div_cancel]

/-- **Soft**, with sections over opens: for `K ⊆ [0, 1]` closed, `U` an open neighbourhood of
`K` and `f ∈ C(U, 𝕋)`, some `g ∈ C([0, 1], 𝕋)` agrees with `f` on an open `V` with
`K ⊆ V ⊆ U`. -/
theorem exists_eqOn_nhds' {K : Set I} (hK : IsClosed K) {U : TopologicalSpace.Opens I}
    (hKU : K ⊆ U) (f : C(U, Circle)) :
    ∃ g : C(I, Circle), ∃ V, IsOpen V ∧ K ⊆ V ∧ ∃ hV : V ⊆ U, ∀ x (hx : x ∈ V),
      g x = f ⟨x, hV hx⟩ := by
  classical
  let F : I → Circle := fun x => if h : x ∈ U then f ⟨x, h⟩ else 1
  have hF : ContinuousOn F U := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert f.continuous using 1
    ext x
    simp [F]
  obtain ⟨g, V, hV, hKV, hgV⟩ := exists_eqOn_nhds (U : Set I) F hK U.isOpen hKU hF
  refine ⟨g, V ∩ U, hV.inter U.isOpen, subset_inter hKV hKU, inter_subset_right,
    fun x hx => ?_⟩
  rw [hgV hx.1]
  exact dite_eq_left (hx.2 : x ∈ U)

end Soft

end Bourbaki.Redaction239
