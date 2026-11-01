import Bourbaki.Upstream.AeNormSqLeOfInner

/-!
# Bourbaki, rédaction n° 551 (Cartier, 1970), Annexe 2, Th. 6: from the square to the diagonal

Théorème 6 of Annexe 2 « Noyaux de type positif » (p. 42) concerns a decomposable covariance
`C(t, t') = ∑ₙ fₙ(t) fₙ(t')` on a measured space `(T, m)`, that is `C(t, t') = ⟪f t, f t'⟫` for
`f = (fₙ)ₙ` with values in a separable Hilbert space. It states that an almost-everywhere bound
`|C| ≤ M` on `T × T` implies the bound `C(t, t) ≤ M` for almost every `t ∈ T`, although the
diagonal of `T × T` may be null; the proof of pp. 43–44 goes through the bound on the quadratic
form `C[u, u] ≤ M ‖u‖₁²` and the integral `∫ u f dm`.

This file proves the implication (b) ⇒ (c) directly, by a covering argument. If the set where
`‖f t‖² ≥ M + η` were not null, one of its countably many pieces `f⁻¹(B(d, δ))`, with `d` in a dense
sequence of the Hilbert space and `4 δ² ≤ η`, would have positive (outer) measure `a`. On that piece
`⟪f t, f t'⟫ ≥ M + η / 2 > M` for all pairs, so a square of product measure `a² > 0` would lie in
the null set where the bound fails. Only the one-sided bound `⟪f t, f t'⟫ ≤ M` is used, and no
measurability of `f` is needed: the product measure of a rectangle is the product of the outer
measures (`MeasureTheory.Measure.prod_prod`) as soon as `m` is s-finite.

* `measure_eq_zero_of_lt_inner`: a set on which every pair satisfies `M < ⟪f t, f t'⟫` is null;
* `inner_gt_of_close`: if `‖u‖², ‖v‖² ≥ M + η` and `u, v` lie in a ball of radius `δ` with
  `4 δ² ≤ η`, then `M < ⟪u, v⟫`;
* `ae_norm_sq_le`: Th. 6 (b) ⇒ (c), for `m` s-finite and a separable real inner product space;
* `ae_norm_sq_le_of_abs`: the same with the hypothesis `|⟪f t, f t'⟫| ≤ M` of the page.

The proofs are general and live in `Bourbaki/Upstream/AeNormSqLeOfInner.lean`
(`MeasureTheory.measure_eq_zero_of_forall_lt_inner`, `lt_real_inner_of_dist_lt`,
`MeasureTheory.ae_norm_sq_le_of_ae_inner_le`, `MeasureTheory.ae_norm_sq_le_of_ae_abs_inner_le`);
the names below are aliases kept for the articles that cite them.
-/

open MeasureTheory TopologicalSpace

namespace Bourbaki.Redaction551Th6

/-- A set on which every pair satisfies `M < ⟪f t, f t'⟫` is null, when the bound
`⟪f t, f t'⟫ ≤ M` holds almost everywhere on `T × T`. No measurability is required. -/
alias measure_eq_zero_of_lt_inner := MeasureTheory.measure_eq_zero_of_forall_lt_inner

/-- Two vectors of squared norm at least `M + η` in a common ball of radius `δ`, with
`4 δ² ≤ η`, have inner product greater than `M`. -/
alias inner_gt_of_close := lt_real_inner_of_dist_lt

/-- **Th. 6 (b) ⇒ (c).** For `m` s-finite and `f` with values in a separable real inner product
space, an almost-everywhere bound `⟪f t, f t'⟫ ≤ M` on `T × T` gives `‖f t‖² ≤ M` for almost
every `t`. -/
alias ae_norm_sq_le := MeasureTheory.ae_norm_sq_le_of_ae_inner_le

/-- Th. 6 (b) ⇒ (c) with the hypothesis of the page, `|C(t, t')| ≤ M` almost everywhere. -/
alias ae_norm_sq_le_of_abs := MeasureTheory.ae_norm_sq_le_of_ae_abs_inner_le

end Bourbaki.Redaction551Th6
