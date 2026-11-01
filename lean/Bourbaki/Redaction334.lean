import Bourbaki.Upstream.FrobeniusRangePow

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
  values in `Kᵖ` has derivative `0` wherever it is differentiable (step (i));
* `mem_fieldRange_frobenius`: `Kᵖ` as the subfield `(frobenius K p).fieldRange`;
* `tendsto_remainder_div`: Taylor's formula along `y = cᵖ w`, the remainder of order `m`
  divided by `(cᵖ)ᵐ` tends to `wᵐ aₘ`;
* `coeff_mem_range_pow`: if `Kᵖ` is closed, `π ∉ Kᵖ` and a power series `Σ aₙ yⁿ` takes values
  in `Kᵖ` near its centre, then every `aₙ` is in `Kᵖ` and `aₙ = 0` unless `p ∣ n`;
* `analyticAt_of_analyticAt_pow`: if `K` is complete, `Kᵖ ≠ K` and `t ↦ h(t)ᵖ` is analytic at
  `x`, then `h` is analytic at `x` (step (ii)).

Step (ii) is proved in one variable, `T ⊆ K`; the case `T ⊆ Kᵐ` of strong effectivity is not
done here. The proof uses neither a `Kᵖ`-basis of `K` nor `[K : Kᵖ] < ∞`, nor step (i): only
that `Kᵖ` is a closed subfield and that `π ∉ Kᵖ`, by induction on the coefficients.

The facts on Frobenius are general and live in `Bourbaki/Upstream/FrobeniusRangePow.lean`
(namespace `CharP`, with `mem_fieldRange_frobenius_iff` for `mem_fieldRange_frobenius`, and
`HasFPowerSeriesAt.tendsto_sub_partialSum_div_pow` for `tendsto_remainder_div`); the names below
are aliases kept for the articles that cite them. The action itself stays here.
-/

open Filter Topology NNReal ENNReal

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
alias sub_mem_range_pow := CharP.sub_mem_range_pow

/-- In a complete normed field of characteristic `p`, the subfield `Kᵖ` is closed. -/
alias isClosed_range_pow := CharP.isClosed_range_pow

/-- If `Kᵖ ≠ K`, then `Kᵖ` has empty interior. -/
alias interior_range_pow_eq_empty := CharP.interior_range_pow_eq_empty

/-- If `Kᵖ` is closed and `π ∉ Kᵖ`, a `Kᵖ`-valued function has zero derivative wherever it is
differentiable: the difference quotients along `cᵖ` lie in `Kᵖ`, those along `π cᵖ` in
`π⁻¹ Kᵖ`, and these two closed sets meet only in `0`. -/
alias hasDerivAt_eq_zero_of_mem_range_pow := CharP.hasDerivAt_eq_zero_of_mem_range_pow

/-- The subfield `Kᵖ`, as the field range of Frobenius. -/
alias mem_fieldRange_frobenius := CharP.mem_fieldRange_frobenius_iff

/-- Taylor's formula along `y = cᵖ w`: if `g` has the power series `P = Σ aₙ yⁿ` at `x`, then
`(g (x + cᵖ w) - Σ_{k<m} a_k (cᵖ w)ᵏ) / (cᵖ)ᵐ` tends to `wᵐ aₘ` as `c → 0`. -/
alias tendsto_remainder_div := HasFPowerSeriesAt.tendsto_sub_partialSum_div_pow

/-- **Step (ii), on coefficients.** Let `Kᵖ` be closed and `π ∉ Kᵖ`. If `g` has the power series
`Σ aₙ yⁿ` at `x` and takes values in `Kᵖ` near `x`, then every `aₙ` lies in `Kᵖ`, and `aₙ = 0`
unless `p ∣ n`. By induction on `m`: the remainder of order `m`, evaluated at `cᵖ w` and divided
by `(cᵖ)ᵐ`, lies in `Kᵖ` and tends to `wᵐ aₘ`; take `w = 1`, then `w = π`. -/
alias coeff_mem_range_pow := CharP.coeff_mem_range_pow

/-- **Step (ii).** Let `K` be complete of characteristic `p` with `Kᵖ ≠ K`. If `t ↦ h(t)ᵖ` is
analytic at `x`, then `h` is analytic at `x`: writing `h(x + y)ᵖ = Σ a_{pn} y^{pn}` with
`a_{pn} = b_nᵖ`, the series `Σ b_n yⁿ` has positive radius, and its `p`-th power is
`Σ b_nᵖ y^{pn}` because Frobenius is additive and continuous. One variable only. -/
alias analyticAt_of_analyticAt_pow := CharP.analyticAt_of_analyticAt_pow

end Bourbaki.Redaction334
