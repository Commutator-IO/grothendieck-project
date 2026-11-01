import Mathlib

/-!
# Bourbaki, rédaction n° 384 (June 1962): the covolume is not continuous

Rédaction 384 of the Bourbaki archive (Archives Henri Poincaré, item 940) is Bruhat's draft of
*Intégration*, ch. VIII, § 5, on the space of closed subgroups of a locally compact group. Exercise 4
shows that the covolume of a cocompact subgroup is not continuous for the topology of closed
subsets. In the discrete group `G = ⊕_n ℤ/2`, the subgroups `H_n = ker p_n`, kernels of the
coordinate projections, have index `2`, hence covolume `2` for the counting measures; and they
converge to `G` itself, of covolume `1`.

For a discrete group, the topology of closed subsets is that of pointwise convergence of
indicator functions, so the convergence `H_n → G` says: every `x ∈ G` lies in `H_n` for all large
`n`. Compactness of `G/H_n` is automatic (it is finite).

* `index_ker`: each `H_n` has index `2`;
* `eventually_mem_ker`: every `x ∈ G` lies in `H_n` for all large `n`;
* `tendsto_indicator`: the indicator functions of the `H_n` converge pointwise to that of `G`.

The general theory of the space of closed subgroups (the Chabauty topology) is not in mathlib and is
not formalised here.
-/

open Filter

namespace Bourbaki.Redaction384

/-- The group `⊕_n ℤ/2`, as finitely supported sequences. -/
abbrev G := ℕ →₀ ZMod 2

/-- The subgroup `H_n`, kernel of the `n`-th coordinate projection. -/
noncomputable def H (n : ℕ) : AddSubgroup G := (Finsupp.applyAddHom n : G →+ ZMod 2).ker

theorem mem_H {n : ℕ} {x : G} : x ∈ H n ↔ x n = 0 := Iff.rfl

/-- Each `H_n` has index `2` in `G`. -/
theorem index_ker (n : ℕ) : (H n).index = 2 := by
  have hs : Function.Surjective (Finsupp.applyAddHom n : G →+ ZMod 2) :=
    fun c => ⟨Finsupp.single n c, by simp⟩
  rw [H, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hs, AddSubgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card]

/-- Every `x ∈ G` lies in `H_n` for all large `n`: `H_n → G` in the space of subgroups. -/
theorem eventually_mem_ker (x : G) : ∀ᶠ n in atTop, x ∈ H n := by
  obtain ⟨N, hN⟩ := x.support.bddAbove
  refine eventually_atTop.2 ⟨N + 1, fun n hn => ?_⟩
  rw [mem_H, ← Finsupp.notMem_support_iff]
  intro h
  have := hN h
  omega

/-- The indicator functions of the `H_n` converge pointwise to the constant `1`. -/
theorem tendsto_indicator (x : G) :
    Tendsto (fun n => (H n : Set G).indicator (fun _ => (1 : ℕ)) x) atTop (pure 1) := by
  refine tendsto_pure.2 ((eventually_mem_ker x).mono fun n hn => ?_)
  exact Set.indicator_of_mem (SetLike.mem_coe.2 hn) _

end Bourbaki.Redaction384
