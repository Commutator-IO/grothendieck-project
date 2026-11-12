import Mathlib

/-!
# Quillen, notebook 1973-6, p. 61: the index of a subgroup as a sum over double cosets

Daniel Quillen's research notebook 1973-6 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201973/1973-6.pdf>), p. 61:
for `Γ' ≤ Γ` of finite index and a finite subgroup `Γ_P`, the index `[Γ : Γ']` is the sum,
over the double cosets `Γ_P γ Γ'`, of `|Γ_P| / |Γ_P ∩ γΓ'γ⁻¹|` (the page's `Σ e_Q / e_{Q_i}`).

Here `H` plays `Γ_P` and `K` plays `Γ'`; `H` acts on the left cosets `G ⧸ K`:

* `stabilizer_eq`: the stabiliser in `H` of the coset `gK` is `H ∩ gKg⁻¹`;
* `index_eq_sum`: **the statement**, `[G : K] = Σ_ω |H| / |H ∩ g_ω K g_ω⁻¹|`, the sum over
  the `H`-orbits `ω` on `G ⧸ K` (the double cosets `H g K`), `g_ω` a representative;
* `index_eq_sum_index`: the same with each term written as the index `[H : H ∩ g_ω K g_ω⁻¹]`
  (no finiteness of `H` needed).

The orbit–stabiliser count is mathlib's `MulAction.card_eq_sum_card_group_div_card_stabilizer`.
-/

namespace Quillen.Notebook1973_6Doset

open MulAction

variable {G : Type*} [Group G] (H K : Subgroup G)

/-- The conjugate `gKg⁻¹`. -/
abbrev conj (g : G) : Subgroup G := K.map (MulAut.conj g).toMonoidHom

theorem mem_conj (g x : G) : x ∈ conj K g ↔ g⁻¹ * x * g ∈ K := by
  rw [conj, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

/-- The stabiliser in `H` of the coset `gK` is `H ∩ gKg⁻¹`, as a subgroup of `H`. -/
theorem stabilizer_eq (g : G) :
    stabilizer H ((g : G ⧸ K)) = (conj K g).subgroupOf H := by
  ext ⟨h, hh⟩
  rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_conj]
  change ((h * g : G) : G ⧸ K) = g ↔ _
  rw [QuotientGroup.eq]
  constructor
  · intro hk
    have := K.inv_mem hk
    simpa [mul_assoc] using this
  · intro hk
    have := K.inv_mem hk
    simpa [mul_assoc] using this

/-- A representative in `G` of an `H`-orbit on `G ⧸ K`. -/
noncomputable def rep (ω : orbitRel.Quotient H (G ⧸ K)) : G := Quotient.out (Quotient.out ω)

/-- **Notebook 1973-6, p. 61**: `[G : K] = Σ_ω |H| / |H ∩ g_ω K g_ω⁻¹|`. -/
theorem index_eq_sum [Finite H] [K.FiniteIndex] :
    K.index = ∑ᶠ ω : orbitRel.Quotient H (G ⧸ K),
      Nat.card H / Nat.card ((conj K (rep H K ω)).subgroupOf H) := by
  classical
  have : Finite (G ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  let _ : Fintype (G ⧸ K) := Fintype.ofFinite _
  let _ : Fintype H := Fintype.ofFinite _
  let _ : Fintype (orbitRel.Quotient H (G ⧸ K)) := Fintype.ofFinite _
  let _ : ∀ b : G ⧸ K, Fintype (stabilizer H b) := fun _ => Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, Subgroup.index, Nat.card_eq_fintype_card,
    card_eq_sum_card_group_div_card_stabilizer H (G ⧸ K)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card (α := stabilizer H _)]
  congr 2
  rw [show ω.out = ((rep H K ω : G) : G ⧸ K) from (QuotientGroup.out_eq' ω.out).symm,
    stabilizer_eq]

/-- The same, each term an index: `[G : K] = Σ_ω [H : H ∩ g_ω K g_ω⁻¹]`. -/
theorem index_eq_sum_index [K.FiniteIndex] :
    K.index = ∑ᶠ ω : orbitRel.Quotient H (G ⧸ K), ((conj K (rep H K ω)).subgroupOf H).index := by
  classical
  have : Finite (G ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  let _ : Fintype (orbitRel.Quotient H (G ⧸ K)) := Fintype.ofFinite _
  rw [Subgroup.index, Nat.card_congr (selfEquivSigmaOrbits H (G ⧸ K)), Nat.card_sigma,
    finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Nat.card_coe_set_eq, ← index_stabilizer,
    show ω.out = ((rep H K ω : G) : G ⧸ K) from (QuotientGroup.out_eq' ω.out).symm,
    stabilizer_eq]

end Quillen.Notebook1973_6Doset
