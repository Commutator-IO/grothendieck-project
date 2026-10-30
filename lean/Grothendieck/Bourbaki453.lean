import Mathlib.Order.Preorder.Chain

/-!
# Bourbaki, rédaction n° 453 (September 1965): universes under Grothendieck's axiom form a chain

Rédaction 453 (Archives Bourbaki, Fonds Cartier) reports a result of a student of Samuel: in
Bourbaki's set theory, with Hilbert's `τ`, Grothendieck's axiom on universes

  (AG) if `P` is a relation and `U` a universe with `∃ x ∈ U, P x`, then `τₓ P ∈ U`

implies that every set is « artinien » (well founded). Its first step is that the universes are
totally ordered by inclusion: if `U ⊄ U'` and `U' ⊄ U`, apply (AG) to `x ∉ U ∩ U'` in `U` and in
`U'`; then `τₓ(x ∉ U ∩ U')` lies in `U ∩ U'`, against the defining property of `τ`.

Here `τ` is Lean's Hilbert choice `Classical.epsilon`, which satisfies `P (ε P)` whenever some `x`
satisfies `P`, and a « universe » is any member of a family of sets satisfying (AG). Only the first
step is formalised; the second (an artinian universe containing a set of cardinal `2^c`, from
rédaction 424) needs the cardinal arithmetic of universes and is not.
-/

namespace Grothendieck.Bourbaki453

variable {α : Type*} [Nonempty α]

/-- Grothendieck's axiom (AG) for a family `𝒰` of « universes », with `τ = Classical.epsilon`. -/
def AxiomAG (𝒰 : Set (Set α)) : Prop :=
  ∀ U ∈ 𝒰, ∀ P : α → Prop, (∃ x ∈ U, P x) → Classical.epsilon P ∈ U

/-- Step a) of rédaction 453: under (AG), inclusion is a total order on the universes. -/
theorem isChain_of_axiomAG {𝒰 : Set (Set α)} (h : AxiomAG 𝒰) : IsChain (· ⊆ ·) 𝒰 := by
  intro U hU V hV _
  by_contra hne
  push Not at hne
  obtain ⟨hUV, hVU⟩ := hne
  obtain ⟨x, hxU, hxV⟩ := Set.not_subset.1 hUV
  obtain ⟨y, hyV, hyU⟩ := Set.not_subset.1 hVU
  let P : α → Prop := fun z => z ∉ U ∩ V
  have hP : ∃ z, P z := ⟨x, fun h => hxV h.2⟩
  have h1 : Classical.epsilon P ∈ U := h U hU P ⟨x, hxU, fun h => hxV h.2⟩
  have h2 : Classical.epsilon P ∈ V := h V hV P ⟨y, hyV, fun h => hyU h.1⟩
  exact Classical.epsilon_spec hP ⟨h1, h2⟩

end Grothendieck.Bourbaki453
