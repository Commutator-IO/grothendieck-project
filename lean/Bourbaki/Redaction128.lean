import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded

/-!
# Bourbaki, rédaction n° 128 (EVT IV, état 4, copy of Laurent Schwartz, March 1950): the « Commentaires »

The « Commentaires » appended to rédaction 128, after the « Compléments sur les théorèmes de
Grothendieck et Banach », isolate two properties of a locally convex space, under names that did
not survive: « bornographique » (every convex set absorbing all bounded sets is a neighbourhood of
`0`) and « fort » (every convex, balanced, closed absorbing set is a neighbourhood of `0`). They are
today's *bornological* and *barrelled* spaces. The page states:

* Prop. A and A′: a metrizable space is bornographique, so a linear map sending bounded sets to
  bounded sets is continuous;
* Prop. B: a Baire locally convex space is « fort ».

Both are in Mathlib, which this file only records against the page: `LinearMap.continuous_of_
locally_bounded` (first-countable domain) for A–A′ together, and the instance
`BaireSpace.instBarrelledSpace` for B (Mathlib defines barrelled through lower semicontinuous
seminorms, equivalent to « barrels are neighbourhoods » in the locally convex case).
-/

namespace Grothendieck.Bourbaki128

/-- Prop. A and A′ of rédaction 128, for a first-countable (e.g. metrizable) domain. -/
theorem propA' {𝕜 𝕜' E F : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [NontriviallyNormedField 𝕜] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
    [NormedField 𝕜'] [Module 𝕜' F] {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ]
    [FirstCountableTopology E] (f : E →ₛₗ[σ] F)
    (hf : ∀ s, Bornology.IsVonNBounded 𝕜 s → Bornology.IsVonNBounded 𝕜' (f '' s)) :
    Continuous f :=
  f.continuous_of_locally_bounded hf

/-- Prop. B of rédaction 128: a Baire space is « fort », i.e. barrelled. -/
theorem propB {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] [BaireSpace E] :
    BarrelledSpace 𝕜 E :=
  inferInstance

end Grothendieck.Bourbaki128
