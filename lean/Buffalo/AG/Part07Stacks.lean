import Buffalo.AG.Part07a
import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct

/-!
# Buffalo, algebraic geometry, part 07 (a): products of separable and of connected `k`-schemes

`Part07a.lean` proves the product statements `19493`, `19954`, `20993` and `21315` for
universally open `k`-schemes only, and lacks the separable half of `19493`. Both gaps close:

* every `k`-scheme is universally open over `Spec k` (Stacks tag 0383): Mathlib's instance
  `UniversallyOpen` for morphisms to the spectrum of a field already gives it at `715a03a`, so the
  hypothesis is dropped below;
* the product over `k` of two geometrically reduced (separable) `k`-schemes is geometrically
  reduced: `geometricallyReduced_pullback_over_field` (Stacks tag 035Z) of the vendored
  AxiomMath/Stacks file `StacksFrontier/AlgebraicGeometry/Variety/Geometrically/ReducedProduct.lean`
  (Apache-2.0, see `lean/Stacks/NOTICE.md`).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Buffalo.AG.Part07

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))

/-- Every `k`-scheme is universally open over `k` (Stacks tag 0383; a Mathlib instance). -/
theorem universallyOpen_over_field : UniversallyOpen f := inferInstance

/-- Oqhr-Gt66es-19493 (5:24:53) [prop] The product over `k` of two separable (geometrically
reduced) `k`-schemes is separable, and the product of two geometrically irreducible `k`-schemes is
geometrically irreducible (Stacks tag 035Z for the first). -/
theorem prop_19493_full :
    (∀ [GeometricallyReduced f] [GeometricallyReduced g],
      GeometricallyReduced (pullback.snd f g ≫ g)) ∧
    (∀ [GeometricallyIrreducible f] [GeometricallyIrreducible g],
      GeometricallyIrreducible (pullback.snd f g ≫ g)) := by
  refine ⟨fun {_ _} => ?_, fun {_ _} => prop_19493 f g⟩
  rw [← pullback.condition]
  exact geometricallyReduced_pullback_over_field f g

/-- Oqhr-Gt66es-19954 (5:32:34) [prop] (part) The product over `k` of a geometrically connected
`k`-scheme and a connected one is connected (no openness hypothesis). -/
theorem prop_19954_general [GeometricallyConnected f] [ConnectedSpace Y] :
    ConnectedSpace ↥(pullback f g) :=
  prop_19954 f g

/-- Oqhr-Gt66es-21315 (5:55:15) [prop] Geometric connectedness is stable under the product of two
`k`-schemes and under extension of the base field (no openness hypothesis). -/
theorem prop_21315_general [GeometricallyConnected f] [GeometricallyConnected g] (K : Type u)
    [Field K] [Algebra k K] :
    GeometricallyConnected (pullback.snd f g ≫ g) ∧ GeometricallyConnected (baseChange f K) :=
  prop_21315 f g K

/-- Oqhr-Gt66es-20993 (5:49:53) [prop] (part) Geometric connectedness is the connectedness of
`X_{k'}` for every extension `k'/k`, and implies that `X ×_k Y` is connected for every connected
`Y` (no openness hypothesis). -/
theorem prop_20993_general :
    (GeometricallyConnected f ↔ ∀ (K : Type u) [Field K] [Algebra k K],
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) ∧
    (∀ [GeometricallyConnected f] [ConnectedSpace Y], ConnectedSpace ↥(pullback f g)) :=
  ⟨(prop_20993 f g).1, fun {_ _} => prop_19954 f g⟩

end Buffalo.AG.Part07
