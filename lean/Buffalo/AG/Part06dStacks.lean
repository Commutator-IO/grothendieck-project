import Buffalo.AG.Part06d
import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct
import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedBaseChange

/-!
# Buffalo, algebraic geometry, part 06 (d): perfect fields and geometric reducedness, completed

Entries of `docs/buffalo-ag/index.tex` lines 893–899 that `Part06d.lean` proves only in part,
completed here with the vendored AxiomMath/Stacks files on geometrically reduced algebras and
schemes (Apache-2.0, see `lean/Stacks/NOTICE.md`):

* `Oqhr-Gt66es-16790`: `prop_16790_tfae` — the four characterisations of perfect fields, using
  `PerfectField.isReduced_tensorProduct` (Stacks tag 00I4) and the counterexample of `Part06d`.
* `Oqhr-Gt66es-17116`: `prop_17116_general` — `K ⊗_k L` reduced for any two extensions of a
  perfect field (tag 00I4).
* `Oqhr-Gt66es-17370`: `prop_17370_tfae` — the equivalent definitions of a separable
  (geometrically reduced) algebra, from `Algebra.isGeometricallyReduced_tfae` (tag 030V) and
  `Algebra.IsGeometricallyReduced.isReduced_tensorProduct` (tag 034N), for any perfect extension
  `K₁` (into which every finite purely inseparable extension embeds, by `PerfectRing.lift`).
* `Oqhr-Gt66es-17899`: `prop_17899_perfect` — over a perfect field every reduced algebra and every
  reduced scheme is separable (tags 00I4, 020I).
* `Oqhr-Gt66es-17970`: `prop_17970_iff` — `X` is separable over `k` iff `X_{k'}` is over `k'`
  (tag 0384).
-/

open CategoryTheory Limits AlgebraicGeometry TensorProduct

universe u

namespace Buffalo.AG.Part06

variable (k : Type u) [Field k]

/-- Oqhr-Gt66es-16790 (4:39:50) [prop] For a field `k` of characteristic `p > 0` the following are
equivalent: `k` is perfect; `A ⊗_k B` is reduced for all reduced `k`-algebras `A, B`;
`A ⊗_k k'` is reduced for every reduced `A` and every extension `k'`; `k' ⊗_k k'` is reduced for
every finite purely inseparable extension `k'`. (In characteristic `0` all four hold.) -/
theorem prop_16790_tfae (p : ℕ) [Fact p.Prime] [CharP k p] :
    List.TFAE
      [PerfectField k,
       ∀ (A B : Type u) [CommRing A] [Algebra k A] [IsReduced A] [CommRing B] [Algebra k B]
         [IsReduced B], IsReduced (A ⊗[k] B),
       ∀ (A K : Type u) [CommRing A] [Algebra k A] [IsReduced A] [Field K] [Algebra k K],
         IsReduced (A ⊗[k] K),
       ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] [IsPurelyInseparable k K],
         IsReduced (K ⊗[k] K)] := by
  tfae_have 1 → 2 := fun _ A B _ _ _ _ _ _ => PerfectField.isReduced_tensorProduct k A B
  tfae_have 2 → 3 := fun h A K _ _ _ _ _ => h A K
  tfae_have 3 → 4 := fun h K _ _ _ _ => h K K
  tfae_have 4 → 1 := by
    intro h
    by_contra hk
    obtain ⟨K, _, _, _, _, hK⟩ := (prop_16790 k p).2 hk
    exact hK (h K)
  tfae_finish

/-- Oqhr-Gt66es-17116 (4:45:16) [prop] If `k` is perfect and `K, L` are two extensions of `k`,
then `K ⊗_k L` is reduced (Stacks tag 00I4). -/
theorem prop_17116_general [PerfectField k] (K L : Type u) [Field K] [Field L] [Algebra k K]
    [Algebra k L] : IsReduced (K ⊗[k] L) :=
  PerfectField.isReduced_tensorProduct k K L

/-- A finite purely inseparable extension `k'` of `k` embeds over `k` into every perfect extension
`K₁` of `k` (in characteristic exponent `p`), so `k' ⊗_k A ⊆ K₁ ⊗_k A`. -/
theorem isReduced_tensor_of_perfect_extension (p : ℕ) [ExpChar k p] (A : Type u) [CommRing A]
    [Algebra k A] (K₁ : Type u) [Field K₁] [Algebra k K₁] [ExpChar K₁ p] [PerfectRing K₁ p]
    [IsReduced (K₁ ⊗[k] A)] (k' : Type u) [Field k'] [Algebra k k'] [IsPurelyInseparable k k'] :
    IsReduced (k' ⊗[k] A) := by
  have : ExpChar k' p := expChar_of_injective_algebraMap (algebraMap k k').injective p
  let φ : k' →ₐ[k] K₁ :=
    { PerfectRing.lift (algebraMap k k') (algebraMap k K₁) p with
      commutes' := PerfectRing.lift_comp_apply (algebraMap k k') (algebraMap k K₁) p }
  have hinj : Function.Injective (φ.toLinearMap.rTensor A) :=
    Module.Flat.rTensor_preserves_injective_linearMap φ.toLinearMap φ.toRingHom.injective
  exact isReduced_of_injective (Algebra.TensorProduct.map φ (AlgHom.id k A)) hinj

/-- Oqhr-Gt66es-17370 (4:49:30) [prop] For a `k`-algebra `A` (`k` of characteristic exponent
`p`) and a perfect extension `K₁` of `k`, the following are equivalent (`A` is then called
geometrically reduced, or separable): `A ⊗_k B` is reduced for every reduced `k`-algebra `B`;
`A ⊗_k k'` is reduced for every extension `k'`; `A ⊗_k K₁` is reduced; `A ⊗_k k'` is reduced for
every finite purely inseparable extension `k'`; and Mathlib's `Algebra.IsGeometricallyReduced`
(`A ⊗_k k̄` reduced). Stacks tags 030V and 034N. -/
theorem prop_17370_tfae (p : ℕ) [ExpChar k p] (A : Type u) [CommRing A] [Algebra k A]
    (K₁ : Type u) [Field K₁] [Algebra k K₁] [ExpChar K₁ p] [PerfectRing K₁ p] :
    List.TFAE
      [∀ (B : Type u) [CommRing B] [Algebra k B] [IsReduced B], IsReduced (A ⊗[k] B),
       ∀ (k' : Type u) [Field k'] [Algebra k k'], IsReduced (A ⊗[k] k'),
       IsReduced (A ⊗[k] K₁),
       ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
         [IsPurelyInseparable k k'], IsReduced (A ⊗[k] k'),
       Algebra.IsGeometricallyReduced k A] := by
  have H := Algebra.isGeometricallyReduced_tfae k p A
    (perfectClosure k (AlgebraicClosure k)) (AlgebraicClosure k)
  -- `A ⊗ B` is reduced iff `B ⊗ A` is.
  have comm : ∀ (B : Type u) [CommRing B] [Algebra k B],
      IsReduced (A ⊗[k] B) ↔ IsReduced (B ⊗[k] A) := fun B _ _ =>
    ⟨fun _ => isReduced_of_injective (Algebra.TensorProduct.comm k B A).toRingHom
        (Algebra.TensorProduct.comm k B A).injective,
     fun _ => isReduced_of_injective (Algebra.TensorProduct.comm k A B).toRingHom
        (Algebra.TensorProduct.comm k A B).injective⟩
  have h56 : (∀ (L : Type u) [Field L] [Algebra k L], IsReduced (L ⊗[k] A)) ↔
      Algebra.IsGeometricallyReduced k A := H.out 5 6
  have h16 : (∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'], IsReduced (k' ⊗[k] A)) ↔
      Algebra.IsGeometricallyReduced k A := H.out 1 6
  tfae_have 5 → 1 := fun _ B _ _ _ => (comm B).2 inferInstance
  tfae_have 1 → 2 := fun h k' _ _ => h k'
  tfae_have 2 → 3 := fun h => h K₁
  tfae_have 3 → 4 := fun h k' _ _ _ _ => by
    have : IsReduced (K₁ ⊗[k] A) := (comm K₁).1 h
    exact (comm k').2 (isReduced_tensor_of_perfect_extension k p A K₁ k')
  tfae_have 4 → 5 := fun h => h16.1 fun k' _ _ _ _ => (comm k').1 (h k')
  tfae_finish

/-- Oqhr-Gt66es-17899 (4:58:19) [prop] (the converse over a perfect field) If `k` is perfect,
every reduced `k`-algebra and every reduced `k`-scheme is separable (Stacks tags 00I4, 020I). With
`prop_17899` (`Part06d`), the converse holds for every algebra if and only if `k` is perfect. -/
theorem prop_17899_perfect [PerfectField k] :
    (∀ (A : Type u) [CommRing A] [Algebra k A] [IsReduced A], Algebra.IsGeometricallyReduced k A) ∧
    (∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsReduced X], GeometricallyReduced f) :=
  ⟨fun A _ _ _ => Algebra.IsGeometricallyReduced.of_perfectField k A,
   fun f _ => geometricallyReduced_of_isReduced f⟩

/-- Oqhr-Gt66es-17970 (4:59:30) [prop] For every extension `k'/k`, a `k`-scheme `X` is separable
over `k` if and only if `X_{k'}` is separable over `k'` (Stacks tag 0384). -/
theorem prop_17970_iff {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (k' : Type u) [Field k']
    [Algebra k k'] :
    GeometricallyReduced f ↔
      GeometricallyReduced (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
  geometricallyReduced_iff_baseChange_fieldExtension k k' f

end Buffalo.AG.Part06
