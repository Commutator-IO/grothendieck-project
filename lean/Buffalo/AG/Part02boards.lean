import Buffalo.AG.Part02

/-!
# Buffalo, algebraic geometry, part 02: board items not covered by the index

Claims on the reconstructed blackboards `public/buffalo-boards/51wmmpHand0-*.json`
(4:56:31–8:36:03) that no index entry of part 02 formalises, and the counterexamples behind the
corrections of the boards. Status in `docs/buffalo-ag/lean/Part02-boards.json`.
-/

open TopologicalSpace PrimeSpectrum

namespace Buffalo.AG.Part02

/-- Board 51wmmpHand0-17719, t = 19952 [m] (corrected) `∐ X_i(K') → X(K')` is injective when
`K' ≠ 0`; for `K' = 0` it is not as soon as there are two indices (`cex_21337`). -/
theorem board_19952 {k : Type*} [CommRing k] {ι : Type*} [DecidableEq ι] (A : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra k (A i)] (k' : Type*) [CommRing k'] [Algebra k k']
    [Nontrivial k'] :
    Function.Injective (fun x : (Σ i, A i →ₐ[k] k') => x.2.comp (Pi.evalAlgHom k A x.1)) := by
  rintro ⟨i, ψ⟩ ⟨j, ψ'⟩ h
  have hij : i = j := by
    by_contra hij
    have := DFunLike.congr_fun h (Pi.single i 1)
    simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply, Pi.single_eq_same, map_one,
      Pi.single_eq_of_ne' hij, map_zero] at this
    exact one_ne_zero this
  subst hij
  have : ψ = ψ' := AlgHom.ext fun a => by
    have := DFunLike.congr_fun h (Pi.single i a)
    simpa using this
  rw [this]

/-- Board 51wmmpHand0-23482, t = 24326 [m] `V(J) ⊇ V(J')` iff `√J ⊆ √J'`. -/
theorem board_24326 {A : Type*} [CommRing A] (J J' : Ideal A) :
    zeroLocus (J' : Set A) ⊆ zeroLocus J ↔ J.radical ≤ J'.radical := by
  rw [zeroLocus_subset_zeroLocus_iff, Ideal.radical_le_radical_iff]

/-- Board 51wmmpHand0-23482, t = 24582 [p] (corrected) The hypothesis `X ≠ ∅` is needed: in the
empty space every nonempty open set is (vacuously) dense, but the empty space is not
irreducible. -/
theorem board_24582 :
    (∀ U : Set Empty, IsOpen U → U.Nonempty → Dense U) ∧ ¬ IrreducibleSpace Empty :=
  ⟨fun _ _ ⟨x, _⟩ => isEmptyElim x, fun h => isEmptyElim h.toNonempty.some⟩

end Buffalo.AG.Part02
