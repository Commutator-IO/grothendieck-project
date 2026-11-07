import Buffalo.AG.Part01

/-!
# Buffalo, algebraic geometry, part 01: board items not covered by the index

Claims on the reconstructed blackboards `public/buffalo-boards/51wmmpHand0-*.json` (0:00:00–4:55:19)
that no index entry of part 01 formalises. Status in `docs/buffalo-ag/lean/Part01-boards.json`.
-/

open MvPolynomial

namespace Buffalo.AG.Part01

/-- Board 51wmmpHand0-5671, t = 5943 [m] Over `k = ℝ`, `x² + 1 = 0` and `x² + y² + 1 = 0` have no
real point but have complex points. -/
theorem board_5943 :
    (∀ x : ℝ, x ^ 2 + 1 ≠ 0) ∧ (∀ x y : ℝ, x ^ 2 + y ^ 2 + 1 ≠ 0) ∧
      (∃ x : ℂ, x ^ 2 + 1 = 0) ∧ (∃ x y : ℂ, x ^ 2 + y ^ 2 + 1 = 0) :=
  ⟨fun x => by positivity, fun x y => by positivity, ⟨Complex.I, by simp⟩,
    ⟨Complex.I, 0, by simp⟩⟩

/-- Board 51wmmpHand0-7660, t = 8910 [p] Points with values in reduced rings only see
`A/nil(A)`: every homomorphism from `A` to a reduced ring kills the nilradical. -/
theorem board_8910 {k A R : Type*} [CommRing k] [CommRing A] [Algebra k A] [CommRing R]
    [IsReduced R] [Algebra k R] (u : A →ₐ[k] R) : nilradical A ≤ RingHom.ker u := fun _ hf =>
  (RingHom.mem_ker).2 (((mem_nilradical).1 hf).map u).eq_zero

end Buffalo.AG.Part01
