import Buffalo.AG.Part07

/-!
# Buffalo, algebraic geometry, part 07: blackboard items

The board items of `public/buffalo-boards/` in the time range of part 07 (video `Oqhr-Gt66es`,
5:24:53–10:19:03) that no index entry formalises (`docs/buffalo-ag/lean/Part07-boards.json`).
-/

open CategoryTheory Limits AlgebraicGeometry PrimeSpectrum TensorProduct

universe u

namespace Buffalo.AG.Part07

noncomputable section

/-- Board `Oqhr-Gt66es-19491`, t = 20540: a quotient map with connected fibres onto a connected
space has a connected source (open-closed subsets are saturated). -/
theorem board_20540 {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
    (hf : Topology.IsQuotientMap f) (hfib : ∀ y, IsConnected (f ⁻¹' {y})) [ConnectedSpace β] :
    ConnectedSpace α := by
  have : Nonempty α := by
    obtain ⟨y⟩ := ‹ConnectedSpace β›.toNonempty
    obtain ⟨x, -⟩ := (hfib y).nonempty
    exact ⟨x⟩
  have hp : PreconnectedSpace α := preconnectedSpace_iff_clopen.2 fun U hU => by
      have hsat : f ⁻¹' (f '' U) = U := by
        refine Set.Subset.antisymm (fun x hx => ?_) (Set.subset_preimage_image f U)
        obtain ⟨x', hx'U, hx'⟩ := hx
        have hc := (hfib (f x)).isPreconnected
        rcases isPreconnected_iff_subset_of_disjoint.mp hc U Uᶜ hU.isOpen hU.compl.isOpen
          (fun z _ => (em (z ∈ U)).elim Or.inl Or.inr) (by simp) with h | h
        · exact h (by simp : x ∈ f ⁻¹' {f x})
        · exact absurd hx'U (h (by simp [hx'] : x' ∈ f ⁻¹' {f x}))
      have hcl : IsClopen (f '' U) :=
        ⟨hf.isClosed_preimage.1 (by rw [hsat]; exact hU.isClosed),
          hf.isOpen_preimage.1 (by rw [hsat]; exact hU.isOpen)⟩
      rcases isClopen_iff.1 hcl with h | h
      · left; rw [← hsat, h, Set.preimage_empty]
      · right; rw [← hsat, h, Set.preimage_univ]
  exact { toPreconnectedSpace := hp, toNonempty := inferInstance }

/-- Board `Oqhr-Gt66es-21373`, t = 21798: diagonals are immersions; separated means that the
diagonal is a closed immersion. -/
theorem board_21798 {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsImmersion (pullback.diagonal f) ∧
      (IsSeparated f ↔ IsClosedImmersion (pullback.diagonal f)) :=
  ⟨inferInstance, ⟨fun h => h.isClosedImmersion_diagonal, fun h => ⟨h⟩⟩⟩

/-- Board `Oqhr-Gt66es-21373`, t = 23093: for `Y = V(J)` with `J` radical, the ideal of functions
vanishing on `Y` is `J`. -/
theorem board_23093 {A : Type*} [CommRing A] (J : Ideal A) (hJ : J.IsRadical) :
    vanishingIdeal (zeroLocus (J : Set A)) = J := by
  rw [vanishingIdeal_zeroLocus_eq_radical, hJ.radical]

/-- Board `Oqhr-Gt66es-24294`, t = 24624: for a class `M` of morphisms stable under composition and
base change, `g ∘ f ∈ M` and `Δ_g ∈ M` imply `f ∈ M` (`f` is the graph, a base change of `Δ_g`,
followed by a base change of `g ∘ f`). -/
theorem board_24624 {C : Type*} [Category C] [HasPullbacks C] (P : MorphismProperty C)
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hfg : P (f ≫ g)) (hg : P (pullback.diagonal g)) : P f := by
  set gr : X ⟶ pullback (f ≫ g) g := pullback.lift (𝟙 X) f (by simp)
  have : f = gr ≫ pullback.snd _ _ := by simp [gr]
  rw [this]
  exact P.comp_mem _ _ (P.of_isPullback (pullback_lift_diagonal_isPullback f g) hg)
    (P.pullback_snd _ _ hfg)

/-- Board `Oqhr-Gt66es-30528`, t = 31224 (for `L = 𝒪_X`): `X_f ∩ X_g = X_{fg}`. -/
theorem board_31224 (X : Scheme.{u}) (f g : Γ(X, ⊤)) :
    X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g :=
  X.basicOpen_mul f g

/-- Board `Oqhr-Gt66es-36305`, t = 37078: flat and faithfully flat modules (mathlib's
`Module.Flat`, `Module.FaithfullyFlat`): faithfully flat iff flat and `N ⊗ M = 0 ⇒ N = 0`. -/
theorem board_37078 (R : Type u) (M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    Module.FaithfullyFlat R M ↔ (Module.Flat R M ∧
      ∀ (N : Type u) [AddCommGroup N] [Module R N], Subsingleton (N ⊗[R] M) → Subsingleton N) :=
  Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality R M

end

end Buffalo.AG.Part07
