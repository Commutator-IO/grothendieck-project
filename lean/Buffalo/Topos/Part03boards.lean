import Buffalo.Topos.Part03c

/-!
# Buffalo, topos theory, part 3: the blackboards

Lean support for the checked items of the reconstructed blackboards `URU5jgTvjhU-30214/34123/38022`
and `PqCQM3Pcl6Q-0000/2947/5910/6937/9878` in the time range of part 3 that no index entry covers,
and for the corrections made to them. Status table: `docs/buffalo-topos/lean/Part03-boards.json`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Topology TypeCat

namespace Buffalo.Topos.Part03

noncomputable section

/-- Board `PqCQM3Pcl6Q-2947`, t = 4217 (corrected): for `C` with finite limits, `u_!` is left exact
iff `u` is (`u` flat); `u^*` is always exact. -/
theorem lan_lex_iff {C C' : Type u} [SmallCategory C] [SmallCategory C'] [HasFiniteLimits C]
    (φ : C ⥤ C') :
    PreservesFiniteLimits φ ↔ PreservesFiniteLimits (φ.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ (C'ᵒᵖ ⥤ Type u)) :=
  preservesFiniteLimits_iff_lan_preservesFiniteLimits φ

/-- ... and in general `u_!` is left exact iff `u` is flat. -/
theorem lan_lex_iff_flat {C C' : Type u} [SmallCategory C] [SmallCategory C'] [HasFiniteLimits C]
    (φ : C ⥤ C') :
    RepresentablyFlat φ ↔
      PreservesFiniteLimits (φ.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ (C'ᵒᵖ ⥤ Type u)) := by
  rw [flat_iff_lan_flat]
  exact ⟨fun _ => preservesFiniteLimits_of_flat _, fun _ => flat_of_preservesFiniteLimits _⟩

/-- Board `PqCQM3Pcl6Q-2947`, t = 4960 (corrected): `Γ = f_*` is a right adjoint, so it commutes with
all products in every topos `Sh(C, J)`; it is the inverse image `I ↦ ∐_I e` whose commutation with
products characterizes local connectedness. -/
theorem global_sections_preservesLimits {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) {T : C} (hT : IsTerminal T) :
    PreservesLimits ((sheafSections J (Type u)).obj (op T)) :=
  (toFinal J hT).adj.rightAdjoint_preservesLimits

/-- Board `PqCQM3Pcl6Q-6937`, t = 8734 (corrected): a ring of characteristic `p` is not flat over
`ℤ`, so « flat over `ℤ` » cannot be meant; the descent `A_i` is flat over `K_i`. -/
theorem zmod_not_flat : ¬ Module.Flat ℤ (ZMod 2) := fun _ => by
  have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := ZMod 2)
    (mem_nonZeroDivisors_of_ne_zero (two_ne_zero : (2 : ℤ) ≠ 0))
  have := @h 1 0 (by decide)
  exact absurd this (by decide)

/-- The presheaf `U ↦ M(U)^{(ℕ)} = M(U) ⊗ K(U)^{(ℕ)}` on the discrete space `ℕ`, with
`M = K = ℤ`-valued functions. -/
def infiniteSumPresheaf : (TopCat.of ℕ).Presheaf (Type) where
  obj U := ℕ →₀ (U.unop → ℤ)
  map i := ↾fun s => Finsupp.mapRange (fun f => f ∘ Set.inclusion (leOfHom i.unop)) rfl s
  map_id U := by
    ext s n x
    simp
  map_comp i j := by
    ext s n x
    simp

/-- Board `PqCQM3Pcl6Q-6937`, t = 7808 (corrected): for `N = K^{(I)}` with `I` infinite the presheaf
tensor product `U ↦ M(U) ⊗ N(U) = M(U)^{(I)}` is not a sheaf. -/
theorem infiniteSumPresheaf_not_isSheaf : ¬ infiniteSumPresheaf.IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types]
  intro h
  let V : ℕ → Opens (TopCat.of ℕ) := fun n => ⟨{n}, isOpen_discrete _⟩
  let sf : ∀ n, infiniteSumPresheaf.obj (op (V n)) := fun n => Finsupp.single n fun _ => 1
  obtain ⟨s, hs, -⟩ := h V sf (fun n m => by
    by_cases hnm : n = m
    · subst hnm; rfl
    · have he : ∀ x : ((V n ⊓ V m : Opens (TopCat.of ℕ)) : Set ℕ), False := fun ⟨x, hx, hx'⟩ =>
        hnm ((Set.mem_singleton_iff.1 hx).symm.trans (Set.mem_singleton_iff.1 hx'))
      have hz : ∀ t : ℕ →₀ ((V n ⊓ V m : Opens (TopCat.of ℕ)) → ℤ), t = 0 :=
        fun t => Finsupp.ext fun k => funext fun x => (he x).elim
      exact (hz _).trans (hz _).symm)
  let s' : ℕ →₀ (↥(iSup V) → ℤ) := s
  have hmem : ∀ n, n ∈ s'.support := fun n => by
    let pt : V n := ⟨n, Set.mem_singleton n⟩
    have := congrArg (fun t : ℕ →₀ (V n → ℤ) => t n pt) (hs n)
    simp only [sf, Finsupp.single_eq_same] at this
    rw [Finsupp.mem_support_iff]
    intro h0
    change (Finsupp.mapRange (fun f => f ∘ Set.inclusion (leOfHom (Opens.leSupr V n))) rfl s') n
      pt = 1 at this
    rw [Finsupp.mapRange_apply, h0] at this
    exact absurd this (by simp)
  exact (Set.infinite_univ (α := ℕ)) ((s'.support.finite_toSet).subset fun n _ => hmem n)

end

end Buffalo.Topos.Part03
