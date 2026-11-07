import Buffalo.AG.Part05

/-!
# Buffalo, algebraic geometry, part 05: blackboard items

The board items of `public/buffalo-boards/` in the time range of part 05 that no index entry
formalises (`docs/buffalo-ag/lean/Part05-boards.json`).
-/

open CategoryTheory

namespace Buffalo.AG.Part05

/-- Board `thSz9ZHDK9o-29212`, t = 31166 (corrected): above an invertible quotient `L` of `M`, the
points of `V*` are the isomorphisms `L ≃ R` (`prop_31232`), i.e. the linear forms `φ ∈ L^∨` that
are bijective; these are exactly the generators of `L^∨ = 𝒪(-1)`, `𝔾_m` acting by multiplication.
So `V* = Isom(𝒪_P(1), 𝒪_P)` is the torsor of `𝒪_P(-1)` under `L ↦ Isom(𝒪, L)`. -/
theorem board_31166 {A L : Type*} [CommRing A] [AddCommGroup L] [Module A L] (e : L ≃ₗ[A] A)
    (φ : Module.Dual A L) : Function.Bijective φ ↔ Submodule.span A {φ} = ⊤ := by
  constructor
  · intro hφ
    let g := LinearEquiv.ofBijective φ hφ
    rw [eq_top_iff]
    intro ψ _
    refine Submodule.mem_span_singleton.2 ⟨ψ (g.symm 1), LinearMap.ext fun l => ?_⟩
    have hl : l = φ l • g.symm 1 := g.injective (by
      rw [map_smul]
      change φ l = φ l • φ (g.symm 1)
      rw [show φ (g.symm 1) = g (g.symm 1) from rfl, LinearEquiv.apply_symm_apply, smul_eq_mul,
        mul_one])
    rw [LinearMap.smul_apply, smul_eq_mul]
    conv_rhs => rw [hl]
    rw [map_smul, smul_eq_mul, mul_comm]
  · intro h
    have he : (e : L →ₗ[A] A) ∈ Submodule.span A {φ} := h ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 he
    have hce : ∀ l, e l = c * φ l := fun l => by
      rw [← smul_eq_mul, ← LinearMap.smul_apply, hc]
      rfl
    have hu : c * φ (e.symm 1) = 1 := by rw [← hce, LinearEquiv.apply_symm_apply]
    refine ⟨fun l l' hll' => e.injective (by rw [hce, hce, hll']), fun a => ?_⟩
    refine ⟨(a * c) • e.symm 1, ?_⟩
    rw [map_smul, smul_eq_mul, mul_assoc, hu, mul_one]

/-- Board `Oqhr-Gt66es-0000`, t = 2728 (corrected): a local artinian ring need not be an algebra
over its residue field, so it is "of finite length", not "finite-dimensional over the residue
field": `ℤ/4` (local artinian with residue field `ℤ/2`) has no `ℤ/2`-algebra structure. -/
theorem board_2728 : IsEmpty (Algebra (ZMod 2) (ZMod 4)) := by
  refine ⟨fun h => ?_⟩
  have h2 : (algebraMap (ZMod 2) (ZMod 4)) 2 = 2 := map_ofNat _ 2
  have h0 : (2 : ZMod 2) = 0 := rfl
  rw [h0, map_zero] at h2
  exact absurd h2 (by decide)

/-- Board `Oqhr-Gt66es-0000`, t = 2857: a noetherian scheme with finitely many points need not be
artinian: a discrete valuation ring (two points) is noetherian but not artinian. -/
theorem board_2857 (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsNoetherianRing R ∧ ¬ IsArtinianRing R :=
  ⟨inferInstance, fun _ => IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)⟩

end Buffalo.AG.Part05
