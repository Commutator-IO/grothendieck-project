import Buffalo.Groupes.Part02

/-!
# Buffalo, algebraic groups, Part 02: board items not covered by an index entry

Board items of `public/buffalo-boards/` in the time range of Part 02 (videos `_lTf_L0yvrU` from
5:51 and `3ULFIl_2Wis` up to 1:42) that make a claim no index entry of the part formalises, or
that were corrected. Statuses in `docs/buffalo-groupes/lean/Part02-boards.json`.
-/

namespace Buffalo.Groupes.Part02

open TensorProduct Polynomial

universe u

/-- _lTf_L0yvrU-21165 board, t = 21555 [p] `M' ⊗ A → M ⊗ A` need not be injective: `2 : ℤ → ℤ`
is injective, but `ℤ ⊗ ℤ/2 → ℤ ⊗ ℤ/2` kills `1 ⊗ 1 ≠ 0`. -/
theorem rTensor_not_injective :
    ¬ Function.Injective ((LinearMap.lsmul ℤ ℤ 2).rTensor (ZMod 2)) := by
  intro h
  have h1 : (LinearMap.lsmul ℤ ℤ 2).rTensor (ZMod 2) ((1 : ℤ) ⊗ₜ (1 : ZMod 2)) = 0 := by
    rw [LinearMap.rTensor_tmul, LinearMap.lsmul_apply, smul_eq_mul, mul_one,
      show (2 : ℤ) = (2 : ℤ) • (1 : ℤ) by norm_num, TensorProduct.smul_tmul]
    rw [show (2 : ℤ) • (1 : ZMod 2) = 0 by decide, TensorProduct.tmul_zero]
  have h2 : ((1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 2)) ≠ 0 := by
    intro h0
    have := congrArg (TensorProduct.lid ℤ (ZMod 2)) h0
    rw [TensorProduct.lid_tmul, one_smul, map_zero] at this
    exact one_ne_zero this
  exact h2 (h (h1.trans (map_zero _).symm))

/-- _lTf_L0yvrU-21165 board, t = 21555 [p] … and `V(M) → V(M')` need not be surjective: for
`2 : ℤ → ℤ`, the identity of `ℤ` is not of the form `φ ∘ 2`. -/
theorem V_not_surjective :
    ¬ Function.Surjective (fun φ : ℤ →ₗ[ℤ] ℤ ↦ φ ∘ₗ LinearMap.lsmul ℤ ℤ 2) := by
  intro h
  obtain ⟨φ, hφ⟩ := h LinearMap.id
  have := LinearMap.congr_fun hφ 1
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lsmul_apply, smul_eq_mul, mul_one,
    LinearMap.id_apply] at this
  have h2 : (2 : ℤ) * φ 1 = 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    convert this using 2
  omega

/-- _lTf_L0yvrU-23851 board, t = 25330 [p] (corrected) The radicial endomorphism `t ↦ t^p` of
`𝔾_m` in characteristic `p` is injective on the points over every reduced ring (fields
included), yet not an isomorphism: it is not injective on `k[ε]`-points
(`Part01.frobUnits_not_injective`). -/
theorem frob_units_injective {R : Type*} [CommRing R] [IsReduced R] (p : ℕ) [Fact p.Prime]
    [CharP R p] : Function.Injective (Part01.frobUnits R p) := by
  intro x y h
  apply Units.ext
  have := congrArg Units.val h
  simp only [Part01.frobUnits, powMonoidHom_apply, Units.val_pow_eq_pow_val] at this
  exact frobenius_inj R p this

/-- _lTf_L0yvrU-28721 board, t = 30559 [p] (corrected) Affine commutative groups are not reflexive
in general: over a field, a character of `𝔾_a` (a unit `u` of `K[X]` with `u(0) = 1`) is
trivial, so `D(𝔾_a) = 1` and `D(D(𝔾_a)) ≠ 𝔾_a`. -/
theorem Ga_characters_trivial {K : Type*} [Field K] (u : K[X]) (hu : IsUnit u)
    (h0 : u.eval 0 = 1) : u = 1 := by
  obtain ⟨r, -, rfl⟩ := Polynomial.isUnit_iff.mp hu
  rw [eval_C] at h0
  rw [h0, C_1]

/-- _lTf_L0yvrU-21165 board, t = 21426 [p] "Unit and associativity then hold on `M''`
automatically": a structure `δ''` compatible with a comodule `δ` along a surjection `q` is a
comodule. -/
theorem quot_isComodule {k A M M'' : Type u} [CommRing k] [AddCommGroup A] [Module k A]
    [Coalgebra k A] [AddCommGroup M] [Module k M] [AddCommGroup M''] [Module k M'']
    {δ : M →ₗ[k] M ⊗[k] A} (hδ : Part01.IsComodule k A M δ) {q : M →ₗ[k] M''}
    (hq : Function.Surjective q) {δ'' : M'' →ₗ[k] M'' ⊗[k] A}
    (h : δ'' ∘ₗ q = q.rTensor A ∘ₗ δ) : Part01.IsComodule k A M'' δ'' := by
  have hc := LinearMap.congr_fun hδ.counit
  have ha := LinearMap.congr_fun hδ.coassoc
  have hh := LinearMap.congr_fun h
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.id_apply]
    at hc ha hh
  constructor
  · refine LinearMap.ext fun y ↦ ?_
    obtain ⟨x, rfl⟩ := hq y
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.id_apply, hh]
    have nat : ∀ z : M ⊗[k] A, TensorProduct.rid k M'' ((Coalgebra.counit (R := k) (A := A)).lTensor
        M'' (q.rTensor A z)) = q (TensorProduct.rid k M ((Coalgebra.counit (R := k)).lTensor M z)) := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a b => simp
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [nat, hc]
  · refine LinearMap.ext fun y ↦ ?_
    obtain ⟨x, rfl⟩ := hq y
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hh]
    have nat1 : ∀ z : M ⊗[k] A, (Coalgebra.comul (R := k) (A := A)).lTensor M'' (q.rTensor A z) =
        q.rTensor (A ⊗[k] A) ((Coalgebra.comul (R := k) (A := A)).lTensor M z) := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a b => simp
      | add a b ha hb => simp only [map_add, ha, hb]
    have nat2 : ∀ z : M ⊗[k] A, δ''.rTensor A (q.rTensor A z) =
        (q.rTensor A).rTensor A (δ.rTensor A z) := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a b => simp [hh]
      | add a b ha hb => simp only [map_add, ha, hb]
    have nat3 : ∀ w : (M ⊗[k] A) ⊗[k] A, TensorProduct.assoc k M'' A A ((q.rTensor A).rTensor A w) =
        q.rTensor (A ⊗[k] A) (TensorProduct.assoc k M A A w) := by
      intro w
      induction w using TensorProduct.inductionOn with
      | tmul a b =>
        induction a using TensorProduct.inductionOn with
        | tmul c d => simp
        | add c d hc hd => simp only [map_add, TensorProduct.add_tmul, hc, hd]
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [nat1, ha, nat2, nat3]

end Buffalo.Groupes.Part02
