import Buffalo.Groupes.Part03

/-!
# Buffalo, algebraic groups, Part 03: board items not covered by the index

Items of the reconstructed blackboards `public/buffalo-boards/3ULFIl_2Wis-*.json` in the time
range of Part 03 that no index entry formalises. Statuses in
`docs/buffalo-groupes/lean/Part03-boards.json`.
-/

namespace Buffalo.Groupes.Part03

open CategoryTheory Limits AlgebraicGeometry

universe u

/-- Board `3ULFIl_2Wis-8161`, t = 8491: a profinite (compact totally disconnected) space is the
limit of its finite discrete quotients, the pro-finite-set side of the equivalence. -/
noncomputable def profinite_asLimit (X : Profinite.{u}) : IsLimit X.asLimitCone :=
  Profinite.asLimit X

/-- Board `3ULFIl_2Wis-14051`, t = 14121: a rational point of a scheme over `k` (a section of the
structure morphism) is a closed immersion, hence a closed point. -/
theorem rationalPoint_isClosedImmersion {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : Spec (.of K) ⟶ X) (hx : x ≫ f = 𝟙 _) : IsClosedImmersion x :=
  isClosedImmersion_of_comp_eq_id f x hx

/-- Board `3ULFIl_2Wis-19834`, t = 21922: `𝔾_m → 𝔾_m`, `λ ↦ λⁿ` (`n ≥ 2`) has no local section
for the Zariski topology: `t` has no `n`-th root among the rational functions `k(t)`. -/
theorem no_rational_nthRoot (K : Type*) [Field K] {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ f : RatFunc K, f ^ n = RatFunc.X := by
  rintro ⟨f, hf⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hf
    exact RatFunc.X_ne_zero hf.symm
  have hdeg : ∀ m : ℕ, (f ^ m).intDegree = m * f.intDegree := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero _ hf0) hf0, ih]; push_cast; ring
  have h := hdeg n
  rw [hf, RatFunc.intDegree_X] at h
  have : (n : ℤ) ∣ 1 := ⟨_, h⟩
  have := Int.eq_one_of_dvd_one (by positivity) this
  omega

/-- Board `3ULFIl_2Wis-19834`, t = 22433: fpqc coverings form a Grothendieck topology on schemes
(Mathlib `Scheme.fpqcTopology`; also `fppfTopology`, `etaleTopology`, `zariskiTopology`). -/
abbrev fpqcSite : GrothendieckTopology Scheme.{u} := Scheme.fpqcTopology

/-- Board `3ULFIl_2Wis-22716`, t = 22847: schemes are sheaves for the fpqc topology (the topology
is subcanonical). -/
theorem fpqc_subcanonical : (Scheme.fpqcTopology.{u}).Subcanonical := inferInstance

/-- Board `3ULFIl_2Wis-22716`, t = 22912: a faithfully flat quasi-compact morphism is an effective
epimorphism, i.e. `Hom(S, X) → Hom(S', X) ⇉ Hom(S' ×_S S', X)` is exact. -/
theorem fpqc_effectiveEpi {S' S : Scheme.{u}} (f : S' ⟶ S) [QuasiCompact f] [Surjective f]
    [Flat f] : EffectiveEpi f := inferInstance

end Buffalo.Groupes.Part03
