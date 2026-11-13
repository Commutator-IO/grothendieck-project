import Mathlib

/-!
# Quillen, notebook 1972-2, pp. 20–21 and p. 46: splitting a finite-rank endomorphism; an integral

Daniel Quillen's research notebook 1972-2 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201972/1972-2.pdf>), written in
February 1972, compares the group of automorphisms `1 + K`, `K` of finite rank, of an infinitely
generated free module with the stable general linear group. Two statements of the notebook are
formalised here.

**The splitting lemma (pp. 20–21, entry of February 19, 1972).** Let `R` be a ring and `K` an
endomorphism of the free module `R^(S)`. There is a decomposition `R^(S) = V ⊕ Q` with `V`
finitely generated, `K(Q) = 0` and `K(V) ⊂ V` (so that `1 + K` is `(1 + K|_V) ⊕ 1`) if and only
if the image of `K` is finitely generated. On the page `K` is of finite rank (its image lies in
`R^T` for a finite `T ⊂ S`); that hypothesis is not needed, since a finitely generated image
always lies in such an `R^T`. Quillen's proof changes coordinates by the vectors
`e_j - ∑ r_{ji} e_i`; we replace the explicit change of basis by the lifting property of the free
module `R^(S - U)` (`exists_isCompl_le_ker`), which yields the same complement. The page adds
that over a non-noetherian ring some finite-rank maps `R^(S) → R` have kernels containing no
summand of finite corank: `not_exists_splitting_of_not_isNoetherianRing`. Over a noetherian ring
every finite-rank endomorphism splits: `exists_splitting_of_isNoetherianRing`.

* `exists_isCompl_le_ker`: if `M = V ⊕ W` with `W` projective and `K(V) = K(M)`, then `V` has a
  complement inside `ker K`;
* `fg_range_of_isCompl`: if `M = V ⊕ Q`, `V` finitely generated and `K(Q) = 0`, then `K(M)` is
  finitely generated;
* `exists_splitting_iff`: **the lemma of pp. 20–21**;
* `exists_splitting_of_isNoetherianRing`, `not_exists_splitting_of_not_isNoetherianRing`: the
  remarks of pp. 21–22.

**The integral (p. 46, February 1972).** For real `a, b > -1`, nonzero and distinct,
`∫₀¹ ∫₀^{1-x} (1 + a x + b y)⁻² dy dx = log(1+a) / (a(b-a)) + log(1+b) / (b(a-b))`, the
integral over the standard triangle `x, y ≥ 0, x + y ≤ 1`, computed on the page as an iterated
integral: `integral_simplex`.
-/

namespace Quillen.Notebook1972_2

open Submodule LinearMap

section Splitting

universe u

variable {R : Type u} [Ring R]

/-- If `M = V ⊕ W` with `W` projective and the restriction of `K` to `V` has the same image as
`K`, then `V` has a complement contained in the kernel of `K` (the graph of a lift
`W → V` of `K|_W` through `K|_V`). -/
theorem exists_isCompl_le_ker {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (K : M →ₗ[R] N) {V W : Submodule R M} (hVW : IsCompl V W)
    [Module.Projective R W] (hK : range K ≤ V.map K) :
    ∃ Q : Submodule R M, IsCompl V Q ∧ Q ≤ ker K := by
  -- `K|_V : V → range K` is surjective; lift `K|_W : W → range K` through it.
  let f : V →ₗ[R] range K := (K ∘ₗ V.subtype).codRestrict (range K) fun v => mem_range_self K _
  let g : W →ₗ[R] range K := (K ∘ₗ W.subtype).codRestrict (range K) fun w => mem_range_self K _
  have hf : Function.Surjective f := fun ⟨_, hy⟩ =>
    let ⟨v, hv, e⟩ := mem_map.1 (hK hy); ⟨⟨v, hv⟩, Subtype.ext e⟩
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f g hf
  have hKh : ∀ w : W, K (h w) = K w := fun w =>
    congrArg Subtype.val (LinearMap.congr_fun hh w)
  -- The complement: `Q = {w - h w | w ∈ W}`.
  refine ⟨range (W.subtype - V.subtype ∘ₗ h), ⟨?_, ?_⟩, ?_⟩
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hxV, w, rfl⟩
    have : w = 0 := Subtype.ext <| (disjoint_iff_inf_le.1 hVW.disjoint)
      ⟨by simpa using V.add_mem hxV (h w).2, w.2⟩
    simp [this]
  · rw [codisjoint_iff, eq_top_iff, ← hVW.sup_eq_top]
    rintro _ hm
    obtain ⟨v, hv, w, hw, rfl⟩ := mem_sup.1 hm
    have := add_mem_sup (V.add_mem hv (h ⟨w, hw⟩).2)
      (mem_range.2 ⟨⟨w, hw⟩, rfl⟩ : w - (h ⟨w, hw⟩ : M) ∈ range (W.subtype - V.subtype ∘ₗ h))
    rwa [add_add_sub_cancel] at this
  · rintro x ⟨w, rfl⟩
    simp [hKh]

/-- If `M = V ⊕ Q` with `V` finitely generated and `K(Q) = 0`, then the image of `K` is finitely
generated: it is `K(V)`. -/
theorem fg_range_of_isCompl {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (K : M →ₗ[R] N) {V Q : Submodule R M} (hVQ : IsCompl V Q) (hV : V.FG)
    (hQ : Q ≤ ker K) : (range K).FG := by
  rw [← Submodule.map_top, ← hVQ.sup_eq_top, Submodule.map_sup, le_ker_iff_map.1 hQ, sup_bot_eq]
  exact hV.map K

variable {S : Type*}

/-- `R^(U)` and `R^(S - U)` are complementary in `R^(S)`. -/
theorem isCompl_supported (U : Set S) :
    IsCompl (Finsupp.supported R R U) (Finsupp.supported R R Uᶜ) :=
  ⟨Finsupp.disjoint_supported_supported isCompl_compl.disjoint,
    Finsupp.codisjoint_supported_supported isCompl_compl.codisjoint⟩

/-- `R^(U)` is finitely generated for `U` finite. -/
theorem fg_supported {U : Set S} (hU : U.Finite) : (Finsupp.supported R R U).FG := by
  rw [Finsupp.supported_eq_span_single]
  exact fg_span (hU.image _)

/-- If the image of `K : R^(S) → N` is finitely generated, there is a finite `U ⊂ S` such that
`K(R^(U))` is the whole image of `K`, and, when `N = R^(S)`, the image lies in `R^(U)`. -/
theorem exists_finite_supported (K : (S →₀ R) →ₗ[R] (S →₀ R)) (hK : (range K).FG) :
    ∃ U : Set S, U.Finite ∧ range K ≤ (Finsupp.supported R R U).map K ∧
      range K ≤ Finsupp.supported R R U := by
  classical
  obtain ⟨G, hG⟩ := hK
  choose x hx using fun g (hg : g ∈ G) => mem_range.1 (hG ▸ subset_span hg : g ∈ range K)
  let U : Set S := ↑(G.attach.biUnion fun g => (g : S →₀ R).support ∪ (x g g.2).support)
  have hU : ∀ g (hg : g ∈ G) s, s ∈ g.support ∨ s ∈ (x g hg).support → s ∈ U := fun g hg s hs => by
    simp only [U, Finset.coe_biUnion, Finset.mem_coe, Finset.mem_attach, Set.iUnion_true,
      Set.mem_iUnion, Finset.coe_union, Set.mem_union]
    exact ⟨⟨g, hg⟩, hs⟩
  refine ⟨U, Finset.finite_toSet _, ?_, ?_⟩ <;> rw [← hG, span_le] <;> intro g hg
  · exact ⟨x g hg, (Finsupp.mem_supported _ _).2 fun s hs => hU g hg s (.inr hs), hx g hg⟩
  · exact (Finsupp.mem_supported _ _).2 fun s hs => hU g hg s (.inl hs)

/-- **Quillen, notebook 1972-2, pp. 20–21.** An endomorphism `K` of the free module `R^(S)` over
any ring admits a decomposition `R^(S) = V ⊕ Q` with `V` finitely generated, `K(Q) = 0` and
`K(V) ⊂ V` if and only if its image is finitely generated. Moreover `V` can be taken of the form
`R^(U)`, `U ⊂ S` finite. -/
theorem exists_splitting_iff (K : (S →₀ R) →ₗ[R] (S →₀ R)) :
    (∃ V Q : Submodule R (S →₀ R), IsCompl V Q ∧ V.FG ∧ Q ≤ ker K ∧ V.map K ≤ V) ↔
      (range K).FG := by
  refine ⟨fun ⟨V, Q, hVQ, hV, hQ, _⟩ => fg_range_of_isCompl K hVQ hV hQ, fun hK => ?_⟩
  obtain ⟨U, hU, hKU, hKU'⟩ := exists_finite_supported K hK
  have : Module.Projective R (Finsupp.supported R R Uᶜ) :=
    Module.Projective.of_equiv (Finsupp.supportedEquivFinsupp Uᶜ).symm
  obtain ⟨Q, hVQ, hQ⟩ := exists_isCompl_le_ker K (isCompl_supported U) hKU
  exact ⟨_, Q, hVQ, fg_supported hU, hQ, (map_le_range).trans hKU'⟩

/-- **Quillen, notebook 1972-2, p. 22.** Over a noetherian ring, every endomorphism of finite rank
of `R^(S)` (image in `R^(T)` for a finite `T ⊂ S`) splits as in `exists_splitting_iff`. -/
theorem exists_splitting_of_isNoetherianRing [IsNoetherianRing R] (K : (S →₀ R) →ₗ[R] (S →₀ R))
    {T : Set S} (hT : T.Finite) (hKT : range K ≤ Finsupp.supported R R T) :
    ∃ V Q : Submodule R (S →₀ R), IsCompl V Q ∧ V.FG ∧ Q ≤ ker K ∧ V.map K ≤ V :=
  (exists_splitting_iff K).2 ((fg_supported hT).of_le hKT)

/-- **Quillen, notebook 1972-2, p. 21.** Over a ring that is not (left) noetherian, there is a
map `K : R^(S) → R`, of finite rank since its target is `R`, whose kernel contains no complement
of a finitely generated submodule: for `S` a left ideal `I` that is not finitely generated, the
map `e_i ↦ i`. -/
theorem not_exists_splitting_of_not_isNoetherianRing (hR : ¬ IsNoetherianRing R) :
    ∃ (S : Type u) (K : (S →₀ R) →ₗ[R] R),
      ¬ ∃ V Q : Submodule R (S →₀ R), IsCompl V Q ∧ V.FG ∧ Q ≤ ker K := by
  obtain ⟨I, hI⟩ : ∃ I : Submodule R R, ¬ I.FG := by
    by_contra! h
    exact hR ⟨h⟩
  refine ⟨I, Finsupp.linearCombination R (Subtype.val : I → R), ?_⟩
  rintro ⟨V, Q, hVQ, hV, hQ⟩
  apply hI
  have := fg_range_of_isCompl _ hVQ hV hQ
  rw [Finsupp.range_linearCombination, Subtype.range_coe_subtype] at this
  have h' : (span R (I : Set R)).FG := this
  rwa [span_eq] at h'

end Splitting

section Integral

open Real intervalIntegral

/-- Positivity of `1 + a x + b y` on the triangle `x, y ≥ 0`, `x + y ≤ 1`, for `a, b > -1`: it
is a convex combination of `1`, `1 + a`, `1 + b`. -/
theorem one_add_pos {a b x y : ℝ} (ha : -1 < a) (hb : -1 < b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ 1) : 0 < 1 + a * x + b * y := by
  set c := min 1 (min (1 + a) (1 + b))
  have hc : 0 < c := lt_min one_pos (lt_min (by linarith) (by linarith))
  have hc1 : c ≤ 1 := min_le_left _ _
  have hca : c ≤ 1 + a := (min_le_right _ _).trans (min_le_left _ _)
  have hcb : c ≤ 1 + b := (min_le_right _ _).trans (min_le_right _ _)
  nlinarith [mul_nonneg hx (sub_nonneg.2 hca), mul_nonneg hy (sub_nonneg.2 hcb),
    mul_nonneg (sub_nonneg.2 hxy) (sub_nonneg.2 hc1)]

/-- The inner integral: `∫₀^{1-x} (1 + a x + b y)⁻² dy = (1/b) (1/(1 + a x) - 1/(1 + a x + b(1-x)))`
for `x ∈ [0, 1]`. -/
theorem integral_inner {a b x : ℝ} (ha : -1 < a) (hb : -1 < b) (hb0 : b ≠ 0) (hx : 0 ≤ x)
    (hx1 : x ≤ 1) :
    ∫ y in (0 : ℝ)..1 - x, ((1 + a * x + b * y) ^ 2)⁻¹ =
      (1 / b) * (1 / (1 + a * x) - 1 / (1 + a * x + b * (1 - x))) := by
  have hpos : ∀ y ∈ Set.uIcc (0 : ℝ) (1 - x), 0 < 1 + a * x + b * y := by
    intro y hy
    rw [Set.uIcc_of_le (by linarith)] at hy
    exact one_add_pos ha hb hx hy.1 (by linarith [hy.2])
  have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) (1 - x),
      HasDerivAt (fun y => -(1 / b) * (1 + a * x + b * y)⁻¹) ((1 + a * x + b * y) ^ 2)⁻¹ y := by
    intro y hy
    have hne := (hpos y hy).ne'
    have h1 : HasDerivAt (fun y => 1 + a * x + b * y) b y := by
      simpa using ((hasDerivAt_id y).const_mul b).const_add (1 + a * x)
    convert (h1.inv hne).const_mul (-(1 / b)) using 1
    field_simp
  have hcont : ContinuousOn (fun y => ((1 + a * x + b * y) ^ 2)⁻¹) (Set.uIcc 0 (1 - x)) :=
    ContinuousOn.inv₀ (by fun_prop) fun y hy => (pow_pos (hpos y hy) 2).ne'
  rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [mul_zero, add_zero]
  ring

/-- **Quillen, notebook 1972-2, p. 46.** For real `a, b > -1` with `a ≠ 0`, `b ≠ 0`, `a ≠ b`,
the integral of `(1 + a x + b y)⁻²` over the triangle `x, y ≥ 0`, `x + y ≤ 1`, written as an
iterated integral, is `log(1+a) / (a(b-a)) + log(1+b) / (b(a-b))`. -/
theorem integral_simplex {a b : ℝ} (ha : -1 < a) (hb : -1 < b) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : a ≠ b) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1 - x, ((1 + a * x + b * y) ^ 2)⁻¹ =
      log (1 + a) / (a * (b - a)) + log (1 + b) / (b * (a - b)) := by
  have hsub : a - b ≠ 0 := sub_ne_zero.2 hab
  have hpos1 : ∀ x ∈ Set.uIcc (0 : ℝ) 1, 0 < 1 + a * x := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    simpa using one_add_pos ha hb hx.1 le_rfl (by linarith [hx.2])
  have hpos2 : ∀ x ∈ Set.uIcc (0 : ℝ) 1, 0 < 1 + a * x + b * (1 - x) := by
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact one_add_pos ha hb hx.1 (by linarith [hx.2]) (by linarith)
  rw [integral_congr (g := fun x => (1 / b) * (1 / (1 + a * x) - 1 / (1 + a * x + b * (1 - x))))
    fun x hx => by
      rw [Set.uIcc_of_le zero_le_one] at hx
      exact integral_inner ha hb hb0 hx.1 hx.2]
  -- An antiderivative of the outer integrand.
  let G : ℝ → ℝ := fun x =>
    (1 / b) * (log (1 + a * x) / a - log (1 + a * x + b * (1 - x)) / (a - b))
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt G ((1 / b) * (1 / (1 + a * x) - 1 / (1 + a * x + b * (1 - x)))) x := by
    intro x hx
    have h1 : HasDerivAt (fun x => 1 + a * x) a x := by
      simpa using ((hasDerivAt_id x).const_mul a).const_add 1
    have h2 : HasDerivAt (fun x => 1 + a * x + b * (1 - x)) (a - b) x := by
      have := ((hasDerivAt_id x).const_mul (a - b)).const_add (1 + b)
      convert this using 1
      · funext y; simp only [id_eq]; ring
      · ring
    have := (((h1.log (hpos1 x hx).ne').div_const a).sub
      ((h2.log (hpos2 x hx).ne').div_const (a - b))).const_mul (1 / b)
    convert this using 1
    field_simp
  have hcont : ContinuousOn
      (fun x => (1 / b) * (1 / (1 + a * x) - 1 / (1 + a * x + b * (1 - x)))) (Set.uIcc 0 1) :=
    continuousOn_const.mul <|
      (continuousOn_const.div (by fun_prop) fun x hx => (hpos1 x hx).ne').sub
        (continuousOn_const.div (by fun_prop) fun x hx => (hpos2 x hx).ne')
  rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [G, mul_one, mul_zero, add_zero, sub_self, log_one, zero_div, sub_zero]
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  field_simp
  ring

end Integral

end Quillen.Notebook1972_2
