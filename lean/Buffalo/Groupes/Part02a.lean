import Buffalo.Groupes.Part01

/-!
# Buffalo, algebraic groups, Part 02 (a): subcomodules, finiteness, embeddings

Entries `_lTf_L0yvrU-21300` to `_lTf_L0yvrU-25194` of `docs/buffalo-groupes/index.tex` (end of
13 June and beginning of 19 June 1973). Statuses in `docs/buffalo-groupes/lean/Part02.json`.

Conventions (as in Part 01). A right comodule over a `k`-coalgebra `A` is a `k`-module `M` with
`δ : M → M ⊗ A` (`Part01.IsComodule`). The algebra `H = A^∨` acts on `M` by
`s • x = (id ⊗ s)(δ x)` (`act`); a submodule `N` is a subcomodule when `δ(N)` lies in the image of
`N ⊗ A → M ⊗ A` (`IsSubcomodule`).
-/

namespace Buffalo.Groupes.Part02

open TensorProduct LinearMap

universe u

variable (k : Type u) [CommRing k]

/-! ## Subcomodules and quotient comodules -/

section Sub

variable {k} {A M M' M'' : Type u} [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M]
  [AddCommGroup M'] [Module k M'] [AddCommGroup M''] [Module k M'']

/-- _lTf_L0yvrU-21300 (5:55:00) [def] For a surjection `q : M → M''`, `V(M'') → V(M)`,
`u ↦ u ∘ q`, is injective (at every `k'`). -/
theorem V_injective_of_surjective {q : M →ₗ[k] M''} (hq : Function.Surjective q) (R : Type u)
    [CommRing R] [Algebra k R] : Function.Injective (fun u : M'' →ₗ[k] R ↦ u ∘ₗ q) :=
  fun u v h ↦ LinearMap.ext fun x ↦ by
    obtain ⟨y, rfl⟩ := hq x
    exact LinearMap.congr_fun h y

/-- _lTf_L0yvrU-21300 (5:55:00) [def] The quotient comodule structure on `M''`, when it exists,
is unique. -/
theorem quot_struct_unique {q : M →ₗ[k] M''} (hq : Function.Surjective q) (δ : M →ₗ[k] M ⊗[k] A)
    (δ₁ δ₂ : M'' →ₗ[k] M'' ⊗[k] A) (h₁ : δ₁ ∘ₗ q = q.rTensor A ∘ₗ δ)
    (h₂ : δ₂ ∘ₗ q = q.rTensor A ∘ₗ δ) : δ₁ = δ₂ :=
  LinearMap.ext fun x ↦ by
    obtain ⟨y, rfl⟩ := hq x
    exact (LinearMap.congr_fun h₁ y).trans (LinearMap.congr_fun h₂ y).symm

/-- _lTf_L0yvrU-21685 (6:01:25) [def] An induced structure on `i : M' → M` is unique when
`M' ⊗ A → M ⊗ A` is injective. -/
theorem induced_struct_unique {i : M' →ₗ[k] M} (hi : Function.Injective (i.rTensor A))
    (δ : M →ₗ[k] M ⊗[k] A) (δ₁ δ₂ : M' →ₗ[k] M' ⊗[k] A) (h₁ : i.rTensor A ∘ₗ δ₁ = δ ∘ₗ i)
    (h₂ : i.rTensor A ∘ₗ δ₂ = δ ∘ₗ i) : δ₁ = δ₂ :=
  LinearMap.ext fun x ↦ hi ((LinearMap.congr_fun h₁ x).trans (LinearMap.congr_fun h₂ x).symm)

/-- With `M' ⊗ A → M ⊗ A` injective, `M'` has an induced structure iff `δ(M')` lands in the image
of `M' ⊗ A`. -/
theorem sub_stable_iff {i : M' →ₗ[k] M} (hi : Function.Injective (i.rTensor A))
    (δ : M →ₗ[k] M ⊗[k] A) :
    (∃ δ' : M' →ₗ[k] M' ⊗[k] A, i.rTensor A ∘ₗ δ' = δ ∘ₗ i) ↔
      ∀ x, δ (i x) ∈ LinearMap.range (i.rTensor A) := by
  constructor
  · rintro ⟨δ', h⟩ x
    exact ⟨δ' x, LinearMap.congr_fun h x⟩
  · intro h
    refine ⟨(LinearEquiv.ofInjective _ hi).symm.toLinearMap ∘ₗ
      LinearMap.codRestrict _ (δ ∘ₗ i) h, LinearMap.ext fun x ↦ ?_⟩
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    exact congrArg Subtype.val ((LinearEquiv.ofInjective _ hi).apply_symm_apply _)

/-- A quotient `q : M → M''` (with kernel the image of `i`) carries a compatible structure iff
`δ(M')` lands in the image of `M' ⊗ A` (right exactness of `⊗ A`; no flatness needed). -/
theorem quot_stable_iff {i : M' →ₗ[k] M} {q : M →ₗ[k] M''} (hex : Function.Exact i q)
    (hq : Function.Surjective q) (δ : M →ₗ[k] M ⊗[k] A) :
    (∃ δ'' : M'' →ₗ[k] M'' ⊗[k] A, δ'' ∘ₗ q = q.rTensor A ∘ₗ δ) ↔
      ∀ x, δ (i x) ∈ LinearMap.range (i.rTensor A) := by
  have hex' := rTensor_exact A hex hq
  constructor
  · rintro ⟨δ'', h⟩ x
    rw [← hex'.linearMap_ker_eq, LinearMap.mem_ker]
    have := LinearMap.congr_fun h (i x)
    simp only [LinearMap.coe_comp, Function.comp_apply, hex.apply_apply_eq_zero, map_zero] at this
    exact this.symm
  · intro h
    have hker : LinearMap.ker q ≤ LinearMap.ker (q.rTensor A ∘ₗ δ) := by
      intro y hy
      obtain ⟨x, rfl⟩ := (hex y).mp hy
      rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.mem_ker, hex'.linearMap_ker_eq]
      exact h x
    refine ⟨q.liftOfSurjective hq ⟨_, hker⟩, LinearMap.ext fun y ↦ ?_⟩
    simp

/-- _lTf_L0yvrU-21749 (6:02:29) [prop] When `M' ⊗ A → M ⊗ A` is injective, `M'` is stable (has an
induced structure) iff the quotient `M''` is. -/
theorem stable_iff_quot_stable {i : M' →ₗ[k] M} {q : M →ₗ[k] M''} (hex : Function.Exact i q)
    (hq : Function.Surjective q) (hi : Function.Injective (i.rTensor A)) (δ : M →ₗ[k] M ⊗[k] A) :
    (∃ δ' : M' →ₗ[k] M' ⊗[k] A, i.rTensor A ∘ₗ δ' = δ ∘ₗ i) ↔
      ∃ δ'' : M'' →ₗ[k] M'' ⊗[k] A, δ'' ∘ₗ q = q.rTensor A ∘ₗ δ :=
  (sub_stable_iff hi δ).trans (quot_stable_iff hex hq δ).symm

/-- _lTf_L0yvrU-21812 (6:03:32) [prop] Injectivity of `M' ⊗ A → M ⊗ A`: if `A` is flat
(Mathlib `Module.Flat.rTensor_preserves_injective_linearMap`) … -/
theorem rTensor_injective_of_flat [Module.Flat k A] {i : M' →ₗ[k] M}
    (hi : Function.Injective i) : Function.Injective (i.rTensor A) :=
  Module.Flat.rTensor_preserves_injective_linearMap i hi

/-- _lTf_L0yvrU-21812 (6:03:32) [prop] … or if `M'` is a direct factor (`i` has a retraction). -/
theorem rTensor_injective_of_retraction {i : M' →ₗ[k] M} {r : M →ₗ[k] M'}
    (hr : r ∘ₗ i = LinearMap.id) : Function.Injective (i.rTensor A) := by
  have : r.rTensor A ∘ₗ i.rTensor A = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, hr, LinearMap.rTensor_id]
  exact Function.LeftInverse.injective (g := r.rTensor A) fun x ↦ LinearMap.congr_fun this x

/-- A submodule `N ⊆ M` is a subcomodule when `δ(N) ⊆ N ⊗ A` (the image of `N ⊗ A → M ⊗ A`). -/
def IsSubcomodule (δ : M →ₗ[k] M ⊗[k] A) (N : Submodule k M) : Prop :=
  ∀ x ∈ N, δ x ∈ LinearMap.range (N.subtype.rTensor A)

theorem range_rTensor_mono {N₁ N₂ : Submodule k M} (h : N₁ ≤ N₂) :
    LinearMap.range (N₁.subtype.rTensor A) ≤ LinearMap.range (N₂.subtype.rTensor A) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨(Submodule.inclusion h).rTensor A y, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  rfl

/-- _lTf_L0yvrU-21812 (6:03:32) [prop] Subcomodules are stable under sums (no hypothesis on `A`). -/
theorem IsSubcomodule.sup {δ : M →ₗ[k] M ⊗[k] A} {N₁ N₂ : Submodule k M}
    (h₁ : IsSubcomodule δ N₁) (h₂ : IsSubcomodule δ N₂) : IsSubcomodule δ (N₁ ⊔ N₂) := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact add_mem (range_rTensor_mono le_sup_left (h₁ y hy))
    (range_rTensor_mono le_sup_right (h₂ z hz))

end Sub

/-! ## The action of `H = A^∨` and subcomodules for `A` projective -/

section Act

variable {k} {A M : Type u} [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M]

/-- The action of a linear form `s ∈ A^∨` on a comodule: `s • x = (id ⊗ s)(δ x)`. -/
noncomputable def act (δ : M →ₗ[k] M ⊗[k] A) (s : A →ₗ[k] k) : M →ₗ[k] M :=
  (TensorProduct.rid k M).toLinearMap ∘ₗ s.lTensor M ∘ₗ δ

theorem rid_lTensor_rTensor {N : Type u} [AddCommGroup N] [Module k N] (f : N →ₗ[k] M)
    (s : A →ₗ[k] k) (y : N ⊗[k] A) :
    TensorProduct.rid k M (s.lTensor M (f.rTensor A y)) = f (TensorProduct.rid k N (s.lTensor N y)) := by
  induction y using TensorProduct.inductionOn with
  | tmul a b => simp
  | add a b ha hb => simp only [map_add, ha, hb]

/-- For `A` projective, linear forms separate the elements of `Q ⊗ A`. -/
theorem eq_zero_of_forall_form [Module.Projective k A] {Q : Type u} [AddCommGroup Q] [Module k Q]
    (z : Q ⊗[k] A) (h : ∀ s : A →ₗ[k] k, TensorProduct.rid k Q (s.lTensor Q z) = 0) : z = 0 := by
  classical
  obtain ⟨σ, hσ⟩ := Module.projective_def'.mp (inferInstance : Module.Projective k A)
  have h1 : σ.lTensor Q z = 0 := by
    apply (finsuppScalarRight k k Q A).injective
    ext a
    rw [finsuppScalarRight_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply,
      ← LinearMap.comp_apply (lTensor Q (Finsupp.lapply a)), ← LinearMap.lTensor_comp]
    exact h _
  have : z = (Finsupp.linearCombination k _root_.id).lTensor Q (σ.lTensor Q z) := by
    rw [← LinearMap.comp_apply (lTensor Q _), ← LinearMap.lTensor_comp, hσ, LinearMap.lTensor_id,
      LinearMap.id_apply]
  rw [this, h1, map_zero]

/-- For `A` projective, `y ∈ M ⊗ A` lies in `N ⊗ A` iff all its contractions `(id ⊗ s) y` lie
in `N`. -/
theorem mem_range_rTensor_iff [Module.Projective k A] (N : Submodule k M) (y : M ⊗[k] A) :
    y ∈ LinearMap.range (N.subtype.rTensor A) ↔
      ∀ s : A →ₗ[k] k, TensorProduct.rid k M (s.lTensor M y) ∈ N := by
  constructor
  · rintro ⟨w, rfl⟩ s
    rw [rid_lTensor_rTensor]
    exact Subtype.mem _
  · intro h
    have hex := rTensor_exact A (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective N)
    rw [← hex.linearMap_ker_eq, LinearMap.mem_ker]
    apply eq_zero_of_forall_form
    intro s
    rw [rid_lTensor_rTensor, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h s

/-- _lTf_L0yvrU-22219 (6:10:19) [prop] If `A` is projective (e.g. a direct sum of finitely
generated projectives), a submodule is a subcomodule iff it is a sub-`H`-module. -/
theorem isSubcomodule_iff [Module.Projective k A] (δ : M →ₗ[k] M ⊗[k] A) (N : Submodule k M) :
    IsSubcomodule δ N ↔ ∀ s : A →ₗ[k] k, ∀ x ∈ N, act δ s x ∈ N := by
  simp only [IsSubcomodule, mem_range_rTensor_iff]
  exact ⟨fun h s x hx ↦ h x hx s, fun h x hx s ↦ h s x hx⟩

/-- The `⇒` half holds for any `A`. -/
theorem IsSubcomodule.act_mem {δ : M →ₗ[k] M ⊗[k] A} {N : Submodule k M} (h : IsSubcomodule δ N)
    (s : A →ₗ[k] k) {x : M} (hx : x ∈ N) : act δ s x ∈ N := by
  obtain ⟨w, hw⟩ := h x hx
  simp only [act, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ← hw,
    rid_lTensor_rTensor]
  exact Subtype.mem _

end Act

/-! ## The action is a module structure over the convolution algebra -/

section ActMul

variable {k} {A M : Type u} [AddCommGroup A] [Module k A] [Coalgebra k A] [AddCommGroup M]
  [Module k M]

open WithConv

/-- `act` by the counit is the identity (counit axiom). -/
theorem act_counit {δ : M →ₗ[k] M ⊗[k] A} (hδ : Part01.IsComodule k A M δ) (x : M) :
    act δ (Coalgebra.counit (R := k) (A := A)) x = x :=
  LinearMap.congr_fun hδ.counit x

/-- `s • (t • x) = (s ⋆ t) • x`, the convolution product of `A^∨` (coassociativity). -/
theorem act_act {δ : M →ₗ[k] M ⊗[k] A} (hδ : Part01.IsComodule k A M δ) (s t : A →ₗ[k] k)
    (x : M) : act δ s (act δ t x) = act δ (toConv s * toConv t).ofConv x := by
  let Φ : M ⊗[k] (A ⊗[k] A) →ₗ[k] M :=
    (TensorProduct.rid k M).toLinearMap ∘ₗ (LinearMap.mul' k k ∘ₗ TensorProduct.map s t).lTensor M
  have hw : ∀ (w : M ⊗[k] A) (b : A), t b • TensorProduct.rid k M (s.lTensor M w) =
      Φ (TensorProduct.assoc k M A A (w ⊗ₜ b)) := by
    intro w b
    induction w using TensorProduct.inductionOn with
    | tmul m a => simp [Φ, smul_smul, mul_comm]
    | add a c ha hc => simp only [map_add, smul_add, ha, hc, TensorProduct.add_tmul]
  have hA : ∀ y : M ⊗[k] A, act δ s (TensorProduct.rid k M (t.lTensor M y)) =
      Φ (TensorProduct.assoc k M A A (δ.rTensor A y)) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul m b =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_smul, LinearMap.rTensor_tmul]
      exact hw (δ m) b
    | add a c ha hc => simp only [map_add, ha, hc]
  have hco := LinearMap.congr_fun hδ.coassoc x
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at hco
  change act δ s (TensorProduct.rid k M (t.lTensor M (δ x))) = _
  rw [hA, ← hco]
  simp only [Φ, act, LinearMap.convMul_def, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [← LinearMap.comp_apply (lTensor M _), ← LinearMap.lTensor_comp]
  rfl

end ActMul

/-! ## Smallest subcomodules and finiteness -/

section Hull

variable {k} {A M : Type u} [AddCommGroup A] [Module k A] [Coalgebra k A] [AddCommGroup M]
  [Module k M]

open WithConv

/-- The sub-`H`-module generated by `N`: `⨆_s s • N`. -/
noncomputable def hull (δ : M →ₗ[k] M ⊗[k] A) (N : Submodule k M) : Submodule k M :=
  ⨆ s : A →ₗ[k] k, N.map (act δ s)

theorem le_hull {δ : M →ₗ[k] M ⊗[k] A} (hδ : Part01.IsComodule k A M δ) (N : Submodule k M) :
    N ≤ hull δ N := fun x hx ↦
  Submodule.mem_iSup_of_mem (Coalgebra.counit (R := k) (A := A))
    ⟨x, hx, act_counit hδ x⟩

theorem hull_act_mem {δ : M →ₗ[k] M ⊗[k] A} (hδ : Part01.IsComodule k A M δ) (N : Submodule k M)
    (s : A →ₗ[k] k) {x : M} (hx : x ∈ hull δ N) : act δ s x ∈ hull δ N := by
  have : (hull δ N).map (act δ s) ≤ hull δ N := by
    rw [hull, Submodule.map_iSup]
    refine iSup_le fun t ↦ ?_
    rw [← Submodule.map_comp]
    have : act δ s ∘ₗ act δ t = act δ (toConv s * toConv t).ofConv :=
      LinearMap.ext fun y ↦ act_act hδ s t y
    rw [this]
    exact le_iSup (fun r : A →ₗ[k] k ↦ N.map (act δ r)) _
  exact this ⟨x, hx, rfl⟩

omit [Coalgebra k A] in
theorem hull_le {δ : M →ₗ[k] M ⊗[k] A} {N N' : Submodule k M} (h : N ≤ N')
    (hN' : IsSubcomodule δ N') : hull δ N ≤ N' :=
  iSup_le fun s ↦ by
    rintro _ ⟨x, hx, rfl⟩
    exact hN'.act_mem s (h hx)

/-- _lTf_L0yvrU-22283 (6:11:23) [prop] For `A` projective, every submodule `N` is contained in a
smallest subcomodule, the sub-`H`-module it generates. -/
theorem hull_isSubcomodule [Module.Projective k A] {δ : M →ₗ[k] M ⊗[k] A}
    (hδ : Part01.IsComodule k A M δ) (N : Submodule k M) :
    N ≤ hull δ N ∧ IsSubcomodule δ (hull δ N) ∧
      ∀ N' : Submodule k M, N ≤ N' → IsSubcomodule δ N' → hull δ N ≤ N' :=
  ⟨le_hull hδ N, (isSubcomodule_iff δ _).mpr fun s _ hx ↦ hull_act_mem hδ N s hx,
    fun _ h h' ↦ hull_le h h'⟩

omit [Coalgebra k A] in
/-- _lTf_L0yvrU-22476 (6:14:36) [prop] The sub-`H`-module generated by `x` is `Hx`, the span of
the image of `s ↦ s • x`. -/
theorem hull_span_singleton (δ : M →ₗ[k] M ⊗[k] A) (x : M) :
    hull δ (Submodule.span k {x}) = Submodule.span k (Set.range fun s : A →ₗ[k] k ↦ act δ s x) := by
  rw [hull]
  simp_rw [Submodule.map_span, Set.image_singleton]
  rw [← Submodule.span_iUnion, Set.iUnion_singleton_eq_range]

section Basis

variable {ι : Type u} [DecidableEq ι] (b : Module.Basis ι k A)

omit [Coalgebra k A] in
/-- With a basis of `A`, `s • x = ∑ s(bᵢ) cᵢ(x)` where `δ x = ∑ cᵢ(x) ⊗ bᵢ`. -/
theorem act_eq_sum (δ : M →ₗ[k] M ⊗[k] A) (s : A →ₗ[k] k) (x : M) :
    act δ s x = (TensorProduct.equivFinsuppOfBasisRight b (δ x)).sum fun i m ↦ s (b i) • m := by
  conv_lhs => rw [act, LinearMap.comp_apply, LinearMap.comp_apply,
    ← (TensorProduct.equivFinsuppOfBasisRight b).symm_apply_apply (δ x),
    TensorProduct.equivFinsuppOfBasisRight_symm_apply]
  simp [map_finsuppSum]

omit [Coalgebra k A] in
theorem act_coord (δ : M →ₗ[k] M ⊗[k] A) (j : ι) (x : M) :
    act δ (b.coord j) x = TensorProduct.equivFinsuppOfBasisRight b (δ x) j := by
  classical
  rw [act_eq_sum b]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rw [Finsupp.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · simp

omit [Coalgebra k A] in
/-- The finite set of coefficients `cᵢ(x)`. -/
noncomputable def coeffs (δ : M →ₗ[k] M ⊗[k] A) (x : M) : Finset M := by
  classical
  exact (TensorProduct.equivFinsuppOfBasisRight b (δ x)).support.image
    (TensorProduct.equivFinsuppOfBasisRight b (δ x))

omit [Coalgebra k A] in
theorem act_mem_span_coeffs (δ : M →ₗ[k] M ⊗[k] A) (s : A →ₗ[k] k) (x : M) :
    act δ s x ∈ Submodule.span k (coeffs b δ x : Set M) := by
  classical
  rw [act_eq_sum b]
  refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp only [coeffs, Finset.coe_image]
  exact Set.mem_image_of_mem _ hi

omit [Coalgebra k A] in
theorem coeffs_subset_hull (δ : M →ₗ[k] M ⊗[k] A) {N : Submodule k M} {x : M} (hx : x ∈ N) :
    (coeffs b δ x : Set M) ⊆ hull δ N := by
  classical
  intro m hm
  simp only [coeffs, Finset.coe_image, Set.mem_image] at hm
  obtain ⟨i, -, rfl⟩ := hm
  rw [← act_coord b]
  exact Submodule.mem_iSup_of_mem (b.coord i) ⟨x, hx, rfl⟩

omit [Coalgebra k A] in
/-- _lTf_L0yvrU-22283 (6:11:23) [prop] For `A` free, the sub-`H`-module generated by a finitely
generated `N` is finitely generated. -/
theorem hull_fg (b : Module.Basis ι k A) (δ : M →ₗ[k] M ⊗[k] A) {N : Submodule k M} (hN : N.FG) : (hull δ N).FG := by
  classical
  obtain ⟨S, rfl⟩ := hN
  refine ⟨S.biUnion (coeffs b δ), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro m hm
    simp only [Finset.coe_biUnion, Set.mem_iUnion] at hm
    obtain ⟨x, hx, hm⟩ := hm
    exact coeffs_subset_hull b δ (Submodule.subset_span hx) hm
  · refine iSup_le fun s ↦ ?_
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.span_mono ?_ (act_mem_span_coeffs b δ s x)
    intro m hm
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨x, hx, hm⟩

omit [Coalgebra k A] in
/-- _lTf_L0yvrU-22476 (6:14:36) [prop] … in particular `Hx` is finitely generated (`A` free). -/
theorem hull_singleton_fg (b : Module.Basis ι k A) (δ : M →ₗ[k] M ⊗[k] A) (x : M) :
    (Submodule.span k (Set.range fun s : A →ₗ[k] k ↦ act δ s x)).FG := by
  rw [← hull_span_singleton]
  exact hull_fg b δ (Submodule.fg_span_singleton x)

/-- _lTf_L0yvrU-22545 (6:15:45) [prop] For `A` free, every comodule is the filtered union of its
finitely generated subcomodules: every `x` lies in one, and the sum of two is one. -/
theorem exists_fg_subcomodule (b : Module.Basis ι k A) {δ : M →ₗ[k] M ⊗[k] A} (hδ : Part01.IsComodule k A M δ) (x : M) :
    ∃ N : Submodule k M, N.FG ∧ IsSubcomodule δ N ∧ x ∈ N := by
  have : Module.Projective k A := Module.Projective.of_basis b
  refine ⟨hull δ (Submodule.span k {x}), hull_fg b δ (Submodule.fg_span_singleton x),
    (hull_isSubcomodule hδ _).2.1, le_hull hδ _ (Submodule.mem_span_singleton_self x)⟩

omit [Coalgebra k A] in
theorem fg_subcomodule_sup {δ : M →ₗ[k] M ⊗[k] A} {N₁ N₂ : Submodule k M}
    (h₁ : N₁.FG ∧ IsSubcomodule δ N₁) (h₂ : N₂.FG ∧ IsSubcomodule δ N₂) :
    (N₁ ⊔ N₂).FG ∧ IsSubcomodule δ (N₁ ⊔ N₂) :=
  ⟨h₁.1.sup h₂.1, h₁.2.sup h₂.2⟩

end Basis

/-- _lTf_L0yvrU-22676 (6:17:56) [prop] A coalgebra is a (right) comodule over itself by `π`; the
same two axioms (Mathlib `Coalgebra.coassoc`, counit laws) make it a left comodule. -/
theorem regular_isComodule : Part01.IsComodule k A A (Coalgebra.comul (R := k) (A := A)) where
  counit := by
    rw [Coalgebra.lTensor_counit_comp_comul]
    ext; simp
  coassoc := Coalgebra.coassoc.symm

end Hull

/-! ## Subcoalgebras -/

section Subcoalgebra

variable {k} {A : Type u} [AddCommGroup A] [Module k A]

/-- _lTf_L0yvrU-22996 (6:23:16) [prop] If `A/B` is flat, `(B ⊗ A) ∩ (A ⊗ B) = B ⊗ B` in
`A ⊗ A`. -/
theorem inter_tensor (B : Submodule k A) [Module.Flat k (A ⧸ B)] (y : A ⊗[k] A)
    (h₁ : y ∈ LinearMap.range (B.subtype.rTensor A))
    (h₂ : y ∈ LinearMap.range (B.subtype.lTensor A)) :
    y ∈ LinearMap.range (TensorProduct.map B.subtype B.subtype) := by
  obtain ⟨z, rfl⟩ := h₁
  obtain ⟨w, hw⟩ := h₂
  have hinj : Function.Injective (B.subtype.rTensor (A ⧸ B)) :=
    Module.Flat.rTensor_preserves_injective_linearMap B.subtype B.injective_subtype
  have h0 : B.mkQ.lTensor B z = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, ← hw, ← LinearMap.comp_apply,
      ← LinearMap.lTensor_comp]
    have : B.mkQ ∘ₗ B.subtype = 0 := by ext; simp
    rw [this, LinearMap.lTensor_zero, LinearMap.zero_apply]
  have hex := lTensor_exact B (LinearMap.exact_subtype_mkQ B) (Submodule.mkQ_surjective B)
  obtain ⟨u, rfl⟩ := (hex z).mp h0
  exact ⟨u, by rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]⟩

/-- _lTf_L0yvrU-22996 (6:23:16) [prop] Hence, `A/B` flat, `B` is stable on the left
(`π(B) ⊆ B ⊗ A`) and on the right (`π(B) ⊆ A ⊗ B`) iff `π(B) ⊆ B ⊗ B`. -/
theorem stable_both_iff (π : A →ₗ[k] A ⊗[k] A) (B : Submodule k A) [Module.Flat k (A ⧸ B)] :
    (∀ x ∈ B, π x ∈ LinearMap.range (B.subtype.rTensor A) ∧
        π x ∈ LinearMap.range (B.subtype.lTensor A)) ↔
      ∀ x ∈ B, π x ∈ LinearMap.range (TensorProduct.map B.subtype B.subtype) := by
  refine ⟨fun h x hx ↦ inter_tensor B _ (h x hx).1 (h x hx).2, fun h x hx ↦ ?_⟩
  obtain ⟨u, hu⟩ := h x hx
  refine ⟨⟨B.subtype.lTensor B u, ?_⟩, ⟨B.subtype.rTensor B u, ?_⟩⟩
  · rw [← hu, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]
  · rw [← hu, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]

end Subcoalgebra

/-! ## Affine monoids and groups over a field: finiteness and linear embeddings -/

section Embedding

variable {k} {A : Type u} [CommRing A] [Bialgebra k A]

/-- _lTf_L0yvrU-23196 (6:26:36) [prop] The step of the proof: the subalgebra generated by a
subcoalgebra `C` is a sub-bialgebra (`π` maps it into `S ⊗ S`), i.e. a quotient monoid. -/
theorem comul_adjoin_mem (C : Submodule k A)
    (hC : ∀ c ∈ C, Coalgebra.comul (R := k) c ∈ LinearMap.range (TensorProduct.map C.subtype C.subtype))
    {a : A} (ha : a ∈ Algebra.adjoin k (C : Set A)) :
    Coalgebra.comul (R := k) a ∈ (Algebra.TensorProduct.map (Algebra.adjoin k (C : Set A)).val
      (Algebra.adjoin k (C : Set A)).val).range := by
  set S := Algebra.adjoin k (C : Set A)
  have hle : Algebra.adjoin k (C : Set A) ≤
      (Algebra.TensorProduct.map S.val S.val).range.comap (Bialgebra.comulAlgHom k A) := by
    rw [Algebra.adjoin_le_iff]
    intro c hc
    obtain ⟨w, hw⟩ := hC c hc
    have hCS : ∀ x ∈ C, x ∈ S := fun x hx ↦ Algebra.subset_adjoin hx
    let ι : C →ₗ[k] S := LinearMap.codRestrict (Subalgebra.toSubmodule S) C.subtype
      fun x ↦ hCS x x.2
    refine ⟨TensorProduct.map ι ι w, ?_⟩
    calc _ = TensorProduct.map (S.val.toLinearMap ∘ₗ ι) (S.val.toLinearMap ∘ₗ ι) w := by
          rw [TensorProduct.map_comp]; rfl
      _ = _ := hw
  exact hle ha

/-- _lTf_L0yvrU-23263 (6:27:43) [thm] The step of the proof of the linear embedding: if
`m₁, …, mₙ` generate `A` as an algebra and `π(mⱼ) = ∑ᵢ mᵢ ⊗ aᵢⱼ`, then the matrix coefficients
`aᵢⱼ` also generate `A` (`mⱼ = ∑ᵢ ε(mᵢ) aᵢⱼ`), so `k[End(kⁿ)] → A`, `xᵢⱼ ↦ aᵢⱼ`, is onto: the
representation on `M = ⟨mᵢ⟩` is a closed immersion into `End(kⁿ)` (also _lTf_L0yvrU-24059,
_lTf_L0yvrU-24788). -/
theorem coeff_generate {n : ℕ} (m : Fin n → A) (a : Fin n → Fin n → A)
    (hm : ∀ j, Coalgebra.comul (R := k) (m j) = ∑ i, m i ⊗ₜ[k] a i j)
    (hgen : Algebra.adjoin k (Set.range m) = ⊤) :
    Algebra.adjoin k (Set.range fun p : Fin n × Fin n ↦ a p.1 p.2) = ⊤ := by
  refine eq_top_iff.mpr (hgen ▸ Algebra.adjoin_le ?_)
  rintro _ ⟨j, rfl⟩
  have h := congrArg (TensorProduct.lid k A ∘ (Coalgebra.counit (R := k) (A := A)).rTensor A) (hm j)
  simp only [Function.comp_apply, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul,
    map_sum, LinearMap.rTensor_tmul] at h
  rw [h]
  exact Subalgebra.sum_mem _ fun i _ ↦ Subalgebra.smul_mem _
    (Algebra.subset_adjoin (Set.mem_range_self (f := fun p : Fin n × Fin n ↦ a p.1 p.2) (i, j))) _

/-- _lTf_L0yvrU-23455 (6:30:55) [prop] One step: for a commutative Hopf algebra the antipode is an
algebra map (Mathlib `HopfAlgebra.antipodeAlgHom`), so the subalgebra generated by a set stable
under the antipode is stable under it, and the quotient monoid `G_i` is a group. -/
theorem antipode_mem_adjoin {H : Type u} [CommRing H] [HopfAlgebra k H] (S : Set H)
    (hS : ∀ s ∈ S, HopfAlgebra.antipode k s ∈ S) {a : H} (ha : a ∈ Algebra.adjoin k S) :
    HopfAlgebra.antipode k a ∈ Algebra.adjoin k S := by
  have : Algebra.adjoin k S ≤ (Algebra.adjoin k S).comap (HopfAlgebra.antipodeAlgHom k H) :=
    Algebra.adjoin_le fun s hs ↦ Algebra.subset_adjoin (hS s hs)
  exact this ha

end Embedding

/-! ## Monomorphisms and monoids embedded in groups -/

section Mono

/-- _lTf_L0yvrU-24192 (6:43:12) [rem] A linear action of a monoid need not be by automorphisms:
`(k, ×)` acting on `k` by multiplication, `0` acts by a non-invertible endomorphism. -/
theorem zero_action_not_unit [Nontrivial k] :
    ¬ IsUnit (LinearMap.mulLeft k (0 : k) : Module.End k k) := fun h ↦
  h.ne_zero (LinearMap.mulLeft_zero_eq_zero k k)

/-- _lTf_L0yvrU-24998 (6:56:38) [prop] A faithful special case: a closed immersion of a noetherian
affine scheme into itself (a surjective ring endomorphism of a noetherian ring) is an
isomorphism. -/
theorem injective_of_surjective_endo {R : Type*} [CommRing R] [IsNoetherianRing R] (f : R →+* R)
    (hf : Function.Surjective f) : Function.Injective f := by
  let K : ℕ →o Ideal R := ⟨fun n ↦ RingHom.ker (f ^ n), fun m n hmn x hx ↦ by
    rw [RingHom.mem_ker] at hx ⊢
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [RingHom.coe_pow] at hx ⊢
    rw [add_comm, Function.iterate_add_apply, hx]
    exact iterate_map_zero f d⟩
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) K
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hsurj : Function.Surjective (f ^ n) := by
    rw [RingHom.coe_pow]; exact hf.iterate n
  obtain ⟨y, rfl⟩ := hsurj x
  have hy : y ∈ K (n + 1) := by
    change (f ^ (n + 1)) y = 0
    rw [RingHom.coe_pow, Function.iterate_succ_apply', ← RingHom.coe_pow, hx]
  rw [← hn (n + 1) (Nat.le_succ n)] at hy
  exact hy

/-- _lTf_L0yvrU-24998 (6:56:38) [prop] The finite step of the arithmetic proof: on a finite set
(the points over a finite field), an injective self-map is bijective. -/
theorem bijective_of_injective_finite {X : Type*} [Finite X] (f : X → X)
    (hf : Function.Injective f) : Function.Bijective f :=
  ⟨hf, Finite.surjective_of_injective hf⟩

/-- _lTf_L0yvrU-25126 (6:58:46) [prop] The same argument on points: a finite monoid that embeds in
a group is a group (translations are injective, hence bijective). -/
theorem isUnit_of_embeds {Mo G : Type*} [Monoid Mo] [Finite Mo] [Group G] (f : Mo →* G)
    (hf : Function.Injective f) (x : Mo) : IsUnit x := by
  have hinj : Function.Injective (x * ·) := fun a b h ↦ hf (by
    have := congrArg f h
    simp only [map_mul] at this
    exact mul_left_cancel this)
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj 1
  have hxy : x * y = 1 := hy
  have hyx : y * x = 1 := hf (by
    have := congrArg f hxy
    rw [map_mul, map_one] at this
    rw [map_mul, map_one, eq_inv_of_mul_eq_one_right this]
    exact inv_mul_cancel (f x))
  exact ⟨⟨x, y, hxy, hyx⟩, rfl⟩

/-- _lTf_L0yvrU-25194 (6:59:54) [cex] `(𝔸¹, ×)` embeds in no group: over any `k' ≠ 0`, a monoid
hom `(k', ×) → G` to a group is never injective. -/
theorem mulMonoid_not_embeds {R G : Type*} [CommRing R] [Nontrivial R] [Group G] (f : R →* G) :
    ¬ Function.Injective f := by
  intro hf
  have h0 : ∀ x : R, f x = 1 := fun x ↦ by
    have : f 0 * f x = f 0 * 1 := by rw [← map_mul, zero_mul, mul_one]
    exact mul_left_cancel this
  exact zero_ne_one (hf ((h0 0).trans (h0 1).symm))

end Mono

/-! ## Quotients of representations of a monoid -/

section QuotRep

variable {k} {M : Type u} [AddCommGroup M] [Module k M]

/-- _lTf_L0yvrU-22019 (6:06:59) [prop] (an abstract monoid `G` acting linearly) A quotient
`M/N` carries an action making `M → M/N` equivariant iff `N` is `G`-stable … -/
theorem quot_action_iff {G : Type*} [Monoid G] (ρ : G →* Module.End k M) (N : Submodule k M) :
    (∃ ρ' : G →* Module.End k (M ⧸ N), ∀ g, ρ' g ∘ₗ N.mkQ = N.mkQ ∘ₗ ρ g) ↔
      ∀ g, ∀ x ∈ N, ρ g x ∈ N := by
  constructor
  · rintro ⟨ρ', h⟩ g x hx
    have := LinearMap.congr_fun (h g) x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero N).mpr hx, map_zero] at this
    exact (Submodule.Quotient.mk_eq_zero N).mp this.symm
  · intro h
    refine ⟨{ toFun := fun g ↦ N.mapQ N (ρ g) (h g)
              map_one' := ?_
              map_mul' := ?_ }, fun g ↦ ?_⟩
    · ext x; simp
    · intro g g'; ext x; simp
    · ext x; simp

/-- … and the action is then unique. -/
theorem quot_action_unique {G : Type*} [Monoid G] (ρ : G →* Module.End k M) (N : Submodule k M)
    (ρ₁ ρ₂ : G →* Module.End k (M ⧸ N)) (h₁ : ∀ g, ρ₁ g ∘ₗ N.mkQ = N.mkQ ∘ₗ ρ g)
    (h₂ : ∀ g, ρ₂ g ∘ₗ N.mkQ = N.mkQ ∘ₗ ρ g) : ρ₁ = ρ₂ :=
  MonoidHom.ext fun g ↦ Submodule.linearMap_qext N ((h₁ g).trans (h₂ g).symm)

end QuotRep

end Buffalo.Groupes.Part02
