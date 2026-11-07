import Buffalo.Groupes.Part02b

/-!
# Buffalo, algebraic groups, Part 02 (c): diagonalizable groups, constant groups, Cartier duality

Entries `_lTf_L0yvrU-28722` to `_lTf_L0yvrU-32249` of `docs/buffalo-groupes/index.tex` (20 June
1973). Statuses in `docs/buffalo-groupes/lean/Part02.json`.

`D(M) = Spec k[M]` (Mathlib `AddMonoidAlgebra k M`, with its bialgebra structure
`e^m ↦ e^m ⊗ e^m`); a representation of `D(M)` on `V` is a comodule `δ : V → V ⊗ k[M]`
(`Part01.IsComodule`); its projectors are `p_m • x = (id ⊗ coord_m)(δ x)` (`proj`).
-/

namespace Buffalo.Groupes.Part02

open TensorProduct LinearMap WithConv

universe u

variable (k : Type u) [CommRing k]

/-! ## Distributions of a diagonalizable group -/

section DistD

variable {k} {M : Type u} [AddCommGroup M] (R : Type u) [CommRing R] [Algebra k R]

/-- The basis `e^m` of `k[M]`. -/
noncomputable abbrev eb : Module.Basis M k (AddMonoidAlgebra k M) := AddMonoidAlgebra.basis M k

omit [AddCommGroup M] in
theorem eb_coord_single [DecidableEq M] (m j : M) :
    (eb (k := k) (M := M)).coord m (AddMonoidAlgebra.single j 1) = if j = m then 1 else 0 := by
  rw [Module.Basis.coord_apply, ← AddMonoidAlgebra.basis_apply (k := k), Module.Basis.repr_self,
    Finsupp.single_apply]

omit [AddCommGroup M] in
theorem eb_repr_single (j : M) :
    (eb (k := k) (M := M)).repr (AddMonoidAlgebra.single j 1) = Finsupp.single j 1 := by
  rw [← AddMonoidAlgebra.basis_apply (k := k), Module.Basis.repr_self]

omit [AddCommGroup M] in
theorem eb_coord_apply (m : M) (u : AddMonoidAlgebra k M) :
    (eb (k := k) (M := M)).coord m u = u.coeff m := rfl

omit [AddCommGroup M] in
/-- _lTf_L0yvrU-28722 (7:58:42) [ex] In `Dist(D(M)) = Hom(k[M], k') ≃ k'^M`, the convolution
product is the ordinary product of functions: `(u ⋆ v)(e^m) = u(e^m) v(e^m)`. -/
theorem convD_single (u v : AddMonoidAlgebra k M →ₗ[k] R) (m : M) :
    (toConv u * toConv v).ofConv (AddMonoidAlgebra.single m 1) =
      u (AddMonoidAlgebra.single m 1) * v (AddMonoidAlgebra.single m 1) := by
  rw [LinearMap.convMul_apply, AddMonoidAlgebra.comul_single]
  simp

/-- The identification `Dist(D(M))(k') ≃ (M → k')`, `u ↦ (m ↦ u(e^m))`. -/
noncomputable def distDEquiv : (AddMonoidAlgebra k M →ₗ[k] R) ≃ₗ[k] (M → R) :=
  ((eb (k := k) (M := M)).constr k).symm

omit [AddCommGroup M] in
theorem distDEquiv_mul (u v : AddMonoidAlgebra k M →ₗ[k] R) :
    distDEquiv R (toConv u * toConv v).ofConv = distDEquiv R u * distDEquiv R v := by
  ext m
  simp only [distDEquiv, Module.Basis.constr_symm_apply, Pi.mul_apply,
    AddMonoidAlgebra.basis_apply]
  exact convD_single R u v m

omit [AddCommGroup M] in
/-- _lTf_L0yvrU-28851 (8:00:51) [prop] The functions `p_m` are pairwise orthogonal idempotents of
`k^M` … -/
theorem pm_idem [DecidableEq M] (m n : M) :
    (Pi.single m 1 : M → k) * Pi.single n 1 = if m = n then Pi.single m 1 else 0 := by
  ext x
  by_cases h : m = n
  · subst h; by_cases hx : x = m <;> simp [hx]
  · rw [Pi.mul_apply]
    simp only [h, ↓reduceIte, Pi.zero_apply]
    by_cases hx : x = m
    · subst hx; simp [Ne.symm h]
    · simp [Pi.single_apply, hx]

omit [AddCommGroup M] in
/-- _lTf_L0yvrU-28851 (8:00:51) [prop] … with sum `1` in the product topology. -/
theorem pm_hasSum [DecidableEq M] [TopologicalSpace k] :
    HasSum (fun m : M ↦ (Pi.single m 1 : M → k)) 1 := by
  rw [Pi.hasSum]
  intro x
  simp only [Pi.one_apply, Pi.single_apply]
  convert hasSum_ite_eq x (1 : k) using 1
  ext m
  by_cases h : x = m <;> simp [h, eq_comm]

omit [AddCommGroup M] in
/-- In `Dist(D(M))`, the coordinate forms `p_m` multiply like the `p_m` of `k^M`. -/
theorem coord_conv [DecidableEq M] (m n : M) :
    toConv ((eb (k := k) (M := M)).coord m) * toConv ((eb (k := k) (M := M)).coord n) =
      if m = n then toConv ((eb (k := k) (M := M)).coord m) else 0 := by
  apply WithConv.ofConv_injective
  apply (eb (k := k) (M := M)).ext
  intro j
  rw [AddMonoidAlgebra.basis_apply, convD_single, eb_coord_single, eb_coord_single]
  split_ifs <;> simp_all [eb_repr_single]

end DistD

/-! ## Representations of `D(M)`: gradings -/

section Grading

variable {k} {M : Type u} [AddCommGroup M] [DecidableEq M] {V : Type u} [AddCommGroup V]
  [Module k V] {δ : V →ₗ[k] V ⊗[k] AddMonoidAlgebra k M}

/-- The projector `p_m` acting on a representation of `D(M)`. -/
noncomputable def proj (δ : V →ₗ[k] V ⊗[k] AddMonoidAlgebra k M) (m : M) : V →ₗ[k] V :=
  act δ ((eb (k := k) (M := M)).coord m)

omit [AddCommGroup M] in
/-- _lTf_L0yvrU-28993 (8:03:13) [prop] The `p_m` act as pairwise orthogonal projectors … -/
theorem proj_proj (hδ : Part01.IsComodule k (AddMonoidAlgebra k M) V δ) (m n : M) (x : V) :
    proj δ m (proj δ n x) = if m = n then proj δ m x else 0 := by
  rw [proj, proj, act_act hδ, coord_conv]
  by_cases h : m = n
  · simp [h]
  · simp only [h, ↓reduceIte]
    simp [act]

omit [AddCommGroup M] in
/-- The coefficient of `e^m` in `δ x` is `p_m x`. -/
theorem proj_eq_coeff (m : M) (x : V) :
    proj δ m x = TensorProduct.equivFinsuppOfBasisRight (eb (k := k) (M := M)) (δ x) m :=
  act_coord _ δ m x

omit [AddCommGroup M] in
/-- _lTf_L0yvrU-28993 (8:03:13) [prop] … for every `x`, only finitely many `p_m x` are non-zero,
and `x = ∑_m p_m x`. -/
theorem proj_finite (x : V) : Set.Finite {m : M | proj δ m x ≠ 0} := by
  refine (TensorProduct.equivFinsuppOfBasisRight (eb (k := k) (M := M)) (δ x)).support.finite_toSet.subset
    fun m hm ↦ ?_
  rw [Set.mem_ofPred_eq, proj_eq_coeff] at hm
  simpa using hm

omit [AddCommGroup M] in
theorem sum_proj (hδ : Part01.IsComodule k (AddMonoidAlgebra k M) V δ) (x : V) :
    (TensorProduct.equivFinsuppOfBasisRight (eb (k := k) (M := M)) (δ x)).support.sum
      (fun m ↦ proj δ m x) = x := by
  conv_rhs => rw [← act_counit hδ x, act_eq_sum (eb (k := k) (M := M))]
  simp only [Finsupp.sum, AddMonoidAlgebra.basis_apply, AddMonoidAlgebra.counit_single,
    CommSemiring.counit_apply, one_smul, proj_eq_coeff]

omit [AddCommGroup M] in
/-- _lTf_L0yvrU-29057 (8:04:17) [thm] One direction: an action of `D(M)` gives a grading
`V = ⊕ V_m` (`V_m` the image of `p_m`): every `x` is uniquely a finite sum of `x_m ∈ V_m`. -/
theorem grading (hδ : Part01.IsComodule k (AddMonoidAlgebra k M) V δ) (x : V) :
    ∃! y : M →₀ V, (∀ m, proj δ m (y m) = y m) ∧ (y.sum fun _ v ↦ v) = x := by
  refine ⟨TensorProduct.equivFinsuppOfBasisRight (eb (k := k) (M := M)) (δ x), ⟨fun m ↦ ?_, ?_⟩, ?_⟩
  · rw [← proj_eq_coeff, proj_proj hδ]; simp
  · rw [Finsupp.sum]
    conv_rhs => rw [← sum_proj hδ x]
    exact Finset.sum_congr rfl fun m _ ↦ (proj_eq_coeff m x).symm
  · rintro y ⟨hy, rfl⟩
    ext n
    rw [← proj_eq_coeff, Finsupp.sum, map_sum]
    rw [Finset.sum_eq_single n]
    · exact (hy n).symm
    · intro m _ hmn
      rw [← hy m, proj_proj hδ]; simp [Ne.symm hmn]
    · intro hn
      rw [Finsupp.notMem_support_iff.mp hn, map_zero]

omit [AddCommGroup M] in
/-- _lTf_L0yvrU-29140 (8:05:40) [prop] On `V_m`, `δ x = x ⊗ e^m`; hence a point `g` of `D(M)`
(an algebra map `k[M] → k'`) acts by the scalar `χ_m(g) = g(e^m)` (`(g ⊗ id)(δ x) = x ⊗ g(e^m)`). -/
theorem delta_of_mem (hδ : Part01.IsComodule k (AddMonoidAlgebra k M) V δ) (m : M) (x : V) :
    δ (proj δ m x) = proj δ m x ⊗ₜ AddMonoidAlgebra.single m 1 := by
  rw [← (TensorProduct.equivFinsuppOfBasisRight (eb (k := k) (M := M))).symm_apply_apply
    (δ (proj δ m x)), TensorProduct.equivFinsuppOfBasisRight_symm_apply]
  have : TensorProduct.equivFinsuppOfBasisRight (eb (k := k) (M := M)) (δ (proj δ m x)) =
      Finsupp.single m (proj δ m x) := by
    ext n
    rw [← proj_eq_coeff, proj_proj hδ, Finsupp.single_apply]
    by_cases h : n = m
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [this, Finsupp.sum_single_index (by simp)]
  rfl

theorem point_acts_by_character (hδ : Part01.IsComodule k (AddMonoidAlgebra k M) V δ) (m : M)
    (x : V) (R : Type u) [CommRing R] [Algebra k R] (g : AddMonoidAlgebra k M →ₐ[k] R) :
    g.toLinearMap.lTensor V (δ (proj δ m x)) = proj δ m x ⊗ₜ g (AddMonoidAlgebra.single m 1) ∧
      IsUnit (g (AddMonoidAlgebra.single m 1)) := by
  refine ⟨by rw [delta_of_mem hδ]; rfl, ?_⟩
  refine ⟨⟨_, g (AddMonoidAlgebra.single (-m) 1), ?_, ?_⟩, rfl⟩ <;>
    rw [← map_mul, AddMonoidAlgebra.single_mul_single, mul_one] <;> simp [← AddMonoidAlgebra.one_def]

omit [DecidableEq M] in
/-- _lTf_L0yvrU-29334 (8:08:54) [prop] The characters add: `χ_m χ_{m'} = χ_{m+m'}`
(`e^m e^{m'} = e^{m+m'}`). -/
theorem character_mul (R : Type u) [CommRing R] [Algebra k R] (g : AddMonoidAlgebra k M →ₐ[k] R)
    (m m' : M) : g (AddMonoidAlgebra.single m 1) * g (AddMonoidAlgebra.single m' 1) =
      g (AddMonoidAlgebra.single (m + m') 1) := by
  rw [← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]

end Grading

/-! ## Constant schemes and biduality -/

section Constant

open CategoryTheory Limits AlgebraicGeometry

/-- _lTf_L0yvrU-29527 (8:12:07) [def] The constant scheme `M_S = ∐_{m ∈ M} S`. -/
noncomputable abbrev constScheme (M : Type u) (S : Scheme.{u}) : Scheme.{u} := ∐ fun _ : M ↦ S

/-- _lTf_L0yvrU-29590 (8:13:10) [prop] One half (Mathlib): for `M` finite and `S` affine, `M_S`
is affine. -/
example (M : Type u) [Finite M] (S : Scheme.{u}) [IsAffine S] : IsAffine (constScheme M S) :=
  inferInstance

/-- _lTf_L0yvrU-29781 (8:16:21) [prop] Morphisms `M_{S'} → X` are the maps `M → Hom(S', X)`. -/
noncomputable def constHomEquiv (M : Type u) (S X : Scheme.{u}) :
    (constScheme M S ⟶ X) ≃ (M → (S ⟶ X)) where
  toFun φ m := Sigma.ι (fun _ : M ↦ S) m ≫ φ
  invFun ψ := Sigma.desc ψ
  left_inv φ := Sigma.hom_ext _ _ fun m ↦ by simp
  right_inv ψ := funext fun m ↦ by simp

variable {k} (M : Type u) [AddCommGroup M] (R : Type u) [CommRing R]

/-- _lTf_L0yvrU-29981 (8:19:41) [prop] The pairing `D(M) × M → 𝔾_m` gives `M → D(D(M))`:
`m ↦ (χ ↦ χ(m))`. -/
def toBidual : Multiplicative M →* (Part01.D M R →* Rˣ) where
  toFun m :=
    { toFun χ := χ m
      map_one' := rfl
      map_mul' _ _ := rfl }
  map_one' := by ext χ; simp
  map_mul' m m' := by ext χ; simp

end Constant

/-! ## Characters of `D(M)`: group-like elements of `R[M]` -/

section GroupLike

variable {k} {M : Type u} [AddCommGroup M] [DecidableEq M]

omit [AddCommGroup M] in
theorem coeff_grouplike {u : AddMonoidAlgebra k M} (hu : IsGroupLikeElem k u) (m n : M) :
    u.coeff m * u.coeff n = if m = n then u.coeff m else 0 := by
  let Φ : AddMonoidAlgebra k M ⊗[k] AddMonoidAlgebra k M →ₗ[k] k :=
    LinearMap.mul' k k ∘ₗ TensorProduct.map ((eb (k := k) (M := M)).coord m)
      ((eb (k := k) (M := M)).coord n)
  have h1 : Φ (u ⊗ₜ u) = u.coeff m * u.coeff n := rfl
  have h2 : Φ ∘ₗ Coalgebra.comul = if m = n then (eb (k := k) (M := M)).coord m else 0 := by
    apply (eb (k := k) (M := M)).ext
    intro j
    rw [LinearMap.comp_apply, AddMonoidAlgebra.basis_apply, AddMonoidAlgebra.comul_single,
      CommSemiring.comul_apply, TensorProduct.map_tmul]
    simp only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
      AddMonoidAlgebra.lsingle_apply, eb_coord_single]
    split_ifs <;> simp_all [eb_repr_single]
  have := LinearMap.congr_fun h2 u
  rw [LinearMap.comp_apply, hu.comul_eq_tmul_self, h1] at this
  rw [this]
  by_cases h : m = n
  · simp only [h, ↓reduceIte]; rfl
  · simp [h]

omit [AddCommGroup M] in
/-- _lTf_L0yvrU-30047 (8:20:47) [thm] (affine `S = Spec R`) A homomorphism `D(M) → 𝔾_m`, i.e. a
group-like element `u = ∑ u_m e^m` of `R[M]`, is a family of pairwise orthogonal idempotents
`u_m` with `∑ u_m = 1`: a partition of `S` into open and closed pieces `S_m`. -/
theorem grouplike_partition {u : AddMonoidAlgebra k M} (hu : IsGroupLikeElem k u) :
    (∀ m, IsIdempotentElem (u.coeff m)) ∧ (∀ m n, m ≠ n → u.coeff m * u.coeff n = 0) ∧
      (u.coeff.sum fun _ c ↦ c) = 1 := by
  refine ⟨fun m ↦ by
    have := coeff_grouplike hu m m
    simp only [↓reduceIte] at this
    exact this, fun m n h ↦ by
    simpa [h] using coeff_grouplike hu m n, ?_⟩
  have := hu.counit_eq_one
  conv_lhs at this => rw [← (eb (k := k) (M := M)).linearCombination_repr u]
  rw [Finsupp.linearCombination_apply, map_finsuppSum] at this
  simp only [map_smul, AddMonoidAlgebra.basis_apply, AddMonoidAlgebra.counit_single,
    CommSemiring.counit_apply, smul_eq_mul, mul_one] at this
  exact this

omit [AddCommGroup M] in
/-- _lTf_L0yvrU-30047 (8:20:47) [prop] If `S = Spec R` is connected and non-empty (no idempotents
but `0, 1`), every homomorphism `D(M) → 𝔾_m` comes from a unique `m ∈ M`: the group-like elements
of `R[M]` are the `e^m`. -/
theorem grouplike_connected [Nontrivial k] (hk : ∀ e : k, IsIdempotentElem e → e = 0 ∨ e = 1)
    {u : AddMonoidAlgebra k M} (hu : IsGroupLikeElem k u) :
    ∃! m : M, u = AddMonoidAlgebra.single m 1 := by
  obtain ⟨hidem, horth, hsum⟩ := grouplike_partition hu
  have hne : u.coeff ≠ 0 := by
    intro h; rw [h, Finsupp.sum_zero_index] at hsum; exact zero_ne_one hsum
  obtain ⟨m, hm⟩ := Finsupp.ne_iff.mp hne
  have hm1 : u.coeff m = 1 := (hk _ (hidem m)).resolve_left hm
  have hother : ∀ n, n ≠ m → u.coeff n = 0 := fun n hn ↦ by
    have := horth n m hn
    rwa [hm1, mul_one] at this
  have hu' : u.coeff = Finsupp.single m 1 := by
    ext n
    rw [Finsupp.single_apply]
    split_ifs with h'
    · subst h'; exact hm1
    · exact hother n (Ne.symm h')
  refine ⟨m, ?_, fun n hn ↦ ?_⟩
  · ext n; rw [hu']; rfl
  · by_contra h
    have := congrArg (fun v : AddMonoidAlgebra k M ↦ v.coeff m) hn
    simp only [hm1] at this
    have h' : (AddMonoidAlgebra.single n (1 : k)).coeff m = 0 := by
      rw [← eb_coord_apply, eb_coord_single]; simp [h]
    rw [h'] at this
    exact one_ne_zero this

/-- _lTf_L0yvrU-30490 (8:28:10) [thm] Over a domain (Mathlib `mapDomainBialgHomAddEquiv`),
`D` is fully faithful: bialgebra maps `R[N] → R[M]` are the homomorphisms `N → M`. -/
noncomputable def D_fullyFaithful (R : Type u) [CommRing R] [IsDomain R] (N : Type u)
    [AddCommGroup N] : (N →+ M) ≃+ Additive (WithConv (AddMonoidAlgebra R N →ₐc[R] AddMonoidAlgebra R M)) :=
  AddMonoidAlgebra.mapDomainBialgHomAddEquiv

end GroupLike

/-! ## Finite locally free schemes and Cartier duality -/

section Cartier

variable {k}

/-- _lTf_L0yvrU-30944 (8:35:44) [prop] (affine base) A finite module is locally free of finite
type (projective) iff it is flat and finitely presented. -/
theorem projective_iff_flat_fp (A : Type u) [AddCommGroup A] [Module k A] [Module.Finite k A] :
    Module.Projective k A ↔ Module.Flat k A ∧ Module.FinitePresentation k A := by
  refine ⟨fun _ ↦ ⟨inferInstance, Module.finitePresentation_of_projective k A⟩, ?_⟩
  rintro ⟨_, _⟩
  exact Part01.projective_of_flat_fp k A

/-- _lTf_L0yvrU-31206 (8:40:06) [prop] For a group `G`, a monoid homomorphism `G → (k', ×)` takes
values in the units: it is a homomorphism `G → 𝔾_m(k')`. -/
def homToUnits {G R : Type*} [Group G] [Monoid R] (f : G →* R) : G →* Rˣ := f.toHomUnits

theorem homToUnits_val {G R : Type*} [Group G] [Monoid R] (f : G →* R) (g : G) :
    (homToUnits f g : R) = f g := rfl

variable {A : Type u} [CommRing A] [Bialgebra k A]

/-- _lTf_L0yvrU-31461 (8:44:21) [prop] A monoid homomorphism `G → (𝔸¹, ×)` is a bialgebra map
`k[ℕ] → A` (`t ↦ u`); its section `u` satisfies `ε(u) = 1` and `π(u) = u ⊗ u`. -/
theorem section_grouplike (f : AddMonoidAlgebra k ℕ →ₐc[k] A) :
    IsGroupLikeElem k (f (AddMonoidAlgebra.single 1 1)) :=
  (AddMonoidAlgebra.isGroupLikeElem_single_one 1).map f

/-- `ev_u : H = A^∨ → k`, `s ↦ s(u)`. -/
noncomputable def evAt (u : A) : WithConv (A →ₗ[k] k) →ₗ[k] k where
  toFun s := s.ofConv u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- _lTf_L0yvrU-31598 (8:46:38) [prop] If `ε(u) = 1` and `π(u) = u ⊗ u`, `s ↦ s(u)` is an algebra
morphism `H = A^∨ → k` (the product of `H` transposed from `π`) … -/
@[simp] theorem evAt_apply (u : A) (s : WithConv (A →ₗ[k] k)) : evAt u s = s.ofConv u := rfl

theorem evAt_mul {u : A} (hu : IsGroupLikeElem k u) (s t : WithConv (A →ₗ[k] k)) :
    evAt u (s * t) = evAt u s * evAt u t := by
  rw [evAt_apply, evAt_apply, evAt_apply, LinearMap.convMul_apply, hu.comul_eq_tmul_self]
  simp

theorem evAt_one {u : A} (hu : IsGroupLikeElem k u) : evAt u (1 : WithConv (A →ₗ[k] k)) = 1 := by
  rw [evAt_apply, LinearMap.convOne_apply, hu.counit_eq_one]
  simp

/-- … and conversely, for `A` projective (locally free), multiplicativity of `s ↦ s(u)` forces
`π(u) = u ⊗ u` (linear forms separate `A ⊗ A`). -/
theorem grouplike_of_evAt [Module.Projective k A] {u : A}
    (hmul : ∀ s t : WithConv (A →ₗ[k] k), evAt u (s * t) = evAt u s * evAt u t)
    (hone : evAt u (1 : WithConv (A →ₗ[k] k)) = 1) : IsGroupLikeElem k u := by
  refine ⟨by simpa [LinearMap.convOne_apply] using hone, ?_⟩
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_form
  intro t
  rw [← Module.forall_dual_apply_eq_zero_iff k]
  intro s
  have := hmul (toConv s) (toConv t)
  simp only [evAt_apply, LinearMap.convMul_apply] at this
  rw [map_sub, map_sub, map_sub]
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_smul, smul_eq_mul]
  rw [sub_eq_zero]
  have key : ∀ z : A ⊗[k] A, s (TensorProduct.rid k A (t.lTensor A z)) =
      LinearMap.mul' k k (TensorProduct.map s t z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [mul_comm]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [key, this, mul_comm]

/-- _lTf_L0yvrU-31792 (8:49:52) [prop] For any (non-commutative) algebra `H`, the algebra maps
`H → k'` to commutative algebras factor uniquely through `H^ab = H/[H, H]` (Mathlib
`RingQuot.liftAlgHom`): `D(G) = Spec H^ab`. -/
noncomputable def abelianizationEquiv (H : Type u) [Ring H] [Algebra k H] (R : Type u) [CommRing R]
    [Algebra k R] :
    (H →ₐ[k] R) ≃ (RingQuot (fun x y : H ↦ ∃ a b, x = a * b ∧ y = b * a) →ₐ[k] R) :=
  { toFun f := RingQuot.liftAlgHom k ⟨f, fun x y ⟨a, b, hx, hy⟩ ↦ by rw [hx, hy, map_mul, map_mul,
        mul_comm]⟩
    invFun F := F.comp (RingQuot.mkAlgHom k _)
    left_inv f := by ext; simp
    right_inv F := by
      apply RingQuot.ringQuot_ext' k
      ext; simp }

/-- _lTf_L0yvrU-31988 (8:53:08) [prop] The duality of locally free modules: `A ≃ A^{∨∨}` for `A`
finitely generated projective (Mathlib `Module.evalEquiv`), the module-level biduality behind
`D(D(G)) = G`. -/
noncomputable def biduality (P : Type u) [AddCommGroup P] [Module k P] [Module.Projective k P]
    [Module.Finite k P] : P ≃ₗ[k] Module.Dual k (Module.Dual k P) :=
  Module.evalEquiv k P

end Cartier

/-! ## `μ_n` and its dual -/

section Mu

open Polynomial

/-- _lTf_L0yvrU-32051 (8:54:11) [ex] `μ_n = D(ℤ/n)` on points: `φ ↦ φ(1)` maps `Hom(ℤ/n, R^×)`
injectively into `μ_n(R)`… -/
theorem D_zmod_to_mu (n : ℕ) (R : Type*) [CommRing R] (φ : Multiplicative (ZMod n) →* Rˣ) :
    φ (Multiplicative.ofAdd 1) ∈ rootsOfUnity n R := by
  rw [mem_rootsOfUnity, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self,
    ofAdd_zero, map_one]

theorem D_zmod_injective (n : ℕ) (R : Type*) [CommRing R] :
    Function.Injective fun φ : Multiplicative (ZMod n) →* Rˣ ↦ φ (Multiplicative.ofAdd 1) := by
  intro φ ψ h
  refine MonoidHom.ext fun x ↦ ?_
  have hx : x = Multiplicative.ofAdd 1 ^ (x.toAdd.cast : ℤ) := by
    rw [← ofAdd_zsmul, zsmul_one, ZMod.intCast_zmod_cast]; rfl
  simp only at h
  rw [hx, map_zpow, map_zpow, h]

/-- … onto: a root of unity `ζ` (`ζ^n = 1`) is `φ(1)` for `φ = (a ↦ ζ^a)`. -/
theorem D_zmod_surjective (n : ℕ) (R : Type*) [CommRing R] (ζ : rootsOfUnity n R) :
    ∃ φ : Multiplicative (ZMod n) →* Rˣ, φ (Multiplicative.ofAdd 1) = ζ := by
  let f : ℤ →+ Additive Rˣ := zmultiplesHom (Additive Rˣ) (Additive.ofMul (ζ : Rˣ))
  have hf : f n = 0 := by
    simp only [f, zmultiplesHom_apply, natCast_zsmul]
    rw [← ofMul_pow, (mem_rootsOfUnity n (ζ : Rˣ)).mp ζ.2, ofMul_one]
  refine ⟨AddMonoidHom.toMultiplicativeLeft (ZMod.lift n ⟨f, hf⟩), ?_⟩
  simp only [AddMonoidHom.toMultiplicativeLeft_apply_apply, toAdd_ofAdd]
  have : (1 : ZMod n) = ((1 : ℤ) : ZMod n) := by simp
  rw [this, ZMod.lift_coe]
  simp [f]

/-- _lTf_L0yvrU-32051 (8:54:11) [ex] Over `Spec ℤ`, `μ_n` (`n > 1`) is not constant: for a prime
`p ∣ n` its fibre `𝔽_p[t]/(tⁿ - 1)` is not reduced (`(t^{n/p} - 1)^p = 0`), while constant
schemes have reduced fibres. -/
theorem mu_fibre_not_reduced (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 0 < n) (hpn : p ∣ n) :
    ¬ IsReduced (AdjoinRoot (X ^ n - 1 : (ZMod p)[X])) := by
  intro hred
  obtain ⟨m, rfl⟩ := hpn
  have hm : 0 < m := Nat.pos_of_mul_pos_left hn
  set y : AdjoinRoot (X ^ (p * m) - 1 : (ZMod p)[X]) := AdjoinRoot.root _ ^ m - 1
  have hy : y ^ p = 0 := by
    have : CharP (AdjoinRoot (X ^ (p * m) - 1 : (ZMod p)[X])) p :=
      charP_of_injective_algebraMap (AdjoinRoot.of.injective_of_degree_ne_zero ?_) p
    · simp only [y]
      rw [sub_pow_char, one_pow, ← pow_mul, mul_comm m p, ← AdjoinRoot.mk_X, ← map_pow,
        ← map_one (AdjoinRoot.mk _), ← map_sub, AdjoinRoot.mk_self]
    · rw [show (1 : (ZMod p)[X]) = C 1 from C_1.symm, degree_X_pow_sub_C (by positivity)]
      exact_mod_cast (Nat.mul_pos hp.out.pos hm).ne'
  have hy0 : y ≠ 0 := by
    simp only [y]
    rw [← AdjoinRoot.mk_X, ← map_pow, ← map_one (AdjoinRoot.mk _), ← map_sub, ne_eq,
      AdjoinRoot.mk_eq_zero]
    intro hdvd
    have hne : (X ^ m - 1 : (ZMod p)[X]) ≠ 0 := X_pow_sub_C_ne_zero hm 1
    have hdeg := Polynomial.natDegree_le_of_dvd hdvd hne
    rw [show (1 : (ZMod p)[X]) = C 1 by simp, natDegree_X_pow_sub_C, natDegree_X_pow_sub_C] at hdeg
    nlinarith [hp.out.two_le]
  exact hy0 (IsReduced.eq_zero y ⟨p, hy⟩)

end Mu

end Buffalo.Groupes.Part02
