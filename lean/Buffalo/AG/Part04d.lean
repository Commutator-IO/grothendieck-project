import Buffalo.AG.Part04c

/-!
# Buffalo, algebraic geometry, part 04 (d): 18 June 1973, gluing, projective space

The entries of `docs/buffalo-ag/index.tex` lines 612–631 (video `thSz9ZHDK9o`, 6:01:54–6:59:05):
gluing schemes, lines and hyperplanes of a vector space, invertible modules and the functor
`𝐏(V)` of invertible quotients, its charts `𝐏_e` and their representing algebras.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry TensorProduct Module

universe u

namespace Buffalo.AG.Part04

noncomputable section

/-! ### Gluing schemes -/

/-- thSz9ZHDK9o-21714 (6:01:54) [prop] Schemes `X_i`, opens `X_{ij} ⊂ X_i` and isomorphisms
`X_{ij} ≅ X_{ji}` satisfying the cocycle condition (mathlib's `Scheme.GlueData`) glue to a
scheme `X` covered by the `X_i`, through open immersions. -/
theorem prop_21714 (D : Scheme.GlueData.{u}) :
    (∀ i, IsOpenImmersion (D.ι i)) ∧ ∀ x : D.glued, ∃ i y, (D.ι i).base y = x :=
  ⟨fun _ => inferInstance, fun x => D.ι_jointly_surjective x⟩

example (D : Scheme.GlueData.{u}) : D.glued.OpenCover := D.openCover

/-! ### Projective space: lines and hyperplanes -/

/-- thSz9ZHDK9o-22643 (6:17:23) [rem] Two nonzero vectors span the same line iff they differ by
a scalar in `k^×`: the set of lines is `(V ∖ {0}) / k^×`. -/
theorem rem_22643 {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (v w : V) :
    (k ∙ v) = (k ∙ w) ↔ ∃ c : kˣ, c • v = w :=
  Submodule.span_singleton_eq_span_singleton

/-- thSz9ZHDK9o-22770 (6:19:30) [prop] In a basis, every line `k v` has some coordinate
`x_i ≠ 0`, and if `x_i(v) ≠ 0` it has a unique point with `x_i = 1`: the line is determined by
the other `n - 1` coordinates of that point. -/
theorem prop_22770 {k : Type*} [Field k] {n : Type*} (v : n → k) (hv : v ≠ 0) :
    (∃ i, v i ≠ 0) ∧ ∀ i, v i ≠ 0 → ∃! w : n → k, w ∈ (k ∙ v) ∧ w i = 1 := by
  refine ⟨by by_contra h; push Not at h; exact hv (funext h), fun i hi => ?_⟩
  refine ⟨(v i)⁻¹ • v, ⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v),
    by simp [hi]⟩, fun w ⟨hw, hwi⟩ => ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  have hc : c = (v i)⁻¹ := by
    simp only [Pi.smul_apply, smul_eq_mul] at hwi
    exact eq_inv_of_mul_eq_one_left hwi
  rw [hc]

/-- thSz9ZHDK9o-22963 (6:22:43) [ex] For `n = 2`, a line `[x : y]` with `x, y ≠ 0` has the two
coordinates `y/x` and `x/y`, independent of the representative and inverse to each other: the
projective line is two copies of `k` glued along `k^×` by `λ ↦ λ⁻¹`. -/
theorem ex_22963 {k : Type*} [Field k] (x y : k) (c : k) (hc : c ≠ 0) :
    y / x = (x / y)⁻¹ ∧ (c * y) / (c * x) = y / x ∧ (c * x) / (c * y) = x / y := by
  refine ⟨(inv_div x y).symm, ?_, ?_⟩ <;> rw [mul_div_mul_left _ _ hc]

/-- thSz9ZHDK9o-23316 (6:28:36) [prop] For `V` finite-dimensional, `W ↦ W^⊥` is an
order-reversing bijection between subspaces of `V` and of `V^∨` with
`dim W + dim W^⊥ = dim V` (so lines of `V` ↔ hyperplanes of `V^∨`); and the hyperplanes `H` of
`V` are the kernels of the `1`-dimensional quotients, `dim V/H = 1 ↔ dim H + 1 = dim V`. -/
theorem prop_23316 {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    Function.Bijective (fun W : Subspace k V => W.dualAnnihilator) ∧
      (∀ W : Subspace k V, finrank k W + finrank k W.dualAnnihilator = finrank k V) ∧
      ∀ H : Subspace k V, finrank k (V ⧸ H) = 1 ↔ finrank k H + 1 = finrank k V := by
  refine ⟨(Subspace.orderIsoFiniteDimensional (K := k) (V := V)).bijective, fun W =>
    Subspace.finrank_add_finrank_dualAnnihilator_eq W, fun H => ?_⟩
  have := Submodule.finrank_quotient_add_finrank H
  omega

/-- thSz9ZHDK9o-23380 (6:29:40) [def] `𝐏(V)` denotes the set of hyperplanes of `V`, i.e. of
`1`-dimensional quotients of `V` (not the set of lines, mathlib's `Projectivization`). -/
def PHyp (k V : Type*) [Field k] [AddCommGroup V] [Module k V] : Type _ :=
  {H : Subspace k V // finrank k (V ⧸ H) = 1}

/-! ### Invertible modules -/

/-- The parity character `ℤ[√-5] → 𝔽₂`, `a + b√-5 ↦ a + b`. -/
def chi5 : ℤ√(-5) →+* ZMod 2 := Zsqrtd.lift ⟨1, by decide⟩

theorem chi5_apply (x : ℤ√(-5)) : chi5 x = (x.re : ZMod 2) + (x.im : ZMod 2) := by
  simp [chi5]

/-- thSz9ZHDK9o-23642 (6:34:02) [cex] Being free of rank `1` is not local: the ideal
`L = (2, 1 + √-5)` of `ℤ[√-5]` is not principal, i.e. not free of rank `1`. Partial: that `L` is
nevertheless locally free of rank `1` (it is invertible, `L² = (2)`, hence Zariski-locally free by
`def_23770`) is not formalised. -/
theorem cex_23642 :
    ¬ (Ideal.span {(2 : ℤ√(-5)), 1 + Zsqrtd.sqrtd} : Ideal (ℤ√(-5))).IsPrincipal := by
  rintro ⟨α, hα⟩
  have hle : Ideal.span {(2 : ℤ√(-5)), 1 + Zsqrtd.sqrtd} ≤ RingHom.ker chi5 := by
    rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · simp only [SetLike.mem_coe, RingHom.mem_ker, map_ofNat]; rfl
    · simp only [SetLike.mem_coe, RingHom.mem_ker, chi5_apply]; decide
  have hαmem : α ∈ Ideal.span {(2 : ℤ√(-5)), 1 + Zsqrtd.sqrtd} := by
    rw [hα]; exact Submodule.mem_span_singleton_self α
  have hpar := hle hαmem
  rw [RingHom.mem_ker, chi5_apply] at hpar
  have h2 : (2 : ℤ√(-5)) ∈ Submodule.span (ℤ√(-5)) {α} := by
    rw [← hα]; exact Ideal.subset_span (Set.mem_insert _ _)
  have h6 : (1 + Zsqrtd.sqrtd : ℤ√(-5)) ∈ Submodule.span (ℤ√(-5)) {α} := by
    rw [← hα]; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.1 h2
  obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.1 h6
  have n2 := congrArg Zsqrtd.norm hβ
  have n6 := congrArg Zsqrtd.norm hγ
  rw [smul_eq_mul, Zsqrtd.norm_mul] at n2 n6
  simp only [Zsqrtd.norm_def] at n2 n6
  norm_num at n2 n6
  have hN : α.re * α.re + 5 * α.im * α.im ∣ 2 := by
    have d4 : α.re * α.re + 5 * α.im * α.im ∣ 4 := Dvd.intro_left _ n2
    have d6 : α.re * α.re + 5 * α.im * α.im ∣ 6 := Dvd.intro_left _ n6
    have := Int.dvd_sub d6 d4
    norm_num at this
    exact this
  have hpos : 0 < α.re * α.re + 5 * α.im * α.im := by
    have hnn : 0 ≤ α.re * α.re + 5 * α.im * α.im := by
      nlinarith [mul_self_nonneg α.re, mul_self_nonneg α.im]
    rcases hnn.lt_or_eq with h | h
    · exact h
    · rw [← h] at n2; norm_num at n2
  have hle2 := Int.le_of_dvd (by norm_num) hN
  have him : α.im = 0 := by nlinarith
  have hre : α.re * α.re ≤ 2 := by rw [him] at hle2; linarith
  have hre' : α.re = 0 ∨ α.re = 1 ∨ α.re = -1 := by
    have : -1 ≤ α.re ∧ α.re ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    omega
  rw [him] at hpar
  rcases hre' with h | h | h <;> rw [h] at hpar hpos <;> simp_all

/-- thSz9ZHDK9o-23770 (6:36:10) [def] An `A`-module `L` is invertible (mathlib's
`Module.Invertible`, `L^∨ ⊗ L ≅ A`); it is then Zariski-locally free of rank `1`: there are
`f_α` generating the unit ideal with `L_{f_α}` free over `A_{f_α}`. -/
theorem def_23770 (A L : Type u) [CommRing A] [AddCommGroup L] [Module A L]
    [Module.Invertible A L] :
    ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ r ∈ s, Module.Free (Localization.Away r) (LocalizedModule.Away r L) :=
  Module.Invertible.exists_finset_free_localization A L

/-- thSz9ZHDK9o-23835 (6:37:15) [prop] `L` is invertible iff there is `M` with `M ⊗ L ≅ A`;
`L^{-1} = Hom_A(L, A)` is such an `M` and is invertible too. -/
theorem prop_23835 (A L : Type u) [CommRing A] [AddCommGroup L] [Module A L] :
    (Module.Invertible A L ↔ ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module A M),
      Nonempty (M ⊗[A] L ≃ₗ[A] A)) ∧
    (Module.Invertible A L → Module.Invertible A (Dual A L)) := by
  refine ⟨⟨fun _ => ⟨Dual A L, inferInstance, inferInstance,
    ⟨Module.Invertible.linearEquiv A L⟩⟩, fun ⟨M, _, _, ⟨e⟩⟩ => Module.Invertible.right e⟩,
    fun _ => inferInstance⟩

/-- thSz9ZHDK9o-23835 (corrected) `M` with `M ⊗ L ≃ A` is unique up to a unique isomorphism
*compatible with the given isomorphisms* `M ⊗ L ≃ A`, `M' ⊗ L ≃ A`. -/
theorem prop_23835_unique {A L M M' : Type u} [CommRing A] [AddCommGroup L] [Module A L]
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (e : M ⊗[A] L ≃ₗ[A] A) (e' : M' ⊗[A] L ≃ₗ[A] A) :
    ∃! φ : M →ₗ[A] M', e'.toLinearMap ∘ₗ φ.rTensor L = e.toLinearMap := by
  let E := Module.Invertible.rTensorEquiv M M' (TensorProduct.comm A L M ≪≫ₗ e)
  have hE : ∀ φ : M →ₗ[A] M', E φ = φ.rTensor L := fun _ => rfl
  refine ⟨E.symm (e'.symm.toLinearMap ∘ₗ e.toLinearMap), ?_, fun φ hφ => ?_⟩
  · have h := E.apply_symm_apply (e'.symm.toLinearMap ∘ₗ e.toLinearMap)
    rw [hE] at h
    change e'.toLinearMap ∘ₗ (E.symm (e'.symm.toLinearMap ∘ₗ e.toLinearMap)).rTensor L = _
    rw [h, ← LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.id_comp]
  · apply E.injective
    rw [E.apply_symm_apply, hE, ← hφ, ← LinearMap.comp_assoc, LinearEquiv.symm_comp,
      LinearMap.id_comp]

/-- thSz9ZHDK9o-23835 [the error] Without that compatibility the isomorphism is not unique: `ℚ`
has two distinct automorphisms as a `ℚ`-module (`M = L = A = ℚ`), `id` and `2 ·`. -/
theorem prop_23835_not_unique :
    LinearEquiv.refl ℚ ℚ ≠ LinearEquiv.smulOfUnit (Units.mk0 (2 : ℚ) two_ne_zero) := by
  intro h
  have := congrArg (fun e : ℚ ≃ₗ[ℚ] ℚ => e 1) h
  norm_num [LinearEquiv.smulOfUnit] at this

/-- thSz9ZHDK9o-23907 (6:38:27) [prop] An invertible module is finitely generated projective and
`L_𝔭` is free of rank `1` for every prime `𝔭`. Partial: this direction; the converse is a TODO
of mathlib. -/
theorem prop_23907 (A L : Type u) [CommRing A] [AddCommGroup L] [Module A L]
    [Module.Invertible A L] (p : Ideal A) [p.IsPrime] :
    Module.Finite A L ∧ Projective A L ∧
      Nonempty (LocalizedModule p.primeCompl L ≃ₗ[Localization.AtPrime p]
        Localization.AtPrime p) := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl L) := inferInstance
  exact (Module.Invertible.free_iff_linearEquiv).1 this

/-- thSz9ZHDK9o-24039 (6:40:39) [prop] The kernel of an invertible (indeed of any projective)
quotient `V → L` is a direct summand. Partial: the rank count `n - 1` at every prime is not
formalised. -/
theorem prop_24039 {A V L : Type u} [CommRing A] [AddCommGroup V] [Module A V] [AddCommGroup L]
    [Module A L] [Module.Invertible A L] (q : V →ₗ[A] L) (hq : Function.Surjective q) :
    ∃ K : Submodule A V, IsCompl (LinearMap.ker q) K := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q LinearMap.id hq
  have hqs : ∀ y, q (s y) = y := fun y => LinearMap.congr_fun hs y
  refine ⟨LinearMap.range s, ⟨Submodule.disjoint_def.2 fun x hx hx' => ?_,
    codisjoint_iff.2 (Submodule.eq_top_iff'.2 fun x => Submodule.mem_sup.2
      ⟨x - s (q x), by simp [hqs], s (q x), ⟨q x, rfl⟩, by abel⟩)⟩⟩
  obtain ⟨y, hy⟩ := hx'
  rw [LinearMap.mem_ker, ← hy, hqs] at hx
  rw [← hy, hx, map_zero]

/-! ### The functor `𝐏(V)` of invertible quotients -/

/-- thSz9ZHDK9o-24104 (6:41:44) [prop] If `L` is an invertible quotient of `V_{k'}` and
`k' → k''`, then `L ⊗_{k'} k''` is an invertible quotient of `V_{k''} = V_{k'} ⊗_{k'} k''`. -/
theorem prop_24104 {k' k'' W L : Type u} [CommRing k'] [CommRing k''] [Algebra k' k'']
    [AddCommGroup W] [Module k' W] [AddCommGroup L] [Module k' L] [Module.Invertible k' L]
    (q : W →ₗ[k'] L) (hq : Function.Surjective q) :
    Function.Surjective (q.baseChange k'') ∧ Module.Invertible k'' (k'' ⊗[k'] L) :=
  ⟨LinearMap.lTensor_surjective k'' hq, inferInstance⟩

/-- thSz9ZHDK9o-24168 (6:42:48) [def] For a `k`-module `V`, `𝐏(V)(k')` is the set of invertible
quotients of `V ⊗_k k'`, i.e. of submodules `K` of `k' ⊗_k V` with invertible quotient
(functoriality: `prop_24104`). -/
def PV (k V k' : Type u) [CommRing k] [AddCommGroup V] [Module k V] [CommRing k']
    [Algebra k k'] : Set (Submodule k' (k' ⊗[k] V)) :=
  {K | Module.Invertible k' ((k' ⊗[k] V) ⧸ K)}

/-- thSz9ZHDK9o-24619 (6:50:19) [prop] `𝐏_e(k')`: the quotients `L` of `V_{k'}` in which the image
of `e` is a basis; this is stable under base change, so `𝐏_e` is a subfunctor of `𝐏(V)`. -/
theorem prop_24619 {k' k'' L : Type u} [CommRing k'] [CommRing k''] [Algebra k' k'']
    [AddCommGroup L] [Module k' L] (b : Basis (Fin 1) k' L) :
    ∃ b' : Basis (Fin 1) k'' (k'' ⊗[k'] L), ∀ i, b' i = 1 ⊗ₜ b i :=
  ⟨b.baseChange k'', fun i => Basis.baseChange_apply k'' b i⟩

/-- thSz9ZHDK9o-24821 (6:53:41) [prop] The locus where a section `s` of a finitely generated
module `L` generates it, `{𝔭 | (L / A s)_𝔭 = 0}`, is open (the complement of the support of
`L / A s`). Partial: that, `L` being invertible, generating at `𝔭` means being a basis of `L_𝔭`,
and the resulting open immersion `𝐏_e → 𝐏(V)` of sheaves, are not formalised. -/
theorem prop_24821 {A L : Type u} [CommRing A] [AddCommGroup L] [Module A L] [Module.Finite A L]
    (s : L) :
    IsOpen {p : PrimeSpectrum A |
      Subsingleton (LocalizedModule p.asIdeal.primeCompl (L ⧸ Submodule.span A {s}))} := by
  have : {p : PrimeSpectrum A |
      Subsingleton (LocalizedModule p.asIdeal.primeCompl (L ⧸ Submodule.span A {s}))} =
      (Module.support A (L ⧸ Submodule.span A {s}))ᶜ := by
    ext p
    simp [Module.notMem_support_iff]
  rw [this, Module.support_eq_zeroLocus]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

/-- thSz9ZHDK9o-25011 (6:56:51) [prop] If the `e_i` generate `V`, the `𝐏_{e_i}` cover `𝐏(V)`:
at a point, `L` is free of rank `1` over a local ring and one of the images of the `e_i` is a
basis. Partial: the local statement (one of the generators is a unit of `L ≅ A`). -/
theorem prop_25011 {A L ι : Type u} [CommRing A] [IsLocalRing A] [AddCommGroup L] [Module A L]
    (e : L ≃ₗ[A] A) (x : ι → L) (hx : Submodule.span A (Set.range x) = ⊤) :
    ∃ i, IsUnit (e (x i)) := by
  by_contra h
  push Not at h
  have hle : Submodule.span A (Set.range x) ≤ Submodule.comap e.toLinearMap (IsLocalRing.maximalIdeal A) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  rw [hx] at hle
  have : e.symm 1 ∈ Submodule.comap e.toLinearMap (IsLocalRing.maximalIdeal A) := hle trivial
  simp at this

/-- thSz9ZHDK9o-25080 (6:58:00) [prop] `𝐏_e` is represented by `Sym(V)/(e - 1)`: a point with
values in `k'` is a linear map `V → k'` (equivalently `V_{k'} → k'`) sending `e` to `1`. -/
def prop_25080 (k V k' : Type u) [CommRing k] [AddCommGroup V] [Module k V] [CommRing k']
    [Algebra k k'] (e : V) :
    (SymmetricAlgebra k V ⧸ Ideal.span {SymmetricAlgebra.ι k V e - 1} →ₐ[k] k') ≃
      {φ : V →ₗ[k] k' // φ e = 1} where
  toFun g := ⟨(g.comp (Ideal.Quotient.mkₐ k _)).toLinearMap ∘ₗ SymmetricAlgebra.ι k V, by
    have h : Ideal.Quotient.mk (Ideal.span {SymmetricAlgebra.ι k V e - 1})
        (SymmetricAlgebra.ι k V e) = 1 := by
      rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact Ideal.subset_span rfl
    change g (Ideal.Quotient.mk _ (SymmetricAlgebra.ι k V e)) = 1
    rw [h, map_one]⟩
  invFun φ := Ideal.Quotient.liftₐ _ (SymmetricAlgebra.lift φ.1) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_sub, SymmetricAlgebra.lift_ι_apply, φ.2, map_one, sub_self, mul_zero])
  left_inv g := by
    apply Ideal.Quotient.algHom_ext
    apply SymmetricAlgebra.algHom_ext
    ext v
    exact SymmetricAlgebra.lift_ι_apply _ v
  right_inv φ := by
    ext v
    exact SymmetricAlgebra.lift_ι_apply _ v

/-- `T_i ↦ 1`, `T_j ↦ T_j` (`j ≠ i`). -/
def quotPhi (k I : Type u) [CommRing k] [DecidableEq I] (i : I) :
    MvPolynomial I k →ₐ[k] MvPolynomial {j // j ≠ i} k :=
  MvPolynomial.aeval fun j => if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩

theorem quotPhi_X_self (k I : Type u) [CommRing k] [DecidableEq I] (i : I) :
    quotPhi k I i (MvPolynomial.X i) = 1 := by
  simp [quotPhi]

theorem quotPhi_X_ne (k I : Type u) [CommRing k] [DecidableEq I] {i j : I} (h : j ≠ i) :
    quotPhi k I i (MvPolynomial.X j) = MvPolynomial.X ⟨j, h⟩ := by
  simp [quotPhi, h]

theorem quotPhi_ker (k I : Type u) [CommRing k] [DecidableEq I] (i : I) :
    ∀ a ∈ Ideal.span {(MvPolynomial.X i - 1 : MvPolynomial I k)}, quotPhi k I i a = 0 := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [map_mul, map_sub, quotPhi_X_self, map_one, sub_self, mul_zero]

theorem quotLift_mk (k I : Type u) [CommRing k] [DecidableEq I] (i : I) (a : MvPolynomial I k) :
    Ideal.Quotient.liftₐ _ (quotPhi k I i) (quotPhi_ker k I i) (Ideal.Quotient.mk _ a) =
      quotPhi k I i a := rfl

theorem mk_X_self (k I : Type u) [CommRing k] (i : I) :
    Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X i - 1 : MvPolynomial I k)}) 1 =
      Ideal.Quotient.mk _ (MvPolynomial.X i) := by
  rw [Ideal.Quotient.eq]
  have : (1 - MvPolynomial.X i : MvPolynomial I k) = -1 * (MvPolynomial.X i - 1) := by ring
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- `k[T_j, j ∈ I] / (T_i - 1) ≃ k[T_j, j ≠ i]`. -/
def quotXsubOne (k I : Type u) [CommRing k] [DecidableEq I] (i : I) :
    (MvPolynomial I k ⧸ Ideal.span {(MvPolynomial.X i - 1 : MvPolynomial I k)}) ≃ₐ[k]
      MvPolynomial {j // j ≠ i} k :=
  AlgEquiv.ofAlgHom (Ideal.Quotient.liftₐ _ (quotPhi k I i) (quotPhi_ker k I i))
    ((Ideal.Quotient.mkₐ k _).comp (MvPolynomial.rename Subtype.val))
    (MvPolynomial.algHom_ext fun j => by
      simp only [AlgHom.comp_apply, MvPolynomial.rename_X, Ideal.Quotient.mkₐ_eq_mk,
        quotLift_mk, quotPhi_X_ne k I j.2, AlgHom.id_apply])
    (Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun j => by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, quotLift_mk, AlgHom.id_apply]
      by_cases h : j = i
      · subst h
        rw [quotPhi_X_self, map_one]
        exact mk_X_self k I j
      · rw [quotPhi_X_ne k I h, MvPolynomial.rename_X]))

/-- thSz9ZHDK9o-25145 (6:59:05) [ex] If `(e_i)` is a basis of `V`, `Sym(V)/(e_i - 1)` is the
polynomial ring in the `T_j`, `j ≠ i`: `𝐏_{e_i}` is the affine space of dimension `|I| - 1`. -/
def ex_25145 (k V I : Type u) [CommRing k] [AddCommGroup V] [Module k V] [DecidableEq I]
    (b : Basis I k V) (i : I) :
    (SymmetricAlgebra k V ⧸ Ideal.span {SymmetricAlgebra.ι k V (b i) - 1}) ≃ₐ[k]
      MvPolynomial {j // j ≠ i} k :=
  (Ideal.quotientEquivAlg _ _ (SymmetricAlgebra.equivMvPolynomial b) (by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]
    erw [SymmetricAlgebra.equivMvPolynomial_ι_apply])).trans (quotXsubOne k I i)

end

end Buffalo.AG.Part04
