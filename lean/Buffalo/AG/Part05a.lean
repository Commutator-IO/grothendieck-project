import Buffalo.AG.Part02a

/-!
# Buffalo, algebraic geometry, part 05 (a): (undated session, from 7:04:25) – 19 June 1973

The entries of `docs/buffalo-ag/index.tex` lines 632–683 (video `thSz9ZHDK9o`, 7:04:25–8:54:39):
Zariski sheaves on `Sch/S` and their restrictions to the small sites, limits and epimorphisms of
Zariski sheaves, local representability, projective bundles `𝐏(ℳ)`, the vector bundle `𝐕(ℳ)` and
the presentation of `𝐏(ℳ)` as the quotient of `𝐕*` by `𝔾_m`.

Conventions. The big Zariski site is mathlib's `Scheme.zariskiTopology` (on all schemes, the case
`S = Spec ℤ`) or `S.overGrothendieckTopology @IsOpenImmersion` (on `Sch/S`). Mathlib has no
projective bundle `𝐏(ℳ)` (the functor of invertible quotients on `Sch/S`, or `Proj Sym ℳ`
with its functor of points): the entries on `𝐏(ℳ)` are formalised in their ring-theoretic
content, over `S' = Spec k'`: an invertible quotient of `M_{k'} = k' ⊗ M` is a surjection
`M_{k'} → L` with `L` an invertible module (locally free of rank `1`, mathlib's
`Module.Invertible`), and on a local ring `k'` it is a surjection `M_{k'} → k'`.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry TensorProduct

universe u

namespace Buffalo.AG.Part05

noncomputable section

/-! ### Zariski sheaves, reformulated -/

section ZariskiSheaves

/-- thSz9ZHDK9o-25465 (7:04:25) [prop] A presheaf `F` on schemes is a Zariski sheaf if and only
if, for every scheme `S'` and every open covering `(S'_i)`, `F(S') → ∏ F(S'_i) ⇉ ∏ F(S'_i ×_{S'}
S'_j)` is an equalizer (case `S = Spec ℤ`). -/
theorem prop_25465 (F : Scheme.{u}ᵒᵖ ⥤ Type u) :
    Presieve.IsSheaf Scheme.zariskiTopology F ↔
      ∀ (X : Scheme.{u}) (𝒰 : Scheme.OpenCover.{u} X),
        Nonempty (IsLimit (Fork.ofι _ (Equalizer.Presieve.Arrows.w F 𝒰.X 𝒰.f))) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{u}]
  refine forall_congr' fun X => forall_congr' fun 𝒰 => ?_
  exact Equalizer.Presieve.Arrows.sheaf_condition F 𝒰.X 𝒰.f

/-- thSz9ZHDK9o-25594 (7:06:34) [prop] (the direct half) The restriction of a Zariski sheaf on
`Sch/S` to the small Zariski site of `S` (the `S`-schemes `U → S` that are open immersions, i.e.
the open sets of `S`) is a sheaf: `F_S` is an ordinary sheaf. -/
theorem prop_25594 (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type u)
    (hF : Presieve.IsSheaf (S.overGrothendieckTopology @IsOpenImmersion) F) :
    Presieve.IsSheaf (S.smallGrothendieckTopology (P := @IsOpenImmersion) (Q := @IsOpenImmersion))
      ((MorphismProperty.Over.forget @IsOpenImmersion ⊤ S).op ⋙ F) := by
  have hle : Scheme.precoverage @IsOpenImmersion ≤
      (@IsOpenImmersion : MorphismProperty Scheme.{u}).precoverage := inf_le_right
  have H := MorphismProperty.isContinuous_comap_forget (P := @IsOpenImmersion) (S := S) _ hle
  rw [MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology _ hle] at H
  exact Functor.op_comp_isSheaf_of_types _ _ _ ⟨F, (isSheaf_iff_isSheaf_of_type _ _).2 hF⟩

/-- The presheaf `F_X : U ↦ F(U)` on the open sets of a scheme `X` induced by a presheaf `F` on
schemes. -/
def restr (F : Scheme.{u}ᵒᵖ ⥤ Type u) (X : Scheme.{u}) : X.Opensᵒᵖ ⥤ Type u where
  obj U := F.obj (op U.unop.toScheme)
  map {U V} i := F.map (X.homOfLE i.unop.le).op
  map_id U := by
    rw [show X.homOfLE (le_refl U.unop) = 𝟙 _ from Scheme.homOfLE_rfl X _]
    exact F.map_id _
  map_comp {U V W} i j := by
    rw [← F.map_comp, ← op_comp, Scheme.homOfLE_homOfLE]

/-- thSz9ZHDK9o-25794 (7:09:54) [prop] A morphism `f : S'' → S'` induces a morphism of presheaves
`F_{S'} → f_* F_{S''}`, given on `U'` by `F(U') → F(f⁻¹U')` (the restriction `f⁻¹U' → U'`). -/
def prop_25794 (F : Scheme.{u}ᵒᵖ ⥤ Type u) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    restr F Y ⟶ (TopologicalSpace.Opens.map f.base).op ⋙ restr F X where
  app U := F.map (f.resLE U.unop (f ⁻¹ᵁ U.unop) le_rfl).op
  naturality {U V} i := by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
    congr 2
    rw [Scheme.Hom.resLE_map]
    exact (Scheme.Hom.map_resLE f _ _).symm

/-- thSz9ZHDK9o-26123 (7:15:23) [prop] (the value on the whole space) `F(S') = F_{S'}(S')`: the
open set `S'` of `S'` is isomorphic to `S'`. -/
def prop_26123 (F : Scheme.{u}ᵒᵖ ⥤ Type u) (X : Scheme.{u}) :
    (restr F X).obj (op ⊤) ≅ F.obj (op X) :=
  F.mapIso (Scheme.topIso X).op.symm

end ZariskiSheaves

/-! ### Limits and epimorphisms of Zariski sheaves -/

section LimitsEpis

/-- thSz9ZHDK9o-26334 (7:18:54) [prop] Projective limits of Zariski sheaves are computed argument
by argument: the forgetful functor to presheaves, then evaluation at `S'`, preserve them. -/
theorem prop_26334 (J : Type u) [SmallCategory J] (X : Scheme.{u}) :
    PreservesLimitsOfShape J (sheafToPresheaf Scheme.zariskiTopology.{u} (Type u) ⋙
      (evaluation _ _).obj (op X)) :=
  inferInstance

/-- thSz9ZHDK9o-26529 (7:22:09) [prop] A locally surjective morphism of Zariski sheaves (every
section of `G` is locally the image of a section of `F`) is an epimorphism; on a small site the
converse holds. -/
theorem prop_26529 {F G : Sheaf Scheme.zariskiTopology.{u} (Type u)} (φ : F ⟶ G)
    [Sheaf.IsLocallySurjective φ] : Epi φ :=
  inferInstance

/-- thSz9ZHDK9o-26529 (7:22:09) [prop] (the converse, on a small site) A morphism of sheaves of
sets is an epimorphism if and only if it is locally surjective. -/
theorem prop_26529_small {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {F G : Sheaf J (Type u)} (φ : F ⟶ G) : Sheaf.IsLocallySurjective φ ↔ Epi φ :=
  Sheaf.isLocallySurjective_iff_epi φ

/-- thSz9ZHDK9o-26850 (7:27:30) [prop] A morphism of schemes `f : X → Y` is locally surjective as a
morphism of Zariski sheaves `h_X → h_Y` if and only if it has local sections: every point of `Y`
has an open neighbourhood `V` and a section `V → X`. -/
theorem prop_26850 {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (yoneda.map f) ↔
      ∀ y : Y, ∃ (V : Scheme.{u}) (j : V ⟶ Y), IsOpenImmersion j ∧ y ∈ Set.range j ∧
        ∃ s : V ⟶ X, s ≫ f = j := by
  constructor
  · intro h y
    have hm := Presheaf.imageSieve_mem Scheme.zariskiTopology (yoneda.map f) (U := op Y) (𝟙 Y)
    obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hm
    obtain ⟨x, hx⟩ := 𝒰.covers y
    obtain ⟨s, hs⟩ := h𝒰 _ _ (Presieve.ofArrows.mk (𝒰.idx y))
    refine ⟨𝒰.X (𝒰.idx y), 𝒰.f (𝒰.idx y), 𝒰.map_prop _, ⟨x, hx⟩, s, ?_⟩
    simpa using hs
  · intro h
    choose V j hj hy s hs using h
    refine ⟨fun {T} t => ?_⟩
    let 𝒰 : Scheme.OpenCover.{u} Y :=
      Scheme.Cover.mkOfCovers Y V j (fun y => ⟨y, hy y⟩) hj
    let s' : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ X := fun i => s i
    have hs' : ∀ i : 𝒰.I₀, s' i ≫ f = 𝒰.f i := fun i => hs i
    refine Scheme.zariskiTopology.superset_covering ?_
      (Scheme.zariskiTopology.pullback_stable t (𝒰.mem_grothendieckTopology))
    rintro W g ⟨Z, a, b, ⟨y⟩, hab⟩
    refine ⟨a ≫ s' y, ?_⟩
    change (a ≫ s' y) ≫ f = g ≫ t
    rw [Category.assoc, hs', ← hab]

/-- thSz9ZHDK9o-27459 (7:37:39) [prop] An open immersion is a monomorphism, also as a morphism of
the represented sheaves. -/
theorem prop_27459 {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Mono f ∧ Mono (yoneda.map f) :=
  ⟨inferInstance, inferInstance⟩

end LimitsEpis

/-! ### Projective bundles: local representability -/

section Representability

/-- thSz9ZHDK9o-27917 (7:45:17) [prop] (case `S = Spec ℤ`) A Zariski sheaf `F` covered by open
subfunctors `F_i` that are representable (`h_{X_i} → F` relatively representable open immersions,
jointly locally surjective) is representable (mathlib: `LocalRepresentability.isRepresentable`). -/
theorem prop_27917 (F : Sheaf Scheme.zariskiTopology.{u} (Type u)) {ι : Type u}
    {X : ι → Scheme.{u}} (f : (i : ι) → yoneda.obj (X i) ⟶ F.1)
    (hf : ∀ i, IsOpenImmersion.presheaf (f i))
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)] :
    F.1.IsRepresentable :=
  Scheme.LocalRepresentability.isRepresentable hf

/-- thSz9ZHDK9o-27980 (7:46:20) [prop] Quasi-coherent modules (mathlib:
`SheafOfModules.IsQuasicoherent`, locally the cokernel of a morphism of free modules). -/
example (X : Scheme.{u}) (M : X.Modules) : Prop := M.IsQuasicoherent

end Representability

/-! ### Projective bundles: the ring-theoretic content -/

section ProjectiveBundles

variable {A : Type u} [CommRing A]

/-- thSz9ZHDK9o-28630 (7:57:10) [prop] The set of points where a section `s` of a finitely
generated module `L` (e.g. an invertible one) generates the stalk is open: it is the complement of
the support of `L/As`. -/
theorem prop_28630 (L : Type u) [AddCommGroup L] [Module A L] [Module.Finite A L] (s : L) :
    IsOpen {p : PrimeSpectrum A | Subsingleton
      (LocalizedModule p.asIdeal.primeCompl (L ⧸ Submodule.span A {s}))} := by
  have hc := Module.isClosed_support (R := A) (M := L ⧸ Submodule.span A {s})
  convert hc.isOpen_compl using 1
  ext p
  simp [Module.notMem_support_iff]

/-- thSz9ZHDK9o-28693 (7:58:13) [prop] Over a local ring, if `e_i` generate a module `L ≃ k'`
free of rank `1` (an invertible quotient), one of the `e_i` is a basis of it. -/
theorem prop_28693 [IsLocalRing A] {L : Type*} [AddCommGroup L] [Module A L] (e : L ≃ₗ[A] A)
    {ι : Type*} (x : ι → L) (hx : Submodule.span A (Set.range x) = ⊤) :
    ∃ i, Submodule.span A {x i} = ⊤ := by
  have h1 : Ideal.span (Set.range (e ∘ x)) = ⊤ := by
    have := congrArg (Submodule.map (e : L →ₗ[A] A)) hx
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at this
    exact this
  by_contra hne
  push Not at hne
  have hle : Ideal.span (Set.range (e ∘ x)) ≤ IsLocalRing.maximalIdeal A := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    refine (IsLocalRing.mem_maximalIdeal _).2 fun hu => hne i ?_
    rw [eq_top_iff]
    intro l _
    refine Submodule.mem_span_singleton.2 ⟨e l * ((hu.unit⁻¹ : Aˣ) : A), e.injective ?_⟩
    rw [map_smul, smul_eq_mul, mul_assoc,
      show ((hu.unit⁻¹ : Aˣ) : A) * e (x i) = 1 from hu.val_inv_mul, mul_one]
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.1 (h1 ▸ hle))

/-- thSz9ZHDK9o-29021 (8:03:41) [prop] `k' ↦ Hom_{k'}(V_{k'}, k') = Hom_k(V, k')` is represented
by `Sym_k(V)`. -/
def prop_29021 (k : Type u) [CommRing k] (V : Type u) [AddCommGroup V] [Module k V]
    (k' : Type u) [CommRing k'] [Algebra k k'] :
    (k' ⊗[k] V →ₗ[k'] k') ≃ (SymmetricAlgebra k V →ₐ[k] k') :=
  (LinearMap.liftBaseChangeEquiv k').toEquiv.symm.trans (SymmetricAlgebra.lift)

/-- thSz9ZHDK9o-29157 (8:05:57) [prop] `P_i(k')`, the homomorphisms `V → k'` sending `e_i` to `1`,
is represented by `Sym(V)/(e_i - 1)`. -/
def prop_29157 (k : Type u) [CommRing k] (V : Type u) [AddCommGroup V] [Module k V] (e : V)
    (k' : Type u) [CommRing k'] [Algebra k k'] :
    {φ : V →ₗ[k] k' // φ e = 1} ≃
      (SymmetricAlgebra k V ⧸ Ideal.span {SymmetricAlgebra.ι k V e - 1} →ₐ[k] k') where
  toFun φ := Ideal.Quotient.liftₐ _ (SymmetricAlgebra.lift φ.1) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_sub, SymmetricAlgebra.lift_ι_apply, φ.2, map_one, sub_self, mul_zero]
  invFun ψ := ⟨SymmetricAlgebra.lift.symm
      (ψ.comp (Ideal.Quotient.mkₐ k _)), by
    have h : Ideal.Quotient.mk (Ideal.span {SymmetricAlgebra.ι k V e - 1})
        (SymmetricAlgebra.ι k V e - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [map_sub, map_one, sub_eq_zero] at h
    change ψ (Ideal.Quotient.mk _ (SymmetricAlgebra.ι k V e)) = 1
    rw [h, map_one]⟩
  left_inv φ := Subtype.ext <| SymmetricAlgebra.lift.injective <| by
    rw [Equiv.apply_symm_apply]
    exact Ideal.Quotient.liftₐ_comp _ _ _
  right_inv ψ := by
    refine Ideal.Quotient.algHom_ext _ (SymmetricAlgebra.algHom_ext ?_)
    ext v
    simp
    rfl

/-- thSz9ZHDK9o-29348 (8:09:08) [def] `𝒪(n) = 𝒪(1)^{⊗n}`, `n ∈ ℤ`: in the Picard group,
`L^{⊗(-m)} = (L^{⊗m})^{-1} = (L^{-1})^{⊗m}`. -/
theorem def_29348 (L : CommRing.Pic A) (m : ℕ) :
    L ^ (-(m : ℤ)) = (L ^ m)⁻¹ ∧ (L ^ m)⁻¹ = L⁻¹ ^ m :=
  ⟨by rw [zpow_neg, zpow_natCast], (inv_pow L m).symm⟩

/-- thSz9ZHDK9o-29606 (8:13:26) [def] The vector bundle `𝐕(M)`: `k' ↦ Hom_{k'}(M_{k'}, k')`,
which is `Hom_k(M, k')` (mathlib: `LinearMap.liftBaseChangeEquiv`) and is represented by
`Sym(M)` (`prop_29021`). -/
def def_29606 (k : Type u) [CommRing k] (M : Type u) [AddCommGroup M] [Module k M]
    (k' : Type u) [CommRing k'] [Algebra k k'] :
    (M →ₗ[k] k') ≃ₗ[k'] (k' ⊗[k] M →ₗ[k'] k') :=
  LinearMap.liftBaseChangeEquiv k'

/-- thSz9ZHDK9o-29932 (8:18:52) [prop] A point `u : M → k'` of `𝐕(M)` is an epimorphism
(`u(M)` generates `k'`) if and only if it is nonzero on each fibre, if and only if it lies off the
zero section: `Spec k' → Spec Sym(M)` avoids `V(M · Sym M)`. -/
theorem prop_29932 (k : Type u) [CommRing k] (M : Type u) [AddCommGroup M] [Module k M]
    (k' : Type u) [CommRing k'] [Algebra k k'] (u : M →ₗ[k] k') :
    (Ideal.span (Set.range u) = ⊤ ↔ ∀ p : Ideal k', p.IsPrime → ∃ m, u m ∉ p) ∧
      (Ideal.span (Set.range u) = ⊤ ↔
        (Ideal.span (Set.range (SymmetricAlgebra.ι k M))).map (SymmetricAlgebra.lift u) = ⊤) := by
  refine ⟨⟨fun h p hp => ?_, fun h => ?_⟩, ?_⟩
  · by_contra hc
    push Not at hc
    refine hp.ne_top (top_le_iff.1 (h ▸ ?_))
    rw [Ideal.span_le]
    rintro _ ⟨m, rfl⟩
    exact hc m
  · by_contra hne
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨m, hm⟩ := h p hp.isPrime
    exact hm (hle (Ideal.subset_span ⟨m, rfl⟩))
  · rw [Ideal.map_span, ← Set.range_comp]
    congr! 3
    ext m
    simp

/-- thSz9ZHDK9o-30064 (8:21:04) [prop] An epimorphism `u : M → R` defines the quotient
`M/ker u`, which is free of rank `1`. -/
def prop_30064 {M : Type*} [AddCommGroup M] [Module A M] (u : M →ₗ[A] A)
    (hu : Function.Surjective u) : (M ⧸ LinearMap.ker u) ≃ₗ[A] A :=
  u.quotKerEquivOfSurjective hu

/-- thSz9ZHDK9o-30256 (8:24:16) [prop] `𝐕* → 𝐏(M)` is an epimorphism: over a local ring an
invertible module `L` is free of rank `1`, so an invertible quotient `q : M → L` is of the form
`M/ker u` with `u : M → R` an epimorphism. -/
theorem prop_30256 [IsLocalRing A] {M L : Type u} [AddCommGroup M] [Module A M] [AddCommGroup L]
    [Module A L] [Module.Invertible A L] (q : M →ₗ[A] L) (hq : Function.Surjective q) :
    ∃ v : M →ₗ[A] A, Function.Surjective v ∧ LinearMap.ker v = LinearMap.ker q := by
  have hfree : Module.Free A L := CommRing.Pic.mk_eq_one_iff_free.1 (Subsingleton.elim _ _)
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.1 hfree
  refine ⟨e.toLinearMap ∘ₗ q, e.surjective.comp hq, ?_⟩
  rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]

/-- thSz9ZHDK9o-30385 (8:26:25) [prop] `𝔾_m` is represented by `k[t, t⁻¹]`: a homomorphism
`k[t, t⁻¹] → k'` is determined by the image of `t`, which can be any unit (`Part02.prop_17855`). -/
theorem prop_30385 (k : Type u) [CommRing k] (k' : Type*) [CommRing k'] [Algebra k k'] :
    Function.Injective (fun φ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k' =>
        φ (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))
          Polynomial.X)) ∧
      Set.range (fun φ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k' =>
        φ (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))
          Polynomial.X)) = {t | IsUnit t} :=
  Buffalo.AG.Part02.prop_17855 k k'

/-- thSz9ZHDK9o-30521 (8:28:41) [prop] `𝔾_m` acts freely on `𝐕*`: `λu = u` with `u` an
epimorphism forces `λ = 1`; on `𝐕` the origin is fixed by every `λ`. -/
theorem prop_30521 {M : Type*} [AddCommGroup M] [Module A M] (u : M →ₗ[A] A)
    (hu : Function.Surjective u) (c : Aˣ) (h : c • u = u) :
    c = 1 ∧ ∀ d : Aˣ, d • (0 : M →ₗ[A] A) = 0 := by
  refine ⟨?_, fun d => smul_zero d⟩
  obtain ⟨m, hm⟩ := hu 1
  have := LinearMap.congr_fun h m
  rw [LinearMap.smul_apply, hm, Units.smul_def, smul_eq_mul, mul_one] at this
  exact Units.ext this

/-- thSz9ZHDK9o-30648 (8:30:48) [prop] `u` and `λu`, `λ` invertible, have the same kernel. -/
theorem prop_30648 {M : Type*} [AddCommGroup M] [Module A M] (u : M →ₗ[A] A) (c : Aˣ) :
    LinearMap.ker (c • u) = LinearMap.ker u := by
  ext m
  simp only [LinearMap.mem_ker, LinearMap.smul_apply, Units.smul_def, smul_eq_mul]
  exact ⟨fun h => by simpa using congrArg (((c⁻¹ : Aˣ) : A) * ·) h, fun h => by rw [h, mul_zero]⟩

/-- thSz9ZHDK9o-30775 (8:32:55) [prop] Two epimorphisms `u, v : M → R` define the same quotient
(have the same kernel) if and only if `v = λu` with `λ` a unit. -/
theorem prop_30775 {M : Type*} [AddCommGroup M] [Module A M] (u v : M →ₗ[A] A)
    (hu : Function.Surjective u) (hv : Function.Surjective v) :
    LinearMap.ker u = LinearMap.ker v ↔ ∃ c : Aˣ, v = c • u := by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ => hc ▸ (prop_30648 u c).symm⟩
  have key : ∀ (u v : M →ₗ[A] A), Function.Surjective u → LinearMap.ker u = LinearMap.ker v →
      ∀ m₀, u m₀ = 1 → v = v m₀ • u := by
    intro u v _ h m₀ hm₀
    ext m
    have hk : m - u m • m₀ ∈ LinearMap.ker v := by
      rw [← h, LinearMap.mem_ker, map_sub, map_smul, hm₀, smul_eq_mul, mul_one, sub_self]
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hk
    rw [LinearMap.smul_apply, hk, smul_eq_mul, mul_comm]
  obtain ⟨m₀, hm₀⟩ := hu 1
  obtain ⟨n₀, hn₀⟩ := hv 1
  have h1 := key u v hu h m₀ hm₀
  have h2 := key v u hv h.symm n₀ hn₀
  have hunit : v m₀ * u n₀ = 1 := by
    have := LinearMap.congr_fun h1 n₀
    rwa [LinearMap.smul_apply, hn₀, smul_eq_mul, eq_comm] at this
  exact ⟨⟨v m₀, u n₀, hunit, by rw [mul_comm, hunit]⟩, h1⟩

/-- thSz9ZHDK9o-30838 (8:33:58) [prop] (pointwise) `𝐕* → 𝐏(M)` is a `𝔾_m`-torsor: the fibre of
`u ↦ ker u` through an epimorphism `u` is the orbit `𝔾_m · u`, on which `𝔾_m` acts freely. -/
theorem prop_30838 {M : Type*} [AddCommGroup M] [Module A M] (u : M →ₗ[A] A)
    (hu : Function.Surjective u) :
    {v : M →ₗ[A] A | Function.Surjective v ∧ LinearMap.ker v = LinearMap.ker u} =
      Set.range (fun c : Aˣ => c • u) ∧ ∀ c d : Aˣ, c • u = d • u → c = d := by
  refine ⟨Set.ext fun v => ⟨fun ⟨hv, h⟩ => ?_, ?_⟩, fun c d h => ?_⟩
  · obtain ⟨c, hc⟩ := (prop_30775 u v hu hv).1 h.symm
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨fun a => ?_, prop_30648 u c⟩
    obtain ⟨m, hm⟩ := hu (((c⁻¹ : Aˣ) : A) * a)
    exact ⟨m, by rw [LinearMap.smul_apply, hm, Units.smul_def, smul_eq_mul, ← mul_assoc,
      Units.mul_inv, one_mul]⟩
  · have h' : (c⁻¹ * d) • u = u := by rw [mul_smul, ← h, ← mul_smul, inv_mul_cancel, one_smul]
    have := (prop_30521 u hu _ h').1
    rw [inv_mul_eq_one] at this
    exact this

/-- thSz9ZHDK9o-30903 (8:35:03) [prop] `𝔾_m = GL_1`: the automorphisms of the module `R` are the
multiplications by units. -/
def prop_30903 : (A ≃ₗ[A] A) ≃* Aˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv A A).symm.trans
    (Units.mapEquiv ((RingEquiv.moduleEndSelf A).symm.trans (RingEquiv.toOpposite A).symm).toMulEquiv)

/-- thSz9ZHDK9o-30966 (8:36:06) [prop] (pointwise) `Isom(R, L)` is a principal homogeneous set
under `Rˣ` when nonempty: two trivializations of `L` differ by a unique unit. -/
theorem prop_30966 {L : Type*} [AddCommGroup L] [Module A L] (e e' : A ≃ₗ[A] L) :
    ∃! c : Aˣ, ∀ a, e' a = e (c * a) := by
  refine ⟨Units.mk (e.symm (e' 1)) (e'.symm (e 1)) ?_ ?_, fun a => ?_, fun c hc => ?_⟩
  · have : e.symm (e' 1) * e'.symm (e 1) = e.symm (e' (e'.symm (e 1))) := by
      rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, mul_one]
    rw [this, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  · have : e'.symm (e 1) * e.symm (e' 1) = e'.symm (e (e.symm (e' 1))) := by
      rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, mul_one]
    rw [this, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  · change e' a = e (e.symm (e' 1) * a)
    rw [mul_comm, ← smul_eq_mul, map_smul, LinearEquiv.apply_symm_apply, ← map_smul, smul_eq_mul,
      mul_one]
  · ext
    have := hc 1
    rw [mul_one] at this
    change (c : A) = e.symm (e' 1)
    rw [this, LinearEquiv.symm_apply_apply]

/-- thSz9ZHDK9o-31032 (8:37:12) [def] (pointwise) A torsor: a nonempty set with a free and
transitive action; it is then isomorphic to the group (`g ↦ g • x`). -/
theorem def_31032 {G X : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) (x : X) :
    Function.Bijective (fun g : G => g • x) := by
  refine ⟨fun g h hgh => ?_, fun y => MulAction.exists_smul_eq G x y⟩
  have : (h⁻¹ * g) • x = x := by
    rw [mul_smul]
    rw [show g • x = h • x from hgh, inv_smul_smul]
  exact (inv_mul_eq_one.1 (hfree _ x this)).symm

/-- thSz9ZHDK9o-31099 (8:38:19) [prop] (pointwise) If `G` acts freely on `F`, `G` acts simply
transitively on each fibre of `F → F/G` (each orbit). -/
theorem prop_31099 {G X : Type*} [Group G] [MulAction G X]
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) {x y : X}
    (h : (Quotient.mk (MulAction.orbitRel G X) x) = Quotient.mk _ y) :
    ∃! g : G, g • x = y := by
  obtain ⟨g, hg⟩ := Quotient.exact h
  change g • y = x at hg
  refine ⟨g⁻¹, ?_, fun g' hg' => ?_⟩
  · change g⁻¹ • x = y
    rw [← hg, inv_smul_smul]
  · have : (g' * g) • y = y := by rw [mul_smul, hg, hg']
    exact eq_inv_of_mul_eq_one_left (hfree _ y this)

/-- thSz9ZHDK9o-31232 (8:40:32) [prop] (pointwise) The points of `𝐕*` above an invertible
quotient `q : M → L` are the trivializations of `L`: an isomorphism `e : L ≃ R` gives the
epimorphism `e ∘ q`, with kernel `ker q`. -/
theorem prop_31232 {M L : Type*} [AddCommGroup M] [Module A M] [AddCommGroup L] [Module A L]
    (q : M →ₗ[A] L) (hq : Function.Surjective q) (e : L ≃ₗ[A] A) :
    Function.Surjective (e.toLinearMap ∘ₗ q) ∧ LinearMap.ker (e.toLinearMap ∘ₗ q) = LinearMap.ker q := by
  refine ⟨e.surjective.comp hq, ?_⟩
  rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]

/-- thSz9ZHDK9o-31617 (8:46:57) [def] Projective space `ℙⁿ` over a field `k`, whose `k`-points
are the lines of `k^{n+1}` (mathlib: `Projectivization`); in Grothendieck's convention
`𝐏(k^{n+1})` parametrizes the rank-one quotients of `k^{n+1}`, i.e. the lines of the dual. -/
example (k : Type*) [Field k] (n : ℕ) : Type _ := Projectivization k (Fin (n + 1) → k)

/-- thSz9ZHDK9o-31747 (8:49:07) [prop] (affine pointwise case) A linear map `u : R^{n+1} → R`
(the `n+1` sections `u(e_i)`) is an epimorphism if and only if the `u(e_i)` generate `R`. -/
theorem prop_31747 (n : ℕ) (u : (Fin (n + 1) → A) →ₗ[A] A) :
    Function.Surjective u ↔ Ideal.span (Set.range fun i => u (Pi.single i 1)) = ⊤ := by
  constructor
  · intro hu
    rw [eq_top_iff]
    intro a _
    obtain ⟨x, rfl⟩ := hu a
    have : x = ∑ i, x i • Pi.single i (1 : A) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · intro h a
    have : a ∈ Ideal.span (Set.range fun i => u (Pi.single i 1)) := h ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 this
    refine ⟨fun i => c i, ?_⟩
    have : (fun i => c i) = ∑ i, c i • Pi.single i (1 : A) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this, map_sum, ← hc]
    simp [map_smul]

/-- thSz9ZHDK9o-32079 (8:54:39) [prop] Invertible quotients up to isomorphism are kernels: two
quotients `q : M → L`, `q' : M → L'` are isomorphic under `M` if and only if they have the same
kernel. -/
theorem prop_32079 {M L L' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup L] [Module A L]
    [AddCommGroup L'] [Module A L'] (q : M →ₗ[A] L) (q' : M →ₗ[A] L')
    (hq : Function.Surjective q) (hq' : Function.Surjective q') :
    LinearMap.ker q = LinearMap.ker q' ↔ ∃ e : L ≃ₗ[A] L', e.toLinearMap ∘ₗ q = q' := by
  constructor
  · intro h
    refine ⟨(q.quotKerEquivOfSurjective hq).symm.trans
      ((Submodule.quotEquivOfEq _ _ h).trans (q'.quotKerEquivOfSurjective hq')), ?_⟩
    ext m
    have h1 : (q.quotKerEquivOfSurjective hq).symm (q m) = Submodule.Quotient.mk m := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.trans_apply, h1, Submodule.quotEquivOfEq_mk]
    rfl
  · rintro ⟨e, rfl⟩
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]

end ProjectiveBundles

end

end Buffalo.AG.Part05
