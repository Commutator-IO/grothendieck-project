import Mathlib

/-!
# Buffalo, algebraic groups, Part 03 (b): regularity, smoothness, normality

Entries `3ULFIl_2Wis-9030` to `3ULFIl_2Wis-13937` of `docs/buffalo-groupes/index.tex` (end of
2 July 1973 and the session of 10 July 1973). Statuses in
`docs/buffalo-groupes/lean/Part03.json`.

Conventions. A scheme is regular when all its local rings are regular local rings (Mathlib's
`IsRegularLocalRing`), normal when they are integrally closed domains; "geometrically `P`" is
Mathlib's `AlgebraicGeometry.geometrically P` (every base change to a field has `P`). Mathlib's
`Smooth` is the smoothness of the structure morphism (formally smooth and locally of finite
presentation); its equivalence with "locally of finite type and geometrically regular" is not in
Mathlib, so the statements below are made with whichever notion Mathlib carries.
-/

namespace Buffalo.Groupes.Part03

open CategoryTheory Limits AlgebraicGeometry TensorProduct Polynomial Set Topology

universe u

/-! ## Regularity and base change -/

/-- 3ULFIl_2Wis-9030 (2:30:30) [thm] Regularity is preserved by extension of the base field: the
case of affine space, `𝔸ⁿ_{k'} = Spec k'[X₁,…,Xₙ]` is regular for every field `k'`. -/
theorem affineSpace_regular (K' : Type*) [Field K'] (n : ℕ) :
    IsRegularRing (MvPolynomial (Fin n) K') :=
  inferInstance

/-- 3ULFIl_2Wis-9092 (2:31:32) [def] Essentially of finite type is Mathlib's
`Algebra.EssFiniteType`; a field extension essentially of finite type is finitely generated as a
field. -/
theorem essFiniteType_field_fg (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] : (⊤ : IntermediateField K L).FG :=
  IntermediateField.fg_top K L

/-- A scheme is regular if its local rings are regular local rings. -/
def IsRegularScheme : ObjectProperty Scheme.{u} :=
  fun X ↦ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- 3ULFIl_2Wis-9541 (2:39:01) [def] `X` is geometrically regular over `k` if every base change to
a field is regular. -/
def GeometricallyRegular : MorphismProperty Scheme.{u} := geometrically IsRegularScheme

/-- 3ULFIl_2Wis-9541 (2:39:01) [def] ... and smooth if moreover locally of finite type. -/
def IsSmoothGR {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  LocallyOfFiniteType f ∧ GeometricallyRegular f

/-- 3ULFIl_2Wis-10463 (2:54:23) [prop] A geometrically regular scheme over `k` is regular. -/
theorem isRegular_of_geometricallyRegular {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (hf : GeometricallyRegular f) : IsRegularScheme X :=
  hf (𝟙 _) (𝟙 X) f IsPullback.of_id_snd.flip

section Insep

variable {K : Type} [Field K] (p : ℕ) [hp : Fact p.Prime] (a : K)

/-- 3ULFIl_2Wis-10463 (2:54:23) [prop] Over an imperfect field `K` (`a ∈ K` not a `p`-th power),
`X^p - a` is irreducible, so `L = K[X]/(X^p - a)` is a field. -/
theorem insep_irreducible (ha : ∀ b : K, b ^ p ≠ a) : Irreducible (X ^ p - C a : K[X]) :=
  X_pow_sub_C_irreducible_of_prime hp.out ha

/-- 3ULFIl_2Wis-10463 (2:54:23) [prop] ... but `L ⊗_K L` is not reduced: `Spec L` is regular (a
field) and not geometrically regular (nor geometrically normal, nor geometrically reduced), so the
converse fails over every imperfect field. -/
theorem insep_tensor_not_reduced [CharP K p] (ha : ∀ b : K, b ^ p ≠ a) :
    ¬ IsReduced (AdjoinRoot (X ^ p - C a : K[X]) ⊗[K] AdjoinRoot (X ^ p - C a : K[X])) := by
  set f : K[X] := X ^ p - C a
  set L := AdjoinRoot f
  have hmon : f.Monic := monic_X_pow_sub_C a hp.out.ne_zero
  have hdeg : f.natDegree = p := natDegree_X_pow_sub_C
  let pb := AdjoinRoot.powerBasis' hmon
  have hdim : pb.dim = p := by simp [pb, hdeg]
  have h1 : 1 < pb.dim := hdim ▸ hp.out.one_lt
  let ψ : L →ₗ[K] K := pb.basis.coord ⟨1, h1⟩
  have hψ1 : ψ 1 = 0 := by
    have : (1 : L) = pb.basis ⟨0, by omega⟩ := by rw [pb.basis_eq_pow]; simp
    rw [this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      ite_eq_right]
    simp [Fin.ext_iff]
  have hψr : ψ (AdjoinRoot.root f) = 1 := by
    have : AdjoinRoot.root f = pb.basis ⟨1, h1⟩ := by rw [pb.basis_eq_pow]; simp [pb]
    rw [this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  let Φ : L ⊗[K] L →ₗ[K] L := TensorProduct.lift
    (LinearMap.mk₂ K (fun u v ↦ ψ v • u) (fun _ _ _ ↦ smul_add _ _ _)
      (fun _ _ _ ↦ smul_comm _ _ _) (fun _ _ _ ↦ by rw [map_add, add_smul])
      (fun _ _ _ ↦ by rw [map_smul, smul_eq_mul, mul_smul]))
  set z : L ⊗[K] L := AdjoinRoot.root f ⊗ₜ 1 - 1 ⊗ₜ AdjoinRoot.root f
  have hz : z ≠ 0 := by
    intro h
    have := congrArg Φ h
    simp [Φ, z, hψ1, hψr] at this
    have := Fact.mk (insep_irreducible p a ha)
    exact one_ne_zero ‹(1 : L) = 0›
  have : Nontrivial (L ⊗[K] L) := ⟨⟨z, 0, hz⟩⟩
  have : CharP (L ⊗[K] L) p := charP_of_injective_algebraMap' K p
  have hroot : AdjoinRoot.root f ^ p = algebraMap K L a := by
    have := AdjoinRoot.eval₂_root f
    simp only [f, eval₂_sub, eval₂_X_pow, eval₂_C] at this
    rw [sub_eq_zero] at this; exact this
  have hzp : z ^ p = 0 := by
    rw [sub_pow_char, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, one_pow,
      hroot, Algebra.algebraMap_eq_smul_one, smul_tmul, sub_self]
  intro hred
  exact hz (hred.eq_zero z ⟨p, hzp⟩)

end Insep

/-- 3ULFIl_2Wis-10525 (2:55:25) [prop] Geometric regularity is invariant under extension of the
base (stable under base change). -/
instance : GeometricallyRegular.IsStableUnderBaseChange :=
  inferInstanceAs (geometrically IsRegularScheme).IsStableUnderBaseChange

/-- 3ULFIl_2Wis-10920 (3:02:00) [def] `X → Y` is geometrically regular at `x` if, after every base
change to a field, the local rings at the points over `x` are regular. -/
def GeometricallyRegularAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  ∀ ⦃K : Type u⦄ [Field K] (y : Spec (.of K) ⟶ Y) ⦃Z : Scheme.{u}⦄ (fst : Z ⟶ X)
    (snd : Z ⟶ Spec (.of K)), IsPullback fst snd f y →
      ∀ z : Z, fst z = x → IsRegularLocalRing (Z.presheaf.stalk z)

/-- 3ULFIl_2Wis-11054 (3:04:14) [thm] Jacobian criterion, one direction: a smooth morphism is,
locally on the source, étale over an affine space `𝔸ⁿ` of the base. -/
theorem smooth_locally_etale_over_affineSpace {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) : ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
      (e : V ≤ f ⁻¹ᵁ U), ∃ n, ∃ g : MvPolynomial (Fin n) Γ(Y, U) →+* Γ(X, V),
        g.comp MvPolynomial.C = (f.appLE U V e).hom ∧ g.Etale := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth f x
  exact ⟨U, hU, V, hV, hx, e, h.exists_etale_mvPolynomial⟩

/-- 3ULFIl_2Wis-11119 (3:05:19) [def] Étale over a field (Mathlib's `Algebra.Etale`) means a finite
product of finite separable extensions. -/
theorem etale_field_iff (K A : Type u) [Field K] [CommRing A] [Algebra K A] :
    Algebra.Etale K A ↔
      ∃ (I : Type u) (_ : Finite I) (Ai : I → Type u) (_ : ∀ i, Field (Ai i))
        (_ : ∀ i, Algebra K (Ai i)) (_ : A ≃ₐ[K] Π i, Ai i),
        ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) :=
  Algebra.Etale.iff_exists_algEquiv_prod K A

/-- 3ULFIl_2Wis-11314 (3:08:34) [def] A scheme étale over `𝔸ⁿ_k` is smooth over `k`. -/
theorem smooth_of_etale_over_affineSpace (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    (n : ℕ) [Algebra (MvPolynomial (Fin n) K) A] [IsScalarTower K (MvPolynomial (Fin n) K) A]
    [Algebra.Etale (MvPolynomial (Fin n) K) A] : Algebra.Smooth K A :=
  Algebra.Smooth.comp K (MvPolynomial (Fin n) K) A

/-- 3ULFIl_2Wis-11575 (3:12:55) [prop] Over a perfect field, every finitely generated extension is
separably generated (a finite separable extension of a purely transcendental one). -/
theorem separablyGenerated_of_perfectField (K L : Type*) [Field K] [Field L] [Algebra K L]
    [PerfectField K] [Algebra.EssFiniteType K L] : Algebra.IsSeparablyGenerated K L :=
  inferInstance

/-- 3ULFIl_2Wis-12229 (3:23:49) [prop] For an algebra of finite presentation, the étale locus is
open. -/
theorem isOpen_etaleLocus (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] : IsOpen (Algebra.etaleLocus R A) :=
  Algebra.isOpen_etaleLocus

/-- 3ULFIl_2Wis-12422 (3:27:02) [prop] The smooth locus of a morphism locally of finite
presentation (e.g. of a scheme locally of finite type over a field) is open. -/
theorem isOpen_smoothLocus {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    IsOpen (f.smoothLocus : Set X) :=
  f.smoothLocus.2

/-- 3ULFIl_2Wis-12486 (3:28:06) [prop] In a quasi-sober space with finitely many irreducible
components, an open set is dense iff it contains the generic points of all the components. -/
theorem dense_iff_genericPoints {X : Type*} [TopologicalSpace X] [QuasiSober X]
    (hfin : (irreducibleComponents X).Finite) {U : Set X} (hU : IsOpen U) :
    Dense U ↔ ∀ Z ∈ irreducibleComponents X, ∀ η : X, IsGenericPoint η Z → η ∈ U := by
  constructor
  · intro hd Z hZ η hη
    have hcl := closure_sUnion_irreducibleComponents_sdiff_singleton hfin Z hZ
    have hO : IsOpen (⋃₀ (irreducibleComponents X \ {Z}))ᶜ :=
      (hfin.sdiff.isClosed_sUnion fun W hW ↦
        isClosed_of_mem_irreducibleComponents W hW.1).isOpen_compl
    have hne : ((⋃₀ (irreducibleComponents X \ {Z}))ᶜ).Nonempty := by
      by_contra h0
      rw [not_nonempty_iff_eq_empty] at h0
      rw [h0, closure_empty] at hcl
      exact hZ.1.nonempty.ne_empty hcl.symm
    obtain ⟨u, huO, huU⟩ := hd.inter_open_nonempty _ hO hne
    have huZ : u ∈ Z := hcl ▸ subset_closure huO
    rw [← hη] at huZ
    exact (specializes_iff_mem_closure.mpr huZ).mem_open hU huU
  · intro h
    rw [dense_iff_inter_open]
    rintro V hV ⟨y, hy⟩
    obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := y))
      isClosed_irreducibleComponent
    have hηU := h _ (irreducibleComponent_mem_irreducibleComponents y) η hη
    have hyη : η ⤳ y := by
      rw [specializes_iff_mem_closure, hη]; exact mem_irreducibleComponent
    exact ⟨η, hyη.mem_open hV hy, hηU⟩

/-- 3ULFIl_2Wis-12486 (3:28:06) [prop] For `X` quasi-compact and locally of finite type over `k`,
the smooth locus is dense iff `X` is smooth at its maximal (generic) points. -/
theorem dense_smoothLocus_iff {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [CompactSpace X] :
    Dense (f.smoothLocus : Set X) ↔
      ∀ Z ∈ irreducibleComponents X, ∀ η : X, IsGenericPoint η Z → η ∈ f.smoothLocus := by
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  exact dense_iff_genericPoints TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    f.smoothLocus.2

/-- 3ULFIl_2Wis-12550 (3:29:10) [prop] A separably generated extension (with a separating
transcendence basis) is formally smooth, i.e. geometrically regular. -/
theorem formallySmooth_of_separatingBasis {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    {v : ι → L} (hv : AlgebraicIndependent K v)
    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) L] :
    Algebra.FormallySmooth K L :=
  Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hv

/-- 3ULFIl_2Wis-12689 (3:31:29) [prop] Over a perfect field, the smooth points of a reduced scheme
locally of finite type form a dense open set. -/
theorem smoothLocus_open_dense {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
    [IsReduced X] (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    IsOpen (f.smoothLocus : Set X) ∧ Dense (f.smoothLocus : Set X) :=
  ⟨f.smoothLocus.2, f.dense_smoothLocus_of_perfectField⟩

/-! ## Geometric normality -/

/-- A scheme is normal if its local rings are integrally closed domains. -/
def IsNormalScheme : ObjectProperty Scheme.{u} :=
  fun X ↦ ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

/-- Geometric normality. -/
def GeometricallyNormal : MorphismProperty Scheme.{u} := geometrically IsNormalScheme

/-- 3ULFIl_2Wis-13011 (3:36:51) [prop] Geometric normality is stable under base change ... -/
instance : GeometricallyNormal.IsStableUnderBaseChange :=
  inferInstanceAs (geometrically IsNormalScheme).IsStableUnderBaseChange

/-- 3ULFIl_2Wis-13011 (3:36:51) [prop] ... and implies normality (the converse fails over an
imperfect field, `insep_tensor_not_reduced`). -/
theorem isNormal_of_geometricallyNormal {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (hf : GeometricallyNormal f) : IsNormalScheme X :=
  hf (𝟙 _) (𝟙 X) f IsPullback.of_id_snd.flip

/-! ## Smoothness of group schemes -/

/-- 3ULFIl_2Wis-13091 (3:38:11) [prop] A geometrically reduced (separable) group scheme locally of
finite type over a field is smooth (Mathlib `smooth_of_grpObj`). -/
theorem grp_smooth_of_geometricallyReduced {K : Type u} [Field K] {G : Scheme.{u}}
    (f : G ⟶ Spec (.of K)) [LocallyOfFiniteType f] [GrpObj (Over.mk f)] [GeometricallyReduced f] :
    Smooth f :=
  smooth_of_grpObj f

/-- 3ULFIl_2Wis-13937 (3:52:17) [prop] In a noetherian space, the connected components are the
irreducible components iff only one irreducible component passes through each point. -/
theorem connected_eq_irreducible_iff {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] :
    (∀ x : X, connectedComponent x ∈ irreducibleComponents X) ↔
      ∀ x : X, ∀ Z₁ ∈ irreducibleComponents X, ∀ Z₂ ∈ irreducibleComponents X,
        x ∈ Z₁ → x ∈ Z₂ → Z₁ = Z₂ := by
  constructor
  · intro h x Z₁ h₁ Z₂ h₂ hx₁ hx₂
    have e : ∀ Z ∈ irreducibleComponents X, x ∈ Z → Z = connectedComponent x := fun Z hZ hxZ ↦
      have hsub := (hZ.1 : IsIrreducible Z).isConnected.isPreconnected.subset_connectedComponent hxZ
      le_antisymm hsub (hZ.2 (h x).1 hsub)
    rw [e Z₁ h₁ hx₁, e Z₂ h₂ hx₂]
  · intro h x
    have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
    set Z := irreducibleComponent x
    have hZ := irreducibleComponent_mem_irreducibleComponents x
    have hcompl : Zᶜ = ⋃₀ (irreducibleComponents X \ {Z}) := by
      ext y
      simp only [mem_compl_iff, mem_sUnion, mem_sdiff, mem_singleton_iff]
      constructor
      · intro hy
        exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
          fun e ↦ hy (e ▸ mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
      · rintro ⟨W, ⟨hW, hWZ⟩, hyW⟩ hyZ
        exact hWZ (h y W hW Z hZ hyW hyZ)
    have hclopen : IsClopen Z := by
      refine ⟨isClosed_irreducibleComponent, ?_⟩
      rw [← isClosed_compl_iff, hcompl]
      exact hfin.sdiff.isClosed_sUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
    have : connectedComponent x = Z := le_antisymm
      (hclopen.connectedComponent_subset mem_irreducibleComponent)
      ((hZ.1 : IsIrreducible Z).isConnected.isPreconnected.subset_connectedComponent
        mem_irreducibleComponent)
    rw [this]; exact hZ

end Buffalo.Groupes.Part03
