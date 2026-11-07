import Mathlib

/-!
# Buffalo, algebraic groups, Part 03 (a): étale schemes, `π₀`, pro-étale schemes

Entries `3ULFIl_2Wis-6157` to `3ULFIl_2Wis-8898` of `docs/buffalo-groupes/index.tex` (session of
2 July 1973, from "Étale schemes, torsors and Galois extensions" to the end of "Pro-étale and
locally profinite schemes"). Statuses in `docs/buffalo-groupes/lean/Part03.json`.

Conventions. An affine étale `k`-scheme is `Spec A` with `A` an étale `k`-algebra
(`Algebra.Etale k A`); its points over a separable closure are read through Mathlib's
`Algebra.Etale.iff_exists_algEquiv_prod` (a finite product of finite separable extensions) and
`Algebra.FormallyEtale.equivPiOfIsSepClosed`. The equivalence between étale `k`-schemes and
discrete `Gal(k_s/k)`-sets is not in Mathlib; statements made through it are proved on the algebra
side only.
-/

namespace Buffalo.Groupes.Part03

open TensorProduct IntermediateField Set Topology CategoryTheory AlgebraicGeometry

universe u

/-! ## Étale schemes, torsors and Galois extensions -/

section Etale

variable (K A B : Type u) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

/-- An étale algebra over a field is finite-dimensional (used throughout). -/
theorem etale_finite [Algebra.Etale K A] : Module.Finite K A :=
  Algebra.FormallyUnramified.finite_of_free K A

/-- An étale algebra over a field is reduced (used throughout). -/
theorem etale_isReduced [Algebra.Etale K A] : IsReduced A :=
  Algebra.FormallyUnramified.isReduced_of_field K A

/-- 3ULFIl_2Wis-6157 (1:42:37) [prop] An étale `k`-scheme is connected and non-empty if and only
if it is `Spec K` with `K` a field: for an étale `k`-algebra `A`, `A ≠ 0` without non-trivial
idempotents iff `A` is a field. -/
theorem etale_connected_iff_isField [Algebra.Etale K A] :
    (Nontrivial A ∧ ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) ↔ IsField A := by
  constructor
  · rintro ⟨hnt, hconn⟩
    obtain ⟨I, _, Ai, _, _, e, -⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
    have hI : Nonempty I := by
      by_contra h
      rw [not_nonempty_iff] at h
      exact (e.toEquiv.subsingleton).elim 0 1 |>.symm ▸ zero_ne_one (α := A) <| rfl
    obtain ⟨i⟩ := hI
    have hsub : ∀ j, j = i := by
      intro j
      by_contra hji
      classical
      have hid : IsIdempotentElem (e.symm (Pi.single i 1)) := by
        rw [IsIdempotentElem, ← map_mul]; congr 1; ext l; by_cases h : l = i
        · subst h; simp
        · simp [h]
      rcases hconn _ hid with h | h
      · have := congrArg (fun x ↦ e x i) h; simp at this
      · have := congrArg (fun x ↦ e x j) h; simp [hji] at this
    let ev : (Π j, Ai j) ≃* Ai i :=
      { toFun := fun x ↦ x i
        invFun := fun a j ↦ (hsub j) ▸ a
        left_inv := fun x ↦ by ext j; obtain rfl := hsub j; rfl
        right_inv := fun a ↦ rfl
        map_mul' := fun _ _ ↦ rfl }
    exact MulEquiv.isField (Field.toIsField (Ai i)) (e.toMulEquiv.trans ev)
  · intro h
    let := h.toField
    refine ⟨inferInstance, fun e he ↦ ?_⟩
    rcases eq_or_ne e 0 with h0 | h0
    · exact .inl h0
    · exact .inr (mul_left_cancel₀ h0 (by rw [he.eq, mul_one]))

/-- 3ULFIl_2Wis-6157 (1:42:37) [prop] ... and the fields étale over `k` are exactly the finite
separable extensions of `k`. -/
theorem field_etale_iff (L : Type u) [Field L] [Algebra K L] :
    Algebra.Etale K L ↔ Module.Finite K L ∧ Algebra.IsSeparable K L := by
  constructor
  · intro _
    exact ⟨etale_finite K L, (Algebra.FormallyEtale.iff_isSeparable K L).mp inferInstance⟩
  · rintro ⟨_, _⟩
    exact ⟨Algebra.FormallyEtale.of_isSeparable K L,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- 3ULFIl_2Wis-6289 (1:44:49) [prop] An affine (= quasi-compact connected-component-wise finite)
étale `k`-scheme has a finite set `E = X(Ω)` of geometric points, for every field `Ω`. -/
theorem etale_finite_points [Algebra.Etale K A] (Ω : Type u) [Field Ω] [Algebra K Ω] :
    Finite (A →ₐ[K] Ω) :=
  have := etale_finite K A
  Finite.algHom K A Ω

/-- 3ULFIl_2Wis-6358 (1:45:58) [prop] Finite projective limits of étale schemes are étale: the
product `Spec A ×_k Spec B = Spec (A ⊗_k B)` of two étale `k`-schemes is étale. -/
theorem etale_tensor [Algebra.Etale K A] [Algebra.Etale K B] : Algebra.Etale K (A ⊗[K] B) :=
  Algebra.Etale.comp K A (A ⊗[K] B)

/-- 3ULFIl_2Wis-6489 (1:48:09) [prop] A morphism `Spec B → Spec A` of affine étale `k`-schemes is
surjective (an epimorphism) iff `A → B` is injective. -/
theorem etale_injective_iff_comap_surjective [Algebra.Etale K A] [Algebra.Etale K B]
    (f : A →ₐ[K] B) :
    Function.Injective f ↔ Function.Surjective (PrimeSpectrum.comap f.toRingHom) := by
  constructor
  · intro hf
    refine RingHom.IsIntegral.comap_surjective (fun b ↦ ?_) hf
    have := etale_finite K B
    obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := K) b
    refine ⟨p.map (algebraMap K A), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    convert hpb using 2
    ext; simp
  · intro hs
    have := etale_isReduced K A
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hnil : a ∈ nilradical A := by
      rw [nilradical, Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro p ⟨-, hp⟩
      obtain ⟨q, hq⟩ := hs ⟨p, hp⟩
      have : a ∈ (PrimeSpectrum.comap f.toRingHom q).asIdeal := by
        show f a ∈ q.asIdeal; rw [ha]; exact q.asIdeal.zero_mem
      rwa [hq] at this
    exact (mem_nilradical.mp hnil).eq_zero

end Etale

/-- 3ULFIl_2Wis-6815 (1:53:35) [prop] A finite Galois extension `L` of `k` inside a separable
closure `k_s` gives the surjective homomorphism `π = Gal(k_s/k) → Gal(L/k)` (restriction). -/
theorem galois_restrict_surjective (K Ks : Type u) [Field K] [Field Ks] [Algebra K Ks]
    [Normal K Ks] (L : IntermediateField K Ks) [Normal K L] :
    Function.Surjective (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ks) L) :=
  AlgEquiv.restrictNormalHom_surjective Ks

/-! ## Pro-étale and locally profinite schemes -/

/-- 3ULFIl_2Wis-8163 (2:16:03) [def] An affine pro-étale `k`-scheme is `Spec A` with `A` the
(filtered) union of its finite étale subalgebras: every element lies in an étale subalgebra
(an étale algebra over a field is finite, `etale_finite`). -/
def IsIndEtale (K A : Type u) [Field K] [CommRing A] [Algebra K A] : Prop :=
  ∀ a : A, ∃ B : Subalgebra K A, Algebra.Etale K B ∧ a ∈ B

/-- 3ULFIl_2Wis-8298 (2:18:18) [prop] A `k`-algebra is ind-étale iff it is integral and separable:
the case of a field extension `L/k`. -/
theorem isIndEtale_iff_isSeparable (K L : Type u) [Field K] [Field L] [Algebra K L] :
    IsIndEtale K L ↔ Algebra.IsSeparable K L := by
  constructor
  · intro h
    refine ⟨fun a ↦ ?_⟩
    obtain ⟨B, hB, haB⟩ := h a
    have hfin : Module.Finite K B := Algebra.FormallyUnramified.finite_of_free K B
    have hfield : IsField B :=
      (Algebra.IsIntegral.isField_iff_isField (algebraMap K B).injective).mp (Field.toIsField K)
    let E := B.toIntermediateField' hfield
    have hEB : E.toSubalgebra = B := rfl
    let φ : B ≃ₐ[K] E := Subalgebra.equivOfEq _ _ hEB.symm
    have : Algebra.Etale K E := Algebra.Etale.of_equiv φ
    have : Algebra.IsSeparable K E := (Algebra.FormallyEtale.iff_isSeparable K E).mp inferInstance
    have := Algebra.IsSeparable.isSeparable K (⟨a, haB⟩ : E)
    have h2 := (isSeparable_map_iff (f := E.val) E.val.injective).mpr this
    simpa using h2
  · intro h a
    have hint : IsIntegral K a := (Algebra.IsSeparable.isSeparable K a).isIntegral
    have : FiniteDimensional K K⟮a⟯ := adjoin.finiteDimensional hint
    have : Algebra.IsSeparable K K⟮a⟯ := Algebra.IsSeparable.of_algHom K L K⟮a⟯.val
    refine ⟨K⟮a⟯.toSubalgebra, ?_, mem_adjoin_simple_self K a⟩
    exact ⟨Algebra.FormallyEtale.of_isSeparable K K⟮a⟯,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- 3ULFIl_2Wis-8360 (2:19:20) [prop] Étaleness, hence (affine) pro-étaleness of the finite
pieces, is preserved by extension of scalars `k → k'`. -/
theorem etale_baseChange (K A K' : Type u) [Field K] [CommRing A] [Algebra K A] [CommRing K']
    [Algebra K K'] [Algebra.Etale K A] : Algebra.Etale K' (K' ⊗[K] A) :=
  inferInstance

/-- 3ULFIl_2Wis-8425 (2:20:25) [thm] Over a separably closed field `k`, an affine étale scheme is
determined by its finite set of points: `A ≃ (Spec A → k)`; the finite case of the equivalence
with compact totally disconnected spaces. -/
theorem etale_sepClosed_functions (K A : Type u) [Field K] [IsSepClosed K] [CommRing A]
    [Algebra K A] [Algebra.Etale K A] : Nonempty (A ≃ₐ[K] (PrimeSpectrum A → K)) :=
  ⟨Algebra.FormallyEtale.equivPiOfIsSepClosed K A⟩

/-- 3ULFIl_2Wis-8622 (2:23:42) [def] A `k`-scheme `X` is locally profinite if every point has an
affine open neighbourhood `U` with `Γ(U, 𝒪_X)` ind-étale over `k`. -/
def IsLocallyProfinite {K : Type u} [Field K] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) : Prop :=
  ∀ x : X, ∃ U : X.Opens, AlgebraicGeometry.IsAffineOpen U ∧ x ∈ U ∧
    letI := ((f.appLE ⊤ U le_top).hom.comp
      (AlgebraicGeometry.Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    IsIndEtale K Γ(X, U)

/-- 3ULFIl_2Wis-8688 (2:24:48) [def] `p : X → P` over `k` is a `π₀(X/k)` if `P` is locally
profinite and every `k`-morphism from `X` to a locally profinite `k`-scheme factors uniquely
through `p`. -/
def IsPiZero {K : Type u} [Field K] {X P : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) (g : P ⟶ AlgebraicGeometry.Spec (.of K))
    (p : X ⟶ P) : Prop :=
  IsLocallyProfinite g ∧ p ≫ g = f ∧
    ∀ (Q : AlgebraicGeometry.Scheme.{u}) (h : Q ⟶ AlgebraicGeometry.Spec (.of K)),
      IsLocallyProfinite h → ∀ q : X ⟶ Q, q ≫ h = f → ∃! r : P ⟶ Q, r ≫ h = g ∧ p ≫ r = q

/-- 3ULFIl_2Wis-8898 (2:28:18) [prop] The connected component of a point is the intersection of
the open and closed sets containing it: proved for noetherian spaces (e.g. quasi-compact schemes
locally of finite type over a field). -/
theorem connectedComponent_eq_iInter_isClopen_of_noetherian {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] (x : X) :
    connectedComponent x = ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, Z := by
  refine (connectedComponent_subset_iInter_isClopen).antisymm ?_
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  let T := {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}
  have hT : (connectedComponent x)ᶜ = ⋃₀ T := by
    ext y
    simp only [mem_compl_iff, mem_sUnion, T, mem_ofPred_eq]
    constructor
    · intro hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h ↦ hy (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨Z, ⟨hZ, hZx⟩, hyZ⟩ hy
      apply hZx
      rw [connectedComponent_eq hy]
      exact (hZ.1 : IsIrreducible Z).isConnected.isPreconnected.subset_connectedComponent hyZ
  have hclopen : IsClopen (connectedComponent x) := by
    refine ⟨isClosed_connectedComponent, ?_⟩
    rw [← isClosed_compl_iff, hT]
    exact (hfin.subset (fun Z hZ ↦ hZ.1)).isClosed_sUnion
      fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1
  exact iInter_subset_of_subset ⟨_, hclopen, mem_connectedComponent⟩ subset_rfl

end Buffalo.Groupes.Part03
