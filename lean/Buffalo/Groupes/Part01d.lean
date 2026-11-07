import Mathlib

/-!
# Buffalo, algebraic groups, Part 01 (d): diagonalizable groups, Hopf algebras, comodules

Entries `_lTf_L0yvrU-8101` to `_lTf_L0yvrU-21055` of `docs/buffalo-groupes/index.tex` (11 and
13 June 1973). Statuses in `docs/buffalo-groupes/lean/Part01.json`.

A point of `Spec A` with values in `R` is a `k`-algebra map `A → R`; the product of two affine
spaces is `Spec (A ⊗ B)` (`tensorPoints`), and the law of a group `Spec A` on points is Mathlib's
convolution product on `WithConv (A →ₐ[k] R)`.
-/

namespace Buffalo.Groupes.Part01

open TensorProduct WithConv

universe u

variable (k : Type u) [CommRing k]

/-! ## Diagonalizable groups -/

/-- _lTf_L0yvrU-8101 (2:15:01) [def] `D(M)(A) = Hom(M, Aˣ)` (the abelian group `M` written
multiplicatively), a commutative group, contravariant in `M`. -/
abbrev D (M : Type*) [AddCommGroup M] (A : Type*) [CommRing A] := Multiplicative M →* Aˣ

example (M : Type*) [AddCommGroup M] (A : Type*) [CommRing A] : CommGroup (D M A) := inferInstance

/-- `D` is contravariant in `M`. -/
def D_map {M N : Type*} [AddCommGroup M] [AddCommGroup N] (f : M →+ N) (A : Type*) [CommRing A] :
    D N A →* D M A where
  toFun φ := φ.comp (AddMonoidHom.toMultiplicative f)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- _lTf_L0yvrU-8234 (2:17:14) [prop] `D(ℤ) = 𝔾_m`. -/
def D_int (A : Type*) [CommRing A] : D ℤ A ≃ Aˣ := (zpowersHom Aˣ).symm

/-- _lTf_L0yvrU-8234 (2:17:14) [prop] `D(M ⊕ N) ≃ D(M) × D(N)`. -/
def D_prod (M N : Type*) [AddCommGroup M] [AddCommGroup N] (A : Type*) [CommRing A] :
    D (M × N) A ≃ D M A × D N A where
  toFun φ := (φ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M N)),
    φ.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M N)))
  invFun p := (p.1.coprod p.2).comp
    (MulEquiv.toMonoidHom (MulEquiv.prodMultiplicative M N))
  left_inv φ := MonoidHom.ext fun x ↦ by
    have hx : x = Multiplicative.ofAdd (x.toAdd.1, 0) * Multiplicative.ofAdd (0, x.toAdd.2) := by
      rw [← ofAdd_add]; simp
    conv_rhs => rw [hx, map_mul]
    rfl
  right_inv p := Prod.ext (MonoidHom.ext fun a ↦ by simp [MulEquiv.prodMultiplicative])
    (MonoidHom.ext fun a ↦ by simp [MulEquiv.prodMultiplicative])

/-- _lTf_L0yvrU-8368 (2:19:28) [def] The group algebra `k[M]`: basis `e^m`, `e^m e^{m'} = e^{m+m'}`
(Mathlib `AddMonoidAlgebra`). -/
theorem groupAlgebra_mul (M : Type*) [AddCommGroup M] (m m' : M) :
    (AddMonoidAlgebra.single m 1 : AddMonoidAlgebra k M) * AddMonoidAlgebra.single m' 1 =
      AddMonoidAlgebra.single (m + m') 1 := by
  rw [AddMonoidAlgebra.single_mul_single, mul_one]

/-- _lTf_L0yvrU-8563 (2:22:43) [prop] `D(M)` is represented by `k[M]`:
`Hom_{k-alg}(k[M], A) ≃ Hom(M, Aˣ)` (Mathlib `AddMonoidAlgebra.lift`); for `M = ℤ`, `k[M]` is
`k[t, t⁻¹]` by definition (`LaurentPolynomial`). -/
noncomputable def D_repr (M : Type*) [AddCommGroup M] (A : Type*) [CommRing A] [Algebra k A] :
    (AddMonoidAlgebra k M →ₐ[k] A) ≃ D M A :=
  (AddMonoidAlgebra.lift k A M).symm.trans
    { toFun φ := φ.toHomUnits
      invFun ψ := (Units.coeHom A).comp ψ
      left_inv _ := rfl
      right_inv _ := by ext; rfl }

example : LaurentPolynomial k = AddMonoidAlgebra k ℤ := rfl

/-- _lTf_L0yvrU-8704 (2:25:04) [thm] One half: if `M` is a quotient of `ℤ^r` (finitely
generated), `D(M)` is a subgroup of `D(ℤ^r) = 𝔾_m^r`, on points (and `k[ℤ^r] → k[M]` is onto,
so the inclusion is closed). -/
theorem D_injective_of_surjective {M N : Type*} [AddCommGroup M] [AddCommGroup N] (f : M →+ N)
    (hf : Function.Surjective f) (A : Type*) [CommRing A] : Function.Injective (D_map f A) := by
  intro φ ψ h
  ext x
  obtain ⟨y, rfl⟩ := hf x
  exact congrArg Units.val (DFunLike.congr_fun h (Multiplicative.ofAdd y))

theorem groupAlgebra_surjective {M N : Type*} [AddCommGroup M] [AddCommGroup N] (f : M →+ N)
    (hf : Function.Surjective f) :
    Function.Surjective (AddMonoidAlgebra.mapDomainAlgHom k k f) := by
  intro x
  induction x using AddMonoidAlgebra.induction_on with
  | of n =>
    obtain ⟨m, rfl⟩ := hf n
    exact ⟨AddMonoidAlgebra.of k M (Multiplicative.ofAdd m), by simp⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
  | smul r x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨r • a, map_smul _ _ _⟩

/-- _lTf_L0yvrU-8833 (2:27:13) [def] A group functor is radicial (infinitesimal) if its groups of
points over reduced algebras are trivial (`μ_p`, `α_p`: `mu_p_trivial`, `alpha_reduced`). -/
def IsRadicial (G : CategoryTheory.Functor (CommAlgCat.{u} k) GrpCat.{u}) : Prop :=
  ∀ A : CommAlgCat.{u} k, IsReduced A → Subsingleton (G.obj A)

/-! ## Group laws as comultiplications -/

/-- _lTf_L0yvrU-9346 (2:35:46) [prop] Points of `Spec A × Spec B = Spec (A ⊗ B)`: pairs of points
(the tensor product is the coproduct of commutative algebras). With Yoneda, a composition law on
`Spec A` is a homomorphism `A → A ⊗ A`, an action on `Spec B` a homomorphism `B → A ⊗ B`. -/
noncomputable def tensorPoints (A B R : Type u) [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] [CommRing R] [Algebra k R] :
    (A ⊗[k] B →ₐ[k] R) ≃ (A →ₐ[k] R) × (B →ₐ[k] R) where
  toFun φ := (φ.comp Algebra.TensorProduct.includeLeft, φ.comp Algebra.TensorProduct.includeRight)
  invFun p := Algebra.TensorProduct.lift p.1 p.2 fun _ _ ↦ Commute.all _ _
  left_inv φ := Algebra.TensorProduct.ext' fun a b ↦ by simp [← map_mul]
  right_inv p := Prod.ext (AlgHom.ext fun a ↦ by simp) (AlgHom.ext fun b ↦ by simp)

/-- _lTf_L0yvrU-9346 (2:35:46) [prop] In Mathlib's affine schemes `(CommAlgCat k)ᵒᵖ`, the
product is `⊗`, so a law `X × X → X` on `X = Spec A` is literally `A ⟶ A ⊗ A`. -/
example (A : CommAlgCat.{u} k) :
    (CategoryTheory.MonoidalCategory.tensorObj (Opposite.op A) (Opposite.op A) ⟶ Opposite.op A) ≃
      (A ⟶ CategoryTheory.MonoidalCategory.tensorObj A A) :=
  Quiver.Hom.opEquiv.symm

/-- _lTf_L0yvrU-9603 (2:40:03) [prop] Group (monoid) laws on affine schemes are the same as
(co)associative counital comultiplications: Mathlib's equivalence between commutative bialgebras
and monoid objects of affine schemes; likewise Hopf algebras and group objects. -/
noncomputable def bialg_equiv_mon :
    CommBialgCat.{u} k ≌ (CategoryTheory.Mon (CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ :=
  commBialgCatEquivComonCommAlgCat k

/-- _lTf_L0yvrU-10378 (2:52:58) [thm] Group structures on `Spec A` = Hopf algebra structures on `A`
(Mathlib `commHopfAlgCatEquivCogrpCommAlgCat`). -/
noncomputable def hopf_equiv_grp :
    CommHopfAlgCat.{u} k ≌ (CategoryTheory.Grp (CommAlgCat.{u} k)ᵒᵖ)ᵒᵖ :=
  commHopfAlgCatEquivCogrpCommAlgCat k

/-- _lTf_L0yvrU-9735 (2:42:15) [prop] A section of `Spec A` over the final object `Spec k` is an
augmentation `A → k`. -/
def sections_eq_augmentations (A : CommAlgCat.{u} k) :
    (Opposite.op (CommAlgCat.of k k) ⟶ Opposite.op A) ≃ (A →ₐ[k] k) where
  toFun f := f.unop.hom
  invFun ε := (CommAlgCat.ofHom ε).op
  left_inv _ := rfl
  right_inv _ := rfl

/-- _lTf_L0yvrU-9927 (2:45:27) [prop] A counit of a comultiplication is unique: if `ε` is a left
and `ε'` a right counit of `π`, then `ε = ε'` (also _lTf_L0yvrU-10706). -/
theorem counit_unique {C : Type*} [AddCommGroup C] [Module k C] (π : C →ₗ[k] C ⊗[k] C)
    (ε ε' : C →ₗ[k] k)
    (hl : (TensorProduct.lid k C).toLinearMap ∘ₗ ε.rTensor C ∘ₗ π = LinearMap.id)
    (hr : (TensorProduct.rid k C).toLinearMap ∘ₗ ε'.lTensor C ∘ₗ π = LinearMap.id) :
    ε = ε' := by
  have key : ∀ x : C ⊗[k] C, ε' (TensorProduct.lid k C (ε.rTensor C x)) =
      ε (TensorProduct.rid k C (ε'.lTensor C x)) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  ext c
  have h1 := congrArg (fun f ↦ ε' (f c)) hl
  have h2 := congrArg (fun f ↦ ε (f c)) hr
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.id_coe,
    id_eq] at h1 h2
  rw [← h2, ← key, h1]

/-- _lTf_L0yvrU-10053 (2:47:33) [prop] The law is commutative iff `τ ∘ π = π`: if the
comultiplication is cocommutative, the group of points is commutative (Mathlib instance) … -/
noncomputable example {C : Type u} [CommRing C] [Bialgebra k C] [Coalgebra.IsCocomm k C] (R : Type u)
    [CommRing R] [Algebra k R] : CommMonoid (WithConv (C →ₐ[k] R)) := inferInstance

/-- _lTf_L0yvrU-10053 (2:47:33) [prop] … and conversely: commutativity of the law on the points
with values in `C ⊗ C` (at the two universal points) gives `τ ∘ π = π`. -/
theorem cocomm_of_comm {C : Type u} [CommRing C] [Bialgebra k C]
    (h : ∀ f g : WithConv (C →ₐ[k] C ⊗[k] C), f * g = g * f) :
    (TensorProduct.comm k C C).toLinearMap ∘ₗ Coalgebra.comul = Coalgebra.comul := by
  have e := DFunLike.congr_fun (congrArg ofConv
    (h (toConv Algebra.TensorProduct.includeLeft) (toConv Algebra.TensorProduct.includeRight)))
  ext c
  have hc := e c
  simp only [AlgHom.convMul_apply] at hc
  have k1 : ∀ x : C ⊗[k] C, Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (S := k))
      (Algebra.TensorProduct.includeRight (A := C)) (fun _ _ ↦ Commute.all _ _) x = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have k2 : ∀ x : C ⊗[k] C, Algebra.TensorProduct.lift (Algebra.TensorProduct.includeRight (A := C))
      (Algebra.TensorProduct.includeLeft (S := k)) (fun _ _ ↦ Commute.all _ _) x =
        TensorProduct.comm k C C x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← k2 (Coalgebra.comul c), ← hc, k1]

/-- _lTf_L0yvrU-10309 (2:51:49) [prop] The inverse map is unique, and a one-sided identity
`m ∘ (id ⊗ σ) ∘ π = η ∘ ε` already determines it: it is the antipode (Mathlib
`eq_antipode_of_id_convMul_eq_one`). -/
theorem antipode_unique {C : Type u} [Semiring C] [HopfAlgebra k C] {σ : C →ₗ[k] C}
    (h : toConv LinearMap.id * toConv σ = 1) : σ = HopfAlgebra.antipode k :=
  HopfAlgebra.eq_antipode_of_id_convMul_eq_one h

/-- _lTf_L0yvrU-10706 (2:58:26) [def] A coalgebra: Mathlib `Coalgebra` (coassociative
comultiplication with counit; the counit is unique, `counit_unique`). -/
example (C : Type u) [AddCommGroup C] [Module k C] [Coalgebra k C] :
    (TensorProduct.lid k C).toLinearMap ∘ₗ (Coalgebra.counit (R := k) (A := C)).rTensor C ∘ₗ
      Coalgebra.comul = LinearMap.id :=
  by ext c; simp

/-- _lTf_L0yvrU-10811 (3:00:11) [def] A bialgebra: Mathlib `Bialgebra` (comultiplication and
counit algebra homomorphisms). -/
example (C : Type u) [CommRing C] [Bialgebra k C] : C →ₐ[k] C ⊗[k] C := Bialgebra.comulAlgHom k C

/-! ## Actions and comodules -/

/-- _lTf_L0yvrU-18942 (5:15:42) [def] A (right) comodule over a coalgebra `A`: `δ : M → M ⊗ A`
with `(id ⊗ ε) ∘ δ = id` and `(id ⊗ π) ∘ δ = (δ ⊗ id) ∘ δ` (up to associativity). -/
structure IsComodule (A M : Type u) [AddCommGroup A] [Module k A] [Coalgebra k A]
    [AddCommGroup M] [Module k M] (δ : M →ₗ[k] M ⊗[k] A) : Prop where
  counit : (TensorProduct.rid k M).toLinearMap ∘ₗ (Coalgebra.counit (R := k) (A := A)).lTensor M ∘ₗ
    δ = LinearMap.id
  coassoc : (Coalgebra.comul (R := k) (A := A)).lTensor M ∘ₗ δ =
    (TensorProduct.assoc k M A A).toLinearMap ∘ₗ δ.rTensor A ∘ₗ δ

/-- _lTf_L0yvrU-19801 (5:30:01) [def] The algebra of distributions `H = A^∨` of a coalgebra `A`:
the dual with the convolution product (Mathlib `WithConv`), a `k`-algebra. -/
noncomputable example (A : Type u) [AddCommGroup A] [Module k A] [Coalgebra k A] :
    Algebra k (WithConv (A →ₗ[k] k)) := inferInstance

/-- _lTf_L0yvrU-19072 (5:17:52) [prop] One direction: a coalgebra structure on `A` makes
`V(A)(k') = Hom_k(A, k')` an algebra over `k'`, for every `k'` (convolution). -/
noncomputable example (A : Type u) [AddCommGroup A] [Module k A] [Coalgebra k A] (R : Type u) [CommRing R]
    [Algebra k R] : Algebra R (WithConv (A →ₗ[k] R)) := inferInstance

/-- _lTf_L0yvrU-11735 (3:15:35) [ex] The comultiplication `t ↦ t ⊗ 1 + 1 ⊗ t` of `k[t]` gives
the addition of `𝔾_a`: at points `t ↦ a`, `t ↦ b`, it is `t ↦ a + b`. -/
theorem Ga_comul (R : Type u) [CommRing R] [Algebra k R] (a b : R) :
    Algebra.TensorProduct.lift (Polynomial.aeval (R := k) a) (Polynomial.aeval (R := k) b)
      (fun _ _ ↦ Commute.all _ _)
      (Polynomial.X ⊗ₜ 1 + 1 ⊗ₜ Polynomial.X) = a + b := by
  simp

/-- _lTf_L0yvrU-11993 (3:19:53) [ex] The comultiplication `t ↦ t ⊗ t` of `k[t, t⁻¹]` gives the
multiplication of `𝔾_m`: at points `t ↦ a`, `t ↦ b` (here on `k[t]`), it is `t ↦ ab`; and it is
Mathlib's comultiplication of the group algebra `k[ℤ]` (`T ↦ T ⊗ T`). -/
theorem Gm_comul (R : Type u) [CommRing R] [Algebra k R] (a b : R) :
    Algebra.TensorProduct.lift (Polynomial.aeval (R := k) a) (Polynomial.aeval (R := k) b)
      (fun _ _ ↦ Commute.all _ _)
      (Polynomial.X ⊗ₜ Polynomial.X) = a * b := by
  simp

theorem Gm_comul_laurent :
    Coalgebra.comul (R := k) (LaurentPolynomial.T 1 : LaurentPolynomial k) =
      LaurentPolynomial.T 1 ⊗ₜ LaurentPolynomial.T 1 := by
  exact AddMonoidAlgebra.comul_single 1 1

end Buffalo.Groupes.Part01
