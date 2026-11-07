import Mathlib

/-!
# Buffalo, algebraic groups, Part 01 (b): the module functors `W(M)`, `V(M)`, endomorphisms

Entries `_lTf_L0yvrU-2834` to `_lTf_L0yvrU-6070` of `docs/buffalo-groupes/index.tex` (4 June and
the beginning of 6 June 1973). Statuses in `docs/buffalo-groupes/lean/Part01.json`.

`W(M)(A) = A ⊗[k] M` and `V(M)(A) = Hom_k(M, A)`, for a `k`-module `M` and a commutative
`k`-algebra `A`; both are `A`-modules, that is modules over the ring functor `𝒪 : A ↦ A`. A
morphism of `𝒪`-modules `W(M) → W(N)` is written out as a family of `A`-linear maps natural in
`A` (`WHom`).
-/

namespace Buffalo.Groupes.Part01

open TensorProduct CategoryTheory

universe u

variable (k : Type u) [CommRing k]

/-! ## Module functors `W(M)` and `V(M)` -/

section WV

variable (M N : Type u) [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- _lTf_L0yvrU-2834 (0:47:14) [def] `W(M) : k' ↦ M ⊗_k k'`, a module over `𝒪` (written
`k' ⊗ M`, an `A`-module). -/
abbrev W (A : Type u) [CommRing A] [Algebra k A] : Type u := A ⊗[k] M

example (A : Type u) [CommRing A] [Algebra k A] : Module A (W k M A) := inferInstance

/-- `W(M)` as a functor on `k`-algebras. -/
noncomputable def WF : CommAlgCat.{u} k ⥤ Type u where
  obj A := A ⊗[k] M
  map f := TypeCat.ofHom (LinearMap.rTensor M f.hom.toLinearMap)
  map_id A := by
    ext x
    exact congrFun (congrArg DFunLike.coe (LinearMap.rTensor_id M A)) x
  map_comp f g := by
    ext x
    change _ = (LinearMap.rTensor M g.hom.toLinearMap) (LinearMap.rTensor M f.hom.toLinearMap x)
    rw [← LinearMap.rTensor_comp_apply]
    rfl

/-- _lTf_L0yvrU-2899 (0:48:19) [prop] If `M ≃ kⁿ`, `W(M)` is the standard affine space: `A ⊗ M ≃ Aⁿ`. -/
noncomputable def W_free (n : ℕ) (e : M ≃ₗ[k] (Fin n → k)) (A : Type u) [CommRing A] [Algebra k A] :
    W k M A ≃ₗ[A] (Fin n → A) :=
  (e.baseChange k A M (Fin n → k)).trans (TensorProduct.piScalarRight k A A (Fin n))

/-- _lTf_L0yvrU-4053 (1:07:33) [def] `V(M) : k' ↦ Hom_k(M, k')`, an `𝒪`-module. -/
abbrev V (A : Type u) [CommRing A] [Algebra k A] : Type u := M →ₗ[k] A

example (A : Type u) [CommRing A] [Algebra k A] : Module A (V k M A) := inferInstance

/-- _lTf_L0yvrU-4185 (1:09:45) [prop] `V(M)` is represented by the symmetric algebra `S_k(M)`
(Mathlib `SymmetricAlgebra.lift`). -/
noncomputable def V_repr (A : Type u) [CommRing A] [Algebra k A] :
    (SymmetricAlgebra k M →ₐ[k] A) ≃ V k M A :=
  (SymmetricAlgebra.lift).symm

/-- _lTf_L0yvrU-4185 (1:09:45) [prop] For `M` free (with basis indexed by `κ`), `S_k(M)` is the
polynomial algebra (Mathlib `SymmetricAlgebra.equivMvPolynomial`). -/
noncomputable def symm_free {κ : Type u} (b : Module.Basis κ k M) :
    SymmetricAlgebra k M ≃ₐ[k] MvPolynomial κ k :=
  SymmetricAlgebra.equivMvPolynomial b

/-- _lTf_L0yvrU-4324 (1:12:04) [prop] `M ↦ W(M)` is covariant: `W(g ∘ f) = W(g) ∘ W(f)` with
`W(f) = A ⊗ f`, an `A`-linear map. -/
theorem W_comp {P : Type u} [AddCommGroup P] [Module k P] (A : Type u) [CommRing A] [Algebra k A]
    (f : M →ₗ[k] N) (g : N →ₗ[k] P) :
    (g ∘ₗ f).baseChange A = g.baseChange A ∘ₗ f.baseChange A :=
  LinearMap.baseChange_comp f g

/-- _lTf_L0yvrU-4324 (1:12:04) [prop] `M ↦ V(M)` is contravariant: `V(f) = (- ∘ f)`, and
`V(g ∘ f) = V(f) ∘ V(g)`. -/
theorem V_comp {P : Type u} [AddCommGroup P] [Module k P] (A : Type u) [CommRing A] [Algebra k A]
    (f : M →ₗ[k] N) (g : N →ₗ[k] P) :
    LinearMap.lcomp k A (g ∘ₗ f) = LinearMap.lcomp k A f ∘ₗ LinearMap.lcomp k A g := rfl

/-- _lTf_L0yvrU-4641 (1:17:21) [def] The pairing `V(M) × W(M) → 𝒪`, `(f, a ⊗ m) ↦ a f(m)`,
`A`-bilinear: `V(M)(A) → Hom_A(W(M)(A), A)` (Mathlib `LinearMap.liftBaseChangeEquiv`). -/
noncomputable def pairing (A : Type u) [CommRing A] [Algebra k A] :
    V k M A ≃ₗ[A] (W k M A →ₗ[A] A) :=
  LinearMap.liftBaseChangeEquiv A

theorem pairing_tmul (A : Type u) [CommRing A] [Algebra k A] (f : V k M A) (a : A) (m : M) :
    pairing k M A f (a ⊗ₜ m) = a * f m := by
  simp [pairing]

/-- _lTf_L0yvrU-4831 (1:20:31) [thm] Biduality, first half, at each `A`: `V(M)(A)` is the
`A`-dual of `W(M)(A)` through the pairing. -/
noncomputable def V_eq_dual_W (A : Type u) [CommRing A] [Algebra k A] :
    V k M A ≃ₗ[A] Module.Dual A (W k M A) :=
  pairing k M A

/-- _lTf_L0yvrU-4960 (1:22:40) [prop] If `M` is finitely generated projective,
`W(M) ≃ V(M^∨)`: `A ⊗ M ≃ Hom_k(M^∨, A)`. -/
noncomputable def W_eq_V_dual [Module.Finite k M] [Module.Projective k M]
    (A : Type u) [CommRing A] [Algebra k A] :
    W k M A ≃ₗ[k] V k (Module.Dual k M) A :=
  ((TensorProduct.comm k A M).trans
    ((Module.evalEquiv k M).rTensor A)).trans
    (dualTensorHomEquiv k (Module.Dual k M) A)

/-- _lTf_L0yvrU-4960 (1:22:40) [prop] … hence `W(M)` is represented by `S_k(M^∨)`. -/
noncomputable def W_repr [Module.Finite k M] [Module.Projective k M]
    (A : Type u) [CommRing A] [Algebra k A] :
    (SymmetricAlgebra k (Module.Dual k M) →ₐ[k] A) ≃ W k M A :=
  (V_repr k _ A).trans (W_eq_V_dual k M A).toEquiv.symm

/-- _lTf_L0yvrU-2966 (0:49:26) [prop] If `M` is finitely generated projective, `W(M)` is
representable (by `S_k(M^∨)`), naturally in `A`. -/
noncomputable def W_corep [Module.Finite k M] [Module.Projective k M] :
    (WF k M).CorepresentableBy (CommAlgCat.of k (SymmetricAlgebra k (Module.Dual k M))) where
  homEquiv {A} := (show (CommAlgCat.of k (SymmetricAlgebra k (Module.Dual k M)) ⟶ A) ≃
      (SymmetricAlgebra k (Module.Dual k M) →ₐ[k] A) from
      ⟨fun f ↦ f.hom, CommAlgCat.ofHom, fun _ ↦ rfl, fun _ ↦ rfl⟩).trans (W_repr k M A)
  homEquiv_comp {A B} g f := by
    apply (W_eq_V_dual k M B).injective
    have key : ∀ x : A ⊗[k] M, W_eq_V_dual k M B (LinearMap.rTensor M g.hom.toLinearMap x) =
        g.hom.toLinearMap ∘ₗ W_eq_V_dual k M A x := by
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul a m => ext φ; simp [W_eq_V_dual]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LinearMap.comp_add]
    change W_eq_V_dual k M B ((W_eq_V_dual k M B).symm (V_repr k _ B (f ≫ g).hom)) =
      W_eq_V_dual k M B (LinearMap.rTensor M g.hom.toLinearMap
        ((W_eq_V_dual k M A).symm (V_repr k _ A f.hom)))
    rw [key, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rfl

/-- _lTf_L0yvrU-3290 (0:54:50) [prop] A representable functor takes injections of `k`-algebras to
injections. -/
theorem corep_injective {R A B : Type u} [CommRing R] [Algebra k R] [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (f : A →ₐ[k] B) (hf : Function.Injective f) :
    Function.Injective (fun φ : R →ₐ[k] A ↦ f.comp φ) := fun _ _ h ↦
  AlgHom.ext fun x ↦ hf (DFunLike.congr_fun h x)

/-- _lTf_L0yvrU-3352 (0:55:52) [prop] A representable functor commutes with products:
`Hom(R, ∏ A_i) ≃ ∏ Hom(R, A_i)`. -/
def corep_pi {R : Type u} [CommRing R] [Algebra k R] {ι : Type u} (A : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra k (A i)] :
    (R →ₐ[k] ∀ i, A i) ≃ ∀ i, (R →ₐ[k] A i) where
  toFun φ i := (Pi.evalAlgHom k A i).comp φ
  invFun φ := AlgHom.pi φ
  left_inv _ := rfl
  right_inv _ := rfl

/-- _lTf_L0yvrU-3352 (0:55:52) [prop] … and with arbitrary projective limits (Mathlib: corepresentable
functors preserve limits). -/
example (X : (CommAlgCat.{u} k)ᵒᵖ) : Limits.PreservesLimits (coyoneda.obj X) := inferInstance

/-- The `kᵐᵒᵖ`-module structure on a `k`-module (`k` commutative), to form square-zero extensions. -/
abbrev modOp (P : Type u) [AddCommGroup P] [Module k P] : Module kᵐᵒᵖ P :=
  Module.compHom P ((RingHom.id k).fromOpposite fun x y ↦ Commute.all x y)

/-- _lTf_L0yvrU-3486 (0:58:06) [prop] `M` is flat iff `k' ↦ k' ⊗ M` takes injections of
`k`-algebras to injections; the converse uses the square-zero extensions `k ⊕ I ⊂ k ⊕ k`. -/
theorem flat_iff_W_injective : Module.Flat k M ↔
    ∀ (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (f : A →ₐ[k] B),
      Function.Injective f → Function.Injective (LinearMap.rTensor M f.toLinearMap) := by
  constructor
  · intro _ A B _ _ _ _ f hf
    exact Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  · intro h
    rw [Module.Flat.iff_rTensor_injective']
    intro I
    have : IsCentralScalar k I := ⟨fun _ _ ↦ Subtype.ext (mul_comm _ _)⟩
    let F := TrivSqZeroExt.map (R' := k) I.subtype
    have hF : Function.Injective F := by
      intro x y hxy
      have h1 := congrArg TrivSqZeroExt.fst hxy
      have h2 := congrArg TrivSqZeroExt.snd hxy
      simp only [F, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map] at h1 h2
      exact TrivSqZeroExt.ext h1 (Subtype.val_injective h2)
    have hinj := h _ _ F hF
    have e1 : F.toLinearMap ∘ₗ TrivSqZeroExt.inrHom k I =
        TrivSqZeroExt.inrHom k k ∘ₗ I.subtype := by
      ext x <;> simp [F]
    have e2 : TrivSqZeroExt.sndHom k I ∘ₗ TrivSqZeroExt.inrHom k I = LinearMap.id := by
      ext x; rfl
    intro x y hxy
    have := congrArg (LinearMap.rTensor M (TrivSqZeroExt.inrHom k k)) hxy
    rw [← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply, ← e1,
      LinearMap.rTensor_comp_apply, LinearMap.rTensor_comp_apply] at this
    have := congrArg (LinearMap.rTensor M (TrivSqZeroExt.sndHom k I)) (hinj this)
    rwa [← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply, e2,
      LinearMap.rTensor_id_apply, LinearMap.rTensor_id_apply] at this

/-- _lTf_L0yvrU-3486 (0:58:06) [prop] … hence `W(M)` representable implies `M` flat. -/
theorem flat_of_W_corep (h : (WF k M).IsCorepresentable) : Module.Flat k M := by
  obtain ⟨R, ⟨e⟩⟩ := h
  refine (flat_iff_W_injective k M).mpr fun A B _ _ _ _ f hf ↦ ?_
  intro x y hxy
  obtain ⟨x, rfl⟩ := e.homEquiv (Y := CommAlgCat.of k A).surjective x
  obtain ⟨y, rfl⟩ := e.homEquiv (Y := CommAlgCat.of k A).surjective y
  have hx := e.homEquiv_comp (CommAlgCat.ofHom f) x
  have hy := e.homEquiv_comp (CommAlgCat.ofHom f) y
  change LinearMap.rTensor M f.toLinearMap _ = _ at hxy
  have hx' : LinearMap.rTensor M f.toLinearMap (e.homEquiv x) =
      e.homEquiv (x ≫ CommAlgCat.ofHom f) := hx.symm
  have hy' : LinearMap.rTensor M f.toLinearMap (e.homEquiv y) =
      e.homEquiv (y ≫ CommAlgCat.ofHom f) := hy.symm
  rw [hx', hy'] at hxy
  have := e.homEquiv.injective hxy
  congr 1
  apply CommAlgCat.hom_ext
  exact corep_injective k f hf (congrArg CommAlgCat.Hom.hom this)

/-- _lTf_L0yvrU-3734 (1:02:14) [prop] If `M ⊗ k^M → M^M` is onto (as it is when `W(M)` is
representable, `W(M)` then commuting with products), `M` is finitely generated: the family
`(m)_{m ∈ M}` falls into the span of finitely many elements. -/
theorem finite_of_tensor_pi_surjective
    (h : Function.Surjective (TensorProduct.piScalarRightHom k k M M)) : Module.Finite k M := by
  classical
  obtain ⟨x, hx⟩ := h id
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  refine ⟨⟨S.image Prod.fst, eq_top_iff.mpr fun m _ ↦ ?_⟩⟩
  have := congrFun hx m
  simp only [map_sum, Finset.sum_apply, TensorProduct.piScalarRightHom_tmul, id] at this
  rw [← this]
  refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hi)

/-- _lTf_L0yvrU-3734 (1:02:14) [prop] Over a noetherian ring, a finitely generated module is flat
iff it is projective (Mathlib `Module.Flat.projective_of_finitePresentation`). -/
theorem flat_iff_projective_of_noetherian [IsNoetherianRing k] [Module.Finite k M] :
    Module.Flat k M ↔ Module.Projective k M := by
  have : Module.FinitePresentation k M := Module.finitePresentation_of_finite k M
  exact ⟨fun _ ↦ Module.Flat.projective_of_finitePresentation, fun _ ↦ inferInstance⟩

/-- _lTf_L0yvrU-3227 (0:53:47) [prop] The last step of the converse: flat and finitely presented
implies finitely generated projective (Mathlib). -/
theorem projective_of_flat_fp [Module.Flat k M] [Module.FinitePresentation k M] :
    Module.Projective k M :=
  Module.Flat.projective_of_finitePresentation

/-- _lTf_L0yvrU-4261 (1:11:01) [prop] `V(M) = Spec S_k(M)` is of finite type iff `M` is finitely
generated. -/
theorem symm_finiteType_iff : Algebra.FiniteType k (SymmetricAlgebra k M) ↔ Module.Finite k M := by
  classical
  constructor
  · rintro ⟨s, hs⟩
    let _ := modOp k M
    have : IsCentralScalar k M := ⟨fun _ _ ↦ rfl⟩
    let F : SymmetricAlgebra k M →ₐ[k] TrivSqZeroExt k M :=
      SymmetricAlgebra.lift (TrivSqZeroExt.inrHom k M)
    let T : Set M := (fun x ↦ (F x).snd) '' s
    let B : Subalgebra k (TrivSqZeroExt k M) :=
      { carrier := {x | x.snd ∈ Submodule.span k T}
        mul_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_ofPred_eq, TrivSqZeroExt.snd_mul] at *
          have : MulOpposite.op b.fst • a.snd = b.fst • a.snd := rfl
          rw [this]
          exact add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ ha)
        add_mem' := fun ha hb ↦ by
          simp only [Set.mem_ofPred_eq, TrivSqZeroExt.snd_add] at *
          exact add_mem ha hb
        algebraMap_mem' := fun r ↦ by
          show (TrivSqZeroExt.inl (algebraMap k k r) : TrivSqZeroExt k M).snd ∈
            Submodule.span k T
          rw [TrivSqZeroExt.snd_inl]
          exact Submodule.zero_mem _ }
    have hle : Algebra.adjoin k (F '' s) ≤ B := Algebra.adjoin_le fun _ ⟨x, hx, hFx⟩ ↦ by
      rw [← hFx]
      exact Submodule.subset_span ⟨x, hx, rfl⟩
    refine ⟨⟨(s.image fun x ↦ (F x).snd), eq_top_iff.mpr fun m _ ↦ ?_⟩⟩
    have hm : TrivSqZeroExt.inr m ∈ Algebra.adjoin k (F '' s) := by
      rw [← AlgHom.map_adjoin, hs, Algebra.map_top]
      exact ⟨SymmetricAlgebra.ι k M m, by simp [F]⟩
    simpa [B, T] using hle hm
  · intro hM
    obtain ⟨s, hs⟩ := hM.fg_top
    refine ⟨⟨s.image (SymmetricAlgebra.ι k M), eq_top_iff.mpr fun x hx ↦ ?_⟩⟩
    clear hx
    induction x using SymmetricAlgebra.induction with
    | algebraMap r => exact Subalgebra.algebraMap_mem _ r
    | ι m =>
      have hm : m ∈ Submodule.span k (s : Set M) := hs ▸ Submodule.mem_top
      have : Submodule.span k ((SymmetricAlgebra.ι k M) '' s) ≤
          (Algebra.adjoin k ((s.image (SymmetricAlgebra.ι k M) : Finset _) : Set _)).toSubmodule := by
        rw [Submodule.span_le]
        intro y hy
        exact Algebra.subset_adjoin (by simpa using hy)
      apply this
      rw [← Submodule.map_span]
      exact Submodule.mem_map_of_mem hm
    | mul a b ha hb => exact mul_mem ha hb
    | add a b ha hb => exact add_mem ha hb

/-- _lTf_L0yvrU-4515 (1:15:15) [thm] A morphism of `𝒪`-modules `W(M) → W(N)`: `A`-linear maps
`A ⊗ M → A ⊗ N`, natural in `A`. -/
structure WHom where
  /-- the component at `A` -/
  app : ∀ (A : Type u) [CommRing A] [Algebra k A], A ⊗[k] M →ₗ[A] A ⊗[k] N
  nat : ∀ (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (x : A ⊗[k] M),
    app B (LinearMap.rTensor M f.toLinearMap x) = LinearMap.rTensor N f.toLinearMap (app A x)

variable {M N} in
/-- `W` on morphisms. -/
noncomputable def W_map (g : M →ₗ[k] N) : WHom k M N where
  app A _ _ := g.baseChange A
  nat A B _ _ _ _ f x := by
    simp only [LinearMap.baseChange_eq_lTensor]
    change (LinearMap.lTensor B g ∘ₗ LinearMap.rTensor M f.toLinearMap) x =
      (LinearMap.rTensor N f.toLinearMap ∘ₗ LinearMap.lTensor A g) x
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]

/-- _lTf_L0yvrU-4515 (1:15:15) [thm] `W` is faithful: `g` is recovered from `W(g)` at `A = k`. -/
theorem W_faithful {g g' : M →ₗ[k] N} (h : (W_map k g).app k = (W_map k g').app k) : g = g' := by
  ext m
  have := congrArg (fun φ ↦ TensorProduct.lid k N (φ (1 ⊗ₜ m))) h
  simpa [W_map] using this

/-- _lTf_L0yvrU-4515 (1:15:15) [thm] `W` is full: every morphism of `𝒪`-modules `W(M) → W(N)` is
`W(g)` for `g` its component at `k`. -/
theorem W_full (φ : WHom k M N) : ∃ g : M →ₗ[k] N, ∀ (A : Type u) [CommRing A] [Algebra k A],
    φ.app A = g.baseChange A := by
  refine ⟨(TensorProduct.lid k N).toLinearMap ∘ₗ (φ.app k).restrictScalars k ∘ₗ
    (TensorProduct.lid k M).symm.toLinearMap, fun A _ _ ↦ ?_⟩
  ext m
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearMap.baseChange_tmul, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    TensorProduct.lid_symm_apply]
  have := φ.nat k A (Algebra.ofId k A) (1 ⊗ₜ m)
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] at this
  rw [this]
  generalize φ.app k (1 ⊗ₜ[k] m) = y
  induction y using TensorProduct.inductionOn with
  | tmul c n => simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy => rw [map_add, hx, hy, map_add, tmul_add]

end WV

/-! ## Endomorphism and automorphism functors -/

section End

variable (M N : Type u) [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  (A : Type u) [CommRing A] [Algebra k A]

/-- _lTf_L0yvrU-5101 (1:25:01) [prop] The value at `A` of `k' ↦ Hom_{k'}(M_{k'}, N_{k'})` is
`Hom_k(M, A ⊗ N)`, the module of `𝒪`-linear maps `W(M) → W(N)` restricted to `A`-algebras
(by `W_full` over the base `A`). -/
noncomputable def homW_eq : (A ⊗[k] M →ₗ[A] A ⊗[k] N) ≃ₗ[A] (M →ₗ[k] A ⊗[k] N) :=
  (LinearMap.liftBaseChangeEquiv A).symm

/-- _lTf_L0yvrU-5166 (1:26:06) [ex] For `M = k` this functor is `W(N)`. -/
noncomputable def homW_k : (A ⊗[k] k →ₗ[A] A ⊗[k] N) ≃ₗ[A] A ⊗[k] N :=
  (LinearEquiv.congrLeft (A ⊗[k] N) A (AlgebraTensorModule.rid k A A)).trans
    (LinearMap.ringLmapEquivSelf A A (A ⊗[k] N))

/-- _lTf_L0yvrU-5230 (1:27:10) [prop] If `N` is finitely generated projective,
`Hom_A(A ⊗ M, A ⊗ N) ≃ V(M ⊗ N^∨)(A) = Hom_k(M ⊗ N^∨, A)`. -/
noncomputable def homW_eq_V [Module.Finite k N] [Module.Projective k N] :
    (A ⊗[k] M →ₗ[A] A ⊗[k] N) ≃ₗ[k] V k (M ⊗[k] Module.Dual k N) A :=
  ((homW_eq k M N A).restrictScalars k).trans
    ((LinearEquiv.congrRight (W_eq_V_dual k N A)).trans
      (TensorProduct.lift.equiv (RingHom.id k) M (Module.Dual k N) A))

/-- _lTf_L0yvrU-5230 (1:27:10) [prop] … represented by `S_k(M ⊗ N^∨)`. -/
noncomputable def homW_repr [Module.Finite k N] [Module.Projective k N] :
    (SymmetricAlgebra k (M ⊗[k] Module.Dual k N) →ₐ[k] A) ≃ (A ⊗[k] M →ₗ[A] A ⊗[k] N) :=
  (V_repr k _ A).trans (homW_eq_V k M N A).toEquiv.symm

/-- _lTf_L0yvrU-5556 (1:32:36) [prop] For `N` finitely generated projective, `End(N_A)` is an
`A`-algebra (non-commutative in general), and `End(N)` is represented by `S_k(N ⊗ N^∨)`. -/
noncomputable def end_repr [Module.Finite k N] [Module.Projective k N] :
    (SymmetricAlgebra k (N ⊗[k] Module.Dual k N) →ₐ[k] A) ≃ Module.End A (A ⊗[k] N) :=
  homW_repr k N N A

example : Algebra A (Module.End A (A ⊗[k] N)) := inferInstance

/-- _lTf_L0yvrU-5749 (1:35:49) [prop] The invertible elements of a monoid are the pairs `(x, y)`
with `xy = 1` and `yx = 1` (the equalizer description, pointwise). -/
def unitsEquivPairs (R : Type*) [Monoid R] : Rˣ ≃ {p : R × R // p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} where
  toFun u := ⟨(u, ↑u⁻¹), u.mul_inv, u.inv_mul⟩
  invFun p := ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- _lTf_L0yvrU-5940 (1:39:00) [prop] `Aut(N)(A) = End(N_A)ˣ`: the units of the endomorphism
algebra are the automorphisms (Mathlib `LinearMap.GeneralLinearGroup.generalLinearEquiv`). -/
noncomputable def aut_eq_units : (Module.End A (A ⊗[k] N))ˣ ≃* (A ⊗[k] N ≃ₗ[A] A ⊗[k] N) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[k] N)

/-- _lTf_L0yvrU-6070 (1:41:10) [prop] An endomorphism of a finitely generated free module is
invertible iff its determinant is (Mathlib `LinearMap.isUnit_iff_isUnit_det`). -/
theorem isUnit_iff_det (P : Type*) [AddCommGroup P] [Module A P] [Module.Finite A P]
    [Module.Free A P] (f : Module.End A P) : IsUnit f ↔ IsUnit (LinearMap.det f) :=
  LinearMap.isUnit_iff_isUnit_det f

end End

end Buffalo.Groupes.Part01
