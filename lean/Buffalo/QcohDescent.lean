import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Descent of morphisms of modules along a pure ring map (Buffalo 1973, Theorem A, affine core)

At 6:26:20 of the video `3ULFIl_2Wis` (`docs/buffalo-groupes/index.tex`, line 504;
`docs/buffalo-ag/index.tex`, line 1254) a listener asks why the topology is not defined by all
universal effective epimorphisms. Theorem A of the open-problems article
(`docs/buffalo-open/article.tex`) says that every universal effective epimorphism of schemes is
a descent morphism for quasi-coherent sheaves: pullback is fully faithful into descent data.
This file proves its affine core.

Setting. `A → B` is a map of commutative rings; tensor products are over `A`, with `B` on the
left. For an `A`-module `N`, condition (c) (`IsEqualizer A B N`) says that
`N → B ⊗ N ⇉ (B ⊗ B) ⊗ N`, `n ↦ 1 ⊗ n`, with the two arrows `b ⊗ n ↦ (b ⊗ 1) ⊗ n` and
`b ⊗ n ↦ (1 ⊗ b) ⊗ n` (`coface₁`, `coface₂`), is an equalizer. A morphism of descent data
`B ⊗ M → B ⊗ N` (for the canonical descent data) is a `B`-linear `g` whose two base changes to
`B ⊗ B`, along `b ↦ b ⊗ 1` and `b ↦ 1 ⊗ b`, agree as maps `(B ⊗ B) ⊗ M → (B ⊗ B) ⊗ N`
(`pullLeft g = pullRight g`, `Compatible g`); the canonical descent isomorphisms are the
identity in this description.

What is proved.
* `descend_bijective`: under (c) for `N`, base change `f ↦ f.baseChange B` is a bijection from
  `M →ₗ[A] N` onto the compatible `g : B ⊗ M →ₗ[B] B ⊗ N`, for every `A`-module `M`
  (Theorem A for `Spec B → Spec A`).
* `isEqualizer_iff_bijective`: conversely, bijectivity for `M = A` alone gives (c) for `N`; so
  `A → B` is a descent morphism for modules (full faithfulness) exactly when (c) holds.
* `isEqualizer_of_injective`, `equalizerCondition_iff_isPure`: (c) for every module is
  equivalent to `A → B` being pure (universally injective), the direction « pure ⇒ (c) » by the
  homotopy `(b₁ ⊗ b₂) ⊗ n ↦ b₂ ⊗ [b₁ ⊗ n]` to `B ⊗ coker(N → B ⊗ N)`, as in Stacks 08WE.
* `descend_bijective_of_isPure`: the same full faithfulness for a pure map `A → B`.

The proof is shorter than the note's: a `B`-linear `g` is determined by the `A`-linear
`m ↦ g (1 ⊗ m)`, and `g` is compatible exactly when this map lands in the equalizer of
`B ⊗ N ⇉ (B ⊗ B) ⊗ N`, which is `N` by (c). The presentation of `M` is not needed.

What is not proved.
* The equivalence of (c) with « `Spec B → Spec A` is a universal effective epimorphism » (Stacks,
  Lemma 0EUA): schemes, effective epimorphisms and the test object `𝔸¹` are not modelled.
* Effectivity of descent along a pure map (Stacks, Theorem 08XA; Joyal–Tierney; B. Mesablishvili,
  « Pure morphisms of commutative rings are effective descent morphisms for modules », TAC 7
  (2000)): only full faithfulness is proved here.
* The scheme-level statement for a non-affine universal effective epimorphism `X → Y`
  (Zariski-localisation on `Y` and the square-zero extension `Spec(𝒪_Y ⊕ F)` of the note).
* Theorems B and C of the article.
-/

open TensorProduct

namespace Buffalo.QcohDescent

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
variable (M N : Type*) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- `b ⊗ n ↦ (b ⊗ 1) ⊗ n`. -/
noncomputable def coface₁ : B ⊗[A] N →ₗ[A] (B ⊗[A] B) ⊗[A] N :=
  (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := B)).toLinearMap.rTensor N

/-- `b ⊗ n ↦ (1 ⊗ b) ⊗ n`. -/
noncomputable def coface₂ : B ⊗[A] N →ₗ[A] (B ⊗[A] B) ⊗[A] N :=
  (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toLinearMap.rTensor N

@[simp] lemma coface₁_tmul (b : B) (n : N) :
    coface₁ A B N (b ⊗ₜ n) = (b ⊗ₜ (1 : B)) ⊗ₜ n := rfl

@[simp] lemma coface₂_tmul (b : B) (n : N) :
    coface₂ A B N (b ⊗ₜ n) = ((1 : B) ⊗ₜ b) ⊗ₜ n := rfl


/-- Condition (c) for the module `N`: `N → B ⊗ N ⇉ (B ⊗ B) ⊗ N` is an equalizer. -/
def IsEqualizer : Prop :=
  Function.Injective (TensorProduct.mk A B N 1) ∧
    ∀ x : B ⊗[A] N, coface₁ A B N x = coface₂ A B N x → ∃ n : N, 1 ⊗ₜ n = x

variable {A B M N}

/-- The base change of `g` along `B → B ⊗ B`, `b ↦ 1 ⊗ b`, written on `(B ⊗ B) ⊗ M`. -/
noncomputable def pullRight (g : B ⊗[A] M →ₗ[B] B ⊗[A] N) :
    (B ⊗[A] B) ⊗[A] M →ₗ[A] (B ⊗[A] B) ⊗[A] N :=
  (TensorProduct.assoc A B B N).symm.toLinearMap ∘ₗ (g.restrictScalars A).lTensor B ∘ₗ
    (TensorProduct.assoc A B B M).toLinearMap

/-- The base change of `g` along `B → B ⊗ B`, `b ↦ b ⊗ 1`, written on `(B ⊗ B) ⊗ M`. -/
noncomputable def pullLeft (g : B ⊗[A] M →ₗ[B] B ⊗[A] N) :
    (B ⊗[A] B) ⊗[A] M →ₗ[A] (B ⊗[A] B) ⊗[A] N :=
  (TensorProduct.comm A B B).toLinearMap.rTensor N ∘ₗ pullRight g ∘ₗ
    (TensorProduct.comm A B B).toLinearMap.rTensor M

lemma pullRight_tmul (g : B ⊗[A] M →ₗ[B] B ⊗[A] N) (b₁ b₂ : B) (m : M) :
    pullRight g ((b₁ ⊗ₜ b₂) ⊗ₜ m) = (b₁ ⊗ₜ[A] b₂) • coface₂ A B N (g (1 ⊗ₜ m)) := by
  have : b₂ ⊗ₜ[A] m = b₂ • ((1 : B) ⊗ₜ[A] m) := by rw [smul_tmul', smul_eq_mul, mul_one]
  simp only [pullRight, LinearMap.comp_apply, LinearEquiv.coe_coe, assoc_tmul,
    LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, this, map_smul]
  generalize g (1 ⊗ₜ m) = x
  induction x with
  | tmul c n => simp [smul_tmul', Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp [tmul_add, smul_add, hx, hy]


lemma pullLeft_tmul (g : B ⊗[A] M →ₗ[B] B ⊗[A] N) (b₁ b₂ : B) (m : M) :
    pullLeft g ((b₁ ⊗ₜ b₂) ⊗ₜ m) = (b₁ ⊗ₜ[A] b₂) • coface₁ A B N (g (1 ⊗ₜ m)) := by
  simp only [pullLeft, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, pullRight_tmul]
  generalize g (1 ⊗ₜ m) = x
  induction x with
  | tmul c n => simp [smul_tmul', Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- A morphism `g : B ⊗ M → B ⊗ N` of `B`-modules is compatible with the canonical descent data
when its two base changes to `B ⊗ B` agree. -/
def Compatible (g : B ⊗[A] M →ₗ[B] B ⊗[A] N) : Prop :=
  pullLeft g = pullRight g

lemma compatible_iff (g : B ⊗[A] M →ₗ[B] B ⊗[A] N) :
    Compatible g ↔ ∀ m : M, coface₁ A B N (g (1 ⊗ₜ m)) = coface₂ A B N (g (1 ⊗ₜ m)) := by
  refine ⟨fun h m ↦ ?_, fun h ↦ TensorProduct.ext_threefold fun b₁ b₂ m ↦ ?_⟩
  · have := LinearMap.congr_fun h ((1 ⊗ₜ 1) ⊗ₜ m)
    rwa [pullLeft_tmul, pullRight_tmul, ← Algebra.TensorProduct.one_def, one_smul,
      one_smul] at this
  · rw [pullLeft_tmul, pullRight_tmul, h]

lemma compatible_baseChange (f : M →ₗ[A] N) : Compatible (f.baseChange B) := by
  simp [compatible_iff]

variable (B) in
/-- Base change, from `A`-linear maps `M → N` to the morphisms of descent data. -/
noncomputable def descend (f : M →ₗ[A] N) :
    {g : B ⊗[A] M →ₗ[B] B ⊗[A] N // Compatible g} :=
  ⟨f.baseChange B, compatible_baseChange f⟩


/-- Two `B`-linear maps out of `B ⊗ M` agree once they agree on the `1 ⊗ m`. -/
lemma ext_one_tmul {P : Type*} [AddCommGroup P] [Module B P] {g g' : B ⊗[A] M →ₗ[B] P}
    (h : ∀ m : M, g (1 ⊗ₜ m) = g' (1 ⊗ₜ m)) : g = g' := by
  ext x
  induction x with
  | tmul b m =>
    have : b ⊗ₜ[A] m = b • ((1 : B) ⊗ₜ[A] m) := by rw [smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **Theorem A, affine case.** If `N → B ⊗ N ⇉ (B ⊗ B) ⊗ N` is an equalizer, base change
`Hom_A(M, N) → Hom_{Des}(B ⊗ M, B ⊗ N)` is a bijection, for every `A`-module `M`. -/
theorem descend_bijective (hN : IsEqualizer A B N) :
    Function.Bijective (descend B : (M →ₗ[A] N) → _) := by
  obtain ⟨hinj, hex⟩ := hN
  refine ⟨fun f f' h ↦ LinearMap.ext fun m ↦ hinj ?_, fun ⟨g, hg⟩ ↦ ?_⟩
  · simpa [descend] using LinearMap.congr_fun (congrArg Subtype.val h) (1 ⊗ₜ m)
  · let ι := TensorProduct.mk A B N 1
    let φ : M →ₗ[A] B ⊗[A] N := g.restrictScalars A ∘ₗ TensorProduct.mk A B M 1
    have hφ : ∀ m, φ m ∈ LinearMap.range ι := fun m ↦ by
      obtain ⟨n, hn⟩ := hex _ ((compatible_iff g).1 hg m)
      exact ⟨n, hn⟩
    let f : M →ₗ[A] N := (LinearEquiv.ofInjective ι hinj).symm.toLinearMap ∘ₗ φ.codRestrict _ hφ
    have hf : ∀ m, (1 : B) ⊗ₜ f m = g (1 ⊗ₜ m) := fun m ↦ by
      have := congrArg Subtype.val
        ((LinearEquiv.ofInjective ι hinj).apply_symm_apply (φ.codRestrict _ hφ m))
      rw [LinearEquiv.ofInjective_apply] at this
      exact this
    exact ⟨f, Subtype.ext (ext_one_tmul fun m ↦ by simpa [descend] using hf m)⟩


/-- Conversely, bijectivity for `M = A` alone gives condition (c) for `N`: `A → B` is a descent
morphism for modules (in the sense of full faithfulness) exactly when (c) holds. -/
theorem isEqualizer_iff_bijective :
    IsEqualizer A B N ↔ Function.Bijective (descend B : (A →ₗ[A] N) → _) := by
  refine ⟨descend_bijective, fun ⟨hinj, hsurj⟩ ↦ ⟨fun n n' h ↦ ?_, fun x hx ↦ ?_⟩⟩
  · have key : descend B (LinearMap.toSpanSingleton A N n) =
        descend B (LinearMap.toSpanSingleton A N n') :=
      Subtype.ext <| ext_one_tmul fun a ↦ by
        simp only [descend, LinearMap.baseChange_tmul, LinearMap.toSpanSingleton_apply, tmul_smul]
        exact congrArg (a • ·) h
    simpa using LinearMap.congr_fun (hinj key) 1
  · let g : B ⊗[A] A →ₗ[B] B ⊗[A] N :=
      LinearMap.toSpanSingleton B _ x ∘ₗ (AlgebraTensorModule.rid A B B).toLinearMap
    have hg1 : ∀ a : A, g (1 ⊗ₜ a) = a • x := fun a ↦ by
      simp [g, AlgebraTensorModule.rid_tmul]
    have hg : Compatible g := (compatible_iff g).2 fun a ↦ by
      rw [hg1, map_smul, map_smul, hx]
    obtain ⟨f, hf⟩ := hsurj ⟨g, hg⟩
    refine ⟨f 1, ?_⟩
    have := LinearMap.congr_fun (congrArg Subtype.val hf) (1 ⊗ₜ 1)
    simpa [descend, hg1] using this


/-- The map `(b₁ ⊗ b₂) ⊗ n ↦ b₂ ⊗ [b₁ ⊗ n]` to `B ⊗ Q`, where `Q` is the cokernel of
`N → B ⊗ N`. It turns `coface₁ - coface₂` into `Q → B ⊗ Q`. -/
noncomputable def homotopy :
    (B ⊗[A] B) ⊗[A] N →ₗ[A] B ⊗[A] ((B ⊗[A] N) ⧸ LinearMap.range (TensorProduct.mk A B N 1)) :=
  (Submodule.mkQ _).lTensor B ∘ₗ (TensorProduct.assoc A B B N).toLinearMap ∘ₗ
    (TensorProduct.comm A B B).toLinearMap.rTensor N

lemma homotopy_comp (x : B ⊗[A] N) :
    homotopy (coface₁ A B N x - coface₂ A B N x) = 1 ⊗ₜ Submodule.mkQ _ x := by
  induction x with
  | tmul b n =>
    have : Submodule.mkQ (LinearMap.range (TensorProduct.mk A B N 1)) ((1 : B) ⊗ₜ n) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ⟨n, rfl⟩
    simp [homotopy, this]
  | add x y hx hy =>
    rw [map_add, map_add, add_sub_add_comm, map_add, hx, hy, map_add, tmul_add]

/-- Universal injectivity, tested on `N` and on the cokernel `Q` of `N → B ⊗ N`, gives
condition (c) for `N` (the direction « pure ⇒ (c) » of Stacks 08WE). -/
theorem isEqualizer_of_injective (hN : Function.Injective (TensorProduct.mk A B N 1))
    (hQ : Function.Injective (TensorProduct.mk A B
      ((B ⊗[A] N) ⧸ LinearMap.range (TensorProduct.mk A B N 1)) 1)) :
    IsEqualizer A B N := by
  refine ⟨hN, fun x hx ↦ ?_⟩
  have h0 : (1 : B) ⊗ₜ[A] Submodule.mkQ (LinearMap.range (TensorProduct.mk A B N 1)) x = 0 := by
    rw [← homotopy_comp, hx, sub_self, map_zero]
  have : Submodule.mkQ (LinearMap.range (TensorProduct.mk A B N 1)) x = 0 :=
    hQ (by simpa using h0)
  exact (Submodule.Quotient.mk_eq_zero _).1 this


section Pure

universe u v w

variable (A : Type v) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- `A → B` is pure, or universally injective: `P → B ⊗ P` is injective for every `A`-module `P`
of the universe `w`. -/
def IsPure : Prop :=
  ∀ (P : Type w) [AddCommGroup P] [Module A P], Function.Injective (TensorProduct.mk A B P 1)

/-- Condition (c) for every `A`-module of the universe `w`. -/
def EqualizerCondition : Prop :=
  ∀ (P : Type w) [AddCommGroup P] [Module A P], IsEqualizer A B P

/-- Stacks 08WE: condition (c) holds iff `A → B` is pure (modules tested in a universe that
contains `B`). -/
theorem equalizerCondition_iff_isPure :
    EqualizerCondition.{u, v, max u w} A B ↔ IsPure.{u, v, max u w} A B :=
  ⟨fun h P _ _ ↦ (h P).1, fun h P _ _ ↦ isEqualizer_of_injective (h P) (h _)⟩

/-- **Theorem A, affine case**, for a pure map `A → B`: base change from `A`-modules to
descent data along `A → B` is fully faithful. -/
theorem descend_bijective_of_isPure (h : IsPure.{u, v, max u w} A B)
    (M : Type*) [AddCommGroup M] [Module A M] (N : Type (max u w)) [AddCommGroup N]
    [Module A N] : Function.Bijective (descend B : (M →ₗ[A] N) → _) :=
  descend_bijective ((equalizerCondition_iff_isPure A B).2 h N)

end Pure

end Buffalo.QcohDescent
