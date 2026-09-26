import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.Flat.Basic

/-!
# Folder 153, the Lemme of page 3 (integer-valued polynomials and free modules)

The modernised reading `transcripts/153/153.modern.tex` (manuscript page 3)
fixes a pair of commutative rings `k₀ ⊂ K₀` and
`Ω = Int(k₀) = {F ∈ K₀[T] | F(λ) ∈ k₀ for all λ ∈ k₀}`, and states:

> **Lemme.** Si `M` est un `k₀`-module libre, l'ensemble des
> `F ∈ K₀[T] ⊗_{k₀} M` tels que `F(x) ∈ M` pour tout `x ∈ k₀` s'identifie à
> `Ω ⊗_{k₀} M` — coordonnée par coordonnée dans une base de `M`.

Here `F(x)` is the image of `F` under `ev_x ⊗ id : K₀[T] ⊗ M → K₀ ⊗ M`, and
"`F(x) ∈ M`" means that it lies in the image of `M → K₀ ⊗ M`, `m ↦ 1 ⊗ m`.
"S'identifie à" is read as: the canonical map `Ω ⊗ M → K₀[T] ⊗ M` is injective
(`lemme_injective`) and its image is exactly that set (`lemme_range`). The
reading's "coordinate by coordinate" is `lemme_coordonnees`: in a basis of `M`,
`F` satisfies the condition iff each of its coordinates lies in `Ω`.

What the formalisation found. The Lemme holds as stated, and one hypothesis
is not used: that `k₀ → K₀` is an inclusion. The proof works for any
`k₀`-algebra `K₀`, `Int(k₀)` being then the polynomials sending `k₀` into the
image of `k₀`. Freeness of `M` is used twice, as the reading says it is: for
the injectivity (a free module is flat, `Module.Flat.of_free`) and for the
coordinates. (The reading's footnote on the co-operations — that
`K₀[X] ⊗_{k₀} K₀[Y] = K₀[X,Y]` needs `K₀ ⊗_{k₀} K₀ = K₀` — concerns the next
paragraph, not this Lemme, and is not formalised here.)
-/

namespace Grothendieck.Folder153

open Polynomial TensorProduct

section Coordonnees

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {ι : Type*} [DecidableEq ι] (b : Module.Basis ι R M)

/-- Coordinates of `N ⊗ M` in a basis `b` of `M`: `N ⊗ M ≃ ι →₀ N`. -/
noncomputable def coords (N : Type*) [AddCommGroup N] [Module R N] :
    N ⊗[R] M ≃ₗ[R] ι →₀ N :=
  TensorProduct.congr (LinearEquiv.refl R N) b.repr ≪≫ₗ finsuppScalarRight R R N ι

variable {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

theorem coords_tmul (n : N) (m : M) (i : ι) :
    coords b N (n ⊗ₜ m) i = b.repr m i • n := by
  simp [coords]

/-- The coordinates are natural in `N`. -/
theorem coords_rTensor (f : N →ₗ[R] P) (t : N ⊗[R] M) :
    coords b P (f.rTensor M t) = Finsupp.mapRange f f.map_zero (coords b N t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul n m => ext i; simp [coords_tmul]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, Finsupp.mapRange_add f.map_add]

/-- An element of `P ⊗ M` comes from `N ⊗ M` iff each coordinate comes from `N`. -/
theorem mem_range_rTensor (f : N →ₗ[R] P) (t : P ⊗[R] M) :
    t ∈ LinearMap.range (f.rTensor M) ↔ ∀ i, coords b P t i ∈ LinearMap.range f := by
  constructor
  · rintro ⟨s, rfl⟩ i
    rw [coords_rTensor, Finsupp.mapRange_apply]
    exact ⟨_, rfl⟩
  · intro h
    choose g hg using h
    let s : ι →₀ N := ∑ i ∈ (coords b P t).support, Finsupp.single i (g i)
    refine ⟨(coords b N).symm s, (coords b P).injective ?_⟩
    rw [coords_rTensor, LinearEquiv.apply_symm_apply]
    ext j
    rw [Finsupp.mapRange_apply, Finsupp.finsetSum_apply]
    simp_rw [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    split_ifs with hj
    · exact hg j
    · rw [map_zero, eq_comm, ← Finsupp.notMem_support_iff]
      exact hj

end Coordonnees

variable {k₀ K₀ : Type*} [CommRing k₀] [CommRing K₀] [Algebra k₀ K₀]

/-- Evaluation at `x ∈ k₀`, as a `k₀`-linear map `K₀[T] → K₀`. -/
noncomputable def ev (x : k₀) : K₀[X] →ₗ[k₀] K₀ :=
  (Polynomial.leval (algebraMap k₀ K₀ x)).restrictScalars k₀

theorem ev_apply (x : k₀) (F : K₀[X]) : ev x F = F.eval (algebraMap k₀ K₀ x) := rfl

variable (k₀ K₀) in
/-- `Ω = Int(k₀)`: the polynomials of `K₀[T]` taking values in `k₀` on `k₀`. -/
noncomputable def Omega : Subalgebra k₀ K₀[X] where
  carrier := {F | ∀ x : k₀, F.eval (algebraMap k₀ K₀ x) ∈ (algebraMap k₀ K₀).range}
  mul_mem' {F G} hF hG x := by rw [eval_mul]; exact mul_mem (hF x) (hG x)
  add_mem' {F G} hF hG x := by rw [eval_add]; exact add_mem (hF x) (hG x)
  algebraMap_mem' c x := by
    rw [Polynomial.algebraMap_apply, eval_C]; exact ⟨c, rfl⟩

variable {M : Type*} [AddCommGroup M] [Module k₀ M]

variable (K₀ M) in
/-- The set of the Lemme: the `F ∈ K₀[T] ⊗ M` such that `F(x) ∈ M` for every
`x ∈ k₀`, i.e. `(ev_x ⊗ id) F` lies in the image of `m ↦ 1 ⊗ m`. -/
def valeursDansM : Set (K₀[X] ⊗[k₀] M) :=
  {F | ∀ x : k₀, (ev x).rTensor M F ∈ LinearMap.range (TensorProduct.mk k₀ K₀ M 1)}

/-- The image of `m ↦ 1 ⊗ m` is the image of `k₀ ⊗ M → K₀ ⊗ M`. -/
theorem range_mk_one :
    LinearMap.range (TensorProduct.mk k₀ K₀ M 1) =
      LinearMap.range ((Algebra.linearMap k₀ K₀).rTensor M) := by
  have : TensorProduct.mk k₀ K₀ M 1 =
      (Algebra.linearMap k₀ K₀).rTensor M ∘ₗ (TensorProduct.lid k₀ M).symm.toLinearMap := by
    ext m; simp
  rw [this, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- **Lemme, coordinate by coordinate.** In a basis `b` of `M`, `F ∈ K₀[T] ⊗ M`
takes values in `M` on `k₀` iff each of its coordinates lies in `Ω = Int(k₀)`. -/
theorem lemme_coordonnees {ι : Type*} [DecidableEq ι] (b : Module.Basis ι k₀ M) (F : K₀[X] ⊗[k₀] M) :
    F ∈ valeursDansM K₀ M ↔ ∀ i, coords b K₀[X] F i ∈ Omega k₀ K₀ := by
  simp only [valeursDansM, Set.mem_ofPred_eq, range_mk_one, mem_range_rTensor b,
    coords_rTensor, Finsupp.mapRange_apply, ev_apply]
  exact ⟨fun h i x => h x i, fun h x i => h i x⟩

/-- **Lemme (1).** For `M` free, `Ω ⊗ M → K₀[T] ⊗ M` is injective. -/
theorem lemme_injective [Module.Free k₀ M] :
    Function.Injective ((Omega k₀ K₀).val.toLinearMap.rTensor M) :=
  Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

/-- **Lemme (2).** For `M` free, the image of `Ω ⊗ M → K₀[T] ⊗ M` is exactly the
set of `F` with `F(x) ∈ M` for every `x ∈ k₀`. -/
theorem lemme_range [Module.Free k₀ M] :
    (LinearMap.range ((Omega k₀ K₀).val.toLinearMap.rTensor M) : Set (K₀[X] ⊗[k₀] M)) =
      valeursDansM K₀ M := by
  classical
  let b := Module.Free.chooseBasis k₀ M
  ext F
  rw [SetLike.mem_coe, mem_range_rTensor b, lemme_coordonnees b]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  rintro ⟨G, hG⟩
  rw [← hG]
  exact G.2

end Grothendieck.Folder153
