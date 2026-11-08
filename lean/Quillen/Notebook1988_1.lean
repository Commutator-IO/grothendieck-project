import Mathlib

/-!
# Quillen, notebook 1988-1, pp. 71-72: `Hom_k(M, A)` modulo commutators is the dual of `M`

Daniel Quillen's research notebook 1988-1 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201988/1988-1.pdf>) turns in
February 1988 to residues and duality, and tries to reconstruct Cartier's and Tate's
definitions of the residue through Hochschild cochains. The entry of February 29, 1988
(pp. 71-72) isolates a lemma, in our words: if `A` is a `k`-algebra and `M` an `A`-module that
is finite-dimensional over `k`, then the space `Hom_k(M, A)`, an `A`-bimodule through
`(a λ b)(x) = a λ(b x)`, has commutator quotient `Hom_k(M, A) / [A, Hom_k(M, A)]` isomorphic
to the dual `M*`, by `λ ↦ (m ↦ tr_M(x ↦ λ(x) m))`. His proof writes `λ = Σ μ_j ⊗ λ(m_j)` with a
basis `m_j` and its dual basis `μ_j`, and moves the coefficient `λ(m_j)` across the tensor sign
modulo commutators. That is the proof formalised here. The page works over a commutative `A`;
the argument does not use it, and the statement here is for any `k`-algebra `A`.

* `op l m`: the `k`-linear endomorphism `x ↦ l x • m` of `M`;
* `traceForm`: the map `Hom_k(M, A) → M*`, `l ↦ (m ↦ tr (op l m))`;
* `leftMul a l = (x ↦ a * l x)` and `rightMul a l = (x ↦ l (a • x))`, the two actions of `A`;
* `commutators`: the `k`-span of the `leftMul a l - rightMul a l`;
* `traceForm_leftMul`: `traceForm` takes the same value on `leftMul a l` and `rightMul a l`;
* `traceForm_embed`: `traceForm` is a retraction of `μ ↦ (x ↦ μ x • 1)`, hence surjective;
* `ker_traceForm`: **the lemma**: the kernel of `traceForm` is exactly `commutators`;
* `quotientEquivDual`: the resulting isomorphism `Hom_k(M, A) / commutators ≃ M*`.
-/

namespace Quillen.Notebook1988_1

open LinearMap

variable (k : Type*) {A M : Type*} [Field k] [Ring A] [Algebra k A] [AddCommGroup M] [Module k M]

/-- Left action of `a ∈ A` on `Hom_k(M, A)`: `x ↦ a * l x`. -/
def leftMul (a : A) (l : M →ₗ[k] A) : M →ₗ[k] A := LinearMap.mulLeft k a ∘ₗ l

@[simp] lemma leftMul_apply (a : A) (l : M →ₗ[k] A) (x : M) : leftMul k a l x = a * l x := rfl

/-- The embedding `M* → Hom_k(M, A)`, `μ ↦ (x ↦ μ x • 1)`. -/
noncomputable def embed : Module.Dual k M →ₗ[k] (M →ₗ[k] A) :=
  LinearMap.llcomp k M k A (Algebra.linearMap k A)

@[simp] lemma embed_apply (μ : Module.Dual k M) (x : M) :
    embed k (A := A) μ x = algebraMap k A (μ x) := rfl

variable [Module A M] [IsScalarTower k A M]

/-- The `k`-linear endomorphism `x ↦ l x • m` of `M`. -/
def op (l : M →ₗ[k] A) (m : M) : M →ₗ[k] M :=
  (LinearMap.toSpanSingleton A M m).restrictScalars k ∘ₗ l

@[simp] lemma op_apply (l : M →ₗ[k] A) (m x : M) : op k l m x = l x • m := by
  simp [op]

/-- Multiplication by `a ∈ A`, as a `k`-linear endomorphism of `M`. -/
def smulEnd (a : A) : M →ₗ[k] M where
  toFun x := a • x
  map_add' := smul_add a
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [← algebraMap_smul A c x, ← algebraMap_smul A c (a • x), smul_smul, smul_smul,
      Algebra.commutes]

@[simp] lemma smulEnd_apply (a : A) (x : M) : smulEnd k a x = a • x := rfl

/-- Right action of `a ∈ A` on `Hom_k(M, A)`: `x ↦ l (a • x)`. -/
def rightMul (a : A) (l : M →ₗ[k] A) : M →ₗ[k] A := l ∘ₗ smulEnd k a

@[simp] lemma rightMul_apply (a : A) (l : M →ₗ[k] A) (x : M) : rightMul k a l x = l (a • x) :=
  rfl

/-- The commutator subspace `[A, Hom_k(M, A)]`. -/
def commutators : Submodule k (M →ₗ[k] A) :=
  Submodule.span k (Set.range fun p : A × (M →ₗ[k] A) => leftMul k p.1 p.2 - rightMul k p.1 p.2)

/-- Quillen's map `Hom_k(M, A) → M*`, `l ↦ (m ↦ tr_M (x ↦ l x • m))`. -/
noncomputable def traceForm : (M →ₗ[k] A) →ₗ[k] Module.Dual k M :=
  LinearMap.mk₂ k (fun l m => LinearMap.trace k M (op k l m))
    (fun l l' m => by
      rw [← map_add]; congr 1; ext x
      simp only [op_apply, LinearMap.add_apply, add_smul])
    (fun c l m => by
      rw [← map_smul]; congr 1; ext x
      simp only [op_apply, LinearMap.smul_apply, smul_assoc])
    (fun l m m' => by
      rw [← map_add]; congr 1; ext x
      simp only [op_apply, LinearMap.add_apply, smul_add])
    (fun c l m => by
      rw [← map_smul]; congr 1; ext x
      simp only [op_apply, LinearMap.smul_apply]
      exact smul_comm _ _ _)

lemma traceForm_apply (l : M →ₗ[k] A) (m : M) :
    traceForm k l m = LinearMap.trace k M (op k l m) := rfl

lemma rightMul_embed (a : A) (μ : Module.Dual k M) :
    rightMul k a (embed k μ) = embed k (μ ∘ₗ smulEnd k a) := rfl

/-- `traceForm` does not see the difference between the two actions of `A`. -/
theorem traceForm_leftMul (a : A) (l : M →ₗ[k] A) :
    traceForm k (leftMul k a l) = traceForm k (rightMul k a l) := by
  ext m
  have h1 : op k (leftMul k a l) m = smulEnd k a * op k l m := by
    ext x; simp [mul_smul]
  have h2 : op k (rightMul k a l) m = op k l m * smulEnd k a := by
    ext x; simp
  rw [traceForm_apply, traceForm_apply, h1, h2, LinearMap.trace_mul_comm]

variable [FiniteDimensional k M]

/-- `traceForm` retracts the embedding `μ ↦ (x ↦ μ x • 1)`. -/
theorem traceForm_embed (μ : Module.Dual k M) : traceForm k (embed k (A := A) μ) = μ := by
  ext m
  have : op k (embed k (A := A) μ) m = μ.smulRight m := by
    ext x; simp [algebraMap_smul]
  rw [traceForm_apply, this, LinearMap.trace_smulRight]

theorem traceForm_surjective : Function.Surjective (traceForm k (A := A) (M := M)) :=
  fun μ => ⟨embed k μ, traceForm_embed k μ⟩

/-- Quillen's decomposition: `l - embed (traceForm l)` is a sum of commutators. -/
theorem sub_embed_traceForm_mem (l : M →ₗ[k] A) :
    l - embed k (traceForm k l) ∈ commutators k := by
  let b := Module.finBasis k M
  set c : Fin (Module.finrank k M) → A := fun j => l (b j)
  set e : Fin (Module.finrank k M) → (M →ₗ[k] A) := fun j => embed k (b.coord j)
  have hl : l = ∑ j, leftMul k (c j) (e j) := by
    ext x
    simp only [LinearMap.sum_apply, leftMul_apply, embed_apply, c, e, Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr x, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Algebra.smul_def, Algebra.commutes]
  have hr : embed k (traceForm k l) = ∑ j, rightMul k (c j) (e j) := by
    conv_lhs => rw [hl]
    simp only [map_sum, traceForm_leftMul, e, rightMul_embed, traceForm_embed]
  rw [hr]
  nth_rewrite 1 [hl]
  rw [← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨(c j, e j), rfl⟩

/-- **The lemma of pp. 71-72.** The kernel of `traceForm` is the commutator subspace. -/
theorem ker_traceForm : LinearMap.ker (traceForm k (A := A) (M := M)) = commutators k := by
  apply le_antisymm
  · intro l hl
    have := sub_embed_traceForm_mem k l
    rwa [LinearMap.mem_ker.mp hl, map_zero, sub_zero] at this
  · rw [commutators, Submodule.span_le]
    rintro _ ⟨⟨a, l⟩, rfl⟩
    simp [LinearMap.mem_ker, traceForm_leftMul]

/-- `Hom_k(M, A) / [A, Hom_k(M, A)] ≃ M*`, through `l ↦ (m ↦ tr_M (x ↦ l x • m))`. -/
noncomputable def quotientEquivDual : ((M →ₗ[k] A) ⧸ commutators k (A := A) (M := M)) ≃ₗ[k] Module.Dual k M :=
  (Submodule.quotEquivOfEq _ _ (ker_traceForm k (A := A) (M := M))).symm.trans
    (LinearMap.quotKerEquivOfSurjective _ (traceForm_surjective k (A := A) (M := M)))

end Quillen.Notebook1988_1
