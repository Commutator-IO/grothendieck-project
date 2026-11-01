import Mathlib

/-!
# A simple module over an algebraically closed field is determined by its trace

Declarations a proof of this repository (`Quillen.Notebook1968_1`, an irreducible representation
is determined by its trace function) needed and that Mathlib does not have at the pinned revision.
Let `k` be an algebraically closed field, of any characteristic, and `A` a `k`-algebra, not
necessarily finite-dimensional. Two simple `A`-modules that are finite-dimensional over `k` and
have the same trace function `a ↦ tr(a | S)` are isomorphic. The proof uses the Jacobson density
theorem (`jacobson_density`) for the semisimple module `S × T` and Schur's lemma.

* `IsSemisimpleModule.prod`: the product of two semisimple modules is semisimple;
* `IsSimpleModule.exists_eq_smul_of_isAlgClosed`: Schur's lemma in the form « every endomorphism
  is a scalar », from `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`;
* `IsSimpleModule.eq_zero_of_isEmpty_linearEquiv`: a linear map between non-isomorphic simple
  modules is zero;
* `IsSimpleModule.exists_trace_eq_one_and_trace_eq_zero`: if `S ≄ T`, some `a : A` has trace `1`
  on `S` and `0` on `T`;
* `IsSimpleModule.nonempty_linearEquiv_of_trace_eq`: simple modules with the same trace function
  are isomorphic; `IsSimpleModule.nonempty_linearEquiv_of_trace_eq_of_finiteDimensional`: the
  same for a finite-dimensional algebra `A`.

Drop a declaration once Mathlib has it.
-/

open Module LinearMap

/-- The product of two semisimple modules is semisimple: it is the sum of the images of the two
inclusions. -/
instance IsSemisimpleModule.prod {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsSemisimpleModule R M] [IsSemisimpleModule R N] :
    IsSemisimpleModule R (M × N) :=
  isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := Bool.rec (range (inr R M N)) (range (inl R M N))) (fun b ↦ by cases b <;> exact .range _)
    (by rw [iSup_bool_eq]; exact sup_range_inl_inr)

namespace IsSimpleModule

variable {k A S T : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup S] [Module A S] [Module k S] [IsScalarTower k A S] [IsSimpleModule A S]
  [AddCommGroup T] [Module A T] [Module k T] [IsScalarTower k A T] [IsSimpleModule A T]

variable (k) in
/-- Schur's lemma over an algebraically closed field: an endomorphism of a simple module that is
finite-dimensional over `k` is multiplication by a scalar. -/
theorem exists_eq_smul_of_isAlgClosed [IsAlgClosed k] [FiniteDimensional k S] (g : S →ₗ[A] S) :
    ∃ c : k, ∀ s, g s = c • s := by
  obtain ⟨c, hc⟩ := (algebraMap_end_bijective_of_isAlgClosed k (A := A) (V := S)).2 g
  exact ⟨c, fun s ↦ by rw [← hc]; rfl⟩

omit [Module k S] [IsScalarTower k A S] [Module k T] [IsScalarTower k A T] in
/-- Schur's lemma: a linear map between non-isomorphic simple modules is zero. -/
theorem eq_zero_of_isEmpty_linearEquiv (h : IsEmpty (S ≃ₗ[A] T)) (f : S →ₗ[A] T) : f = 0 := by
  by_contra hf
  exact h.false (.ofBijective f (bijective_of_ne_zero hf))

/-- If `S` and `T` are not isomorphic, some element of `A` acts with trace `1` on `S` and trace `0`
on `T`. By density for `S × T`, whose endomorphisms are diagonal and scalar, the map acting as a
rank-one idempotent on `S` and as zero on `T` comes from an element of `A`. -/
theorem exists_trace_eq_one_and_trace_eq_zero [IsAlgClosed k] [FiniteDimensional k S]
    [FiniteDimensional k T] (h : IsEmpty (S ≃ₗ[A] T)) :
    ∃ a : A, trace k S (toModuleEnd k S a) = 1 ∧ trace k T (toModuleEnd k T a) = 0 := by
  have := IsSimpleModule.nontrivial A S
  have : Module.Finite (Module.End A (S × T)) (S × T) :=
    Module.Finite.of_restrictScalars_finite k _ _
  obtain ⟨v, hv⟩ := exists_ne (0 : S)
  obtain ⟨φ, hφ⟩ := Projective.exists_dual_eq_one k hv
  let ψ : S →ₗ[k] S := φ.smulRight v
  let f : Module.End (Module.End A (S × T)) (S × T) :=
    { toFun := fun m ↦ (ψ m.1, 0)
      map_add' := fun m n ↦ by simp
      map_smul' := fun g m ↦ by
        obtain ⟨c, hc⟩ := exists_eq_smul_of_isAlgClosed k (fst A S T ∘ₗ g ∘ₗ inl A S T)
        obtain ⟨d, hd⟩ := exists_eq_smul_of_isAlgClosed k (snd A S T ∘ₗ g ∘ₗ inr A S T)
        have h12 := eq_zero_of_isEmpty_linearEquiv h (snd A S T ∘ₗ g ∘ₗ inl A S T)
        have h21 := eq_zero_of_isEmpty_linearEquiv (S := T) (T := S)
          ⟨fun e ↦ h.false e.symm⟩ (fst A S T ∘ₗ g ∘ₗ inr A S T)
        have hg : ∀ x : S × T, g x = (c • x.1, d • x.2) := by
          intro x
          have hx : x = inl A S T x.1 + inr A S T x.2 := by simp
          have e1 := hc x.1; have e2 := hd x.2
          have e3 := congr($h12 x.1); have e4 := congr($h21 x.2)
          simp only [coe_comp, Function.comp_apply, coe_fst, coe_snd, inl_apply,
            inr_apply, LinearMap.zero_apply] at e1 e2 e3 e4
          rw [hx, map_add]
          ext <;> simp only [inl_apply, inr_apply, Prod.fst_add, Prod.snd_add, e1, e2, e3, e4,
            add_zero, zero_add]
        simp only [Module.End.smul_def, RingHom.id_apply, hg, map_smul]
        simp }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective f
  have hS : toModuleEnd k S a = ψ := by
    ext s; simpa [f] using congr(($ha (s, 0)).1)
  have hT : toModuleEnd k T a = 0 := by
    ext t; simpa [f] using congr(($ha (0, t)).2)
  refine ⟨a, ?_, ?_⟩
  · rw [hS, trace_smulRight, hφ]
  · rw [hT, map_zero]

/-- Over an algebraically closed field, in any characteristic, two finite-dimensional simple
modules with the same trace function are isomorphic. -/
theorem nonempty_linearEquiv_of_trace_eq [IsAlgClosed k] [FiniteDimensional k S]
    [FiniteDimensional k T]
    (h : ∀ a : A, trace k S (toModuleEnd k S a) = trace k T (toModuleEnd k T a)) :
    Nonempty (S ≃ₗ[A] T) := by
  by_contra hne
  obtain ⟨a, h1, h0⟩ := exists_trace_eq_one_and_trace_eq_zero (k := k) (not_nonempty_iff.mp hne)
  exact one_ne_zero (h1.symm.trans ((h a).trans h0))

/-- For a finite-dimensional algebra `A`, simple modules are automatically finite-dimensional,
and are determined by their trace functions. -/
theorem nonempty_linearEquiv_of_trace_eq_of_finiteDimensional [IsAlgClosed k]
    [FiniteDimensional k A]
    (h : ∀ a : A, trace k S (toModuleEnd k S a) = trace k T (toModuleEnd k T a)) :
    Nonempty (S ≃ₗ[A] T) :=
  have : FiniteDimensional k S := Module.Finite.trans A S
  have : FiniteDimensional k T := Module.Finite.trans A T
  nonempty_linearEquiv_of_trace_eq h

end IsSimpleModule
