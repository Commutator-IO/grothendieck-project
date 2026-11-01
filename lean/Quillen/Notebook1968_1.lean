import Mathlib

/-!
# Quillen, notebook 1968-1: a simple module is determined by its trace

Daniel Quillen's notebook 1968-1 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201968/1968-1.pdf>), dated
January 1968, is mostly about representations of semisimple Lie algebras. On PDF p. 4 he records,
as a basic theorem, that an irreducible representation of a finite-dimensional complex algebra is
determined by its trace function `a ↦ tr(a | S)`. His sketch: the trace vanishes on the radical,
since elements of the radical act nilpotently; by Wedderburn the semisimple quotient is a product
of simple algebras, and the trace of `S` is nonzero on the factor belonging to `S` and zero on the
others. A remark that the trace takes the value `dim S` at `1` is crossed out, rightly so in
positive characteristic, where `dim S` may vanish in the field.

We prove the statement over any algebraically closed field `k`, of any characteristic, and without
assuming `A` finite-dimensional (only the two modules are). Instead of Wedderburn–Artin we use the
Jacobson density theorem (`jacobson_density`) for the semisimple module `S × T`: by Schur's lemma
its `A`-endomorphisms are diagonal with scalar entries when `S ≄ T`, so a `k`-linear map acting as a
rank-one idempotent on `S` and as zero on `T` is induced by an element of `A`, whose traces on `S`
and `T` are `1` and `0`.

* `isSemisimpleModule_prod`: the product of two simple modules is semisimple;
* `exists_eq_smul_of_isAlgClosed`: Schur's lemma over an algebraically closed field, every
  endomorphism of a finite-dimensional simple module is a scalar;
* `eq_zero_of_isEmpty_linearEquiv`: a linear map between non-isomorphic simple modules is zero;
* `exists_trace_eq_one_trace_eq_zero`: if `S ≄ T`, some `a : A` has trace `1` on `S`, `0` on `T`;
* `nonempty_linearEquiv_of_trace_eq`: simple modules with the same trace function are isomorphic;
* `nonempty_linearEquiv_of_trace_eq'`: the same for a finite-dimensional algebra `A`, as in the
  notebook, where the finite-dimensionality of the modules is automatic.

This is classical (Curtis–Reiner, *Representation Theory of Finite Groups and Associative
Algebras*, chapter on characters of algebras; Lam, *A First Course in Noncommutative Rings*,
chapter on representations); mathlib has the density theorem and Wedderburn–Artin over
algebraically closed fields, not this statement.
-/

namespace Quillen.Notebook1968_1

open Module LinearMap

variable {k A S T : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup S] [Module A S] [Module k S] [IsScalarTower k A S] [IsSimpleModule A S]
  [AddCommGroup T] [Module A T] [Module k T] [IsScalarTower k A T] [IsSimpleModule A T]

omit [Module k S] [IsScalarTower k A S] [Module k T] [IsScalarTower k A T] in
/-- The product of two simple modules is semisimple: it is the sum of the images of the two
inclusions. -/
theorem isSemisimpleModule_prod : IsSemisimpleModule A (S × T) :=
  isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := Bool.rec (range (inr A S T)) (range (inl A S T))) (fun b ↦ by cases b <;> exact .range _)
    (by rw [iSup_bool_eq]; exact sup_range_inl_inr)

variable (k) in
/-- Schur's lemma over an algebraically closed field: an endomorphism of a simple module that is
finite-dimensional over `k` is multiplication by a scalar, namely any of its eigenvalues. -/
theorem exists_eq_smul_of_isAlgClosed [IsAlgClosed k] [FiniteDimensional k S] (g : S →ₗ[A] S) :
    ∃ c : k, ∀ s, g s = c • s := by
  have := IsSimpleModule.nontrivial A S
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (g.restrictScalars k)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, fun s ↦ ?_⟩
  rcases (g - algebraMap k (Module.End A S) c).injective_or_eq_zero with h | h
  · refine absurd (h (a₂ := 0) ?_) hv.2
    simpa [sub_eq_zero] using hv.apply_eq_smul
  · simpa [sub_eq_zero] using congr($h s)

omit [Module k S] [IsScalarTower k A S] [Module k T] [IsScalarTower k A T] in
/-- Schur's lemma: a linear map between non-isomorphic simple modules is zero. -/
theorem eq_zero_of_isEmpty_linearEquiv (h : IsEmpty (S ≃ₗ[A] T)) (f : S →ₗ[A] T) : f = 0 := by
  by_contra hf
  exact h.false (.ofBijective f (bijective_of_ne_zero hf))

/-- If `S` and `T` are not isomorphic, some element of `A` acts with trace `1` on `S` and trace `0`
on `T`. By density for `S × T`, whose endomorphisms are diagonal and scalar, the map acting as a
rank-one idempotent on `S` and as zero on `T` comes from an element of `A`. -/
theorem exists_trace_eq_one_trace_eq_zero [IsAlgClosed k] [FiniteDimensional k S]
    [FiniteDimensional k T] (h : IsEmpty (S ≃ₗ[A] T)) :
    ∃ a : A, trace k S (toModuleEnd k S a) = 1 ∧ trace k T (toModuleEnd k T a) = 0 := by
  have := IsSimpleModule.nontrivial A S
  have := isSemisimpleModule_prod (A := A) (S := S) (T := T)
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

/-- **Quillen, 1968-1, p. 4.** Over an algebraically closed field, in any characteristic, two
finite-dimensional simple modules with the same trace function are isomorphic. -/
theorem nonempty_linearEquiv_of_trace_eq [IsAlgClosed k] [FiniteDimensional k S]
    [FiniteDimensional k T]
    (h : ∀ a : A, trace k S (toModuleEnd k S a) = trace k T (toModuleEnd k T a)) :
    Nonempty (S ≃ₗ[A] T) := by
  by_contra hne
  obtain ⟨a, h1, h0⟩ := exists_trace_eq_one_trace_eq_zero (k := k) (not_nonempty_iff.mp hne)
  exact one_ne_zero (h1.symm.trans ((h a).trans h0))

/-- The notebook's form: for a finite-dimensional algebra `A`, simple modules are automatically
finite-dimensional, and are determined by their trace functions. -/
theorem nonempty_linearEquiv_of_trace_eq' [IsAlgClosed k] [FiniteDimensional k A]
    (h : ∀ a : A, trace k S (toModuleEnd k S a) = trace k T (toModuleEnd k T a)) :
    Nonempty (S ≃ₗ[A] T) :=
  have : FiniteDimensional k S := Module.Finite.trans A S
  have : FiniteDimensional k T := Module.Finite.trans A T
  nonempty_linearEquiv_of_trace_eq h

end Quillen.Notebook1968_1
