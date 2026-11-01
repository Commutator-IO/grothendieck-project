import Quillen.Upstream.IsSimpleModuleTrace

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

The proofs are general and live in `Quillen.Upstream.IsSimpleModuleTrace`
(`IsSemisimpleModule.prod`, `IsSimpleModule.nonempty_linearEquiv_of_trace_eq`, …); Schur's lemma
in scalar form comes from Mathlib's `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`. The
declarations below keep the names of this page.
-/

namespace Quillen.Notebook1968_1

open Module LinearMap

variable {k A S T : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup S] [Module A S] [Module k S] [IsScalarTower k A S] [IsSimpleModule A S]
  [AddCommGroup T] [Module A T] [Module k T] [IsScalarTower k A T] [IsSimpleModule A T]

omit [Module k S] [IsScalarTower k A S] [Module k T] [IsScalarTower k A T] in
/-- The product of two simple modules is semisimple: it is the sum of the images of the two
inclusions. -/
theorem isSemisimpleModule_prod : IsSemisimpleModule A (S × T) := inferInstance

variable (k) in
/-- Schur's lemma over an algebraically closed field: an endomorphism of a simple module that is
finite-dimensional over `k` is multiplication by a scalar. -/
theorem exists_eq_smul_of_isAlgClosed [IsAlgClosed k] [FiniteDimensional k S] (g : S →ₗ[A] S) :
    ∃ c : k, ∀ s, g s = c • s :=
  IsSimpleModule.exists_eq_smul_of_isAlgClosed k g

omit [Module k S] [IsScalarTower k A S] [Module k T] [IsScalarTower k A T] in
/-- Schur's lemma: a linear map between non-isomorphic simple modules is zero. -/
theorem eq_zero_of_isEmpty_linearEquiv (h : IsEmpty (S ≃ₗ[A] T)) (f : S →ₗ[A] T) : f = 0 :=
  IsSimpleModule.eq_zero_of_isEmpty_linearEquiv h f

/-- If `S` and `T` are not isomorphic, some element of `A` acts with trace `1` on `S` and trace `0`
on `T`. By density for `S × T`, whose endomorphisms are diagonal and scalar, the map acting as a
rank-one idempotent on `S` and as zero on `T` comes from an element of `A`. -/
theorem exists_trace_eq_one_trace_eq_zero [IsAlgClosed k] [FiniteDimensional k S]
    [FiniteDimensional k T] (h : IsEmpty (S ≃ₗ[A] T)) :
    ∃ a : A, trace k S (toModuleEnd k S a) = 1 ∧ trace k T (toModuleEnd k T a) = 0 :=
  IsSimpleModule.exists_trace_eq_one_and_trace_eq_zero h

/-- **Quillen, 1968-1, p. 4.** Over an algebraically closed field, in any characteristic, two
finite-dimensional simple modules with the same trace function are isomorphic. -/
theorem nonempty_linearEquiv_of_trace_eq [IsAlgClosed k] [FiniteDimensional k S]
    [FiniteDimensional k T]
    (h : ∀ a : A, trace k S (toModuleEnd k S a) = trace k T (toModuleEnd k T a)) :
    Nonempty (S ≃ₗ[A] T) :=
  IsSimpleModule.nonempty_linearEquiv_of_trace_eq h

/-- The notebook's form: for a finite-dimensional algebra `A`, simple modules are automatically
finite-dimensional, and are determined by their trace functions. -/
theorem nonempty_linearEquiv_of_trace_eq' [IsAlgClosed k] [FiniteDimensional k A]
    (h : ∀ a : A, trace k S (toModuleEnd k S a) = trace k T (toModuleEnd k T a)) :
    Nonempty (S ≃ₗ[A] T) :=
  IsSimpleModule.nonempty_linearEquiv_of_trace_eq_of_finiteDimensional h

end Quillen.Notebook1968_1
