import Mathlib

/-!
# Buffalo, algebraic geometry, part 06 (d): 26 June 1973, from 4:39:50

The entries of `docs/buffalo-ag/index.tex` lines 880–906 (video `Oqhr-Gt66es`, 4:39:50–5:23:27):
perfect fields and geometric reducedness, separably closed fields and geometric irreducibility.

Conventions. A `k`-scheme is a morphism `X ⟶ Spec k`. Mathlib's `GeometricallyReduced` and
`GeometricallyIrreducible` are defined by base change to every field, and
`Algebra.IsGeometricallyReduced k A` by base change to an algebraic closure. The key computation
is `not_isReduced_tensor`: for `k` of characteristic `p` and `k' = k[t]/(tᵖ - x)`, the element
`α ⊗ 1 - 1 ⊗ α` of `k' ⊗_k k'` is a nonzero nilpotent.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial TensorProduct

universe u

namespace Buffalo.AG.Part06

noncomputable section

/-! ### Perfect fields and geometric reducedness -/

section Perfect

variable (k : Type u) [Field k]

/-- A finite separable extension stays reduced after any extension of scalars to a field:
`L ⊗_k K` is formally unramified and essentially of finite type over the field `L`. -/
theorem isReduced_tensor_of_isSeparable (K L : Type u) [Field K] [Field L] [Algebra k K]
    [Algebra k L] [FiniteDimensional k K] [Algebra.IsSeparable k K] : IsReduced (L ⊗[k] K) := by
  have : Algebra.FormallyUnramified k K := Algebra.FormallyUnramified.of_isSeparable k K
  have : Algebra.FormallyUnramified L (L ⊗[k] K) := Algebra.FormallyUnramified.base_change L
  exact Algebra.FormallyUnramified.isReduced_of_field L (L ⊗[k] K)

section Root

variable (p : ℕ) [hp : Fact p.Prime] (x : k)

/-- The polynomial `tᵖ - x`. -/
abbrev rootPoly : k[X] := X ^ p - C x

theorem rootPoly_monic : (rootPoly k p x).Monic := monic_X_pow_sub_C x hp.out.ne_zero

/-- `α ⊗ 1 - 1 ⊗ α` in `k' ⊗_k k'`, `k' = k[t]/(tᵖ - x)`, `α` the class of `t`. -/
abbrev diffElt : AdjoinRoot (rootPoly k p x) ⊗[k] AdjoinRoot (rootPoly k p x) :=
  AdjoinRoot.root (rootPoly k p x) ⊗ₜ 1 - 1 ⊗ₜ AdjoinRoot.root (rootPoly k p x)

omit hp in
theorem root_pow : AdjoinRoot.root (rootPoly k p x) ^ p = algebraMap k _ x := by
  have := AdjoinRoot.eval₂_root (rootPoly k p x)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at this
  rw [AdjoinRoot.algebraMap_eq]
  exact sub_eq_zero.1 this

/-- `α ⊗ 1 - 1 ⊗ α ≠ 0`: the functional `a ⊗ b ↦ c₁(a) c₀(b)` (coordinates in the basis
`1, α, …, α^{p-1}`) takes the value `1` on it. -/
theorem diffElt_ne_zero : diffElt k p x ≠ 0 := by
  set pb := AdjoinRoot.powerBasis' (rootPoly_monic k p x)
  have hdim : pb.dim = p := by
    rw [AdjoinRoot.powerBasis'_dim, natDegree_X_pow_sub_C]
  have h1 : 1 < pb.dim := by rw [hdim]; exact hp.out.one_lt
  let i₀ : Fin pb.dim := ⟨0, by omega⟩
  let i₁ : Fin pb.dim := ⟨1, h1⟩
  have hb₀ : pb.basis i₀ = 1 := by simp [PowerBasis.coe_basis, i₀]
  have hb₁ : pb.basis i₁ = AdjoinRoot.root (rootPoly k p x) := by
    simp [PowerBasis.coe_basis, i₁, pb, AdjoinRoot.powerBasis'_gen]
  let L : AdjoinRoot (rootPoly k p x) ⊗[k] AdjoinRoot (rootPoly k p x) →ₗ[k] k :=
    (TensorProduct.lid k k).toLinearMap ∘ₗ TensorProduct.map (pb.basis.coord i₁) (pb.basis.coord i₀)
  have hL : L (diffElt k p x) = 1 := by
    simp only [L, diffElt, map_sub, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearEquiv.coe_coe, TensorProduct.lid_tmul, smul_eq_mul]
    rw [← hb₀, ← hb₁]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self]
    simp [i₀, i₁]
  intro h
  rw [h, map_zero] at hL
  exact zero_ne_one hL

variable [CharP k p]

/-- `α ⊗ 1 - 1 ⊗ α` is nilpotent: its `p`-th power is `x ⊗ 1 - 1 ⊗ x = 0`. -/
theorem diffElt_pow : diffElt k p x ^ p = 0 := by
  have : Nontrivial (AdjoinRoot (rootPoly k p x) ⊗[k] AdjoinRoot (rootPoly k p x)) :=
    nontrivial_of_ne _ _ (diffElt_ne_zero k p x)
  have : CharP (AdjoinRoot (rootPoly k p x) ⊗[k] AdjoinRoot (rootPoly k p x)) p :=
    charP_of_injective_algebraMap (algebraMap k _).injective p
  rw [diffElt, sub_pow_char]
  simp only [Algebra.TensorProduct.tmul_pow, one_pow]
  rw [root_pow, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, sub_self]

/-- Oqhr-Gt66es-17048 (4:44:08) [cex] For `k' = k[t]/(tᵖ - x)`, `k' ⊗_k k'` is not reduced (it is
`k'[t]/(t - α)ᵖ`; the presentation is not formalised): `α ⊗ 1 - 1 ⊗ α` is a nonzero nilpotent.
(The hypothesis `x ∉ kᵖ` makes `k'` a field; it is not needed for non-reducedness.) -/
theorem not_isReduced_tensor :
    ¬ IsReduced (AdjoinRoot (rootPoly k p x) ⊗[k] AdjoinRoot (rootPoly k p x)) := fun h =>
  diffElt_ne_zero k p x (h.eq_zero _ ⟨p, diffElt_pow k p x⟩)

omit [CharP k p] in
/-- For `x ∉ kᵖ`, `k' = k[t]/(tᵖ - x)` is a field, purely inseparable over `k`. -/
theorem rootPoly_irreducible (hx : ∀ b : k, b ^ p ≠ x) : Irreducible (rootPoly k p x) :=
  X_pow_sub_C_irreducible_of_prime hp.out hx

/-- Every element of `k[t]/(tᵖ - x)` has its `p`-th power in `k`. -/
theorem pow_mem_range (y : AdjoinRoot (rootPoly k p x)) :
    y ^ p ∈ (algebraMap k (AdjoinRoot (rootPoly k p x))).range := by
  have : Nontrivial (AdjoinRoot (rootPoly k p x)) := AdjoinRoot.nontrivial _ (by
    rw [degree_X_pow_sub_C hp.out.pos]; exact_mod_cast hp.out.ne_zero)
  have : CharP (AdjoinRoot (rootPoly k p x)) p :=
    charP_of_injective_algebraMap (algebraMap k _).injective p
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective y
  induction f using Polynomial.induction_on with
  | C a => exact RingHom.mem_range.2 ⟨a ^ p, by rw [map_pow, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]⟩
  | add f g hf hg =>
    rw [map_add, add_pow_char]
    exact Subring.add_mem _ hf hg
  | monomial n a _ =>
    rw [map_mul, map_pow, AdjoinRoot.mk_X, mul_pow, ← pow_mul, mul_comm (n + 1) p, pow_mul,
      root_pow, AdjoinRoot.mk_C]
    exact Subring.mul_mem _ (RingHom.mem_range.2 ⟨a ^ p, by rw [map_pow, AdjoinRoot.algebraMap_eq]⟩)
      (Subring.pow_mem _ (RingHom.mem_range.2 ⟨x, rfl⟩) _)

/-- A field of characteristic `p` that is not perfect has an element that is not a `p`-th power. -/
theorem exists_not_pow_of_not_perfect (h : ¬ PerfectField k) : ∃ x : k, ∀ b : k, b ^ p ≠ x := by
  by_contra hc
  push Not at hc
  apply h
  have : ExpChar k p := ExpChar.prime hp.out
  have : PerfectRing k p := PerfectRing.ofSurjective k p fun x => by
    obtain ⟨b, hb⟩ := hc x
    exact ⟨b, by rw [frobenius_def, hb]⟩
  exact PerfectRing.toPerfectField k p

end Root

/-- Oqhr-Gt66es-16790 (4:39:50) [prop] For a field `k` (of characteristic `p`), `k` is perfect iff
`k' ⊗_k k'` is reduced for every finite purely inseparable extension `k'/k`. Proved: this
equivalence of the first and last conditions (⇒ even for every finite extension; ⇐ with
`k' = k[t]/(tᵖ - x)`, `x ∉ kᵖ`); the conditions on arbitrary reduced algebras are not formalised. -/
theorem prop_16790 (p : ℕ) [hp : Fact p.Prime] [CharP k p] :
    (PerfectField k → ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
      IsReduced (K ⊗[k] K)) ∧
    (¬ PerfectField k → ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      FiniteDimensional k K ∧ IsPurelyInseparable k K ∧ ¬ IsReduced (K ⊗[k] K)) := by
  refine ⟨fun _ K _ _ _ => isReduced_tensor_of_isSeparable k K K, fun h => ?_⟩
  obtain ⟨x, hx⟩ := exists_not_pow_of_not_perfect k p h
  have : Fact (Irreducible (rootPoly k p x)) := ⟨rootPoly_irreducible k p x hx⟩
  have : ExpChar k p := ExpChar.prime hp.out
  refine ⟨AdjoinRoot (rootPoly k p x), inferInstance, inferInstance,
    (AdjoinRoot.powerBasis' (rootPoly_monic k p x)).finite, ?_, not_isReduced_tensor k p x⟩
  exact (isPurelyInseparable_iff_pow_mem k p).2 fun y => ⟨1, by
    rw [pow_one]; exact pow_mem_range k p x y⟩

/-- Oqhr-Gt66es-17116 (4:45:16) [prop] If `k` is perfect and `K, L` are extensions of `k`,
`K ⊗_k L` is reduced. Proved for `K` finite over `k` (`L` arbitrary). -/
theorem prop_17116 [PerfectField k] (K L : Type u) [Field K] [Field L] [Algebra k K]
    [Algebra k L] [FiniteDimensional k K] : IsReduced (L ⊗[k] K) :=
  isReduced_tensor_of_isSeparable k K L

/-- Oqhr-Gt66es-17370 (4:49:30) [prop] For a `k`-algebra `A`, the conditions defining geometric
reducedness are equivalent. Mathlib's definition (`Algebra.IsGeometricallyReduced`: `k̄ ⊗_k A`
reduced) gives `A` reduced and `K ⊗_k A` reduced for every algebraic extension `K`; the other
implications are not formalised. -/
theorem prop_17370 (A : Type u) [CommRing A] [Algebra k A] [Algebra.IsGeometricallyReduced k A] :
    IsReduced A ∧ ∀ (K : Type u) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K],
      IsReduced (K ⊗[k] A) :=
  ⟨Algebra.isReduced_of_isGeometricallyReduced k, fun _ _ _ _ => inferInstance⟩

/-- Oqhr-Gt66es-17834 (4:57:14) [def] A `k`-scheme is geometrically reduced (separable) if its base
changes are reduced (mathlib: `GeometricallyReduced`, base changes to all fields). -/
example : @GeometricallyReduced = geometrically AlgebraicGeometry.IsReduced :=
  GeometricallyReduced.eq_geometrically

/-- Oqhr-Gt66es-17899 (4:58:19) [prop] A separable `k`-algebra is reduced; the converse holds for
every algebra only if `k` is perfect. Proved: both statements (the second with `k' = k[t]/(tᵖ - x)`,
a field, reduced and not geometrically reduced); that the converse holds when `k` is perfect is
not formalised. -/
theorem prop_17899 (p : ℕ) [Fact p.Prime] [CharP k p] :
    (∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra.IsGeometricallyReduced k A],
      IsReduced A) ∧
    (¬ PerfectField k → ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      IsReduced K ∧ ¬ Algebra.IsGeometricallyReduced k K) := by
  refine ⟨fun A _ _ _ => Algebra.isReduced_of_isGeometricallyReduced k, fun h => ?_⟩
  obtain ⟨K, _, _, hfin, -, hnr⟩ := (prop_16790 k p).2 h
  refine ⟨K, inferInstance, inferInstance, inferInstance, fun hg => hnr ?_⟩
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  infer_instance

/-- Oqhr-Gt66es-17970 (4:59:30) [prop] For every extension `k'/k`, `X` is separable over `k` iff
`X_{k'}` is over `k'`. Proved: the direction ⇒ (stability under base change); ⇐ not formalised. -/
theorem prop_17970 {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [GeometricallyReduced f]
    (k' : Type u) [Field k'] (φ : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) :
    GeometricallyReduced (pullback.snd f φ) :=
  inferInstance

end Perfect

/-! ### Separably closed fields and geometric irreducibility -/

section SepClosed

variable (k : Type u) [Field k]

/-- Oqhr-Gt66es-18099 (5:01:39) [prop] `k` is separably closed iff its algebraic extensions are
purely inseparable (mathlib: `isSepClosed_iff_isPurelyInseparable_algebraicClosure`,
`Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`); in characteristic zero every field is
perfect and separably closed is equivalent to algebraically closed. -/
theorem prop_18099 :
    (IsSepClosed k ↔ IsPurelyInseparable k (AlgebraicClosure k)) ∧
    (∀ (K : Type u) [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] [IsSepClosed k],
      IsPurelyInseparable k K) ∧
    (CharZero k → PerfectField k ∧ (IsSepClosed k ↔ IsAlgClosed k)) := by
  refine ⟨isSepClosed_iff_isPurelyInseparable_algebraicClosure k _, fun K _ _ _ _ => inferInstance,
    fun _ => ⟨inferInstance, fun _ => IsSepClosed.isAlgClosed_of_perfectField k,
      fun _ => inferInstance⟩⟩

/-- Oqhr-Gt66es-18295 (5:04:55) [prop] `k` is separably closed iff, among others, `k' ⊗_k k'` is an
integral domain for every finite Galois extension `k'`. Proved: the key step of (4) ⇒ (1): if
`k' ⊗_k k'` is a domain for a finite extension `k'`, then `k' = k` (a finite-dimensional domain is a
field, so `k' ⊗_k k' → k'` is injective and `[k' : k]² ≤ [k' : k]`). -/
theorem prop_18295 (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
    [IsDomain (K ⊗[k] K)] : Module.finrank k K = 1 := by
  have : IsArtinianRing (K ⊗[k] K) := IsArtinianRing.of_finite k (K ⊗[k] K)
  have hf : IsField (K ⊗[k] K) := IsArtinianRing.isField_of_isDomain _
  let F : Field (K ⊗[k] K) := hf.toField
  have hinj : Function.Injective (Algebra.TensorProduct.lmul' k : K ⊗[k] K →ₐ[k] K) :=
    RingHom.injective (Algebra.TensorProduct.lmul' k : K ⊗[k] K →ₐ[k] K).toRingHom
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (Algebra.TensorProduct.lmul' k : K ⊗[k] K →ₐ[k] K).toLinearMap) hinj
  rw [Module.finrank_tensorProduct] at hle
  have hpos : 0 < Module.finrank k K := Module.finrank_pos
  nlinarith

/-- Oqhr-Gt66es-18552 (5:09:12) [prop] Geometric irreducibility. Mathlib's definition
(`GeometricallyIrreducible`: every base change to a field is irreducible) gives: `X_{k'}` is
irreducible for every extension `k'`; the other equivalences are not formalised. -/
theorem prop_18552 {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [GeometricallyIrreducible f]
    (k' : Type u) [Field k'] (φ : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) :
    IrreducibleSpace ↥(pullback f φ) := by
  have h : geometrically (fun X => IrreducibleSpace X) f := by
    rw [← GeometricallyIrreducible.eq_geometrically]; infer_instance
  exact pullback_of_geometrically h k' φ

/-- Oqhr-Gt66es-19341 (5:22:21) [prop] A geometrically irreducible `k`-scheme is irreducible
(mathlib: `GeometricallyIrreducible.irreducibleSpace_of_subsingleton`); the converse for every `X`
iff `k` separably closed is not formalised. -/
theorem prop_19341 {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [GeometricallyIrreducible f] :
    IrreducibleSpace X :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton f

/-- Oqhr-Gt66es-19407 (5:23:27) [prop] For every extension `k'/k`, `X` is geometrically irreducible
over `k` iff `X_{k'}` is over `k'`. Proved: ⇒ (stability under base change). -/
theorem prop_19407 {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [GeometricallyIrreducible f]
    (k' : Type u) [Field k'] (φ : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) :
    GeometricallyIrreducible (pullback.snd f φ) :=
  inferInstance

end SepClosed

end

end Buffalo.AG.Part06
