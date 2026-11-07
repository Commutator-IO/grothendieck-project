import Mathlib

/-!
# Buffalo, algebraic geometry, part 07 (a): 26 June 1973, from 5:24:53

The entries of `docs/buffalo-ag/index.tex` lines 907–940 (video `Oqhr-Gt66es`, 5:24:53–6:43:27):
geometric integrality and connectedness (with the tensor squares of finite extensions of `k`),
and complements on subschemes and coherence.

Conventions. A `k`-scheme is a morphism `f : X ⟶ Spec k`; `X_{k'}` is the pullback along
`Spec k' → Spec k`. Mathlib's `GeometricallyIrreducible`, `GeometricallyConnected`,
`GeometricallyReduced` ("separable") and `GeometricallyIntegral` are the notions of the lecture.
Universal openness of a scheme over a field, which the lecture uses freely, is not in mathlib in
general; it is assumed where needed, or deduced from flatness for schemes locally of finite
presentation.
-/

open TensorProduct Polynomial AlgebraicGeometry CategoryTheory Limits PrimeSpectrum Topology

universe u

namespace Buffalo.AG.Part07

noncomputable section

/-! ### Tensor squares of finite extensions -/

theorem finrank_eq_one_of_isDomain_tensor (k K : Type*) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsDomain (K ⊗[k] K)] : Module.finrank k K = 1 := by
  have hinj : Function.Injective (algebraMap k (K ⊗[k] K)) := (algebraMap k _).injective
  have hF : IsField (K ⊗[k] K) :=
    (Algebra.IsIntegral.isField_iff_isField hinj).1 (Field.toIsField k)
  let m := Algebra.TensorProduct.lmul' k (S := K)
  have hsurj : Function.Surjective m := fun x => ⟨x ⊗ₜ 1, by simp [m]⟩
  let := hF.toField
  have hbij : Function.Bijective m := ⟨m.toRingHom.injective, hsurj⟩
  have h := (AlgEquiv.ofBijective m hbij).toLinearEquiv.finrank_eq
  rw [Module.finrank_tensorProduct] at h
  have hpos : 0 < Module.finrank k K := Module.finrank_pos
  nlinarith

/-- A root in an extension of degree one comes from a root in the base. -/
theorem exists_eval_eq_zero_of_finrank_eq_one {k K : Type*} [Field k] [Field K] [Algebra k K]
    (h : Module.finrank k K = 1) (p : k[X]) (x : K) (hx : aeval x p = 0) : ∃ a, p.eval a = 0 := by
  have hx' : x ∈ (⊥ : Subalgebra k K) := by
    rw [Subalgebra.bot_eq_top_of_finrank_eq_one h]; trivial
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.1 hx'
  refine ⟨a, (algebraMap k K).injective ?_⟩
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval, hx, map_zero]

/-! ### Geometric irreducibility, integrality and connectedness -/

/-- Oqhr-Gt66es-19691 (5:28:11) [prop] (part) `k` is algebraically closed iff `k' ⊗_k k'` is an
integral domain for every finite extension `k'/k`. -/
theorem prop_19691 (k : Type u) [Field k] :
    IsAlgClosed k ↔ ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
      IsDomain (K ⊗[k] K) := by
  constructor
  · intro _ K _ _ _
    let e : K ≃ₐ[k] k := (AlgEquiv.ofBijective (Algebra.ofId k K)
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm
    let f : K ⊗[k] K ≃ₐ[k] k :=
      (Algebra.TensorProduct.congr e e).trans (Algebra.TensorProduct.lid k k)
    exact Function.Injective.isDomain f.toRingEquiv.toRingHom f.injective
  · intro H
    refine IsAlgClosed.of_exists_root k fun p hmon hirr => ?_
    have : Fact (Irreducible p) := ⟨hirr⟩
    have : FiniteDimensional k (AdjoinRoot p) :=
      (AdjoinRoot.powerBasis hirr.ne_zero).finite
    have h1 := finrank_eq_one_of_isDomain_tensor k (AdjoinRoot p)
    exact exists_eval_eq_zero_of_finrank_eq_one h1 p _ (AdjoinRoot.aeval_eq p ▸ AdjoinRoot.mk_self)

/-- `Spec R` is connected iff `0` and `1` are the only idempotents of `R`. -/
theorem preconnectedSpace_iff_idempotent (R : Type*) [CommRing R] :
    PreconnectedSpace (PrimeSpectrum R) ↔ ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  constructor
  · intro _ e he
    have hc := isClopen_basicOpen_of_mul_add e (1 - e) (by rw [mul_sub, mul_one, he.eq, sub_self])
      (by ring)
    rcases _root_.isClopen_iff.1 hc with h | h
    · left
      obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_eq_bot_iff e).1 (SetLike.coe_injective h)
      rw [← he.pow_succ_eq n, pow_succ, hn, zero_mul]
    · right
      have h1 : IsNilpotent (1 - e) := by
        refine (PrimeSpectrum.basicOpen_eq_bot_iff _).1 (SetLike.coe_injective (Set.eq_empty_of_forall_notMem ?_))
        intro p hp
        have hpe : p ∈ (basicOpen e : Set _) := h ▸ Set.mem_univ p
        have h0 : e * (1 - e) ∈ p.asIdeal := by
          rw [mul_sub, mul_one, he.eq, sub_self]; exact p.asIdeal.zero_mem
        rcases p.isPrime.mem_or_mem h0 with h' | h'
        · exact hpe h'
        · exact hp h'
      have he' : IsIdempotentElem (1 - e) := he.one_sub
      obtain ⟨n, hn⟩ := h1
      have : 1 - e = 0 := by rw [← he'.pow_succ_eq n, pow_succ, hn, zero_mul]
      exact (sub_eq_zero.1 this).symm
  · intro H
    refine preconnectedSpace_iff_clopen.2 fun s hs => ?_
    obtain ⟨e, he, rfl⟩ := exists_idempotent_basicOpen_eq_of_isClopen hs
    rcases H e he with rfl | rfl
    · left; simp
    · right; simp

section Geometric

/-- The base change `X_K → Spec K` of a `k`-scheme `X` along a field extension `K/k`. -/
abbrev baseChange {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (K : Type u)
    [Field K] [Algebra k K] : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
      Spec (.of K) :=
  pullback.snd _ _

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))

/-- Oqhr-Gt66es-19493 (5:24:53) [prop] (irreducible half) The product over `k` of two
geometrically irreducible (universally open) `k`-schemes is geometrically irreducible. -/
theorem prop_19493 [GeometricallyIrreducible f] [GeometricallyIrreducible g] [UniversallyOpen f]
    [UniversallyOpen g] : GeometricallyIrreducible (pullback.snd f g ≫ g) :=
  GeometricallyIrreducible.comp _ _

/-- Oqhr-Gt66es-19761 (5:29:21) [prop] (part) If `X` is geometrically integral over `k`, then
`X_{k'}` is integral for every extension `k'/k`. -/
theorem prop_19761 :
    GeometricallyIntegral f → ∀ (K : Type u) [Field K] [Algebra k K],
      IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := fun h K _ _ =>
  pullback_of_geometrically ((geometricallyIntegral_iff f).1 h) K _

/-- Oqhr-Gt66es-19828 (5:30:28) [def] `X` is geometrically integral iff geometrically reduced
("separable") and geometrically irreducible (mathlib: `GeometricallyIntegral`); it is then
integral. -/
theorem def_19828 :
    (GeometricallyIntegral f ↔ GeometricallyReduced f ∧ GeometricallyIrreducible f) ∧
    (GeometricallyIntegral f → IsIntegral X) := by
  refine ⟨?_, fun _ => GeometricallyIntegral.isIntegral_of_subsingleton f⟩
  rw [GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible]; rfl

/-- Oqhr-Gt66es-19891 (5:31:31) [prop] (one direction) Geometric integrality is preserved by
extension of the base field. -/
theorem prop_19891 [GeometricallyIntegral f] (K : Type u) [Field K] [Algebra k K] :
    GeometricallyIntegral (baseChange f K) := inferInstance

/-- Oqhr-Gt66es-19954 (5:32:34) [prop] (part) The product over `k` of a geometrically connected,
universally open `k`-scheme and a connected one is connected. -/
theorem prop_19954 [GeometricallyConnected f] [UniversallyOpen f] [ConnectedSpace Y] :
    ConnectedSpace ↥(pullback f g) := inferInstance

/-- Oqhr-Gt66es-20091 (5:34:51) [prop] (affine form) If `k'/k` is purely inseparable, the
projection `Spec(k' ⊗_k A) → Spec(k ⊗_k A)` is a homeomorphism. -/
theorem prop_20091 (k' A : Type u) [Field k'] [Algebra k k'] [IsPurelyInseparable k k'] [CommRing A]
    [Algebra k A] :
    IsHomeomorph (PrimeSpectrum.comap
      (Algebra.TensorProduct.map (Algebra.ofId k k') (.id k A)).toRingHom) :=
  PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable k k A k'

/-- Oqhr-Gt66es-20413 (5:40:13) [prop] For `Y` nonempty, the projection `X ×_k Y → X` is
surjective; it is open when `Y` is locally of finite presentation over `k` (then flat, hence
universally open). -/
theorem prop_20413 [Nonempty Y] :
    Surjective (pullback.fst f g) ∧
    (LocallyOfFinitePresentation g → IsOpenMap (pullback.fst f g)) := by
  have : Surjective g := ⟨fun y => by
    obtain ⟨x⟩ := ‹Nonempty Y›; exact ⟨x, Subsingleton.elim _ _⟩⟩
  refine ⟨inferInstance, fun _ => ?_⟩
  have : UniversallyOpen g := UniversallyOpen.of_flat g
  exact (pullback.fst f g).isOpenMap

/-- Oqhr-Gt66es-21315 (5:55:15) [prop] (part) The product of two geometrically connected
(universally open) `k`-schemes is geometrically connected; geometric connectedness is preserved by
extension of the base field. -/
theorem prop_21315 [GeometricallyConnected f] [GeometricallyConnected g] [UniversallyOpen f]
    [UniversallyOpen g] (K : Type u) [Field K] [Algebra k K] :
    GeometricallyConnected (pullback.snd f g ≫ g) ∧ GeometricallyConnected (baseChange f K) :=
  ⟨GeometricallyConnected.comp _ _, inferInstance⟩

/-- Oqhr-Gt66es-20993 (5:49:53) [prop] (part) Geometric connectedness (mathlib's
`GeometricallyConnected`) is the connectedness of `X_{k'}` for every extension `k'/k`; it implies
that `X ×_k Y` is connected for every connected `Y` (`X` universally open over `k`). -/
theorem prop_20993 :
    (GeometricallyConnected f ↔ ∀ (K : Type u) [Field K] [Algebra k K],
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) ∧
    (∀ [GeometricallyConnected f] [UniversallyOpen f] [ConnectedSpace Y],
      ConnectedSpace ↥(pullback f g)) := by
  refine ⟨?_, fun {_ _ _} => inferInstance⟩
  rw [geometricallyConnected_iff]
  exact geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms

/-- Oqhr-Gt66es-20993 (5:49:53) [prop] (first half) A geometrically connected `k`-scheme is
connected. -/
theorem prop_20993_conn [GeometricallyConnected f] : ConnectedSpace X :=
  GeometricallyConnected.connectedSpace_of_subsingleton f

/-- Oqhr-Gt66es-20476 (5:41:16) [prop] (nonempty half) If `X` is nonempty, so is `X_{k'}` for
every extension `k'/k`. -/
theorem prop_20476 [Nonempty X] (K : Type u) [Field K] [Algebra k K] :
    Nonempty ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    ⟨fun y => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨z, -⟩ := (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).surjective x
  exact ⟨z⟩

/-- Oqhr-Gt66es-20602 (5:43:22) [prop] (affine form) The fibre of `Spec B → Spec A` at `𝔭` is
`Spec(κ(𝔭) ⊗_A B)`: the primes of `B` over `𝔭` are those of `κ(𝔭) ⊗_A B`. -/
def prop_20602 (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A)
    [p.IsPrime] : ↑(p.primesOver B) ≃o PrimeSpectrum (p.Fiber B) :=
  PrimeSpectrum.primesOverOrderIsoFiber A B p

end Geometric

/-- Oqhr-Gt66es-20796 (5:46:36) [prop] (affine form) If `Spec(k' ⊗_k k')` is connected for every
finite Galois extension `k'/k`, then `k` is separably closed; for `k'/k` separable,
`k' ⊗_k k' ≃ k' × T` (the diagonal is open and closed), so `T = 0` and `[k':k] = 1`. -/
theorem prop_20796 (k : Type u) [Field k]
    (H : ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K],
      PreconnectedSpace (PrimeSpectrum (K ⊗[k] K))) : IsSepClosed k := by
  refine IsSepClosed.of_exists_root k fun p _ hirr hsep => ?_
  have := IsGalois.of_separable_splitting_field (E := p.SplittingField) hsep
  set L := p.SplittingField
  have := Algebra.FormallyUnramified.of_isSeparable k L
  obtain ⟨T, _, _, ⟨e⟩⟩ := Algebra.FormallyUnramified.exists_algEquiv_prod k L
  have hc := (preconnectedSpace_iff_idempotent _).1 (H L) (e.symm (1, 0))
    (by rw [IsIdempotentElem, ← map_mul]; simp)
  have hT : Subsingleton T := by
    rcases hc with h | h
    · have := congrArg (fun x => (e x).1) h; simp at this
    · have := congrArg (fun x => (e x).2) h; simp at this
      exact subsingleton_of_zero_eq_one this
  have hinj : Function.Injective ((RingHom.fst L T).comp e.toRingEquiv.toRingHom) := by
    intro x y hxy
    apply e.injective
    exact Prod.ext hxy (Subsingleton.elim _ _)
  have : IsDomain (L ⊗[k] L) := Function.Injective.isDomain _ hinj
  have h1 := finrank_eq_one_of_isDomain_tensor k L
  obtain ⟨x, hx⟩ := Polynomial.Splits.exists_eval_eq_zero (SplittingField.splits p)
    (by rw [degree_map]; exact (Polynomial.degree_pos_of_irreducible hirr).ne')
  exact exists_eval_eq_zero_of_finrank_eq_one h1 p x (by rwa [aeval_def, eval₂_eq_eval_map])

section DirectLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {G : ι → Type*}
  [∀ i, CommRing (G i)] (f : ∀ i j, i ≤ j → G i →+* G j)
  [DirectedSystem G fun i j h => f i j h]

/-- Oqhr-Gt66es-21188 (5:53:08) [prop] (affine form) A filtered inductive limit of rings whose
only idempotents are `0` and `1` (connected spectra) has only the idempotents `0` and `1`:
the filtered projective limit of the connected affine schemes `Spec G_i` is connected. -/
theorem prop_21188 (H : ∀ i (e : G i), IsIdempotentElem e → e = 0 ∨ e = 1)
    (e : Ring.DirectLimit G (fun i j h => f i j h)) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of e
  have h0 : Ring.DirectLimit.of G (fun i j h => f i j h) i (x * x - x) = 0 := by
    rw [map_sub, map_mul, he.eq, sub_self]
  obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact h0
  have hy : IsIdempotentElem (f i j hij x) := by
    rw [map_sub, map_mul, sub_eq_zero] at hj; exact hj
  rw [← Ring.DirectLimit.of_f (G := G) (f := fun i j h => f i j h) hij x]
  rcases H j _ hy with h | h <;> rw [h] <;> simp

/-- Oqhr-Gt66es-36375 (10:06:15) [prop] A filtered inductive limit of rings is zero iff one of
the rings is zero. -/
theorem prop_36375 :
    Subsingleton (Ring.DirectLimit G (fun i j h => f i j h)) ↔ ∃ i, Subsingleton (G i) := by
  constructor
  · intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    have h1 : Ring.DirectLimit.of G (fun i j h => f i j h) i 1 = 0 := Subsingleton.elim _ _
    obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact h1
    exact ⟨j, subsingleton_of_zero_eq_one (by rw [← hj, map_one])⟩
  · rintro ⟨i, hi⟩
    refine subsingleton_of_zero_eq_one ?_
    rw [← map_zero (Ring.DirectLimit.of G (fun i j h => f i j h) i),
      ← map_one (Ring.DirectLimit.of G (fun i j h => f i j h) i), Subsingleton.elim (0 : G i) 1]

end DirectLimit

/-! ### Complements on subschemes and coherence -/

section Subsheaves

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type*}

/-- Oqhr-Gt66es-21601 (6:00:01) [prop] For subsheaves `F_i` of a sheaf `F`, the supremum is the
sheafification of the union `⋃ F_i`: a subsheaf containing the `F_i`, the smallest one, and its
sections over `U` are those that belong locally (on a covering sieve) to one of the `F_i`. -/
theorem prop_21601 (hF : Presieve.IsSheaf J F) {ι : Type*} (G : ι → Subfunctor F) :
    (∀ i, G i ≤ (⨆ i, G i).sheafify J) ∧ Presieve.IsSheaf J ((⨆ i, G i).sheafify J).toFunctor ∧
    (∀ G' : Subfunctor F, Presieve.IsSheaf J G'.toFunctor → (∀ i, G i ≤ G') →
      (⨆ i, G i).sheafify J ≤ G') ∧
    (∀ U s, s ∈ ((⨆ i, G i).sheafify J).obj U ↔
      Sieve.mk (fun V (g : V ⟶ U.unop) => ∃ i, F.map g.op s ∈ (G i).obj (Opposite.op V))
        (fun {V W} g hg h => by
          obtain ⟨i, hi⟩ := hg
          exact ⟨i, by rw [op_comp, F.map_comp, types_comp_apply]; exact (G i).map h.op hi⟩) ∈
        J U.unop) := by
  refine ⟨fun i => (le_iSup G i).trans (Subfunctor.le_sheafify J _),
    Subfunctor.sheafify_isSheaf _ hF, fun G' hG' hle => Subfunctor.sheafify_le _ _ (iSup_le hle) hF hG',
    fun U s => ?_⟩
  change (⨆ i, G i).sieveOfSection s ∈ J U.unop ↔ _
  have : (⨆ i, G i).sieveOfSection s = Sieve.mk (fun V (g : V ⟶ U.unop) =>
      ∃ i, F.map g.op s ∈ (G i).obj (Opposite.op V)) (fun {V W} g hg h => by
          obtain ⟨i, hi⟩ := hg
          exact ⟨i, by rw [op_comp, F.map_comp, types_comp_apply]; exact (G i).map h.op hi⟩) := by
    ext V g
    simp [Subfunctor.sieveOfSection, Subfunctor.iSup_obj]
  rw [this]

end Subsheaves

/-- Oqhr-Gt66es-22510 (6:15:10) [def] (module form) A module is coherent if it is of finite type
and the kernel of every morphism `Rⁿ → M` is of finite type. -/
def IsCoherentModule (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Module.Finite R M ∧ ∀ (n : ℕ) (φ : (Fin n → R) →ₗ[R] M), (LinearMap.ker φ).FG

/-- Oqhr-Gt66es-22637 (6:17:17) [prop] (affine, noetherian form) Over a noetherian ring, coherent,
finitely presented and finite modules coincide; in particular the ring is coherent. -/
theorem prop_22637 (R M : Type*) [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] :
    (IsCoherentModule R M ↔ Module.Finite R M) ∧
    (Module.FinitePresentation R M ↔ Module.Finite R M) ∧ IsCoherentModule R R :=
  ⟨⟨fun h => h.1, fun h => ⟨h, fun _ _ => IsNoetherian.noetherian _⟩⟩,
    Module.finitePresentation_iff_finite R M, ⟨inferInstance, fun _ _ => IsNoetherian.noetherian _⟩⟩

/-- Oqhr-Gt66es-22572 (6:16:12) [thm] (noetherian form) Over a noetherian ring, coherent (= finite)
modules are stable under kernels (submodules), cokernels (quotients), images, finite sums and
extensions. -/
theorem thm_22572 (R : Type*) [CommRing R] [IsNoetherianRing R] {M N P : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] :
    (Module.Finite R N → ∀ K : Submodule R N, Module.Finite R K) ∧
    (Module.Finite R N → ∀ K : Submodule R N, Module.Finite R (N ⧸ K)) ∧
    (Module.Finite R M → Module.Finite R N → Module.Finite R (M × N)) ∧
    (∀ (f : M →ₗ[R] N) (g : N →ₗ[R] P), Function.Exact f g → Function.Surjective g →
      Module.Finite R M → Module.Finite R P → Module.Finite R N) :=
  ⟨fun _ _ => inferInstance, fun _ _ => inferInstance, fun _ _ => inferInstance,
    fun _ _ h hs _ _ => Module.Finite.of_exact h hs⟩

/-- Oqhr-Gt66es-22896 (6:21:36) [prop] (first half) A surjective open immersion is an
isomorphism (and conversely). -/
theorem prop_22896 {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion f ∧ Surjective f :=
  isIso_iff_isOpenImmersion_and_surjective f

/-- Oqhr-Gt66es-23161 (6:26:01) [prop] (affine form) For `Y` closed in `Spec A`, the ideal
`J_Y` of functions vanishing on `Y` is radical, `V(J_Y) = Y`, and it is the largest ideal `J`
with `V(J) = Y`. -/
theorem prop_23161 {A : Type*} [CommRing A] (Y : Set (PrimeSpectrum A)) (hY : IsClosed Y) :
    (vanishingIdeal Y).IsRadical ∧ zeroLocus (vanishingIdeal Y : Set A) = Y ∧
    ∀ J : Ideal A, zeroLocus (J : Set A) = Y → J ≤ vanishingIdeal Y := by
  refine ⟨isRadical_vanishingIdeal Y, by rw [zeroLocus_vanishingIdeal_eq_closure, hY.closure_eq],
    fun J hJ => ?_⟩
  rw [← hJ, vanishingIdeal_zeroLocus_eq_radical]
  exact Ideal.le_radical

/-- Oqhr-Gt66es-23290 (6:28:10) [prop] (affine form) `V(J^{n+1}) = V(J)`. -/
theorem prop_23290 {A : Type*} [CommRing A] (J : Ideal A) (n : ℕ) :
    zeroLocus ((J ^ (n + 1) : Ideal A) : Set A) = zeroLocus J :=
  zeroLocus_pow J n.succ_ne_zero

/-- Oqhr-Gt66es-23353 (6:29:13) [prop] (affine form) The closed immersion `Spec(A/J) → Spec A`
is onto (a homeomorphism) iff `J` is a nil ideal; it is an isomorphism only if `J = 0`. -/
theorem prop_23353 {A : Type*} [CommRing A] (J : Ideal A) :
    zeroLocus (J : Set A) = Set.univ ↔ J ≤ nilradical A :=
  zeroLocus_eq_univ_iff _

/-- Oqhr-Gt66es-23421 (6:30:21) [prop] Every locally noetherian scheme is quasi-separated. -/
theorem prop_23421 (X : Scheme.{u}) [IsLocallyNoetherian X] : QuasiSeparatedSpace X :=
  inferInstance

/-- Oqhr-Gt66es-23618 (6:33:38) [prop] (one direction) A coherent (quasi-compact
quasi-separated) scheme is a finite union of affine open sets with quasi-compact pairwise
intersections. -/
theorem prop_23618 (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ s : Finset X.affineOpens, (⋃ U ∈ s, (U : Set X)) = Set.univ ∧
      ∀ U ∈ s, ∀ V ∈ s, IsCompact ((U : Set X) ∩ V) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩)
  refine ⟨s, Set.eq_univ_of_univ_subset hs, fun U _ V _ => ?_⟩
  exact QuasiSeparatedSpace.inter_isCompact _ _ U.1.isOpen U.2.isCompact V.1.isOpen V.2.isCompact

/-- Oqhr-Gt66es-24145 (6:42:25) [def] An open set is retrocompact if its intersection with every
quasi-compact open set is quasi-compact (mathlib: `IsRetrocompact`). -/
theorem def_24145 {X : Type*} [TopologicalSpace X] (U : Set X) :
    IsRetrocompact U ↔ ∀ V, IsCompact V → IsOpen V → IsCompact (U ∩ V) := Iff.rfl

/-- `ℤ[1/2]`. -/
abbrev Z2 := Localization.Away (2 : ℤ)

/-- The componentwise map `∏ ℤ → ∏ ℤ[1/2]`. -/
def piToZ2 : (ℕ → ℤ) →+* (ℕ → Z2) :=
  RingHom.pi fun n => (algebraMap ℤ Z2).comp (Pi.evalRingHom _ n)

theorem piToZ2_apply (m : ℕ → ℤ) (n : ℕ) : piToZ2 m n = algebraMap ℤ Z2 (m n) := rfl

/-- The image of `2` in `∏ ℤ[1/2]` is a unit. -/
theorem isUnit_two_pi : IsUnit (piToZ2 2) := by
  refine isUnit_iff_exists_inv.2 ⟨fun _ => IsLocalization.mk' Z2 (1 : ℤ) ⟨2, Submonoid.mem_powers 2⟩,
    funext fun n => ?_⟩
  rw [Pi.mul_apply, piToZ2_apply, Pi.one_apply, Pi.ofNat_apply, IsLocalization.mul_mk'_eq_mk'_of_mul,
    mul_one]
  exact IsLocalization.mk'_self _ (Submonoid.mem_powers 2)

/-- The canonical map `(∏ ℤ)[1/2] → ∏ ℤ[1/2]`. -/
def piLocMap : Localization.Away (2 : ℕ → ℤ) →+* (ℕ → Z2) :=
  IsLocalization.Away.lift (2 : ℕ → ℤ) isUnit_two_pi

/-- Oqhr-Gt66es-24017 (6:40:17) [cex] (algebraic core) An infinite product of quasi-coherent
modules is not quasi-coherent in general: on `Spec ℤ`, the sections of `∏ ℤ~` over `D(2)` are
`∏ ℤ[1/2]`, which is not `(∏ ℤ)[1/2]`: the canonical map is not onto, `(1/2ⁿ)ₙ` is not in its
image. -/
theorem cex_24017 : ¬ Function.Surjective piLocMap := by
  intro h
  obtain ⟨y, hy⟩ := h fun n => IsLocalization.mk' Z2 (1 : ℤ)
    ⟨2 ^ n, (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩
  obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (2 : ℕ → ℤ)) y
  have key := congrArg piLocMap (IsLocalization.mk'_spec (Localization.Away (2 : ℕ → ℤ)) m
    ⟨(2 : ℕ → ℤ) ^ k, (Submonoid.mem_powers_iff _ _).2 ⟨k, rfl⟩⟩)
  dsimp only at hy
  rw [map_mul, hy] at key
  simp only [piLocMap, IsLocalization.Away.lift, IsLocalization.lift_eq] at key
  have h1 := congrFun key (k + 1)
  rw [Pi.mul_apply, piToZ2_apply, piToZ2_apply, Pi.pow_apply, Pi.ofNat_apply] at h1
  have hinj : Function.Injective (algebraMap ℤ Z2) :=
    IsLocalization.injective Z2 (powers_le_nonZeroDivisors_of_noZeroDivisors two_ne_zero)
  have h2 : algebraMap ℤ Z2 1 = algebraMap ℤ Z2 (2 * m (k + 1)) := by
    rw [map_mul, ← h1, ← mul_assoc, map_one]
    rw [mul_comm (algebraMap ℤ Z2 2), mul_assoc, ← map_mul, ← pow_succ',
      IsLocalization.mk'_spec_mk, map_one]
  have := hinj h2
  omega

end

end Buffalo.AG.Part07
