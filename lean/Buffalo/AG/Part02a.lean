import Buffalo.AG.Part01

/-!
# Buffalo, algebraic geometry, part 02 (a): 5 June 1973

The entries of `docs/buffalo-ag/index.tex` for the session of 5 June 1973 (video `51wmmpHand0`,
4:55:19–6:38:51): closed subspaces of an affine space and ideals of its ring, flatness tested on
algebras through the dual numbers `D_K(N)`, finite sums of affine spaces and idempotents,
connected and `0`-connected objects, points with values in fields and the prime spectrum, the
Zariski topology and irreducible spaces.

Notation as in `Buffalo.AG.Part01a`: `k` is a commutative ring (the lecture's `K`), `V k A` is the
functor `k' ↦ Hom_k(A, k')` represented by `A`, and `𝒞 = (CommAlgCat k)ᵒᵖ` is the category of
affine spaces over `k`.
-/

open CategoryTheory Limits

universe u

namespace Buffalo.AG.Part02

open Buffalo.AG.Part01

noncomputable section

section June5

variable (k : Type u) [CommRing k]

/-- A point of `V_A` with values in `k'`, seen as a homomorphism `A → k'`. -/
abbrev pt {A : Type u} [CommRing A] [Algebra k A] {k' : CommAlgCat.{u} k} (x : (V k A).obj k') :
    A →ₐ[k] k' := x

/-! ### Closed subspaces, flatness and dual numbers -/

/-- 51wmmpHand0-17855 (4:57:35) [prop] The functor represented by `K[T]` is `K' ↦ K'`
(`Buffalo.AG.Part01.E1.corepresentableBy`); that of `K[T, T⁻¹]` is `K' ↦ K'ˣ`: a homomorphism
`K[T, T⁻¹] → K'` is determined by the image of `T`, which can be any unit, and it restricts along
`K[T] → K[T, T⁻¹]` to the point `T ↦ u(T)` of `K'`. -/
theorem prop_17855 (k' : Type*) [CommRing k'] [Algebra k k'] :
    Function.Injective (fun φ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k' =>
        φ (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))
          Polynomial.X)) ∧
      Set.range (fun φ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k' =>
        φ (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))
          Polynomial.X)) = {t | IsUnit t} := by
  let L := Localization.Away (Polynomial.X : Polynomial k)
  let ι : Polynomial k →ₐ[k] L := IsScalarTower.toAlgHom k _ _
  refine ⟨fun u v huv => ?_, ?_⟩
  · have h1 : u.comp ι = v.comp ι := Polynomial.algHom_ext huv
    have h2 : u.toRingHom.comp (algebraMap (Polynomial k) L) =
        v.toRingHom.comp (algebraMap (Polynomial k) L) :=
      RingHom.ext fun p => DFunLike.congr_fun h1 p
    have := IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial k)) h2
    exact AlgHom.ext fun x => DFunLike.congr_fun this x
  · ext t
    constructor
    · rintro ⟨u, rfl⟩
      exact (IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial k)).map u
    · intro ht
      let g : Polynomial k →+* k' := (Polynomial.aeval t).toRingHom
      have hg : IsUnit (g Polynomial.X) := by simpa [g] using ht
      let l : L →+* k' := IsLocalization.Away.lift (Polynomial.X : Polynomial k) hg
      have hl : ∀ p, l (algebraMap _ _ p) = Polynomial.aeval t p :=
        fun p => IsLocalization.lift_eq _ p
      refine ⟨{ l with commutes' := fun c => ?_ }, ?_⟩
      · change l (algebraMap k L c) = _
        rw [IsScalarTower.algebraMap_apply k (Polynomial k) L, hl]
        exact (Polynomial.aeval t).commutes c
      · change l _ = _
        rw [hl, Polynomial.aeval_X]

/-- 51wmmpHand0-18250 (5:04:10) [prop] If `X = V_A`, the point `id_A ∈ X(A)` is universal: every
point `x ∈ X(K')` is the image of `id_A` under a unique homomorphism `A → K'`. -/
theorem prop_18250 (A : Type u) [CommRing A] [Algebra k A] (k' : CommAlgCat.{u} k)
    (x : (V k A).obj k') :
    ∃! h : CommAlgCat.of k A ⟶ k', (V k A).map h (AlgHom.id k A) = x := by
  refine ⟨hm k (A := CommAlgCat.of k A) x, AlgHom.ext fun _ => rfl, fun h hh => ?_⟩
  apply CommAlgCat.hom_ext
  rw [← hh]
  rfl

/-- The morphism `V_B → V_A` defined by a homomorphism `f : A → B`. -/
def Vmap {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (f : A →ₐ[k] B) :
    V k B ⟶ V k A where
  app _ := ↾fun φ => φ.comp f

/-- 51wmmpHand0-18383 (5:06:23) [prop] A homomorphism `f : A → B` of `K`-algebras is an
epimorphism if and only if `V_B → V_A` is a monomorphism of functors (a subfunctor). -/
theorem prop_18383 {A B : CommAlgCat.{u} k} (f : A ⟶ B) : Epi f ↔ Mono (Vmap k f.hom) := by
  rw [NatTrans.mono_iff_mono_app]
  simp_rw [mono_iff_injective]
  constructor
  · intro hf k' φ ψ h
    have h' : f ≫ hm k (A := B) (B := k') φ = f ≫ hm k (A := B) (B := k') ψ :=
      CommAlgCat.hom_ext h
    exact congrArg (fun g => g.hom) (cancel_epi f |>.1 h')
  · intro h
    refine ⟨fun {C} g g' hgg => CommAlgCat.hom_ext (h C ?_)⟩
    exact congrArg (fun g => g.hom) hgg

/-- 51wmmpHand0-18446 (5:07:26) [cex] An epimorphism of rings need not be surjective:
`ℤ → ℚ`. -/
theorem cex_18446 :
    Epi (CommRingCat.ofHom (Int.castRingHom ℚ)) ∧ ¬ Function.Surjective (Int.castRingHom ℚ) := by
  refine ⟨⟨fun g h _ => CommRingCat.hom_ext (RingHom.ext_rat _ _)⟩, fun hs => ?_⟩
  obtain ⟨n, hn⟩ := hs (1 / 2)
  have h2 : ((2 * n : ℤ) : ℚ) = 1 := by
    push_cast
    rw [show ((n : ℤ) : ℚ) = Int.castRingHom ℚ n from rfl, hn]
    norm_num
  have : 2 * n = 1 := by exact_mod_cast h2
  omega

/-- 51wmmpHand0-18708 (5:11:48) [prop] For `X = V_A` and an ideal `J` of `A`, the subfunctor
`Y_J : K' ↦ {u ∈ Hom(A, K') | u(J) = 0}` of `X`. -/
def YJ {A : Type u} [CommRing A] [Algebra k A] (J : Ideal A) : Subfunctor (V k A) where
  obj k' := {u : A →ₐ[k] k' | ∀ f ∈ J, u f = 0}
  map {k' k''} g u hu f hf := by
    change g (pt k u f) = 0
    rw [hu f hf, map_zero]

/-- 51wmmpHand0-18446 (5:07:26) [cex] The surjective homomorphisms `f : A → B` correspond to
closed immersions: `V_B → V_A` is then injective, with image the closed subspace `Y_{ker f}`. -/
theorem cex_18446_surj {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (f : A →ₐ[k] B) (hf : Function.Surjective f) (k' : CommAlgCat.{u} k) :
    Function.Injective ((Vmap k f).app k') ∧ ∀ x : (V k A).obj k',
      x ∈ (YJ k (RingHom.ker f)).obj k' ↔ x ∈ Set.range ((Vmap k f).app k') := by
  refine ⟨fun φ ψ h => AlgHom.ext fun b => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨a, rfl⟩ := hf b
    exact DFunLike.congr_fun (show (pt k φ).comp f = (pt k ψ).comp f from h) a
  · let e := Ideal.quotientKerAlgEquivOfSurjective hf
    let ψ : B →ₐ[k] k' := (Ideal.Quotient.liftₐ (RingHom.ker f) (pt k x) hx).comp e.symm.toAlgHom
    refine ⟨ψ, AlgHom.ext fun a => ?_⟩
    have he : e.symm (f a) = Ideal.Quotient.mk _ a := e.symm_apply_eq.2 rfl
    change Ideal.Quotient.liftₐ (RingHom.ker f) (pt k x) hx (e.symm (f a)) = pt k x a
    rw [he]
    rfl
  · rintro ⟨φ, rfl⟩ a ha
    change pt k φ (f a) = 0
    rw [(RingHom.mem_ker).1 ha, map_zero]

/-- 51wmmpHand0-18773 (5:12:53) [prop] The ideal `J` is recovered from `Y_J` as the set of
`f ∈ A` such that `x(f) = 0` for every `K'` and every `x ∈ Y_J(K')` (it suffices to take
`K' = A/J`). -/
theorem prop_18773 {A : Type u} [CommRing A] [Algebra k A] (J : Ideal A) (f : A) :
    f ∈ J ↔ ∀ (k' : CommAlgCat.{u} k) (x : (V k A).obj k'), x ∈ (YJ k J).obj k' → pt k x f = 0 := by
  refine ⟨fun hf k' x hx => hx f hf, fun h => ?_⟩
  have := h (CommAlgCat.of k (A ⧸ J)) (Ideal.Quotient.mkₐ k J) fun g hg =>
    Ideal.Quotient.eq_zero_iff_mem.2 hg
  exact Ideal.Quotient.eq_zero_iff_mem.1 this

/-- 51wmmpHand0-18708 (5:11:48) [prop] `Y_J` is a closed subspace of `X = V_A`: it is represented
by `A/J`. -/
def YJ.corepresentableBy {A : Type u} [CommRing A] [Algebra k A] (J : Ideal A) :
    (YJ k J).toFunctor.CorepresentableBy (CommAlgCat.of k (A ⧸ J)) where
  homEquiv {k'} :=
    { toFun := fun φ => ⟨φ.hom.comp (Ideal.Quotient.mkₐ k J), fun f hf => by
        change φ.hom (Ideal.Quotient.mk J f) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]⟩
      invFun := fun x => CommAlgCat.ofHom (Ideal.Quotient.liftₐ J (pt k x.1) x.2)
      left_inv := fun φ => by
        apply CommAlgCat.hom_ext
        exact Ideal.Quotient.algHom_ext _ (AlgHom.ext fun _ => rfl)
      right_inv := fun x => Subtype.ext (AlgHom.ext fun _ => rfl) }
  homEquiv_comp _ _ := rfl

/-- 51wmmpHand0-18708 (5:11:48) [prop] `J ↦ Y_J` is an order-reversing bijection from the ideals
of `A` onto the closed subspaces `Y_J` of `X`. -/
theorem prop_18708 {A : Type u} [CommRing A] [Algebra k A] :
    (∀ J J' : Ideal A, J ≤ J' ↔ YJ k J' ≤ YJ k J) ∧ Function.Injective (YJ k (A := A)) := by
  have key : ∀ J J' : Ideal A, J ≤ J' ↔ YJ k J' ≤ YJ k J := fun J J' =>
    ⟨fun h k' x hx f hf => hx f (h hf), fun h f hf =>
      (prop_18773 k J' f).2 fun k' x hx => h k' hx f hf⟩
  exact ⟨key, fun J J' h => le_antisymm ((key J J').2 h.symm.le) ((key J' J).2 h.le)⟩

/-- 51wmmpHand0-18837 (5:13:57) [disc] Not every subfunctor of an affine space is closed: the
subfunctor `K' ↦ K'ˣ` of the line `V_{K[T]}` (points sending `T` to a unit) is not of the form
`Y_J` when `K ≠ 0`. -/
theorem disc_18837 [Nontrivial k] :
    ¬ ∃ J : Ideal (Polynomial k), ∀ (k' : CommAlgCat.{u} k) (x : (V k (Polynomial k)).obj k'),
      x ∈ (YJ k J).obj k' ↔ IsUnit (pt k x Polynomial.X) := by
  rintro ⟨J, hJ⟩
  have hJ0 : J = ⊥ := by
    refine (Submodule.eq_bot_iff J).2 fun f hf => ?_
    let x : Polynomial k →ₐ[k] LaurentPolynomial k :=
      { Polynomial.toLaurent with commutes' := fun c => by simp }
    have hx := (hJ (CommAlgCat.of k (LaurentPolynomial k)) x).2 (by
      change IsUnit (Polynomial.toLaurent Polynomial.X)
      rw [Polynomial.toLaurent_X]
      exact LaurentPolynomial.isUnit_T 1)
    exact Polynomial.toLaurent_injective ((hx f hf).trans (map_zero _).symm)
  have h0 := (hJ (CommAlgCat.of k k) (Polynomial.aeval (0 : k))).1 fun f hf => by
    rw [hJ0] at hf
    rw [(Submodule.mem_bot _).1 hf, map_zero]
  simp at h0

/-- 51wmmpHand0-18901 (5:15:01) [prop] The ring `A` is identified with `Hom(X, 𝔸¹_K)`:
`f ∈ A` defines `x ↦ x(f)`, functorially in `K'` (`Buffalo.AG.Part01.prop_9373`). -/
theorem prop_18901 (A : Type u) [CommRing A] [Algebra k A] (a : A) (k' : CommAlgCat.{u} k)
    (x : (V k A).obj k') : ((prop_9373 k A).symm a).app k' x = (show A →ₐ[k] k' from x) a :=
  prop_9373_apply k A a k' x

/-- 51wmmpHand0-19161 (5:19:21) [def] The algebra of dual numbers `D_K(N) = K × N` (mathlib's
trivial square-zero extension `TrivSqZeroExt K N`). -/
abbrev D (N : Type*) [AddCommGroup N] [Module k N] [Module kᵐᵒᵖ N] [IsCentralScalar k N] :=
  TrivSqZeroExt k N

/-- 51wmmpHand0-19161 (5:19:21) [def] In `D_K(N)`, `(λ, x)(λ', x') = (λλ', λx' + λ'x)`, `N` is an
ideal of square zero, and `D_K(N)` is functorial in `N`. -/
theorem def_19161 {N N' N'' : Type*} [AddCommGroup N] [Module k N] [Module kᵐᵒᵖ N]
    [IsCentralScalar k N] [AddCommGroup N'] [Module k N'] [Module kᵐᵒᵖ N'] [IsCentralScalar k N']
    [AddCommGroup N''] [Module k N''] [Module kᵐᵒᵖ N''] [IsCentralScalar k N'']
    (p q : D k N) (x y : N) (f : N →ₗ[k] N') (g : N' →ₗ[k] N'') :
    (p * q).fst = p.fst * q.fst ∧ (p * q).snd = p.fst • q.snd + q.fst • p.snd ∧
      (TrivSqZeroExt.inr x : D k N) * TrivSqZeroExt.inr y = 0 ∧
      (TrivSqZeroExt.map g).comp (TrivSqZeroExt.map f) = TrivSqZeroExt.map (g ∘ₗ f) ∧
      TrivSqZeroExt.map (LinearMap.id : N →ₗ[k] N) = AlgHom.id k _ := by
  refine ⟨rfl, ?_, TrivSqZeroExt.inr_mul_inr k x y, (TrivSqZeroExt.map_comp_map f g).symm,
    TrivSqZeroExt.map_id⟩
  rw [TrivSqZeroExt.snd_mul, op_smul_eq_smul]

/-- `D_K(N) = K × N` as a `K`-module. -/
@[simps apply]
def tauD (N : Type*) [AddCommGroup N] [Module k N] [Module kᵐᵒᵖ N] [IsCentralScalar k N] :
    D k N ≃ₗ[k] k × N where
  toFun p := (p.fst, p.snd)
  invFun q := TrivSqZeroExt.inl q.1 + TrivSqZeroExt.inr q.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv p := by ext <;> simp
  right_inv q := by ext <;> simp

/-- 51wmmpHand0-19362 (5:22:42) [prop] `M ⊗_K D_K(N) ≃ M ⊕ (M ⊗_K N)` (as `K`-modules). -/
def prop_19362 (M N : Type*) [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [Module kᵐᵒᵖ N] [IsCentralScalar k N] :
    TensorProduct k M (D k N) ≃ₗ[k] M × TensorProduct k M N :=
  ((tauD k N).lTensor M).trans <| (TensorProduct.prodRight k k M k N).trans
    (LinearEquiv.prodCongr (TensorProduct.rid k M) (LinearEquiv.refl k _))

/-- 51wmmpHand0-19362 (5:22:42) [prop] The isomorphism `M ⊗ D_K(N) ≃ M ⊕ (M ⊗ N)` is functorial
in `N`: it carries `M ⊗ D(f)` to `id ⊕ (M ⊗ f)`. -/
theorem prop_19362_natural (M N N' : Type*) [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k N] [Module kᵐᵒᵖ N] [IsCentralScalar k N] [AddCommGroup N'] [Module k N']
    [Module kᵐᵒᵖ N'] [IsCentralScalar k N'] (f : N →ₗ[k] N') (z : TensorProduct k M (D k N)) :
    prop_19362 k M N' ((TrivSqZeroExt.map f).toLinearMap.lTensor M z) =
      Prod.map id (f.lTensor M) (prop_19362 k M N z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m p =>
    simp [prop_19362, tauD_apply, TensorProduct.prodRight_tmul]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    ext <;> simp

/-- 51wmmpHand0-19097 (5:18:17) [prop] A `K`-module `M` is flat if and only if
`M ⊗ K' → M ⊗ K''` is injective for every injective homomorphism of `K`-algebras `K' → K''`
(test with `D_K(J) → D_K(K)` for the ideals `J` of `K`, by `prop_19362`). -/
theorem prop_19097 (M : Type u) [AddCommGroup M] [Module k M] :
    Module.Flat k M ↔ ∀ (K' K'' : Type u) [CommRing K'] [CommRing K''] [Algebra k K']
      [Algebra k K''] (f : K' →ₐ[k] K''), Function.Injective f →
        Function.Injective (f.toLinearMap.lTensor M) := by
  constructor
  · intro _ K' K'' _ _ _ _ f hf
    exact Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  · intro h
    rw [Module.Flat.iff_lTensor_injective']
    intro J x y hxy
    have hinj : Function.Injective (TrivSqZeroExt.map J.subtype : D k J →ₐ[k] D k k) := by
      intro p q hpq
      have h1 := congrArg TrivSqZeroExt.fst hpq
      have h2 := congrArg TrivSqZeroExt.snd hpq
      simp only [TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map] at h1 h2
      exact TrivSqZeroExt.ext h1 (Subtype.val_injective h2)
    have H := h (D k J) (D k k) _ hinj
    let x' := (prop_19362 k M J).symm (0, x)
    let y' := (prop_19362 k M J).symm (0, y)
    have : x' = y' := by
      apply H
      apply (prop_19362 k M k).injective
      rw [prop_19362_natural, prop_19362_natural]
      simp only [x', y', LinearEquiv.apply_symm_apply, Prod.map_apply, id]
      exact congrArg _ hxy
    simpa [x', y'] using this

/-- 51wmmpHand0-19491 (5:24:51) [prop] Products of affine spaces correspond to tensor products of
algebras (`Buffalo.AG.Part01.prop_10867`, `prop_11633`) and fibre products to `A ⊗_C B`
(`Buffalo.AG.Part01.prop_12165`): `Hom(A ⊗_K B, C) ≃ Hom(A, C) × Hom(B, C)`. -/
def prop_19491 (A B C : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    [CommRing C] [Algebra k C] :
    (TensorProduct k A B →ₐ[k] C) ≃ (A →ₐ[k] C) × (B →ₐ[k] C) :=
  prop_10867 k A B C

/-- 51wmmpHand0-19491 (5:24:51) [prop] The kernel of `u, v : A ⇉ B` of algebras (the equalizer of
the corresponding pair `V_B ⇉ V_A`) is the closed subspace `Y_J` of `V_B` defined by the ideal `J`
generated by the `u(x) - v(x)`; it is represented by `B/J` (`Buffalo.AG.Part01.prop_13847`). -/
theorem prop_19491_ker {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (u v : A →ₐ[k] B) (k' : CommAlgCat.{u} k) (w : (V k B).obj k') :
    w ∈ (YJ k (Ideal.span (Set.range fun x => u x - v x))).obj k' ↔
      (pt k w).comp u = (pt k w).comp v := by
  constructor
  · intro hw
    ext x
    have := hw (u x - v x) (Ideal.subset_span ⟨x, rfl⟩)
    change pt k w (u x - v x) = 0 at this
    rw [map_sub, sub_eq_zero] at this
    exact this
  · intro hw f hf
    have hle : Ideal.span (Set.range fun x => u x - v x) ≤
        RingHom.ker (pt k w) := Ideal.span_le.2 (by
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, sub_eq_zero]
      exact DFunLike.congr_fun hw x)
    exact hle hf

/-- 51wmmpHand0-19557 (5:25:57) [prop] The kernel of `G = V_A → H = V_B` (given by `φ : B → A`,
with unit section `ε : B → K`) is the closed subspace `Y_J` of `G` with `J = φ(ker ε)A`; the
stabilizer of a rational point is likewise the equalizer of two morphisms `G → X`, closed by
`prop_19491_ker`. -/
theorem prop_19557 {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (φ : B →ₐ[k] A) (ε : B →ₐ[k] k) (k' : CommAlgCat.{u} k) (g : (V k A).obj k') :
    g ∈ (YJ k ((RingHom.ker ε).map φ)).obj k' ↔
      (pt k g).comp φ = (Algebra.ofId k k').comp ε :=
  kills_iff k φ ε g

/-- The zero algebra receives no homomorphism, except into a zero algebra. -/
def toSubsingleton (A B : Type*) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    [Subsingleton B] : A →ₐ[k] B where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := rfl
  map_add' _ _ := Subsingleton.elim _ _
  commutes' _ := Subsingleton.elim _ _

/-- A zero algebra is a final object of `CommAlgCat k`. -/
def isTerminalOfSubsingleton (B : CommAlgCat.{u} k) [Subsingleton B] : IsTerminal B :=
  IsTerminal.ofUniqueHom (fun A => hm k (toSubsingleton k A B))
    fun _ _ => CommAlgCat.hom_ext (AlgHom.ext fun _ => Subsingleton.elim _ _)

/-- An algebra whose affine space is initial in `𝒞` is zero. -/
theorem subsingleton_of_isInitial {B : CommAlgCat.{u} k} (h : IsInitial (Opposite.op B)) :
    Subsingleton B := by
  let P := CommAlgCat.of k (Polynomial k)
  have := h.hom_ext (hm k (A := P) (B := B) (Polynomial.aeval 0)).op
    (hm k (A := P) (B := B) (Polynomial.aeval 1)).op
  have h01 := congrArg (fun f => f.unop.hom Polynomial.X) this
  simp only [Quiver.Hom.unop_op, ConcreteCategory.hom_ofHom] at h01
  have h01' : (0 : B) = 1 := by erw [Polynomial.aeval_X, Polynomial.aeval_X] at h01; exact h01
  exact subsingleton_of_zero_eq_one h01'

/-- An affine space is initial in `𝒞` if and only if its ring is zero. -/
theorem nonempty_isInitial_iff (B : CommAlgCat.{u} k) :
    Nonempty (IsInitial (Opposite.op B)) ↔ Subsingleton B :=
  ⟨fun ⟨h⟩ => subsingleton_of_isInitial k h, fun _ => ⟨(isTerminalOfSubsingleton k B).op⟩⟩

/-- 51wmmpHand0-19684 (5:28:04) [rem] The embedding of affine spaces into functors commutes with
projective limits (`Buffalo.AG.Part01.prop_11436`) but not with inductive limits: the sum of two
copies of the final object `V_K` is `V_{K × K}`, but at `K' = 0` the sum of functors has two points
and `V_{K × K}(0)` only one. -/
theorem rem_19684 :
    ¬ Function.Injective (fun x : (V k k).obj (CommAlgCat.of k PUnit.{u + 1}) ⊕
        (V k k).obj (CommAlgCat.of k PUnit.{u + 1}) =>
      (x.elim (fun φ => φ.comp (AlgHom.fst k k k)) (fun φ => φ.comp (AlgHom.snd k k k)) :
        k × k →ₐ[k] PUnit.{u + 1})) := fun h => by
  have := @h (Sum.inl (toSubsingleton k k PUnit)) (Sum.inr (toSubsingleton k k PUnit))
    (AlgHom.ext fun _ => Subsingleton.elim _ _)
  exact Sum.inl_ne_inr this

/-! ### Sums and connectedness -/

section Sums

variable {ι : Type u} (A : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra k (A i)]

/-- The product `∏ A_i` with its projections, as a fan in `CommAlgCat k`. -/
def piFan : Fan (fun i => CommAlgCat.of k (A i)) :=
  Fan.mk (CommAlgCat.of k (∀ i, A i)) fun i => CommAlgCat.ofHom (Pi.evalAlgHom k A i)

/-- 51wmmpHand0-19812 (5:30:12) [prop] The sum of the affine spaces `X_i = V_{A_i}` is the affine
space with ring `∏ A_i`, the canonical injections corresponding to the projections: `∏ A_i` is the
product in `CommAlgCat k`, i.e. the sum in `𝒞` (finiteness is not needed here). -/
def prop_19812 : IsLimit (piFan k A) :=
  Fan.IsLimit.mk _ (fun s => CommAlgCat.ofHom (AlgHom.pi fun i => (s.proj i).hom))
    (fun _ _ => rfl) fun s m hm => by
      apply CommAlgCat.hom_ext
      ext x
      funext i
      exact congrArg (fun f => f.hom x) (hm i)

/-- 51wmmpHand0-19886 (5:31:26) [prop] The projections `∏ A_j → A_i` are surjective, so
`X_i → ∐ X_j` is a closed immersion, injective on points with values in every `K'`. -/
theorem prop_19886 [DecidableEq ι] (i : ι) :
    Function.Surjective (Pi.evalAlgHom k A i) ∧
      ∀ (k' : Type*) [CommRing k'] [Algebra k k'],
        Function.Injective (fun φ : A i →ₐ[k] k' => φ.comp (Pi.evalAlgHom k A i)) := by
  have hs : Function.Surjective (Pi.evalAlgHom k A i) :=
    fun a => ⟨Pi.single i a, Pi.single_eq_same i a⟩
  refine ⟨hs, fun k' _ _ φ ψ h => AlgHom.ext fun a => ?_⟩
  obtain ⟨b, rfl⟩ := hs a
  exact DFunLike.congr_fun h b

end Sums

/-- 51wmmpHand0-20208 (5:36:48) [def] An object `X` of a category is connected if, for every
decomposition `X = X' ⊔ X''` as a sum, `X'` or `X''` is initial. -/
def IsConnectedObj {C : Type*} [Category C] (X : C) : Prop :=
  ∀ (X' X'' : C) (i' : X' ⟶ X) (i'' : X'' ⟶ X), Nonempty (IsColimit (BinaryCofan.mk i' i'')) →
    Nonempty (IsInitial X') ∨ Nonempty (IsInitial X'')

/-- A topological space is initial in `TopCat` if and only if it is empty. -/
theorem TopCat.nonempty_isInitial_iff (Y : TopCat.{u}) : Nonempty (IsInitial Y) ↔ IsEmpty Y := by
  constructor
  · rintro ⟨h⟩
    exact ⟨fun y => ((h.to (TopCat.of PEmpty.{u + 1})) y).elim⟩
  · intro _
    exact ⟨IsInitial.ofUniqueHom (fun Z => TopCat.ofHom ⟨isEmptyElim, ⟨fun s _ => by
        rw [Set.eq_empty_of_isEmpty (isEmptyElim ⁻¹' s : Set Y)]; exact isOpen_empty⟩⟩)
      fun _ _ => TopCat.hom_ext (ContinuousMap.ext fun y => isEmptyElim y)⟩

/-- 51wmmpHand0-20208 (5:36:48) [def] In topological spaces one recovers connectedness: `X` is a
connected object of `TopCat` if and only if it is preconnected (the empty space is connected in
the categorical sense, as in mathlib's `PreconnectedSpace`). -/
theorem def_20208_top (X : Type u) [TopologicalSpace X] :
    IsConnectedObj (TopCat.of X) ↔ PreconnectedSpace X := by
  rw [preconnectedSpace_iff_clopen]
  constructor
  · intro h s hs
    let i' : TopCat.of s ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let i'' : TopCat.of (sᶜ : Set X) ⟶ TopCat.of X :=
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    have hc : Nonempty (IsColimit (BinaryCofan.mk i' i'')) := by
      rw [TopCat.binaryCofan_isColimit_iff]
      refine ⟨hs.isOpen.isOpenEmbedding_subtypeVal, hs.compl.isOpen.isOpenEmbedding_subtypeVal, ?_⟩
      change IsCompl (Set.range (Subtype.val : s → X)) (Set.range (Subtype.val : (sᶜ : Set X) → X))
      rw [Subtype.range_coe, Subtype.range_coe]
      exact isCompl_compl
    rcases h _ _ i' i'' hc with h1 | h1
    · rw [TopCat.nonempty_isInitial_iff] at h1
      exact Or.inl (Set.isEmpty_coe_sort.1 h1)
    · rw [TopCat.nonempty_isInitial_iff] at h1
      exact Or.inr (Set.compl_empty_iff.1 (Set.isEmpty_coe_sort.1 h1))
  · intro h X' X'' i' i'' hc
    rw [TopCat.binaryCofan_isColimit_iff] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    simp only [BinaryCofan.mk_inl, BinaryCofan.mk_inr] at h1 h2 h3
    have hcl : IsClopen (Set.range i') := by
      refine ⟨?_, h1.isOpen_range⟩
      rw [← isOpen_compl_iff, h3.compl_eq]
      exact h2.isOpen_range
    rcases h _ hcl with he | he
    · left
      rw [TopCat.nonempty_isInitial_iff]
      exact ⟨fun x => (Set.eq_empty_iff_forall_notMem.1 he) _ ⟨x, rfl⟩⟩
    · right
      rw [TopCat.nonempty_isInitial_iff]
      have : Set.range i'' = ∅ := by rw [← h3.compl_eq, he, Set.compl_univ]
      exact ⟨fun x => (Set.eq_empty_iff_forall_notMem.1 this) _ ⟨x, rfl⟩⟩

/-- 51wmmpHand0-20350 (5:39:10) [prop] `Hom(0, K')` is nonempty if and only if `K' = 0`, and has
at most one element; the affine space of the zero algebra, "empty", is the initial object of
`𝒞`. -/
theorem prop_20350 (k' : Type*) [CommRing k'] [Algebra k k'] :
    (Nonempty (PUnit.{u + 1} →ₐ[k] k') ↔ Subsingleton k') ∧
      Subsingleton (PUnit.{u + 1} →ₐ[k] k') ∧
      Nonempty (IsInitial (Opposite.op (CommAlgCat.of k PUnit.{u + 1}))) := by
  refine ⟨⟨fun ⟨φ⟩ => subsingleton_of_zero_eq_one (by rw [← map_zero φ, ← map_one φ]),
    fun _ => ⟨toSubsingleton k _ _⟩⟩, ⟨fun φ ψ => AlgHom.ext fun x => by
      rw [show x = 1 from Subsingleton.elim _ _, map_one, map_one]⟩,
    (nonempty_isInitial_iff k _).2 inferInstance⟩

/-- 51wmmpHand0-20474 (5:41:14) [prop] A decomposition of an affine space as a sum of two affine
spaces is a decomposition of its ring as a product: `A' × A''`, with its projections, is the
product of `A'` and `A''` in `CommAlgCat k` (the sum in `𝒞`). -/
def prop_20474 (A' A'' : Type u) [CommRing A'] [Algebra k A'] [CommRing A''] [Algebra k A''] :
    IsLimit (BinaryFan.mk (P := CommAlgCat.of k (A' × A''))
      (CommAlgCat.ofHom (AlgHom.fst k A' A'')) (CommAlgCat.ofHom (AlgHom.snd k A' A''))) :=
  BinaryFan.IsLimit.mk _ (fun f g => CommAlgCat.ofHom (f.hom.prod g.hom)) (fun _ _ => rfl)
    (fun _ _ => rfl) fun f g m h1 h2 => by
      apply CommAlgCat.hom_ext
      ext x
      exact Prod.ext (congrArg (fun φ => φ.hom x) h1) (congrArg (fun φ => φ.hom x) h2)

/-- For an idempotent `e`, `A → A/(1-e) × A/(e)` is bijective. -/
theorem bijective_prod_of_idempotent {A : Type*} [CommRing A] [Algebra k A] {e : A}
    (he : IsIdempotentElem e) :
    Function.Bijective ((Ideal.Quotient.mkₐ k (Ideal.span {1 - e})).prod
      (Ideal.Quotient.mkₐ k (Ideal.span {e}))) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    simp only [AlgHom.prod_apply, Prod.mk_eq_zero, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hx
    have h1 : e * x = 0 := by
      rw [← ha, mul_comm a, ← mul_assoc, mul_sub, mul_one, he.eq, sub_self, zero_mul]
    have h2 : e * x = x := by rw [← hb, mul_comm b, ← mul_assoc, he.eq]
    rw [← h2, h1]
  · rintro ⟨y, z⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨a * e + b * (1 - e), ?_⟩
    simp only [AlgHom.prod_apply, Ideal.Quotient.mkₐ_eq_mk, Prod.mk.injEq]
    constructor
    · rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      exact ⟨b - a, by ring⟩
    · rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      exact ⟨a - b, by ring⟩

/-- 51wmmpHand0-20539 (5:42:19) [prop] A decomposition `A = A' × A''` amounts to orthogonal
idempotents `e', e''` with sum `1`: in `A' × A''` these are `(1,0)` and `(0,1)`, and conversely an
idempotent `e` (with `e'' = 1 - e`) gives `A ≃ A/(1 - e) × A/(e)`. -/
theorem prop_20539 {A' A'' : Type*} [CommRing A'] [CommRing A''] {A : Type*} [CommRing A]
    [Algebra k A] {e : A} (he : IsIdempotentElem e) :
    (IsIdempotentElem ((1, 0) : A' × A'') ∧ IsIdempotentElem ((0, 1) : A' × A'') ∧
      ((1, 0) : A' × A'') * (0, 1) = 0 ∧ ((1, 0) : A' × A'') + (0, 1) = 1) ∧
      Function.Bijective ((Ideal.Quotient.mkₐ k (Ideal.span {1 - e})).prod
        (Ideal.Quotient.mkₐ k (Ideal.span {e}))) :=
  ⟨⟨by simp [IsIdempotentElem], by simp [IsIdempotentElem], by simp, by simp⟩,
    bijective_prod_of_idempotent k he⟩

/-- 51wmmpHand0-20656 (5:44:16) [prop] A decomposition of `A` as a product of `n` rings amounts to
`n` pairwise orthogonal idempotents with sum `1`: `A ≃ ∏ A/(1 - e_i)` (mathlib:
`CompleteOrthogonalIdempotents.bijective_pi`), and the `Pi.single i 1` of a product form such a
family (`CompleteOrthogonalIdempotents.single`). -/
theorem prop_20656 {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A] {e : ι → A}
    (he : CompleteOrthogonalIdempotents e) (B : ι → Type*) [∀ i, CommRing (B i)] :
    Function.Bijective (RingHom.pi fun i => Ideal.Quotient.mk (Ideal.span {1 - e i})) ∧
      CompleteOrthogonalIdempotents (fun i => (Pi.single i 1 : ∀ j, B j)) :=
  ⟨he.bijective_pi, CompleteOrthogonalIdempotents.single B⟩

/-- 51wmmpHand0-20722 (5:45:22) [prop] If `e` is idempotent, so is `1 - e`, and `e(1 - e) = 0`;
a pair of orthogonal idempotents with sum `1` is the same as one idempotent. -/
theorem prop_20722 {A : Type*} [CommRing A] (e : A) :
    (IsIdempotentElem e → IsIdempotentElem (1 - e) ∧ e * (1 - e) = 0) ∧
      ((∃ e'', IsIdempotentElem e ∧ IsIdempotentElem e'' ∧ e * e'' = 0 ∧ e + e'' = 1) ↔
        IsIdempotentElem e) := by
  have h : IsIdempotentElem e → IsIdempotentElem (1 - e) ∧ e * (1 - e) = 0 := fun he =>
    ⟨he.one_sub, by rw [mul_sub, mul_one, he.eq, sub_self]⟩
  refine ⟨h, ⟨fun ⟨_, he, _⟩ => he, fun he => ⟨1 - e, he, (h he).1, (h he).2, by ring⟩⟩⟩

/-- 51wmmpHand0-20786 (5:46:26) [prop] A ring `A` is connected (its affine space is a connected
object of `𝒞`) if and only if its only idempotents are `0` and `1`. -/
theorem prop_20786 (A : Type u) [CommRing A] [Algebra k A] :
    IsConnectedObj (Opposite.op (CommAlgCat.of k A)) ↔
      ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  constructor
  · intro h e he
    let B := CommAlgCat.of k (A ⧸ Ideal.span {1 - e})
    let C := CommAlgCat.of k (A ⧸ Ideal.span {e})
    let p : A →ₐ[k] B := Ideal.Quotient.mkₐ k _
    let q : A →ₐ[k] C := Ideal.Quotient.mkₐ k _
    let Φ := AlgEquiv.ofBijective (p.prod q) (bijective_prod_of_idempotent k he)
    have hΦ : ∀ y, p.prod q (Φ.symm y) = y := fun y => Φ.apply_symm_apply y
    let i' : Opposite.op B ⟶ Opposite.op (CommAlgCat.of k A) := (hm k p).op
    let i'' : Opposite.op C ⟶ Opposite.op (CommAlgCat.of k A) := (hm k q).op
    have hc : IsColimit (BinaryCofan.mk i' i'') := by
      refine BinaryCofan.IsColimit.mk _
        (fun {T} f g => (hm k (A := T.unop) (B := CommAlgCat.of k A)
          (Φ.symm.toAlgHom.comp (f.unop.hom.prod g.unop.hom))).op) ?_ ?_ ?_
      · intro T f g
        apply Quiver.Hom.unop_inj
        apply CommAlgCat.hom_ext
        ext x
        exact congrArg Prod.fst (hΦ (f.unop.hom x, g.unop.hom x))
      · intro T f g
        apply Quiver.Hom.unop_inj
        apply CommAlgCat.hom_ext
        ext x
        exact congrArg Prod.snd (hΦ (f.unop.hom x, g.unop.hom x))
      · intro T f g m h1 h2
        apply Quiver.Hom.unop_inj
        apply CommAlgCat.hom_ext
        ext x
        change m.unop.hom x = Φ.symm (f.unop.hom x, g.unop.hom x)
        rw [Φ.eq_symm_apply]
        change (p (m.unop.hom x), q (m.unop.hom x)) = _
        rw [← h1, ← h2]
        rfl
    rcases h _ _ i' i'' ⟨hc⟩ with h1 | h1
    · obtain ⟨h1⟩ := h1
      have := subsingleton_of_isInitial k h1
      have h0 : (Ideal.Quotient.mk (Ideal.span {1 - e}) 1 : A ⧸ _) = 0 := Subsingleton.elim _ _
      left
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
      obtain ⟨c, hc⟩ := h0
      have : e = e * (1 - e) * c := by rw [mul_assoc, ← hc, mul_one]
      rw [this, mul_sub, mul_one, he.eq, sub_self, zero_mul]
    · obtain ⟨h1⟩ := h1
      have := subsingleton_of_isInitial k h1
      have h0 : (Ideal.Quotient.mk (Ideal.span {e}) 1 : A ⧸ _) = 0 := Subsingleton.elim _ _
      right
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
      obtain ⟨c, hc⟩ := h0
      have : 1 - e = (1 - e) * e * c := by rw [mul_assoc, ← hc, mul_one]
      rw [sub_mul, one_mul, he.eq, sub_self, zero_mul, sub_eq_zero] at this
      exact this.symm
  · intro h X' X'' i' i'' hc
    obtain ⟨hc⟩ := hc
    let B := X'.unop
    let C := X''.unop
    let f : A →ₐ[k] B := i'.unop.hom
    let g : A →ₐ[k] C := i''.unop.hom
    let P := CommAlgCat.of k (B × C)
    let p1 : X' ⟶ Opposite.op P := (hm k (A := P) (B := B) (AlgHom.fst k B C)).op
    let p2 : X'' ⟶ Opposite.op P := (hm k (A := P) (B := C) (AlgHom.snd k B C)).op
    obtain ⟨d, hd1, hd2⟩ := BinaryCofan.IsColimit.desc' hc p1 p2
    let hh : B × C →ₐ[k] A := d.unop.hom
    have e1 : ∀ y, f (hh y) = y.1 := fun y =>
      congrArg (fun φ => φ.unop.hom y) hd1
    have e2 : ∀ y, g (hh y) = y.2 := fun y =>
      congrArg (fun φ => φ.unop.hom y) hd2
    have hid : IsIdempotentElem (hh (1, 0)) := by
      rw [IsIdempotentElem, ← map_mul]; simp
    rcases h _ hid with h0 | h0
    · left
      have := e1 (1, 0)
      rw [h0, map_zero] at this
      exact (nonempty_isInitial_iff k B).2 (subsingleton_of_zero_eq_one this)
    · right
      have := e2 (1, 0)
      rw [h0, map_one] at this
      exact (nonempty_isInitial_iff k C).2 (subsingleton_of_zero_eq_one this.symm)

/-- 51wmmpHand0-20850 (5:47:30) [def] An object is `0`-connected if it is connected and not
initial. -/
def IsZeroConnected {C : Type*} [Category C] (X : C) : Prop :=
  IsConnectedObj X ∧ IsEmpty (IsInitial X)

/-- 51wmmpHand0-20850 (5:47:30) [def] A ring is `0`-connected (its affine space is) if and only if
it is connected and nonzero. -/
theorem def_20850 (A : Type u) [CommRing A] [Algebra k A] :
    IsZeroConnected (Opposite.op (CommAlgCat.of k A)) ↔
      (∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) ∧ Nontrivial A := by
  rw [IsZeroConnected, prop_20786, ← not_nonempty_iff, nonempty_isInitial_iff,
    not_subsingleton_iff_nontrivial]

/-- 51wmmpHand0-21041 (5:50:41) [prop] A morphism `Z = V_C → ∐ X_i` (finite sum, `X_i = V_{A_i}`),
i.e. a homomorphism `∏ A_i → C`, decomposes `Z`: the images of the unit idempotents of `∏ A_i`
form a complete family of orthogonal idempotents of `C`. -/
theorem prop_21041 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra k (A i)] {C : Type*} [CommRing C] [Algebra k C]
    (φ : (∀ i, A i) →ₐ[k] C) :
    CompleteOrthogonalIdempotents (fun i => φ (Pi.single i 1)) :=
  (CompleteOrthogonalIdempotents.single A).map φ.toRingHom

/-- 51wmmpHand0-21173 (5:52:53) [prop] If `K'` is `0`-connected, the map
`∐ X_i(K') → X(K')`, `X = ∐ X_i` (finite sum), is bijective. -/
theorem prop_21173 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra k (A i)] (k' : Type*) [CommRing k'] [Algebra k k']
    [Nontrivial k'] (hk' : ∀ e : k', IsIdempotentElem e → e = 0 ∨ e = 1) :
    Function.Bijective (fun x : (Σ i, A i →ₐ[k] k') => x.2.comp (Pi.evalAlgHom k A x.1)) := by
  constructor
  · rintro ⟨i, ψ⟩ ⟨j, ψ'⟩ h
    have hij : i = j := by
      by_contra hij
      have := DFunLike.congr_fun h (Pi.single i 1)
      simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply, Pi.single_eq_same, map_one,
        Pi.single_eq_of_ne' hij, map_zero] at this
      exact one_ne_zero this
    subst hij
    have hs : Function.Surjective (Pi.evalAlgHom k A i) :=
      fun a => ⟨Pi.single i a, Pi.single_eq_same i a⟩
    have : ψ = ψ' := AlgHom.ext fun a => by
      obtain ⟨b, rfl⟩ := hs a
      exact DFunLike.congr_fun h b
    rw [this]
  · intro φ
    have hc := prop_21041 k A φ
    have h01 : ∀ i, φ (Pi.single i 1) = 0 ∨ φ (Pi.single i 1) = 1 := fun i => hk' _ (hc.idem i)
    have hex : ∃ i, φ (Pi.single i 1) = 1 := by
      by_contra hne
      simp only [not_exists] at hne
      have := hc.complete
      rw [Finset.sum_eq_zero fun i _ => (h01 i).resolve_right (hne i)] at this
      exact zero_ne_one this
    obtain ⟨i, hi⟩ := hex
    let ψ : A i →ₐ[k] k' :=
      { toFun := fun a => φ (Pi.single i a)
        map_one' := hi
        map_mul' := fun a b => by rw [← map_mul, Pi.single_mul]
        map_zero' := by rw [Pi.single_zero, map_zero]
        map_add' := fun a b => by rw [Pi.single_add, map_add]
        commutes' := fun c => by
          have : Pi.single i (algebraMap k (A i) c) = algebraMap k (∀ j, A j) c * Pi.single i 1 := by
            ext j
            by_cases hj : j = i
            · subst hj; simp
            · simp [Pi.single_eq_of_ne hj]
          change φ (Pi.single i (algebraMap k (A i) c)) = _
          rw [this, map_mul, AlgHom.commutes, hi, mul_one] }
    refine ⟨⟨i, ψ⟩, AlgHom.ext fun a => ?_⟩
    change φ (Pi.single i (a i)) = φ a
    have : Pi.single i (a i) = a * Pi.single i 1 := by
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]
    rw [this, map_mul, hi, mul_one]

/-- 51wmmpHand0-21173 (5:52:53) [prop] An integral domain is `0`-connected. -/
theorem prop_21173_domain (A : Type*) [CommRing A] [IsDomain A] :
    (∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) ∧ Nontrivial A :=
  ⟨fun _ he => IsIdempotentElem.iff_eq_zero_or_one.1 he, inferInstance⟩

/-- 51wmmpHand0-21237 (5:53:57) [prop] A local ring is `0`-connected. -/
theorem prop_21237 (A : Type*) [CommRing A] [IsLocalRing A] :
    (∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) ∧ Nontrivial A := by
  have key : ∀ x : A, IsIdempotentElem x → IsUnit x → x = 1 := fun x hx ⟨u, hu⟩ => by
    subst hu
    calc (u : A) = u * u * ↑u⁻¹ := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = u * ↑u⁻¹ := by rw [hx.eq]
      _ = 1 := Units.mul_inv u
  refine ⟨fun e he => ?_, inferInstance⟩
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · exact Or.inr (key e he h)
  · have := key _ he.one_sub h
    left
    linear_combination -this

/-- 51wmmpHand0-21237 (5:53:57) [rem] An affine space is connected (resp. empty) if and only if
the topological space `Spec A` is (mathlib: `PrimeSpectrum.isIdempotentElemEquivClopens`,
`PrimeSpectrum.isEmpty_iff_subsingleton`). -/
theorem rem_21237 (A : Type*) [CommRing A] :
    ((∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) ↔ PreconnectedSpace (PrimeSpectrum A)) ∧
      (IsEmpty (PrimeSpectrum A) ↔ Subsingleton A) := by
  refine ⟨?_, PrimeSpectrum.isEmpty_iff_subsingleton⟩
  let Φ := PrimeSpectrum.isIdempotentElemEquivClopens (R := A)
  rw [preconnectedSpace_iff_clopen]
  constructor
  · intro h s hs
    rcases h _ (Φ.symm ⟨s, hs⟩).2 with h0 | h0
    · left
      have : Φ.symm ⟨s, hs⟩ = Φ.symm ⊥ := by
        rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot]; exact Subtype.ext h0
      have := congrArg (fun c : TopologicalSpace.Clopens _ => (c : Set (PrimeSpectrum A)))
        (Φ.symm.injective this)
      exact this
    · right
      have : Φ.symm ⟨s, hs⟩ = Φ.symm ⊤ := by
        rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_top]; exact Subtype.ext h0
      have := congrArg (fun c : TopologicalSpace.Clopens _ => (c : Set (PrimeSpectrum A)))
        (Φ.symm.injective this)
      exact this
  · intro h e he
    rcases h _ (Φ ⟨e, he⟩).isClopen with h0 | h0
    · left
      have : Φ ⟨e, he⟩ = ⊥ := TopologicalSpace.Clopens.ext h0
      have := congrArg Subtype.val ((Φ.symm_apply_eq.2 this.symm).symm.trans
        PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot)
      exact this
    · right
      have : Φ ⟨e, he⟩ = ⊤ := TopologicalSpace.Clopens.ext h0
      have := congrArg Subtype.val ((Φ.symm_apply_eq.2 this.symm).symm.trans
        PrimeSpectrum.isIdempotentElemEquivClopens_symm_top)
      exact this

/-- 51wmmpHand0-21337 (5:55:37) [cex] For `K' = 0` the hypothesis "nonzero" is necessary: `X(0)`
is a singleton while `∐ X_i(0)` has one point for each `i`, so the map of `prop_21173` is not
injective as soon as there are two indices. -/
theorem cex_21337 {ι : Type*} [Fintype ι] (A : ι → Type*) [∀ i, CommRing (A i)]
    [∀ i, Algebra k (A i)] {i j : ι} (hij : i ≠ j) :
    ¬ Function.Injective (fun x : (Σ i, A i →ₐ[k] PUnit.{u + 1}) =>
      x.2.comp (Pi.evalAlgHom k A x.1)) := fun h => by
  have := @h ⟨i, toSubsingleton k _ _⟩ ⟨j, toSubsingleton k _ _⟩
    (AlgHom.ext fun _ => Subsingleton.elim _ _)
  exact hij (congrArg Sigma.fst this)

/-! ### Points with values in fields and the spectrum -/

/-- 51wmmpHand0-21723 (6:02:03) [def] Points `u' ∈ X(K')`, `u'' ∈ X(K'')` with values in fields
are equivalent if they have the same image in `X(K''')` for some `K', K'' → K'''` into a field
(stated for rings, `K = ℤ`). -/
def PtEquiv {A K' K'' : Type u} [CommRing A] [Field K'] [Field K''] (u' : A →+* K')
    (u'' : A →+* K'') : Prop :=
  ∃ (L : Type u) (_ : Field L) (f : K' →+* L) (g : K'' →+* L), f.comp u' = g.comp u''

/-- The kernel of a ring homomorphism into a field, after a field homomorphism. -/
theorem ker_comp_field {A K' L : Type*} [CommRing A] [Field K'] [Field L] (u : A →+* K')
    (f : K' →+* L) : RingHom.ker (f.comp u) = RingHom.ker u := by
  ext a
  simp only [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff f f.injective]

/-- 51wmmpHand0-21859 (6:04:19) [prop] Two homomorphisms `u' : A → K'`, `u'' : A → K''` into
fields are equivalent if and only if `ker u' = ker u''` (hence an equivalence relation). -/
theorem prop_21859 {A K' K'' : Type u} [CommRing A] [Field K'] [Field K''] (u' : A →+* K')
    (u'' : A →+* K'') : PtEquiv u' u'' ↔ RingHom.ker u' = RingHom.ker u'' := by
  constructor
  · rintro ⟨L, _, f, g, h⟩
    rw [← ker_comp_field u' f, ← ker_comp_field u'' g, h]
  · intro h
    let P := RingHom.ker u'
    let R := A ⧸ P
    let a' : R →+* K' := Ideal.Quotient.lift P u' fun _ ha => ha
    let a'' : R →+* K'' := Ideal.Quotient.lift P u'' fun _ ha => by
      change _ ∈ RingHom.ker u''; rw [← h]; exact ha
    let _ : Algebra R K' := a'.toAlgebra
    let _ : Algebra R K'' := a''.toAlgebra
    have ha' : Function.Injective (algebraMap R K') := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact Ideal.Quotient.eq_zero_iff_mem.2 hx
    have ha'' : Function.Injective (algebraMap R K'') := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      change a ∈ RingHom.ker u'
      rw [h]
      exact hx
    have := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain R K' K''
      ha' ha''
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct R K' K'')
    let _ := Ideal.Quotient.field M
    refine ⟨_, inferInstance,
      (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeLeft (S := R)).toRingHom,
      (Ideal.Quotient.mk M).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
    ext a
    have e' : u' a = algebraMap R K' (Ideal.Quotient.mk P a) := rfl
    have e'' : u'' a = algebraMap R K'' (Ideal.Quotient.mk P a) := rfl
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [e', e'', AlgHom.commutes, AlgHom.commutes]

/-- 51wmmpHand0-21989 (6:06:29) [prop] The kernel of a homomorphism from `A` into a field is a
prime ideal `P`, and the homomorphisms `A → K'` with kernel `P` correspond to the homomorphisms
`κ(P) = Frac(A/P) → K'`. -/
theorem prop_21989 {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime] (K' : Type*) [Field K'] :
    (∀ u : A →+* K', (RingHom.ker u).IsPrime) ∧
      Nonempty ({u : A →+* K' // RingHom.ker u = P} ≃ (FractionRing (A ⧸ P) →+* K')) := by
  refine ⟨fun u => RingHom.ker_isPrime u, ⟨?_⟩⟩
  let κ := FractionRing (A ⧸ P)
  let j : A →+* κ := (algebraMap (A ⧸ P) κ).comp (Ideal.Quotient.mk P)
  have hj : RingHom.ker j = P := by
    ext a
    simp only [j, RingHom.mem_ker, RingHom.comp_apply,
      IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hinj : ∀ u : {u : A →+* K' // RingHom.ker u = P},
      Function.Injective (Ideal.Quotient.lift P u.1 fun a ha => by rw [← u.2] at ha; exact ha) :=
    fun u => by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      change (u.1 : A →+* K') a = 0 at hx
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      rw [← u.2]; exact hx
  exact
    { toFun := fun u => IsFractionRing.lift (hinj u)
      invFun := fun φ => ⟨φ.comp j, by rw [ker_comp_field, hj]⟩
      left_inv := fun u => Subtype.ext (RingHom.ext fun a => by
        simp only [j, RingHom.comp_apply]
        rw [IsFractionRing.lift_algebraMap]
        rfl)
      right_inv := fun φ => by
        apply IsLocalization.ringHom_ext (nonZeroDivisors (A ⧸ P))
        apply Ideal.Quotient.ringHom_ext
        ext a
        simp only [j, RingHom.comp_apply]
        rw [IsFractionRing.lift_algebraMap]
        rfl }

/-- 51wmmpHand0-22052 (6:07:32) [prop] Two extensions `K'`, `K''` of a field `κ` have a common
extension: `K' ⊗_κ K''` is nonzero, hence has a quotient that is a field. -/
theorem prop_22052 (κ K' K'' : Type u) [Field κ] [Field K'] [Field K''] [Algebra κ K']
    [Algebra κ K''] :
    Nontrivial (TensorProduct κ K' K'') ∧ ∃ (L : Type u) (_ : Field L) (_ : Algebra κ L),
      Nonempty (K' →ₐ[κ] L) ∧ Nonempty (K'' →ₐ[κ] L) := by
  have := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain κ K' K''
    (algebraMap κ K').injective (algebraMap κ K'').injective
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct κ K' K'')
  let _ := Ideal.Quotient.field M
  exact ⟨inferInstance, _, inferInstance, inferInstance,
    ⟨(Ideal.Quotient.mkₐ κ M).comp Algebra.TensorProduct.includeLeft⟩,
    ⟨(Ideal.Quotient.mkₐ κ M).comp Algebra.TensorProduct.includeRight⟩⟩

/-- 51wmmpHand0-22123 (6:08:43) [prop] The classes of points with values in fields are identified
with `Spec A`: `u ↦ ker u` takes every prime as value (`A → κ(P)`), and two points have the same
kernel exactly when they are equivalent (`prop_21859`). -/
theorem prop_22123 (A : Type u) [CommRing A] :
    (∀ P : PrimeSpectrum A, ∃ (K : Type u) (_ : Field K) (u : A →+* K),
      RingHom.ker u = P.asIdeal) ∧
    ∀ {K' K'' : Type u} [Field K'] [Field K''] (u' : A →+* K') (u'' : A →+* K''),
      PtEquiv u' u'' ↔ RingHom.ker u' = RingHom.ker u'' := by
  refine ⟨fun P => ?_, fun u' u'' => prop_21859 u' u''⟩
  refine ⟨FractionRing (A ⧸ P.asIdeal), inferInstance,
    (algebraMap (A ⧸ P.asIdeal) _).comp (Ideal.Quotient.mk P.asIdeal), ?_⟩
  ext a
  simp only [RingHom.mem_ker, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]

/-! ### The Zariski topology on the spectrum -/

open PrimeSpectrum

/-- 51wmmpHand0-22510 (6:15:10) [prop] `V(S) = V(J_S) = V(√J_S)` (mathlib:
`PrimeSpectrum.zeroLocus_span`, `PrimeSpectrum.zeroLocus_radical`). -/
theorem prop_22510 {A : Type*} [CommRing A] (S : Set A) :
    zeroLocus S = zeroLocus (Ideal.span S : Set A) ∧
      zeroLocus S = zeroLocus ((Ideal.span S).radical : Set A) := by
  rw [zeroLocus_radical, zeroLocus_span]
  exact ⟨rfl, rfl⟩

/-- 51wmmpHand0-22575 (6:16:15) [prop] The radical of an ideal is the intersection of the primes
containing it (mathlib: `Ideal.radical_eq_sInf`), so `J ↦ V(J)` is injective on radical ideals. -/
theorem prop_22575 {A : Type*} [CommRing A] (J : Ideal A) :
    J.radical = sInf {P | J ≤ P ∧ P.IsPrime} ∧
      ∀ J' : Ideal A, J.IsRadical → J'.IsRadical →
        zeroLocus (J : Set A) = zeroLocus J' → J = J' := by
  refine ⟨Ideal.radical_eq_sInf J, fun J' hJ hJ' h => ?_⟩
  rw [← hJ.radical, ← hJ'.radical, ← vanishingIdeal_zeroLocus_eq_radical,
    ← vanishingIdeal_zeroLocus_eq_radical, h]

/-- 51wmmpHand0-22644 (6:17:24) [prop] For radical `J`, `J'`, `V(J) ⊆ V(J')` iff `J ⊇ J'`. -/
theorem prop_22644 {A : Type*} [CommRing A] (J J' : Ideal A) (hJ : J.IsRadical) :
    zeroLocus (J : Set A) ⊆ zeroLocus J' ↔ J' ≤ J := by
  rw [zeroLocus_subset_zeroLocus_iff, hJ.radical]

/-- 51wmmpHand0-22774 (6:19:34) [prop] `⋂ V(J_i) = V(∑ J_i)` (mathlib:
`PrimeSpectrum.zeroLocus_iSup`). -/
theorem prop_22774 {A ι : Type*} [CommRing A] (J : ι → Ideal A) :
    zeroLocus ((⨆ i, J i : Ideal A) : Set A) = ⋂ i, zeroLocus (J i : Set A) :=
  zeroLocus_iSup J

/-- 51wmmpHand0-22837 (6:20:37) [prop] For a finite family of ideals,
`⋃ V(J_i) = V(⋂ J_i) = V(∏ J_i)`. -/
theorem prop_22837 {A ι : Type*} [CommRing A] (s : Finset ι) (J : ι → Ideal A) :
    zeroLocus ((s.inf J : Ideal A) : Set A) = ⋃ i ∈ s, zeroLocus (J i : Set A) ∧
      zeroLocus ((s.prod J : Ideal A) : Set A) = ⋃ i ∈ s, zeroLocus (J i : Set A) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.inf_insert, Finset.prod_insert hi, zeroLocus_inf, zeroLocus_mul, ih.1, ih.2,
      Finset.set_biUnion_insert]
    exact ⟨rfl, rfl⟩

/-- 51wmmpHand0-23031 (6:23:51) [prop] The `V(J)` are the closed sets of a topology on `Spec A`,
in bijection with the radical ideals (`Z ↦ I(Z)`, `J ↦ V(J)`). -/
theorem prop_23031 {A : Type*} [CommRing A] :
    (∀ Z : Set (PrimeSpectrum A), IsClosed Z ↔ ∃ J : Ideal A, Z = zeroLocus J) ∧
      (∀ Z : Set (PrimeSpectrum A), IsClosed Z → zeroLocus (vanishingIdeal Z : Set A) = Z) ∧
      (∀ J : Ideal A, J.IsRadical → vanishingIdeal (zeroLocus (J : Set A)) = J) :=
  ⟨isClosed_iff_zeroLocus_ideal, fun Z hZ => by
    rw [zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq], fun J hJ => by
    rw [vanishingIdeal_zeroLocus_eq_radical, hJ.radical]⟩

/-- 51wmmpHand0-23031 (6:23:51) [prop] `Spec A` is quasi-compact (mathlib:
`PrimeSpectrum.compactSpace`). -/
theorem prop_23031_compact (A : Type*) [CommRing A] : CompactSpace (PrimeSpectrum A) :=
  PrimeSpectrum.compactSpace

/-- 51wmmpHand0-23167 (6:26:07) [prop] `V(J) = ∅` iff `J = A` (mathlib:
`PrimeSpectrum.zeroLocus_empty_iff_eq_top`). -/
theorem prop_23167 {A : Type*} [CommRing A] (J : Ideal A) :
    zeroLocus (J : Set A) = ∅ ↔ J = ⊤ :=
  zeroLocus_empty_iff_eq_top

/-- 51wmmpHand0-23294 (6:28:14) [prop] The closure of the point `x` is `V(P_x)`; `y` lies in the
closure of `x` iff `P_y ⊇ P_x` (mathlib: `PrimeSpectrum.closure_singleton`,
`PrimeSpectrum.le_iff_mem_closure`). -/
theorem prop_23294 {A : Type*} [CommRing A] (x y : PrimeSpectrum A) :
    closure {x} = zeroLocus (x.asIdeal : Set A) ∧ (y ∈ closure {x} ↔ x.asIdeal ≤ y.asIdeal) :=
  ⟨closure_singleton x, (le_iff_mem_closure x y).symm⟩

/-- 51wmmpHand0-23357 (6:29:17) [prop] Specialization on `Spec A` is the reverse inclusion of
primes, and `Spec A` is sober: every irreducible closed set is the closure of a unique point. -/
theorem prop_23357 {A : Type*} [CommRing A] :
    (∀ x y : PrimeSpectrum A, x ⤳ y ↔ x.asIdeal ≤ y.asIdeal) ∧
      ∀ Z : Set (PrimeSpectrum A), IsIrreducible Z → IsClosed Z → ∃! x, closure {x} = Z :=
  ⟨fun x y => (le_iff_specializes x y).symm, fun Z hZ hZc => by
    obtain ⟨x, hx⟩ := QuasiSober.sober hZ hZc
    exact ⟨x, hx, fun y hy => (IsGenericPoint.eq (S := Z) hy hx)⟩⟩

/-! ### Irreducible spaces -/

/-- 51wmmpHand0-23485 (6:31:25) [prop] A space is irreducible iff it is nonempty and not the union
of two strictly smaller closed sets; the closure of an irreducible subset is irreducible. -/
theorem prop_23485 (X : Type*) [TopologicalSpace X] :
    (IrreducibleSpace X ↔ Nonempty X ∧ ∀ Z₁ Z₂ : Set X, IsClosed Z₁ → IsClosed Z₂ →
      Z₁ ∪ Z₂ = Set.univ → Z₁ = Set.univ ∨ Z₂ = Set.univ) ∧
      ∀ s : Set X, IsIrreducible s → IsIrreducible (closure s) := by
  refine ⟨?_, fun s hs => hs.closure⟩
  rw [irreducibleSpace_def, IsIrreducible, isPreirreducible_iff_isClosed_union_isClosed,
    Set.top_eq_univ, ← Set.nonempty_iff_univ_nonempty]
  refine and_congr_right fun _ => ?_
  simp only [Set.univ_subset_iff]

/-- 51wmmpHand0-23485 (6:31:25) [prop] The closure of a point is irreducible; the image of an
irreducible space under a continuous map is irreducible (mathlib: `isIrreducible_singleton`,
`IsIrreducible.image`). -/
theorem prop_23485_image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (x : X)
    (f : X → Y) (hf : Continuous f) (s : Set X) (hs : IsIrreducible s) :
    IsIrreducible (closure {x}) ∧ IsIrreducible (f '' s) :=
  ⟨isIrreducible_singleton.closure, hs.image f hf.continuousOn⟩

/-- 51wmmpHand0-23547 (6:32:27) [prop] A Hausdorff space is irreducible iff it is a point. -/
theorem prop_23547 (X : Type*) [TopologicalSpace X] [T2Space X] :
    IrreducibleSpace X ↔ ∃ x : X, (Set.univ : Set X) = {x} := by
  rw [irreducibleSpace_def]
  constructor
  · intro h
    obtain ⟨x, -⟩ := h.nonempty
    exact ⟨x, Set.eq_singleton_iff_unique_mem.2 ⟨trivial, fun y _ =>
      h.isPreirreducible.subsingleton trivial trivial⟩⟩
  · rintro ⟨x, hx⟩
    rw [Set.top_eq_univ, hx]
    exact isIrreducible_singleton

/-- 51wmmpHand0-23611 (6:33:31) [prop] `Spec A` with its topology does not change when `A` is
replaced by `A / nil(A)`: `Spec(A/nil A) → Spec A` is a homeomorphism, every prime containing the
nilradical. -/
theorem prop_23611 (A : Type*) [CommRing A] :
    Nonempty (PrimeSpectrum (A ⧸ nilradical A) ≃ₜ PrimeSpectrum A) := by
  have hs : Function.Surjective (Ideal.Quotient.mk (nilradical A)) := Ideal.Quotient.mk_surjective
  have he := isClosedEmbedding_comap_of_surjective _ _ hs
  have hr : Function.Surjective (comap (Ideal.Quotient.mk (nilradical A))) := by
    rw [← Set.range_eq_univ, range_comap_of_surjective _ _ hs, Ideal.mk_ker,
      zeroLocus_eq_univ_iff]
  exact ⟨he.isEmbedding.toHomeomorphOfSurjective hr⟩

/-- 51wmmpHand0-23676 (6:34:36) [prop] `Spec A = ∅` iff `A = 0` (mathlib:
`PrimeSpectrum.isEmpty_iff_subsingleton`). -/
theorem prop_23676 (A : Type*) [CommRing A] : IsEmpty (PrimeSpectrum A) ↔ Subsingleton A :=
  PrimeSpectrum.isEmpty_iff_subsingleton

/-- 51wmmpHand0-23738 (6:35:38) [prop] For `A` reduced, `Spec A = V(J') ∪ V(J'')` iff `J'J'' = 0`
(the radicality of `J'`, `J''` is not needed). -/
theorem prop_23738 {A : Type*} [CommRing A] [IsReduced A] (J' J'' : Ideal A) :
    zeroLocus (J' : Set A) ∪ zeroLocus J'' = Set.univ ↔ J' * J'' = ⊥ := by
  rw [← zeroLocus_mul, zeroLocus_eq_univ_iff, nilradical_eq_zero, Submodule.zero_eq_bot,
    SetLike.coe_subset_coe, le_bot_iff]

/-- 51wmmpHand0-23801 (6:36:41) [prop] `Spec A` is irreducible iff `A / nil(A)` is an integral
domain. -/
theorem prop_23801 (A : Type*) [CommRing A] :
    IrreducibleSpace (PrimeSpectrum A) ↔ IsDomain (A ⧸ nilradical A) := by
  rw [irreducibleSpace_def, Set.top_eq_univ, isIrreducible_iff_vanishingIdeal_isPrime,
    vanishingIdeal_univ, Ideal.Quotient.isDomain_iff_prime]

end June5

end

end Buffalo.AG.Part02
