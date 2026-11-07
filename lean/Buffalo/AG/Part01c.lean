import Buffalo.AG.Part01b

/-!
# Buffalo, algebraic geometry, part 01 (c): 4 June 1973

The session of 4 June 1973 (video `51wmmpHand0`, 3:07:15–4:55:19): projective limits in the
category `𝒞` of affine spaces (products, final object, fibre products, base change, kernels of
pairs of arrows), filtered limits, finite presentation and noetherian rings, kernels and
stabilizers of affine groups, inductive limits and quotients, and the first example of
`GL_n / B`. Notation as in `Buffalo.AG.Part01a`; `𝒞` is `(CommAlgCat k)ᵒᵖ`, identified with the
representable functors by `prop_6911`.
-/

open CategoryTheory MvPolynomial

universe u

namespace Buffalo.AG.Part01

noncomputable section

section June4

variable (k : Type u) [CommRing k] {I : Type u}

/-! ### Projective limits in `𝒞` -/

/-- 51wmmpHand0-11436 (3:10:36) [prop] Projective limits of representable functors are
representable: `𝒞` has all projective limits and `coyoneda` preserves them. -/
theorem prop_11436 {J : Type u} [SmallCategory J] (F : J ⥤ (CommAlgCat.{u} k)ᵒᵖ) :
    (Limits.limit (F ⋙ coyoneda)).IsCorepresentable :=
  Functor.IsCorepresentable.mk' (X := (Limits.limit F).unop) (preservesLimitIso coyoneda F)

/-- The functor `k' ↦ Hom(A, k') × Hom(B, k')`, the product `V_A × V_B`. -/
def VProd (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] :
    CommAlgCat.{u} k ⥤ Type u where
  obj k' := (A →ₐ[k] k') × (B →ₐ[k] k')
  map {_ _} f := ↾fun p => (f.hom.comp p.1, f.hom.comp p.2)

/-- 51wmmpHand0-11633 (3:13:53) [prop] For `X = V_A` and `Y = V_B`, `X × Y` is represented by
`A ⊗_k B`. -/
def prop_11633 (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] :
    (VProd k A B).CorepresentableBy (CommAlgCat.of k (TensorProduct k A B)) where
  homEquiv {k'} :=
    { toFun := fun φ => prop_10867 k A B k' φ.hom
      invFun := fun p => CommAlgCat.ofHom ((prop_10867 k A B k').symm p)
      left_inv := fun φ => by
        apply CommAlgCat.hom_ext
        exact (prop_10867 k A B k').symm_apply_apply φ.hom
      right_inv := fun p => (prop_10867 k A B k').apply_symm_apply p }
  homEquiv_comp _ _ := rfl

/-- 51wmmpHand0-11778 (3:16:18) [prop] The final object of `𝒞` is `V_k = Spec k`: `k` is the
initial `k`-algebra, and `V_k(k')` is a point. -/
theorem prop_11778 (k' : Type*) [CommRing k'] [Algebra k k'] :
    Nonempty (Limits.IsTerminal (Opposite.op (CommAlgCat.of k k))) ∧
      Nonempty (Unique (k →ₐ[k] k')) :=
  ⟨⟨(isInitialSelf k).op⟩, ⟨⟨⟨Algebra.ofId k k'⟩, fun _ => Subsingleton.elim _ _⟩⟩⟩

/-- 51wmmpHand0-11778 (3:16:18) [prop] To have all projective limits, products and fibre products
suffice. -/
theorem prop_11778_limits {C : Type u} [Category.{u} C] [Limits.HasProducts.{u} C]
    [Limits.HasPullbacks C] : Limits.HasLimits C := by
  have : Limits.HasFiniteProducts C := Limits.hasFiniteProducts_of_hasProducts C
  have : Limits.HasEqualizers C := Limits.hasEqualizers_of_hasPullbacks_and_binary_products
  exact Limits.has_limits_of_hasEqualizers_and_products

/-- 51wmmpHand0-12039 (3:20:39) [prop] For `S = V_A`, `𝒞/S` is the opposite of the category of
`A`-algebras; here for `k = ℤ`, i.e. over the category of rings (mathlib:
`Over.opEquivOpUnder`, `commAlgCatEquivUnder`). -/
def prop_12039 (A : CommRingCat.{u}) : Over (Opposite.op A) ≌ (CommAlgCat.{u} A)ᵒᵖ :=
  (Over.opEquivOpUnder A).trans (commAlgCatEquivUnder A).symm.op

/-- 51wmmpHand0-12165 (3:22:45) [prop] The fibre product `X ×_S Y` is represented by `B ⊗_A C`:
`B ⊗_A C` is the pushout of `B ← A → C` (here in rings; mathlib:
`CommRingCat.pushoutCoconeIsColimit`). -/
def prop_12165 (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] : Limits.IsColimit (CommRingCat.pushoutCocone A B C) :=
  CommRingCat.pushoutCoconeIsColimit A B C

/-- 51wmmpHand0-12293 (3:24:53) [prop] `X × Y` is the fibre product over the final object
(mathlib: `prodIsoPullback`). -/
def prop_12293 {C : Type*} [Category C] [Limits.HasTerminal C] [Limits.HasPullbacks C] (X Y : C)
    [Limits.HasBinaryProduct X Y] :
    X ⨯ Y ≅ Limits.pullback (Limits.terminal.from X) (Limits.terminal.from Y) :=
  _root_.prodIsoPullback X Y

/-- 51wmmpHand0-12487 (3:28:07) [prop] Base change along `S' → S` is right adjoint to
composition `𝒞/S' → 𝒞/S` (mathlib: `Over.mapPullbackAdj`). -/
def prop_12487 {C : Type*} [Category C] [Limits.HasPullbacks C] {S' S : C} (f : S' ⟶ S) :
    Over.map f ⊣ Over.pullback f :=
  Over.mapPullbackAdj f

/-- 51wmmpHand0-12811 (3:33:31) [prop] `Hom_{S'}(Z', X') ≃ Hom_S(Z', X)`: `X'` is the restriction
of `X` along `𝒞/S' → 𝒞/S`. -/
def prop_12811 {C : Type*} [Category C] [Limits.HasPullbacks C] {S' S : C} (f : S' ⟶ S)
    (Z' : Over S') (X : Over S) : ((Over.map f).obj Z' ⟶ X) ≃ (Z' ⟶ (Over.pullback f).obj X) :=
  (Over.mapPullbackAdj f).homEquiv Z' X

/-- 51wmmpHand0-12939 (3:35:39) [prop] and 51wmmpHand0-13009 (3:36:49) [prop] For `X = V_B`, the
base change along `A → A'` is represented by `A' ⊗_A B`: its `A'`-points are the `A`-points of
`X` (mathlib: `AlgHom.liftEquiv`). -/
def prop_12939 (A A' B C : Type u) [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
    [Algebra A A'] [Algebra A B] [Algebra A C] [Algebra A' C] [IsScalarTower A A' C] :
    (B →ₐ[A] C) ≃ (TensorProduct A A' B →ₐ[A'] C) :=
  AlgHom.liftEquiv A A' B C

/-! ### Kernels of pairs of arrows -/

/-- 51wmmpHand0-13203 (3:40:03) [def] The kernel of a pair `u, v : X → Y`, the subfunctor
`K(Z) = {x : u(x) = v(x)}` (representable: `prop_13847`). -/
def eqKer {X Y : CommAlgCat.{u} k ⥤ Type u} (u v : X ⟶ Y) : Subfunctor X where
  obj Z := {x | u.app Z x = v.app Z x}
  map {Z Z'} f x (hx : u.app Z x = v.app Z x) := by
    change u.app Z' (X.map f x) = v.app Z' (X.map f x)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hx]

/-- 51wmmpHand0-13331 (3:42:11) [prop] The kernel of `(u, v)` is the fibre product of
`(u, v) : X → Y × Y` and the diagonal (pointwise, as limits of functors are). -/
def prop_13331 {X Y : Type*} (u v : X → Y) :
    {x // u x = v x} ≃ {p : X × Y // (u p.1, v p.1) = (p.2, p.2)} where
  toFun x := ⟨(x.1, u x.1), by rw [x.2]⟩
  invFun p := ⟨p.1.1, by
    have h := p.2
    simp only [Prod.mk.injEq] at h
    rw [h.1, h.2]⟩
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨⟨x, y⟩, h⟩ := p
    simp only [Prod.mk.injEq] at h
    simp [h.1]

open TensorProduct in
/-- 51wmmpHand0-13584 (3:46:24) [prop] The diagonal of `V_B` corresponds to the multiplication
`B ⊗_k B → B`, which is surjective with kernel generated by the `x ⊗ 1 - 1 ⊗ x` (mathlib:
`KaehlerDifferential.span_range_eq_ideal`). -/
theorem prop_13584 (B : Type u) [CommRing B] [Algebra k B] :
    Function.Surjective (Algebra.TensorProduct.lmul' k : B ⊗[k] B →ₐ[k] B) ∧
      Ideal.span (Set.range fun s : B => (1 : B) ⊗ₜ[k] s - s ⊗ₜ[k] (1 : B)) =
        RingHom.ker (Algebra.TensorProduct.lmul' k : B ⊗[k] B →ₐ[k] B) :=
  ⟨fun b => ⟨b ⊗ₜ 1, by simp⟩, KaehlerDifferential.span_range_eq_ideal k B⟩

/-- 51wmmpHand0-13847 (3:50:47) [prop] If `u, v : B → A` correspond to `X ⇉ Y`, the kernel of
`(u, v)` is represented by `A/I`, `I` generated by the `u(x) - v(x)`. -/
def prop_13847 {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (u v : B →ₐ[k] A) (k' : Type*) [CommRing k'] [Algebra k k'] :
    (A ⧸ Ideal.span (Set.range fun x => u x - v x) →ₐ[k] k') ≃
      {w : A →ₐ[k] k' // w.comp u = w.comp v} where
  toFun f := ⟨f.comp (Ideal.Quotient.mkₐ k _), AlgHom.ext fun x => by
    have h : Ideal.Quotient.mk (Ideal.span (Set.range fun x => u x - v x)) (u x - v x) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨x, rfl⟩)
    change f (Ideal.Quotient.mk _ (u x)) = f (Ideal.Quotient.mk _ (v x))
    exact sub_eq_zero.1 (by rw [← map_sub, ← map_sub, h, map_zero])⟩
  invFun w := Ideal.Quotient.liftₐ _ w.1 fun a ha => by
    have : Ideal.span (Set.range fun x => u x - v x) ≤ RingHom.ker w.1 := Ideal.span_le.2 (by
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, sub_eq_zero]
      exact DFunLike.congr_fun w.2 x)
    exact this ha
  left_inv f := Ideal.Quotient.algHom_ext _ (AlgHom.ext fun _ => rfl)
  right_inv w := Subtype.ext (AlgHom.ext fun _ => rfl)

/-! ### Filtered limits, finite presentation and noetherian rings -/

/-- 51wmmpHand0-13983 (3:53:03) [disc] `k(T)` is finitely generated as a field but not as a
`k`-algebra (by Zariski's lemma it would be finite over `k`, but `T` is transcendental). -/
theorem disc_13983 (K : Type u) [Field K] : ¬ Algebra.FiniteType K (RatFunc K) := fun _ => by
  have : Module.Finite K (RatFunc K) := finite_of_finite_type_of_isJacobsonRing K (RatFunc K)
  exact RatFunc.transcendental_X
    ((Algebra.IsIntegral.of_finite K (RatFunc K)).isIntegral RatFunc.X).isAlgebraic

/-- 51wmmpHand0-14373 (3:59:33) [prop] Filtered projective limits in `𝒞` are filtered inductive
limits of `k`-algebras, computed on the underlying sets (`prop_11182`). -/
theorem prop_14373 : Limits.PreservesFilteredColimits (forget (CommAlgCat.{u} k)) :=
  inferInstance

/-- 51wmmpHand0-14500 (4:01:40) [prop] Every `k`-algebra is the filtered union of its finitely
generated subalgebras (dually, every affine space is a filtered projective limit of affine spaces
of finite type). -/
theorem prop_14500 (A : Type u) [CommRing A] [Algebra k A] :
    DirectedOn (· ≤ ·) {S : Subalgebra k A | S.FG} ∧ ∀ a : A, ∃ S : Subalgebra k A, S.FG ∧ a ∈ S :=
  ⟨fun _ hS _ hT => ⟨_, hS.sup hT, le_sup_left, le_sup_right⟩,
    fun a => ⟨Algebra.adjoin k {a}, ⟨{a}, by simp⟩, Algebra.subset_adjoin rfl⟩⟩

/-- 51wmmpHand0-14628 (4:03:48) [prop] A `k`-algebra is finitely generated iff it is a quotient
of a polynomial ring in finitely many variables (mathlib:
`Algebra.FiniteType.iff_quotient_mvPolynomial''`). -/
theorem prop_14628 (A : Type u) [CommRing A] [Algebra k A] :
    Algebra.FiniteType k A ↔
      ∃ (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] A), Function.Surjective f :=
  Algebra.FiniteType.iff_quotient_mvPolynomial''

/-- 51wmmpHand0-14693 (4:04:53) [def] `A` is finitely presented if `A ≃ k[T_1..T_n]/J` with `J`
finitely generated (mathlib: `Algebra.FinitePresentation`). -/
example (A : Type u) [CommRing A] [Algebra k A] :
    Algebra.FinitePresentation k A ↔ ∃ (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] A),
      Function.Surjective f ∧ (RingHom.ker f.toRingHom).FG :=
  ⟨fun h => h.out, fun h => ⟨h⟩⟩

/-- 51wmmpHand0-14761 (4:06:01) [prop] If `A` is finitely presented, every presentation of `A` as
a quotient of a polynomial ring in finitely many variables has a finitely generated ideal
(mathlib: `Algebra.FinitePresentation.ker_fg_of_mvPolynomial`). -/
theorem prop_14761 (A : Type u) [CommRing A] [Algebra k A] [Algebra.FinitePresentation k A]
    {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] A) (hf : Function.Surjective f) :
    (RingHom.ker f.toRingHom).FG :=
  Algebra.FinitePresentation.ker_fg_of_mvPolynomial f hf

/-- 51wmmpHand0-14825 (4:07:05) [thm] Hilbert's basis theorem: every ideal of `K[T_1..T_n]` is
finitely generated (mathlib: `MvPolynomial.isNoetherianRing`). -/
theorem thm_14825 (K : Type u) [Field K] (n : ℕ) (J : Ideal (MvPolynomial (Fin n) K)) : J.FG :=
  IsNoetherian.noetherian J

/-- 51wmmpHand0-14889 (4:08:09) [def] A ring is noetherian (mathlib: `IsNoetherianRing`) iff all
its ideals are finitely generated, iff every increasing sequence of ideals is stationary. -/
example (R : Type u) [CommRing R] :
    (IsNoetherianRing R ↔ ∀ J : Ideal R, J.FG) ∧
      (IsNoetherianRing R ↔ ∀ f : ℕ →o Ideal R, ∃ n, ∀ m, n ≤ m → f n = f m) :=
  ⟨isNoetherianRing_iff_ideal_fg R,
    isNoetherianRing_iff.trans monotone_stabilizes_iff_noetherian.symm⟩

/-- 51wmmpHand0-14955 (4:09:15) [prop] If `k` is noetherian, so are `k[T]` and `k[T_1..T_n]`
(mathlib: `Polynomial.isNoetherianRing`, `MvPolynomial.isNoetherianRing`). -/
theorem prop_14955 [IsNoetherianRing k] (n : ℕ) :
    IsNoetherianRing (Polynomial k) ∧ IsNoetherianRing (MvPolynomial (Fin n) k) :=
  ⟨inferInstance, inferInstance⟩

/-- 51wmmpHand0-15019 (4:10:19) [prop] Over a noetherian `k`, every finitely generated algebra
is finitely presented, and every closed subspace of `E^n` is defined by finitely many equations
(mathlib: `Algebra.FinitePresentation.of_finiteType`). -/
theorem prop_15019 [IsNoetherianRing k] (A : Type u) [CommRing A] [Algebra k A] {σ : Type u}
    [Finite σ] :
    (Algebra.FiniteType k A ↔ Algebra.FinitePresentation k A) ∧
      ∀ J : Ideal (MvPolynomial σ k), ∃ S : Finset (MvPolynomial σ k),
        VJ k J = VS k (S : Set _) := by
  refine ⟨Algebra.FinitePresentation.of_finiteType, fun J => ?_⟩
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian J : J.FG)
  refine ⟨S, ?_⟩
  rw [prop_2102 k (S : Set (MvPolynomial σ k))]
  exact congrArg (VJ k) hS.symm

/-! ### Group objects, kernels and stabilizers -/

/-- 51wmmpHand0-15218 (4:13:38) [prop] A section of `X` over the final object `V_k` amounts to a
point `x ∈ X(k)` (Yoneda). -/
def prop_15218 (X : CommAlgCat.{u} k ⥤ Type u) : (V k k ⟶ X) ≃ X.obj (CommAlgCat.of k k) :=
  homEquivOfCorep k (V.corepresentableBy k k)

/-- An algebra homomorphism `g` kills the ideal generated by `φ(ker ε)` iff `g ∘ φ` factors
through the augmentation `ε`. -/
theorem kills_iff {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (φ : B →ₐ[k] A) (ε : B →ₐ[k] k) {k' : Type*} [CommRing k'] [Algebra k k'] (g : A →ₐ[k] k') :
    (∀ a ∈ (RingHom.ker ε).map φ, g a = 0) ↔ g.comp φ = (Algebra.ofId k k').comp ε := by
  constructor
  · intro h
    ext b
    have hb : b - algebraMap k B (ε b) ∈ RingHom.ker ε := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        sub_self]
    have := h _ (Ideal.mem_map_of_mem φ hb)
    rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_eq_zero] at this
    exact this
  · intro h a ha
    have hle : (RingHom.ker ε).map φ ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker]
      have := DFunLike.congr_fun h b
      simp only [AlgHom.comp_apply] at this
      rw [this, (RingHom.mem_ker).1 hb, map_zero]
    exact (RingHom.mem_ker).1 (hle ha)

/-- 51wmmpHand0-15479 (4:17:59) [prop] If `G = V_A`, `H = V_B` (`φ : B → A`) and `B⁺` is the
augmentation ideal of `B` (`ε : B → k`, the unit section), the kernel of `G → H`, the functor
`Z ↦ {g : g ∘ φ = ε}`, is represented by `A/B⁺A`. -/
def prop_15479 {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (φ : B →ₐ[k] A) (ε : B →ₐ[k] k) (k' : Type*) [CommRing k'] [Algebra k k'] :
    (A ⧸ (RingHom.ker ε).map φ →ₐ[k] k') ≃
      {g : A →ₐ[k] k' // g.comp φ = (Algebra.ofId k k').comp ε} where
  toFun w := ⟨w.comp (Ideal.Quotient.mkₐ k _), (kills_iff k φ ε _).1 fun a ha => by
    change w (Ideal.Quotient.mk _ a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]⟩
  invFun g := Ideal.Quotient.liftₐ _ g.1 ((kills_iff k φ ε g.1).2 g.2)
  left_inv w := Ideal.Quotient.algHom_ext _ (AlgHom.ext fun _ => rfl)
  right_inv g := Subtype.ext (AlgHom.ext fun _ => rfl)

/-- 51wmmpHand0-15555 (4:19:15) [prop] `A ⊗_B (B/J) ≃ A/JA` (mathlib:
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`). -/
def prop_15555 (A B : Type u) [CommRing A] [CommRing B] [Algebra B A] (J : Ideal B) :
    (A ⧸ J.map (algebraMap B A)) ≃ₐ[A] TensorProduct B A (B ⧸ J) :=
  Algebra.TensorProduct.quotIdealMapEquivTensorQuot A J

/-- 51wmmpHand0-15944 (4:25:44) [prop] An intersection of closed subspaces is closed:
`⋂ V_{S_i} = V_{⋃ S_i}` (in particular for finitely many stabilizers). -/
theorem prop_15944 {ι : Type*} (S : ι → Set (MvPolynomial I k)) :
    ⨅ i, VS k (S i) = VS k (⋃ i, S i) := by
  refine Subfunctor.ext (_root_.funext fun k' => Set.ext fun x => ?_)
  rw [Subfunctor.iInf_obj, Set.mem_iInter]
  exact ⟨fun h f hf => by obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hf; exact h i f hi,
    fun h i f hf => h f (Set.mem_iUnion.2 ⟨i, hf⟩)⟩

/-- 51wmmpHand0-16010 (4:26:50) [prop] The intersection of the stabilizers `G_{x_i}` is the
stabilizer of the point `(x_i)` of `∏ X_i` (pointwise, for each `G(Z)`). -/
theorem prop_16010 {G ι : Type*} [Group G] {X : ι → Type*} [∀ i, MulAction G (X i)]
    (x : ∀ i, X i) : MulAction.stabilizer G x = ⨅ i, MulAction.stabilizer G (x i) := by
  ext g
  simp [MulAction.mem_stabilizer_iff, Subgroup.mem_iInf, funext_iff]

/-- 51wmmpHand0-16207 (4:30:07) [prop] Intersections of subobjects, even infinite, are fibre
products over `X`, which exist in `𝒞` (closed case: `prop_15944`). -/
example : Limits.HasWidePullbacks.{u} (CommAlgCat.{u} k)ᵒᵖ := inferInstance

/-! ### Inductive limits and quotients -/

/-- 51wmmpHand0-16465 (4:34:25) [prop] `𝒞` has all inductive limits, since `k`-algebras have all
projective limits. -/
theorem prop_16465 : Limits.HasColimits (CommAlgCat.{u} k)ᵒᵖ := inferInstance

/-- 51wmmpHand0-16527 (4:35:27) [prop] Projective limits of `k`-algebras are computed on the
underlying sets. -/
theorem prop_16527 : Limits.PreservesLimits (forget (CommAlgCat.{u} k)) :=
  Limits.preservesLimits_of_natIso (forgetIsoUnder k).symm

/-- 51wmmpHand0-16658 (4:37:38) [def] A pair `R ⇉ X` is an equivalence relation if `R → X × X` is
a monomorphism and each `R(Z)` is the graph of an equivalence relation on `X(Z)`. -/
def IsEquivRel {X R : CommAlgCat.{u} k ⥤ Type u} (p₁ p₂ : R ⟶ X) : Prop :=
  (∀ Z, Function.Injective fun r : R.obj Z => (p₁.app Z r, p₂.app Z r)) ∧
    ∀ Z, Equivalence fun x y : X.obj Z => ∃ r, p₁.app Z r = x ∧ p₂.app Z r = y

/-- 51wmmpHand0-16789 (4:39:49) [prop] The cokernel of `X ⇉ Y` in `𝒞`, corresponding to
`u, v : B → A`, is represented by the subalgebra `{x ∈ B : u(x) = v(x)}`: morphisms into it are
the `w : C → B` with `u ∘ w = v ∘ w`. -/
def prop_16789 {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (u v : B →ₐ[k] A) (C : Type*) [CommRing C] [Algebra k C] :
    (C →ₐ[k] AlgHom.equalizer u v) ≃ {w : C →ₐ[k] B // u.comp w = v.comp w} where
  toFun f := ⟨(AlgHom.equalizer u v).val.comp f, AlgHom.ext fun c => (f c).2⟩
  invFun w := w.1.codRestrict _ fun c => DFunLike.congr_fun w.2 c
  left_inv _ := rfl
  right_inv _ := rfl

/-- 51wmmpHand0-16981 (4:43:01) [ex], 51wmmpHand0-17146 (4:45:46) [disc] and 51wmmpHand0-17211
(4:46:51) [ex] For a subgroup `H` of `G` (pointwise, in each `G(Z)`), `(h, g) ↦ (g, hg)` is
injective, its image is the relation `g' g⁻¹ ∈ H`, an equivalence relation whose classes are the
`Hg`. -/
theorem ex_16981 {G : Type*} [Group G] (H : Subgroup G) :
    Function.Injective (fun p : H × G => (p.2, (p.1 : G) * p.2)) ∧
      (∀ g g' : G, (∃ p : H × G, (p.2, (p.1 : G) * p.2) = (g, g')) ↔ g' * g⁻¹ ∈ H) ∧
      Equivalence (fun g g' : G => g' * g⁻¹ ∈ H) ∧
      ∀ g g' : G, g' * g⁻¹ ∈ H ↔ ∃ h : H, (h : G) * g = g' := by
  refine ⟨fun p q h => ?_, fun g g' => ⟨?_, fun hg => ⟨(⟨g' * g⁻¹, hg⟩, g), by simp⟩⟩,
    ⟨fun g => by simp, fun {g g'} h => ?_, fun {g g' g''} h h' => ?_⟩, fun g g' => ⟨fun hg =>
      ⟨⟨g' * g⁻¹, hg⟩, by simp⟩, ?_⟩⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h1] at h2
    exact Prod.ext (Subtype.ext (mul_right_cancel h2)) h1
  · rintro ⟨⟨h, g₀⟩, hp⟩
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simp
  · simpa using H.inv_mem h
  · simpa [mul_assoc] using H.mul_mem h' h
  · rintro ⟨h, rfl⟩
    simp

/-- 51wmmpHand0-17406 (4:50:06) [def] The standard Borel subgroup: invertible upper triangular
matrices (the diagonal coefficients are then invertible). -/
def borel (m : ℕ) (k' : Type*) [CommRing k'] : Set (GL (Fin m) k') :=
  {M | ∀ i j, j < i → (M : Matrix (Fin m) (Fin m) k') i j = 0}

/-! ### `GL_n` -/

section GeneralLinear

variable (n : Type u) [Fintype n] [DecidableEq n]

/-- The determinant of the generic matrix `(T_ij)`. -/
def detP : MvPolynomial (n × n) k := (Matrix.of fun i j => (X (i, j) : MvPolynomial (n × n) k)).det

/-- `k[T_ij][1/det]`. -/
abbrev OGL := Localization.Away (detP k n)

theorem aeval_detP {k' : Type*} [CommRing k'] [Algebra k k'] (M : Matrix n n k') :
    aeval (fun p : n × n => M p.1 p.2) (detP k n) = M.det := by
  rw [detP, AlgHom.map_det]
  congr 1
  ext i j
  simp [AlgHom.mapMatrix_apply]

/-- 51wmmpHand0-17469 (4:51:09) [prop] `GL_n` is represented by `k[T_ij][1/det]`: `u ↦ (u(T_ij))`
is a bijection from `Hom_k(k[T_ij][1/det], k')` onto the matrices with invertible determinant. -/
theorem prop_17469 (k' : Type u) [CommRing k'] [Algebra k k'] :
    Function.Injective (fun u : OGL k n →ₐ[k] k' =>
        (Matrix.of fun i j => u (algebraMap (MvPolynomial (n × n) k) (OGL k n) (X (i, j)))  : Matrix n n k')) ∧
      Set.range (fun u : OGL k n →ₐ[k] k' =>
        (Matrix.of fun i j => u (algebraMap (MvPolynomial (n × n) k) (OGL k n) (X (i, j))) : Matrix n n k')) =
        {M | IsUnit M.det} := by
  let ι : MvPolynomial (n × n) k →ₐ[k] OGL k n := IsScalarTower.toAlgHom k _ _
  refine ⟨fun u v huv => ?_, ?_⟩
  · have h1 : u.comp ι = v.comp ι := algHom_ext fun p => by
      have := congrFun (congrFun huv p.1) p.2
      simpa [ι] using this
    have h2 : u.toRingHom.comp (algebraMap (MvPolynomial (n × n) k) (OGL k n)) =
        v.toRingHom.comp (algebraMap (MvPolynomial (n × n) k) (OGL k n)) :=
      RingHom.ext fun p => DFunLike.congr_fun h1 p
    have := IsLocalization.ringHom_ext (Submonoid.powers (detP k n)) h2
    exact AlgHom.ext fun x => DFunLike.congr_fun this x
  · ext M
    constructor
    · rintro ⟨u, rfl⟩
      have h := aeval_unique (u.comp ι)
      have hd := DFunLike.congr_fun h (detP k n)
      change IsUnit (Matrix.of fun i j =>
        u (algebraMap (MvPolynomial (n × n) k) (OGL k n) (X (i, j)))).det
      rw [← aeval_detP k]
      have : (fun p : n × n => (Matrix.of fun i j => u (algebraMap _ (OGL k n) (X (i, j)))) p.1 p.2)
          = (u.comp ι) ∘ X := rfl
      rw [this, ← hd]
      exact (IsLocalization.Away.algebraMap_isUnit (detP k n)).map u
    · intro hM
      let g : MvPolynomial (n × n) k →+* k' := (aeval fun p : n × n => M p.1 p.2).toRingHom
      have hg : IsUnit (g (detP k n)) := by
        change IsUnit (aeval (fun p : n × n => M p.1 p.2) (detP k n))
        rw [aeval_detP]; exact hM
      let l : OGL k n →+* k' := IsLocalization.Away.lift (detP k n) hg
      have hl : ∀ p, l (algebraMap _ _ p) = aeval (fun p : n × n => M p.1 p.2) p :=
        fun p => IsLocalization.lift_eq _ p
      refine ⟨{ l with commutes' := fun c => ?_ }, ?_⟩
      · change l (algebraMap k (OGL k n) c) = _
        rw [IsScalarTower.algebraMap_apply k (MvPolynomial (n × n) k) (OGL k n), hl,
          AlgHom.commutes]
      · ext i j
        change l _ = _
        rw [hl, aeval_X]

end GeneralLinear

end June4

end

end Buffalo.AG.Part01
