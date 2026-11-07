import Mathlib

/-!
# Buffalo, algebraic geometry, part 01 (a): 29 and 30 May 1973

The entries of `docs/buffalo-ag/index.tex` for the sessions of 29 and 30 May 1973 (video
`51wmmpHand0`, 0:00:00–3:07:15): affine algebraic spaces over a ring `k` as functors on
`k`-algebras, the dictionary with ideals of polynomial rings, the Nullstellensatz, algebras of
functions, and products and sums of affine spaces.

Conventions. `k` is a commutative ring, a `k`-algebra is an object of `CommAlgCat.{u} k`, and
`P_I = MvPolynomial I k`. The functor `E k I` is the standard affine space `k' ↦ k'^I`;
`Z S k'` is the set of solutions in `k'^I` of a system `S ⊆ P_I`, and `VS k S` the subfunctor of
`E k I` it defines; `V k A` is the functor `k' ↦ Hom_k(A, k')` represented by `A`. "Representable"
is mathlib's `Functor.IsCorepresentable` (a covariant functor `CommAlgCat k ⥤ Type u`).
-/

open CategoryTheory MvPolynomial

universe u

namespace Buffalo.AG.Part01

noncomputable section

section Setup

variable (k : Type u) [CommRing k]

/-- `aeval` commutes with algebra homomorphisms: `f(φ ∘ x) = φ(f(x))`. -/
theorem aeval_comp_algHom {I A B : Type*} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (φ : A →ₐ[k] B) (x : I → A) (f : MvPolynomial I k) :
    aeval (fun i => φ (x i)) f = φ (aeval x f) :=
  (DFunLike.congr_fun (comp_aeval (R := k) x φ) f).symm

/-- `Ideal.Quotient.liftₐ` on a class. -/
@[simp] theorem liftₐ_mk {A B : Type*} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (J : Ideal A) (f : A →ₐ[k] B) (hf : ∀ a ∈ J, f a = 0) (a : A) :
    Ideal.Quotient.liftₐ J f hf (Ideal.Quotient.mk J a) = f a := rfl

/-- A morphism of `CommAlgCat k` from an algebra homomorphism, with the objects given. -/
abbrev hm {A B : CommAlgCat.{u} k} (f : A →ₐ[k] B) : A ⟶ B := ConcreteCategory.ofHom f

/-- 51wmmpHand0-1570 (0:26:10) [def] The standard affine space `E^I`, the functor
`k' ↦ k'^I` on `k`-algebras, a homomorphism `u` acting by `u^I`. -/
def E (I : Type u) : CommAlgCat.{u} k ⥤ Type u where
  obj k' := I → k'
  map {_ _} f := ↾fun x i => f (x i)

@[simp] theorem E_map_apply (I : Type u) {k' k'' : CommAlgCat.{u} k} (f : k' ⟶ k'')
    (x : (E k I).obj k') : (E k I).map f x = fun i => f (x i) := rfl

/-- The solutions in `k'^I` of a system of equations `S ⊆ P_I`. -/
def Z {I : Type*} (S : Set (MvPolynomial I k)) (L : Type*) [CommRing L] [Algebra k L] :
    Set (I → L) :=
  {x | ∀ f ∈ S, aeval x f = 0}

/-- 51wmmpHand0-1703 (0:28:23) [def] A system of equations `S = (f_j)` in `P_I` defines a
subfunctor `V_S ⊂ E^I`: `V_S(k')` is the set of solutions in `k'^I`. -/
def VS {I : Type u} (S : Set (MvPolynomial I k)) : Subfunctor (E k I) where
  obj k' := Z k S k'
  map {k' k''} u x hx f hf := by
    change aeval (fun i => u (x i)) f = 0
    rw [aeval_comp_algHom k u.hom x f, hx f hf, map_zero]

/-- The closed subspace `V_J` defined by an ideal `J` of `P_I`. -/
abbrev VJ {I : Type u} (J : Ideal (MvPolynomial I k)) : Subfunctor (E k I) := VS k (J : Set _)

/-- The functor `V_A : k' ↦ Hom_k(A, k')` represented by a `k`-algebra `A`. -/
def V (A : Type u) [CommRing A] [Algebra k A] : CommAlgCat.{u} k ⥤ Type u where
  obj k' := A →ₐ[k] k'
  map {_ _} f := ↾fun φ => f.hom.comp φ

@[simp] theorem V_map_apply (A : Type u) [CommRing A] [Algebra k A] {k' k'' : CommAlgCat.{u} k}
    (f : k' ⟶ k'') (φ : (V k A).obj k') : (V k A).map f φ = f.hom.comp φ := rfl

/-- `V_A` is represented by `A`. -/
def V.corepresentableBy (A : Type u) [CommRing A] [Algebra k A] :
    (V k A).CorepresentableBy (CommAlgCat.of k A) where
  homEquiv := { toFun := fun f => f.hom, invFun := CommAlgCat.ofHom,
                left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  homEquiv_comp _ _ := rfl

instance (A : Type u) [CommRing A] [Algebra k A] : (V k A).IsCorepresentable :=
  (V.corepresentableBy k A).isCorepresentable

/-- Natural transformations out of a functor represented by `X` are the elements of the target
at `X` (Yoneda), transported along the representation. -/
noncomputable def homEquivOfCorep {F G : CommAlgCat.{u} k ⥤ Type u} {X : CommAlgCat.{u} k}
    (e : F.CorepresentableBy X) : (F ⟶ G) ≃ G.obj X :=
  (e.toIso.symm.homCongr (Iso.refl G)).trans coyonedaEquiv

/-- Two representable functors `V_A`, `V_B` are isomorphic iff `A ≃ B` (Yoneda). -/
theorem nonempty_V_iso_iff (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] :
    Nonempty (V k A ≅ V k B) ↔ Nonempty (A ≃ₐ[k] B) := by
  constructor
  · rintro ⟨e⟩
    let e' : coyoneda.obj (Opposite.op (CommAlgCat.of k A)) ≅
        coyoneda.obj (Opposite.op (CommAlgCat.of k B)) :=
      (V.corepresentableBy k A).toIso ≪≫ e ≪≫ (V.corepresentableBy k B).toIso.symm
    exact ⟨(CommAlgCat.algEquivOfIso (Coyoneda.fullyFaithful.preimageIso e').unop).symm⟩
  · rintro ⟨e⟩
    exact ⟨(V.corepresentableBy k A).toIso.symm ≪≫
      coyoneda.mapIso (CommAlgCat.isoMk e).symm.op ≪≫ (V.corepresentableBy k B).toIso⟩

end Setup

/-! ## 29 May 1973 — Affine algebraic spaces as functors -/

section May29

variable (k : Type u) [CommRing k] {I : Type u}

/-- 51wmmpHand0-791 (0:13:11) [cex] A polynomial `f ∈ P_I` defines a map `k^I → k` which in
general does not determine `f`: over `k = 𝔽₂`, `T² - T ≠ 0` vanishes at every point. -/
theorem cex_791 : ∃ f : MvPolynomial Unit (ZMod 2), f ≠ 0 ∧ ∀ x : Unit → ZMod 2, eval x f = 0 := by
  refine ⟨X () ^ 2 - X (), fun h => ?_, fun x => ?_⟩
  · have := congrArg (aeval (R := ZMod 2) (fun _ => (Polynomial.X : Polynomial (ZMod 2)))) h
    simp only [map_sub, map_pow, aeval_X, map_zero] at this
    have h2 := congrArg (Polynomial.coeff · 1) this
    simp [Polynomial.coeff_X] at h2
  · simp only [map_sub, map_pow, eval_X]
    generalize x () = a
    fin_cases a <;> decide

/-- 51wmmpHand0-920 (0:15:20) [prop] For every `k`-algebra `k'`, `u ↦ (u(T_i))_i` is a bijection
from `Hom_k(P_I, k')` onto `k'^I`. -/
theorem prop_920 (k' : Type*) [CommRing k'] [Algebra k k'] :
    Function.Bijective (fun u : MvPolynomial I k →ₐ[k] k' => fun i => u (X i)) :=
  ⟨fun _ _ h => algHom_ext fun i => congrFun h i, fun x => ⟨aeval x, funext fun i => aeval_X x i⟩⟩

/-- 51wmmpHand0-983 (0:16:23) [prop] A point `x ∈ k^I` is a homomorphism `ε_x : P_I → k`, and
`f(x) = ε_x(f)` (mathlib: `MvPolynomial.coe_aeval_eq_eval`). -/
theorem prop_983 (x : I → k) (f : MvPolynomial I k) : eval x f = aeval x f := by
  rw [← coe_aeval_eq_eval]; rfl

/-- 51wmmpHand0-1047 (0:17:27) [prop] For fixed `x`, `f ↦ f(x)` is a homomorphism of
`k`-algebras: `(f+g)(x) = f(x)+g(x)`, `(fg)(x) = f(x)g(x)`, `(λf)(x) = λ f(x)`. -/
theorem prop_1047 {k' : Type*} [CommRing k'] [Algebra k k'] (x : I → k') (f g : MvPolynomial I k)
    (c : k) : aeval x (f + g) = aeval x f + aeval x g ∧ aeval x (f * g) = aeval x f * aeval x g ∧
      aeval x (c • f) = c • aeval x f :=
  ⟨map_add _ _ _, map_mul _ _ _, map_smul _ _ _⟩

/-- 51wmmpHand0-2102 (0:35:02) [prop] The solutions of `S` in every `k'` are those of the ideal
generated by `S`: `V_S = V_J`. -/
theorem prop_2102 (S : Set (MvPolynomial I k)) : VS k S = VJ k (Ideal.span S) := by
  ext k' x
  refine ⟨fun h f hf => ?_, fun h f hf => h f (Ideal.subset_span hf)⟩
  have : Ideal.span S ≤ RingHom.ker (aeval (R := k) (x : I → k')) :=
    Ideal.span_le.2 fun g hg => (RingHom.mem_ker).2 (h g hg)
  exact (RingHom.mem_ker).1 (this hf)

/-- The canonical point of `V_J` with values in `P_I/J`. -/
def can (J : Ideal (MvPolynomial I k)) : I → MvPolynomial I k ⧸ J :=
  fun i => Ideal.Quotient.mk J (X i)

theorem aeval_can (J : Ideal (MvPolynomial I k)) (f : MvPolynomial I k) :
    aeval (can k J) f = Ideal.Quotient.mk J f := by
  have := aeval_comp_algHom k (Ideal.Quotient.mkₐ k J) X f
  rw [aeval_X_left_apply] at this
  exact this

theorem can_mem (J : Ideal (MvPolynomial I k)) : can k J ∈ Z k (J : Set _) _ := fun f hf => by
  rw [aeval_can, Ideal.Quotient.eq_zero_iff_mem]; exact hf

/-- 51wmmpHand0-6782 (1:53:02) [prop] `J ⊆ J'` if and only if `V_{J'} ⊆ V_J`. -/
theorem prop_6782 (J J' : Ideal (MvPolynomial I k)) : J ≤ J' ↔ VJ k J' ≤ VJ k J := by
  refine ⟨fun h k' x hx f hf => hx f (h hf), fun h f hf => ?_⟩
  have := h (CommAlgCat.of k (MvPolynomial I k ⧸ J')) (can_mem k J') f hf
  rwa [aeval_can, Ideal.Quotient.eq_zero_iff_mem] at this

/-- 51wmmpHand0-2298 (0:38:18) [prop] The map `J ↦ V_J` is injective; its values are the
subfunctors defined by equations. -/
theorem prop_2298 : Function.Injective (fun J : Ideal (MvPolynomial I k) => VJ k J) ∧
    ∀ S : Set (MvPolynomial I k), ∃ J : Ideal (MvPolynomial I k), VS k S = VJ k J :=
  ⟨fun J J' h => le_antisymm ((prop_6782 k J J').2 (le_of_eq h.symm))
      ((prop_6782 k J' J).2 (le_of_eq h)), fun S => ⟨_, prop_2102 k S⟩⟩

/-- 51wmmpHand0-6522 (1:48:42) [prop] `f ∈ J` iff `f(x') = 0` for every `k'` and every
`x' ∈ V_J(k')`. -/
theorem prop_6522 (J : Ideal (MvPolynomial I k)) (f : MvPolynomial I k) :
    f ∈ J ↔ ∀ (k' : CommAlgCat.{u} k), ∀ x ∈ (VJ k J).obj k', aeval x f = 0 := by
  refine ⟨fun hf k' x hx => hx f hf, fun h => ?_⟩
  have := h (CommAlgCat.of k (MvPolynomial I k ⧸ J)) _ (can_mem k J)
  rwa [aeval_can, Ideal.Quotient.eq_zero_iff_mem] at this

/-- 51wmmpHand0-6651 (1:50:51) [prop] It suffices to take `k' = P_I/J` and the canonical point:
`f ∈ J` iff `f` vanishes at the point `(T_i mod J)` of `V_J(P_I/J)`. -/
theorem prop_6651 (J : Ideal (MvPolynomial I k)) (f : MvPolynomial I k) :
    f ∈ J ↔ aeval (can k J) f = 0 := by
  rw [aeval_can, Ideal.Quotient.eq_zero_iff_mem]

/-- 51wmmpHand0-2819 (0:46:59) [prop] `V_J(k')` is identified with the homomorphisms `P_I → k'`
vanishing on `J`, hence with `Hom_k(P_I/J, k')`; 51wmmpHand0-2889 (0:48:09) [prop] the
identification is functorial: `V_J` is represented by `P_I/J`. -/
def VJ.corepresentableBy (J : Ideal (MvPolynomial I k)) :
    (VJ k J).toFunctor.CorepresentableBy (CommAlgCat.of k (MvPolynomial I k ⧸ J)) where
  homEquiv {k'} :=
    { toFun := fun φ => ⟨fun i => φ (Ideal.Quotient.mk J (X i)), fun f hf => by
        have := aeval_comp_algHom k φ.hom (can k J) f
        simp only [can] at this
        rw [this, aeval_can, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]⟩
      invFun := fun x => CommAlgCat.ofHom (Ideal.Quotient.liftₐ J (aeval x.1) x.2)
      left_inv := fun φ => by
        apply CommAlgCat.hom_ext
        apply Ideal.Quotient.algHom_ext
        apply MvPolynomial.algHom_ext
        intro i
        exact aeval_X _ i
      right_inv := fun x => by
        apply Subtype.ext
        funext i
        exact aeval_X _ i }
  homEquiv_comp _ _ := rfl

theorem prop_2819 (J : Ideal (MvPolynomial I k)) (k' : CommAlgCat.{u} k) :
    Nonempty ((VJ k J).obj k' ≃ (MvPolynomial I k ⧸ J →ₐ[k] k')) :=
  ⟨((VJ.corepresentableBy k J).homEquiv.symm).trans
    { toFun := fun f => f.hom, invFun := CommAlgCat.ofHom,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }⟩

/-- 51wmmpHand0-2889 (0:48:09) [prop] `V_J ≃ V_{P_I/J}`, functorially in `k'`. -/
noncomputable def prop_2889 (J : Ideal (MvPolynomial I k)) :
    (VJ k J).toFunctor ≅ V k (MvPolynomial I k ⧸ J) :=
  (VJ.corepresentableBy k J).toIso.symm ≪≫ (V.corepresentableBy k _).toIso

/-- 51wmmpHand0-2954 (0:49:14) [def] The closed algebraic subspaces of `E^I` are the `V_J`; a
functor isomorphic to one of them is an affine algebraic space over `k`. -/
def IsAffineAlgSpace (F : CommAlgCat.{u} k ⥤ Type u) : Prop :=
  ∃ (I : Type u) (J : Ideal (MvPolynomial I k)), Nonempty (F ≅ (VJ k J).toFunctor)

/-- 51wmmpHand0-3290 (0:54:50) [prop] Every `k`-algebra `A` is a quotient `P_I/J`: take `I = A`,
`T_a ↦ a`, and `J` its kernel. -/
noncomputable def prop_3290 (A : Type u) [CommRing A] [Algebra k A] :
    (MvPolynomial A k ⧸ RingHom.ker (aeval (R := k) (id : A → A))) ≃ₐ[k] A :=
  Ideal.quotientKerAlgEquivOfSurjective (f := aeval (R := k) (id : A → A))
    fun a => ⟨X a, aeval_X _ _⟩

/-- 51wmmpHand0-2430 (0:40:30) [prop] A functor from `k`-algebras to sets is isomorphic to some
`V_S` if and only if it is representable. -/
theorem prop_2430 (F : CommAlgCat.{u} k ⥤ Type u) :
    (∃ (I : Type u) (S : Set (MvPolynomial I k)), Nonempty (F ≅ (VS k S).toFunctor)) ↔
      F.IsCorepresentable := by
  constructor
  · rintro ⟨I, S, ⟨e⟩⟩
    rw [prop_2102] at e
    exact ((VJ.corepresentableBy k _).ofIso e.symm).isCorepresentable
  · intro hF
    let A := F.coreprX
    refine ⟨A, (RingHom.ker (aeval (R := k) (id : A → A)) : Set _), ⟨?_⟩⟩
    exact F.coreprW.symm ≪≫ coyoneda.mapIso (CommAlgCat.isoMk (prop_3290 k A)).op ≪≫
      (VJ.corepresentableBy k _).toIso

/-- 51wmmpHand0-2499 (0:41:39) [prop] `V_A` is isomorphic to a subfunctor `V_S` of `E^I` if and
only if `A` is a quotient of `P_I`, that is, generated by a family indexed by `I`. -/
theorem prop_2499 (A : Type u) [CommRing A] [Algebra k A] :
    (∃ S : Set (MvPolynomial I k), Nonempty (V k A ≅ (VS k S).toFunctor)) ↔
      ∃ a : I → A, Function.Surjective (aeval (R := k) a) := by
  constructor
  · rintro ⟨S, ⟨e⟩⟩
    rw [prop_2102] at e
    obtain ⟨f⟩ := (nonempty_V_iso_iff k _ _).1 ⟨(e ≪≫ prop_2889 k _).symm⟩
    refine ⟨fun i => f (Ideal.Quotient.mk _ (X i)), fun a => ?_⟩
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (f.symm a)
    refine ⟨p, ?_⟩
    have h3 : (aeval fun i => f (Ideal.Quotient.mk _ (X i))) p = f (aeval (can k _) p) :=
      aeval_comp_algHom k f.toAlgHom (can k _) p
    rw [h3, aeval_can, hp, AlgEquiv.apply_symm_apply]
  · rintro ⟨a, ha⟩
    obtain ⟨e⟩ := (nonempty_V_iso_iff k A (MvPolynomial I k ⧸ RingHom.ker (aeval (R := k) a))).2
      ⟨(Ideal.quotientKerAlgEquivOfSurjective ha).symm⟩
    exact ⟨(RingHom.ker (aeval (R := k) a) : Set _), ⟨e ≪≫ (prop_2889 k _).symm⟩⟩

/-- The map `Hom_k(A, k') → k'^I`, `u ↦ (u(a_i))_i`, defined by a family `a : I → A`. -/
def embFun {A : Type u} [CommRing A] [Algebra k A] (a : I → A) (k' : Type u) [CommRing k']
    [Algebra k k'] : (A →ₐ[k] k') → (I → k') := fun u i => u (a i)

/-- The morphism `V_A → E^I` defined by a family `a : I → A`. -/
def emb {A : Type u} [CommRing A] [Algebra k A] (a : I → A) : V k A ⟶ E k I where
  app k' := ↾embFun k a k'
  naturality _ _ _ := rfl

@[simp] theorem emb_app_apply {A : Type u} [CommRing A] [Algebra k A] (a : I → A)
    (k' : CommAlgCat.{u} k) (u : (V k A).obj k') : (emb k a).app k' u = embFun k a k' u := rfl

/-- 51wmmpHand0-2565 (0:42:45) [prop] The morphism `V_A → E^I` defined by `a : I → A` is an
isomorphism onto a closed subspace `V_S` if and only if `(a_i)` generates `A`. (Every morphism
`V_A → E^I` is of this form: `prop_4837`.) -/
theorem prop_2565 {A : Type u} [CommRing A] [Algebra k A] (a : I → A) :
    (∃ S : Set (MvPolynomial I k), ∀ k' : CommAlgCat.{u} k,
      Function.Injective (embFun k a k') ∧ Set.range (embFun k a k') = Z k S k') ↔
      Function.Surjective (aeval (R := k) a) := by
  constructor
  · rintro ⟨S, hS⟩
    set J := Ideal.span S
    have hZ : ∀ L : Type u, ∀ [CommRing L] [Algebra k L], Z k S L = Z k (J : Set _) L := by
      intro L _ _
      exact congrArg (fun G : Subfunctor (E k I) => G.obj (CommAlgCat.of k L)) (prop_2102 k S)
    -- `a ∈ V_J(A)`, so `J ⊆ ker (aeval a)`.
    have haJ : a ∈ Z k (J : Set _) A := by
      rw [← hZ, ← (hS (CommAlgCat.of k A)).2]
      exact ⟨AlgHom.id k A, rfl⟩
    let abar : MvPolynomial I k ⧸ J →ₐ[k] A := Ideal.Quotient.liftₐ J (aeval a) haJ
    -- the canonical point of `V_J(P_I/J)` comes from some `u : A → P_I/J`.
    have hc : can k J ∈ Set.range (embFun k a (MvPolynomial I k ⧸ J)) := by
      rw [(hS (CommAlgCat.of k (MvPolynomial I k ⧸ J))).2, hZ]; exact can_mem k J
    obtain ⟨w, hw⟩ := hc
    have hw' : ∀ i, w (a i) = Ideal.Quotient.mk J (X i) := fun i => congrFun hw i
    have h1 : (abar.comp w) = AlgHom.id k A := by
      apply (hS (CommAlgCat.of k A)).1
      funext i
      simp only [embFun, AlgHom.comp_apply, hw', AlgHom.id_apply]
      exact aeval_X a i
    intro y
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (w y)
    refine ⟨p, ?_⟩
    have : abar (w y) = y := by simpa using DFunLike.congr_fun h1 y
    rw [← this, ← hp]
    rfl
  · intro ha
    refine ⟨(RingHom.ker (aeval (R := k) a) : Set _), fun k' => ⟨?_, ?_⟩⟩
    · intro u v huv
      have : u.comp (aeval a) = v.comp (aeval a) :=
        algHom_ext fun i => by simpa [embFun] using congrFun huv i
      ext y
      obtain ⟨p, rfl⟩ := ha y
      exact DFunLike.congr_fun this p
    · ext x
      constructor
      · rintro ⟨u, rfl⟩ f hf
        change aeval (fun i => u (a i)) f = 0
        rw [aeval_comp_algHom k u, (RingHom.mem_ker).1 hf, map_zero]
      · intro hx
        refine ⟨AlgHom.liftOfSurjective (aeval a) ha (aeval x)
          (fun f hf => (RingHom.mem_ker).2 (hx f hf)), ?_⟩
        funext i
        simp only [embFun]
        rw [← aeval_X (R := k) a i, AlgHom.liftOfSurjective_apply, aeval_X]

/-- 51wmmpHand0-3423 (0:57:03) [prop] The affine algebraic spaces over `k` are exactly the
representable functors (and an embedding into `E^I` amounts to a generating family indexed by
`I`: `prop_2565`). -/
theorem prop_3423 (F : CommAlgCat.{u} k ⥤ Type u) : IsAffineAlgSpace k F ↔ F.IsCorepresentable := by
  rw [← prop_2430]
  constructor
  · rintro ⟨I, J, e⟩; exact ⟨I, _, e⟩
  · rintro ⟨I, S, ⟨e⟩⟩
    rw [prop_2102] at e
    exact ⟨I, _, ⟨e⟩⟩

/-- 51wmmpHand0-3851 (1:04:11) [def] A morphism `V_J → V_{J'}` is a natural transformation. -/
example (J : Ideal (MvPolynomial I k)) {I' : Type u} (J' : Ideal (MvPolynomial I' k)) :
    ((VJ k J).toFunctor ⟶ (VJ k J').toFunctor) = NatTrans (VJ k J).toFunctor (VJ k J').toFunctor :=
  rfl

/-- 51wmmpHand0-4057 (1:07:37) [prop] A family `(F_{i'})` of polynomials of `P_I` defines a
morphism `E^I → E^{I'}`. -/
def polyMap {I' : Type u} (F : I' → MvPolynomial I k) : E k I ⟶ E k I' where
  app k' := ↾fun x i' => aeval x (F i')
  naturality k' k'' u := ConcreteCategory.hom_ext _ _ fun x => _root_.funext fun i' => by
    change aeval (fun i => u (x i)) (F i') = u (aeval x (F i'))
    exact aeval_comp_algHom k u.hom x (F i')

/-- 51wmmpHand0-4188 (1:09:48) [prop] The morphisms `V_A → V_{A'}` correspond bijectively to the
homomorphisms of `k`-algebras `A' → A` (Yoneda). -/
noncomputable def prop_4188 (A A' : Type u) [CommRing A] [Algebra k A] [CommRing A']
    [Algebra k A'] : (V k A ⟶ V k A') ≃ (A' →ₐ[k] A) :=
  homEquivOfCorep k (V.corepresentableBy k A)

/-- 51wmmpHand0-4571 (1:16:11) [prop] Every morphism `V_J → V_{J'}` is induced by a polynomial
map `E^I → E^{I'}`, given by `F : I' → P_I`, whose homomorphism `P_{I'} → P_I` sends `J'` into
`J`. -/
theorem prop_4571 {I' : Type u} (J : Ideal (MvPolynomial I k)) (J' : Ideal (MvPolynomial I' k))
    (φ : (VJ k J).toFunctor ⟶ (VJ k J').toFunctor) :
    ∃ F : I' → MvPolynomial I k, (∀ f ∈ J', bind₁ F f ∈ J) ∧
      ∀ (k' : CommAlgCat.{u} k) (x : (VJ k J).toFunctor.obj k'),
        (φ.app k' x).1 = fun i' => aeval x.1 (F i') := by
  let K := CommAlgCat.of k (MvPolynomial I k ⧸ J)
  let x0 : (VJ k J).toFunctor.obj K := ⟨can k J, can_mem k J⟩
  let p : I' → MvPolynomial I k ⧸ J := (φ.app K x0).1
  choose F hF using fun i' => Ideal.Quotient.mk_surjective (p i')
  have hp : p = fun i' => Ideal.Quotient.mk J (F i') := funext fun i' => (hF i').symm
  refine ⟨F, fun f hf => ?_, fun k' x => ?_⟩
  · have h := (φ.app K x0).2 f hf
    change aeval p f = 0 at h
    rw [hp] at h
    have := aeval_comp_algHom k (Ideal.Quotient.mkₐ k J) F f
    simp only [Ideal.Quotient.mkₐ_eq_mk] at this
    rw [this, Ideal.Quotient.eq_zero_iff_mem] at h
    exact h
  · let u : K ⟶ k' := CommAlgCat.ofHom (Ideal.Quotient.liftₐ J (aeval x.1) x.2)
    have hx : (VJ k J).toFunctor.map u x0 = x := by
      apply Subtype.ext
      funext i
      exact aeval_X _ i
    have h := NatTrans.naturality_apply φ u x0
    rw [hx] at h
    rw [h]
    funext i'
    change u (p i') = _
    rw [hp]
    rfl

/-- 51wmmpHand0-4837 (1:20:37) [prop] `E^I` is represented by `P_I`. -/
def E.corepresentableBy (I : Type u) :
    (E k I).CorepresentableBy (CommAlgCat.of k (MvPolynomial I k)) where
  homEquiv :=
    { toFun := fun φ i => φ (X i), invFun := fun x => CommAlgCat.ofHom (aeval x),
      left_inv := fun φ => by
        apply CommAlgCat.hom_ext
        apply MvPolynomial.algHom_ext
        intro i
        simp
      right_inv := fun x => by funext i; exact aeval_X x i }
  homEquiv_comp _ _ := rfl

/-- 51wmmpHand0-4837 (1:20:37) [prop] A morphism `V_A → E^I` amounts to a homomorphism
`P_I → A`, that is, to a family of elements of `A` indexed by `I`; the family `a` gives the
morphism `emb a`. -/
theorem prop_4837 (A : Type u) [CommRing A] [Algebra k A] :
    Function.Bijective (fun a : I → A => emb k a) := by
  let idA : (V k A).obj (CommAlgCat.of k A) := AlgHom.id k A
  refine ⟨fun a b h => funext fun i => ?_, fun φ => ⟨φ.app (CommAlgCat.of k A) idA, ?_⟩⟩
  · have := congrArg (fun φ : V k A ⟶ E k I => φ.app (CommAlgCat.of k A) idA i) h
    exact this
  · refine NatTrans.ext (funext fun k' => ConcreteCategory.hom_ext _ _ fun u => ?_)
    have h := NatTrans.naturality_apply φ (hm k (A := CommAlgCat.of k A) (B := k') u) idA
    have h2 : (V k A).map (hm k (A := CommAlgCat.of k A) (B := k') u) idA = u := rfl
    rw [h2] at h
    change embFun k (φ.app (CommAlgCat.of k A) idA : I → A) k' u = φ.app k' u
    rw [h]
    rfl

/-- 51wmmpHand0-4970 (1:22:50) [prop] The morphism `V_A → E^I` defined by `P_I → A` is a
monomorphism iff `P_I → A` is an epimorphism (of `k`-algebras); surjectivity is sufficient
(`prop_4970_surj`) but not necessary (`ex_5353`). -/
theorem prop_4970 {A : Type u} [CommRing A] [Algebra k A] (a : I → A) :
    Mono (emb k a) ↔ Epi (CommAlgCat.ofHom (aeval (R := k) a)) := by
  rw [NatTrans.mono_iff_mono_app]
  simp only [mono_iff_injective]
  constructor
  · intro h
    refine ⟨fun {k'} u v huv => ?_⟩
    apply CommAlgCat.hom_ext
    apply h k'
    funext i
    show embFun k a k' u.hom i = embFun k a k' v.hom i
    have := congrArg (fun w : CommAlgCat.of k (MvPolynomial I k) ⟶ k' => w (X i)) huv
    simpa [embFun] using this
  · intro h k' u v huv
    have huv' : embFun k a k' u = embFun k a k' v := huv
    have : CommAlgCat.ofHom (aeval (R := k) a) ≫ CommAlgCat.ofHom u =
        CommAlgCat.ofHom (aeval (R := k) a) ≫ CommAlgCat.ofHom v := by
      apply CommAlgCat.hom_ext
      apply MvPolynomial.algHom_ext
      intro i
      change (show A →ₐ[k] k' from u) (aeval a (X i)) = (show A →ₐ[k] k' from v) (aeval a (X i))
      rw [aeval_X]
      exact congrFun huv' i
    exact congrArg CommAlgCat.Hom.hom ((cancel_epi _).1 this)

theorem prop_4970_surj {A : Type u} [CommRing A] [Algebra k A] (a : I → A)
    (ha : Function.Surjective (aeval (R := k) a)) : Mono (emb k a) := by
  rw [prop_4970]
  refine ⟨fun {k'} u v huv => ?_⟩
  ext y
  obtain ⟨p, rfl⟩ := ha y
  exact congrArg (fun w : CommAlgCat.of k (MvPolynomial I k) ⟶ k' => w p) huv

open LaurentPolynomial in
/-- 51wmmpHand0-5353 (1:29:13) [ex] The inclusion `k[T] → k[T, T⁻¹]` is a non-surjective
epimorphism (`k ≠ 0`): a homomorphism from `k[T, T⁻¹]` is determined by the image of `T`. -/
theorem ex_5353 [Nontrivial k] :
    Epi (CommAlgCat.ofHom (Polynomial.toLaurentAlg (R := k))) ∧
      ¬ Function.Surjective (Polynomial.toLaurent (R := k)) := by
  refine ⟨⟨fun {k'} u v huv => ?_⟩, fun h => ?_⟩
  · apply CommAlgCat.hom_ext
    have h' : u.hom.toRingHom.comp (algebraMap (Polynomial k) k[T;T⁻¹]) =
        v.hom.toRingHom.comp (algebraMap (Polynomial k) k[T;T⁻¹]) := by
      ext p
      · simpa [algebraMap_eq_toLaurent] using
          congrArg (fun w : CommAlgCat.of k (Polynomial k) ⟶ k' => w (Polynomial.C p)) huv
      · simpa [algebraMap_eq_toLaurent] using
          congrArg (fun w : CommAlgCat.of k (Polynomial k) ⟶ k' => w Polynomial.X) huv
    have := IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : (Polynomial k))) h'
    exact AlgHom.ext fun x => DFunLike.congr_fun this x
  · obtain ⟨p, hp⟩ := h (T (-1))
    have h1 : Polynomial.toLaurent (Polynomial.X * p) = Polynomial.toLaurent (1 : (Polynomial k)) := by
      rw [map_mul, hp, Polynomial.toLaurent_X, ← T_add, map_one]
      norm_num
    exact Polynomial.not_isUnit_X (isUnit_iff_exists_inv.2 ⟨p, Polynomial.toLaurent_injective h1⟩)

open LaurentPolynomial in
/-- 51wmmpHand0-5417 (1:30:17) [prop] `Hom_k(k[T, T⁻¹], k')` is in bijection with the invertible
elements of `k'`, by `u ↦ u(T)`. -/
theorem prop_5417 (k' : Type*) [CommRing k'] [Algebra k k'] :
    Function.Injective (fun u : k[T;T⁻¹] →ₐ[k] k' => u (T 1)) ∧
      Set.range (fun u : k[T;T⁻¹] →ₐ[k] k' => u (T 1)) = {t | IsUnit t} := by
  refine ⟨fun u v huv => ?_, ?_⟩
  · have h' : u.toRingHom.comp (algebraMap (Polynomial k) k[T;T⁻¹]) =
        v.toRingHom.comp (algebraMap (Polynomial k) k[T;T⁻¹]) := by
      ext p
      · simp [algebraMap_eq_toLaurent]
        rw [LaurentPolynomial.C_eq_algebraMap, AlgHom.commutes, AlgHom.commutes]
      · simpa [algebraMap_eq_toLaurent] using huv
    have := IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : (Polynomial k))) h'
    exact AlgHom.ext fun x => DFunLike.congr_fun this x
  · ext t
    constructor
    · rintro ⟨u, rfl⟩
      exact (isUnit_T 1).map u
    · intro ht
      let g : (Polynomial k) →+* k' := (Polynomial.aeval t).toRingHom
      have hg : IsUnit (g Polynomial.X) := by simpa [g] using ht
      let l : k[T;T⁻¹] →+* k' := IsLocalization.Away.lift (Polynomial.X : (Polynomial k)) hg
      have hl : ∀ p : (Polynomial k), l (Polynomial.toLaurent p) = Polynomial.aeval t p := fun p => by
        rw [← algebraMap_eq_toLaurent]
        exact IsLocalization.lift_eq _ p
      refine ⟨{ l with commutes' := fun c => ?_ }, ?_⟩
      · change l (algebraMap k k[T;T⁻¹] c) = _
        rw [← LaurentPolynomial.C_eq_algebraMap, ← Polynomial.toLaurent_C, hl]
        simp
      · change l (T 1) = t
        rw [← Polynomial.toLaurent_X, hl]
        simp

open LaurentPolynomial in
/-- 51wmmpHand0-5552 (1:32:32) [cex] The monomorphism `V_{k[T,T⁻¹]} → E^1`, `u ↦ u(T)`, is an
isomorphism onto no closed subspace `V_J` of `E^1` (`k ≠ 0`). -/
theorem cex_5552 [Nontrivial k] : ¬ ∃ J : Ideal (Polynomial k), ∀ (k' : Type u) [CommRing k'] [Algebra k k']
    (t : k'), (∃ u : k[T;T⁻¹] →ₐ[k] k', u (T 1) = t) ↔ ∀ f ∈ J, Polynomial.aeval t f = 0 := by
  rintro ⟨J, hJ⟩
  have h0 : ∀ f ∈ J, f = 0 := by
    intro f hf
    have := ((hJ k[T;T⁻¹] (T 1)).1 ⟨AlgHom.id k _, rfl⟩) f hf
    have h2 : Polynomial.aeval (T 1 : k[T;T⁻¹]) f = Polynomial.toLaurent f := by
      rw [← Polynomial.toLaurent_X, ← Polynomial.coe_toLaurentAlg (R := k),
        Polynomial.aeval_algHom_apply, Polynomial.aeval_X_left_apply]
    rw [h2] at this
    exact Polynomial.toLaurent_injective (by rw [this, map_zero])
  obtain ⟨u, hu⟩ := (hJ (Polynomial k) Polynomial.X).2 fun f hf => by rw [h0 f hf, map_zero]
  exact Polynomial.not_isUnit_X (hu ▸ (isUnit_T 1).map u)

end May29

end

end Buffalo.AG.Part01
