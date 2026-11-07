import Mathlib

/-!
# Buffalo, algebraic geometry, part 09 (a): 10 July 1973, from 4:22:15

The entries of `docs/buffalo-ag/index.tex` lines 1191–1218 (video `vuys5SNs2eQ`, 4:22:15–5:39:27):
effective descent for schemes, the radicial and the very ample cases, norms, the finite
extension principle, descent and group actions.

Conventions. mathlib has no category of descent data of schemes relative to `S' → S` and no
relative ampleness, so the statements on descent data are made *on points* (Grothendieck's own
reading, `X''(Z) ⊂ X'(Z) × X'(Z)`): a scheme over `S'` is replaced by a family of sets `X' s`
over the points `s` of a set `S'` mapping to `S`, and `S'' = S' ×_S S'` by the pairs `(s, t)` with
`π s = π t`. By Yoneda, the statements on points for every `Z` are the scheme statements.
-/

open CategoryTheory Limits AlgebraicGeometry Topology TensorProduct

universe u

namespace Buffalo.AG.Part09

noncomputable section

/-! ### Effective descent for schemes (on points) -/

section Points

variable {S S' : Type*} (π : S' → S) (X' : S' → Type*)

/-- A gluing datum on `X'` (on points): for `(s, t) ∈ S'' = S' ×_S S'` a bijection
`X'_s ≃ X'_t`, i.e. an isomorphism `p₁^* X' ≃ p₂^* X'` over `S''`. -/
abbrev GluingDatum := ∀ s t : S', π s = π t → X' s ≃ X' t

variable {π X'}

/-- The cocycle condition on `S''' = S' ×_S S' ×_S S'`: `φ_{tu} ∘ φ_{st} = φ_{su}`. -/
def GluingDatum.Cocycle (φ : GluingDatum π X') : Prop :=
  ∀ (s t u : S') (h₁ : π s = π t) (h₂ : π t = π u) (x : X' s),
    φ t u h₂ (φ s t h₁ x) = φ s u (h₁.trans h₂) x

/-- The relation `X'' ⇉ X'` defined by a gluing datum: `X'' = p₁^* X'`, with `q₁` the projection
and `q₂` the projection composed with `φ`; its image in `X' × X'`. -/
def GluingDatum.rel (φ : GluingDatum π X') (a b : Σ s, X' s) : Prop :=
  ∃ h : π a.1 = π b.1, φ a.1 b.1 h a.2 = b.2

lemma GluingDatum.Cocycle.self {φ : GluingDatum π X'} (hφ : φ.Cocycle) (s : S') (h : π s = π s)
    (x : X' s) : φ s s h x = x :=
  (φ s s h).injective (hφ s s s h h x)

/-- vuys5SNs2eQ-15735 (4:22:15) [prop] A gluing datum on `X'` is a descent datum (satisfies the
cocycle condition) if and only if `X'' ⇉ X'` is an equivalence relation (on points). -/
theorem prop_15735 (φ : GluingDatum π X') : Equivalence φ.rel ↔ φ.Cocycle := by
  constructor
  · intro hE s t u h₁ h₂ x
    obtain ⟨h, e⟩ := hE.trans (x := ⟨s, x⟩) (y := ⟨t, φ s t h₁ x⟩) (z := ⟨u, φ t u h₂ (φ s t h₁ x)⟩)
      ⟨h₁, rfl⟩ ⟨h₂, rfl⟩
    exact e.symm
  · intro hφ
    refine ⟨fun ⟨s, x⟩ => ⟨rfl, hφ.self s rfl x⟩, ?_, ?_⟩
    · rintro ⟨s, x⟩ ⟨t, y⟩ ⟨h, e⟩
      dsimp only at h e
      exact ⟨h.symm, by dsimp only; rw [← e, hφ s t s h h.symm x, hφ.self]⟩
    · rintro ⟨s, x⟩ ⟨t, y⟩ ⟨u, z⟩ ⟨h₁, e₁⟩ ⟨h₂, e₂⟩
      dsimp only at h₁ h₂ e₁ e₂
      exact ⟨h₁.trans h₂, by dsimp only; rw [← e₂, ← e₁, hφ s t u h₁ h₂ x]⟩

/-- The equivalence relation of a descent datum, as a setoid on `X' = Σ s, X' s`. -/
def GluingDatum.setoid {φ : GluingDatum π X'} (hφ : φ.Cocycle) : Setoid (Σ s, X' s) :=
  ⟨φ.rel, (prop_15735 φ).2 hφ⟩

/-- The quotient `X = X' / X''` and its map to `S`. -/
def GluingDatum.quotToBase {φ : GluingDatum π X'} (hφ : φ.Cocycle) :
    Quotient (GluingDatum.setoid hφ) → S :=
  Quotient.lift (fun a => π a.1) fun _ _ h => h.1

/-- vuys5SNs2eQ-16055 (4:27:35) [prop] (on points, where every equivalence relation is
universally effective) A descent datum is effective: the quotient `X = X'/X''` exists, `X'' =
X' ×_X X'`, and `X'` is recovered as `X ×_S S'` (fibre by fibre: `X'_s ≃ X_{π s}`). -/
theorem prop_16055 {φ : GluingDatum π X'} (hφ : φ.Cocycle) :
    (∀ a b, (Quotient.mk (GluingDatum.setoid hφ) a = Quotient.mk _ b ↔ φ.rel a b)) ∧
      ∀ s : S', Function.Bijective (fun x : X' s =>
        (⟨Quotient.mk (GluingDatum.setoid hφ) ⟨s, x⟩, rfl⟩ :
          {q // GluingDatum.quotToBase hφ q = π s})) := by
  refine ⟨fun a b => Quotient.eq, fun s => ⟨fun x y hxy => ?_, ?_⟩⟩
  · obtain ⟨h, e⟩ := Quotient.eq.1 (congrArg Subtype.val hxy)
    rwa [hφ.self] at e
  · rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | h a =>
      obtain ⟨t, y⟩ := a
      refine ⟨φ t s hq y, Subtype.ext (Quotient.sound ⟨hq.symm, ?_⟩)⟩
      change φ s t hq.symm (φ t s hq y) = y
      rw [hφ t s t hq hq.symm y, hφ.self]

/-- vuys5SNs2eQ-16510 (4:35:10) [prop] A subset `U` of `X'` is stable under the descent datum
(saturated for `X''`) if and only if it has the same inverse image under `q₁` and `q₂`. -/
theorem prop_16510 (φ : GluingDatum π X') (U : Set (Σ s, X' s)) :
    ((fun r : {p : (Σ s, X' s) × (Σ s, X' s) // φ.rel p.1 p.2} => r.1.1) ⁻¹' U =
        (fun r : {p : (Σ s, X' s) × (Σ s, X' s) // φ.rel p.1 p.2} => r.1.2) ⁻¹' U) ↔
      ∀ a b, φ.rel a b → (a ∈ U ↔ b ∈ U) := by
  constructor
  · intro h a b hab
    exact Set.ext_iff.1 h ⟨(a, b), hab⟩
  · intro h
    ext r
    exact h _ _ r.2

end Points

/-! ### Cases where descent data are effective -/

section Radicial

/-- vuys5SNs2eQ-17754 (4:55:54) [prop] A faithfully flat, quasi-compact and radicial (universally
injective) morphism is a homeomorphism; these hypotheses being stable under base change, it is a
universal homeomorphism (`prop_17754_universal`). -/
theorem prop_17754 {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f] [Surjective f]
    [UniversallyInjective f] : IsHomeomorph f.base := by
  have hq : IsQuotientMap f := Flat.isQuotientMap_of_surjective f
  refine ⟨f.continuous, fun U hU => ?_, f.injective, f.surjective⟩
  rw [← hq.isOpen_preimage, Set.preimage_image_eq _ f.injective]
  exact hU

/-- vuys5SNs2eQ-17754 (4:55:54) [prop] (universality) every base change of a faithfully flat
quasi-compact radicial morphism is a homeomorphism. -/
theorem prop_17754_universal {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f]
    [Surjective f] [UniversallyInjective f] (g : Y' ⟶ Y) :
    IsHomeomorph (pullback.snd f g).base := by
  have : UniversallyInjective (pullback.snd f g) :=
    UniversallyInjective.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f g) inferInstance
  exact prop_17754 _

/-- vuys5SNs2eQ-18155 (5:02:35) [prop] (the case `X' = S'`) If `g : S' → S` is radicial, the two
projections `S'' = S' ×_S S' ⇉ S'` agree on underlying points, so every subset is stable. -/
theorem prop_18155 {S S' : Scheme.{u}} (g : S' ⟶ S) [UniversallyInjective g]
    (z : ↥(pullback g g)) : pullback.fst g g z = pullback.snd g g z := by
  obtain ⟨t, rfl⟩ := ((UniversallyInjective.iff_diagonal g).1 inferInstance).surj z
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.diagonal_fst,
    pullback.diagonal_snd]

end Radicial

section VeryAmple

/-- vuys5SNs2eQ-18554 (5:09:14) [prop] (affine case) Direct image commutes with base change: for
`A → B`, a `B`-module `N` and `A → A'`, the base change `N ⊗_B (B ⊗_A A')` of `N` to
`X' = Spec (B ⊗_A A')`, viewed over `A`, is `N ⊗_A A'`, the base change of `f_* N`. -/
def prop_18554 (A B A' N : Type*) [CommRing A] [CommRing B] [CommRing A'] [Algebra A B]
    [Algebra A A'] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] :
    N ⊗[B] (B ⊗[A] A') ≃ₗ[B] N ⊗[A] A' :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange A B B N A'

/-- vuys5SNs2eQ-19389 (5:23:09) [prop] For `B` free of finite rank over `A`, the norm
`N(x) = det(x ·)` is multiplicative, `N(1) = 1`, and sends units to units (whence the norm of
an invertible sheaf, a torsor under `B^*`, to a torsor under `A^*`). -/
theorem prop_19389 (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (x y : B) :
    Algebra.norm A x = LinearMap.det (Algebra.lmul A B x) ∧
      Algebra.norm A (x * y) = Algebra.norm A x * Algebra.norm A y ∧ Algebra.norm A (1 : B) = 1 ∧
      (IsUnit x → IsUnit (Algebra.norm A x)) :=
  ⟨Algebra.norm_apply A x, map_mul _ x y, map_one _, fun h => h.map _⟩

end VeryAmple

/-! ### Descent and group actions (on points) -/

section Actions

variable {S S' X' G : Type*} (π : S' → S) (f : X' → S')

/-- A gluing datum on `X' → S'` (on points), as the relation `X'' ⊂ X' × X'`: it lies over
`S''`, and for every `x` over `s` and every `t` with `(s, t) ∈ S''` there is exactly one `y` over
`t` related to `x` (the bijection `X'_s ≃ X'_t`). -/
def IsGluing (R : X' → X' → Prop) : Prop :=
  (∀ x y, R x y → π (f x) = π (f y)) ∧ ∀ x t, π (f x) = π t → ∃! y, f y = t ∧ R x y

/-- vuys5SNs2eQ-20176 (5:36:16) [prop] (on points) Let `G` act on `S'` so that `S' × G ≃ S' ×_S S'`,
`(s, g) ↦ (s, g s)` (a pseudo-torsor). A gluing datum `R` on `X'` is a descent datum (an
equivalence relation) if and only if it is the orbit relation of an action of `G` on `X'`
compatible with the projection to `S'`. -/
theorem prop_20176 [Group G] [MulAction G S']
    (htors : ∀ s t, π s = π t ↔ ∃ g : G, g • s = t)
    (R : X' → X' → Prop) (hR : IsGluing π f R) :
    Equivalence R ↔ ∃ a : G → X' → X', (∀ x, a 1 x = x) ∧ (∀ g h x, a (g * h) x = a g (a h x)) ∧
      (∀ g x, f (a g x) = g • f x) ∧ ∀ x y, R x y ↔ ∃ g, y = a g x := by
  constructor
  · intro hE
    have hex : ∀ (g : G) (x : X'), ∃! y, f y = g • f x ∧ R x y :=
      fun g x => hR.2 x _ ((htors _ _).2 ⟨g, rfl⟩)
    choose a ha hau using hex
    have huniq : ∀ g x y, f y = g • f x → R x y → y = a g x := fun g x y h1 h2 =>
      hau g x y ⟨h1, h2⟩
    refine ⟨a, fun x => (huniq 1 x x (by rw [one_smul]) (hE.refl x)).symm, fun g h x => ?_,
      fun g x => (ha g x).1, fun x y => ⟨fun hxy => ?_, ?_⟩⟩
    · refine (huniq _ _ _ ?_ (hE.trans (ha h x).2 (ha g (a h x)).2)).symm
      rw [(ha g _).1, (ha h x).1, mul_smul]
    · obtain ⟨g, hg⟩ := (htors _ _).1 (hR.1 x y hxy)
      exact ⟨g, huniq g x y hg.symm hxy⟩
    · rintro ⟨g, rfl⟩
      exact (ha g x).2
  · rintro ⟨a, h1, hmul, -, hRa⟩
    refine ⟨fun x => (hRa x x).2 ⟨1, (h1 x).symm⟩, fun {x y} hxy => ?_, fun {x y z} hxy hyz => ?_⟩
    · obtain ⟨g, rfl⟩ := (hRa x _).1 hxy
      exact (hRa _ _).2 ⟨g⁻¹, by rw [← hmul, inv_mul_cancel, h1]⟩
    · obtain ⟨g, rfl⟩ := (hRa x _).1 hxy
      obtain ⟨g', rfl⟩ := (hRa _ _).1 hyz
      exact (hRa _ _).2 ⟨g' * g, (hmul _ _ _).symm⟩

end Actions

/-! ### Galois descent (affine level) -/

section Galois

/-- vuys5SNs2eQ-20367 (5:39:27) [prop] (the case `X = Spec k`, `Y = 𝔸¹`, for `S' → S` the
spectrum of a Galois extension, of descent of rank 1) Full faithfulness on points: the
`k`-points of the affine line are its `Γ`-invariant `k'`-points, `k = k'^Γ`. -/
theorem prop_20367 (k k' : Type*) [Field k] [Field k'] [Algebra k k'] [IsGalois k k'] (x : k') :
    x ∈ Set.range (algebraMap k k') ↔ ∀ σ : k' ≃ₐ[k] k', σ x = x :=
  InfiniteGalois.mem_range_algebraMap_iff_fixed x

end Galois

end

end Buffalo.AG.Part09
