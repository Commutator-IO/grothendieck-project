import Mathlib

/-!
# Folder 120, pages 20–23: collapsing a tame subset over a field

The modernised reading `transcripts/120/120.modern.tex` (« Topologie modérée », dated by the
inventory « à partir de 1973 — à partir de 1978 ») sets up, for a set `R`, families
`𝓜_I ⊂ 𝔓(R^I)` of *tame* subsets indexed by the finite sets `I`, subject to (M′1)–(M′4):
stability by `u^* : R^J → R^I`, `x ↦ x ∘ u` (direct images, preimages for `u` surjective,
cuts `A ∩ (u^*)⁻¹ B`), and products. A map is tame when its graph is a tame subset; a *tame
function* on `X ∈ 𝓜_I` is a map `X → R` whose graph lies in `𝓜_{I ⊔ 1}`; the tame points
`R₀` are the `c` with `{c} ∈ 𝓜_1`. Axiom (M6) asks that a tame `Y ⊂ X` be a fibre
`⋂ f_α⁻¹(e_α)`, `e_α ∈ R₀`, of finitely many tame functions, « and one may assume that the
`f_α` separate the points of `X ∖ Y` », which says that `X/Y` exists in the strict sense.
Section (VI) supposes `R` a field with (M11): `0, 1` tame points, `x - y` and `xy` tame on
every `A ∈ 𝓜₂`, tame sets of inverses. It states:

> **Proposition (page 23).** Under (M1)–(M7) and (M11), every tame subset `Y` of a tame space
> `X` which is the common zero set of finitely many tame functions is also that of a finite
> family of tame functions separating the points of `X ∖ Y`; that is, `X/Y` is a tame space.

The proof (pages 22–23): translate to `e_α = 0`, take tame `g_β` embedding `X`, and use the
`f_α` and the `f_α g_β`; for `x ≠ y` off `Y` not separated by the `f_α`, some
`λ = f_α(x) ≠ 0` and some `g_β(x) ≠ g_β(y)` give `λ g_β(x) ≠ λ g_β(y)`.
This is finding `120-collapse-separation-over-a-field` of `src/content/findings.ts`.

What is formalised. The axioms are those of the reading in the form (M′1)–(M′4) it uses
(`TameModel`, index types finite), (M11) b) as `RingOps`, (M11) in full as `M11` for a field.

* `TameModel.isTameFun_mul`, `isTameFun_sub`, `isTameFun_const`, `isTameFun_coord`: the tame
  functions on a tame `X` are stable by `-` and `·`, contain the constants of `R₀` and the
  coordinates. Only (M′1), (M′2), (M′4) and (M11) b) are used.
* `separates_off_zeroSet` (any commutative ring without zero divisors, any set `X`, no
  finiteness): the family `f_α`, `f_α g_β` has the zero set of the `f_α` and separates the
  points off it as soon as the `g_β` separate points. `not_separates_zmod4`: with zero
  divisors it fails (`ℤ/4`, `f = 2`, `g = id`).
* `collapse_separation` (page 23 with the translation of page 22): for `X ∈ 𝓜_I`, tame `f_α`,
  `e_α ∈ R₀`, tame `g_β` injective on `X`, the functions `f_α - e_α` and `(f_α - e_α) g_β`
  are tame, vanish together exactly on `Y = ⋂ f_α⁻¹(e_α)`, and separate the points of
  `X ∖ Y`. `exists_separating_family` and `exists_separating_family_of_field` state the
  Proposition as an existence, the second under (M11) for a field.

The statement holds, more generally: neither (M3), (M5)–(M7), (M11) a), c), nor the
finiteness of the families is used, and « field » can be weakened to « no zero divisors ».
The reading's corrections `e_α ∈ R₀` (page 22) and `X ∖ Y` (page 23) are both needed: the
first for the translation, the second because a family constant on `Y` cannot separate two
points of `Y`.
-/

namespace Grothendieck.Folder120

open Function

universe u

/-- The axioms (M′1)–(M′4) of page 2 (with (M′) for finite index sets, page 4): a family
`M I ⊂ 𝔓(R^I)` of tame subsets, `u^* x = x ∘ u`. -/
structure TameModel (R : Type u) where
  /-- The tame subsets of `R^I`. -/
  M : (I : Type) → Set (Set (I → R))
  /-- (M′1) direct image by `u^*`. -/
  m1 : ∀ {I J : Type} [Finite I] [Finite J] (u : I → J) {A : Set (J → R)},
    A ∈ M J → (fun x : J → R => x ∘ u) '' A ∈ M I
  /-- (M′2) preimage by `u^*` for `u` surjective. -/
  m2 : ∀ {I J : Type} [Finite I] [Finite J] (u : I → J), Surjective u →
    ∀ {B : Set (I → R)}, B ∈ M I → (fun x : J → R => x ∘ u) ⁻¹' B ∈ M J
  /-- (M′3) cut of a tame subset by a preimage. -/
  m3 : ∀ {I J : Type} [Finite I] [Finite J] (u : I → J) {A : Set (J → R)}
    {B : Set (I → R)}, A ∈ M J → B ∈ M I → (fun x : J → R => x ∘ u) ⁻¹' B ∩ A ∈ M J
  /-- (M′4) products, `R^I × R^J = R^{I ⊔ J}`. -/
  m4 : ∀ {I J : Type} [Finite I] [Finite J] {A : Set (I → R)} {B : Set (J → R)},
    A ∈ M I → B ∈ M J → {x : I ⊕ J → R | x ∘ Sum.inl ∈ A ∧ x ∘ Sum.inr ∈ B} ∈ M (I ⊕ J)

/-- The graph over `X ⊂ R^I` of a family `F : R^I → R^K`, a subset of `R^{I ⊔ K}`. -/
def graphOn {R : Type u} {I K : Type} (X : Set (I → R)) (F : (I → R) → K → R) :
    Set (I ⊕ K → R) :=
  {y | y ∘ Sum.inl ∈ X ∧ ∀ k, y (Sum.inr k) = F (y ∘ Sum.inl) k}

namespace TameModel

variable {R : Type u} (T : TameModel R)

/-- A tame function on `X`: its graph over `X` is a tame subset of `R^{I ⊔ 1}`. -/
def IsTameFun {I : Type} (X : Set (I → R)) (f : (I → R) → R) : Prop :=
  graphOn X (fun x (_ : Unit) => f x) ∈ T.M (I ⊕ Unit)

/-- The tame points `R₀ = {c | {c} ∈ 𝓜₁}`. -/
def R0 : Set R := {c | {fun _ : Unit => c} ∈ T.M Unit}

/-- (M11) b) (page 20): `x - y` and `xy` are tame on every tame `A ⊂ R²`. -/
def RingOps [CommRing R] : Prop :=
  ∀ A ∈ T.M (Fin 2), T.IsTameFun A (fun z => z 0 - z 1) ∧ T.IsTameFun A (fun z => z 0 * z 1)

/-- (M11) in full, for a field (page 20): `0` and `1` tame points, b), and a tame set
containing the inverses of a tame `A ⊂ R^*`. -/
structure M11 [Field R] : Prop where
  zero_mem : (0 : R) ∈ T.R0
  one_mem : (1 : R) ∈ T.R0
  ringOps : T.RingOps
  inv : ∀ A ∈ T.M Unit, (∀ x ∈ A, x () ≠ 0) →
    ∃ B ∈ T.M Unit, ∀ x ∈ A, (fun _ => (x ())⁻¹) ∈ B

/-- The joint graph of two tame functions is tame ((M′2) and (M′4)). -/
theorem graphOn_pair_mem {I : Type} [Finite I] {X : Set (I → R)} {f g : (I → R) → R}
    (hf : T.IsTameFun X f) (hg : T.IsTameFun X g) :
    graphOn X (fun x => ![f x, g x]) ∈ T.M (I ⊕ Fin 2) := by
  let w : (I ⊕ Unit) ⊕ (I ⊕ Unit) → I ⊕ Fin 2 := fun
    | .inl (.inl i) => .inl i
    | .inl (.inr _) => .inr 0
    | .inr (.inl i) => .inl i
    | .inr (.inr _) => .inr 1
  have hw : Surjective w := by
    rintro (i | k)
    · exact ⟨.inl (.inl i), rfl⟩
    · fin_cases k
      · exact ⟨.inl (.inr ()), rfl⟩
      · exact ⟨.inr (.inr ()), rfl⟩
  have := T.m2 w hw (T.m4 hf hg)
  convert this using 1
  ext y
  constructor
  · rintro ⟨hX, hk⟩
    exact ⟨⟨hX, fun _ => hk 0⟩, hX, fun _ => hk 1⟩
  · rintro ⟨⟨hX, h0⟩, -, h1⟩
    refine ⟨hX, fun k => ?_⟩
    fin_cases k
    · exact h0 ()
    · exact h1 ()

/-- The image `F(X)` of `X` by a family with tame graph is tame ((M′1)). -/
theorem image_mem {I K : Type} [Finite I] [Finite K] {X : Set (I → R)}
    {F : (I → R) → K → R} (hF : graphOn X F ∈ T.M (I ⊕ K)) : F '' X ∈ T.M K := by
  convert T.m1 Sum.inr hF using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Sum.elim x (F x), ⟨hx, fun _ => rfl⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hk⟩, rfl⟩
    exact ⟨y ∘ Sum.inl, hy, funext fun k => (hk k).symm⟩

/-- Composition: a tame function of a family with tame graph is tame ((M′1), (M′2),
(M′4)). -/
theorem isTameFun_comp {I K : Type} [Finite I] [Finite K] {X : Set (I → R)}
    {F : (I → R) → K → R} (hF : graphOn X F ∈ T.M (I ⊕ K)) {h : (K → R) → R}
    (hh : T.IsTameFun (F '' X) h) : T.IsTameFun X (fun x => h (F x)) := by
  let w : (I ⊕ K) ⊕ (K ⊕ Unit) → (I ⊕ K) ⊕ Unit := fun
    | .inl p => .inl p
    | .inr (.inl k) => .inl (.inr k)
    | .inr (.inr _) => .inr ()
  have hw : Surjective w := by
    rintro (p | _)
    · exact ⟨.inl p, rfl⟩
    · exact ⟨.inr (.inr ()), rfl⟩
  let v : I ⊕ Unit → (I ⊕ K) ⊕ Unit := fun
    | .inl i => .inl (.inl i)
    | .inr _ => .inr ()
  have := T.m1 v (T.m2 w hw (T.m4 hF hh))
  unfold IsTameFun
  convert this using 1
  ext z
  simp only [graphOn, Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨hz, hk⟩
    refine ⟨Sum.elim (Sum.elim (z ∘ Sum.inl) (F (z ∘ Sum.inl))) (fun _ => z (.inr ())),
      ⟨⟨hz, fun _ => rfl⟩, ⟨_, hz, rfl⟩, fun _ => hk ()⟩, ?_⟩
    funext i
    rcases i with i | _ <;> rfl
  · rintro ⟨y, ⟨⟨hy, hyk⟩, -, hyh⟩, rfl⟩
    refine ⟨hy, fun _ => ?_⟩
    have hF' : (fun k => y (.inl (.inr k))) = F (fun i => y (.inl (.inl i))) :=
      funext hyk
    have := hyh ()
    simp only [comp_apply] at this ⊢
    rw [this]
    exact congrArg h hF'

/-- The tame functions are stable by product (page 20). -/
theorem isTameFun_mul [CommRing R] (h11 : T.RingOps) {I : Type} [Finite I]
    {X : Set (I → R)} {f g : (I → R) → R} (hf : T.IsTameFun X f) (hg : T.IsTameFun X g) :
    T.IsTameFun X (fun x => f x * g x) := by
  have hP := T.graphOn_pair_mem hf hg
  simpa using T.isTameFun_comp hP (h11 _ (T.image_mem hP)).2

/-- The tame functions are stable by difference (page 20). -/
theorem isTameFun_sub [CommRing R] (h11 : T.RingOps) {I : Type} [Finite I]
    {X : Set (I → R)} {f g : (I → R) → R} (hf : T.IsTameFun X f) (hg : T.IsTameFun X g) :
    T.IsTameFun X (fun x => f x - g x) := by
  have hP := T.graphOn_pair_mem hf hg
  simpa using T.isTameFun_comp hP (h11 _ (T.image_mem hP)).1

/-- A constant `c ∈ R₀` is a tame function on a tame `X` ((M′4)): its graph is `X × {c}`. -/
theorem isTameFun_const {I : Type} [Finite I] {X : Set (I → R)} (hX : X ∈ T.M I) {c : R}
    (hc : c ∈ T.R0) : T.IsTameFun X (fun _ => c) := by
  unfold IsTameFun
  convert T.m4 hX hc using 1
  ext y
  simp only [graphOn, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact and_congr_right fun _ => ⟨fun h => funext h, fun h k => congrFun h k⟩

/-- The coordinates are tame functions on a tame `X` ((M′1)). -/
theorem isTameFun_coord {I : Type} [Finite I] {X : Set (I → R)} (hX : X ∈ T.M I) (i : I) :
    T.IsTameFun X (fun x => x i) := by
  unfold IsTameFun
  have := T.m1 (Sum.elim id fun _ => i : I ⊕ Unit → I) hX
  convert this using 1
  ext y
  simp only [graphOn, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hy, hk⟩
    refine ⟨y ∘ Sum.inl, hy, funext fun j => ?_⟩
    rcases j with j | _
    · rfl
    · exact (hk ()).symm
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, fun _ => rfl⟩

end TameModel

/-- The family of page 22: the `f_α` and the products `f_α g_β`. -/
def collapseFamily {R X A B : Type*} [Mul R] (f : A → X → R) (g : B → X → R) :
    A ⊕ A × B → X → R :=
  Sum.elim f fun p x => f p.1 x * g p.2 x

/-- The family has the common zero set of the `f_α`. -/
theorem collapseFamily_eq_zero_iff {R X A B : Type*} [MulZeroClass R] (f : A → X → R)
    (g : B → X → R) (x : X) : (∀ c, collapseFamily f g c x = 0) ↔ ∀ a, f a x = 0 := by
  refine ⟨fun h a => h (.inl a), fun h c => ?_⟩
  rcases c with a | ⟨a, b⟩
  · exact h a
  · simp [collapseFamily, h a]

/-- Pages 22–23, the argument: if `x` is off the zero set of the `f_α` and some `g_β`
separates `x` and `y`, the `f_α` and `f_α g_β` separate `x` and `y`. Any ring without zero
divisors, any set. -/
theorem separates_off_zeroSet {R X A B : Type*} [Ring R] [NoZeroDivisors R] (f : A → X → R)
    (g : B → X → R) {x y : X} (hx : ∃ a, f a x ≠ 0) (hg : ∃ b, g b x ≠ g b y) :
    ∃ c, collapseFamily f g c x ≠ collapseFamily f g c y := by
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hg
  have h1 : f a x = f a y := h (.inl a)
  have h2 : f a x * g b x = f a y * g b y := h (.inr (a, b))
  rw [← h1] at h2
  exact hb (mul_left_cancel₀ ha h2)

/-- Zero divisors break the argument: over `ℤ/4`, `f = 2` and `g = id`, the family `2, 2x`
does not separate `0` and `2`, though `f(0) ≠ 0` and `g(0) ≠ g(2)`. -/
theorem not_separates_zmod4 :
    ¬ ∃ c, collapseFamily (fun (_ : Unit) (_ : ZMod 4) => (2 : ZMod 4))
      (fun (_ : Unit) (x : ZMod 4) => x) c 0 ≠
      collapseFamily (fun (_ : Unit) (_ : ZMod 4) => (2 : ZMod 4))
      (fun (_ : Unit) (x : ZMod 4) => x) c 2 := by
  decide

namespace TameModel

variable {R : Type u} (T : TameModel R)

/-- **Proposition (page 23)**, with the translation of page 22: for tame `f_α`, tame points
`e_α`, and tame `g_β` embedding `X`, the functions `f_α - e_α` and `(f_α - e_α) g_β` are tame,
vanish together exactly on `Y = ⋂ f_α⁻¹(e_α)`, and separate the points of `X ∖ Y`. -/
theorem collapse_separation [CommRing R] [NoZeroDivisors R] (h11 : T.RingOps) {I : Type}
    [Finite I] {X : Set (I → R)} (hX : X ∈ T.M I) {A B : Type} (f : A → (I → R) → R)
    (hf : ∀ a, T.IsTameFun X (f a)) (e : A → R) (he : ∀ a, e a ∈ T.R0)
    (g : B → (I → R) → R) (hg : ∀ b, T.IsTameFun X (g b))
    (hinj : Set.InjOn (fun x b => g b x) X) :
    (∀ c, T.IsTameFun X (collapseFamily (fun a x => f a x - e a) g c)) ∧
    (∀ x, (∀ c, collapseFamily (fun a x => f a x - e a) g c x = 0) ↔ ∀ a, f a x = e a) ∧
    ∀ x ∈ X, ∀ y ∈ X, (∃ a, f a x ≠ e a) → x ≠ y →
      ∃ c, collapseFamily (fun a x => f a x - e a) g c x ≠
        collapseFamily (fun a x => f a x - e a) g c y := by
  have hf' : ∀ a, T.IsTameFun X (fun x => f a x - e a) := fun a =>
    T.isTameFun_sub h11 (hf a) (T.isTameFun_const hX (he a))
  refine ⟨?_, fun x => ?_, fun x hx y hy hxy hne => ?_⟩
  · rintro (a | ⟨a, b⟩)
    · exact hf' a
    · exact T.isTameFun_mul h11 (hf' a) (hg b)
  · rw [collapseFamily_eq_zero_iff]
    exact forall_congr' fun a => sub_eq_zero
  · refine separates_off_zeroSet _ g ?_ ?_
    · obtain ⟨a, ha⟩ := hxy
      exact ⟨a, sub_ne_zero.mpr ha⟩
    · by_contra h
      push Not at h
      exact hne (hinj hx hy (funext h))

/-- **Proposition (page 23)** as an existence: a tame `Y = ⋂ f_α⁻¹(e_α)` of a tame `X` is the
common zero set of a finite family of tame functions separating the points of `X ∖ Y`
(the coordinates serve as the `g_β`). -/
theorem exists_separating_family [CommRing R] [NoZeroDivisors R] (h11 : T.RingOps)
    {I : Type} [Finite I] {X : Set (I → R)} (hX : X ∈ T.M I) {A : Type} [Finite A]
    (f : A → (I → R) → R) (hf : ∀ a, T.IsTameFun X (f a)) (e : A → R)
    (he : ∀ a, e a ∈ T.R0) :
    ∃ (C : Type) (_ : Finite C) (h : C → (I → R) → R), (∀ c, T.IsTameFun X (h c)) ∧
      (∀ x, (∀ c, h c x = 0) ↔ ∀ a, f a x = e a) ∧
      ∀ x ∈ X, ∀ y ∈ X, (∃ a, f a x ≠ e a) → x ≠ y → ∃ c, h c x ≠ h c y :=
  ⟨A ⊕ A × I, inferInstance, _, T.collapse_separation h11 hX f hf e he (fun i x => x i)
    (T.isTameFun_coord hX) fun _ _ _ _ h => h⟩

/-- The Proposition under (M11) for a field, as the page states it. -/
theorem exists_separating_family_of_field [Field R] (h11 : T.M11) {I : Type} [Finite I]
    {X : Set (I → R)} (hX : X ∈ T.M I) {A : Type} [Finite A] (f : A → (I → R) → R)
    (hf : ∀ a, T.IsTameFun X (f a)) (e : A → R) (he : ∀ a, e a ∈ T.R0) :
    ∃ (C : Type) (_ : Finite C) (h : C → (I → R) → R), (∀ c, T.IsTameFun X (h c)) ∧
      (∀ x, (∀ c, h c x = 0) ↔ ∀ a, f a x = e a) ∧
      ∀ x ∈ X, ∀ y ∈ X, (∃ a, f a x ≠ e a) → x ≠ y → ∃ c, h c x ≠ h c y :=
  T.exists_separating_family h11.ringOps hX f hf e he

end TameModel

/-- Page 23's « sépare les points de X » cannot be meant literally: a family vanishing on
`Y` does not separate two distinct points of `Y`. -/
theorem not_separates_on_zeroSet {R X C : Type*} [Zero R] (h : C → X → R) {x y : X}
    (hx : ∀ c, h c x = 0) (hy : ∀ c, h c y = 0) : ∀ c, h c x = h c y := fun c => by
  rw [hx, hy]

end Grothendieck.Folder120
