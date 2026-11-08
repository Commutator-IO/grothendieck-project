import Buffalo.Topos.Part05d

/-!
# Problem three for all small limits: the counterexample `{2} → Set`

Problem three of the Buffalo lectures (video `4gynb9uTEE4`, 2:03:54 and 2:10:23) asks whether
`I → R` is basic exactly when condition (G) holds: every strictly full subcategory of `R`
containing the image of `I` and stable under `D`-limits is `R` itself. The companion
article on problem three (`docs/problem-three/article.tex`, §7, formerly Appendix B of the
open-problems article) shows that
for `D` all small limits the converse fails, with `{2} → Set`. The counterexample is the
edition's, not the lecturer's. This file checks its two concrete halves, with `Set = Type`.

What is proved.
* `equivEqualizer` (Proposition 7.1): every set `X` is in bijection with the equalizer of the two
  maps `f, g : 2^{P(X)} ⇉ 2^{P(P(X)) ⊔ P(X)}` of the article (`eqLeft`, `eqRight`), the
  complete Boolean homomorphisms `P(X) → 2`, through `x ↦ [x ∈ -]`.
* `saturation n` is the stage `Iₙ` of the saturation of `{2} → Set` under small limits (the
  repletion of `{2}`, then at each step the repletion of the previous stage together with the
  limits of small diagrams in it). `saturation_two`: `I₂` is everything. `not_saturation_one`:
  `Fin 3 ∉ I₁`, by `Buffalo.Topos.Part05.no_limit_of_bools` (no limit of copies of `2` has three
  elements). So exactly two steps are needed (Corollary 7.2).
* `conditionG`: condition (G) for `{2} → Set` and small limits. A property of types that is
  invariant under bijection, holds for `Bool` and is stable under limits of small diagrams holds
  for every type.
* `not_isCardinalPresentable`, `not_isPresentable` (Proposition 7.3): in `Setᵒᵖ` the object `2`
  is not `κ`-presentable for any regular `κ`, so not presentable. The `κ`-filtered diagram is the
  chain of tails `[α, κ)` of `κ.ord.ToType` in `Setᵒᵖ` (`tailChain`), whose colimit is the empty
  set (`tailCoconeIsColimit`); the constant maps to `true` and to `false` agree on the colimit and
  at no stage.

What is not formalised, and stays on paper.
* Proposition 7.4 and Theorem 7.5: an algebraic category, in the 2-category of cocomplete categories, has all its
  objects presentable. It rests on Kelly's sketches (Thms 5.56, 6.5, 6.11, 6.23 of his book) and
  on a coherence for chains argued there at the level of universal properties. Hence the conclusions « `Setᵒᵖ` is
  not algebraic » and « `{2} → Set` satisfies (G) without being basic » are not checked here.
* The notions « basic » and « algebraic » themselves, the hypothesis (H) (envelopes,
  localisations, adjunction of arrows in `Cat_D`), and the transfinite saturation of
  Proposition 2.4: only the finite stages are defined, which suffices since `I₂` is everything.
* The dual statement, (G) for `{2} → Setᵒᵖ` under colimits, which is (G) above read in `Setᵒᵖ`.
-/

open CategoryTheory Limits Opposite

namespace Buffalo.ProblemThree

noncomputable section

open scoped Classical

/-- The map `f` of Proposition 7.1: `u ↦ (S ↦ u (⋂₀ S), A ↦ u Aᶜ)`. -/
def eqLeft (X : Type) (u : Set X → Bool) : Set (Set X) ⊕ Set X → Bool
  | .inl S => u (⋂₀ S)
  | .inr A => u Aᶜ

/-- The map `g` of Proposition 7.1: `u ↦ (S ↦ ⋀_{A ∈ S} u A, A ↦ ¬ u A)`. -/
def eqRight (X : Type) (u : Set X → Bool) : Set (Set X) ⊕ Set X → Bool
  | .inl S => decide (∀ A ∈ S, u A = true)
  | .inr A => !u A

/-- Evaluation at a point, `u_x(A) = [x ∈ A]`, a complete Boolean homomorphism `P(X) → 2`. -/
def evalPoint (X : Type) (x : X) : {u : Set X → Bool // eqLeft X u = eqRight X u} :=
  ⟨fun A => decide (x ∈ A), by
    funext s
    rcases s with S | A
    · simp [eqLeft, eqRight]
    · simp [eqLeft, eqRight]⟩

/-- Every complete Boolean homomorphism `P(X) → 2` is evaluation at a unique point. -/
theorem evalPoint_bijective (X : Type) : Function.Bijective (evalPoint X) := by
  constructor
  · intro x y h
    have := congrFun (congrArg Subtype.val h) {x}
    exact (by simpa [evalPoint] using this : y = x).symm
  · rintro ⟨u, hu⟩
    have hS : ∀ S, u (⋂₀ S) = decide (∀ A ∈ S, u A = true) := fun S => congrFun hu (.inl S)
    have hC : ∀ A, u Aᶜ = !u A := fun A => congrFun hu (.inr A)
    have huniv : u Set.univ = true := by simpa using hS ∅
    have hempty : u ∅ = false := by simpa [huniv] using hC Set.univ
    have hF : u (⋂₀ {A | u A = true}) = true := by simpa using hS {A | u A = true}
    obtain ⟨x, hx⟩ : (⋂₀ {A | u A = true}).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro h
      rw [h, hempty] at hF
      exact Bool.false_ne_true hF
    refine ⟨x, Subtype.ext (funext fun A => ?_)⟩
    simp only [evalPoint]
    by_cases hA : u A = true
    · simp [hA, Set.mem_sInter.1 hx A hA]
    · have hxA : x ∈ Aᶜ := Set.mem_sInter.1 hx _ (by simpa [hC] using hA)
      simp only [hA, decide_eq_false_iff_not]
      exact hxA

/-- **Proposition 7.1.** Every set is an equalizer of two maps between powers of `2`. -/
def equivEqualizer (X : Type) : X ≃ {u : Set X → Bool // eqLeft X u = eqRight X u} :=
  Equiv.ofBijective _ (evalPoint_bijective X)

/-- One step of the saturation under small limits: the types in bijection with a type of `P`
or with the vertex of a limit cone over a small diagram of types of `P`. -/
def LimitStep (P : Type → Prop) (X : Type) : Prop :=
  P X ∨ ∃ (K : Type) (_ : SmallCategory K) (F : K ⥤ Type) (c : Cone F),
    (∀ k, P (F.obj k)) ∧ Nonempty (IsLimit c) ∧ Nonempty (X ≃ c.pt)

/-- The finite stages `I₀ ⊆ I₁ ⊆ ⋯` of the saturation of `{2} → Set` under small limits. -/
def saturation : ℕ → Type → Prop
  | 0 => fun X => Nonempty (X ≃ Bool)
  | n + 1 => LimitStep (saturation n)

/-- Every power `2^S` lies in `I₁`. -/
theorem saturation_one_pow (S : Type) : saturation 1 (S → Bool) := by
  refine .inr ⟨Discrete S, inferInstance, Discrete.functor fun _ => Bool,
    (Types.productLimitCone.{0, 0} fun _ : S => Bool).cone, fun _ => ⟨Equiv.refl _⟩,
    ⟨(Types.productLimitCone.{0, 0} fun _ : S => Bool).isLimit⟩, ⟨Equiv.refl _⟩⟩

/-- The saturation reaches every set in two steps: `I₂ = Set`. -/
theorem saturation_two (X : Type) : saturation 2 X := by
  let f : (Set X → Bool) ⟶ (Set (Set X) ⊕ Set X → Bool) := TypeCat.ofHom (eqLeft X)
  let g : (Set X → Bool) ⟶ (Set (Set X) ⊕ Set X → Bool) := TypeCat.ofHom (eqRight X)
  refine .inr ⟨WalkingParallelPair, inferInstance, parallelPair f g,
    (Types.equalizerLimit (g := f) (h := g)).cone, ?_,
    ⟨(Types.equalizerLimit (g := f) (h := g)).isLimit⟩, ⟨equivEqualizer X⟩⟩
  rintro (_ | _)
  · exact saturation_one_pow _
  · exact saturation_one_pow _

/-- One step does not suffice: a three-element set is not in `I₁`. -/
theorem not_saturation_one : ¬ saturation 1 (Fin 3) := by
  rintro (h | ⟨K, _, F, c, hF, ⟨hc⟩, ⟨e⟩⟩)
  · obtain ⟨e⟩ : Nonempty (Fin 3 ≃ Bool) := h
    simpa using Fintype.card_congr e
  · exact (Topos.Part05.no_limit_of_bools F (fun k => (hF k).some) hc).false e.symm

/-- Each stage of the saturation lies in every replete class containing `2` and closed under
small limits. -/
theorem saturation_le (P : Type → Prop) (hiso : ∀ {X Y : Type}, (X ≃ Y) → P X → P Y)
    (h2 : P Bool) (hlim : ∀ (K : Type) [SmallCategory K] (F : K ⥤ Type) (c : Cone F),
      IsLimit c → (∀ k, P (F.obj k)) → P c.pt) :
    ∀ (n : ℕ) (X : Type), saturation n X → P X
  | 0, _, ⟨e⟩ => hiso e.symm h2
  | n + 1, _, .inl h => saturation_le P hiso h2 hlim n _ h
  | n + 1, _, .inr ⟨K, _, F, c, hF, ⟨hc⟩, ⟨e⟩⟩ =>
    hiso e.symm (hlim K F c hc fun k => saturation_le P hiso h2 hlim n _ (hF k))

/-- **Condition (G)** for `{2} → Set` and `D` all small limits. -/
theorem conditionG (P : Type → Prop) (hiso : ∀ {X Y : Type}, (X ≃ Y) → P X → P Y)
    (h2 : P Bool) (hlim : ∀ (K : Type) [SmallCategory K] (F : K ⥤ Type) (c : Cone F),
      IsLimit c → (∀ k, P (F.obj k)) → P c.pt) (X : Type) : P X :=
  saturation_le P hiso h2 hlim 2 X (saturation_two X)

/-- The chain of tails `[α, κ)`, `α < κ`, as a `κ`-filtered diagram in `Setᵒᵖ`. -/
def tailChain (κ : Cardinal.{0}) : κ.ord.ToType ⥤ Typeᵒᵖ where
  obj α := op {β // α ≤ β}
  map {α α'} h := (TypeCat.ofHom fun β : {β // α' ≤ β} =>
    (⟨β.1, (leOfHom h).trans β.2⟩ : {β // α ≤ β})).op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A cone over the tails in `Set` has an empty vertex: a compatible choice of points of all the
tails would be a point of their intersection. -/
theorem isEmpty_cocone_pt (κ : Cardinal.{0}) [Fact κ.IsRegular] (s : Cocone (tailChain κ)) :
    IsEmpty s.pt.unop := by
  have := Cardinal.noMaxOrder (Fact.out : κ.IsRegular).aleph0_le
  have := Cardinal.nonempty_ord_toType (Fact.out : κ.IsRegular).pos.ne'
  refine ⟨fun y => ?_⟩
  let α₀ : κ.ord.ToType := Classical.arbitrary _
  let β₀ := (s.ι.app α₀).unop y
  obtain ⟨α₁, h₁⟩ := exists_gt β₀.1
  have hw := congrArg (fun m => m.unop y) (s.w (homOfLE (β₀.2.trans h₁.le)))
  have : ((s.ι.app α₁).unop y).1 = β₀.1 := congrArg Subtype.val hw
  exact absurd ((s.ι.app α₁).unop y).2 (by rw [this]; exact not_le.2 h₁)

/-- The empty set with its inclusions in the tails, as a cocone in `Setᵒᵖ`. -/
def tailCocone (κ : Cardinal.{0}) : Cocone (tailChain κ) where
  pt := op PEmpty
  ι := { app _ := (TypeCat.ofHom PEmpty.elim).op
         naturality _ _ _ := Quiver.Hom.unop_inj (by ext x; exact x.elim) }

/-- The tails have empty intersection: `∅` is their limit in `Set`. -/
def tailCoconeIsColimit (κ : Cardinal.{0}) [Fact κ.IsRegular] : IsColimit (tailCocone κ) where
  desc s := (TypeCat.ofHom fun y => (isEmpty_cocone_pt κ s).elim y).op
  fac s _ := Quiver.Hom.unop_inj (by ext y; exact (isEmpty_cocone_pt κ s).elim y)
  uniq s _ _ := Quiver.Hom.unop_inj (by ext y; exact (isEmpty_cocone_pt κ s).elim y)

/-- **Proposition 7.3.** In `Setᵒᵖ` the object `2` is not `κ`-presentable, for any regular `κ`. -/
theorem not_isCardinalPresentable (κ : Cardinal.{0}) [Fact κ.IsRegular] :
    ¬ IsCardinalPresentable (op Bool : Typeᵒᵖ) κ := by
  intro h
  have := Cardinal.nonempty_ord_toType (Fact.out : κ.IsRegular).pos.ne'
  let α₀ : κ.ord.ToType := Classical.arbitrary _
  let f₁ : op Bool ⟶ (tailChain κ).obj α₀ := (TypeCat.ofHom fun _ => true).op
  let f₂ : op Bool ⟶ (tailChain κ).obj α₀ := (TypeCat.ofHom fun _ => false).op
  obtain ⟨j, u, hu⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ (tailCoconeIsColimit κ)
    f₁ f₂ (Quiver.Hom.unop_inj (by ext x; exact x.elim))
  have := congrArg (fun m => m.unop ⟨j, le_rfl⟩) hu
  exact Bool.noConfusion this

/-- In `Setᵒᵖ` the object `2` is not presentable. -/
theorem not_isPresentable : ¬ IsPresentable.{0} (op Bool : Typeᵒᵖ) := by
  rintro ⟨κ, hκ, h⟩
  exact not_isCardinalPresentable κ h

end

end Buffalo.ProblemThree
