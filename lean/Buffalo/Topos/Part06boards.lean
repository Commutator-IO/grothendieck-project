import Buffalo.Topos.Part06c

/-!
# Buffalo, topos theory, part 6: the blackboards

Lean support for the checked items of the reconstructed blackboards `4gynb9uTEE4-12717/16589/
20493/24404` and `ORG14LNb5gE-0000` in the time range of part 6 that no index entry covers, and for
the corrections made to them. Status table: `docs/buffalo-topos/lean/Part06-boards.json`.
-/

universe u

open CategoryTheory Limits Opposite Cardinal

namespace Buffalo.Topos.Part06

noncomputable section

/-- Board `4gynb9uTEE4-12717`, t = 16360: `X = colim X_j ⇒ Hom(X, -) = lim_j Hom(X_j, -)`
(a map out of a colimit is a cocone; Mathlib). -/
def colimit_hom_equiv {J E : Type*} [Category* J] [Category* E] {F : J ⥤ E} {c : Cocone F}
    (hc : IsColimit c) (W : E) : (c.pt ⟶ W) ≃ (F ⟶ (Functor.const J).obj W) :=
  hc.homEquiv

/-- The final segments `{β ≥ α}` of the well-order `κ`, a `κ`-cofiltered system of nonempty
sets. -/
@[simps]
def finalSegments (κ : Cardinal.{u}) : κ.ord.ToTypeᵒᵖ ⥤ Type u where
  obj α := {β : κ.ord.ToType // α.unop ≤ β}
  map {α α'} h := ↾fun β => ⟨β.1, le_trans (leOfHom h.unop) β.2⟩

/-- A compatible family of points of the final segments cannot exist (`κ` infinite). -/
theorem finalSegments_no_section (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (s : Cone (finalSegments κ))
    (x : s.pt) : False := by
  have : NoMaxOrder κ.ord.ToType := Cardinal.noMaxOrder hκ
  have : Nonempty κ.ord.ToType := ⟨(Classical.arbitrary (Option κ.ord.ToType)).getD
    (Classical.choice (by
      rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_toType, Cardinal.card_ord]
      exact (Cardinal.aleph0_pos.trans_le hκ).ne'))⟩
  let a := Classical.arbitrary κ.ord.ToType
  let b := fun α : κ.ord.ToType => (s.π.app (op α) x).1
  have hb : ∀ α, b α = b a := fun α => by
    obtain ⟨γ, hγ1, hγ2⟩ := directed_of (· ≤ ·) α a
    have e1 := congrArg Subtype.val (ConcreteCategory.congr_hom (s.w (homOfLE hγ1).op) x)
    have e2 := congrArg Subtype.val (ConcreteCategory.congr_hom (s.w (homOfLE hγ2).op) x)
    exact e1.symm.trans e2
  obtain ⟨β, hβ⟩ := exists_gt (b a)
  have := (s.π.app (op β) x).2
  change β ≤ b β at this
  rw [hb β] at this
  exact not_le.2 hβ this

/-- The cone with point `∅`. -/
def emptyCone (κ : Cardinal.{u}) : Cone (finalSegments κ) where
  pt := PEmpty
  π := { app := fun _ => ↾fun x => x.elim
         naturality := fun _ _ _ => by ext x; exact x.elim }

/-- Their limit is empty: the cone with point `∅` is a limit cone. -/
def finalSegmentsIsLimit (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) : IsLimit (emptyCone κ) where
  lift s := ↾fun x => (finalSegments_no_section κ hκ s x).elim
  fac s j := by ext x; exact (finalSegments_no_section κ hκ s x).elim
  uniq s m _ := by ext x; exact (finalSegments_no_section κ hκ s x).elim

/-- Board `4gynb9uTEE4-16589`, t = 16845 (corrected `|X| ≤ 1` to `|X| = 1`): the empty set is not
an accessible object of `Set^op` (a `κ`-cofiltered limit of nonempty sets can be empty) ... -/
theorem not_isCardinalPresentable_op_empty (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    ¬ IsCardinalPresentable (op (PEmpty : Type u)) κ := by
  intro hX
  have hκ : ℵ₀ ≤ κ := (Fact.out : κ.IsRegular).aleph0_le
  have hc := (finalSegmentsIsLimit κ hκ).op
  have : IsCardinalFiltered κ.ord.ToTypeᵒᵖᵒᵖ κ :=
    IsCardinalFiltered.of_equivalence κ (opOpEquivalence _).symm
  obtain ⟨α, g, -⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hc (X := op PEmpty) (𝟙 _)
  exact (g.unop ⟨α.unop.unop, le_rfl⟩).elim

/-- The constant functor `Set^op → Set` with value a point is accessible. -/
theorem const_punit_isCardinalAccessible (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    ((Functor.const (Type u)ᵒᵖ).obj PUnit.{u + 1}).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ :=
    { preservesColimit {F} :=
        { preserves {c} hc := ⟨by
            have h := isFiltered_of_isCardinalFiltered J κ
            have (j : J) : IsIso ((((Functor.const _).obj PUnit.{u + 1}).mapCocone c).ι.app j) := by
              dsimp
              infer_instance
            exact Functor.IsEventuallyConstantFrom.isColimitOfIsIso
              (i₀ := h.nonempty.some) (fun _ _ ↦ by dsimp; infer_instance) _⟩ } }

/-- ... while a one-point set is: `Hom(-, 1)` is constant. -/
theorem isCardinalPresentable_op_punit (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    IsCardinalPresentable (op (PUnit : Type u)) κ := by
  let e : coyoneda.obj (op (op (PUnit : Type u))) ≅ (Functor.const _).obj PUnit.{u + 1} :=
    NatIso.ofComponents (fun X => Equiv.toIso
      { toFun := fun _ => PUnit.unit
        invFun := fun _ => Quiver.Hom.op (↾fun _ => PUnit.unit)
        left_inv := fun f => Quiver.Hom.unop_inj (by ext)
        right_inv := fun _ => rfl })
  have := const_punit_isCardinalAccessible.{u} κ
  exact Functor.isCardinalAccessible_of_natIso e.symm κ

/-- Board `4gynb9uTEE4-20493`, t = 22920: on `ℤ²` the map equal to the identity on the two axes and
to `0` elsewhere commutes with all `x ↦ nx` but is not a homomorphism. -/
theorem int_sq_powers_not_full :
    ∃ f : ℤ × ℤ → ℤ × ℤ, (∀ (n : ℤ) x, f (n • x) = n • f x) ∧
      ¬ ∀ x y, f (x + y) = f x + f y := by
  classical
  refine ⟨fun x => if x.1 * x.2 = 0 then x else 0, fun n x => ?_, fun h => ?_⟩
  · by_cases hx : x.1 * x.2 = 0
    · have : (n • x).1 * (n • x).2 = 0 := by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        rw [show n * x.1 * (n * x.2) = n * n * (x.1 * x.2) by ring, hx, mul_zero]
      dsimp only
      simp only [this, hx, ↓reduceIte]
    · by_cases hn : n = 0
      · subst hn; simp
      · have : (n • x).1 * (n • x).2 ≠ 0 := by
          simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
          rw [show n * x.1 * (n * x.2) = n * n * (x.1 * x.2) by ring]
          exact mul_ne_zero (mul_ne_zero hn hn) hx
        dsimp only
        simp only [this, hx, ↓reduceIte, smul_zero]
  · have := h (1, 0) (0, 1)
    simp only [Prod.mk_add_mk, add_zero, zero_add, mul_one, mul_zero, ite_true,
      one_ne_zero, ite_false] at this
    exact absurd this (by decide)

/-- Board `4gynb9uTEE4-20493`, t = 23531: in a Lawvere theory,
`Hom(Xⁿ, X^m) = Hom(Xⁿ, X)^m`. -/
def LawvereTheory.homEquiv (T : LawvereTheory) (n m : ℕ) :
    letI := T.cat
    (n ⟶ m) ≃ (Fin m → (n ⟶ 1)) :=
  letI := T.cat
  { toFun := fun f i => f ≫ T.proj m i
    invFun := fun g => Fan.IsLimit.lift (T.isLimit m) g
    left_inv := fun f => Fan.IsLimit.hom_ext (T.isLimit m) _ _ (fun i => by
      have := Fan.IsLimit.fac (T.isLimit m) (fun i => f ≫ T.proj m i) i
      simpa using this)
    right_inv := fun g => funext fun i => by simpa using Fan.IsLimit.fac (T.isLimit m) g i }

end

end Buffalo.Topos.Part06
