import Mathlib

/-!
# Buffalo, topos theory, part 7c: what is not a theory, faithfulness, points (12 July 1973)

Entries of `docs/buffalo-topos/index.tex` lines 965–1114 (video `ORG14LNb5gE`, 3:48:16–4:36:27):
properties not stable under filtered colimits (rank-`n` coverings, rings with `n` connected
components; both corrected to `n ≥ 2`), faithfulness of actions, topoi without points. Statuses in
`docs/buffalo-topos/lean/Part07.json`.
-/

universe u v w

open CategoryTheory Limits Opposite

namespace Buffalo.Topos.Part07

noncomputable section

/-! ## Rank-`n` coverings of the terminal object -/

section Rank

/-- The sequence `Fin n → Fin n → ⋯` whose transition maps are constant. -/
def collapseSeq (n : ℕ) (hn : 0 < n) : ℕ ⥤ Type where
  obj _ := Fin n
  map {i j} _ := ↾(fun x => if i = j then x else ⟨0, hn⟩)
  map_id i := ConcreteCategory.hom_ext _ _ fun x => by
    show (if i = i then x else ⟨0, hn⟩) = x
    simp
  map_comp {i j k} f g := ConcreteCategory.hom_ext _ _ fun x => by
    have hij := leOfHom f
    have hjk := leOfHom g
    show (if i = k then x else ⟨0, hn⟩) =
      (if j = k then (if i = j then x else ⟨0, hn⟩) else ⟨0, hn⟩)
    split_ifs <;> first | rfl | omega

/-- Its cocone to the point. -/
def collapseCocone (n : ℕ) (hn : 0 < n) : Cocone (collapseSeq n hn) where
  pt := PUnit
  ι := { app := fun _ => ↾(fun _ => PUnit.unit) }

/-- ... which is a colimit cocone. -/
def collapseIsColimit (n : ℕ) (hn : 0 < n) : IsColimit (collapseCocone n hn) :=
  Types.FilteredColimit.isColimitOf _ _
    (fun _ => ⟨0, ⟨0, hn⟩, rfl⟩)
    (fun i j xi xj _ => ⟨max i j + 1, homOfLE (by omega), homOfLE (by omega), by
      change Fin n at xi xj
      show (if i = max i j + 1 then xi else (⟨0, hn⟩ : Fin n)) =
        (if j = max i j + 1 then xj else (⟨0, hn⟩ : Fin n))
      split_ifs <;> first | rfl | omega⟩)

/-- The colimit of a filtered sequence of `n`-element sets can have one element. -/
theorem card_not_stable (n : ℕ) (hn : 0 < n) :
    (∀ i, Nat.card ((collapseSeq n hn).obj i) = n) ∧ Nat.card (collapseCocone n hn).pt = 1 := by
  refine ⟨fun i => ?_, ?_⟩
  · simp [collapseSeq]
  · simp [collapseCocone]

/-- For `n = 1` the property holds: one-element sets are stable under filtered colimits. -/
theorem singleton_stable {J : Type} [SmallCategory J] [IsFiltered J] (F : J ⥤ Type)
    (hF : ∀ j, Nonempty (Unique (F.obj j))) (c : Cocone F) (hc : IsColimit c) :
    Nonempty (Unique c.pt) := by
  have hs : ∀ x : c.pt, ∃ j y, c.ι.app j y = x := Types.jointly_surjective_of_isColimit hc
  obtain ⟨j0⟩ := IsFiltered.nonempty (C := J)
  obtain ⟨u⟩ := hF j0
  refine ⟨⟨⟨c.ι.app j0 default⟩, fun x => ?_⟩⟩
  obtain ⟨j, y, rfl⟩ := hs x
  have h1 := ConcreteCategory.congr_hom (c.w (IsFiltered.leftToMax j j0)) y
  have h2 := ConcreteCategory.congr_hom (c.w (IsFiltered.rightToMax j j0)) default
  obtain ⟨u'⟩ := hF (IsFiltered.max j j0)
  rw [ConcreteCategory.comp_apply] at h1 h2
  rw [← h1, ← h2]
  congr 1
  exact Subsingleton.elim _ _

/-- ORG14LNb5gE-13696 (3:48:16) [cex], corrected: for `n ≥ 2`, sets with `n` elements are not
stable under filtered colimits (for `n ≤ 1` they are, `singleton_stable`: rank `1` coverings are
the terminal object, classified by `Φ₁`). -/
theorem rank_not_stable (n : ℕ) (hn : 2 ≤ n) :
    ∃ (F : ℕ ⥤ Type) (c : Cocone F), Nonempty (IsColimit c) ∧
      (∀ i, Nat.card (F.obj i) = n) ∧ Nat.card c.pt ≠ n :=
  ⟨collapseSeq n (by omega), collapseCocone n (by omega), ⟨collapseIsColimit n (by omega)⟩,
    (card_not_stable n (by omega)).1, by rw [(card_not_stable n (by omega)).2]; omega⟩
end Rank

/-! ## Rings with `n` connected components -/

section Components

variable (n : ℕ) (hn : 0 < n)

/-- `x ↦ (x₀, …, x₀)` on `ℤⁿ`. -/
def diag0 : (Fin n → ℤ) →+* (Fin n → ℤ) := RingHom.pi fun _ => Pi.evalRingHom (fun _ => ℤ) ⟨0, hn⟩

/-- The sequence `ℤⁿ → ℤⁿ → ⋯` with transition maps `x ↦ (x₀, …, x₀)`. -/
def ringSeq : ℕ ⥤ CommRingCat.{0} where
  obj _ := CommRingCat.of (Fin n → ℤ)
  map {i j} _ := if i = j then 𝟙 _ else CommRingCat.ofHom (diag0 n hn)
  map_id i := by simp
  map_comp {i j k} f g := by
    have hij := leOfHom f
    have hjk := leOfHom g
    by_cases h1 : i = j <;> by_cases h2 : j = k
    · subst h1 h2; simp
    · subst h1; simp [h2]
    · subst h2; simp [h1]
    · simp only [h1, h2, show i ≠ k by omega, ↓reduceIte]
      ext x m
      rfl

/-- Its cocone to `ℤ` (first coordinate). -/
def ringCocone : Cocone (ringSeq n hn) where
  pt := CommRingCat.of ℤ
  ι := { app := fun _ => CommRingCat.ofHom (Pi.evalRingHom (fun _ => ℤ) ⟨0, hn⟩)
         naturality := fun i j f => by
           simp only [ringSeq, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
           split_ifs
           · simp
           · rfl }

/-- ... a colimit cocone. -/
def ringCoconeIsColimit : IsColimit (ringCocone n hn) where
  desc s := CommRingCat.ofHom (Int.castRingHom s.pt)
  fac s j := by
    ext x
    have hw := s.w (homOfLE (Nat.le_succ j) : j ⟶ j + 1)
    have := congrArg (fun φ => φ.hom x) hw
    simp only [ringSeq, CommRingCat.hom_comp, show j ≠ j + 1 by omega, ↓reduceIte,
      CommRingCat.hom_ofHom] at this
    refine Eq.trans ?_ this
    change Fin n → ℤ at x
    have hx : diag0 n hn x = ((x ⟨0, hn⟩ : ℤ) : Fin n → ℤ) := by ext; rfl
    change ((x ⟨0, hn⟩ : ℤ) : s.pt) = (s.ι.app (j + 1)).hom (diag0 n hn x)
    rw [hx]
    exact (map_intCast (s.ι.app (j + 1)).hom _).symm
  uniq s m _ := by
    ext x
    simp [RingHom.ext_int m.hom (Int.castRingHom s.pt)]
    rfl

/-- The idempotents of `ℤ`: `ℤ` is connected. -/
theorem int_idem (a : ℤ) : IsIdempotentElem a ↔ a = 0 ∨ a = 1 := by
  constructor
  · intro h
    have : a * (a - 1) = 0 := by rw [mul_sub, h.eq, mul_one, sub_self]
    rcases mul_eq_zero.mp this with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rintro (rfl | rfl) <;> rfl

/-- The idempotents of `ℤⁿ`. -/
theorem pi_idem (x : Fin n → ℤ) : IsIdempotentElem x ↔ ∀ i, x i = 0 ∨ x i = 1 := by
  simp only [← int_idem]
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

/-- The idempotents of `ℤⁿ` are the `2ⁿ` vectors of `0` and `1`. -/
def idemEquiv : {x : Fin n → ℤ // IsIdempotentElem x} ≃ (Fin n → Bool) where
  toFun x i := decide (x.1 i = 1)
  invFun b := ⟨fun i => if b i then 1 else 0, (pi_idem n _).2 fun i => by cases b i <;> simp⟩
  left_inv x := by
    ext i
    rcases (pi_idem n x.1).1 x.2 i with h | h <;> simp [h]
  right_inv b := by funext i; cases h : b i <;> simp [h]

theorem idempotents_card : Nat.card {x : Fin n → ℤ // IsIdempotentElem x} = 2 ^ n := by
  rw [Nat.card_congr (idemEquiv n)]
  simp

/-- ORG14LNb5gE-14022 (3:53:42) [cex], corrected: for `n ≥ 2`, having exactly `n` connected
components (`2ⁿ` idempotents) is not stable under filtered colimits: the colimit of the sequence of
rings `ℤⁿ` (`n` components) is `ℤ` (one component). For `n = 1` it is connectedness, a theory
(entry 13957). -/
theorem components_not_stable (n : ℕ) (hn : 2 ≤ n) :
    (∀ i, Nat.card {x : (ringSeq n (by omega)).obj i // IsIdempotentElem x} = 2 ^ n) ∧
      Nat.card {x : ℤ // IsIdempotentElem x} = 2 ^ 1 ∧ 2 ^ n ≠ 2 ^ 1 := by
  refine ⟨fun i => idempotents_card n, ?_, ?_⟩
  · have := idempotents_card 1
    rw [← this]
    exact Nat.card_congr
      { toFun := fun x => ⟨fun _ => x.1, (pi_idem 1 _).2 fun _ => (int_idem _).1 x.2⟩
        invFun := fun x => ⟨x.1 0, (int_idem _).2 ((pi_idem 1 x.1).1 x.2 0)⟩
        left_inv := fun x => rfl
        right_inv := fun x => by
          ext i
          fin_cases i
          rfl }
  · exact (Nat.pow_right_injective (le_refl 2)).ne (by omega)
end Components

/-! ## Faithful actions, topoi without points -/

/-- The action of `Perm Bool × Perm Bool` on `Bool` through the first factor. -/
instance : MulAction (Equiv.Perm Bool × Equiv.Perm Bool) Bool := MulAction.compHom Bool (MonoidHom.fst _ _)

/-- A faithful action: only `1` acts trivially. -/
def IsFaithfulAction (G X : Type*) [Group G] [MulAction G X] : Prop := ∀ g : G, (∀ x : X, g • x = x) → g = 1

/-- ORG14LNb5gE-15944 (4:25:44) [cex] Faithfulness of a `G`-action is not stable under inverse
image. On the discrete two-point space (sheaves = pairs of sets), `G = 𝔖₂ × 𝔖₂` acting on
`(Bool, Bool)` factorwise acts faithfully, but its stalk at the first point (the inverse image by
that point) is `Bool` with the action through the first factor, which is not faithful. -/
theorem faithful_not_stable :
    (∀ g : Equiv.Perm Bool × Equiv.Perm Bool, (∀ x : Bool, g.1 x = x) → (∀ y : Bool, g.2 y = y) → g = 1) ∧
      ¬ IsFaithfulAction (Equiv.Perm Bool × Equiv.Perm Bool) Bool := by
  refine ⟨fun g h1 h2 => Prod.ext (Equiv.ext h1) (Equiv.ext h2), fun h => ?_⟩
  have := h (1, Equiv.swap true false) (fun x => rfl)
  have := congrArg (fun g => g.2 true) this
  simp at this

/-- ORG14LNb5gE-16521 (4:35:21) [prop] / ORG14LNb5gE-16587 (4:36:27) [ex] A completely prime
filter of a complete Boolean algebra (a point of the localic topos) is generated by an atom. So the
topos of an atomless complete Boolean algebra, such as the Borel sets of `[0, 1]` modulo null sets
(countable covers suffice there, the algebra being ccc), has no point. -/
theorem completelyPrime_atom {B : Type u} [CompleteBooleanAlgebra B] (F : Set B)
    (hinf : ∀ a b, a ∈ F → b ∈ F → a ⊓ b ∈ F)
    (htop : ⊤ ∈ F) (hbot : ⊥ ∉ F) (hprime : ∀ s : Set B, sSup s ∈ F → ∃ b ∈ s, b ∈ F) :
    ∃ a, IsAtom a ∧ a ∈ F := by
  set a := sInf F with ha
  have hcov : sSup (insert a (compl '' F)) = ⊤ := by
    rw [sSup_insert, eq_top_iff]
    calc ⊤ = a ⊔ aᶜ := (sup_compl_eq_top).symm
      _ ≤ a ⊔ sSup (compl '' F) := by
        gcongr
        rw [ha, compl_sInf']
  have haF : a ∈ F := by
    obtain ⟨b, hb, hbF⟩ := hprime _ (hcov ▸ htop)
    rcases hb with rfl | ⟨f, hf, rfl⟩
    · exact hbF
    · exact absurd (by simpa using hinf _ _ hf hbF) hbot
  refine ⟨a, ⟨fun h => hbot (h ▸ haF), fun b hb => ?_⟩, haF⟩
  have hsplit : a = b ⊔ (a ⊓ bᶜ) := by
    rw [sup_inf_left, sup_compl_eq_top, inf_top_eq, sup_eq_right.2 hb.le]
  obtain ⟨c, hc, hcF⟩ := hprime {b, a ⊓ bᶜ} (by rw [sSup_pair, ← hsplit]; exact haF)
  rcases hc with rfl | rfl
  · exact absurd (le_antisymm hb.le (sInf_le hcF)) hb.ne
  · have h1 : a ≤ bᶜ := (sInf_le hcF).trans inf_le_right
    have := le_inf (le_refl b) (hb.le.trans h1)
    rwa [inf_compl_eq_bot, le_bot_iff] at this

/-- In particular an atomless complete Boolean algebra has no completely prime filter. -/
theorem atomless_no_point {B : Type u} [CompleteBooleanAlgebra B] (hB : ∀ a : B, ¬ IsAtom a) (F : Set B)
    (hinf : ∀ a b, a ∈ F → b ∈ F → a ⊓ b ∈ F) (htop : ⊤ ∈ F) (hbot : ⊥ ∉ F)
    (hprime : ∀ s : Set B, sSup s ∈ F → ∃ b ∈ s, b ∈ F) : False := by
  obtain ⟨a, ha, -⟩ := completelyPrime_atom F hinf htop hbot hprime
  exact hB a ha

end

end Buffalo.Topos.Part07
