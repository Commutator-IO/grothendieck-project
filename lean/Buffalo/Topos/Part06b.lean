import Buffalo.Topos.Part06a
import Buffalo.Topos.Part03b

/-!
# Buffalo, topos theory, part 6b: strict generation, theories, Lawvere, Birkhoff (11 July 1973)

Entries of `docs/buffalo-topos/index.tex` lines 880–931 (video `4gynb9uTEE4`, 5:43:46–7:19:36):
strictly generating functors, theories defined by finite limits, finitely presented objects,
Lawvere theories, Birkhoff's theorem, pseudo-topoi and classifying topoi. The status of each entry
is in `docs/buffalo-topos/lean/Part06.json`.

A strictly generating functor `i : C → E` is Mathlib's dense functor (`Functor.IsDense`); a
strictly epimorphic family is Mathlib's `EffectiveEpiFamily`; morphisms of topoi are modelled by
`Buffalo.Topos.Part03.TopMor` (an adjunction `f^* ⊣ f_*` with `f^*` left exact).
-/

universe w v u

open CategoryTheory Limits Opposite

namespace Buffalo.Topos.Part06

noncomputable section

/-! ## Strictly generating functors -/

section StrictlyGenerating

variable {C : Type*} [Category* C] {E : Type*} [Category* E]

/-- 4gynb9uTEE4-20626 (5:43:46) [prop] For `i : C → E` full, every `X` is the colimit of the
`i(Y)`, `(Y, u) ∈ C/X` (`i` dense), iff `E → Ĉ`, `X ↦ Hom(i(-), X)`, is fully faithful
(Mathlib). -/
theorem isDense_iff_fullyFaithful (i : C ⥤ E) [i.Full] :
    i.IsDense ↔ Nonempty (Presheaf.restrictedULiftYoneda.{w} i).FullyFaithful :=
  Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda i

/-- 4gynb9uTEE4-20819 (5:46:59) [prop] (partial: first half) If `i` is strictly generating, every
`X` is the target of a strictly epimorphic family: all the arrows `u : i(Y) → X`. -/
def effectiveEpiFamilyStructOfIsDense (i : C ⥤ E) [i.IsDense] (X : E) :
    EffectiveEpiFamilyStruct (fun a : CostructuredArrow i X => i.obj a.left)
      (fun a => a.hom) where
  desc {W} e h := (i.denseAt X).desc
    { pt := W
      ι := { app a := e a
             naturality a b φ := by
               have := h (Z := i.obj a.left) a b (𝟙 _) (i.map φ.left)
                 (by simp)
               simp at this; simp [this] } }
  fac {W} e h a := by simpa using (i.denseAt X).fac _ a
  uniq {W} e h m hm := (i.denseAt X).hom_ext (fun a => by
    rw [(i.denseAt X).fac]
    simpa using hm a)

theorem effectiveEpiFamily_of_isDense (i : C ⥤ E) [i.IsDense] (X : E) :
    EffectiveEpiFamily (fun a : CostructuredArrow i X => i.obj a.left) (fun a => a.hom) :=
  ⟨⟨effectiveEpiFamilyStructOfIsDense i X⟩⟩

end StrictlyGenerating

section Reflective

variable {C : Type v} [SmallCategory C] {E : Type u} [Category.{v} E] [HasColimitsOfSize.{v, v} E]

/-- 4gynb9uTEE4-21008 (5:50:08) [prop] (partial: direct half) `i` extends to
`i_! : Ĉ → E`, left adjoint to `E → Ĉ`; if `i` is strictly generating, `i_!` is a localization,
making `E` a category of fractions of `Ĉ`. -/
theorem isLocalization_of_isDense (i : C ⥤ E) [i.IsDense] :
    (uliftYoneda.{v}.leftKanExtension i).IsLocalization
      ((MorphismProperty.isomorphisms E).inverseImage (uliftYoneda.{v}.leftKanExtension i)) :=
  (Presheaf.uliftYonedaAdjunction.{0} _ (uliftYoneda.{v}.leftKanExtensionUnit i)).isLocalization

/-- 4gynb9uTEE4-21139 (5:52:19) [thm] (partial: direct half) If `i : C → E` (`C` small) is
strictly generating, `E → Ĉ` is a reflective full embedding. -/
theorem reflective_of_isDense (i : C ⥤ E) [i.IsDense] :
    Nonempty (Reflective (Presheaf.restrictedULiftYoneda.{v} i)) :=
  ⟨{ L := _, adj := Presheaf.uliftYonedaAdjunction.{0} _ (uliftYoneda.{v}.leftKanExtensionUnit i) }⟩

end Reflective

open Classical in
/-- 4gynb9uTEE4-21464 (5:57:44) [cex] In compact spaces the point is not strictly generating:
`Hom(pt, -)` is the underlying set, and a map of underlying sets of compact spaces need not be
continuous (the indicator of `∞` on the one-point compactification of `ℕ`). -/
theorem onePoint_indicator_not_continuous :
    ¬ Continuous (fun x : OnePoint ℕ => decide (x = OnePoint.infty)) := by
  intro h
  have ho : IsOpen ((fun x : OnePoint ℕ => decide (x = OnePoint.infty)) ⁻¹' {true}) :=
    (isOpen_discrete _).preimage h
  have hs : ((fun x : OnePoint ℕ => decide (x = OnePoint.infty)) ⁻¹' {true}) =
      {OnePoint.infty} := by ext x; simp
  rw [hs, OnePoint.isOpen_iff_of_mem (Set.mem_singleton _)] at ho
  have : (((↑) : ℕ → OnePoint ℕ) ⁻¹' {OnePoint.infty})ᶜ = Set.univ := by ext n; simp
  rw [this] at ho
  exact noncompact_univ ℕ ho.2

theorem onePoint_compHaus : CompactSpace (OnePoint ℕ) ∧ T2Space (OnePoint ℕ) :=
  ⟨inferInstance, inferInstance⟩

/-! ## Theories defined by finite limits -/

/-- 4gynb9uTEE4-21923 (6:05:23) [prop] (partial) `C` embeds fully in `Hom(C, Set)^op`
(`C^op → Hom(C, Set)` is fully faithful: coYoneda). -/
theorem coyoneda_fullyFaithful (C : Type u) [Category.{v} C] :
    (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v).Full ∧ (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v).Faithful :=
  ⟨inferInstance, inferInstance⟩

/-- 4gynb9uTEE4-22244 (6:10:44) [prop] For finite diagrams, an algebraic theory is a small
category `R₀` with finite limits, its realizations in `Set` the left exact functors `R₀ → Set`;
dually `Σ₀ = R₀^op` has finite colimits. -/
theorem sigma0_hasFiniteColimits (R₀ : Type u) [SmallCategory R₀] [HasFiniteLimits R₀] :
    HasFiniteColimits R₀ᵒᵖ := inferInstance

/-- The realizations of the theory `R₀`: left exact functors `R₀ → Set`. -/
abbrev Realizations (R₀ : Type u) [SmallCategory R₀] : Type (u + 1) := LeftExactFunctor R₀ (Type u)

/-! ## Finitely presented objects -/

/-- 4gynb9uTEE4-22374 (6:12:54) [def] `X` finitely presented: `Hom(X, -)` commutes with filtered
colimits (Mathlib `IsFinitelyPresentable`, i.e. `ℵ₀`-presentable). -/
theorem isFinitelyPresentable_iff {E : Type u} [Category.{v} E] (X : E) :
    IsFinitelyPresentable.{v} X ↔ PreservesFilteredColimitsOfSize.{v, v} (coyoneda.obj (op X)) :=
  isFinitelyPresentable_iff_preservesFilteredColimitsOfSize

/-- 4gynb9uTEE4-22438 (6:13:58) [prop] (partial) For `R₀` small with finite limits and
`Σ₀ = R₀^op`, `S = Lex(R₀, Set) ≃ Ind(Σ₀)`: a functor `R₀ → Set` is an ind-object of `Σ₀` iff it
is left exact (Mathlib) ... -/
theorem lex_iff_isIndObject (R₀ : Type u) [SmallCategory R₀] [HasFiniteLimits R₀]
    (A : R₀ᵒᵖᵒᵖ ⥤ Type u) : IsIndObject A ↔ PreservesFiniteLimits A :=
  isIndObject_iff_preservesFiniteLimits A

/-- ... and the representables are finitely presented. -/
theorem representable_isFinitelyPresentable (C : Type u) [SmallCategory C] (X : C) :
    IsFinitelyPresentable.{u} (uliftYoneda.{u}.obj X) := inferInstance

/-- 4gynb9uTEE4-22501 (6:15:01) [prop] (false as stated: only "if" holds) Counterexample to
"`Ind(Σ₀) → S` fully faithful ⇒ `Σ₀ ⊂ S_fp`": in `S = ℕ∞ = {0 < 1 < ⋯ < ∞}` (all small colimits),
`Σ₀ = {∞}` has `Ind(Σ₀) = Σ₀` (one object, one arrow), so `Ind(Σ₀) → S` is fully faithful, but
`∞ = colim n` is not finitely presented. -/
theorem top_not_isFinitelyPresentable : ¬ IsFinitelyPresentable.{0} (⊤ : ℕ∞) := by
  intro h
  let F : ℕ ⥤ ℕ∞ := Monotone.functor (f := fun n : ℕ => (n : ℕ∞)) Nat.mono_cast
  let c := CompleteLattice.colimitCocone F
  have hpt : (⊤ : ℕ∞) ≤ c.cocone.pt := by
    change (⊤ : ℕ∞) ≤ ⨆ n : ℕ, (n : ℕ∞)
    rw [ENat.iSup_natCast]
  obtain ⟨n, g, -⟩ := IsFinitelyPresentable.exists_hom_of_isColimit c.isColimit (homOfLE hpt)
  exact ENat.top_ne_natCast n (le_antisymm le_top (leOfHom g)).symm

/-- 4gynb9uTEE4-22570 (6:16:10) [ex] (partial: commutative algebras, one direction) A finitely
presented commutative `R`-algebra is a finitely presentable object of `R`-algebras (Mathlib). -/
theorem commRing_fp {R : CommRingCat.{u}} (S : Under R) (hS : S.hom.hom.FinitePresentation) :
    IsFinitelyPresentable.{u} S :=
  CommRingCat.isFinitelyPresentable_under R S hS

instance fact_isRegular_aleph0 : Fact Cardinal.aleph0.{v}.IsRegular := ⟨Cardinal.isRegular_aleph0⟩

/-- 4gynb9uTEE4-22638 (6:17:18) [thm] (partial) `S` with small colimits is locally finitely
presentable iff `S_fp` is essentially small and strictly generating (`κ = ℵ₀` in
`locallyPresentable_iff_dense`); the identification with `T(Set)` for a finite-limit theory
(Gabriel–Ulmer) is not in Mathlib. -/
theorem locallyFinitelyPresentable_iff (S : Type u) [Category.{v} S] [HasColimitsOfSize.{v, v} S]
    [LocallySmall.{v} S] :
    IsCardinalLocallyPresentable S Cardinal.aleph0.{v} ↔
      ObjectProperty.EssentiallySmall.{v} (isCardinalPresentable S Cardinal.aleph0.{v}) ∧
        (isCardinalPresentable S Cardinal.aleph0.{v}).ι.IsDense :=
  locallyPresentable_iff_dense _

/-- 4gynb9uTEE4-22766 (6:19:26) [ex] In groups, with `C = {ℤ}`, `Ĉ` is the sets with an action of
the monoid `(ℤ, ×)`, and `G ↦ (G, x ↦ x^n)` is not full: on `(ℤ/2)²` the map sending `0` to `0`
and every other element to `1 ∈ ℤ/2` commutes with all the power maps but is not a homomorphism. -/
theorem powers_not_full :
    ∃ f : ZMod 2 × ZMod 2 → ZMod 2, (∀ (n : ℤ) x, f (n • x) = n • f x) ∧
      ¬ ∀ x y, f (x + y) = f x + f y := by
  classical
  refine ⟨fun x => if x = 0 then 0 else 1, fun n x => ?_, fun h => ?_⟩
  · have h2 : ∀ y : ZMod 2 × ZMod 2, y + y = 0 := by decide
    have h2' : ∀ y : ZMod 2, y + y = 0 := by decide
    rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [add_zsmul, add_zsmul, h2, h2']
      simp
    · have e1 : (2 * k + 1) • x = x := by
        rw [add_zsmul, mul_comm, mul_zsmul, two_zsmul, h2, zsmul_zero, zero_add, one_zsmul]
      have e2 : ∀ y : ZMod 2, (2 * k + 1) • y = y := fun y => by
        rw [add_zsmul, mul_comm, mul_zsmul, two_zsmul, h2', zsmul_zero, zero_add, one_zsmul]
      rw [e1, e2]
  · have := h (1, 0) (0, 1)
    revert this
    decide

/-- 4gynb9uTEE4-22960 (6:22:40) [rem] (partial) In a balanced category with equalizers (e.g. a
topos), "conservative" (detecting) and "faithful" (separating) generation coincide (Mathlib). -/
theorem isDetecting_iff_isSeparating' {E : Type*} [Category* E] [HasEqualizers E] [Balanced E]
    (P : ObjectProperty E) : P.IsDetecting ↔ P.IsSeparating :=
  ObjectProperty.isDetecting_iff_isSeparating (P := P)

/-- 4gynb9uTEE4-23147 (6:25:47) [prop] The free groups of finite rank strictly generate `Gr`: a
family of maps `Hom(F_n, G) → Hom(F_n, H)` natural in the homomorphisms `F_m → F_n` comes from a
unique homomorphism `G → H`. -/
theorem freeGroup_strictly_generating {G H : Type u} [Group G] [Group H]
    (φ : ∀ n : ℕ, (FreeGroup (Fin n) →* G) → (FreeGroup (Fin n) →* H))
    (hφ : ∀ m n (k : FreeGroup (Fin m) →* FreeGroup (Fin n)) (x : FreeGroup (Fin n) →* G),
      φ m (x.comp k) = (φ n x).comp k) :
    ∃! f : G →* H, ∀ n x, φ n x = f.comp x := by
  let fn : G → H := fun g => φ 1 (FreeGroup.lift fun _ => g) (FreeGroup.of 0)
  have hA : ∀ n (x : FreeGroup (Fin n) →* G) (i : Fin n),
      φ n x (FreeGroup.of i) = fn (x (FreeGroup.of i)) := by
    intro n x i
    let k : FreeGroup (Fin 1) →* FreeGroup (Fin n) := FreeGroup.lift fun _ => FreeGroup.of i
    have hk : x.comp k = FreeGroup.lift fun _ => x (FreeGroup.of i) := by
      ext j; simp [k]
    have := congrArg (fun ψ : FreeGroup (Fin 1) →* H => ψ (FreeGroup.of 0)) (hφ 1 n k x)
    simp only [MonoidHom.comp_apply, hk] at this
    simp only [fn]
    rw [this]
    simp [k]
  let f : G →* H := MonoidHom.mk' fn (fun a b => by
    let x : FreeGroup (Fin 2) →* G := FreeGroup.lift ![a, b]
    let k : FreeGroup (Fin 1) →* FreeGroup (Fin 2) :=
      FreeGroup.lift fun _ => FreeGroup.of 0 * FreeGroup.of 1
    have hk : x.comp k = FreeGroup.lift fun _ => a * b := by
      ext j; simp [k, x]
    have := congrArg (fun ψ : FreeGroup (Fin 1) →* H => ψ (FreeGroup.of 0)) (hφ 1 2 k x)
    simp only [MonoidHom.comp_apply, hk] at this
    change φ 1 _ _ = _ * _
    rw [this]
    simp only [k, FreeGroup.lift_apply_of, map_mul, hA]
    simp [x])
  refine ⟨f, fun n x => FreeGroup.ext_hom _ _ (fun i => by simp [f, hA]), fun f' hf' => ?_⟩
  ext g
  have := congrArg (fun ψ : FreeGroup (Fin 1) →* H => ψ (FreeGroup.of 0))
    (hf' 1 (FreeGroup.lift fun _ => g))
  simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of] at this
  rw [← this]
  rfl

/-! ## Lawvere theories -/

/-- 4gynb9uTEE4-23662 (6:34:22) [def] A theory with one base object defined by finite products
(Lawvere theory): a category with objects `ℕ` in which `n` is the `n`-th power of `1`. -/
structure LawvereTheory where
  /-- The category structure (`H_n = Hom(n, 1)` and substitution). -/
  cat : Category.{0} ℕ
  /-- The projections `n → 1`. -/
  proj : ∀ n : ℕ, Fin n → (n ⟶ 1)
  /-- They make `n` the product of `n` copies of `1`. -/
  isLimit : ∀ n : ℕ, IsLimit (Fan.mk (f := fun _ : Fin n => (1 : ℕ)) n (proj n))

/-- 4gynb9uTEE4-23791 (6:36:31) [def] The realizations of a Lawvere theory in a category `E` with
finite products: the functors commuting with finite products. -/
def LawvereTheory.Model (T : LawvereTheory) (E : Type*) [Category* E] : Type _ :=
  letI := T.cat
  { F : ℕ ⥤ E // PreservesFiniteProducts F }

/-! ## Birkhoff's theorem -/

/-- 4gynb9uTEE4-24671 (6:51:11) [prop] (special case) Abelian groups form a reflective full
subcategory of groups: the reflection of `G` is its largest abelian quotient (Mathlib). -/
theorem abelian_reflective : Nonempty (Reflective (forget₂ CommGrpCat.{u} GrpCat.{u})) :=
  ⟨{ L := GrpCat.abelianize, adj := GrpCat.abelianizeAdj }⟩

/-- Torsion-free abelian groups. -/
def TorsionFree (A : Type*) [AddCommGroup A] : Prop :=
  ∀ (n : ℕ) (a : A), n ≠ 0 → n • a = 0 → a = 0

/-- 4gynb9uTEE4-24737 (6:52:17) [cex] Torsion-free abelian groups are stable under products ... -/
theorem torsionFree_pi {ι : Type*} (A : ι → Type*) [∀ i, AddCommGroup (A i)]
    (h : ∀ i, TorsionFree (A i)) : TorsionFree (∀ i, A i) := fun n a hn ha => by
  funext i
  exact h i n (a i) hn (by simpa using congrFun ha i)

/-- ... and subgroups ... -/
theorem torsionFree_subgroup {A : Type*} [AddCommGroup A] (h : TorsionFree A)
    (B : AddSubgroup A) : TorsionFree B := fun n a hn ha =>
  Subtype.ext (h n a hn (by simpa using congrArg Subtype.val ha))

/-- ... but not under quotients (`ℤ → ℤ/2`), so they are not definable by equations. -/
theorem torsionFree_not_quotient :
    TorsionFree ℤ ∧ Function.Surjective (Int.castAddHom (ZMod 2)) ∧ ¬ TorsionFree (ZMod 2) := by
  refine ⟨fun n a hn ha => ?_, ZMod.intCast_surjective, fun h => ?_⟩
  · simpa [hn] using ha
  · exact absurd (h 2 1 (by norm_num) (by decide)) (by decide)

/-- 4gynb9uTEE4-25511 (7:05:11) [cex] Groups are the monoids in which the arrow
`(x, y) ↦ (x, xy)` of `M × M` is invertible ... -/
theorem isGroup_iff_shear_bijective (M : Type*) [Monoid M] :
    (∀ x : M, IsUnit x) ↔ Function.Bijective (fun p : M × M => (p.1, p.1 * p.2)) := by
  constructor
  · intro h
    refine ⟨fun p q hpq => ?_, fun q => ?_⟩
    · simp only [Prod.mk.injEq] at hpq
      obtain ⟨h1, h2⟩ := hpq
      ext
      · exact h1
      · rw [h1] at h2; exact (h q.1).mul_left_cancel h2
    · obtain ⟨u, hu⟩ := h q.1
      refine ⟨(q.1, ↑u⁻¹ * q.2), ?_⟩
      ext
      · rfl
      · simp [← hu]
  · rintro ⟨hinj, hsurj⟩ x
    obtain ⟨⟨a, y⟩, hy⟩ := hsurj (x, 1)
    simp only [Prod.mk.injEq] at hy
    obtain ⟨rfl, hxy⟩ := hy
    have hyx : y * a = 1 := by
      have := @hinj (a, y * a) (a, 1) (by simp [← mul_assoc, hxy])
      exact congrArg Prod.snd this
    exact ⟨⟨a, y, hxy, hyx⟩, rfl⟩

/-- ... but groups are not stable under submonoids (`ℕ ⊂ ℤ`), so they are not definable by
equations in monoids. -/
theorem submonoid_not_group :
    ∃ M : Submonoid (Multiplicative ℤ), ∃ x ∈ M, ∀ y ∈ M, y * x ≠ 1 := by
  refine ⟨Submonoid.powers (Multiplicative.ofAdd 1), _, Submonoid.mem_powers _, ?_⟩
  rintro y ⟨k, rfl⟩ h
  have := congrArg Multiplicative.toAdd h
  simp at this
  omega

/-! ## Pseudo-topoi and classifying topoi -/

section PseudoTopos

variable (E : Type u) [Category.{v} E]

/-- An internal equivalence relation `(r₁, r₂) : R ⇉ X`. -/
structure IsEquivRel {E : Type u} [Category.{v} E] {X R : E} (r₁ r₂ : R ⟶ X) : Prop where
  jointlyMono : ∀ {T : E} (a b : T ⟶ R), a ≫ r₁ = b ≫ r₁ → a ≫ r₂ = b ≫ r₂ → a = b
  refl : ∀ {T : E} (x : T ⟶ X), ∃ a : T ⟶ R, a ≫ r₁ = x ∧ a ≫ r₂ = x
  symm : ∀ {T : E} (a : T ⟶ R), ∃ b : T ⟶ R, b ≫ r₁ = a ≫ r₂ ∧ b ≫ r₂ = a ≫ r₁
  trans : ∀ {T : E} (a b : T ⟶ R), a ≫ r₂ = b ≫ r₁ →
    ∃ c : T ⟶ R, c ≫ r₁ = a ≫ r₁ ∧ c ≫ r₂ = b ≫ r₂

/-- 4gynb9uTEE4-25846 (7:10:46) [def] A pseudo-topos: Giraud's axioms a) small colimits and
finite limits; b) small coproducts disjoint and universal; c) equivalence relations effective and
universal. -/
structure IsPseudoTopos : Prop where
  hasColimits : HasColimitsOfSize.{v, v} E
  hasFiniteLimits : HasFiniteLimits E
  mono_inj : ∀ {ι : Type v} (X : ι → E) (c : Cofan X), IsColimit c → ∀ i, Mono (c.inj i)
  disjoint : ∀ {ι : Type v} (X : ι → E) (c : Cofan X), IsColimit c → ∀ i j, i ≠ j →
    ∀ (P : E) (p₁ : P ⟶ X i) (p₂ : P ⟶ X j), IsPullback p₁ p₂ (c.inj i) (c.inj j) →
      Nonempty (IsInitial P)
  universal : ∀ {ι : Type v} (X : ι → E) (c : Cofan X), IsColimit c → IsUniversalColimit c
  effective : ∀ {X R : E} (r₁ r₂ : R ⟶ X), IsEquivRel r₁ r₂ →
    ∃ c : Cofork r₁ r₂, Nonempty (IsColimit c) ∧ IsPullback r₁ r₂ c.π c.π ∧ IsUniversalColimit c

/-- 4gynb9uTEE4-25975 (7:12:55) [prop] (presheaf topoi) A functor `Ĉ → E` commuting with small
colimits and finite limits is the inverse image `f^*` of a morphism of topoi `f : E → Ĉ`. -/
def topMorOfLex {C : Type u} [SmallCategory C] {E : Type*} [Category.{u} E]
    [HasColimitsOfSize.{u, u} E] (L : (Cᵒᵖ ⥤ Type u) ⥤ E) [PreservesColimitsOfSize.{u, u} L]
    [PreservesFiniteLimits L] : Part03.TopMor E (Cᵒᵖ ⥤ Type u) :=
  have : L.IsLeftAdjoint := Presheaf.isLeftAdjoint_of_preservesColimits.{0} L
  { inv := L, dir := L.rightAdjoint, adj := Adjunction.ofIsLeftAdjoint L, lex := inferInstance }

/-- 4gynb9uTEE4-26048 (7:14:08) [def] `E` classifies the theory `T_C` of left exact functors on
`C`, with universal object `U : C → E`, if `f ↦ f^* U` is an equivalence
`Top(F, E)^op ≃ Lex(C, F)` for every `F`: essentially surjective onto the left exact functors and
bijective on arrows (2-arrows `f → g` are direct-image transformations, sent to
`g^* U → f^* U`). -/
def Classifies {C : Type u} [SmallCategory C] {E : Type*} [Category* E] (U : C ⥤ E) : Prop :=
  ∀ (F : Type u) [Category.{u} F],
    (∀ G : C ⥤ F, PreservesFiniteLimits G → ∃ f : Part03.TopMor F E, Nonempty (U ⋙ f.inv ≅ G)) ∧
    ∀ f g : Part03.TopMor F E,
      Function.Bijective (fun α : f ⟶ g => Functor.whiskerLeft U (Part03.TopMor.homEquivInv f g α))

/-- 4gynb9uTEE4-26376 (7:19:36) [prop] (partial) A morphism of topoi `f : E → Ĉ` gives the left
exact functor `C → E`, `X ↦ f^*(yX)`, the restriction of `f^*` along the Yoneda embedding. -/
theorem yoneda_comp_inv_lex {C : Type u} [SmallCategory C] {E : Type*} [Category* E]
    (f : Part03.TopMor E (Cᵒᵖ ⥤ Type u)) : PreservesFiniteLimits (yoneda ⋙ f.inv) := by
  have := f.lex
  exact comp_preservesFiniteLimits _ _

end PseudoTopos

end

end Buffalo.Topos.Part06
