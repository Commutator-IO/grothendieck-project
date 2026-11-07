import Mathlib

/-!
# Buffalo, topos theory, part 7a: generating subcategories, strict epimorphisms, subtopoi

Entries of `docs/buffalo-topos/index.tex` lines 965–1114 (video `ORG14LNb5gE`, 12 July 1973) on
generating subcategories of a topos and strictly epimorphic families (0:32:47–0:50:01), and the
subtopoi of `Sh(C, τ)` (1:19:23). The status of each entry is in
`docs/buffalo-topos/lean/Part07.json`.

A strictly epimorphic family in the sense of SGA 4 (I 10.3) is Mathlib's `EffectiveEpiFamily`;
« strictly and universally epimorphic » is « the generated sieve covers for the canonical
topology » (SGA 4 II 2.5), `IsUniversalStrictEpi` below. For a full subcategory `ι : C ⥤ E`,
condition (b) « every `X` is the colimit of `C/X` » is Mathlib's `ι.isDenseAt X`.

The counterexamples in groups use `F₂ = FreeGroup Bool` for `ℤ * ℤ` and the full subcategory
`C = {ℤ}` of `GrpCat`, as the induced category on one object.
-/

universe u v w

open CategoryTheory Limits

namespace Buffalo.Topos.Part07

noncomputable section

/-! ## Generating subcategories: (b) and (b′) -/

section Generating

variable {C : Type u} [Category.{v} C] {E : Type w} [Category.{v} E] (ι : C ⥤ E)

/-- The cocone over `C/X` defined by a compatible family. -/
@[simps]
def compatCocone {X W : E} (e : ∀ g : CostructuredArrow ι X, ι.obj g.left ⟶ W)
    (h : ∀ {Z : E} (a₁ a₂ : CostructuredArrow ι X) (g₁ : Z ⟶ ι.obj a₁.left)
      (g₂ : Z ⟶ ι.obj a₂.left), g₁ ≫ a₁.hom = g₂ ≫ a₂.hom → g₁ ≫ e a₁ = g₂ ≫ e a₂) :
    Cocone (CostructuredArrow.proj ι X ⋙ ι) where
  pt := W
  ι := { app := fun g => e g
         naturality := fun g g' φ => by
           have := h g' g (ι.map φ.left) (𝟙 _) (by simp)
           simpa using this }

/-- If `X` is the colimit of `C/X` (condition (b) at `X`), the family of all arrows `ι Y → X` is
strictly epimorphic. -/
def effEpiOfDenseAt {X : E} (hX : ι.DenseAt X) :
    EffectiveEpiFamilyStruct (fun g : CostructuredArrow ι X => ι.obj g.left) (fun g => g.hom) where
  desc e h := hX.desc (compatCocone ι e h)
  fac e h g := by
    have := hX.fac (compatCocone ι e h) g
    simp at this
    exact this
  uniq e h m hm := by
    apply hX.hom_ext
    intro g
    have := hX.fac (compatCocone ι e h) g
    simp at this ⊢
    exact (hm g).trans this.symm

/-- ORG14LNb5gE-2891 (0:48:11) [prop], direction (b) ⇒ (b′), pointwise: if `X` is the colimit of
`C/X`, the family of all arrows `Y → X`, `Y` in `C`, is strictly epimorphic. -/
theorem effEpi_of_denseAt {X : E} (hX : ι.isDenseAt X) :
    EffectiveEpiFamily (fun g : CostructuredArrow ι X => ι.obj g.left) (fun g => g.hom) :=
  ⟨⟨effEpiOfDenseAt ι hX.some⟩⟩

/-- ORG14LNb5gE-2891 (0:48:11) [prop], direction (b′) ⇒ (b): for `C` full in `E`, if for every
object the family of all arrows from `C` is strictly epimorphic, then every `X` is the colimit of
`C/X` (the compatibility over an arbitrary test object is checked after restriction to `C`). -/
def denseAtOfEffEpi [ι.Full]
    (H : ∀ Y : E, EffectiveEpiFamily (fun g : CostructuredArrow ι Y => ι.obj g.left)
      (fun g => g.hom)) (X : E) : ι.DenseAt X :=
  haveI := H X
  { desc := fun s => EffectiveEpiFamily.desc (fun g : CostructuredArrow ι X => ι.obj g.left)
      (fun g => g.hom) (fun g => s.ι.app g)
      (fun {Z} a₁ a₂ g₁ g₂ hg => by
        have := H Z
        apply EffectiveEpiFamily.hom_ext (fun g : CostructuredArrow ι Z => ι.obj g.left)
          (fun g => g.hom)
        intro t
        have w₁ := s.w (CostructuredArrow.homMk (ι.preimage (t.hom ≫ g₁)) (by simp) :
          CostructuredArrow.mk (t.hom ≫ g₁ ≫ a₁.hom) ⟶ a₁)
        have w₂ := s.w (CostructuredArrow.homMk (ι.preimage (t.hom ≫ g₂)) (by simp) :
          CostructuredArrow.mk (t.hom ≫ g₂ ≫ a₂.hom) ⟶ a₂)
        simp only [Functor.comp_map, CostructuredArrow.proj_map, CostructuredArrow.homMk_left,
          Functor.map_preimage, Category.assoc] at w₁ w₂
        rw [w₁, w₂]
        have key : ∀ f f' : ι.obj t.left ⟶ X, f = f' →
            s.ι.app (CostructuredArrow.mk f) = s.ι.app (CostructuredArrow.mk f') := by
          rintro f _ rfl; rfl
        exact key _ _ (by rw [hg]))
    fac := fun s g => by
      have := EffectiveEpiFamily.fac (fun g : CostructuredArrow ι X => ι.obj g.left)
        (fun g => g.hom) (fun g => s.ι.app g)
      dsimp [Functor.LeftExtension.coconeAt]
      rw [Category.id_comp]
      exact this _ g
    uniq := fun s m hm => by
      apply EffectiveEpiFamily.uniq
      intro g
      simpa using hm g }

/-- ORG14LNb5gE-2891 (0:48:11) [prop] (b) ⇔ (b′), for `C` full in `E`. -/
theorem isDense_iff_effEpi [ι.Full] :
    ι.IsDense ↔ ∀ X : E,
      EffectiveEpiFamily (fun g : CostructuredArrow ι X => ι.obj g.left) (fun g => g.hom) :=
  ⟨fun _ X => effEpi_of_denseAt ι (Functor.IsDense.isDenseAt ι X),
    fun H => ⟨fun X => ⟨denseAtOfEffEpi ι H X⟩⟩⟩

/-- ORG14LNb5gE-2248 (0:37:28) [prop] (a) ⇔ (b): for `C` full in `E`, the restricted Yoneda
functor `E → Ĉ` is fully faithful iff `ι` is dense (every `X` is the colimit of `C/X`). -/
theorem dense_iff_fullyFaithful [ι.Full] :
    ι.IsDense ↔ Nonempty (Presheaf.restrictedULiftYoneda.{w} ι).FullyFaithful :=
  Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda ι

/-- ORG14LNb5gE-2248 (0:37:28) [prop] (b) ⇒ (c): every `X` is the target of a strictly
epimorphic family with sources in `C` (all the arrows from `C`). -/
theorem dense_strictlyGenerated [ι.IsDense] (X : E) :
    EffectiveEpiFamily (fun g : CostructuredArrow ι X => ι.obj g.left) (fun g => g.hom) :=
  effEpi_of_denseAt ι (Functor.IsDense.isDenseAt ι X)

/-- ORG14LNb5gE-3001 (0:50:01) [prop] A family `(Y_a → X)` is strictly epimorphic iff, for every
`Z`, `Hom(X, Z)` is the set of compatible families of the `Hom(Y_a, Z)`: Mathlib's
`EffectiveEpiFamily` is by definition this sheaf condition for the representables. -/
theorem effEpi_iff_sheaf {B : E} {α : Type*} (X : α → E) (π : ∀ a, X a ⟶ B) :
    EffectiveEpiFamily X π ↔ ∀ Y : E, (Presieve.ofArrows X π).IsSheafFor (yoneda.obj Y) := by
  rw [← Sieve.effectiveEpimorphic_family, Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]

/-! ### Strictly and universally epimorphic families -/

/-- A family `(X_a → B)` is strictly and universally epimorphic if the sieve it generates is
covering for the canonical topology (SGA 4 II 2.5: every pullback of it is strictly
epimorphic). -/
def IsUniversalStrictEpi {B : E} {α : Type*} (X : α → E) (π : ∀ a, X a ⟶ B) : Prop :=
  Sieve.generateFamily X π ∈ Sheaf.canonicalTopology E B

/-- A strictly and universally epimorphic family is strictly epimorphic. -/
theorem effEpi_of_universal {B : E} {α : Type*} (X : α → E) (π : ∀ a, X a ⟶ B)
    (h : IsUniversalStrictEpi X π) : EffectiveEpiFamily X π := by
  rw [effEpi_iff_sheaf]
  intro Y
  rw [Presieve.isSheafFor_iff_generate, Sieve.generateFamily_eq]
  exact Sheaf.isSheaf_yoneda_obj Y _ h

/-- ORG14LNb5gE-2829 (0:47:09) [prop] If a strictly and universally epimorphic family `(Y_b → B)`
factors through a family `(X_a → B)`, the latter is again strictly and universally epimorphic. -/
theorem universal_of_factor {B : E} {α β : Type*} {X : α → E} (π : ∀ a, X a ⟶ B) {Y : β → E}
    (ρ : ∀ b, Y b ⟶ B) (h : IsUniversalStrictEpi Y ρ)
    (hf : ∀ b, ∃ a, ∃ u : Y b ⟶ X a, u ≫ π a = ρ b) : IsUniversalStrictEpi X π := by
  refine GrothendieckTopology.superset_covering _ (fun Z f hf0 => ?_) h
  obtain ⟨b, g, rfl⟩ := hf0
  obtain ⟨a, u, hu⟩ := hf b
  exact ⟨a, g ≫ u, by simp [hu]⟩

/-- ORG14LNb5gE-2765 (0:46:05) [prop] (c′) ⇒ (b): if every object is the target of a strictly and
universally epimorphic family with sources in the full subcategory `C`, every `X` is the colimit
of `C/X`. -/
theorem isDenseAt_of_universal [ι.Full]
    (H : ∀ X : E, ∃ (α : Type v) (c : α → C) (π : ∀ a, ι.obj (c a) ⟶ X),
      IsUniversalStrictEpi _ π) (X : E) : ι.isDenseAt X :=
  ⟨denseAtOfEffEpi ι (fun Y => by
    obtain ⟨α, c, π, h⟩ := H Y
    exact effEpi_of_universal _ _ (universal_of_factor _ π h fun b =>
      ⟨CostructuredArrow.mk (π b), 𝟙 _, by simp⟩)) X⟩

/-- ORG14LNb5gE-2572 (0:42:52) [prop], first half (Mathlib): if fibre products exist and
distribute over the coproduct, `(X_a → B)` is strictly epimorphic as soon as `∐ X_a → B` is. -/
def effEpiFamilyOfDesc {B : E} {α : Type*} (X : α → E) (π : ∀ a, X a ⟶ B) [HasCoproduct X]
    [EffectiveEpi (Sigma.desc π)]
    [∀ {Z : E} (g : Z ⟶ ∐ X) (a : α), HasPullback g (Sigma.ι X a)]
    [∀ {Z : E} (g : Z ⟶ ∐ X), HasCoproduct (fun a ↦ pullback g (Sigma.ι X a))]
    [∀ {Z : E} (g : Z ⟶ ∐ X), Epi (Sigma.desc (fun a ↦ pullback.fst g (Sigma.ι X a)))] :
    EffectiveEpiFamilyStruct X π :=
  effectiveEpiFamilyStructOfEffectiveEpiDesc X π

/-- ORG14LNb5gE-2572 (0:42:52) [prop], converse (always true, Mathlib): if `(X_a → B)` is strictly
epimorphic, so is `∐ X_a → B`. -/
theorem effEpi_desc {B : E} {α : Type*} (X : α → E) (π : ∀ a, X a ⟶ B) [HasCoproduct X]
    [EffectiveEpiFamily X π] : EffectiveEpi (Sigma.desc π) := inferInstance

/-- ORG14LNb5gE-1967 (0:32:47) [prop] The comparison lemma: if a small full subcategory
`G : C → D` is cover-dense (generates) for the site `(D, K)`, `Sh(C, J) ≃ Sh(D, K)` for the induced
topology `J`. Stated for the topos `Sh(D, K)`. -/
def generating_sheafEquiv {C D : Type u} [SmallCategory C] [SmallCategory D] (G : C ⥤ D)
    (K : GrothendieckTopology D) [G.IsCoverDense K] [G.IsLocallyFull K] [G.IsLocallyFaithful K] :
    Sheaf (G.inducedTopology K) (Type u) ≌ Sheaf K (Type u) :=
  G.sheafInducedTopologyEquivOfIsCoverDense K (Type u)

end Generating

/-! ## Groups: strictly epimorphic families and the subcategory `{ℤ}` -/

section Groups

/-- `ℤ * ℤ`, the free group on two generators `a = of false`, `b = of true`. -/
abbrev F2 := FreeGroup Bool

/-- The generator `1` of `ℤ`, written multiplicatively. -/
def gen1 : Multiplicative ℤ := Multiplicative.ofAdd (1 : ℤ)

@[simp] theorem toAdd_gen1 : Multiplicative.toAdd gen1 = 1 := rfl


/-- exponent sum of `a = of false`. -/
def ea : F2 →* Multiplicative ℤ := FreeGroup.lift fun x => cond x 1 gen1
/-- exponent sum of `b = of true`. -/
def eb : F2 →* Multiplicative ℤ := FreeGroup.lift fun x => cond x gen1 1

/-- A function `F₂ → ℤ`: the exponent sum in `a` on the elements of exponent sum `0` in `b`,
`0` elsewhere. -/
def kfun (g : F2) : Multiplicative ℤ := if eb g = 1 then ea g else 1

/-- `kfun` is compatible with every relation `g^m = h^n`: it is a compatible family for the family
of all arrows `ℤ → F₂`. -/
theorem kfun_compat (g h : F2) (m n : ℤ) (hgh : g ^ m = h ^ n) : kfun g ^ m = kfun h ^ n := by
  have ha := congrArg (fun x => Multiplicative.toAdd (ea x)) hgh
  have hb := congrArg (fun x => Multiplicative.toAdd (eb x)) hgh
  simp only [map_zpow, toAdd_zpow, smul_eq_mul] at ha hb
  apply Multiplicative.toAdd.injective
  simp only [kfun, toAdd_zpow, smul_eq_mul]
  have key : ∀ x : F2, eb x = 1 ↔ Multiplicative.toAdd (eb x) = 0 := fun x =>
    ⟨fun h => by simp [h], fun h => Multiplicative.toAdd.injective (by simpa using h)⟩
  by_cases hg : eb g = 1 <;> by_cases hh : eb h = 1 <;>
    simp only [hg, hh, ite_true, ite_false, toAdd_one, mul_zero]
  · exact ha
  · rw [(key g).1 hg, mul_zero] at hb
    have hn : n = 0 := (mul_eq_zero.mp hb.symm).resolve_right (fun h0 => hh ((key h).2 h0))
    rw [hn, zero_mul] at ha
    exact ha
  · rw [(key h).1 hh, mul_zero] at hb
    have hm : m = 0 := (mul_eq_zero.mp hb).resolve_right (fun h0 => hg ((key g).2 h0))
    rw [hm, zero_mul] at ha
    exact ha

/-- ... but it is not a homomorphism. -/
theorem kfun_not_hom : ¬ ∃ φ : F2 →* Multiplicative ℤ, ∀ g, φ g = kfun g := by
  rintro ⟨φ, hφ⟩
  have h1 := hφ (FreeGroup.of false * FreeGroup.of true)
  rw [map_mul, hφ, hφ] at h1
  simp [kfun, ea, eb] at h1
  exact absurd (congrArg Multiplicative.toAdd h1) (by simp)

/-- `zpowersHom x` sends the generator to `x`. -/
theorem zpowersHom_gen1 {G : Type} [Group G] (x : G) : zpowersHom G x gen1 = x := by
  simp [zpowersHom_apply]

/-- A homomorphism from `ℤ` is determined by the image of the generator. -/
theorem hom_from_int {G : Type} [Group G] (φ : Multiplicative ℤ →* G) (x : Multiplicative ℤ) :
    φ x = φ gen1 ^ Multiplicative.toAdd x := by
  conv_lhs => rw [← (zpowersHom G).apply_symm_apply φ]
  simp [zpowersHom_apply]
  rfl

/-- `ℤ` as an object of `GrpCat`. -/
abbrev Zg : GrpCat.{0} := GrpCat.of (Multiplicative ℤ)
/-- `ℤ * ℤ` as an object of `GrpCat`. -/
abbrev F2g : GrpCat.{0} := GrpCat.of F2

/-- The full subcategory `C = {ℤ}` of groups. -/
abbrev ιZ : InducedCategory GrpCat.{0} (fun _ : Unit => Zg) ⥤ GrpCat.{0} := inducedFunctor _

/-- A family of arrows `ℤ → F₂` reaching every element of `F₂` is not strictly epimorphic
(`kfun` is a compatible family that does not descend). -/
theorem not_effEpi_of_cover {α : Type} (π : α → (Zg ⟶ F2g))
    (hπ : ∀ g : F2, ∃ a, (π a).hom gen1 = g) : ¬ EffectiveEpiFamily (fun _ => Zg) π := by
  intro H
  let e : α → (Zg ⟶ Zg) := fun a => GrpCat.ofHom (zpowersHom _ (kfun ((π a).hom gen1)))
  have he : ∀ {Z : GrpCat.{0}} (a₁ a₂ : α) (g₁ : Z ⟶ Zg) (g₂ : Z ⟶ Zg),
      g₁ ≫ π a₁ = g₂ ≫ π a₂ → g₁ ≫ e a₁ = g₂ ≫ e a₂ := by
    intro Z a₁ a₂ g₁ g₂ hg
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro z
    have := congrArg (fun φ => φ.hom z) hg
    simp only [GrpCat.hom_comp, MonoidHom.comp_apply] at this
    rw [hom_from_int (π a₁).hom, hom_from_int (π a₂).hom] at this
    simp only [e, GrpCat.hom_comp, MonoidHom.comp_apply, GrpCat.hom_ofHom]
    exact kfun_compat _ _ _ _ this
  apply kfun_not_hom
  refine ⟨(EffectiveEpiFamily.desc _ _ e he).hom, fun g => ?_⟩
  obtain ⟨a, rfl⟩ := hπ g
  have := congrArg (fun φ => φ.hom gen1) (EffectiveEpiFamily.fac _ _ e he a)
  simp only [GrpCat.hom_comp, MonoidHom.coe_comp, Function.comp_apply] at this
  simpa [e] using this

/-- ORG14LNb5gE-2446 (0:40:46) [cex] The family of all the arrows `ℤ → ℤ * ℤ` in groups is not
strictly epimorphic, although it contains the strictly epimorphic family of the two generators
(`effEpi_generators`): enlarging a strictly epimorphic family can make it lose this property. -/
theorem not_effEpi_all :
    ¬ EffectiveEpiFamily (fun f : CostructuredArrow ιZ F2g => ιZ.obj f.left) (fun f => f.hom) :=
  not_effEpi_of_cover (fun f : CostructuredArrow ιZ F2g => f.hom) fun g =>
    ⟨CostructuredArrow.mk (S := ιZ) (Y := (show InducedCategory GrpCat.{0} (fun _ : Unit => Zg) from ()))
      (GrpCat.ofHom (zpowersHom F2 g)), by simp [gen1]⟩

/-- The free group on `F₂`, the free product of copies of `ℤ` indexed by `F₂`, as a cofan. -/
def freeCofan : Cofan (fun _ : F2 => Zg) :=
  Cofan.mk (GrpCat.of (FreeGroup F2)) (fun g => GrpCat.ofHom (zpowersHom _ (FreeGroup.of g)))

/-- The free group on `F₂` is the coproduct of `F₂` copies of `ℤ` in `GrpCat`. -/
def freeCofanIsColimit : IsColimit freeCofan :=
  Cofan.IsColimit.mk _ (fun s => GrpCat.ofHom (FreeGroup.lift fun g => (s.inj g).hom gen1))
    (fun s g => by
      apply GrpCat.hom_ext
      ext
      simp [freeCofan]
      rfl)
    (fun s m hm => by
      apply GrpCat.hom_ext
      apply FreeGroup.ext_hom
      intro g
      have := congrArg (fun φ => φ.hom gen1) (hm g)
      simp only [GrpCat.hom_comp, MonoidHom.coe_comp] at this
      simp only [Function.comp_apply] at this
      have h2 : (zpowersHom (FreeGroup F2) (FreeGroup.of g)) gen1 = FreeGroup.of g :=
        zpowersHom_gen1 _
      change m.hom (zpowersHom (FreeGroup F2) (FreeGroup.of g) gen1) = _ at this
      exact (congrArg _ h2.symm).trans (this.trans (FreeGroup.lift_apply_of (f := fun g => (s.inj g).hom gen1) (x := g)).symm))

/-- In groups, a surjective homomorphism is a strict epimorphism. -/
def effEpiStructOfSurjective {A B : GrpCat.{0}} (p : A ⟶ B) (hp : Function.Surjective p.hom) :
    EffectiveEpiStruct p where
  desc {W} e h := GrpCat.ofHom ((p.hom.liftOfRightInverse (Function.surjInv hp)
    (Function.rightInverse_surjInv hp)) ⟨e.hom, fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      have := h (GrpCat.ofHom (zpowersHom A x)) (GrpCat.ofHom 1) (by
        apply GrpCat.hom_ext
        ext
        simp [hx])
      have := congrArg (fun φ => φ.hom gen1) this
      simpa [gen1] using this⟩)
  fac {W} e h := by
    apply GrpCat.hom_ext
    simp only [GrpCat.hom_comp, GrpCat.hom_ofHom]
    exact MonoidHom.liftOfRightInverse_comp _ _ _ _
  uniq {W} e h m hm := by
    apply GrpCat.hom_ext
    simp only [GrpCat.hom_ofHom]
    exact MonoidHom.eq_liftOfRightInverse _ _ _ e.hom _ m.hom (by rw [← hm]; rfl)

/-- ORG14LNb5gE-2572 (0:42:52) [prop] « false in general »: in groups, the map `∐_{g ∈ F₂} ℤ → F₂`
is a strict epimorphism (it is surjective), but the family `(ℤ → F₂)_{g}` is not strictly
epimorphic. -/
theorem sigma_effEpi_not_family :
    EffectiveEpi (freeCofanIsColimit.desc (Cofan.mk F2g fun g => GrpCat.ofHom (zpowersHom F2 g))) ∧
      ¬ EffectiveEpiFamily (fun _ : F2 => Zg) (fun g => GrpCat.ofHom (zpowersHom F2 g)) := by
  refine ⟨⟨⟨effEpiStructOfSurjective _ fun g => ⟨FreeGroup.of g, ?_⟩⟩⟩,
    not_effEpi_of_cover _ fun g => ⟨g, by simp [gen1]⟩⟩
  have := congrArg (fun φ => φ.hom gen1)
    (freeCofanIsColimit.fac (Cofan.mk F2g fun g => GrpCat.ofHom (zpowersHom F2 g)) ⟨g⟩)
  simp only [GrpCat.hom_comp, MonoidHom.coe_comp, Function.comp_apply] at this
  simp only [freeCofan, Cofan.mk_ι_app, GrpCat.hom_ofHom] at this
  have h2 : (zpowersHom (FreeGroup F2) (FreeGroup.of g)) gen1 = FreeGroup.of g :=
    zpowersHom_gen1 _
  rw [zpowersHom_gen1] at this
  exact (congrArg _ h2.symm).trans this

/-- ORG14LNb5gE-2380 (0:39:40) [cex], condition (c) for `ℤ * ℤ`: the two generators `ℤ → ℤ * ℤ`
form a strictly epimorphic family. -/
theorem effEpi_generators :
    EffectiveEpiFamily (fun _ : Bool => Zg) (fun b => GrpCat.ofHom (zpowersHom F2 (FreeGroup.of b))) :=
  ⟨⟨{ desc := fun e _ => GrpCat.ofHom (FreeGroup.lift fun b => (e b).hom gen1)
      fac := fun e _ b => by
        ext
        simp
        rfl
      uniq := fun e _ m hm => by
        ext x
        simp only [GrpCat.hom_ofHom]
        congr 1
        apply FreeGroup.ext_hom
        intro b
        have := congrArg (fun φ => φ.hom gen1) (hm b)
        simp only [GrpCat.hom_comp, MonoidHom.coe_comp] at this
        simp only [Function.comp_apply] at this
        simpa using this }⟩⟩
/-- ORG14LNb5gE-2380 (0:39:40) [cex] In groups, with `C = {ℤ}`: `ℤ * ℤ` satisfies (c) (the two
generators form a strictly epimorphic family) but is not the colimit of `C/(ℤ * ℤ)` (b). -/
theorem free_c_not_b : EffectiveEpiFamily (fun _ : Bool => Zg)
      (fun b => GrpCat.ofHom (zpowersHom F2 (FreeGroup.of b))) ∧ ¬ ιZ.isDenseAt F2g :=
  ⟨effEpi_generators, fun h => not_effEpi_all (effEpi_of_denseAt ιZ h)⟩

end Groups

/-! ## Subtopoi of `Sh(C, τ)` -/

section Subtopos

variable {C : Type u} [SmallCategory C] {τ τ' : GrothendieckTopology C}

/-- A sheaf for a finer topology is a sheaf. -/
theorem isSheaf_le (h : τ ≤ τ') :
    Presheaf.IsSheaf τ' (A := Type u) ≤ Presheaf.IsSheaf τ := fun P hP =>
  (isSheaf_iff_isSheaf_of_type τ P).2
    (Presieve.isSheaf_of_le _ h ((isSheaf_iff_isSheaf_of_type τ' P).1 hP))

/-- The inclusion `Sh(C, τ') ⊂ Sh(C, τ)` for `τ ≤ τ'`. -/
abbrev sheafIncl (h : τ ≤ τ') : Sheaf τ' (Type u) ⥤ Sheaf τ (Type u) :=
  ObjectProperty.ιOfLE (isSheaf_le h)

/-- The inclusion is fully faithful. -/
def sheafInclFullyFaithful (h : τ ≤ τ') : (sheafIncl h).FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE _

/-- The associated sheaf for `τ'` is left adjoint to the inclusion. -/
def sheafInclAdj (h : τ ≤ τ') :
    (sheafToPresheaf τ (Type u) ⋙ presheafToSheaf τ' (Type u)) ⊣ sheafIncl h :=
  (sheafificationAdjunction τ' (Type u)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf τ (Type u)) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

/-- ORG14LNb5gE-4763 (1:19:23) [prop], one direction: for `τ'` finer than `τ`, `Sh(C, τ')` is a
subtopos of `Sh(C, τ)`: the inclusion is fully faithful with a left exact left adjoint. -/
theorem subtopos_of_le (h : τ ≤ τ') :
    (sheafIncl h).Full ∧ (sheafIncl h).Faithful ∧
      PreservesFiniteLimits (sheafToPresheaf τ (Type u) ⋙ presheafToSheaf τ' (Type u)) :=
  ⟨(sheafInclFullyFaithful h).full, (sheafInclFullyFaithful h).faithful, inferInstance⟩
end Subtopos

end

end Buffalo.Topos.Part07
