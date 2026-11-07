import Buffalo.Topos.Part03a

/-!
# Buffalo, topos theory, part 3b: morphisms of topoi, presheaf topoi, Giraud (1973)

Entries of `docs/buffalo-topos/index.tex` lines 390–535 on morphisms of topoi and the 2-category
of topoi, the initial and final topoi, presheaf topoi and the functors `u^*`, `u_!`, `u_*`, induced
topoi, and the topos-theoretic structure of `Sh(C, J)` (Giraud's theorem, elementary topoi). The
status of each entry is in `docs/buffalo-topos/lean/Part03.json`.

Mathlib has no notion of Grothendieck topos or of geometric morphism; a morphism of topoi is
modelled here by `TopMor` (an adjunction `f^* ⊣ f_*` with `f^*` left exact), between arbitrary
categories, and statements about « a topos » are proved for the categories of sheaves `Sh(C, J)`
on a small site or of presheaves `Ĉ`.
-/

universe w u v

open CategoryTheory Limits TopologicalSpace Opposite Topology TypeCat GrothendieckTopology

namespace Buffalo.Topos.Part03

noncomputable section

/-- URU5jgTvjhU-38154 (10:35:54) [def] A morphism of topoi `f : E → F`: a pair of adjoint functors
`f^* ⊣ f_*`, with `f^* : F → E` left exact. -/
structure TopMor (E : Type*) [Category E] (F : Type*) [Category F] where
  /-- The inverse image `f^*`. -/
  inv : F ⥤ E
  /-- The direct image `f_*`. -/
  dir : E ⥤ F
  /-- `f^* ⊣ f_*`. -/
  adj : inv ⊣ dir
  /-- `f^*` is left exact. -/
  lex : PreservesFiniteLimits inv

namespace TopMor

variable {E : Type*} [Category E] {F : Type*} [Category F] {G : Type*} [Category G]
  {H : Type*} [Category H]

/-- URU5jgTvjhU-38285 (10:38:05) [def] The category `Homtop(E, F)`: an arrow `f → g` is a natural
transformation `f_* → g_*`. -/
instance : Category (TopMor E F) where
  Hom f g := f.dir ⟶ g.dir
  id f := 𝟙 f.dir
  comp a b := a ≫ b

/-- ... equivalently a natural transformation `g^* → f^*` (conjugate transformations). -/
def homEquivInv (f g : TopMor E F) : (f ⟶ g) ≃ (g.inv ⟶ f.inv) :=
  (conjugateEquiv f.adj g.adj).symm

/-- The identity morphism. -/
def id (E : Type*) [Category E] : TopMor E E where
  inv := 𝟭 E
  dir := 𝟭 E
  adj := Adjunction.id
  lex := inferInstance

/-- URU5jgTvjhU-38728 (10:45:28) [prop] Composition: `(gf)_* = g_* f_*`, `(gf)^* = f^* g^*`. -/
def comp (f : TopMor E F) (g : TopMor F G) : TopMor E G where
  inv := g.inv ⋙ f.inv
  dir := f.dir ⋙ g.dir
  adj := g.adj.comp f.adj
  lex := by have := f.lex; have := g.lex; exact comp_preservesFiniteLimits _ _

theorem comp_assoc (f : TopMor E F) (g : TopMor F G) (h : TopMor G H) :
    ((f.comp g).comp h).dir = (f.comp (g.comp h)).dir ∧
      ((f.comp g).comp h).inv = (f.comp (g.comp h)).inv := ⟨rfl, rfl⟩

/-- URU5jgTvjhU-38859 (10:47:39) [prop] Composition is a functor
`Homtop(E, F) × Homtop(F, G) → Homtop(E, G)` (horizontal composition of 2-cells). -/
def compFunctor {E F G : Type u} [Category.{v} E] [Category.{v} F] [Category.{v} G] :
    TopMor E F × TopMor F G ⥤ TopMor E G where
  obj p := p.1.comp p.2
  map {p q} α := NatTrans.hcomp (C := E) (D := F) (E := G) α.1 α.2
  map_id p := NatTrans.ext (funext fun X => by
    change (𝟙 p.1.dir ◫ 𝟙 p.2.dir).app X = 𝟙 _
    simp)
  map_comp α β := NatTrans.exchange (C := E) (D := F) (E := G) α.1 β.1 α.2 β.2

/-- A morphism of topoi is an equivalence if it has a quasi-inverse in the 2-category of topoi. -/
def IsEquiv (f : TopMor E F) : Prop :=
  ∃ g : TopMor F E, Nonempty (f.comp g ≅ id E) ∧ Nonempty (g.comp f ≅ id F)

/-- URU5jgTvjhU-39237 (10:53:57) [prop] `f` is an equivalence of topoi iff `f_*` is an
equivalence of categories, iff `f^*` is. -/
theorem isEquiv_iff (f : TopMor E F) :
    f.IsEquiv ↔ f.dir.IsEquivalence := by
  constructor
  · rintro ⟨g, ⟨e₁⟩, ⟨e₂⟩⟩
    let e₁' : f.dir ⋙ g.dir ≅ 𝟭 E :=
      { hom := e₁.hom, inv := e₁.inv, hom_inv_id := e₁.hom_inv_id, inv_hom_id := e₁.inv_hom_id }
    let e₂' : g.dir ⋙ f.dir ≅ 𝟭 F :=
      { hom := e₂.hom, inv := e₂.inv, hom_inv_id := e₂.hom_inv_id, inv_hom_id := e₂.inv_hom_id }
    exact (CategoryTheory.Equivalence.mk f.dir g.dir e₁'.symm e₂').isEquivalence_functor
  · intro hf
    let g : TopMor F E :=
      { inv := f.dir
        dir := f.dir.inv
        adj := f.dir.asEquivalence.toAdjunction
        lex := inferInstance }
    refine ⟨g, ⟨?_⟩, ⟨?_⟩⟩
    · exact { hom := f.dir.asEquivalence.unitInv, inv := f.dir.asEquivalence.unit,
              hom_inv_id := f.dir.asEquivalence.unitIso.inv_hom_id,
              inv_hom_id := f.dir.asEquivalence.unitIso.hom_inv_id }
    · exact { hom := f.dir.asEquivalence.counit, inv := f.dir.asEquivalence.counitInv,
              hom_inv_id := f.dir.asEquivalence.counitIso.hom_inv_id,
              inv_hom_id := f.dir.asEquivalence.counitIso.inv_hom_id }

theorem dir_isEquivalence_iff_inv (f : TopMor E F) :
    f.dir.IsEquivalence ↔ f.inv.IsEquivalence :=
  ⟨fun _ => f.adj.isEquivalence_left_of_isEquivalence_right,
    fun _ => f.adj.isEquivalence_right_of_isEquivalence_left⟩

/-- An isomorphism of direct images is an isomorphism in `Homtop`. -/
def isoMk {f g : TopMor E F} (e : f.dir ≅ g.dir) : f ≅ g where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- The unique arrow of the one-point category. -/
def ptHom (a b : Discrete PUnit.{w + 1}) : a ⟶ b := eqToHom (Discrete.ext (Subsingleton.elim _ _))

/-- Every cone in the one-point category is a limit. -/
def isLimitPUnit {J : Type*} [Category J] {K : J ⥤ Discrete PUnit.{w + 1}} (c : Cone K) :
    IsLimit c where
  lift s := ptHom _ _

instance preservesFiniteLimits_toPUnit (K : E ⥤ Discrete PUnit.{w + 1}) :
    PreservesFiniteLimits K :=
  ⟨fun _ _ _ => ⟨fun {_} => ⟨fun {_} _ => ⟨isLimitPUnit _⟩⟩⟩⟩

/-- PqCQM3Pcl6Q-5315 (1:28:35) [prop] The empty topos (the one-point category) maps to every
topos `E`. -/
def fromPUnit (E : Type*) [Category E] [HasTerminal E] : TopMor (Discrete PUnit.{w + 1}) E where
  inv := (Functor.const E).obj ⟨PUnit.unit⟩
  dir := (Functor.const _).obj (⊤_ E)
  adj := Adjunction.mkOfHomEquiv
    { homEquiv X _ :=
        { toFun _ := terminal.from X
          invFun _ := ptHom _ _
          left_inv _ := Subsingleton.elim _ _
          right_inv _ := terminal.hom_ext _ _ }
      homEquiv_naturality_left_symm _ _ := Subsingleton.elim _ _
      homEquiv_naturality_right _ _ := terminal.hom_ext _ _ }
  lex := inferInstance

/-- The direct image of a morphism from the empty topos takes terminal values. -/
def dirIsTerminal (f : TopMor (Discrete PUnit.{w + 1}) E) (i : Discrete PUnit.{w + 1}) :
    IsTerminal (f.dir.obj i) :=
  IsTerminal.ofUniqueHom (fun X => f.adj.homEquiv _ _ (ptHom _ _))
    (fun X m => by
      rw [← (f.adj.homEquiv _ _).apply_symm_apply m]
      congr 1)

/-- ... and this morphism is unique up to (unique) isomorphism: the empty topos is initial. -/
theorem fromPUnit_unique (f g : TopMor (Discrete PUnit.{w + 1}) E) : Nonempty (f ≅ g) :=
  ⟨isoMk (Discrete.natIso fun i => (dirIsTerminal f i).uniqueUpToIso (dirIsTerminal g i))⟩

/-- PqCQM3Pcl6Q-5501 (1:31:41) [prop] The empty topos is strictly initial: a topos `E` admitting a
morphism to it is itself empty (all its objects are initial). -/
theorem trivial_of_toPUnit [HasStrictInitialObjects E] (f : TopMor E (Discrete PUnit.{w + 1}))
    (X : E) : Nonempty (IsInitial X) := by
  have := f.lex
  let pt : Discrete PUnit.{w + 1} := ⟨PUnit.unit⟩
  have hpt : IsTerminal pt := IsTerminal.ofUniqueHom (fun _ => ptHom _ _)
    (fun _ _ => Subsingleton.elim _ _)
  have hT : IsTerminal (f.inv.obj pt) := hpt.isTerminalObj f.inv pt
  have hI : IsInitial (f.inv.obj pt) :=
    IsInitial.ofUniqueHom (fun Y => (f.adj.homEquiv _ _).symm (ptHom _ _))
      (fun Y m => (f.adj.homEquiv _ _).injective (Subsingleton.elim _ _))
  have : IsIso (hT.from X) := hI.isIso_to _
  exact ⟨hI.ofIso (asIso (hT.from X)).symm⟩

end TopMor

/-! ## Presheaf topoi and the functors `u^*`, `u_!`, `u_*` -/

section Presheaf

variable {C C' : Type u} [SmallCategory C] [SmallCategory C'] (φ : C ⥤ C')

/-- The restriction `u^* : Ĉ' → Ĉ`, `F ↦ F ∘ u`. -/
abbrev restr : (C'ᵒᵖ ⥤ Type u) ⥤ (Cᵒᵖ ⥤ Type u) := (Functor.whiskeringLeft _ _ _).obj φ.op

/-- PqCQM3Pcl6Q-3520 (0:58:40) [prop] `u^*` commutes with all limits and colimits. -/
theorem restr_preserves : PreservesLimits (restr φ) ∧ PreservesColimits (restr φ) :=
  ⟨inferInstance, inferInstance⟩

/-- ... and is the inverse image of a morphism of topoi `Ĉ → Ĉ'` whose direct image `u_*` is its
right adjoint (right Kan extension). -/
def presheafMor : TopMor (Cᵒᵖ ⥤ Type u) (C'ᵒᵖ ⥤ Type u) where
  inv := restr φ
  dir := φ.op.ran
  adj := φ.op.ranAdjunction (Type u)
  lex := inferInstance

/-- PqCQM3Pcl6Q-4092 (1:08:12) [prop] If `u^*` has a left exact left adjoint `u_!`, then `u_!` is the
inverse image of a morphism of topoi in the opposite direction, of which `u^*` is the direct
image. -/
def presheafMorOp [PreservesFiniteLimits (φ.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ _)] :
    TopMor (C'ᵒᵖ ⥤ Type u) (Cᵒᵖ ⥤ Type u) where
  inv := φ.op.lan
  dir := restr φ
  adj := φ.op.lanAdjunction (Type u)
  lex := inferInstance

/-- PqCQM3Pcl6Q-4217 (1:10:17) [prop] If `C` has finite limits and `u` preserves them, `u_!` is
left exact. -/
theorem lan_lex [HasFiniteLimits C] [PreservesFiniteLimits φ] :
    PreservesFiniteLimits (φ.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ (C'ᵒᵖ ⥤ Type u)) := inferInstance

/-- PqCQM3Pcl6Q-4342 (1:12:22) [prop] A natural transformation `u → v` gives a 2-morphism between
the associated morphisms of topoi (on inverse images, `v^* → u^*`). -/
def restrMap {φ ψ : C ⥤ C'} (α : φ ⟶ ψ) : restr ψ ⟶ restr φ :=
  (Functor.whiskeringLeft _ _ _).map (NatTrans.op α)

/-- PqCQM3Pcl6Q-4407 (1:13:27) [prop] The functor `Hom(C, C') → Homtop(Ĉ, Ĉ')` is fully faithful:
natural transformations `u → v` correspond bijectively to 2-morphisms (`v^* → u^*`). -/
def restrMapEquiv (φ ψ : C ⥤ C') : (φ ⟶ ψ) ≃ (restr ψ ⟶ restr φ) where
  toFun := restrMap
  invFun η :=
    { app c := (η.app (yoneda.obj (ψ.obj c))).app (op c) (𝟙 (ψ.obj c))
      naturality c d k := by
        have h1 := NatTrans.naturality_apply (η.app (yoneda.obj (ψ.obj d))) k.op (𝟙 (ψ.obj d))
        have h2 := congrArg (fun t => t.app (op c) (𝟙 (ψ.obj c))) (η.naturality (yoneda.map (ψ.map k)))
        simp [restr] at h1 h2
        exact h1.symm.trans h2 }
  left_inv α := by
    ext c
    simp [restrMap]
  right_inv η := by
    ext F c x
    obtain ⟨a, rfl⟩ := (yonedaEquiv : (yoneda.obj (ψ.obj c.unop) ⟶ F) ≃
      F.obj (op (ψ.obj c.unop))).surjective x
    have h := congrArg (fun t => t.app c (𝟙 (ψ.obj c.unop))) (η.naturality a)
    simp [restrMap, restr] at h ⊢
    rw [CategoryTheory.yonedaEquiv_apply, h]
    generalize (η.app (yoneda.obj (ψ.obj (unop c)))).app c (𝟙 (ψ.obj (unop c))) = t
    have h3 := NatTrans.naturality_apply a (X := op (ψ.obj c.unop)) (Y := op (φ.obj c.unop))
      t.op (𝟙 (ψ.obj c.unop))
    simp at h3
    exact h3.symm

end Presheaf

/-! ## Points of a topos -/

/-- PqCQM3Pcl6Q-765 (0:12:45) [def] A point of `E` is a morphism of topoi `Set → E`; its inverse
image is the fibre functor. The category of points is opposite to that of fibre functors
(`TopMor.homEquivInv`). -/
abbrev TopPoint (E : Type*) [Category E] := TopMor (Type u) E

/-! ## The final topos -/

section Final

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) {T : C} (hT : IsTerminal T)

/-- PqCQM3Pcl6Q-4541 (1:15:41) / PqCQM3Pcl6Q-4795 (1:19:55) For `E = Sh(C, J)` (`C` with a final
object `T`), the morphism `E → Set` with inverse image the constant sheaf `I ↦ ∐_I 1` and direct
image `Γ = Hom(1, -) = F(T)`. -/
def toFinal : TopMor (Sheaf J (Type u)) (Type u) where
  inv := constantSheaf J (Type u)
  dir := (sheafSections J (Type u)).obj (op T)
  adj := constantSheafAdj J (Type u) hT
  lex := by unfold constantSheaf; infer_instance

/-- URU5jgTvjhU-5053-type statement, presheaf case (PqCQM3Pcl6Q-5053 (1:24:13)): for a presheaf
topos `Ĉ` (locally connected), the inverse image `Set → Ĉ` (constant presheaves) commutes with all
limits, in particular with infinite products. -/
theorem const_preservesLimits : PreservesLimits (Functor.const Cᵒᵖ : Type u ⥤ (Cᵒᵖ ⥤ Type u)) :=
  inferInstance

/-- PqCQM3Pcl6Q-3328 (0:55:28) [prop] In `Ĉ`, `Γ(F) = Hom(1, F) = lim F` (the sections). -/
def presheafGlobalSections (F : Cᵒᵖ ⥤ Type u) :
    F.sections ≃ ((Functor.const Cᵒᵖ).obj PUnit.{u + 1} ⟶ F) :=
  F.sectionsEquivHom PUnit

end Final

/-! ## Presheaf topoi: limits, points, generators -/

section PresheafTopos

variable {C : Type u} [SmallCategory C]

/-- URU5jgTvjhU-36436 (10:07:16) [prop] `Ĉ` is a topos with the exactness properties of `Set`:
limits and colimits (computed argumentwise), internal `Hom`, a subobject classifier, and every
presheaf is a colimit of representables. -/
theorem presheaf_topos :
    HasLimits (Cᵒᵖ ⥤ Type u) ∧ HasColimits (Cᵒᵖ ⥤ Type u) ∧
      Nonempty (MonoidalClosed (Cᵒᵖ ⥤ Type u)) ∧ HasSubobjectClassifier (Cᵒᵖ ⥤ Type u) :=
  ⟨inferInstance, inferInstance, ⟨inferInstance⟩, inferInstance⟩

/-- ... (every presheaf is the colimit of the representables over it). -/
def presheaf_colimit_representables (P : Cᵒᵖ ⥤ Type u) :
    IsColimit (Presheaf.tautologicalCocone P) :=
  Presheaf.isColimitTautologicalCocone P

/-- URU5jgTvjhU-36693 (10:11:33) [prop] / PqCQM3Pcl6Q-9000 (2:30:00) [prop] For `X ∈ C`,
`F ↦ F(X)` is a point of `Ĉ` (`pointBot X`, whose fibre functor is evaluation at `X`), and these
points form a conservative family: `Ĉ` has enough points. (Every point's fibre functor is by
definition the filtered colimit of evaluations over its category of elements,
`Point.presheafFiber`.) -/
def pointBot_eval (X : C) :
    (pointBot.{u} X).presheafFiber (A := Type u) ≅ (evaluation Cᵒᵖ (Type u)).obj (op X) :=
  pointBotPresheafFiberIso X (Type u)

theorem presheaf_enoughPoints :
    (pointsBot.{u} C).IsConservativeFamilyOfPoints ∧ HasEnoughPoints.{u} (⊥ : GrothendieckTopology C) :=
  ⟨isConservative_pointsBot C, inferInstance⟩

/-- PqCQM3Pcl6Q-9189 (2:33:09) [prop], one direction: the fibre functor of a point coming from `C`
(evaluation) commutes with all limits. -/
theorem eval_preservesLimits (X : C) : PreservesLimits ((evaluation Cᵒᵖ (Type u)).obj (op X)) :=
  inferInstance

/-- URU5jgTvjhU-37400 (10:23:20) [prop] / PqCQM3Pcl6Q-6237 (1:43:57), presheaf case: for a presheaf
`A`, the induced topos `Ĉ/A` is again a presheaf topos, on the category of elements of `A`. -/
def presheafOverEquiv (A : Cᵒᵖ ⥤ Type u) :
    Over A ≌ ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type u) :=
  overEquivPresheafCostructuredArrow A

/-- URU5jgTvjhU-37930 (10:32:10) [prop], presheaf case: a functor `Ĉ → Set` commuting with colimits
has a right adjoint. -/
theorem presheaf_isLeftAdjoint (L : (Cᵒᵖ ⥤ Type u) ⥤ Type u) [PreservesColimits L] :
    L.IsLeftAdjoint :=
  Presheaf.isLeftAdjoint_of_preservesColimits.{0} L

/-- PqCQM3Pcl6Q-3770 (1:02:50) [prop] `u^*` has a left adjoint `u_!` and a right adjoint `u_*`;
an inverse image with a left adjoint commutes with all limits. -/
theorem restr_adjoints {C' : Type u} [SmallCategory C'] (φ : C ⥤ C') :
    (restr φ).IsRightAdjoint ∧ (restr φ).IsLeftAdjoint :=
  Part01.restriction_adjoints φ

theorem preservesLimits_of_leftAdjoint {E F : Type*} [Category E] [Category F] (f : TopMor E F)
    {L : E ⥤ F} (h : L ⊣ f.inv) : PreservesLimits f.inv :=
  h.rightAdjoint_preservesLimits

/-- PqCQM3Pcl6Q-3770 (1:02:50) [ex] For `Δ_{≤ n} ⊂ Δ`, `u^*` is truncation of simplicial sets,
`u_!` the skeleton and `u_*` the coskeleton (Kan extensions). -/
def skeleton_adj (n : ℕ) : SSet.Truncated.sk.{u} n ⊣ SSet.truncation.{u} n := SSet.skAdj n

def coskeleton_adj (n : ℕ) : SSet.truncation.{u} n ⊣ SSet.Truncated.cosk.{u} n := SSet.coskAdj n

end PresheafTopos

/-! ## Topoi of sheaves on a site: Giraud's axioms, elementary topoi -/

section Site

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- URU5jgTvjhU-35193 (9:46:33) [thm] Giraud, the direction « sheaves on a site »: `Sh(C, J)`
embeds fully faithfully in `Ĉ`, with a left exact left adjoint (the associated sheaf). -/
theorem sheaf_reflective :
    Nonempty (sheafToPresheaf J (Type u)).FullyFaithful ∧
      Nonempty (presheafToSheaf J (Type u) ⊣ sheafToPresheaf J (Type u)) ∧
      PreservesFiniteLimits (presheafToSheaf J (Type u)) :=
  ⟨⟨fullyFaithfulSheafToPresheaf J _⟩, ⟨sheafificationAdjunction J _⟩, inferInstance⟩

/-- URU5jgTvjhU-35724 (9:55:24) [prop] In `Sh(C, J)`, internal `Hom` exists (cartesian closed). -/
theorem sheaf_closed : Nonempty (MonoidalClosed (Sheaf J (Type u))) := ⟨inferInstance⟩

/-- URU5jgTvjhU-35789 (9:56:29) [prop] In `Sh(C, J)`, `Z ↦ Sub(Z)` is representable: there is a
subobject classifier `P_E = Ω`. -/
theorem sheaf_classifier : HasSubobjectClassifier (Sheaf J (Type u)) := inferInstance

/-- URU5jgTvjhU-36055 (10:00:55) [prop] / URU5jgTvjhU-35591 (9:53:11), the direction
« Grothendieck topos ⇒ elementary topos »: `Sh(C, J)` has finite limits, is cartesian closed and
has a subobject classifier (and has all small limits). -/
theorem sheaf_elementary :
    HasFiniteLimits (Sheaf J (Type u)) ∧ Nonempty (MonoidalClosed (Sheaf J (Type u))) ∧
      HasSubobjectClassifier (Sheaf J (Type u)) ∧ HasLimits (Sheaf J (Type u)) :=
  ⟨inferInstance, ⟨inferInstance⟩, inferInstance, inferInstance⟩

/-- URU5jgTvjhU-35860 (9:57:40) [prop], the direction « representable ⇒ sends colimits to
limits ». -/
theorem representable_preservesLimits (X : Sheaf J (Type u)) :
    PreservesLimits (yoneda.obj X) := inferInstance

/-- PqCQM3Pcl6Q-6357 (1:45:57) [prop] / PqCQM3Pcl6Q-6421 (1:47:01) The localization functor
`j^* : E → E/X'`, `Y ↦ Y × X'`, has the left adjoint `j_!` forgetting the map to `X'`, hence
commutes with limits. -/
def localization_adj (X' : Sheaf J (Type u)) : Over.forget X' ⊣ Over.star X' := Over.forgetAdjStar X'

theorem localization_preservesLimits (X' : Sheaf J (Type u)) : PreservesLimits (Over.star X') :=
  (Over.forgetAdjStar X').rightAdjoint_preservesLimits

end Site

/-- PqCQM3Pcl6Q-6421 (correction). The localization morphism `E/X' → E` is an embedding (its `j_!`
is fully faithful, as for an open immersion) only when `X'` is subterminal: for `E = Set` and
`X' = Bool`, `j_!` (forget the map to `X'`) is not full. In general `E/X' → E` is the analogue of an
étale map. -/
theorem overForget_not_full : ¬ (Over.forget (Bool : Type)).Full := by
  intro h
  let A : Over (Bool : Type) := Over.mk (↾fun _ : PUnit.{1} => true)
  let B : Over (Bool : Type) := Over.mk (↾fun _ : PUnit.{1} => false)
  obtain ⟨f, -⟩ := (Over.forget (Bool : Type)).map_surjective (X := A) (Y := B) (𝟙 PUnit)
  have := congrArg (fun k => k PUnit.unit) (Over.w f)
  simp [A, B] at this

end

end Buffalo.Topos.Part03
