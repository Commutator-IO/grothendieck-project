import Buffalo.Topos.Part02
import Buffalo.Topos.Part03

/-!
# Buffalo, topos theory, part 7b: classifying topoi, examples and special cases (12 July 1973)

Entries of `docs/buffalo-topos/index.tex` lines 965–1114 (video `ORG14LNb5gE`, 2:28:03–5:16:37)
on the classifying topos of objects and its subtopoi, flat functors, `B_G`, torsors, connected
rings, elementary topoi, flatness, hypertopoi and universes. Mathlib has no Grothendieck topos as
such and no classifying topos; each entry is checked in a faithful special case (points, i.e.
models in `Set`, or a presheaf or sheaf topos), as said in `docs/buffalo-topos/lean/Part07.json`.
-/

universe u v w

open CategoryTheory Limits TopologicalSpace Opposite Topology TypeCat GrothendieckTopology

namespace Buffalo.Topos.Part07

noncomputable section

/-- ORG14LNb5gE-8883 (2:28:03) [prop] `u : X → Y` is an epimorphism iff `Y ⊔_X Y → Y` is an
isomorphism (`Part02.epi_iff_isIso_codiagonal`). -/
theorem epi_iff_codiagonal {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) [HasPushout f f] :
    Epi f ↔ IsIso (pushout.desc (f := f) (g := f) (𝟙 Y) (𝟙 Y) rfl) :=
  Part02.epi_iff_isIso_codiagonal f

/-- ORG14LNb5gE-15238 (4:13:58) [prop], for a presheaf target `Ĉ'`: `φ : C → C'` (with `C` finitely
complete) is left exact iff its colimit-preserving extension `φ_! : Ĉ → Ĉ'` is. -/
theorem lex_iff_extension_lex {C C' : Type u} [SmallCategory C] [SmallCategory C']
    [HasFiniteLimits C] (φ : C ⥤ C') :
    PreservesFiniteLimits φ ↔
      PreservesFiniteLimits (φ.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ (C'ᵒᵖ ⥤ Type u)) :=
  Part03.lan_lex_iff φ

/-- ORG14LNb5gE-12268 (3:24:28) [prop] A group morphism `G → G'` induces by restriction a functor
`B_{G'} → B_G` (presheaves on the one-object categories) with both adjoints: an essential morphism
`B_G → B_{G'}`. -/
theorem res_essential {G G' : Type} [Group G] [Group G'] (f : G →* G') :
    (Part03.restr (SingleObj.mapHom G G' f)).IsRightAdjoint ∧
      (Part03.restr (SingleObj.mapHom G G' f)).IsLeftAdjoint :=
  Part03.restr_adjoints _

/-- ORG14LNb5gE-9433 (2:37:13) [prop], the case of points: in `Set`, filtered colimits commute with
finite limits, so a filtered colimit of left exact functors to `Set` is left exact. -/
theorem filtered_colim_lex {K : Type u} [SmallCategory K] [IsFiltered K] :
    PreservesFiniteLimits (colim : (K ⥤ Type u) ⥤ Type u) := inferInstance

/-- ORG14LNb5gE-9758 (2:42:38) [ex] The subobjects of the terminal object of `B = [FinSet, Set]` are
the upward-closed classes of finite sets (`P A → (A → B) → P B`); there are exactly three: `∅`, the
nonempty sets (the image of `X → e`) and all sets. -/
theorem subterminal_classifying (P : FintypeCat.{u} → Prop)
    (hP : ∀ (A B : FintypeCat.{u}) (_ : A ⟶ B), P A → P B) :
    P = (fun _ => False) ∨ P = (fun A : FintypeCat.{u} => Nonempty (A : Type u)) ∨ P = (fun _ => True) := by
  by_cases h0 : ∃ A : FintypeCat.{u}, IsEmpty A ∧ P A
  · obtain ⟨A, hA, hPA⟩ := h0
    right; right
    funext B
    simp only [eq_iff_iff, iff_true]
    exact hP A B (FintypeCat.homMk (fun a => isEmptyElim a)) hPA
  · by_cases h1 : ∃ A, P A
    · obtain ⟨A, hPA⟩ := h1
      right; left
      funext B
      apply propext
      constructor
      · intro hB
        by_contra hne
        exact h0 ⟨B, not_nonempty_iff.mp hne, hB⟩
      · rintro ⟨b⟩
        exact hP A B (FintypeCat.homMk fun _ => b) hPA
    · left
      funext B
      simp only [eq_iff_iff, iff_false]
      exact fun hB => h1 ⟨B, hB⟩

/-- ORG14LNb5gE-10017 (2:46:57) [ex], points of `B*`: `x → e` is an epimorphism of sets iff `x` is
nonempty. -/
theorem epi_toUnit_iff (X : Type u) : Epi (↾(fun _ : X => PUnit.unit.{u+1})) ↔ Nonempty X := by
  rw [epi_iff_surjective]
  exact ⟨fun h => ⟨(h PUnit.unit).choose⟩, fun ⟨x⟩ _ => ⟨x, rfl⟩⟩

/-- ORG14LNb5gE-10210 (2:50:10) [ex], points of `Φ₀₁`: `x → e` is a monomorphism iff `x` has at most
one element. -/
theorem mono_toUnit_iff (X : Type u) : Mono (↾(fun _ : X => PUnit.unit.{u+1})) ↔ Subsingleton X := by
  rw [mono_iff_injective]
  exact ⟨fun h => ⟨fun a b => h rfl⟩, fun h a b _ => Subsingleton.elim a b⟩

/-- ORG14LNb5gE-10342 (2:52:22) [ex], points of `Φ₁ = Φ₀₁ ∩ B*`: `x → e` is mono and epi, i.e. an
isomorphism, iff `x` has exactly one element. -/
theorem isIso_toUnit_iff (X : Type u) :
    IsIso (↾(fun _ : X => PUnit.unit.{u+1})) ↔ Nonempty X ∧ Subsingleton X := by
  rw [isIso_iff_bijective]
  exact ⟨fun h => ⟨⟨(h.2 PUnit.unit).choose⟩, ⟨fun a b => h.1 rfl⟩⟩,
    fun ⟨⟨x⟩, hs⟩ => ⟨fun a b _ => Subsingleton.elim a b, fun _ => ⟨x, rfl⟩⟩⟩

/-- ORG14LNb5gE-9888 (2:44:48) [ex], the point of `Φ₀`: a set is initial iff it is empty. -/
theorem isInitial_iff_isEmpty (X : Type u) : Nonempty (IsInitial X) ↔ IsEmpty X := by
  constructor
  · rintro ⟨h⟩
    refine ⟨fun x => ?_⟩
    have := h.hom_ext (↾(fun _ => ULift.up true) : X ⟶ ULift.{u} Bool) (↾(fun _ => ULift.up false))
    have := congrArg (fun f => (f x).down) this
    simp at this
  · intro h
    exact ⟨IsInitial.ofUniqueHom (fun Y => ↾(fun x => isEmptyElim x))
      (fun Y f => by ext x; exact isEmptyElim x)⟩

/-- ORG14LNb5gE-10727 (2:58:47) [prop] Every `T₀` space embeds in a product of copies of the
Sierpiński space `Prop` (Mathlib `productOfMemOpens_isEmbedding`). -/
theorem t0_embeds (X : Type u) [TopologicalSpace X] [T0Space X] :
    Topology.IsEmbedding (productOfMemOpens X) := productOfMemOpens_isEmbedding X

/-- ORG14LNb5gE-10665 (2:57:45) [ex], for spaces: a continuous map to the Sierpiński space is the
same as an open subset. -/
def sierpinski_classifies_opens (X : Type u) [TopologicalSpace X] :
    {p : X → Prop // Continuous p} ≃ Opens X where
  toFun q := ⟨{x | q.1 x}, continuous_Prop.1 q.2⟩
  invFun U := ⟨fun x => x ∈ U, continuous_Prop.2 U.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- ORG14LNb5gE-10793 (2:59:53) [prop], for `Ĉ`: the topologies on `C` (the subtopoi of `Ĉ`) form a
complete lattice. -/
theorem topologies_completeLattice (C : Type u) [Category.{v} C] :
    Nonempty (CompleteLattice (GrothendieckTopology C)) := ⟨inferInstance⟩

/-- ORG14LNb5gE-11198 (3:06:38) [ex] `ℤ` is the universal group: `Hom(ℤ, G) ≃ G`. -/
def intHomEquiv (G : Type u) [Group G] : (Multiplicative ℤ →* G) ≃ G := (zpowersHom G).symm

/-- ORG14LNb5gE-11403 (3:10:03) [prop], for a presheaf target: `φ` is flat iff its extension `φ_!`
is left exact; if `C` has finite limits, flat means left exact. -/
theorem flat_iff {C D : Type u} [SmallCategory C] [SmallCategory D] [HasFiniteLimits C] (φ : C ⥤ D) :
    (RepresentablyFlat φ ↔ PreservesFiniteLimits (φ.op.lan : (Cᵒᵖ ⥤ Type u) ⥤ (Dᵒᵖ ⥤ Type u))) ∧
    (RepresentablyFlat φ ↔ PreservesFiniteLimits φ) :=
  ⟨Buffalo.Topos.Part03.lan_lex_iff_flat φ,
    ⟨fun _ => preservesFiniteLimits_of_flat φ, fun _ => flat_of_preservesFiniteLimits φ⟩⟩

/-- ORG14LNb5gE-12140 (3:22:20) [prop], for `S = Set`: the forgetful functor `B_G → Set` is faithful
and commutes with all limits (and colimits). -/
theorem action_forget (G : Type u) [Group G] :
    (Action.forget (Type u) G).Faithful ∧ PreservesLimits (Action.forget (Type u) G) ∧
      PreservesColimits (Action.forget (Type u) G) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- ORG14LNb5gE-12397 (3:26:37) [def] The universal torsor: `G` acting on itself by left
translations. -/
def universalTorsor (G : Type u) [Group G] : Action (Type u) G := Action.ofMulAction G G

/-- ... the right translations commute with the left action (the right action of `p^*G`). -/
theorem right_translation_equivariant (G : Type u) [Group G] (g h x : G) :
    g • (x * h) = (g • x) * h := by simp [smul_eq_mul, mul_assoc]

/-- ORG14LNb5gE-15494 (4:18:14) [prop], connectedness: for `C` with finite limits (a terminal object
suffices), the constant functor `Set → Ĉ` is fully faithful. -/
theorem const_fullyFaithful (C : Type u) [SmallCategory C] [HasTerminal C] :
    (Functor.const Cᵒᵖ : Type u ⥤ (Cᵒᵖ ⥤ Type u)).Full ∧
      (Functor.const Cᵒᵖ : Type u ⥤ (Cᵒᵖ ⥤ Type u)).Faithful := by
  have : IsConnected C := isConnected_of_hasTerminal C
  exact ⟨inferInstance, inferInstance⟩

/-- ... acyclicity: `Γ` is evaluation at the terminal object, which commutes with colimits. -/
theorem eval_terminal_colimits (C : Type u) [SmallCategory C] [HasTerminal C] :
    PreservesColimits ((evaluation Cᵒᵖ (Type u)).obj (Opposite.op (⊤_ C))) := inferInstance

/-- ORG14LNb5gE-15751 (4:22:31) [def] An elementary topos: finite limits, cartesian closed, a
subobject classifier. -/
structure IsElementaryTopos (E : Type u) [Category.{v} E] [MonoidalCategory E] : Prop where
  cartesian : Nonempty (CartesianMonoidalCategory E)
  finiteLimits : HasFiniteLimits E
  closed : Nonempty (MonoidalClosed E)
  classifier : HasSubobjectClassifier E

/-- `Sh(C, J)` is an elementary topos. -/
theorem sheaf_isElementaryTopos {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    IsElementaryTopos (Sheaf J (Type u)) := ⟨⟨inferInstance⟩, inferInstance, ⟨inferInstance⟩, inferInstance⟩


/-- ORG14LNb5gE-18019 (5:00:19) [prop] In `Set`, an arbitrary product of surjections is surjective
(the failure in other topoi: `Part02.product_of_epis_not_epi`). -/
theorem pi_surjective {ι : Type u} {X Y : ι → Type v} (f : ∀ i, X i → Y i)
    (hf : ∀ i, Function.Surjective (f i)) : Function.Surjective (fun (x : ∀ i, X i) i => f i (x i)) :=
  fun y => ⟨fun i => (hf i (y i)).choose, funext fun i => (hf i (y i)).choose_spec⟩

/-- ORG14LNb5gE-18084 (5:01:24) [prop], for `Ĉ`: the constant functor has a left adjoint
(`colim`, i.e. `π₀`), so `Ĉ → pt` is essential... -/
def const_leftAdjoint (C : Type u) [SmallCategory C] :
    (colim : (Cᵒᵖ ⥤ Type u) ⥤ Type u) ⊣ Functor.const Cᵒᵖ := colimConstAdj

/-- ... and the constant functor commutes with all limits. -/
theorem const_preservesLimits (C : Type u) [SmallCategory C] :
    PreservesLimits (Functor.const Cᵒᵖ : Type u ⥤ (Cᵒᵖ ⥤ Type u)) :=
  colimConstAdj.rightAdjoint_preservesLimits

/-- `Set` is Karoubian. -/
instance types_isIdempotentComplete : IsIdempotentComplete (Type u) :=
  (Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent _).2
    fun _ _ _ => inferInstance

/-- ORG14LNb5gE-18411 (5:06:51) [prop], why the Karoubian hypothesis: `Ĉ` only determines `C` up to
its Karoubi envelope, `Ĉ ≃ (Kar C)^`. -/
def presheaf_karoubi (C : Type u) [SmallCategory C] :
    (Cᵒᵖ ⥤ Type u) ≌ (Idempotents.Karoubi Cᵒᵖ ⥤ Type u) :=
  Idempotents.karoubiUniversal Cᵒᵖ (Type u)

/-- ORG14LNb5gE-18604 (5:10:04) [prop] For `D` with finite limits, a functor `D → Set` (a point of
`D̂`) is left exact iff it is an ind-object of `Dᵒᵖ`: `Hom_lex(D, Set) = Ind(Dᵒᵖ)`. -/
theorem points_indObjects (D : Type u) [SmallCategory D] [HasFiniteLimits D]
    (A : Dᵒᵖᵒᵖ ⥤ Type u) : IsIndObject A ↔ PreservesFiniteLimits A :=
  isIndObject_iff_preservesFiniteLimits A

/-- ORG14LNb5gE-18997 (5:16:37) [prop], in the type theory of Lean: the cardinal of the universe
`Type u` is strongly inaccessible in `Type (u+1)`. -/
theorem universe_inaccessible : Cardinal.IsInaccessible Cardinal.univ.{u, u + 1} :=
  Cardinal.IsInaccessible.univ

/-- ORG14LNb5gE-9568 (2:39:28) [prop] `FinSet` is Karoubian, so the essential points of `B`
(objects of the Karoubi envelope of `FinSetᵒᵖ`) are the finite sets. -/
instance fintypeCat_isIdempotentComplete : IsIdempotentComplete FintypeCat.{u} :=
  (Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent _).2
    fun _ _ _ => inferInstance

/-- ORG14LNb5gE-5906 (1:38:26) [prop], `I` a point: `FinSetᵒᵖ` has finite limits (the free
finite-product category on one object is also finitely complete). -/
theorem finSetOp_finiteLimits : HasFiniteLimits FintypeCat.{u}ᵒᵖ := inferInstance

/-- ORG14LNb5gE-10145 (2:49:05) [ex] For the topology `⊤` (all sieves cover: the empty subtopos)
every sheaf is terminal at every object: only the trivial model. -/
theorem top_sheaf_terminal {C : Type u} [Category.{v} C]
    (F : Sheaf (⊤ : GrothendieckTopology C) (Type w)) (U : C) :
    Nonempty (IsTerminal (F.1.obj (op U))) := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 F.2
  have := hF (Sieve.generate (Presieve.ofArrows (X := U) (Empty.elim : Empty → C)
    (fun e => Empty.instIsEmpty.elim e))) (by trivial)
  rw [← Presieve.isSheafFor_iff_generate] at this
  exact ⟨Presieve.isTerminal_of_isSheafFor_empty_presieve U F.1 this⟩

/-- ORG14LNb5gE-16919 (4:41:59) [prop], for affine `X`: the constructible topology on `Spec R` is
quasi-compact (same points). -/
theorem constructible_compact (R : Type u) [CommRing R] :
    CompactSpace (WithConstructibleTopology (PrimeSpectrum R)) := inferInstance

/-- ORG14LNb5gE-17111 (4:45:11) [def] Absolutely flat rings: all modules are flat. -/
def IsAbsolutelyFlat (R : Type u) [CommRing R] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M], Module.Flat R M

/-- Fields are absolutely flat. -/
theorem field_absolutelyFlat (K : Type u) [Field K] : IsAbsolutelyFlat K :=
  fun _ _ _ => inferInstance

/-- ORG14LNb5gE-17307 (4:48:27) [prop], punctual topos: `M` is flat iff `J ⊗ M → M` is injective
for every finitely generated ideal `J`. -/
theorem flat_criterion (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔ ∀ ⦃I : Ideal R⦄, I.FG → Function.Injective (I.subtype.rTensor M) :=
  Module.Flat.iff_rTensor_injective

/-- ORG14LNb5gE-13957 (3:52:37) [prop] Clopens of `Spec R` ↔ complementary idempotents: `Spec R` is
connected iff the only idempotents are `0` and `1` (and `0 ≠ 1`). -/
def clopens_idempotents (R : Type u) [CommRing R] :
    {e : R × R // e.1 * e.2 = 0 ∧ e.1 + e.2 = 1} ≃o Clopens (PrimeSpectrum R) :=
  PrimeSpectrum.mulZeroAddOneEquivClopens

/-- ORG14LNb5gE-13187 (3:39:47) [prop], trivial topology: for `t ≅ s`, `Isom(s, t)` is a torsor under
`Aut(s)` acting by `g • f = g⁻¹ ≫ f`. -/
theorem iso_torsor {C : Type u} [Category.{v} C] {s t : C} (f f' : s ≅ t) :
    ∃! g : s ≅ s, g.symm ≪≫ f = f' := by
  refine ⟨(f ≪≫ f'.symm), by ext; simp, fun g hg => ?_⟩
  ext
  rw [← hg]
  simp


section Contracted

variable (G : Type u) [Group G]


/-- The relation `(p, x) ∼ (p g⁻¹, g x)` on `P × X`. -/
def contractedSetoid (P X : Type u) [MulAction Gᵐᵒᵖ P] [MulAction G X] : Setoid (P × X) where
  r a b := ∃ g : G, b = (MulOpposite.op g⁻¹ • a.1, g • a.2)
  iseqv := {
    refl := fun a => ⟨1, by simp⟩
    symm := fun {a b} ⟨g, h⟩ => ⟨g⁻¹, by subst h; simp [smul_smul]⟩
    trans := fun {a b c} ⟨g, h⟩ ⟨g', h'⟩ => ⟨g' * g, by
      subst h; subst h'
      ext
      · simp only [smul_smul, mul_inv_rev, MulOpposite.op_mul, MulOpposite.op_inv]
      · simp [smul_smul]⟩ }

/-- ORG14LNb5gE-11601 (3:13:21) [def] The contracted product `P ∧^G X`: the quotient of `P × X` by
`(pg, x) ∼ (p, gx)` (`P` a right, `X` a left `G`-set). -/
def ContractedProduct (P X : Type u) [MulAction Gᵐᵒᵖ P] [MulAction G X] : Type u :=
  Quotient (contractedSetoid G P X)

/-- `[pg, x] = [p, gx]`. -/
theorem contracted_rel (P X : Type u) [MulAction Gᵐᵒᵖ P] [MulAction G X] (p : P) (g : G) (x : X) :
    (Quotient.mk (contractedSetoid G P X) (MulOpposite.op g • p, x) : ContractedProduct G P X) =
      Quotient.mk _ (p, g • x) :=
  Quotient.sound ⟨g, by simp [smul_smul]⟩

/-- ORG14LNb5gE-11533 (3:12:13) [prop] The extension `P ↦ P ∧^G X` sends the representable `G` to
`X`. -/
def contractedRegular (X : Type u) [MulAction G X] : ContractedProduct G G X ≃ X where
  toFun := Quotient.lift (fun a : G × X => a.1 • a.2) (fun a b ⟨g, h⟩ => by
    subst h; simp [smul_smul, MulOpposite.smul_eq_mul_unop])
  invFun x := Quotient.mk _ (1, x)
  left_inv := by
    rintro ⟨p, x⟩
    refine Quotient.sound ⟨p⁻¹, ?_⟩
    show (p, x) = (MulOpposite.op p⁻¹⁻¹ • (1 : G), p⁻¹ • p • x)
    simp [MulOpposite.smul_eq_mul_unop]
  right_inv x := by simp

/-- ORG14LNb5gE-11667 (3:14:27) [prop], terminal object: `pt ∧^G X ≃ X/G`, so the extension
preserves the terminal object iff `X` is nonempty and transitive. -/
def contractedPoint (X : Type u) [MulAction G X] :
    ContractedProduct G PUnit X ≃ MulAction.orbitRel.Quotient G X where
  toFun := Quotient.lift (fun a : PUnit × X => (Quotient.mk _ a.2 : MulAction.orbitRel.Quotient G X))
    (fun a b ⟨g, h⟩ => by
      subst h
      exact Quotient.sound ⟨g⁻¹, by simp [smul_smul]⟩)
  invFun := Quotient.lift (fun x => Quotient.mk _ (PUnit.unit, x)) (fun x y ⟨g, h⟩ => by
    subst h
    exact Quotient.sound ⟨g⁻¹, by simp [smul_smul]⟩)
  left_inv := by
    rintro ⟨⟨⟩, x⟩
    rfl
  right_inv := by
    rintro ⟨x⟩
    rfl
end Contracted

end

end Buffalo.Topos.Part07
