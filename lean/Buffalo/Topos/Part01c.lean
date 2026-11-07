import Buffalo.Topos.Part01a

/-!
# Buffalo, topos theory, part 1c: direct and inverse images, stalks (11 May 1973)

Entries of `docs/buffalo-topos/index.tex` from « Direct and inverse images » to « Stalks and
epimorphisms » (video `URU5jgTvjhU`, 3:24:08–4:55:12). The status of each entry is in
`docs/buffalo-topos/lean/Part01.json`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace Buffalo.Topos.Part01

noncomputable section

variable {X Y : TopCat.{u}}

/-! ## Direct and inverse images -/

/-- URU5jgTvjhU-12248 (3:24:08) [def] For `f : X → Y`, an `f`-morphism `G → F` is a family
`G(V) → F(U)`, for `f(U) ⊆ V`, compatible with the restrictions. -/
structure FMorphism (f : X ⟶ Y) (G : Y.Presheaf (Type u)) (F : X.Presheaf (Type u)) where
  /-- The map `G(V) → F(U)` for `U ⊆ f⁻¹(V)`. -/
  app : ∀ (U : Opens X) (V : Opens Y), U ≤ (Opens.map f).obj V → G.obj (op V) → F.obj (op U)
  /-- Compatibility with the restrictions. -/
  compat : ∀ (U U' : Opens X) (V V' : Opens Y) (hU : U' ≤ U) (hV : V' ≤ V)
    (h : U ≤ (Opens.map f).obj V) (h' : U' ≤ (Opens.map f).obj V') (s : G.obj (op V)),
    F.map (homOfLE hU).op (app U V h s) = app U' V' h' (G.map (homOfLE hV).op s)

theorem FMorphism.ext' {f : X ⟶ Y} {G : Y.Presheaf (Type u)} {F : X.Presheaf (Type u)}
    {φ ψ : FMorphism f G F} (h : φ.app = ψ.app) : φ = ψ := by
  cases φ; cases ψ; cases h; rfl

/-- URU5jgTvjhU-12440 (3:27:20) [prop] and URU5jgTvjhU-12768 (3:32:48) [prop] An `f`-morphism
`G → F` is equivalent to a compatible family `G(V) → F(f⁻¹(V))`, that is, to a morphism of
presheaves `G → f_*F`. -/
def fMorphismEquiv (f : X ⟶ Y) (G : Y.Presheaf (Type u)) (F : X.Presheaf (Type u)) :
    FMorphism f G F ≃ (G ⟶ (TopCat.Presheaf.pushforward (Type u) f).obj F) where
  toFun φ :=
    { app := fun V => ↾fun s => φ.app _ V.unop le_rfl s
      naturality := fun V V' i => by
        ext s
        exact (φ.compat _ _ _ _ ((Opens.map f).monotone i.unop.le) i.unop.le le_rfl le_rfl s).symm }
  invFun α :=
    { app := fun U V h s => F.map (homOfLE h).op (α.app (op V) s)
      compat := by
        intro U U' V V' hU hV h h' s
        rw [NatTrans.naturality_apply α (homOfLE hV).op s]
        change F.map _ (F.map _ _) = F.map _ (F.map _ _)
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
        rfl }
  left_inv φ := by
    apply FMorphism.ext'
    funext U V h s
    change F.map (homOfLE h).op (φ.app _ V le_rfl s) = _
    rw [φ.compat _ U V V h le_rfl le_rfl h s]
    exact congrArg (φ.app U V h) (Functor.map_id_apply G (op V) s)
  right_inv α := by
    ext V s
    exact Functor.map_id_apply F _ _

/-- URU5jgTvjhU-12633 (3:30:33) [prop] `V ↦ f⁻¹(V)` is an increasing functor `𝒪_Y → 𝒪_X` that
commutes with arbitrary unions. -/
theorem opens_map_iSup (f : X ⟶ Y) {ι : Type*} (V : ι → Opens Y) :
    Monotone (Opens.map f).obj ∧ (Opens.map f).obj (iSup V) = ⨆ i, (Opens.map f).obj (V i) :=
  ⟨(Opens.map f).monotone, Opens.map_iSup f V⟩

/-- URU5jgTvjhU-12702 (3:31:42) [def] The direct image `f_*F(V) = F(f⁻¹(V))`. -/
example (f : X ⟶ Y) (F : X.Presheaf (Type u)) (V : Opens Y) :
    ((TopCat.Presheaf.pushforward (Type u) f).obj F).obj (op V) = F.obj (op ((Opens.map f).obj V)) :=
  rfl

/-- URU5jgTvjhU-12832 (3:33:52) [prop] On presheaves, `f_*` commutes with arbitrary limits and
colimits. -/
theorem pushforward_preserves (f : X ⟶ Y) :
    Nonempty (PreservesLimits (TopCat.Presheaf.pushforward (Type u) f)) ∧
      Nonempty (PreservesColimits (TopCat.Presheaf.pushforward (Type u) f)) :=
  ⟨⟨inferInstanceAs (PreservesLimits ((Functor.whiskeringLeft _ _ _).obj (Opens.map f).op))⟩,
    ⟨inferInstanceAs (PreservesColimits ((Functor.whiskeringLeft _ _ _).obj (Opens.map f).op))⟩⟩

/-- URU5jgTvjhU-12899 (3:34:59) [prop] The direct image of a sheaf is a sheaf. -/
theorem pushforward_isSheaf (f : X ⟶ Y) {F : X.Presheaf (Type u)} (h : F.IsSheaf) :
    ((TopCat.Presheaf.pushforward (Type u) f).obj F).IsSheaf :=
  TopCat.Sheaf.pushforward_sheaf_of_sheaf f h

/-- URU5jgTvjhU-13294 (3:41:34) [def] The inverse image `f^*` is the left adjoint of `f_*`. -/
def pullback_adjunction (f : X ⟶ Y) :
    TopCat.Sheaf.pullback (Type u) f ⊣ TopCat.Sheaf.pushforward (Type u) f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f

/-- URU5jgTvjhU-13097 (3:38:17) [prop] `f_* : Sh(X) → Sh(Y)` commutes with arbitrary limits (it is
a right adjoint). -/
theorem sheaf_pushforward_preservesLimits (f : X ⟶ Y) :
    Nonempty (PreservesLimits (TopCat.Sheaf.pushforward (Type u) f)) :=
  ⟨(pullback_adjunction f).rightAdjoint_preservesLimits⟩

/-- URU5jgTvjhU-13743 (3:49:03) [prop] `f^*` commutes with arbitrary colimits (left adjoint). -/
theorem sheaf_pullback_preservesColimits (f : X ⟶ Y) :
    Nonempty (PreservesColimits (TopCat.Sheaf.pullback (Type u) f)) :=
  ⟨(pullback_adjunction f).leftAdjoint_preservesColimits⟩

/-- URU5jgTvjhU-13614 (3:46:54) [prop] `f^*G` is the sheaf associated to the presheaf inverse
image. -/
def sheaf_pullback_iso (f : X ⟶ Y) :
    TopCat.Sheaf.pullback (Type u) f ≅
      TopCat.Sheaf.forget (Type u) Y ⋙ TopCat.Presheaf.pullback (Type u) f ⋙
        presheafToSheaf (Opens.grothendieckTopology X) (Type u) :=
  TopCat.Sheaf.pullbackIso (Type u) f

/-- URU5jgTvjhU-13485 (3:44:45) [prop] For every functor `φ : C → D` between small categories, the
restriction `D̂ → Ĉ`, `P ↦ P ∘ φ`, has a left adjoint and a right adjoint (Kan extensions). -/
theorem restriction_adjoints {C D : Type u} [SmallCategory C] [SmallCategory D] (φ : C ⥤ D) :
    ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj φ.op).IsRightAdjoint ∧
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj φ.op).IsLeftAdjoint :=
  ⟨⟨_, ⟨φ.op.lanAdjunction (Type u)⟩⟩, ⟨_, ⟨φ.op.ranAdjunction (Type u)⟩⟩⟩

/-- URU5jgTvjhU-13162 (3:39:22) [cex] `f_*` does not commute with coproducts in general: for
`f : ∅ → pt`, `f_*` sends no sheaf to an initial sheaf (the empty coproduct is not preserved), since
every sheaf on `∅` has a section over `∅ = f⁻¹(pt)` while a sheaf on the point may have none. -/
theorem pushforward_not_initial (f : TopCat.of PEmpty.{u + 1} ⟶ TopCat.of PUnit.{u + 1})
    (I : TopCat.Sheaf (Type u) (TopCat.of PEmpty.{u + 1})) :
    ¬ Nonempty (IsInitial ((TopCat.Sheaf.pushforward (Type u) f).obj I)) := by
  rintro ⟨h⟩
  let S : TopCat.Sheaf (Type u) (TopCat.of PUnit.{u + 1}) :=
    ⟨(TopCat.of PUnit.{u + 1}).presheafToTypes fun _ => PEmpty.{u + 1},
      TopCat.Presheaf.toTypes_isSheaf _ _⟩
  have hbot : (Opens.map f).obj ⊤ = ⊥ := by
    ext x
    exact x.elim
  have hu : Unique (I.obj.obj (op ⊥)) :=
    Types.isTerminalEquivUnique _ (TopCat.Sheaf.isTerminalOfEmpty I)
  let s : I.obj.obj (op ((Opens.map f).obj ⊤)) := hbot ▸ hu.default
  have t := (h.to S).hom.app (op ⊤) s
  exact (t ⟨PUnit.unit, trivial⟩).elim

/-- URU5jgTvjhU-13945 (3:52:25) [def] The inverse image of a space `G → Y` under `f` is the fibre
product `X ×_Y G ⊆ X × G`, with the induced topology. -/
def pullbackIsoSubtype {Z : TopCat.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    pullback f g ≅ TopCat.of { p : X × Z // f p.1 = g p.2 } :=
  TopCat.pullbackIsoProdSubtype f g

/-- URU5jgTvjhU-14011 (3:53:31) [prop] Étalé maps are stable under base change: if `g : G → Y` is a
local homeomorphism, so is `X ×_Y G → X`. -/
theorem isLocalHomeomorph_pullback {A B G : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace G] (f : A → B) (hf : Continuous f) (g : G → B) (hg : IsLocalHomeomorph g) :
    IsLocalHomeomorph fun p : { p : A × G // f p.1 = g p.2 } => p.1.1 := by
  refine isLocalHomeomorph_of_isOpenMap (continuous_fst.comp continuous_subtype_val) ?_ ?_
  · intro W hW
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨⟨⟨a, e⟩, hae⟩, hp, rfl⟩
    obtain ⟨W', hW', hWW'⟩ := isOpen_induced_iff.1 hW
    have hmem : (a, e) ∈ W' := by rw [← hWW'] at hp; exact hp
    obtain ⟨A0, B0, hA0, hB0, ha, he, hsub⟩ := isOpen_prod_iff.1 hW' a e hmem
    refine ⟨A0 ∩ f ⁻¹' (g '' B0), ?_, hA0.inter (hg.isOpenMap _ hB0 |>.preimage hf), ha,
      ⟨e, he, hae.symm⟩⟩
    rintro a' ⟨ha', e', he', hfe'⟩
    refine ⟨⟨(a', e'), hfe'.symm⟩, ?_, rfl⟩
    rw [← hWW']
    exact hsub ⟨ha', he'⟩
  · rintro ⟨⟨a, e⟩, hae⟩
    obtain ⟨U, hU, he, hinj⟩ := hg.isLocallyInjective e
    refine ⟨{p | p.1.2 ∈ U}, hU.preimage (continuous_snd.comp continuous_subtype_val), he, ?_⟩
    rintro ⟨⟨a₁, e₁⟩, h₁⟩ hp₁ ⟨⟨a₂, e₂⟩, h₂⟩ hp₂ (h : a₁ = a₂)
    subst h
    have : e₁ = e₂ := hinj hp₁ hp₂ (h₁.symm.trans h₂)
    subst this
    rfl

/-- URU5jgTvjhU-14268 (3:57:48) [prop] Étalé spaces over `B` are stable under finite limits in
spaces over `B`: the terminal object `B → B`, fibre products `E ×_B E'`, and equalizers
`{e | a e = b e}` of maps over `B` are étalé over `B`. -/
theorem etale_finite_limits {B E E' : Type*} [TopologicalSpace B] [TopologicalSpace E]
    [TopologicalSpace E'] (p : E → B) (hp : IsLocalHomeomorph p) (p' : E' → B)
    (hp' : IsLocalHomeomorph p') :
    IsLocalHomeomorph (id : B → B) ∧
      IsLocalHomeomorph (fun q : { q : E × E' // p q.1 = p' q.2 } => p q.1.1) ∧
      ∀ (a b : E → E'), Continuous a → Continuous b → p' ∘ a = p → p' ∘ b = p →
        IsLocalHomeomorph fun e : { e : E // a e = b e } => p e.1 := by
  refine ⟨(Homeomorph.refl B).isLocalHomeomorph,
    hp.comp (isLocalHomeomorph_pullback p hp.continuous p' hp'), ?_⟩
  intro a b ha hb hap hbp
  have hopen : IsOpen {e | a e = b e} :=
    hp'.isLocallyInjective.isOpen_eqLocus ha hb (hap.trans hbp.symm)
  exact hp.comp hopen.isOpenEmbedding_subtypeVal.isLocalHomeomorph

/-- URU5jgTvjhU-14268 (3:57:48) [prop] The fibre of `X ×_Y G` at `x` is homeomorphic to the fibre
of `G` at `f(x)`. -/
def pullback_fibre {A B G : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace G]
    (f : A → B) (g : G → B) (x : A) :
    { q : { p : A × G // f p.1 = g p.2 } // q.1.1 = x } ≃ₜ { e : G // g e = f x } where
  toFun q := ⟨q.1.1.2, by rw [← q.1.2, q.2]⟩
  invFun e := ⟨⟨(x, e.1), e.2.symm⟩, rfl⟩
  left_inv q := by
    obtain ⟨⟨⟨a, e⟩, h⟩, rfl⟩ := q
    rfl
  right_inv e := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- URU5jgTvjhU-14332 (3:58:52) [prop] `(f^*G)_x ≃ G_{f(x)}`. -/
def pullback_stalk (f : X ⟶ Y) (G : Y.Presheaf (Type u)) (x : X) :
    G.stalk (f x) ≅ ((TopCat.Presheaf.pullback (Type u) f).obj G).stalk x :=
  TopCat.Presheaf.stalkPullbackIso (Type u) f G x

/-! ## Stalks and epimorphisms -/

/-- URU5jgTvjhU-17311 (4:48:31) [prop] Two morphisms `u, v : F → G` of sheaves are equal if and
only if `u_x = v_x` for all `x`: the fibre functors form a faithful family. -/
theorem sheaf_hom_ext_stalks {F G : TopCat.Sheaf (Type u) X} (u v : F ⟶ G) :
    u = v ↔ ∀ x, (TopCat.Presheaf.stalkFunctor (Type u) x).map u.hom =
      (TopCat.Presheaf.stalkFunctor (Type u) x).map v.hom := by
  refine ⟨fun h _ => h ▸ rfl, fun h => ?_⟩
  apply (TopCat.Sheaf.forget (Type u) X).map_injective
  ext U s
  apply TopCat.Presheaf.section_ext G U
  intro x hx
  have hu := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx u.hom s
  have hv := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx v.hom s
  rw [h x] at hu
  exact hv.symm.trans hu |>.symm

/-- URU5jgTvjhU-17440 (4:50:40) [prop] The fibre functors commute with colimits (each is a left
adjoint) and form a conservative family. -/
theorem stalk_colimits_conservative (x : X) :
    Nonempty (PreservesColimits (TopCat.Presheaf.stalkFunctor (Type u) x)) ∧
      ∀ {F G : TopCat.Sheaf (Type u) X} (f : F ⟶ G),
        (∀ x, IsIso ((TopCat.Presheaf.stalkFunctor (Type u) x).map f.hom)) → IsIso f :=
  ⟨⟨inferInstance⟩, fun f _ => TopCat.Presheaf.isIso_of_stalkFunctor_map_iso f⟩

/-- URU5jgTvjhU-17585 (4:53:05) [prop] `φ : F → G` is an epimorphism of sheaves if and only if every
section of `G` lifts locally to a section of `F`. -/
theorem sheaf_epi_iff_local_lift {F G : TopCat.Sheaf (Type u) X} (φ : F ⟶ G) :
    Epi φ ↔ ∀ (U : Opens X) (t : G.obj.obj (op U)) (x : X), x ∈ U →
      ∃ (V : Opens X) (i : V ⟶ U), x ∈ V ∧ ∃ s : F.obj.obj (op V), φ.hom.app (op V) s = G.obj.map i.op t := by
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi]
  constructor
  · intro h U t x hx
    obtain ⟨V, i, ⟨s, hs⟩, hxV⟩ := h.imageSieve_mem t x hx
    exact ⟨V, i, hxV, s, hs⟩
  · intro h
    constructor
    intro U t x hx
    obtain ⟨V, i, hxV, s, hs⟩ := h U t x hx
    exact ⟨V, i, ⟨s, hs⟩, hxV⟩

/-- The local predicate on `ℝ`: continuous `s : U → Bool` with `s = true` only on `(-∞, 1)` and
`s = false` only on `(0, ∞)` (sections of the étalé space `(-∞,1) ⊔ (0,∞) → ℝ`). -/
def twoIntervals : TopCat.LocalPredicate fun _ : TopCat.of ℝ => Bool where
  pred {U} f := Continuous f ∧ ∀ x : U, (f x = true → (x : ℝ) < 1) ∧ (f x = false → 0 < (x : ℝ))
  res {U V} i f h := ⟨(TopCat.continuousLocal _ Bool).res i f h.1, fun x => h.2 ⟨x.1, i.le x.2⟩⟩
  locality {U} f w := by
    refine ⟨(TopCat.continuousLocal _ Bool).locality f fun x => ?_, fun x => ?_⟩
    · obtain ⟨V, m, i, h⟩ := w x
      exact ⟨V, m, i, h.1⟩
    · obtain ⟨V, m, i, h⟩ := w x
      exact h.2 ⟨x, m⟩

/-- URU5jgTvjhU-17712 (4:55:12) [cex] An epimorphism of sheaves need not be surjective on global
sections: on `ℝ`, the sheaf of sections of `(-∞,1) ⊔ (0,∞) → ℝ` maps onto the terminal sheaf, but
has no global section (`ℝ` is connected). -/
theorem epi_not_surjective_global :
    ∃ (F G : TopCat.Sheaf (Type) (TopCat.of ℝ)) (φ : F ⟶ G),
      Epi φ ∧ ¬ Function.Surjective (φ.hom.app (op ⊤)) := by
  let F := TopCat.subsheafToTypes.{0, 0} twoIntervals
  let G : TopCat.Sheaf (Type) (TopCat.of ℝ) :=
    ⟨(TopCat.of ℝ).presheafToTypes fun _ => PUnit.{1}, TopCat.Presheaf.toTypes_isSheaf _ _⟩
  let φ : F ⟶ G := ObjectProperty.homMk
    { app := fun _ => ↾fun _ _ => PUnit.unit
      naturality := fun _ _ _ => rfl }
  refine ⟨F, G, φ, ?_, ?_⟩
  · rw [sheaf_epi_iff_local_lift]
    intro U t x hx
    by_cases hx1 : x < 1
    · refine ⟨U ⊓ ⟨Set.Iio 1, isOpen_Iio⟩, homOfLE inf_le_left, ⟨hx, hx1⟩,
        ⟨fun _ => true, continuous_const, fun y => ⟨fun _ => y.2.2, fun h => by simp at h⟩⟩,
        rfl⟩
    · refine ⟨U ⊓ ⟨Set.Ioi 0, isOpen_Ioi⟩, homOfLE inf_le_left,
        ⟨hx, lt_of_lt_of_le one_pos (not_lt.1 hx1)⟩,
        ⟨fun _ => false, continuous_const, fun y => ⟨fun h => by simp at h, fun _ => y.2.2⟩⟩,
        rfl⟩
  · intro hsurj
    obtain ⟨⟨f, hfc, hf⟩, -⟩ := hsurj fun _ => PUnit.unit
    let g : ℝ → Bool := fun x => f ⟨x, trivial⟩
    have hg : Continuous g := hfc.comp (continuous_id.subtype_mk _)
    have h1 : g (-1) = true := by
      cases h : g (-1)
      · have := (hf ⟨-1, trivial⟩).2 h
        norm_num at this
      · rfl
    have h2 : g 2 = false := by
      cases h : g 2
      · rfl
      · have := (hf ⟨2, trivial⟩).1 h
        norm_num at this
    have := PreconnectedSpace.constant inferInstance hg (x := -1) (y := 2)
    rw [h1, h2] at this
    exact Bool.noConfusion this

/-- URU5jgTvjhU-17712 (4:55:12) [prop] The entry as written is false: the Sierpiński space `Prop`
is compact and not totally disconnected, yet `Γ` sends every epimorphism of sheaves to a surjection
(the closed point has `X` as its only neighbourhood). The statement needs `X` Hausdorff. -/
theorem sierpinski_counterexample :
    CompactSpace Prop ∧ ¬ TotallyDisconnectedSpace Prop ∧
      ∀ (F G : TopCat.Sheaf (Type) (TopCat.of Prop)) (φ : F ⟶ G), Epi φ →
        Function.Surjective (φ.hom.app (op ⊤)) := by
  have nhdF : ∀ s : Set Prop, IsOpen s → False ∈ s → s = Set.univ := fun s hs hF => by
    have := hs.mem_nhds hF
    rwa [nhds_false, Filter.mem_top] at this
  refine ⟨inferInstance, fun h => ?_, fun F G φ hφ t => ?_⟩
  · have hpre : PreconnectedSpace Prop := by
      rw [preconnectedSpace_iff_clopen]
      intro s hs
      by_cases hF : False ∈ s
      · exact Or.inr (nhdF s hs.isOpen hF)
      · left
        have := nhdF sᶜ hs.isClosed.isOpen_compl hF
        simpa using this
    have := h.isTotallyDisconnected_univ Set.univ subset_rfl isPreconnected_univ
    have hTF : True = False := this (Set.mem_univ True) (Set.mem_univ False)
    exact hTF ▸ trivial
  · obtain ⟨V, i, hV, s, hs⟩ := (sheaf_epi_iff_local_lift φ).1 hφ ⊤ t False trivial
    have hVtop : V = ⊤ := Opens.ext (by simpa using nhdF V V.isOpen hV)
    subst hVtop
    refine ⟨s, hs.trans ?_⟩
    rw [Subsingleton.elim i (𝟙 _), op_id]
    exact Functor.map_id_apply G.obj _ t

end

end Buffalo.Topos.Part01
