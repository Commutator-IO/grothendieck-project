import Buffalo.Topos.Part01

/-!
# Buffalo, topos theory, part 3a: points, fibre functors, classifying topoi (11 May and 30 May 1973)

Entries of `docs/buffalo-topos/index.tex` lines 390–535 concerning points of topoi, the classifying
topos `B_G`, fibre functors on `Sh(X)` and the 2-cells between morphisms of topoi of spaces (videos
`URU5jgTvjhU` 9:27:02–11:04:45 and `PqCQM3Pcl6Q` 0:04:34–0:53:20). The status of each entry is in
`docs/buffalo-topos/lean/Part03.json`.

Points of `Sh(X)` are modelled by Mathlib's points of the site `(Opens X, J)`
(`GrothendieckTopology.Point`, the fibre functors of SGA 4 IV 6.3), and `B_G` by `Action (Type u) G`.
-/

universe w u

open CategoryTheory Limits TopologicalSpace Opposite Topology TypeCat GrothendieckTopology

namespace Buffalo.Topos.Part03

noncomputable section

/-! ## Localic presheaf topoi: `Ĉ ≃ Sh(X)` forces `C` to be ordered -/

section Glue
variable {C : Type w} [Category.{u} C] (P : Cᵒᵖ ⥤ Type u) (I : ∀ c, Set (P.obj c))
  (hI : ∀ {c c'} (k : c ⟶ c') (x), x ∈ I c → P.map k x ∈ I c')

/-- The relation identifying the two copies of a point of `I`. -/
inductive GlueRel (c : Cᵒᵖ) : P.obj c ⊕ P.obj c → P.obj c ⊕ P.obj c → Prop
  | glue (x : P.obj c) (hx : x ∈ I c) : GlueRel c (.inl x) (.inr x)

/-- Two copies of `P` glued along `I`. -/
def glue : Cᵒᵖ ⥤ Type u where
  obj c := Quot (GlueRel P I c)
  map k := ↾(Quot.map (Sum.map (P.map k) (P.map k))
    (by rintro _ _ ⟨x, hx⟩; exact .glue _ (hI k x hx)))
  map_id c := by
    ext q
    induction q using Quot.ind with | _ a => rcases a with a | a <;> simp [Quot.map]
  map_comp f g := by
    ext q
    induction q using Quot.ind with | _ a => rcases a with a | a <;> simp [Quot.map]

/-- The left inclusion. -/
def glueInl : P ⟶ glue P I hI where
  app c := ↾fun x => Quot.mk _ (.inl x)
  naturality _ _ k := by ext x; rfl

/-- The right inclusion. -/
def glueInr : P ⟶ glue P I hI where
  app c := ↾fun x => Quot.mk _ (.inr x)
  naturality _ _ k := by ext x; rfl

theorem mem_of_glue {c : Cᵒᵖ} (x : P.obj c)
    (h : (glueInl P I hI).app c x = (glueInr P I hI).app c x) : x ∈ I c := by
  let f : P.obj c ⊕ P.obj c → P.obj c × Prop := fun
    | .inl y => (y, y ∈ I c)
    | .inr y => (y, True)
  have hf : ∀ a b, GlueRel P I c a b → f a = f b := by
    rintro _ _ ⟨y, hy⟩; simp [f, hy]
  have h2 : f (.inl x) = f (.inr x) := congrArg (Quot.lift f hf) h
  simpa [f] using congrArg Prod.snd h2

end Glue

/-- A family of maps `aᵢ : Sᵢ → P` of presheaves that is jointly epimorphic is jointly surjective
on every argument. -/
theorem jointly_surjective_of_jointly_epi {C : Type w} [Category.{u} C] {P : Cᵒᵖ ⥤ Type u}
    {ι : Type*} {S : ι → Cᵒᵖ ⥤ Type u} (a : ∀ i, S i ⟶ P)
    (h : ∀ (T : Cᵒᵖ ⥤ Type u) (f g : P ⟶ T), (∀ i, a i ≫ f = a i ≫ g) → f = g)
    (c : Cᵒᵖ) (x : P.obj c) : ∃ i s, (a i).app c s = x := by
  let I : ∀ c, Set (P.obj c) := fun c => {x | ∃ i s, (a i).app c s = x}
  have hI : ∀ {c c'} (k : c ⟶ c') (x), x ∈ I c → P.map k x ∈ I c' := by
    rintro c c' k _ ⟨i, s, rfl⟩
    exact ⟨i, (S i).map k s, by simp⟩
  have := h (glue P I hI) (glueInl P I hI) (glueInr P I hI) (fun i => by
    ext c s
    simp only [NatTrans.comp_app]
    exact Quot.sound (.glue _ ⟨i, s, rfl⟩))
  exact mem_of_glue P I hI x (by rw [this])


/-- An object with at most one arrow into it from any object (a subterminal object). -/
def IsSubterminal' {D : Type*} [Category D] (S : D) : Prop := ∀ T : D, Subsingleton (T ⟶ S)

theorem opensSheaf_subterminal {X : TopCat.{u}} (U : Opens X) :
    IsSubterminal' (Part01.opensSheaf U) := fun T => ⟨fun f g => by
  apply (sheafToPresheaf _ _).map_injective
  ext V s
  exact Subsingleton.elim (α := unop V ⟶ U) _ _⟩

/-- PqCQM3Pcl6Q-9251 (2:34:11) [prop] If `Ĉ ≃ Sh(X)` for a space `X`, then `C` is an ordered
category: there is at most one arrow between two objects. (Every object of `Sh(X)` is covered by
subterminal objects, the opens; transported to `Ĉ`, the representable `h_d` is covered by
subterminal presheaves, so every `Hom(c, d)` has at most one element.) -/
theorem thin_of_presheaf_equiv_sheaf {X : TopCat.{u}} {C : Type w} [Category.{u} C]
    (e : (Cᵒᵖ ⥤ Type u) ≌ Sheaf (Opens.grothendieckTopology X) (Type u)) (c d : C) :
    Subsingleton (c ⟶ d) := by
  let P : Cᵒᵖ ⥤ Type u := yoneda.obj d
  let ι := Σ U : Opens X, (Part01.opensSheaf U ⟶ e.functor.obj P)
  let S : ι → Cᵒᵖ ⥤ Type u := fun i => e.inverse.obj (Part01.opensSheaf i.1)
  let a : ∀ i, S i ⟶ P := fun i => (e.symm.toAdjunction.homEquiv _ _).symm i.2
  have hepi : ∀ (T : Cᵒᵖ ⥤ Type u) (f g : P ⟶ T), (∀ i, a i ≫ f = a i ≫ g) → f = g := by
    intro T f g h
    apply e.functor.map_injective
    apply Part01.opensSheaf_separating
    intro U a'
    have h1 := congrArg (e.symm.toAdjunction.homEquiv _ _) (h ⟨U, a'⟩)
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right] at h1
    simpa [a] using h1
  obtain ⟨i, s, hs⟩ := jointly_surjective_of_jointly_epi a hepi (op d) (𝟙 d)
  have hsub : ∀ c' : C, Subsingleton ((S i).obj (op c')) := fun c' => by
    have := opensSheaf_subterminal i.1 (e.functor.obj (yoneda.obj c'))
    have : Subsingleton (yoneda.obj c' ⟶ S i) := (e.toAdjunction.homEquiv _ _).symm.subsingleton
    exact yonedaEquiv.symm.subsingleton
  have key : ∀ k : c ⟶ d, (a i).app (op c) ((S i).map k.op s) = k := by
    intro k
    rw [NatTrans.naturality_apply, hs]
    simp [P]
  refine ⟨fun k k' => ?_⟩
  rw [← key k, ← key k', Subsingleton.elim ((S i).map k.op s) ((S i).map k'.op s)]

/-! ## The classifying topos `B_G` -/

section Classifying

variable (G : Type u) [Group G]

/-- `B_G ≃ Ĉ` for `C = (SingleObj G)ᵒᵖ`, the category with one object whose endomorphisms form
the group `Gᵐᵒᵖ ≅ G`. -/
def actionEquivPresheaf : Action (Type u) G ≌ ((SingleObj G)ᵒᵖᵒᵖ ⥤ Type u) :=
  (Action.functorCategoryEquivalence (Type u) G).trans
    (opOpEquivalence (SingleObj G)).congrLeft.symm

/-- The orbit map `h ↦ h • x` as a morphism from the regular `G`-set. -/
def orbitHom (A : Action (Type u) G) (x : A.V) : Action.ofMulAction G G ⟶ A where
  hom := ↾fun h => A.ρ h x
  comm h := by
    ext (k : G)
    show A.ρ (h * k) x = A.ρ h (A.ρ k x)
    rw [map_mul]
    rfl

theorem forget_end (η : Action.forget (Type u) G ⟶ Action.forget (Type u) G) :
    ∃! g : G, ∀ (A : Action (Type u) G) (x : A.V), η.app A x = A.ρ g x := by
  refine ⟨η.app (Action.ofMulAction G G) (1 : G), fun A x => ?_, fun g hg => ?_⟩
  · have h := NatTrans.naturality_apply η (orbitHom G A x) (1 : G)
    have h1 : A.ρ (1 : G) x = x := by simp
    change η.app A (A.ρ 1 x) = A.ρ _ x at h
    rwa [h1] at h
  · have := hg (Action.ofMulAction G G) (1 : G)
    rw [this]
    show g = g * 1
    rw [mul_one]

/-- URU5jgTvjhU-34130 (9:28:50) [cex] If `G ≠ 1`, the topos `B_G` is equivalent to no `Sh(X)`:
by `thin_of_presheaf_equiv_sheaf`, the one-object category with endomorphisms `G` would be
ordered. -/
theorem classifying_not_spatial [Nontrivial G] (X : TopCat.{u}) :
    IsEmpty (Action (Type u) G ≌ Sheaf (Opens.grothendieckTopology X) (Type u)) := by
  refine ⟨fun e => ?_⟩
  have := thin_of_presheaf_equiv_sheaf ((actionEquivPresheaf G).symm.trans e)
    (op (SingleObj.star G)) (op (SingleObj.star G))
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  apply hg
  have h := Subsingleton.elim (show SingleObj.star G ⟶ SingleObj.star G from g).op
    (show SingleObj.star G ⟶ SingleObj.star G from 1).op
  exact Quiver.Hom.op_inj h

/-- URU5jgTvjhU-34201 (9:30:01) [ex] The forgetful functor `B_G → Set` is a fibre functor (it
commutes with finite limits and all colimits)... -/
theorem forget_isFibreFunctor :
    PreservesFiniteLimits (Action.forget (Type u) G) ∧ PreservesColimits (Action.forget (Type u) G) :=
  ⟨inferInstance, inferInstance⟩

/-- URU5jgTvjhU-37075 (10:17:55) [prop] `Γ(X) = Hom(1, X)` is the set of `G`-invariant elements
of `X`. -/
def globalSectionsEquiv (A : Action (Type u) G) :
    (Action.trivial G (PUnit : Type u) ⟶ A) ≃ {x : A.V // ∀ g : G, A.ρ g x = x} where
  toFun f := ⟨f.hom PUnit.unit, fun g => by
    have := congrArg (fun k => k PUnit.unit) (f.comm g)
    exact this.symm⟩
  invFun x :=
    { hom := ↾fun _ => x.1
      comm g := by ext; exact (x.2 g).symm }
  left_inv f := by ext ⟨⟩; rfl
  right_inv x := rfl

/-- ... and `H^i(B_G, M) = H^i(G, M)`: the cohomology of `B_G` (derived functors of
`Γ = Hom(ℤ, -)` on `(B_G)_ab = Rep ℤ G`) is `Ext^i(ℤ, M)`, group cohomology. -/
def cohomology_classifying {k : Type u} [CommRing k] (M : Rep k G) (n : ℕ) :
    groupCohomology M n ≅ ((Ext k (Rep k G) n).obj (op (Rep.trivial k G k))).obj M :=
  groupCohomologyIsoExt M n

/-- PqCQM3Pcl6Q-3200 (0:53:20) [def] / PqCQM3Pcl6Q-10701 (2:58:21) [prop] For `f : G → G'`, the
inverse image of `Bf : BG → BG'` restricts the action along `f`, and commutes with all limits and
colimits. -/
theorem res_preserves {H : Type u} [Group H] (f : G →* H) :
    PreservesLimits (Action.res (Type u) f) ∧ PreservesColimits (Action.res (Type u) f) := by
  have : PreservesLimits (Action.res (Type u) f ⋙ Action.forget (Type u) G) :=
    inferInstanceAs (PreservesLimits (Action.forget (Type u) H))
  have : PreservesColimits (Action.res (Type u) f ⋙ Action.forget (Type u) G) :=
    inferInstanceAs (PreservesColimits (Action.forget (Type u) H))
  exact ⟨preservesLimits_of_reflects_of_preserves _ (Action.forget (Type u) G),
    preservesColimits_of_reflects_of_preserves _ (Action.forget (Type u) G)⟩

/-- PqCQM3Pcl6Q-12172 (3:22:52) [rem] For `H ≠ G`, the localization object `G/H → 1` of `BG` is
not a monomorphism. -/
theorem quotient_not_mono {H : Subgroup G} (hH : H ≠ ⊤)
    (f : Action.ofMulAction G (G ⧸ H) ⟶ Action.ofMulAction G PUnit.{u + 1}) : ¬ Mono f := by
  intro hf
  have : Mono ((Action.forget (Type u) G).map f) := inferInstance
  rw [mono_iff_injective] at this
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
    by_contra h
    push Not at h
    exact hH (eq_top_iff.2 fun g _ => h g)
  have := this (a₁ := (g : G ⧸ H)) (a₂ := ((1 : G) : G ⧸ H))
    (Subsingleton.elim (α := PUnit.{u + 1}) _ _)
  have h2 : ((g : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := this
  rw [QuotientGroup.eq, mul_one] at h2
  exact hg (by simpa using h2)

end Classifying

/-! ## Points of `Sh(X)` -/

section Points

variable {X : Type u} [TopologicalSpace X]

theorem fiber_mono (Φ : Point.{u} (Opens.grothendieckTopology X)) {U V : Opens X} (h : U ≤ V) :
    Nonempty (Φ.fiber.obj U) → Nonempty (Φ.fiber.obj V) :=
  fun ⟨a⟩ => ⟨Φ.fiber.map (homOfLE h) a⟩

theorem fiber_top (Φ : Point.{u} (Opens.grothendieckTopology X)) : Nonempty (Φ.fiber.obj ⊤) :=
  ⟨(Φ.uniqueFiberObj ⊤ isTerminalTop).default⟩

theorem fiber_inf (Φ : Point.{u} (Opens.grothendieckTopology X)) {U V : Opens X} :
    Nonempty (Φ.fiber.obj U) → Nonempty (Φ.fiber.obj V) → Nonempty (Φ.fiber.obj (U ⊓ V)) := by
  rintro ⟨a⟩ ⟨b⟩
  let A : Φ.fiber.Elements := Φ.fiber.elementsMk U a
  let B : Φ.fiber.Elements := Φ.fiber.elementsMk V b
  let W := IsCofiltered.min A B
  have h1 : W.1 ≤ U := leOfHom (IsCofiltered.minToLeft A B).1
  have h2 : W.1 ≤ V := leOfHom (IsCofiltered.minToRight A B).1
  exact fiber_mono Φ (le_inf h1 h2) ⟨W.2⟩

/-- A point of the site of `X` is completely prime: if its fibre over `U` is non-empty and `U` is
covered by a family `𝒱` of opens, then its fibre over some member of `𝒱` is non-empty. -/
theorem fiber_cover (Φ : Point.{u} (Opens.grothendieckTopology X)) (U : Opens X)
    (𝒱 : Set (Opens X)) (h𝒱 : ∀ x ∈ U, ∃ V ∈ 𝒱, x ∈ V) (hU : Nonempty (Φ.fiber.obj U)) :
    ∃ V ∈ 𝒱, Nonempty (Φ.fiber.obj V) := by
  obtain ⟨a⟩ := hU
  let R : Sieve U :=
    { arrows := fun W _ => ∃ V ∈ 𝒱, W ≤ V
      downward_closed := by
        rintro W W' f ⟨V, hV, hWV⟩ g
        exact ⟨V, hV, (leOfHom g).trans hWV⟩ }
  have hR : R ∈ Opens.grothendieckTopology X U := by
    intro x hx
    obtain ⟨V, hV, hxV⟩ := h𝒱 x hx
    exact ⟨U ⊓ V, homOfLE inf_le_left, ⟨V, hV, inf_le_right⟩, ⟨hx, hxV⟩⟩
  obtain ⟨W, f, ⟨V, hV, hWV⟩, y, -⟩ := Φ.jointly_surjective R hR a
  exact ⟨V, hV, fiber_mono Φ hWV ⟨y⟩⟩

/-- Two points with the same non-empty fibres are isomorphic. -/
def pointIsoOfNonempty (Φ Ψ : Point.{u} (Opens.grothendieckTopology X))
    (h : ∀ U, Nonempty (Φ.fiber.obj U) ↔ Nonempty (Ψ.fiber.obj U)) : Φ ≅ Ψ where
  hom := ⟨{ app U := ↾fun b => Classical.choice ((h U).2 ⟨b⟩)
            naturality _ _ _ := by ext; subsingleton }⟩
  inv := ⟨{ app U := ↾fun b => Classical.choice ((h U).1 ⟨b⟩)
            naturality _ _ _ := by ext; subsingleton }⟩
  hom_inv_id := by ext; subsingleton
  inv_hom_id := by ext; subsingleton

theorem nonempty_iff_of_iso {Φ Ψ : Point.{u} (Opens.grothendieckTopology X)} (e : Φ ≅ Ψ)
    (U : Opens X) : Nonempty (Φ.fiber.obj U) ↔ Nonempty (Ψ.fiber.obj U) :=
  ⟨fun ⟨a⟩ => ⟨e.inv.hom.app U a⟩, fun ⟨b⟩ => ⟨e.hom.hom.app U b⟩⟩

theorem point_fiber_iff (x : X) (U : Opens X) :
    Nonempty ((Opens.pointGrothendieckTopology x).fiber.obj U) ↔ x ∈ U :=
  ⟨fun ⟨⟨⟨h⟩⟩⟩ => h, fun h => ⟨⟨⟨h⟩⟩⟩⟩

/-- URU5jgTvjhU-34328 / PqCQM3Pcl6Q-2100. For `X` sober, every point of the site of `X` (fibre
functor in the sense of SGA 4 IV 6.3) is isomorphic to the point `F ↦ F_x` of a unique `x ∈ X`. -/
theorem point_classification [QuasiSober X] [T0Space X]
    (Φ : Point.{u} (Opens.grothendieckTopology X)) :
    ∃! x : X, Nonempty (Φ ≅ Opens.pointGrothendieckTopology x) := by
  let 𝒱 : Set (Opens X) := {U | ¬ Nonempty (Φ.fiber.obj U)}
  let W : Opens X := sSup 𝒱
  have hW : ¬ Nonempty (Φ.fiber.obj W) := by
    intro hW
    obtain ⟨V, hV, hV'⟩ := fiber_cover Φ W 𝒱 (fun x hx => by
      obtain ⟨V, hV, hxV⟩ := (Opens.mem_sSup).1 hx
      exact ⟨V, hV, hxV⟩) hW
    exact hV hV'
  let Z : Set X := (W : Set X)ᶜ
  have key : ∀ U : Opens X, Nonempty (Φ.fiber.obj U) ↔ ((U : Set X) ∩ Z).Nonempty := by
    intro U
    constructor
    · intro hU
      by_contra hne
      apply hW
      refine fiber_mono Φ ?_ hU
      intro x hx
      by_contra hxW
      exact hne ⟨x, hx, hxW⟩
    · rintro ⟨z, hzU, hzW⟩
      by_contra hU
      exact hzW (Opens.mem_sSup.2 ⟨U, hU, hzU⟩)
  have hZc : IsClosed Z := W.2.isClosed_compl
  have hZ : IsIrreducible Z := by
    refine ⟨?_, ?_⟩
    · obtain ⟨z, -, hz⟩ := (key ⊤).1 (fiber_top Φ)
      exact ⟨z, hz⟩
    · intro u v hu hv ⟨x, hxZ, hxu⟩ ⟨y, hyZ, hyv⟩
      have h1 := (key ⟨u, hu⟩).2 ⟨x, hxu, hxZ⟩
      have h2 := (key ⟨v, hv⟩).2 ⟨y, hyv, hyZ⟩
      obtain ⟨z, ⟨hzu, hzv⟩, hzZ⟩ := (key _).1 (fiber_inf Φ h1 h2)
      exact ⟨z, hzZ, hzu, hzv⟩
  obtain ⟨x, hx⟩ := QuasiSober.sober hZ hZc
  have hxU : ∀ U : Opens X, Nonempty (Φ.fiber.obj U) ↔
      Nonempty ((Opens.pointGrothendieckTopology x).fiber.obj U) := fun U => by
    have : x ∈ U ↔ (Z ∩ (U : Set X)).Nonempty := hx.mem_open_set_iff U.2
    rw [key U, point_fiber_iff, this, Set.inter_comm]
  refine ⟨x, ⟨pointIsoOfNonempty _ _ hxU⟩, fun y ⟨e⟩ => ?_⟩
  have e' := (pointIsoOfNonempty _ _ hxU).symm ≪≫ e
  exact ((Opens.pointGrothendieckTopologyHomEquiv e'.inv).antisymm
    (Opens.pointGrothendieckTopologyHomEquiv e'.hom)).eq


instance : Infinite (CofiniteTopology ℕ) := Infinite.of_injective _ CofiniteTopology.of.injective

theorem cofinite_inter_nonempty {U V : Set (CofiniteTopology ℕ)} (hU : IsOpen U) (hV : IsOpen V)
    (hU' : U.Nonempty) (hV' : V.Nonempty) : (U ∩ V).Nonempty := by
  rw [CofiniteTopology.isOpen_iff] at hU hV
  have : (U ∩ V)ᶜ.Finite := by rw [Set.compl_inter]; exact (hU hU').union (hV hV')
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  rw [h, Set.compl_empty] at this
  exact Set.infinite_univ (α := CofiniteTopology ℕ) this

/-- The generic point of `ℕ` with the cofinite topology: its fibre over `U` is non-empty iff
`U ≠ ∅`. -/
def cofiniteGenericPoint : Point.{0} (Opens.grothendieckTopology (CofiniteTopology ℕ)) where
  fiber.obj U := PLift (U : Set (CofiniteTopology ℕ)).Nonempty
  fiber.map f := ↾fun h => ⟨h.down.mono (leOfHom f)⟩
  isCofiltered :=
    { nonempty := ⟨.mk (obj := ⊤) ⟨⟨CofiniteTopology.of 0, trivial⟩⟩⟩
      cone_objs U V := by
        induction U with | @mk U hU
        induction V with | @mk V hV
        obtain ⟨hU⟩ := hU
        obtain ⟨hV⟩ := hV
        exact ⟨.mk (obj := U ⊓ V) ⟨cofinite_inter_nonempty U.2 V.2 hU hV⟩,
          Functor.Elements.homMk (homOfLE (by simp)) rfl,
          Functor.Elements.homMk (homOfLE (by simp)) rfl, by tauto⟩
      cone_maps _ _ _ _ := ⟨_, 𝟙 _, rfl⟩ }
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective := by
    rintro U R hR ⟨⟨x, hx⟩⟩
    obtain ⟨V, f, hf, hV⟩ := hR x hx
    exact ⟨_, _, hf, ⟨⟨x, hV⟩⟩, rfl⟩

/-- PqCQM3Pcl6Q-1445 (correction). Without sobriety the category of fibre functors is not the
set of points: on `ℕ` with the cofinite topology (not sober), the generic point is isomorphic to
no point `F ↦ F_x`. -/
theorem cofiniteGenericPoint_not_iso (x : CofiniteTopology ℕ) :
    IsEmpty (cofiniteGenericPoint ≅ Opens.pointGrothendieckTopology x) := by
  refine ⟨fun e => ?_⟩
  let U : Opens (CofiniteTopology ℕ) := ⟨{x}ᶜ, by
    rw [CofiniteTopology.isOpen_iff, compl_compl]; exact fun _ => Set.finite_singleton x⟩
  have hU : (U : Set (CofiniteTopology ℕ)).Nonempty :=
    (Set.finite_singleton x).infinite_compl.nonempty
  have := (e.inv.hom.app U ⟨hU⟩).down.down
  exact this rfl

/-- URU5jgTvjhU-34393 (9:33:13) [prop] Specialization `y ∈ closure {x}` (`x ⤳ y`) is a preorder,
an order for `X` sober (T0), and induces `F_y → F_x`, functorial in `F`. -/
theorem specialization_order [T0Space X] {x y : X} (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x = y :=
  (h₁.antisymm h₂).eq

theorem stalkSpecializes_natural {Y : TopCat.{u}} {F G : Y.Presheaf (Type u)} (f : F ⟶ G)
    {x y : Y} (h : x ⤳ y) :
    F.stalkSpecializes h ≫ (TopCat.Presheaf.stalkFunctor (Type u) x).map f =
      (TopCat.Presheaf.stalkFunctor (Type u) y).map f ≫ G.stalkSpecializes h :=
  TopCat.Presheaf.stalkSpecializes_stalkFunctor_map f h

/-- URU5jgTvjhU-34662 (9:37:42) / PqCQM3Pcl6Q-1445 (0:24:05) There is a morphism of fibre functors
`ε_y → ε_x` (a morphism of points `x → y`) iff `x ⤳ y`, i.e. `y ∈ closure {x}`, and it is unique. -/
theorem point_hom_iff (x y : X) :
    Nonempty (Opens.pointGrothendieckTopology x ⟶ Opens.pointGrothendieckTopology y) ↔ x ⤳ y ∧
      Subsingleton (Opens.pointGrothendieckTopology x ⟶ Opens.pointGrothendieckTopology y) :=
  ⟨fun ⟨f⟩ => ⟨Opens.pointGrothendieckTopologyHomEquiv f, inferInstance⟩,
    fun ⟨h, _⟩ => ⟨Opens.pointGrothendieckTopologyHomEquiv.symm h⟩⟩

/-- URU5jgTvjhU-39560 (10:59:20) [prop] For `Y` sober the category of points is `Y` ordered by
specialization: every point is isomorphic to a unique `ε_y`, and `Hom(ε_x, ε_y)` is a singleton if
`x ⤳ y`, empty otherwise. -/
theorem points_category [QuasiSober X] [T0Space X] :
    (∀ Φ : Point.{u} (Opens.grothendieckTopology X),
      ∃! x : X, Nonempty (Φ ≅ Opens.pointGrothendieckTopology x)) ∧
    (∀ x y : X, Nonempty (Opens.pointGrothendieckTopology x ⟶ Opens.pointGrothendieckTopology y) ↔
      x ⤳ y) ∧ Quiver.IsThin (Point.{u} (Opens.grothendieckTopology X)) :=
  ⟨point_classification, fun _ _ => ⟨fun ⟨f⟩ => Opens.pointGrothendieckTopologyHomEquiv f,
    fun h => ⟨Opens.pointGrothendieckTopologyHomEquiv.symm h⟩⟩, inferInstance⟩

/-- URU5jgTvjhU-36756 (10:12:36) / PqCQM3Pcl6Q-2947 (0:49:07), case `G = 1`: the stalk functors
form a conservative family of points of `Sh(X)` (`Sh(X)` has enough points). -/
theorem stalks_conservative :
    (Opens.pointsGrothendieckTopology X).IsConservativeFamilyOfPoints :=
  Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology X

end Points

/-! ## 2-morphisms between morphisms of topoi of spaces -/

section TwoCells

variable {X Y : TopCat.{u}}

/-- The restriction 2-cell `f_* → g_*` when `f(x) ⤳ g(x)` for all `x`. -/
def pushforwardTwoCell (f g : X ⟶ Y) (h : ∀ x, f x ⤳ g x) :
    TopCat.Sheaf.pushforward (Type u) f ⟶ TopCat.Sheaf.pushforward (Type u) g where
  app F := ⟨{ app V := F.obj.map (homOfLE (fun x (hx : g x ∈ V.unop) =>
                  (specializes_iff_forall_open.1 (h x) _ V.unop.2 hx : f x ∈ V.unop))).op
              naturality V W k := by
                change F.obj.map ((Opens.map f).map k.unop).op ≫ F.obj.map _ =
                  F.obj.map _ ≫ F.obj.map ((Opens.map g).map k.unop).op
                rw [← F.obj.map_comp, ← F.obj.map_comp]
                rfl }⟩
  naturality F F' φ := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact (φ.hom.naturality _).symm

theorem pushforward_hom_iff (f g : X ⟶ Y) :
    Nonempty (TopCat.Sheaf.pushforward (Type u) f ⟶ TopCat.Sheaf.pushforward (Type u) g) ↔
      ∀ x, f x ⤳ g x := by
  refine ⟨fun ⟨η⟩ x => ?_, fun h => ⟨pushforwardTwoCell f g h⟩⟩
  rw [specializes_iff_forall_open]
  intro V hV hx
  let V' : Opens Y := ⟨V, hV⟩
  let F := Part01.opensSheaf ((Opens.map f).obj V')
  have := (η.app F).hom.app (op V') (𝟙 _)
  exact (leOfHom this) hx

theorem pushforward_twoCell_eval (f g : X ⟶ Y)
    (η : TopCat.Sheaf.pushforward (Type u) f ⟶ TopCat.Sheaf.pushforward (Type u) g)
    (F : TopCat.Sheaf (Type u) X) (V : (Opens Y)ᵒᵖ)
    (a : Part01.opensSheaf ((Opens.map f).obj V.unop) ⟶ F) :
    (η.app F).hom.app V (Part01.opensSheaf_hom _ F a) =
      a.hom.app (op ((Opens.map g).obj V.unop))
        ((η.app (Part01.opensSheaf ((Opens.map f).obj V.unop))).hom.app V (𝟙 _)) := by
  have := congrArg (fun φ => φ.hom.app V (𝟙 ((Opens.map f).obj V.unop))) (η.naturality a)
  exact this

instance pushforward_hom_subsingleton (f g : X ⟶ Y) :
    Subsingleton (TopCat.Sheaf.pushforward (Type u) f ⟶ TopCat.Sheaf.pushforward (Type u) g) :=
  ⟨fun η η' => by
    apply NatTrans.ext
    funext F
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    ext s
    obtain ⟨a, rfl⟩ := (Part01.opensSheaf_hom ((Opens.map f).obj V.unop) F).surjective s
    refine (pushforward_twoCell_eval f g η F V a).trans
      (Eq.trans ?_ (pushforward_twoCell_eval f g η' F V a).symm)
    congr 1
    exact Subsingleton.elim (α := (Opens.map g).obj V.unop ⟶ (Opens.map f).obj V.unop) _ _⟩

/-- URU5jgTvjhU-39885 (11:04:45) [prop] If `Y` is separated (T1 suffices), the category
`Homtop(Sh(X), Sh(Y))` is discrete: there is a 2-morphism `f_* → g_*` only if `f = g`. -/
theorem pushforward_hom_iff_eq [T1Space Y] (f g : X ⟶ Y) :
    Nonempty (TopCat.Sheaf.pushforward (Type u) f ⟶ TopCat.Sheaf.pushforward (Type u) g) ↔
      f = g := by
  rw [pushforward_hom_iff]
  refine ⟨fun h => TopCat.ext fun x => specializes_iff_eq.1 (h x), ?_⟩
  rintro rfl x
  exact specializes_refl _

/-- PqCQM3Pcl6Q-640 (0:10:40) [prop], uniqueness: for `Y` T0, a continuous map is determined by its
morphism of topoi (isomorphic direct images force `f = g`). -/
theorem eq_of_pushforward_iso [T0Space Y] (f g : X ⟶ Y)
    (e : TopCat.Sheaf.pushforward (Type u) f ≅ TopCat.Sheaf.pushforward (Type u) g) : f = g :=
  TopCat.ext fun x => (((pushforward_hom_iff f g).1 ⟨e.hom⟩ x).antisymm
    ((pushforward_hom_iff g f).1 ⟨e.inv⟩ x)).eq

end TwoCells

end

end Buffalo.Topos.Part03
