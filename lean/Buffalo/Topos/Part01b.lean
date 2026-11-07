import Mathlib

/-!
# Buffalo, topos theory, part 1b: torsors, generators, abelian sheaves (11 May 1973)

Entries of `docs/buffalo-topos/index.tex` from « Torsors and stalkwise checks » to « Abelian
sheaves and injectives » (video `URU5jgTvjhU`, 2:33:33–3:21:12). The status of each entry is in
`docs/buffalo-topos/lean/Part01.json`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace Buffalo.Topos.Part01

noncomputable section

variable {X : TopCat.{u}}

/-! ## Torsors and stalkwise checks -/

/-- URU5jgTvjhU-9213 (2:33:33) [def] In `Set`, `G` acts simply transitively on `E` if
`G × E → E × E`, `(g, x) ↦ (gx, x)`, is bijective. -/
def IsSimplyTransitive (G E : Type*) [Group G] [MulAction G E] : Prop :=
  Function.Bijective fun p : G × E => (p.1 • p.2, p.2)

/-- URU5jgTvjhU-9213 (2:33:33) [def] `E` is a torsor if moreover `E → pt` is surjective. -/
def IsTorsor (G E : Type*) [Group G] [MulAction G E] : Prop :=
  IsSimplyTransitive G E ∧ Function.Surjective fun _ : E => (PUnit.unit : PUnit.{1})

/-- The bijectivity of `(g, x) ↦ (gx, x)` says that for all `x, y` there is exactly one `g` with
`gx = y`. -/
theorem isSimplyTransitive_iff (G E : Type*) [Group G] [MulAction G E] :
    IsSimplyTransitive G E ↔ ∀ x y : E, ∃! g : G, g • x = y := by
  constructor
  · rintro ⟨hinj, hsurj⟩ x y
    obtain ⟨⟨g, x'⟩, h⟩ := hsurj (y, x)
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    refine ⟨g, h1, fun g' hg' => ?_⟩
    have := @hinj (g', x') (g, x') (by simp [h1, hg'])
    exact congrArg Prod.fst this
  · intro h
    refine ⟨?_, ?_⟩
    · rintro ⟨g, x⟩ ⟨g', x'⟩ hp
      simp only [Prod.mk.injEq] at hp
      obtain ⟨h1, rfl⟩ := hp
      obtain ⟨k, -, hk⟩ := h x (g • x)
      rw [hk g rfl, hk g' h1.symm]
    · rintro ⟨y, x⟩
      obtain ⟨g, hg, -⟩ := h x y
      exact ⟨(g, x), by simp [hg]⟩

/-- URU5jgTvjhU-9274 (2:34:34) [prop] `f : E → F` is a monomorphism iff the diagonal
`E → E ×_F E` is an isomorphism; dually an epimorphism iff `F ⊔_E F → F` is one. -/
theorem mono_iff_diagonal_epi_iff_codiagonal {C : Type*} [Category C] {E F : C} (f : E ⟶ F)
    [HasPullback f f] [HasPushout f f] :
    (Mono f ↔ IsIso (pullback.diagonal f)) ∧ (Epi f ↔ IsIso (pushout.codiagonal f)) :=
  ⟨(pullback.isIso_diagonal_iff f).symm, (pushout.isIso_codiagonal_iff f).symm⟩

/-- URU5jgTvjhU-9402 (2:36:42) [prop] A morphism of sheaves is an epimorphism if and only if it is
one (a surjection) on every stalk. -/
theorem sheaf_epi_iff_stalks {F G : TopCat.Sheaf (Type u) X} (φ : F ⟶ G) :
    Epi φ ↔ ∀ x, Function.Surjective ((TopCat.Presheaf.stalkFunctor (Type u) x).map φ.hom) := by
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi]
  exact TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _

/-- URU5jgTvjhU-9900 (2:45:00) [cex] The structures of field and of integral domain are not stable
under products (`ℚ × ℚ` is not a domain), whereas structures defined by finite limits are. -/
theorem prod_not_isDomain : ¬ IsDomain (ℚ × ℚ) := by
  intro h
  have h0 : ((1 : ℚ), (0 : ℚ)) * ((0 : ℚ), (1 : ℚ)) = 0 := by ext <;> simp
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact one_ne_zero (congrArg Prod.fst h1)
  · exact one_ne_zero (congrArg Prod.snd h1)

/-- URU5jgTvjhU-10423 (2:53:43) The sections `f ∈ K(U)` whose multiplication is a monomorphism
of `K|_U`: for every `V ⊆ U`, multiplication by `f|_V` is injective on `K(V)`. -/
def regularSections (K : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X) :
    Set (K.obj.obj (op U)) :=
  {f | ∀ (V : Opens X) (i : V ⟶ U) (g : K.obj.obj (op V)), (K.obj.map i.op).hom f * g = 0 → g = 0}

/-- URU5jgTvjhU-10229 (2:50:29) [def] A sheaf of rings `K` is integral if `K' ⊔ 1 → K` (inclusion
and zero section) is an epimorphism: locally, every section is zero or in `K'`. -/
def IsIntegralSheaf (K : TopCat.Sheaf CommRingCat.{u} X) : Prop :=
  ∀ (U : Opens X) (f : K.obj.obj (op U)) (x : X), x ∈ U →
    ∃ (V : Opens X) (i : V ⟶ U), x ∈ V ∧
      ((K.obj.map i.op).hom f = 0 ∨ (K.obj.map i.op).hom f ∈ regularSections K V)

/-- URU5jgTvjhU-10358 (2:52:38) [prop] For two sheaves `K`, `L`, the presheaf
`U ↦ Hom(K|_U, L|_U)` is a sheaf. -/
theorem presheafHom_isSheaf (K L : TopCat.Sheaf (Type u) X) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (presheafHom K.obj L.obj) :=
  Presheaf.IsSheaf.hom K.obj L.obj L.property

/-- URU5jgTvjhU-10423 (2:53:43) [prop] The sections whose multiplications are monomorphisms form a
subpresheaf `K'` of `K`: stable under restriction ... -/
theorem regularSections_res (K : TopCat.Sheaf CommRingCat.{u} X) {U W : Opens X} (j : W ⟶ U)
    {f : K.obj.obj (op U)} (hf : f ∈ regularSections K U) :
    (K.obj.map j.op).hom f ∈ regularSections K W := by
  intro V i g hg
  apply hf V (i ≫ j) g
  rwa [op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]

/-- URU5jgTvjhU-10423 (2:53:43) [prop] ... and membership in `K'` is a local property, so `K'` is a
subsheaf. -/
theorem regularSections_local (K : TopCat.Sheaf CommRingCat.{u} X) {ι : Type u} (U : ι → Opens X)
    (f : K.obj.obj (op (iSup U)))
    (hf : ∀ i, (K.obj.map (Opens.leSupr U i).op).hom f ∈ regularSections K (U i)) :
    f ∈ regularSections K (iSup U) := by
  intro V i g hg
  have hcov : V ≤ iSup fun k => V ⊓ U k := by
    intro x hx
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (i.le hx)
    exact Opens.mem_iSup.2 ⟨k, ⟨hx, hk⟩⟩
  refine TopCat.Sheaf.eq_of_locally_eq' K (fun k => V ⊓ U k) V
    (fun k => homOfLE inf_le_left) hcov g 0 fun k => ?_
  rw [map_zero]
  apply hf k (V ⊓ U k) (homOfLE inf_le_right)
  have h := congrArg (K.obj.map (homOfLE (inf_le_left : V ⊓ U k ≤ V)).op).hom hg
  rw [map_mul, map_zero] at h
  rw [← h]
  congr 1
  simp only [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp, ← op_comp]
  rfl

/-! ## Generating families and images -/

/-- URU5jgTvjhU-10756 (2:59:16) [def] `(Zᵢ)` is a generating family if every monomorphism
`E → F` inducing bijections `Hom(Zᵢ, E) → Hom(Zᵢ, F)` is an isomorphism (SGA 4 I 7.1). -/
def IsGeneratingFamily {C : Type*} [Category C] {ι : Type*} (Z : ι → C) : Prop :=
  ∀ ⦃E F : C⦄ (m : E ⟶ F) [Mono m],
    (∀ i, Function.Bijective fun h : Z i ⟶ E => h ≫ m) → IsIso m

/-- The functors `Hom(Zᵢ, -)` form a conservative family. -/
def IsConservativeFamily {C : Type*} [Category C] {ι : Type*} (Z : ι → C) : Prop :=
  ∀ ⦃E F : C⦄ (f : E ⟶ F), (∀ i, Function.Bijective fun h : Z i ⟶ E => h ≫ f) → IsIso f

/-- URU5jgTvjhU-10884 (3:01:24) [prop] In a category with fibre products (such as `Sh(X)`),
`(Zᵢ)` is generating if and only if the family of functors `Hom(Zᵢ, -)` is conservative. -/
theorem isGeneratingFamily_iff {C : Type*} [Category C] [HasPullbacks C] {ι : Type*}
    (Z : ι → C) : IsGeneratingFamily Z ↔ IsConservativeFamily Z := by
  constructor
  · intro hZ E F f hf
    have hmono : Mono f := by
      rw [← pullback.isIso_diagonal_iff]
      apply hZ (pullback.diagonal f)
      intro i
      refine ⟨fun a b h => (cancel_mono _).1 h, fun h => ?_⟩
      have e : h ≫ pullback.fst f f = h ≫ pullback.snd f f :=
        (hf i).1 (by simp [Category.assoc, pullback.condition])
      refine ⟨h ≫ pullback.fst f f, ?_⟩
      apply pullback.hom_ext
      · simp
      · simp [e]
    exact hZ f hf
  · intro hZ E F m _ hm
    exact hZ m hm

/-- URU5jgTvjhU-11028 (3:03:48) [prop] In `Sh(X)` every morphism factors as an epimorphism followed
by a monomorphism (the image sheaf). -/
theorem sheaf_image {F G : Sheaf (Opens.grothendieckTopology X) (Type u)} (f : F ⟶ G) :
    Sheaf.toImage f ≫ Sheaf.imageι f = f ∧ Epi (Sheaf.toImage f) ∧ Mono (Sheaf.imageι f) :=
  ⟨Sheaf.toImage_ι f, inferInstance, inferInstance⟩

/-- URU5jgTvjhU-11157 (3:05:57) [prop] In `Sh(X)`, a monomorphism that is an epimorphism is an
isomorphism (the category is balanced). -/
theorem sheaf_isIso_of_mono_of_epi {F G : Sheaf (Opens.grothendieckTopology X) (Type u)} (f : F ⟶ G) [Mono f] [Epi f] :
    IsIso f :=
  isIso_of_mono_of_epi f

/-- URU5jgTvjhU-11349 (3:09:09) [def] An open set `U` defines a sheaf: `U(V)` is a singleton if
`V ⊆ U`, empty otherwise (the presheaf represented by `U`). -/
theorem yoneda_isSheaf (U : Opens X) : TopCat.Presheaf.IsSheaf (X := X) (yoneda.obj U) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types]
  intro ι V sf _
  exact ⟨homOfLE (iSup_le fun i => (sf i).le), fun i => Subsingleton.elim (α := V i ⟶ U) _ _,
    fun _ _ => Subsingleton.elim (α := iSup V ⟶ U) _ _⟩

/-- The sheaf represented by an open set. -/
def opensSheaf (U : Opens X) : Sheaf (Opens.grothendieckTopology X) (Type u) :=
  ⟨yoneda.obj U, yoneda_isSheaf U⟩

/-- URU5jgTvjhU-11484 (3:11:24) [prop] For every sheaf `E`, `Hom(U, E) = E(U)` ... -/
def opensSheaf_hom (U : Opens X) (E : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    (opensSheaf U ⟶ E) ≃ E.obj.obj (op U) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans yonedaEquiv

/-- The identification `Hom(U, E) = E(U)` is natural in `E`. -/
theorem opensSheaf_hom_comp (U : Opens X) {E F : Sheaf (Opens.grothendieckTopology X) (Type u)}
    (a : opensSheaf U ⟶ E) (k : E ⟶ F) :
    opensSheaf_hom U F (a ≫ k) = k.hom.app (op U) (opensSheaf_hom U E a) :=
  rfl

/-- URU5jgTvjhU-11484 (3:11:24) [prop] ... so the open sets form a small generating family of
`Sh(X)`: two morphisms agreeing after every `U → E` are equal. -/
theorem opensSheaf_separating {E F : Sheaf (Opens.grothendieckTopology X) (Type u)} (f g : E ⟶ F)
    (h : ∀ (U : Opens X) (a : opensSheaf U ⟶ E), a ≫ f = a ≫ g) : f = g := by
  apply (sheafToPresheaf _ _).map_injective
  ext U s
  obtain ⟨a, rfl⟩ := (opensSheaf_hom U.unop E).surjective s
  have h1 := congrArg (opensSheaf_hom U.unop F) (h U.unop a)
  rw [opensSheaf_hom_comp, opensSheaf_hom_comp] at h1
  exact h1

/-! ## Abelian sheaves and injectives -/

/-- URU5jgTvjhU-11555 (3:12:35) [prop] The abelian sheaves on `X` form an abelian category. -/
theorem ab_abelian : Nonempty (Abelian (TopCat.Sheaf AddCommGrpCat.{u} X)) := ⟨inferInstance⟩

/-- URU5jgTvjhU-11687 (3:14:47) [prop] `Ab(X)` admits limits and colimits, and filtered colimits
are exact there (it is a Grothendieck abelian category). -/
theorem ab_grothendieck : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstance

/-- URU5jgTvjhU-11816 (3:16:56) [def] An abelian sheaf `I` is injective if every `F → I` extends
along every monomorphism `F → G` (Mathlib's `Injective`). -/
example {I F G : TopCat.Sheaf AddCommGrpCat.{u} X} [Injective I] (g : F ⟶ I) (f : F ⟶ G) [Mono f] :
    ∃ h : G ⟶ I, f ≫ h = g :=
  Injective.factors g f

/-- URU5jgTvjhU-11881 (3:18:01) [prop] An abelian category with exact filtered colimits and a
generator has enough injectives; this is the case of `Ab(X)`. -/
theorem ab_enoughInjectives : EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstance

/-- URU5jgTvjhU-11945 (3:19:05) [prop] For a sheaf of rings `A`, `Mod(A)` is abelian with exact
filtered colimits and a generator, hence has enough injectives. -/
theorem modules_enoughInjectives (A : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} A) ∧ EnoughInjectives (SheafOfModules.{u} A) :=
  ⟨inferInstance, inferInstance⟩

end

end Buffalo.Topos.Part01
