import Mathlib

/-!
# Buffalo, algebraic geometry, part 08 (a): 6 July 1973 (from 10:19:03) and 9 July 1973, tape 1

The entries of `docs/buffalo-ag/index.tex` lines 1054–1068 (video `Oqhr-Gt66es`, 10:19:03–10:52:45)
and 1072–1098 (video `vuys5SNs2eQ`, 0:00:02–0:45:50): flat and faithfully flat modules and
morphisms, flatness criteria over Dedekind rings, faithfully flat base change.

Conventions. Modules are mathlib's `Module.Flat` and `Module.FaithfullyFlat`; spectra are
`PrimeSpectrum` with `PrimeSpectrum.comap`; schemes and their morphism properties are those of
`Mathlib.AlgebraicGeometry` (`Flat`, `Surjective`, `QuasiCompact`, `UniversallyInjective`…). A
*maximal point* of a space is a point whose closure is an irreducible component; a map
*dominates* a closed irreducible set `Y'` when its image is dense in `Y'`.
-/

open CategoryTheory Limits TensorProduct Topology PrimeSpectrum AlgebraicGeometry

universe u v

namespace Buffalo.AG.Part08

noncomputable section

/-! ### Flat and faithfully flat modules -/

section Modules

variable {A : Type u} [CommRing A]

/-- Oqhr-Gt66es-37143 (10:19:03) [def] `M` is flat if `M ⊗_A -` is exact, faithfully flat if
moreover `M ⊗_A N = 0` implies `N = 0` (mathlib: `Module.Flat`,
`Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality`). -/
theorem def_37143 (M : Type v) [AddCommGroup M] [Module A M] :
    Module.FaithfullyFlat A M ↔
      Module.Flat A M ∧ ∀ (N : Type max u v) [AddCommGroup N] [Module A N],
        Subsingleton (M ⊗[A] N) → Subsingleton N :=
  Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality A M

/-- Oqhr-Gt66es-37209 (10:20:09) [prop] A flat module `M` is faithfully flat if and only if `u` is
injective (resp. surjective, bijective) as soon as `M ⊗ u` is (mathlib for the forward
directions: `Module.FaithfullyFlat.lTensor_injective_iff_injective` and its variants; the converses
test `N → 0` and `0 → N`). -/
theorem prop_37209 (M : Type v) [AddCommGroup M] [Module A M] [Module.Flat A M] :
    (Module.FaithfullyFlat A M ↔ ∀ (N P : Type max u v) [AddCommGroup N] [Module A N]
        [AddCommGroup P] [Module A P] (w : N →ₗ[A] P),
        Function.Injective (w.lTensor M) → Function.Injective w) ∧
    (Module.FaithfullyFlat A M ↔ ∀ (N P : Type max u v) [AddCommGroup N] [Module A N]
        [AddCommGroup P] [Module A P] (w : N →ₗ[A] P),
        Function.Surjective (w.lTensor M) → Function.Surjective w) ∧
    (Module.FaithfullyFlat A M ↔ ∀ (N P : Type max u v) [AddCommGroup N] [Module A N]
        [AddCommGroup P] [Module A P] (w : N →ₗ[A] P),
        Function.Bijective (w.lTensor M) → Function.Bijective w) := by
  have inj : ∀ (N : Type max u v) [AddCommGroup N] [Module A N] [Subsingleton (M ⊗[A] N)],
      Function.Injective ((0 : N →ₗ[A] PUnit.{max u v + 1}).lTensor M) :=
    fun N _ _ _ x y _ => Subsingleton.elim x y
  have sur : ∀ (N : Type max u v) [AddCommGroup N] [Module A N] [Subsingleton (M ⊗[A] N)],
      Function.Surjective ((0 : PUnit.{max u v + 1} →ₗ[A] N).lTensor M) :=
    fun N _ _ _ y => ⟨0, Subsingleton.elim _ _⟩
  refine ⟨⟨fun _ N P _ _ _ _ w => (Module.FaithfullyFlat.lTensor_injective_iff_injective A M w).1,
      fun H => (def_37143 M).2 ⟨inferInstance, fun N _ _ _ => ?_⟩⟩,
    ⟨fun _ N P _ _ _ _ w => (Module.FaithfullyFlat.lTensor_surjective_iff_surjective A M w).1,
      fun H => (def_37143 M).2 ⟨inferInstance, fun N _ _ _ => ?_⟩⟩,
    ⟨fun _ N P _ _ _ _ w => (Module.FaithfullyFlat.lTensor_bijective_iff_bijective A M w).1,
      fun H => (def_37143 M).2 ⟨inferInstance, fun N _ _ _ => ?_⟩⟩⟩
  · exact ⟨fun x y => H N PUnit _ (inj N) (Subsingleton.elim _ _)⟩
  · refine ⟨fun x y => ?_⟩
    obtain ⟨a, rfl⟩ := H PUnit N _ (sur N) x
    obtain ⟨b, rfl⟩ := H PUnit N _ (sur N) y
    simp
  · exact ⟨fun x y => (H N PUnit _ ⟨inj N, fun z => ⟨0, Subsingleton.elim _ _⟩⟩).1
      (Subsingleton.elim _ _)⟩

/-- Oqhr-Gt66es-37402 (10:23:22) [prop] `M` is faithfully flat if and only if it is flat and
`M/𝔪M ≠ 0` for every maximal ideal `𝔪` (mathlib: `Module.FaithfullyFlat.iff_flat_and_proper_ideal`,
for all proper ideals). -/
theorem prop_37402 (M : Type v) [AddCommGroup M] [Module A M] :
    Module.FaithfullyFlat A M ↔
      Module.Flat A M ∧ ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔪 • (⊤ : Submodule A M) ≠ ⊤ := by
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal A M]
  refine and_congr_right fun _ => ⟨fun h 𝔪 h𝔪 => h 𝔪 h𝔪.ne_top, fun h I hI => ?_⟩
  obtain ⟨𝔪, h𝔪, hI𝔪⟩ := I.exists_le_maximal hI
  intro hItop
  apply h 𝔪 h𝔪
  have := Submodule.smul_mono_left (N := (⊤ : Submodule A M)) hI𝔪
  rw [hItop] at this
  exact top_le_iff.1 this

variable {B : Type v} [CommRing B] [Algebra A B]

/-- Oqhr-Gt66es-37726 (10:28:46) [prop] `B` is faithfully flat over `A` if and only if it is flat
and `Spec B → Spec A` is surjective (mathlib: `Module.FaithfullyFlat.of_comap_surjective`,
`PrimeSpectrum.comap_surjective_of_faithfullyFlat`). -/
theorem prop_37726 :
    Module.FaithfullyFlat A B ↔
      Module.Flat A B ∧ Function.Surjective (comap (algebraMap A B)) :=
  ⟨fun _ => ⟨inferInstance, comap_surjective_of_faithfullyFlat⟩,
    fun ⟨_, h⟩ => Module.FaithfullyFlat.of_comap_surjective h⟩

/-- Oqhr-Gt66es-37918 (10:31:58) [prop] For a local homomorphism of local rings, `B` flat over
`A` is equivalent to `B` faithfully flat, and then `Spec B → Spec A` is surjective (mathlib:
`Module.FaithfullyFlat.of_flat_of_isLocalHom`). -/
theorem prop_37918 [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] :
    (Module.Flat A B ↔ Module.FaithfullyFlat A B) ∧
      (Module.Flat A B → Function.Surjective (comap (algebraMap A B))) :=
  ⟨⟨fun _ => .of_flat_of_isLocalHom, fun _ => inferInstance⟩,
    fun _ => have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)
      comap_surjective_of_faithfullyFlat⟩

/-- Oqhr-Gt66es-38052 (10:34:12) [prop] If `B` is flat over `A`, any localization `B[T⁻¹]` is
flat over `A[S⁻¹]` (for whatever `A[S⁻¹]`-algebra structure compatible with `A`); in particular the
local rings `B_𝔮` are flat over `A_𝔭` (mathlib: `Module.flat_iff_of_isLocalization`,
`Localization.flat`). -/
theorem prop_38052 [Module.Flat A B] (S : Submonoid A) (T : Submonoid B)
    [Algebra (Localization S) (Localization T)]
    [IsScalarTower A (Localization S) (Localization T)] :
    Module.Flat (Localization S) (Localization T) :=
  (Module.flat_iff_of_isLocalization (Localization S) S (Localization T)).2 inferInstance

/-- Oqhr-Gt66es-38114 (10:35:14) [prop] If `B` is flat over `A`, `Spec B → Spec A` is
generalizing (mathlib: `RingHom.Flat.generalizingMap_comap`). -/
theorem prop_38114 [Module.Flat A B] : GeneralizingMap (comap (algebraMap A B)) :=
  RingHom.Flat.generalizingMap_comap (RingHom.flat_algebraMap_iff.2 inferInstance)

/-- Oqhr-Gt66es-38243 (10:37:23) [prop] A module is flat if and only if its fibres (stalks) are flat
over the fibres of the sheaf of rings; on `Spec A` (stalk of `M~` at `𝔭` = `M_𝔭`): `M` is flat
over `A` iff every `M_𝔭` is flat over `A_𝔭` (mathlib: `Module.Flat.localizedModule`,
`Module.flat_of_localized_maximal`). -/
theorem prop_38243 (M : Type v) [AddCommGroup M] [Module A M] :
    Module.Flat A M ↔ ∀ (𝔭 : Ideal A) [𝔭.IsPrime],
      Module.Flat (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl M) := by
  refine ⟨fun _ 𝔭 _ => inferInstance, fun h => Module.flat_of_localized_maximal M fun P _ => ?_⟩
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime P) P.primeCompl _).1 (h P)

/-- Oqhr-Gt66es-38374 (10:39:34) [prop] `M~` on `Spec A` is flat if and only if `M` is flat
(stalks of `M~` are the `M_𝔭`; see `prop_38243`). -/
theorem prop_38374 (M : Type v) [AddCommGroup M] [Module A M] :
    (∀ (𝔭 : Ideal A) [𝔭.IsPrime],
      Module.Flat (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl M)) ↔ Module.Flat A M :=
  (prop_38243 M).symm

/-- Oqhr-Gt66es-39030 (10:50:30) [prop] `f` faithfully flat iff `f^*` is exact and faithful; for
`Spec B → Spec A`, `f^* = B ⊗_A -`: `B` is faithfully flat iff `B ⊗_A -` preserves injections and
`B ⊗_A N = 0 ⇒ N = 0` (mathlib: `Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality`,
`Module.Flat.iff_lTensor_preserves_injective_linearMap`). -/
theorem prop_39030 :
    Module.FaithfullyFlat A B ↔
      (∀ (N P : Type (max u v)) [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
        (w : N →ₗ[A] P), Function.Injective w → Function.Injective (w.lTensor B)) ∧
      ∀ (N : Type max u v) [AddCommGroup N] [Module A N],
        Subsingleton (B ⊗[A] N) → Subsingleton N := by
  rw [def_37143, Module.Flat.iff_lTensor_preserves_injective_linearMap]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    intro N P _ _ _ _ w hw
    exact h1 w hw
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    intro N P _ _ _ _ w hw
    exact h1 N P w hw

end Modules

/-! ### Generalizing maps and irreducible components (topology) -/

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous generalizing map between quasi-sober spaces sends irreducible components to sets
whose closure is an irreducible component. -/
theorem closure_image_mem_irreducibleComponents [QuasiSober X] [QuasiSober Y] {f : X → Y}
    (hf : Continuous f) (hg : GeneralizingMap f) {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    closure (f '' Z) ∈ irreducibleComponents Y := by
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hη : closure {hZ.1.genericPoint} = Z := hZ.1.closure_genericPoint hZc
  have hηZ : hZ.1.genericPoint ∈ Z := hη.le (subset_closure (Set.mem_singleton _))
  refine ⟨(hZ.1.image f hf.continuousOn).closure, fun W hW hsub => ?_⟩
  have hw : closure {hW.genericPoint} = closure W := hW.genericPoint_closure_eq
  have h1 : hW.genericPoint ⤳ f hZ.1.genericPoint := by
    rw [specializes_iff_mem_closure, hw]
    exact subset_closure (hsub (subset_closure ⟨_, hηZ, rfl⟩))
  obtain ⟨x', hx', hfx'⟩ := hg h1
  have hZx' : Z ⊆ closure {x'} := by
    rw [← hη]; exact closure_minimal (by simpa [← specializes_iff_mem_closure] using hx')
      isClosed_closure
  have hx'Z : x' ∈ Z := hZ.2 isIrreducible_singleton.closure hZx' (subset_closure rfl)
  calc W ⊆ closure W := subset_closure
    _ = closure {hW.genericPoint} := hw.symm
    _ ⊆ closure (f '' Z) := closure_mono (by simpa [← hfx'] using ⟨x', hx'Z, rfl⟩)

/-- A *maximal point* is a point whose closure is an irreducible component. -/
def IsMaximalPoint (x : X) : Prop := closure ({x} : Set X) ∈ irreducibleComponents X

/-- vuys5SNs2eQ-2 (0:00:02) [prop] A generalizing morphism sends the maximal points of `X` (generic
points of the irreducible components) to maximal points of `Y`. -/
theorem prop_2 [QuasiSober X] [QuasiSober Y] {f : X → Y} (hf : Continuous f)
    (hg : GeneralizingMap f) {x : X} (hx : IsMaximalPoint x) : IsMaximalPoint (f x) := by
  have := closure_image_mem_irreducibleComponents hf hg hx
  have e : closure (f '' closure {x}) = closure {f x} :=
    le_antisymm (closure_minimal ((image_closure_subset_closure_image hf).trans
      (by rw [Set.image_singleton])) isClosed_closure)
      (closure_mono (Set.singleton_subset_iff.2 ⟨x, subset_closure (Set.mem_singleton x), rfl⟩))
  rwa [e] at this

/-- vuys5SNs2eQ-131 (0:02:11) [prop] `f` is generalizing if and only if, for every irreducible
closed `Y' ⊂ Y`, every irreducible component of the subspace `f⁻¹(Y')` dominates `Y'` (for
`X` quasi-sober and `Y` sober, e.g. schemes). -/
theorem prop_131 [QuasiSober X] [QuasiSober Y] [T0Space Y] {f : X → Y} (hf : Continuous f) :
    GeneralizingMap f ↔ ∀ Y' : Set Y, IsClosed Y' → IsIrreducible Y' →
      ∀ C ∈ irreducibleComponents (f ⁻¹' Y'), Y' ⊆ closure ((f ∘ Subtype.val) '' C) := by
  constructor
  · intro hg Y' hY'c hY' C hC
    have : QuasiSober (f ⁻¹' Y') := ((hY'c.preimage hf).isClosedEmbedding_subtypeVal).quasiSober
    have hCc := isClosed_of_mem_irreducibleComponents C hC
    have hξ : closure {hC.1.genericPoint} = C := hC.1.closure_genericPoint hCc
    have hy : closure {hY'.genericPoint} = Y' := hY'.closure_genericPoint hY'c
    have h1 : hY'.genericPoint ⤳ f hC.1.genericPoint := by
      rw [specializes_iff_mem_closure, hy]; exact hC.1.genericPoint.2
    obtain ⟨x', hx', hfx'⟩ := hg h1
    have hx'Y : x' ∈ f ⁻¹' Y' := by
      show f x' ∈ Y'
      rw [hfx']; exact hy.le (subset_closure (Set.mem_singleton _))
    have hsp : (⟨x', hx'Y⟩ : f ⁻¹' Y') ⤳ hC.1.genericPoint := by
      rwa [subtype_specializes_iff]
    have hCx' : C ⊆ closure {(⟨x', hx'Y⟩ : f ⁻¹' Y')} := by
      rw [← hξ]; exact closure_minimal (by simpa [← specializes_iff_mem_closure] using hsp)
        isClosed_closure
    have hx'C : (⟨x', hx'Y⟩ : f ⁻¹' Y') ∈ C :=
      hC.2 isIrreducible_singleton.closure hCx' (subset_closure rfl)
    calc Y' = closure {hY'.genericPoint} := hy.symm
      _ ⊆ _ := closure_mono (Set.singleton_subset_iff.2
        (show hY'.genericPoint ∈ (f ∘ Subtype.val) '' C from ⟨⟨x', hx'Y⟩, hx'C, hfx'⟩))
  · intro H x y hxy
    have hx : x ∈ f ⁻¹' closure ({y} : Set Y) := by
      simpa [← specializes_iff_mem_closure] using hxy
    have : QuasiSober (f ⁻¹' closure ({y} : Set Y)) :=
      ((isClosed_closure.preimage hf).isClosedEmbedding_subtypeVal).quasiSober
    obtain ⟨C, hC, hxC⟩ : ∃ C ∈ irreducibleComponents (f ⁻¹' closure ({y} : Set Y)),
        (⟨x, hx⟩ : f ⁻¹' closure ({y} : Set Y)) ∈ C :=
      ⟨_, irreducibleComponent_mem_irreducibleComponents _, mem_irreducibleComponent⟩
    have hCc := isClosed_of_mem_irreducibleComponents C hC
    have hξ : closure {hC.1.genericPoint} = C := hC.1.closure_genericPoint hCc
    have hdom := H _ isClosed_closure isIrreducible_singleton.closure C hC
    have himg : (f ∘ Subtype.val) '' C ⊆ closure {f hC.1.genericPoint} := by
      rintro _ ⟨z, hz, rfl⟩
      have hz' : hC.1.genericPoint ⤳ z := by
        rw [specializes_iff_mem_closure]; exact hξ.ge hz
      exact specializes_iff_mem_closure.1 ((hz'.map continuous_subtype_val).map hf)
    have h1 : f hC.1.genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure]
      exact closure_minimal himg isClosed_closure (hdom (subset_closure rfl))
    have h2 : y ⤳ f hC.1.genericPoint := by
      rw [specializes_iff_mem_closure]; exact hC.1.genericPoint.2
    refine ⟨hC.1.genericPoint, ?_, (h1.antisymm h2).eq⟩
    have : hC.1.genericPoint ⤳ (⟨x, hx⟩ : f ⁻¹' closure ({y} : Set Y)) := by
      rw [specializes_iff_mem_closure]; exact hξ.ge hxC
    exact (subtype_specializes_iff _ _).1 this

end Topology

/-! ### Flat morphisms of schemes -/

section Schemes

variable {X Y : Scheme.{u}}

/-- Oqhr-Gt66es-38502 (10:41:42) [prop] A module `M` on `X` is flat relative to `f` if each `M_x` is
flat over `𝒪_{Y,f(x)}`. For `M = 𝒪_X` this is mathlib's `Flat f` (`Flat.iff_flat_stalkMap`). -/
theorem prop_38502 (f : X ⟶ Y) : Flat f ↔ ∀ x, (f.stalkMap x).hom.Flat :=
  Flat.iff_flat_stalkMap f

/-- Oqhr-Gt66es-38630 (10:43:50) [def] `f` is flat (mathlib: `AlgebraicGeometry.Flat`, local on
both sides, `HasRingHomProperty @Flat RingHom.Flat`); equivalently all `𝒪_{X,x}` are flat over
`𝒪_{Y,f(x)}`; for `Spec B → Spec A`, `B` is flat over `A` (`Flat.SpecMap_iff`). -/
theorem def_38630 (f : X ⟶ Y) {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (Flat f ↔ ∀ x, (f.stalkMap x).hom.Flat) ∧ (Flat (Spec.map φ) ↔ φ.hom.Flat) :=
  ⟨Flat.iff_flat_stalkMap f, Flat.SpecMap_iff⟩

/-- Oqhr-Gt66es-38767 (10:46:07) [prop] A flat morphism is generalizing, hence universally
generalizing; flat morphisms contain the isomorphisms and are stable under composition and base
change (mathlib: `Flat.generalizingMap`, `Flat.isStableUnderBaseChange`, `IsMultiplicative`). -/
theorem prop_38767 (f : X ⟶ Y) [Flat f] :
    GeneralizingMap f ∧ (∀ (Y' : Scheme.{u}) (g : Y' ⟶ Y), GeneralizingMap (pullback.snd f g)) ∧
      MorphismProperty.IsMultiplicative @Flat.{u} ∧ MorphismProperty.IsStableUnderBaseChange @Flat.{u} :=
  ⟨Flat.generalizingMap f, fun _ g => Flat.generalizingMap (pullback.snd f g), inferInstance,
    inferInstance⟩

/-- Oqhr-Gt66es-38963 (10:49:23) [def] `f` is faithfully flat if it is flat and surjective; these
morphisms are stable under composition and base change. -/
theorem def_38963 {Z S' : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : S' ⟶ Y)
    [Flat f] [Surjective f] [Flat g] [Surjective g] :
    (Flat (f ≫ g) ∧ Surjective (f ≫ g)) ∧
      (Flat (pullback.snd f h) ∧ Surjective (pullback.snd f h)) :=
  ⟨⟨inferInstance, inferInstance⟩, inferInstance, inferInstance⟩

/-- Oqhr-Gt66es-39165 (10:52:45) [prop] If `f` is flat, the closure of the image of every
irreducible component of `X` is an irreducible component of `Y`. -/
theorem prop_39165 (f : X ⟶ Y) [Flat f] {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    closure (f '' Z) ∈ irreducibleComponents Y :=
  closure_image_mem_irreducibleComponents f.continuous (Flat.generalizingMap f) hZ

/-- vuys5SNs2eQ-131 (0:02:11) [prop] For a field extension `k'/k` and a `k`-scheme `X`, every
irreducible component of `X_{k'}` dominates an irreducible component of `X` (the projection is
flat, being a base change of `Spec k' → Spec k`). -/
theorem prop_131_field (k k' : Type u) [Field k] [Field k'] (φ : k →+* k')
    (h : X ⟶ Spec (CommRingCat.of k)) {Z : Set ↥(pullback h (Spec.map (CommRingCat.ofHom φ)))}
    (hZ : Z ∈ irreducibleComponents _) :
    closure (pullback.fst h (Spec.map (CommRingCat.ofHom φ)) '' Z) ∈ irreducibleComponents X :=
  have : Flat (Spec.map (CommRingCat.ofHom φ)) :=
    Flat.SpecMap_iff.2 (RingHom.Flat.of_isField (Field.toIsField k) _)
  prop_39165 _ hZ

end Schemes

/-! ### Flatness criteria over Dedekind rings -/

section Criteria

variable {A : Type u} [CommRing A]

/-- vuys5SNs2eQ-327 (0:05:27) [prop] Over a principal ideal ring (domain), a module is flat if and
only if it is torsion-free (mathlib: `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`). -/
theorem prop_327 [IsDomain A] [IsPrincipalIdealRing A] (M : Type v) [AddCommGroup M] [Module A M] :
    Module.Flat A M ↔ Submodule.torsion A M = ⊥ :=
  Module.Flat.flat_iff_torsion_eq_bot_of_isBezout

/-- vuys5SNs2eQ-327 (0:05:27) [prop] The hypothesis "domain" cannot be dropped from `prop_327` if
torsion-free is read as `a m = 0 ⇒ a = 0 ∨ m = 0`: over the principal ideal ring `ℤ/4`, the module
`ℤ/4` is flat but `2 · 2 = 0`. -/
theorem cex_327 : Module.Flat (ZMod 4) (ZMod 4) ∧ (2 : ZMod 4) • (2 : ZMod 4) = 0 ∧
    (2 : ZMod 4) ≠ 0 :=
  ⟨inferInstance, by decide, by decide⟩

/-- vuys5SNs2eQ-390 (0:06:30) [prop] Over an integral domain, every flat module is torsion-free
(mathlib: `Module.Flat.torsion_eq_bot`). -/
theorem prop_390 [IsDomain A] (M : Type v) [AddCommGroup M] [Module A M] [Module.Flat A M] :
    Submodule.torsion A M = ⊥ :=
  Module.Flat.torsion_eq_bot

/-- vuys5SNs2eQ-455 (0:07:35) [prop] Over a Dedekind ring every torsion-free module is flat
(mathlib: `IsDedekindDomain.flat_iff_torsion_eq_bot`, proved by localizing at maximal ideals). -/
theorem prop_455 [IsDedekindDomain A] (M : Type v) [AddCommGroup M] [Module A M] :
    Module.Flat A M ↔ Submodule.torsion A M = ⊥ :=
  IsDedekindDomain.flat_iff_torsion_eq_bot

/-- vuys5SNs2eQ-520 (0:08:40) [prop] A filtered inductive limit of flat modules is flat (proved
with the equational criterion `Module.Flat.iff_forall_isTrivialRelation`). -/
theorem prop_520 {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]
    {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module A (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[A] G j) [DirectedSystem G (f · · ·)]
    [∀ i, Module.Flat A (G i)] : Module.Flat A (Module.DirectLimit G f) := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l c x} hx => ?_
  choose i y hy using fun k => Module.DirectLimit.exists_of (x k)
  obtain ⟨j, hj⟩ := Finset.exists_le (Finset.univ.image i)
  have hij : ∀ k, i k ≤ j := fun k => hj _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  have hz : ∀ k, Module.DirectLimit.of A ι G f j (f _ _ (hij k) (y k)) = x k := fun k => by
    rw [Module.DirectLimit.of_f, hy]
  have hsum : Module.DirectLimit.of A ι G f j (∑ k, c k • f _ _ (hij k) (y k)) = 0 := by
    simp only [map_sum, map_smul, hz, hx]
  obtain ⟨j', hjj', h0⟩ := Module.DirectLimit.of.zero_exact hsum
  have h' : ∑ k, c k • f j j' hjj' (f _ _ (hij k) (y k)) = 0 := by
    simpa only [map_sum, map_smul] using h0
  obtain ⟨n, a, w, hw1, hw2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h'
  refine ⟨n, a, fun m => Module.DirectLimit.of A ι G f j' (w m), fun k => ?_, hw2⟩
  rw [← hz k, ← Module.DirectLimit.of_f (hij := hjj'), show f j j' hjj' (f _ _ (hij k) (y k)) =
    ∑ m, a k m • w m from hw1 k, map_sum]
  simp only [map_smul]

/-- Over a Dedekind ring, an algebra is flat iff no nonzero scalar kills a nonzero element. -/
theorem flat_iff_smul_eq_zero [IsDedekindDomain A] {B : Type v} [CommRing B]
    [Algebra A B] : Module.Flat A B ↔ ∀ (a : A) (b : B), a • b = 0 → a = 0 ∨ b = 0 := by
  rw [← Module.isTorsionFree_iff_smul_eq_zero]
  exact ⟨fun _ => inferInstance, fun _ => inferInstance⟩

/-- vuys5SNs2eQ-584 (0:09:44) [prop] `Y` integral regular of dimension `1`, `X` reduced over `Y`:
`X` is flat over `Y` iff every irreducible component of `X` dominates `Y`. Affine case: `A` a
Dedekind ring, `B` a reduced `A`-algebra; `B` is flat iff every minimal prime of `B` lies over the
generic point `(0)` of `Spec A`. -/
theorem prop_584 [IsDedekindDomain A] {B : Type v} [CommRing B] [Algebra A B]
    [IsReduced B] :
    Module.Flat A B ↔ ∀ q ∈ minimalPrimes B, q.comap (algebraMap A B) = ⊥ := by
  rw [flat_iff_smul_eq_zero]
  constructor
  · intro h q hq
    refine eq_bot_iff.2 fun a ha => ?_
    have hz := notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.mem_comap.1 ha) hq
    by_contra ha0
    apply hz
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact (h a x (by rw [Algebra.smul_def]; exact hx)).resolve_left (by simpa using ha0)
    · exact (h a x (by rw [Algebra.smul_def, mul_comm]; exact hx)).resolve_left (by simpa using ha0)
  · intro h a b hab
    by_contra! hne
    obtain ⟨q, hq, hbq⟩ : ∃ q ∈ minimalPrimes B, b ∉ q := by
      by_contra! H
      have : b ∈ (⊥ : Ideal B).radical := by
        rw [← Ideal.sInf_minimalPrimes]; exact Submodule.mem_sInf.2 H
      exact hne.2 (IsReduced.eq_zero b this)
    have hmem : algebraMap A B a * b ∈ q := by rw [← Algebra.smul_def, hab]; exact q.zero_mem
    have : a ∈ q.comap (algebraMap A B) :=
      (hq.1.1.mem_or_mem hmem).resolve_right hbq
    rw [h q hq] at this
    exact hne.1 this

/-- vuys5SNs2eQ-587 (0:09:47) [prop] Without `X` reduced (`X` locally noetherian), `X` is flat over
`Y` iff all associated points of `X` map to the generic point of `Y`. Affine case: `A` Dedekind,
`B` a noetherian `A`-algebra; `B` is flat iff every associated prime of `B` lies over `(0)`. -/
theorem prop_587 [IsDedekindDomain A] {B : Type v} [CommRing B] [Algebra A B]
    [IsNoetherianRing B] :
    Module.Flat A B ↔ ∀ P ∈ associatedPrimes B B, P.comap (algebraMap A B) = ⊥ := by
  rw [flat_iff_smul_eq_zero]
  have hzd := biUnion_associatedPrimes_eq_zero_divisors B B
  constructor
  · intro h P hP
    refine eq_bot_iff.2 fun a ha => ?_
    have : algebraMap A B a ∈ ⋃ p ∈ associatedPrimes B B, (p : Set B) :=
      Set.mem_biUnion hP (Ideal.mem_comap.1 ha)
    rw [hzd] at this
    obtain ⟨b, hb0, hb⟩ := this
    rcases h a b (by rw [Algebra.smul_def]; exact hb) with h0 | h0
    · simp [h0]
    · exact absurd h0 hb0
  · intro h a b hab
    by_contra! hne
    have : algebraMap A B a ∈ {r : B | ∃ x : B, x ≠ 0 ∧ r • x = 0} :=
      ⟨b, hne.2, by rw [smul_eq_mul, ← Algebra.smul_def, hab]⟩
    rw [← hzd] at this
    obtain ⟨P, hP, haP⟩ := Set.mem_iUnion₂.1 this
    have : a ∈ P.comap (algebraMap A B) := haP
    rw [h P hP] at this
    exact hne.1 this

end Criteria

/-! ### Faithfully flat base change

Conventions: `g : S' ⟶ S` is the base change, `f : X ⟶ S`, and `f' = pullback.snd f g :
X ×_S S' ⟶ S'` (with `g' = pullback.fst f g : X' ⟶ X`). -/

section BaseChange

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]

/-- vuys5SNs2eQ-1166 (0:19:26) [prop] If `f` is faithfully flat, `Y' ↦ f⁻¹(Y')` is injective on
subschemes. Proved for open subschemes (`f` surjective) and for closed subschemes of an affine
scheme (`Ideal.map_injective_of_faithfullyFlat`). -/
theorem prop_1166 {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [Module.FaithfullyFlat A B] :
    Function.Injective (fun U : Y.Opens => f ⁻¹ᵁ U) ∧
      Function.Injective (Ideal.map (algebraMap A B)) := by
  refine ⟨fun U V h => ?_, Ideal.map_injective_of_faithfullyFlat⟩
  ext1
  exact (Set.preimage_injective.2 f.surjective) (congrArg SetLike.coe h)

/-- vuys5SNs2eQ-1230 (0:20:30) [prop] If `f` is faithfully flat, the inverse image of
quasi-coherent modules is exact and faithful, and two submodules that become equal are equal.
Affine case (mathlib: `Module.FaithfullyFlat.lTensor_exact_iff_exact`,
`Submodule.baseChange_injective`). -/
theorem prop_1230 [Module.FaithfullyFlat A B] {M N P : Type v} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P] (u : M →ₗ[A] N) (w : N →ₗ[A] P) :
    (Function.Exact (u.lTensor B) (w.lTensor B) ↔ Function.Exact u w) ∧
      (u.lTensor B = 0 ↔ u = 0) ∧
      ∀ p q : Submodule A M, p.baseChange B = q.baseChange B → p = q :=
  ⟨Module.FaithfullyFlat.lTensor_exact_iff_exact A B u w,
    (Module.FaithfullyFlat.zero_iff_lTensor_zero A B u).symm,
    fun _ _ h => Submodule.baseChange_injective h⟩

/-- vuys5SNs2eQ-1299 (0:21:39) [prop] If `S' → S` is faithfully flat, base change is faithful:
`Hom_S(X, Y) → Hom_{S'}(X', Y')` is injective. No quasi-compactness is needed: `X' → X` is flat and
surjective, hence an epimorphism (mathlib: `epi_of_flat_of_surjective`). -/
theorem prop_1299 {S S' X Y : Scheme.{u}} (g : S' ⟶ S) [Flat g] [Surjective g] (hX : X ⟶ S)
    (hY : Y ⟶ S) (u v : X ⟶ Y) (hu : u ≫ hY = hX) (hv : v ≫ hY = hX)
    (h : pullback.map hX g hY g u (𝟙 _) (𝟙 _) (by simp [hu]) (by simp) =
      pullback.map hX g hY g v (𝟙 _) (𝟙 _) (by simp [hv]) (by simp)) : u = v := by
  have := Flat.epi_of_flat_of_surjective (pullback.fst hX g)
  rw [← cancel_epi (pullback.fst hX g)]
  have := congrArg (· ≫ pullback.fst hY g) h
  simpa using this

section Sections

variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
  (H : IsPullback g iY iX f) {US : S.Opens} {UT : T.Opens}
  {UX : X.Opens} (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US)
  {UY : Y.Opens} (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)

include H hUY in
/-- vuys5SNs2eQ-1625 (0:27:05) [prop] For a cartesian square there is a canonical base change
morphism `g^* f_* F → f'_* F'`. For `F = 𝒪_X` on affine opens: mathlib's `pushoutSection`,
`Γ(X, U_X) ⊗_{Γ(S, U_S)} Γ(T, U_T) → Γ(X ×_S T, U_Y)`. -/
theorem prop_1625 :
    Nonempty (pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ⟶ Γ(Y, UY)) :=
  ⟨pushoutSection H hUST hUSX hUY⟩

/-- vuys5SNs2eQ-1827 (0:30:27) [prop] `f` qcqs, `g` flat: `g^* f_* F ≅ f'_* g'^* F`. Case
`F = 𝒪_X`, `i = 0`, over affine opens of the base (mathlib:
`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`). -/
theorem prop_1827 [Flat f] (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
    (hUX : IsCompact (X := X) UX) (hUX' : IsQuasiSeparated (α := X) UX) :
    IsIso (pushoutSection H hUST hUSX hUY) :=
  isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hUST hUSX hUY hUS hUT hUX hUX'

/-- vuys5SNs2eQ-2356 (0:39:16) [prop] The base change morphism is an isomorphism with no flatness
hypothesis if `f` is affine. Case `F = 𝒪_X` over affine opens (mathlib:
`isIso_pushoutSection_of_isAffineOpen`). -/
theorem prop_2356 (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsAffineOpen UX) :
    IsIso (pushoutSection H hUST hUSX hUY) :=
  isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hUS hUT hUX

end Sections

/-- vuys5SNs2eQ-2099 (0:34:59) [prop] A flat local homomorphism of local rings is faithfully flat,
and the map of spectra is surjective (as `prop_37918`). -/
theorem prop_2099 [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Module.Flat A B] :
    Module.FaithfullyFlat A B ∧ Function.Surjective (comap (algebraMap A B)) :=
  ⟨(prop_37918.1).1 inferInstance, prop_37918.2 inferInstance⟩

/-- vuys5SNs2eQ-2164 (0:36:04) [prop] A flat morphism is generalizing, hence universally
generalizing (as `prop_38767`). -/
theorem prop_2164 {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    GeneralizingMap f ∧ ∀ (Y' : Scheme.{u}) (g : Y' ⟶ Y), GeneralizingMap (pullback.snd f g) :=
  ⟨(prop_38767 f).1, (prop_38767 f).2.1⟩

/-- vuys5SNs2eQ-2620 (0:43:40) [def] `f` is radicial if it is universally injective (mathlib:
`AlgebraicGeometry.UniversallyInjective`, `universallyInjective_eq`). -/
theorem def_2620 :
    @UniversallyInjective = MorphismProperty.universally (topologically Function.Injective) :=
  universallyInjective_eq

/-- Surjectivity descends along surjective morphisms. -/
theorem surjective_descendsAlong :
    MorphismProperty.DescendsAlong @Surjective.{u} (@Surjective : MorphismProperty Scheme.{u}) := by
  apply MorphismProperty.DescendsAlong.mk'
  intro X Y Z f g _ hf hfst
  refine ⟨fun z => ?_⟩
  obtain ⟨x, rfl⟩ := hf.surj z
  obtain ⟨p, rfl⟩ := hfst.surj x
  exact ⟨pullback.snd f g p, by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩

instance quasiCompact_respectsIso : MorphismProperty.RespectsIso @QuasiCompact.{u} :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ f (_ : IsIso f) => inferInstance)

/-- Quasi-compactness descends along surjective quasi-compact morphisms. -/
theorem quasiCompact_descendsAlong :
    MorphismProperty.DescendsAlong @QuasiCompact.{u}
      (@Surjective ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  apply MorphismProperty.DescendsAlong.mk'
  intro X Y Z f g _ hf hfst
  obtain ⟨hf1, hf2⟩ := hf
  refine ⟨fun U hU hc => ?_⟩
  have hsnd : Function.Surjective (pullback.snd f g) := (inferInstance : Surjective _).surj
  have e : g ⁻¹' U = pullback.snd f g '' (pullback.fst f g ⁻¹' (f ⁻¹' U)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hy
      obtain ⟨p, rfl⟩ := hsnd y
      refine ⟨p, ?_, rfl⟩
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      exact hy
    · rintro ⟨p, hp, rfl⟩
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
      exact hp
  rw [e]
  exact (hfst.isCompact_preimage _ (hU.preimage f.continuous)
    (hf2.isCompact_preimage U hU hc)).image (pullback.snd f g).continuous

attribute [local instance] surjective_descendsAlong quasiCompact_descendsAlong

/-- vuys5SNs2eQ-2620 (0:43:40) [prop] If `g : S' → S` is surjective, `f` is surjective (resp.
radicial) if and only if `f'` is (radicial = diagonal surjective, and diagonal properties descend:
mathlib's `MorphismProperty.DescendsAlong` instance for `diagonal`). -/
theorem prop_2620 {S S' X : Scheme.{u}} (g : S' ⟶ S) [Surjective g] (f : X ⟶ S) :
    (Surjective (pullback.snd f g) ↔ Surjective f) ∧
      (UniversallyInjective (pullback.snd f g) ↔ UniversallyInjective f) := by
  refine ⟨MorphismProperty.pullback_snd_iff (P := @Surjective) (Q := @Surjective)
    (inferInstance : Surjective g), ?_⟩
  have : (MorphismProperty.diagonal @Surjective.{u}).IsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.diagonal
  have : (MorphismProperty.diagonal @Surjective.{u}).DescendsAlong @Surjective.{u} :=
    MorphismProperty.instDescendsAlongDiagonalOfRespectsIsoOfIsStableUnderBaseChange _ _
  rw [universallyInjective_eq_diagonal]
  exact MorphismProperty.pullback_snd_iff (Q := @Surjective) (inferInstance : Surjective g)

/-- vuys5SNs2eQ-2686 (0:44:46) [prop] A morphism is radicial iff its diagonal is surjective
(mathlib: `UniversallyInjective.iff_diagonal`). -/
theorem prop_2686 {X Y : Scheme.{u}} (f : X ⟶ Y) :
    UniversallyInjective f ↔ Surjective (pullback.diagonal f) :=
  UniversallyInjective.iff_diagonal f

/-- vuys5SNs2eQ-2750 (0:45:50) [prop] If `g` is surjective and quasi-compact, `f` is quasi-compact
(resp. quasi-separated, coherent) if and only if `f'` is. -/
theorem prop_2750 {S S' X : Scheme.{u}} (g : S' ⟶ S) [Surjective g] [QuasiCompact g]
    (f : X ⟶ S) :
    (QuasiCompact (pullback.snd f g) ↔ QuasiCompact f) ∧
      (QuasiSeparated (pullback.snd f g) ↔ QuasiSeparated f) ∧
      ((QuasiCompact (pullback.snd f g) ∧ QuasiSeparated (pullback.snd f g)) ↔
        (QuasiCompact f ∧ QuasiSeparated f)) := by
  have hg : (@Surjective ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) g :=
    ⟨inferInstance, inferInstance⟩
  have h1 := MorphismProperty.pullback_snd_iff (P := @QuasiCompact) (f := f) hg
  have h2 : QuasiSeparated (pullback.snd f g) ↔ QuasiSeparated f := by
    have : (MorphismProperty.diagonal @QuasiCompact.{u}).IsStableUnderBaseChange :=
      MorphismProperty.IsStableUnderBaseChange.diagonal
    have : (@Surjective ⊓ @QuasiCompact : MorphismProperty Scheme.{u}).IsStableUnderBaseChange :=
      MorphismProperty.IsStableUnderBaseChange.inf
    have : (MorphismProperty.diagonal @QuasiCompact.{u}).DescendsAlong
        (@Surjective ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
      MorphismProperty.instDescendsAlongDiagonalOfRespectsIsoOfIsStableUnderBaseChange _ _
    rw [quasiSeparated_eq_diagonal_is_quasiCompact]
    exact MorphismProperty.pullback_snd_iff hg
  exact ⟨h1, h2, and_congr h1 h2⟩

end BaseChange

end

end Buffalo.AG.Part08
