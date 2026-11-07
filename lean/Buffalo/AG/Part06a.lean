import Mathlib

/-!
# Buffalo, algebraic geometry, part 06 (a): 25 June 1973, open and closed immersions

The entries of `docs/buffalo-ag/index.tex` lines 770–800 (video `Oqhr-Gt66es`, 0:58:06–1:34:42):
open immersions, closed immersions, closed subschemes and quasi-coherent ideals, immersions.

Conventions. Schemes and their morphisms are mathlib's (`AlgebraicGeometry.Scheme`); the classes
of morphisms are mathlib's `IsOpenImmersion`, `IsClosedImmersion`, `IsImmersion`, and their
stability is stated with `MorphismProperty`. Statements about closed subschemes of an affine
scheme `Spec A` are made on the rings (`A → A/J`).
-/

open CategoryTheory Limits AlgebraicGeometry Topology TensorProduct

universe u

namespace Buffalo.AG.Part06

noncomputable section

/-! ### Open immersions -/

section OpenImmersions

variable {X Y Z : Scheme.{u}}

/-- Oqhr-Gt66es-3486 (0:58:06) [def] An open immersion is a homeomorphism onto an open set of `Y`,
the structure sheaf of `X` being induced by that of `Y` (mathlib: `IsOpenImmersion`; with
`IsOpenImmersion.iff_isIso_stalkMap`: an open embedding inducing isomorphisms of local rings). -/
example (f : X ⟶ Y) : IsOpenImmersion f ↔ IsOpenEmbedding f ∧ ∀ x, IsIso (f.stalkMap x) :=
  IsOpenImmersion.iff_isIso_stalkMap

/-- Oqhr-Gt66es-3549 (0:59:09) [prop] The subobjects of `Y` defined by open immersions correspond
to the open sets of `Y` (every open `U` gives `U.ι` with image `U`, and two open immersions with
the same image are isomorphic over `Y`); open immersions are stable under composition and base
change. -/
theorem prop_3549 :
    (∀ U : Y.Opens, Set.range U.ι = U) ∧
    (∀ (f : X ⟶ Y) (g : Z ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
      (h : Set.range f = Set.range g), (IsOpenImmersion.isoOfRangeEq f g h).hom ≫ g = f) ∧
    MorphismProperty.IsStableUnderComposition (@IsOpenImmersion : MorphismProperty Scheme.{u}) ∧
    MorphismProperty.IsStableUnderBaseChange (@IsOpenImmersion : MorphismProperty Scheme.{u}) :=
  ⟨fun U => U.range_ι, fun f g _ _ h => IsOpenImmersion.isoOfRangeEq_hom_fac f g h,
    inferInstance, inferInstance⟩

end OpenImmersions

/-! ### Closed immersions -/

section ClosedImmersions

variable {X Y Z : Scheme.{u}}

/-- Oqhr-Gt66es-3678 (1:01:18) [def] `f` is a closed immersion if, for a covering of `Y` by affine
open sets `Y_i = Spec A_i`, `f⁻¹(Y_i) = Spec B_i` is affine and `A_i → B_i` is surjective
(mathlib: `IsClosedImmersion`, whose affine-local description is
`isClosedImmersion_iff_isAffineHom`: affine, and surjective on sections over affine opens). -/
example (f : X ⟶ Y) : IsClosedImmersion f ↔
    IsAffineHom f ∧ ∀ U : Y.Opens, IsAffineOpen U → Function.Surjective (f.app U) :=
  isClosedImmersion_iff_isAffineHom

/-- Oqhr-Gt66es-3740 (1:02:20) [prop] Intrinsic characterization: `f` is a closed immersion iff it
is a homeomorphism onto a closed set and `𝒪_Y → f_*𝒪_X` is surjective (mathlib's definition of
`IsClosedImmersion`; surjectivity of the map of sheaves is surjectivity on stalks). -/
theorem prop_3740 (f : X ⟶ Y) :
    IsClosedImmersion f ↔ IsClosedEmbedding f ∧ ∀ x, Function.Surjective (f.stalkMap x) :=
  ⟨fun h => ⟨h.isClosedEmbedding, h.stalkMap_surjective⟩,
    fun ⟨h₁, h₂⟩ => { stalkMap_surjective := h₂, isClosedEmbedding := h₁ }⟩

/-- Oqhr-Gt66es-3941 (1:05:41) [prop] A closed immersion is a monomorphism. -/
theorem prop_3941 (f : X ⟶ Y) [IsClosedImmersion f] : Mono f := inferInstance

/-- Oqhr-Gt66es-4070 (1:07:50) [prop] The closed subschemes of `Y` correspond to the
quasi-coherent ideals `J ⊂ 𝒪_Y` (mathlib: `IsClosedImmersion.overEquivIdealSheafData`, an
(anti-)equivalence between closed immersions into `Y` and ideal sheaves of `Y`). -/
def prop_4070 (Y : Scheme.{u}) := IsClosedImmersion.overEquivIdealSheafData Y

/-- Oqhr-Gt66es-4200 (1:10:00) [prop] Closed immersions are stable under base change:
`V(J) ×_Y Y' = V(J𝒪_{Y'})`, since `A' ⊗_A A/J ≃ A'/JA'`
(`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`). -/
theorem prop_4200 :
    MorphismProperty.IsStableUnderBaseChange (@IsClosedImmersion : MorphismProperty Scheme.{u}) ∧
    ∀ (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A'] (J : Ideal A),
      Nonempty ((A' ⧸ J.map (algebraMap A A')) ≃ₐ[A'] A' ⊗[A] (A ⧸ J)) :=
  ⟨inferInstance, fun _ A' _ _ _ J => ⟨Algebra.TensorProduct.quotIdealMapEquivTensorQuot A' J⟩⟩

/-- Oqhr-Gt66es-4265 (1:11:05) [prop] For `X = V(J)`, the ideals of `𝒪_X` correspond to the ideals
`K ⊃ J` via `K ↦ K/J`, and `V(K/J) = V(K)`. Affine case: ideals of `A/J` are the ideals of `A`
containing `J`, and `(A/J)/(K/J) ≃ A/K`. -/
theorem prop_4265 {A : Type u} [CommRing A] (J : Ideal A) :
    Nonempty (Ideal (A ⧸ J) ≃o {K : Ideal A // J ≤ K}) ∧
    ∀ K : Ideal A, J ≤ K → Nonempty ((A ⧸ J) ⧸ K.map (Ideal.Quotient.mk J) ≃+* A ⧸ K) := by
  refine ⟨⟨(Ideal.relIsoOfSurjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).trans
    (Set.orderIsoOfEq _ _ ?_)⟩, fun K hK => ⟨DoubleQuot.quotQuotEquivQuotOfLE hK⟩⟩
  ext K
  change Ideal.comap _ ⊥ ≤ K ↔ J ≤ K
  rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

/-- Oqhr-Gt66es-4328 (1:12:08) [prop] Closed immersions are stable under composition. -/
theorem prop_4328 : MorphismProperty.IsStableUnderComposition
    (@IsClosedImmersion : MorphismProperty Scheme.{u}) :=
  ⟨fun f g hf hg => by have := hf; have := hg; exact IsClosedImmersion.comp f g⟩

/-- Oqhr-Gt66es-4647 (1:17:27) [prop] For `f` quasi-compact, the kernel of `𝒪_Y → f_*𝒪_X` is a
quasi-coherent ideal: mathlib's `Scheme.Hom.ker` (an ideal sheaf, i.e. a quasi-coherent ideal
given on affine opens) is, on every affine open `U`, the kernel of `Γ(Y, U) → Γ(X, f⁻¹U)`. -/
theorem prop_4647 (f : X ⟶ Y) [QuasiCompact f] (U : Y.affineOpens) :
    f.ker.ideal U = RingHom.ker (f.app U).hom :=
  f.ker_apply U

/-- Oqhr-Gt66es-4903 (1:21:43) [prop] For `Y = Spec A` and `J` an ideal of `A`,
`V(J) = Spec A/J` (a closed immersion onto the zero locus of `J`); `J ↦ V(J)` reverses order. -/
theorem prop_4903 {A : Type u} [CommRing A] (J : Ideal A) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ∧
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) = PrimeSpectrum.zeroLocus J ∧
    ∀ J' : Ideal A, J ≤ J' → PrimeSpectrum.zeroLocus (J' : Set A) ⊆ PrimeSpectrum.zeroLocus J :=
  ⟨IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective,
    by rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker],
    fun _ h => PrimeSpectrum.zeroLocus_anti_mono h⟩

/-- Oqhr-Gt66es-4968 (1:22:48) [prop] Open subschemes are ordered like the open sets (`V ≤ U` iff
`V.ι` factors through `U.ι`); closed subschemes are ordered like the ideals, reversed. Affine
case for the latter: `A → A/K` factors through `A → A/J` iff `J ≤ K`. -/
theorem prop_4968 {A : Type u} [CommRing A] (J K : Ideal A) :
    (∃ φ : A ⧸ J →+* A ⧸ K, φ.comp (Ideal.Quotient.mk J) = Ideal.Quotient.mk K) ↔ J ≤ K := by
  constructor
  · rintro ⟨φ, hφ⟩ x hx
    have := congrArg (fun g : A →+* A ⧸ K => g x) hφ
    simp only [RingHom.coe_comp, Function.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx,
      map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm
  · intro h
    exact ⟨Ideal.Quotient.factor h, rfl⟩

/-- The same for open subschemes: `V ≤ U` iff the inclusion of `V` factors through `U`. -/
theorem prop_4968_open (U V : Y.Opens) :
    (∃ g : V.toScheme ⟶ U.toScheme, g ≫ U.ι = V.ι) ↔ V ≤ U := by
  constructor
  · rintro ⟨g, hg⟩ y hy
    have : V.ι ⟨y, hy⟩ ∈ Set.range U.ι := by rw [← hg]; exact ⟨g ⟨y, hy⟩, rfl⟩
    rw [U.range_ι] at this
    simpa using this
  · intro h
    exact ⟨Y.homOfLE h, Y.homOfLE_ι h⟩

/-- Oqhr-Gt66es-5038 (1:23:58) [prop] The intersection of `V(J₁)` and `V(J₂)` is `V(J₁ + J₂)`:
`A/J₁ ⊗_A A/J₂ ≃ A/(J₁ + J₂)`. -/
def prop_5038 {A : Type u} [CommRing A] (J₁ J₂ : Ideal A) :
    (A ⧸ J₂) ⊗[A] (A ⧸ J₁) ≃+* A ⧸ (J₁ ⊔ J₂) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A ⧸ J₂) J₁).toRingEquiv.symm.trans <|
    (Ideal.quotEquivOfEq (by rw [Ideal.Quotient.algebraMap_eq])).trans <|
      (DoubleQuot.quotQuotEquivQuotSup J₂ J₁).trans (Ideal.quotEquivOfEq (sup_comm J₂ J₁))

end ClosedImmersions

/-! ### Immersions -/

section Immersions

variable {X Y Z : Scheme.{u}}

/-- Oqhr-Gt66es-5165 (1:26:05) [def] An immersion factors as a closed immersion followed by an
open immersion (mathlib: `IsImmersion`, `IsImmersion.isImmersion_iff_exists`). -/
example (f : X ⟶ Y) : IsImmersion f ↔ ∃ (Z : Scheme) (g₁ : X ⟶ Z) (g₂ : Z ⟶ Y),
    IsClosedImmersion g₁ ∧ IsOpenImmersion g₂ ∧ g₁ ≫ g₂ = f :=
  IsImmersion.isImmersion_iff_exists

/-- Every open set in which a subset `s` is closed is contained in `(s̄ ∖ s)ᶜ`. -/
theorem subset_coborder_of_isClosed {T : Type*} [TopologicalSpace T] {s U : Set T}
    (_hU : IsOpen U) (_hsU : s ⊆ U) (hcl : closure s ∩ U ⊆ s) : U ⊆ coborder s := by
  intro y hy hy'
  exact hy'.2 (hcl ⟨hy'.1, hy⟩)

/-- Oqhr-Gt66es-5297 (1:28:17) [prop] An immersion is a homeomorphism onto a locally closed subset
`X` of `Y`; the largest open set in which `X` is closed is `Y ∖ (X̄ ∖ X)` (mathlib: `coborder`):
the image is closed in its coborder, and every open set in which it is closed lies in it. -/
theorem prop_5297 (f : X ⟶ Y) [IsImmersion f] :
    IsEmbedding f ∧ IsLocallyClosed (Set.range f) ∧
    IsOpen (coborder (Set.range f)) ∧ Set.range f ⊆ coborder (Set.range f) ∧
    closure (Set.range f) ∩ coborder (Set.range f) ⊆ Set.range f ∧
    ∀ U : Set Y, IsOpen U → Set.range f ⊆ U → closure (Set.range f) ∩ U ⊆ Set.range f →
      U ⊆ coborder (Set.range f) := by
  have hlc := f.isLocallyClosed_range
  refine ⟨f.isEmbedding, hlc, isLocallyClosed_iff_isOpen_coborder.1 hlc, subset_coborder,
    fun y hy => ?_, fun U hU h1 h2 => subset_coborder_of_isClosed hU h1 h2⟩
  by_contra h
  exact hy.2 ⟨hy.1, h⟩

/-- Oqhr-Gt66es-5361 (1:29:21) [prop] Intrinsic characterization: `f` is an immersion iff it is a
homeomorphism onto a locally closed subset and `f⁻¹𝒪_Y → 𝒪_X` is surjective (on stalks; mathlib's
definition of `IsImmersion` over `IsPreimmersion`). -/
theorem prop_5361 (f : X ⟶ Y) :
    IsImmersion f ↔ IsEmbedding f ∧ IsLocallyClosed (Set.range f) ∧
      ∀ x, Function.Surjective (f.stalkMap x) :=
  ⟨fun h => ⟨h.isEmbedding, h.isLocallyClosed_range, h.stalkMap_surjective⟩,
    fun ⟨h₁, h₂, h₃⟩ => { stalkMap_surjective := h₃, isEmbedding := h₁, isLocallyClosed_range := h₂ }⟩

/-- Oqhr-Gt66es-5426 (1:30:26) [prop] Equivalently, `f(X)` has an open neighbourhood `V` such that
`f⁻¹(V) → V` is a closed immersion (here `V` is the coborder, `f⁻¹(V) = X`); conversely such a
factorisation makes `f` an immersion. -/
theorem prop_5426 (f : X ⟶ Y) :
    IsImmersion f ↔ ∃ (V : Y.Opens) (g : X ⟶ V.toScheme), IsClosedImmersion g ∧ g ≫ V.ι = f := by
  constructor
  · intro _
    exact ⟨f.coborderRange, f.liftCoborder, inferInstance, f.liftCoborder_ι⟩
  · rintro ⟨V, g, hg, rfl⟩
    infer_instance

/-- Oqhr-Gt66es-5617 (1:33:37) [prop] Immersions are stable under base change and composition. -/
theorem prop_5617 :
    MorphismProperty.IsStableUnderBaseChange (@IsImmersion : MorphismProperty Scheme.{u}) ∧
    MorphismProperty.IsStableUnderComposition (@IsImmersion : MorphismProperty Scheme.{u}) :=
  ⟨inferInstance, ⟨fun f g hf hg => by have := hf; have := hg; infer_instance⟩⟩

/-- Oqhr-Gt66es-5682 (1:34:42) [prop] Every diagonal morphism is an immersion; every section of an
`S`-scheme is an immersion; the kernel of two morphisms `u, v : X → Y` of `S`-schemes (the base
change of the diagonal along `(u, v)`) is an immersion. -/
theorem prop_5682 {S : Scheme.{u}} (g : Y ⟶ S) :
    IsImmersion (pullback.diagonal g) ∧
    (∀ s : S ⟶ Y, s ≫ g = 𝟙 S → IsImmersion s) ∧
    ∀ (u v : X ⟶ Y) (h : u ≫ g = v ≫ g),
      IsImmersion (pullback.fst (pullback.lift u v h) (pullback.diagonal g)) := by
  refine ⟨inferInstance, fun s hs => ?_, fun u v h => inferInstance⟩
  have : IsImmersion (s ≫ g) := by rw [hs]; infer_instance
  exact IsImmersion.of_comp s g

end Immersions

end

end Buffalo.AG.Part06
