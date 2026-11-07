import Buffalo.AG.Part04a

/-!
# Buffalo, algebraic geometry, part 04 (b): 13 June 1973, locally ringed spaces and schemes

The entries of `docs/buffalo-ag/index.tex` lines 519–548 (video `thSz9ZHDK9o`, 2:26:42–3:57:31):
the open sets `U_f` of a ringed space, morphisms of spectra, local homomorphisms and morphisms of
locally ringed spaces, the counterexample of a discrete valuation ring, the full faithfulness of
`Spec`, schemes and their functor of points.
-/

open CategoryTheory Limits Opposite IsLocalRing TopologicalSpace AlgebraicGeometry

universe u

namespace Buffalo.AG.Part04

noncomputable section

/-! ### Locally ringed spaces and morphisms of spectra -/

/-- thSz9ZHDK9o-8874 (2:27:54) [def] For `f ∈ 𝒪_X(U)`, `U_f` is the set of `x ∈ U` where `f_x`
is invertible (mathlib's `RingedSpace.basicOpen`); in a locally ringed space this is the set
where the value `f(x) ∈ κ(x)` is nonzero. -/
theorem def_8874 (X : LocallyRingedSpace.{u}) {U : Opens X} (f : X.presheaf.obj (op U)) (x : X)
    (hx : x ∈ U) :
    (x ∈ X.toRingedSpace.basicOpen f ↔ IsUnit (X.presheaf.germ U x hx f)) ∧
      (x ∈ X.toRingedSpace.basicOpen f ↔
        IsLocalRing.residue (X.presheaf.stalk x) (X.presheaf.germ U x hx f) ≠ 0) :=
  ⟨X.toRingedSpace.mem_basicOpen f x hx,
    (X.toRingedSpace.mem_basicOpen f x hx).trans (IsLocalRing.residue_ne_zero_iff_isUnit _).symm⟩

/-- thSz9ZHDK9o-9004 (2:30:04) [prop] A ringed space with nonzero fibres is locally ringed iff,
for `f₁, …, fₙ ∈ 𝒪_X(U)` with `∑ fᵢ = 1`, the `U_{fᵢ}` cover `U`. -/
theorem prop_9004 (X : RingedSpace.{u}) (hX : ∀ x : X, Nontrivial (X.presheaf.stalk x)) :
    (∀ x : X, IsLocalRing (X.presheaf.stalk x)) ↔
      ∀ (U : Opens X) (n : ℕ) (f : Fin n → X.presheaf.obj (op U)), ∑ i, f i = 1 →
        ⨆ i, X.basicOpen (f i) = U := by
  constructor
  · intro hloc U n f hf
    apply le_antisymm (iSup_le fun i => X.basicOpen_le (f i))
    intro x hx
    have hu : IsUnit (∑ i, X.presheaf.germ U x hx (f i)) := by
      rw [← map_sum, hf, map_one]; exact isUnit_one
    obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum hu
    exact Opens.mem_iSup.2 ⟨i, (X.mem_basicOpen (f i) x hx).2 hi⟩
  · intro H x
    have := hX x
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
    obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
    have h := H U 2 ![s, 1 - s] (by simp)
    have hx : x ∈ ⨆ i, X.basicOpen (![s, 1 - s] i) := by rw [h]; exact hxU
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
    rw [X.mem_basicOpen _ x hxU] at hi
    fin_cases i
    · exact Or.inl hi
    · right; simpa using hi

/-- thSz9ZHDK9o-9067 (2:31:07) [prop] For `u : A → B`, `𝔭 ↦ u⁻¹(𝔭)` is continuous. -/
theorem prop_9067 {A B : Type u} [CommRing A] [CommRing B] (u : A →+* B) :
    Continuous (fun p : PrimeSpectrum B => PrimeSpectrum.comap u p) :=
  PrimeSpectrum.continuous_comap u

/-- thSz9ZHDK9o-9194 (2:33:14) [prop] `φ⁻¹(Y_f) = X_{u(f)}`, and `u` defines a morphism of
(locally) ringed spaces `Spec B → Spec A` (`Spec.map`). -/
theorem prop_9194 {A B : CommRingCat.{u}} (u : A ⟶ B) (f : A) :
    Spec.map u ⁻¹ᵁ PrimeSpectrum.basicOpen f = PrimeSpectrum.basicOpen (u f) :=
  SpecMap_preimage_basicOpen u f

/-- thSz9ZHDK9o-9257 (2:34:17) [prop] For an `A`-algebra `B` and `f ∈ A`, the localization of the
ring `B` at the image of `f` is the localization of the `A`-module `B` at `f`. -/
theorem prop_9257 {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (f : A) :
    IsLocalizedModule (Submonoid.powers f)
      (IsScalarTower.toAlgHom A B (Localization.Away (algebraMap A B f))).toLinearMap := by
  rw [isLocalizedModule_iff_isLocalization, Algebra.algebraMapSubmonoid,
    Submonoid.map_powers]
  infer_instance

/-- thSz9ZHDK9o-9386 (2:36:26) [prop] `u` is recovered as `Γ(φ^♯)` (up to `Γ(Spec A) ≅ A`), and
`Hom(A, B) → Hom(Spec B, Spec A)` is injective. -/
theorem prop_9386 {A B : CommRingCat.{u}} (u : A ⟶ B) :
    (Spec.map u).appTop ≫ (Scheme.ΓSpecIso B).hom = (Scheme.ΓSpecIso A).hom ≫ u ∧
      Function.Injective (Spec.map : (A ⟶ B) → (Spec B ⟶ Spec A)) :=
  ⟨Scheme.ΓSpecIso_naturality u, Spec.map_injective⟩

/-- thSz9ZHDK9o-9833 (2:43:53) [prop] `Hom_{𝒪_Y}(M^~, G) ≃ Hom_A(M, Γ(Y, G))` (the adjunction
`tilde ⊣ Γ`, applied to `G = φ_* N^~`, whose global sections are `N_{[A]}`) and
`Hom_A(M, N_{[A]}) ≃ Hom_B(M ⊗_A B, N)` (extension ⊣ restriction of scalars). -/
def prop_9833 {A B : CommRingCat.{u}} (u : A ⟶ B) (M : ModuleCat.{u} A)
    (G : (Spec A).Modules) (N : ModuleCat.{u} B) :
    (((tilde.functor A).obj M ⟶ G) ≃ (M ⟶ moduleSpecΓFunctor.obj G)) ×
      (((ModuleCat.extendScalars u.hom).obj M ⟶ N) ≃
        (M ⟶ (ModuleCat.restrictScalars u.hom).obj N)) :=
  ((tilde.adjunction (R := A)).homEquiv M G,
    (ModuleCat.extendRestrictScalarsAdj u.hom).homEquiv M N)

/-- thSz9ZHDK9o-9513 (2:38:33) [prop] The direct image of a quasi-coherent module `N^~` on
`Spec B` is again of the form `M^~` (with `M` its module of global sections, `N_{[A]}`): the
canonical map `Γ(φ_* N^~)^~ → φ_* N^~` is an isomorphism. -/
theorem prop_9513 {A B : CommRingCat.{u}} (u : A ⟶ B) (N : (Spec B).Modules)
    [IsIso N.fromTildeΓ] :
    IsIso ((Scheme.Modules.pushforward (Spec.map u)).obj N).fromTildeΓ :=
  isIso_fromTildeΓ_pushforward u N

/-- thSz9ZHDK9o-10229 (2:50:29) [def] `u : O → O'` between local rings is local
(`IsLocalHom u`) iff `u⁻¹(𝔪') = 𝔪`; a morphism of ringed spaces induces the maps of stalks
`Hom.stalkMap`. -/
theorem def_10229 {O O' : Type u} [CommRing O] [CommRing O'] [IsLocalRing O] [IsLocalRing O']
    (u : O →+* O') : IsLocalHom u ↔ (maximalIdeal O').comap u = maximalIdeal O :=
  (IsLocalRing.local_hom_TFAE u).out 1 5

/-- thSz9ZHDK9o-10435 (2:53:55) [prop] For `u : O → O'` between local rings, `u⁻¹(𝔪') ⊂ 𝔪`
always; `u` is local iff `u(𝔪) ⊂ 𝔪'`, iff (`f ∈ O^* ⇔ u(f) ∈ O'^*`). -/
theorem prop_10435 {O O' : Type u} [CommRing O] [CommRing O'] [IsLocalRing O] [IsLocalRing O']
    (u : O →+* O') :
    (maximalIdeal O').comap u ≤ maximalIdeal O ∧
      (IsLocalHom u ↔ u '' maximalIdeal O ⊆ maximalIdeal O') ∧
      (IsLocalHom u ↔ ∀ f, IsUnit f ↔ IsUnit (u f)) := by
  refine ⟨IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top u (IsLocalRing.maximalIdeal.isMaximal
    O').ne_top), (IsLocalRing.local_hom_TFAE u).out 1 2, ⟨fun h f => ?_, fun h => ⟨fun f hf =>
    (h f).2 hf⟩⟩⟩
  exact ⟨fun hf => hf.map u, fun hf => isUnit_of_map_unit u f hf⟩

/-- thSz9ZHDK9o-10502 (2:55:02) [def] A morphism of locally ringed spaces is a morphism of ringed
spaces whose maps on stalks are local (mathlib's `LocallyRingedSpace.Hom`). -/
example {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    IsLocalHom (f.stalkMap x).hom := inferInstance

/-- thSz9ZHDK9o-10708 (2:58:28) [prop] For a morphism of ringed spaces `φ : X → Y` between
locally ringed spaces, `φ⁻¹(Y_f) ⊂ X_{φ^*(f)}`; `φ` is local iff this is always an equality. -/
theorem prop_10708 {X Y : LocallyRingedSpace.{u}} (φ : X.toPresheafedSpace ⟶ Y.toPresheafedSpace) :
    (∀ (U : Opens Y) (f : Y.presheaf.obj (op U)),
      (Opens.map φ.base).obj (Y.toRingedSpace.basicOpen f) ≤
        X.toRingedSpace.basicOpen (φ.c.app (op U) f)) ∧
    ((∀ x, IsLocalHom (φ.stalkMap x).hom) ↔
      ∀ (U : Opens Y) (f : Y.presheaf.obj (op U)),
        (Opens.map φ.base).obj (Y.toRingedSpace.basicOpen f) =
          X.toRingedSpace.basicOpen (φ.c.app (op U) f)) := by
  have key : ∀ (U : Opens Y) (f : Y.presheaf.obj (op U)) (x : X) (hx : φ.base x ∈ U),
      φ.stalkMap x (Y.presheaf.germ U (φ.base x) hx f) =
        X.presheaf.germ ((Opens.map φ.base).obj U) x hx (φ.c.app (op U) f) :=
    fun U f x hx => PresheafedSpace.stalkMap_germ_apply φ U x hx f
  have incl : ∀ (U : Opens Y) (f : Y.presheaf.obj (op U)),
      (Opens.map φ.base).obj (Y.toRingedSpace.basicOpen f) ≤
        X.toRingedSpace.basicOpen (φ.c.app (op U) f) := by
    intro U f x hx
    obtain ⟨hxU, hu⟩ := hx
    refine (X.toRingedSpace.mem_basicOpen _ x hxU).2 ?_
    rw [← key]
    exact hu.map _
  refine ⟨incl, ⟨fun hloc U f => le_antisymm (incl U f) fun x hx => ?_, fun H x => ⟨fun a ha => ?_⟩⟩⟩
  · obtain ⟨hxU, hu⟩ := hx
    refine ⟨hxU, ?_⟩
    have hxU' : φ.base x ∈ U := hxU
    have h2 : IsUnit (φ.stalkMap x (Y.presheaf.germ U _ hxU' f)) := by
      rw [key U f x hxU']; exact hu
    exact isUnit_of_map_unit _ _ h2
  · obtain ⟨U, hxU, s, rfl⟩ := Y.presheaf.exists_germ_eq a
    have hxs : x ∈ X.toRingedSpace.basicOpen (φ.c.app (op U) s) :=
      (X.toRingedSpace.mem_basicOpen _ x hxU).2 (by rw [← key]; exact ha)
    rw [← H U s] at hxs
    exact (Y.toRingedSpace.mem_basicOpen s _ hxU).1 hxs

end

end Buffalo.AG.Part04

namespace Buffalo.AG.Part04

noncomputable section

/-! ### The counterexample of a discrete valuation ring -/

/-- thSz9ZHDK9o-12148 (3:22:28) [cex] For `V` a discrete valuation ring with fraction field `K`,
the morphism of ringed spaces `Spec K → Spec V` sending the point to the closed point with
`V ⊂ K` on sections is not local: its map on stalks at the closed point is `V → K`, which is not
a local homomorphism; and it does not come from a ring homomorphism, since `Γ` would force
`u = (V ⊂ K)`, and `Spec` of the inclusion sends the point to the generic point `(0) ≠ 𝔪`.
(The ringed-space morphism itself is not constructed.) -/
theorem cex_12148 (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] :
    ¬ IsLocalHom (algebraMap V K) ∧
      ∀ p : PrimeSpectrum K, (PrimeSpectrum.comap (algebraMap V K) p).asIdeal = ⊥ ∧
        (⊥ : Ideal V) ≠ maximalIdeal V := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hne : ϖ ≠ 0 := hϖ.ne_zero
  refine ⟨fun h => hϖ.not_isUnit ?_, fun p => ⟨?_, ?_⟩⟩
  · apply isUnit_of_map_unit (algebraMap V K)
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hne)).isUnit
  · have hp : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime p.asIdeal
    rw [PrimeSpectrum.comap_asIdeal, hp, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V K)]
  · intro h
    exact hϖ.not_isUnit (by
      by_contra hu
      have : ϖ ∈ maximalIdeal V := hu
      rw [← h] at this
      exact hne this)

/-! ### `Spec` is fully faithful on locally ringed spaces -/

/-- thSz9ZHDK9o-12408 (3:26:48) [prop] A morphism of locally ringed spaces (of schemes)
`φ : Spec B → Spec A` is `Spec u` for `u` the ring homomorphism it induces on global sections;
on points `φ(𝔭) = u⁻¹(𝔭)`. -/
theorem prop_12408 {A B : CommRingCat.{u}} (φ : Spec B ⟶ Spec A) :
    ∃ u : A ⟶ B, φ = Spec.map u ∧
      φ.appTop ≫ (Scheme.ΓSpecIso B).hom = (Scheme.ΓSpecIso A).hom ≫ u ∧
      ∀ p : PrimeSpectrum B, φ.base p = PrimeSpectrum.comap u.hom p := by
  refine ⟨Spec.preimage φ, (Spec.map_preimage φ).symm, ?_, fun p => ?_⟩
  · conv_lhs => rw [← Spec.map_preimage φ]
    exact Scheme.ΓSpecIso_naturality _
  · conv_lhs => rw [← Spec.map_preimage φ]
    rfl

/-- thSz9ZHDK9o-12471 (3:27:51) [prop] `Hom(A, B) → Hom_loc(Spec B, Spec A)` is bijective. -/
theorem prop_12471 (A B : CommRingCat.{u}) :
    Function.Bijective (Spec.map : (A ⟶ B) → (Spec B ⟶ Spec A)) :=
  ⟨Spec.map_injective, fun φ => ⟨Spec.preimage φ, Spec.map_preimage φ⟩⟩

/-- Morphisms of schemes are the morphisms of the underlying locally ringed spaces. -/
example (X Y : Scheme.{u}) : (X ⟶ Y) ≃ (X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace) :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.homEquiv

/-! ### Schemes and their functor of points -/

/-- thSz9ZHDK9o-12602 (3:30:02) [def] Affine schemes (locally ringed spaces isomorphic to a
spectrum) form a category anti-equivalent to rings (mathlib's `AffineScheme.equivCommRingCat`);
over `k`, to `k`-algebras, hence (`Buffalo.AG.Part01.prop_3423`) to affine algebraic spaces. -/
example : AffineScheme.{u} ≌ CommRingCat.{u}ᵒᵖ := AffineScheme.equivCommRingCat

/-- thSz9ZHDK9o-12665 (3:31:05) [prop] The global functions on the projective line, glued from
two affine lines along `k^×` (`ex_22963`), are the constants: inside `k[T, T⁻¹]`, a function
regular on both charts is a polynomial in `T` and in `T⁻¹`, hence constant. -/
theorem prop_12665 {R : Type u} [CommRing R] (f : LaurentPolynomial R) (p q : Polynomial R)
    (hp : f = p.toLaurent) (hq : f = LaurentPolynomial.invert q.toLaurent) :
    f = LaurentPolynomial.C (f.coeff 0) := by
  have key : ∀ (r : Polynomial R) (n : ℤ), n < 0 → r.toLaurent.coeff n = 0 := by
    intro r n hn
    by_contra h
    have : n ∈ r.toLaurent.coeff.support := Finsupp.mem_support_iff.2 h
    rw [LaurentPolynomial.support_coeff_toLaurent, Finset.mem_map] at this
    obtain ⟨k, -, rfl⟩ := this
    exact absurd hn (by simp)
  refine LaurentPolynomial.ext fun n => ?_
  rw [LaurentPolynomial.C_apply]
  split_ifs with h
  · rw [h]
  · rcases lt_or_gt_of_ne h with hn | hn
    · rw [hp]; exact key p n hn
    · rw [hq, LaurentPolynomial.invert_apply]; exact key q (-n) (by omega)

/-- thSz9ZHDK9o-12727 (3:32:07) [def] A scheme is a locally ringed space covered by open sets
isomorphic to spectra (mathlib's `Scheme`); its affine open sets form a basis. -/
example (X : Scheme.{u}) : Opens.IsBasis X.affineOpens := X.isBasis_affineOpens

/-- thSz9ZHDK9o-12791 (3:33:11) [prop] A `k`-scheme structure on `X`, a morphism `X → Spec k`,
amounts to a ring homomorphism `k → Γ(X, 𝒪_X)`. -/
def prop_12791 (X : Scheme.{u}) (k : CommRingCat.{u}) : (X ⟶ Spec k) ≃ (k ⟶ Γ(X, ⊤)) :=
  (ΓSpec.adjunction.homEquiv X (op k)).symm.trans (opEquiv _ _)

/-- thSz9ZHDK9o-14251 (3:57:31) [prop] For `X` a locally ringed space,
`Hom_loc(X, Spec A) ≃ Hom(A, Γ(X, 𝒪_X))`. -/
def prop_14251 (X : LocallyRingedSpace.{u}) (A : CommRingCat.{u}) :
    (X ⟶ Spec.toLocallyRingedSpace.obj (op A)) ≃ (A ⟶ LocallyRingedSpace.Γ.obj (op X)) :=
  (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op A)).symm.trans (opEquiv _ _)

/-- thSz9ZHDK9o-13111 (3:38:31) [def] `X(k') = Hom_k(Spec k', X)`; for `X = Spec A` one
recovers `Hom_{k-alg}(A, k')`. -/
def def_13111 (k A k' : Type u) [CommRing k] [CommRing A] [Algebra k A] [CommRing k']
    [Algebra k k'] :
    {f : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of A) //
      f ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
        Spec.map (CommRingCat.ofHom (algebraMap k k'))} ≃ (A →ₐ[k] k') where
  toFun f :=
    { (Spec.preimage f.1).hom with
      commutes' := fun c => by
        have h := f.2
        rw [← Spec.map_preimage f.1, ← Spec.map_comp, Spec.map_inj] at h
        exact congrArg (fun g => g.hom c) h }
  invFun φ := ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), by
    rw [← Spec.map_comp]; congr 1; ext c; exact φ.commutes c⟩
  left_inv f := Subtype.ext (by
    change Spec.map (CommRingCat.ofHom (Spec.preimage f.1).hom) = f.1
    exact Spec.map_preimage f.1)
  right_inv φ := by
    ext a
    change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))).hom a = φ a
    rw [Spec.preimage_map]; rfl

/-- The functor of points of schemes on rings: `X ↦ (R ↦ Hom(Spec R, X))`, the restriction of
`Hom(-, X)` to affine schemes. -/
abbrev pts : Scheme.{u} ⥤ (CommRingCat.{u} ⥤ Type u) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj Scheme.Spec.rightOp

/-- Two morphisms of schemes agreeing on all points with values in rings are equal. -/
theorem ext_of_affine {X Y : Scheme.{u}} (f g : X ⟶ Y)
    (h : ∀ (R : CommRingCat.{u}) (a : Spec R ⟶ X), a ≫ f = a ≫ g) : f = g :=
  Scheme.Cover.hom_ext X.affineCover f g fun _ => h _ _

/-- Naturality of a morphism of functors of points, for all morphisms of affine schemes. -/
theorem pts_nat {X Y : Scheme.{u}} (η : pts.obj X ⟶ pts.obj Y) {R S : CommRingCat.{u}}
    (c : Spec S ⟶ Spec R) (a : Spec R ⟶ X) : c ≫ η.app R a = η.app S (c ≫ a) := by
  have := NatTrans.naturality_apply η (Spec.preimage c) a
  rw [← Spec.map_preimage c]
  exact this.symm

theorem pts_aux {X Y Z : Scheme.{u}} (η : pts.obj X ⟶ pts.obj Y) {S R R' : CommRingCat.{u}}
    (b : Spec S ⟶ Z) (p : Z ⟶ Spec R) (q : Z ⟶ Spec R') (c : Spec R ⟶ X) (g : Spec R' ⟶ X)
    (G : X ⟶ Y) (hc : p ≫ c = q ≫ g) (h1 : g ≫ G = η.app R' g) :
    b ≫ p ≫ c ≫ G = b ≫ p ≫ η.app R c := by
  rw [reassoc_of% hc, h1, ← Category.assoc, ← Category.assoc, pts_nat, pts_nat,
    Category.assoc, Category.assoc, hc]

/-- Fullness of the functor of points, given an affine open cover of the source. -/
theorem pts_full_aux {X Y : Scheme.{u}} (𝒰 : X.AffineOpenCover) (η : pts.obj X ⟶ pts.obj Y) :
    ∃ F : X ⟶ Y, pts.map F = η := by
  have hf : ∀ i j, pullback.fst (𝒰.openCover.f i) (𝒰.openCover.f j) ≫ η.app _ (𝒰.f i) =
      pullback.snd (𝒰.openCover.f i) (𝒰.openCover.f j) ≫ η.app _ (𝒰.f j) := by
    intro i j
    refine ext_of_affine _ _ fun R b => ?_
    have hc : (b ≫ pullback.fst (𝒰.openCover.f i) (𝒰.openCover.f j)) ≫ 𝒰.f i =
        (b ≫ pullback.snd (𝒰.openCover.f i) (𝒰.openCover.f j)) ≫ 𝒰.f j :=
      (Category.assoc _ _ _).trans ((congrArg (b ≫ ·) pullback.condition).trans
        (Category.assoc _ _ _).symm)
    calc _ = (b ≫ pullback.fst (𝒰.openCover.f i) (𝒰.openCover.f j)) ≫ η.app _ (𝒰.f i) :=
          (Category.assoc _ _ _).symm
      _ = η.app R ((b ≫ pullback.fst (𝒰.openCover.f i) (𝒰.openCover.f j)) ≫ 𝒰.f i) :=
          pts_nat _ _ _
      _ = η.app R ((b ≫ pullback.snd (𝒰.openCover.f i) (𝒰.openCover.f j)) ≫ 𝒰.f j) := by
          rw [hc]
      _ = (b ≫ pullback.snd (𝒰.openCover.f i) (𝒰.openCover.f j)) ≫ η.app _ (𝒰.f j) :=
          (pts_nat _ _ _).symm
      _ = _ := Category.assoc _ _ _
  suffices key : ∀ (R : CommRingCat.{u}) (c : Spec R ⟶ X),
      c ≫ 𝒰.openCover.glueMorphisms (fun i => η.app _ (𝒰.f i)) hf = η.app R c by
    refine ⟨𝒰.openCover.glueMorphisms (fun i => η.app _ (𝒰.f i)) hf, ?_⟩
    ext R c
    exact key R c
  intro R c
  refine Scheme.Cover.hom_ext (𝒰.openCover.pullback₁ c) _ _ fun i => ?_
  refine ext_of_affine _ _ fun S b => ?_
  have h1 := Scheme.Cover.ι_glueMorphisms 𝒰.openCover (fun i => η.app _ (𝒰.f i)) hf i
  exact pts_aux η b (pullback.fst c (𝒰.f i)) (pullback.snd c (𝒰.f i)) c (𝒰.f i) _
    pullback.condition h1

/-- thSz9ZHDK9o-13183 (3:39:43) [prop] The functor associating to a scheme its functor of points
on rings is fully faithful (here over `k = ℤ`, i.e. all schemes and all rings). -/
theorem prop_13183 : pts.{u}.Faithful ∧ pts.{u}.Full := by
  refine ⟨⟨fun {X Y} f g h => ext_of_affine f g fun R a => ?_⟩,
    ⟨fun {X Y} η => pts_full_aux X.affineOpenCover η⟩⟩
  have := NatTrans.congr_app h R
  exact ConcreteCategory.congr_hom this a

/-- thSz9ZHDK9o-13375 (3:42:55) [prop] If `X = Spec A` is affine, `Hom(X, Y) → Hom(X', Y')` is
bijective (Yoneda, `X'` being representable). -/
theorem prop_13375 (A : CommRingCat.{u}) (Y : Scheme.{u}) :
    Function.Bijective (pts.map : (Spec A ⟶ Y) → (pts.obj (Spec A) ⟶ pts.obj Y)) := by
  obtain ⟨_, _⟩ := prop_13183.{u}
  exact ⟨pts.map_injective, pts.map_surjective⟩

/-- thSz9ZHDK9o-13648 (3:47:28) [prop] For an open covering `(X_i)` of a scheme `X`,
`Hom(X, Y) → ∏ Hom(X_i, Y) ⇉ ∏ Hom(X_{ij}, Y)` is exact (here for `Y` a scheme;
`X_{ij} = X_i ×_X X_j = X_i ∩ X_j`). -/
theorem prop_13648 {X Y : Scheme.{u}} (𝒰 : X.OpenCover) :
    (∀ f g : X ⟶ Y, (∀ i, 𝒰.f i ≫ f = 𝒰.f i ≫ g) → f = g) ∧
      ∀ (f : ∀ i, 𝒰.X i ⟶ Y),
        (∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd _ _ ≫ f j) →
          ∃ g : X ⟶ Y, ∀ i, 𝒰.f i ≫ g = f i :=
  ⟨fun f g h => Scheme.Cover.hom_ext 𝒰 f g h,
    fun f hf => ⟨𝒰.glueMorphisms f hf, fun i => Scheme.Cover.ι_glueMorphisms 𝒰 f hf i⟩⟩

end

end Buffalo.AG.Part04

namespace Buffalo.AG.Part04

/-- thSz9ZHDK9o-9961 (2:46:01) [prop] `φ^* M^~ ≃ (M ⊗_A B)^~`. Partial: the two adjunctions whose
left adjoints these are — `φ^* ⊣ φ_*` on modules over schemes and extension ⊣ restriction of
scalars — are in mathlib (`prop_9833`), but not the identification `Γ ∘ φ_* ≅ (·)_{[A]} ∘ Γ`
that makes the two left adjoints agree on `M^~`. -/
noncomputable def prop_9961 {A B : CommRingCat.{u}} (u : A ⟶ B) :
    Scheme.Modules.pullback (Spec.map u) ⊣ Scheme.Modules.pushforward (Spec.map u) :=
  Scheme.Modules.pullbackPushforwardAdjunction (Spec.map u)

end Buffalo.AG.Part04
