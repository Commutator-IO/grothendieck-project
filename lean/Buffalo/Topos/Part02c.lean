import Buffalo.Topos.Part02a

/-!
# Buffalo, topos theory, part 2c: sober spaces and fibre functors (18 and 25 May 1973)

Entries of `docs/buffalo-topos/index.tex` from « Irreducible closed sets and sober spaces » to
« Points and morphisms of sober spaces » (video `URU5jgTvjhU`, 7:54:19–8:33:13). The status of
each entry is in `docs/buffalo-topos/lean/Part02.json`.

The space `X̃` of irreducible closed subsets is `Sob X` (a type synonym of Mathlib's
`IrreducibleCloseds X`) with the topology of the sets `Ũ = {Y | Y ∩ U ≠ ∅}`. Fibre functors on
`Sh(X)` are Mathlib's points of the site `𝒪(X)` (`GrothendieckTopology.Point`, SGA 4 IV 6.3):
`irrPoint Y` is the point `F ↦ F_Y` attached to an irreducible closed set `Y`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace Buffalo.Topos.Part02

noncomputable section

variable {Z : Type u} [TopologicalSpace Z]

/-! ## Irreducible closed sets -/

/-- URU5jgTvjhU-28459 (7:54:19) [def] The entry's definition read literally: `Z` nonempty and not a
union of two *distinct* closed subsets. -/
def IsIrreducibleLiteral (Z : Type*) [TopologicalSpace Z] : Prop :=
  Nonempty Z ∧ ¬ ∃ A B : Set Z, IsClosed A ∧ IsClosed B ∧ A ≠ B ∧ A ∪ B = Set.univ

/-- URU5jgTvjhU-28459 (7:54:19) [def] The literal reading is never satisfied (`Z = Z ∪ ∅`), though the
point is irreducible: « distinct » must be « distinct from `Z` ». -/
theorem isIrreducibleLiteral_false (Z : Type*) [TopologicalSpace Z] : ¬ IsIrreducibleLiteral Z := by
  rintro ⟨⟨z⟩, h⟩
  exact h ⟨Set.univ, ∅, isClosed_univ, isClosed_empty,
    fun e => (e ▸ Set.mem_univ z : z ∈ (∅ : Set Z)), Set.union_empty _⟩

/-- URU5jgTvjhU-28459 (7:54:19) [def] The corrected definition: `Z` is irreducible iff it is
nonempty and not the union of two closed subsets distinct from `Z`. -/
theorem irreducibleSpace_iff_closed (Z : Type*) [TopologicalSpace Z] :
    IrreducibleSpace Z ↔ Nonempty Z ∧
      ¬ ∃ A B : Set Z, IsClosed A ∧ IsClosed B ∧ A ≠ Set.univ ∧ B ≠ Set.univ ∧
        A ∪ B = Set.univ := by
  rw [irreducibleSpace_def, IsIrreducible, isPreirreducible_iff_isClosed_union_isClosed]
  simp only [Set.top_eq_univ]
  rw [← Set.nonempty_iff_univ_nonempty]
  refine and_congr_right fun _ => ⟨fun h ⟨A, B, hA, hB, hA', hB', hAB⟩ => ?_, fun h A B hA hB hAB => ?_⟩
  · rcases h A B hA hB hAB.ge with h' | h'
    · exact hA' (Set.univ_subset_iff.1 h')
    · exact hB' (Set.univ_subset_iff.1 h')
  · by_contra hc
    push Not at hc
    exact h ⟨A, B, hA, hB, fun e => hc.1 (e ▸ le_rfl), fun e => hc.2 (e ▸ le_rfl),
      Set.univ_subset_iff.1 hAB⟩

/-- URU5jgTvjhU-28524 (7:55:24) [prop] A separated space is irreducible iff it is a point. -/
theorem t2_isIrreducible_iff [T2Space Z] {S : Set Z} : IsIrreducible S ↔ ∃ x, S = {x} :=
  isIrreducible_iff_singleton

/-- URU5jgTvjhU-28524 (7:55:24) [prop] For the Zariski topology, `V(I)` (`I` radical) is
irreducible iff `I` is prime. -/
theorem zariski_isIrreducible_iff {R : Type*} [CommRing R] {I : Ideal R} (hI : I.IsRadical) :
    IsIrreducible (PrimeSpectrum.zeroLocus (I : Set R)) ↔ I.IsPrime :=
  PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical I hI

/-- URU5jgTvjhU-28524 (7:55:24) [prop] The closure of an irreducible subset is irreducible. -/
theorem closure_irreducible {S : Set Z} (h : IsIrreducible S) : IsIrreducible (closure S) :=
  h.closure

/-! ## The space `X̃` of irreducible closed sets -/

variable (Z) in
/-- URU5jgTvjhU-28590 (7:56:30) [def] `X̃`, the set of irreducible closed subsets of `X`. -/
def Sob : Type u := IrreducibleCloseds Z

instance : SetLike (Sob Z) Z := inferInstanceAs (SetLike (IrreducibleCloseds Z) Z)

/-- URU5jgTvjhU-28590 (7:56:30) [def] `i : X → X̃`, `x ↦ closure {x}`. -/
def sobMap (x : Z) : Sob Z :=
  (⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ : IrreducibleCloseds Z)

@[simp] theorem coe_sobMap (x : Z) : ((sobMap x : Sob Z) : Set Z) = closure {x} := rfl

theorem Sob.isIrreducible (Y : Sob Z) : IsIrreducible (Y : Set Z) :=
  IrreducibleCloseds.isIrreducible (Y : IrreducibleCloseds Z)

theorem Sob.isClosed (Y : Sob Z) : IsClosed (Y : Set Z) :=
  IrreducibleCloseds.isClosed (Y : IrreducibleCloseds Z)

/-- The irreducible closed set `Y` as an element of `Sob Z`. -/
def Sob.mk (Y : Set Z) (h₁ : IsIrreducible Y) (h₂ : IsClosed Y) : Sob Z :=
  (⟨Y, h₁, h₂⟩ : IrreducibleCloseds Z)

@[simp] theorem Sob.coe_mk (Y : Set Z) (h₁ : IsIrreducible Y) (h₂ : IsClosed Y) :
    ((Sob.mk Y h₁ h₂ : Sob Z) : Set Z) = Y := rfl

@[ext] theorem Sob.ext {Y Y' : Sob Z} (h : (Y : Set Z) = Y') : Y = Y' := SetLike.coe_injective h

/-- URU5jgTvjhU-28654 (7:57:34) [prop] `Ũ = {Y ∈ X̃ | Y ∩ U ≠ ∅}`. -/
def tilde (U : Set Z) : Set (Sob Z) := {Y | ((Y : Set Z) ∩ U).Nonempty}

/-- URU5jgTvjhU-28654 (7:57:34) [prop] `U ↦ Ũ` respects unions. -/
theorem tilde_sUnion (S : Set (Set Z)) : tilde (⋃₀ S) = ⋃ U ∈ S, tilde U := by
  ext Y
  simp only [tilde, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨x, hxY, U, hU, hxU⟩
    exact ⟨U, hU, x, hxY, hxU⟩
  · rintro ⟨U, hU, x, hxY, hxU⟩
    exact ⟨x, hxY, U, hU, hxU⟩

/-- URU5jgTvjhU-28654 (7:57:34) [prop] `U ↦ Ũ` respects finite intersections of open sets (since
the `Y` are irreducible). -/
theorem tilde_inter {U V : Set Z} (hU : IsOpen U) (hV : IsOpen V) :
    tilde (U ∩ V) = tilde U ∩ tilde V := by
  ext Y
  refine ⟨fun ⟨x, hY, hU', hV'⟩ => ⟨⟨x, hY, hU'⟩, ⟨x, hY, hV'⟩⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  exact Y.isIrreducible.isPreirreducible U V hU hV h₁ h₂

theorem tilde_univ : tilde (Set.univ : Set Z) = Set.univ := by
  ext Y
  simpa [tilde] using Y.isIrreducible.nonempty

theorem tilde_mono {U V : Set Z} (h : U ⊆ V) : tilde U ⊆ tilde V :=
  fun _ ⟨x, hY, hU⟩ => ⟨x, hY, h hU⟩

/-- URU5jgTvjhU-28654 (7:57:34) [prop] The sets `Ũ`, `U` open, form a topology on `X̃`. -/
instance : TopologicalSpace (Sob Z) where
  IsOpen 𝒰 := ∃ U : Set Z, IsOpen U ∧ 𝒰 = tilde U
  isOpen_univ := ⟨Set.univ, isOpen_univ, tilde_univ.symm⟩
  isOpen_inter := by
    rintro _ _ ⟨U, hU, rfl⟩ ⟨V, hV, rfl⟩
    exact ⟨U ∩ V, hU.inter hV, (tilde_inter hU hV).symm⟩
  isOpen_sUnion := by
    intro S hS
    choose U hU hSU using hS
    refine ⟨⋃ (s : Set (Sob Z)) (h : s ∈ S), U s h, isOpen_iUnion fun s => isOpen_iUnion fun h => hU s h, ?_⟩
    ext Y
    constructor
    · rintro ⟨s, hs, hY⟩
      rw [hSU s hs] at hY
      obtain ⟨x, hxY, hxU⟩ := hY
      exact ⟨x, hxY, Set.mem_iUnion₂.2 ⟨s, hs, hxU⟩⟩
    · rintro ⟨x, hxY, hx⟩
      obtain ⟨s, hs, hxU⟩ := Set.mem_iUnion₂.1 hx
      exact ⟨s, hs, by rw [hSU s hs]; exact ⟨x, hxY, hxU⟩⟩

theorem isOpen_sob_iff {𝒰 : Set (Sob Z)} : IsOpen 𝒰 ↔ ∃ U : Set Z, IsOpen U ∧ 𝒰 = tilde U :=
  Iff.rfl

theorem isOpen_tilde {U : Set Z} (hU : IsOpen U) : IsOpen (tilde U) := ⟨U, hU, rfl⟩

/-- URU5jgTvjhU-28850 (8:00:50) [prop] `i⁻¹(Ũ) = U` for `U` open. -/
theorem sobMap_preimage_tilde {U : Set Z} (hU : IsOpen U) : sobMap ⁻¹' tilde U = U := by
  ext x
  exact (isGenericPoint_closure.mem_open_set_iff hU).symm

/-- URU5jgTvjhU-28850 (8:00:50) [prop] `i : X → X̃` is continuous. -/
theorem continuous_sobMap : Continuous (sobMap : Z → Sob Z) := by
  rw [continuous_def]
  rintro _ ⟨U, hU, rfl⟩
  rwa [sobMap_preimage_tilde hU]

/-- Two closed sets meeting the same open sets are equal. -/
theorem closed_eq_of_meets {A B : Set Z} (hA : IsClosed A) (hB : IsClosed B)
    (h : ∀ U : Set Z, IsOpen U → ((A ∩ U).Nonempty ↔ (B ∩ U).Nonempty)) : A = B := by
  have key : ∀ {A B : Set Z}, IsClosed B →
      (∀ U : Set Z, IsOpen U → (A ∩ U).Nonempty → (B ∩ U).Nonempty) → A ⊆ B := by
    intro A B hB h x hxA
    by_contra hxB
    obtain ⟨y, hyB, hyU⟩ := h Bᶜ hB.isOpen_compl ⟨x, hxA, hxB⟩
    exact hyU hyB
  exact le_antisymm (key hB fun U hU => (h U hU).1) (key hA fun U hU => (h U hU).2)

theorem tilde_injective {U V : Set Z} (hU : IsOpen U) (hV : IsOpen V) (h : tilde U = tilde V) :
    U = V := by
  rw [← sobMap_preimage_tilde hU, h, sobMap_preimage_tilde hV]

/-- URU5jgTvjhU-28850 (8:00:50) [prop] `i` induces a lattice isomorphism `𝒪(X̃) ≃ 𝒪(X)`. -/
def opensSobIso : Opens (Sob Z) ≃o Opens Z where
  toFun 𝒰 := ⟨sobMap ⁻¹' 𝒰, 𝒰.2.preimage continuous_sobMap⟩
  invFun U := ⟨tilde U, isOpen_tilde U.2⟩
  left_inv 𝒰 := by
    obtain ⟨𝒰, U, hU, rfl⟩ := 𝒰
    ext1
    change tilde (sobMap ⁻¹' tilde U) = tilde U
    rw [sobMap_preimage_tilde hU]
  right_inv U := by
    ext1
    exact sobMap_preimage_tilde U.2
  map_rel_iff' {𝒰 𝒱} := by
    obtain ⟨𝒰, U, hU, rfl⟩ := 𝒰
    obtain ⟨𝒱, V, hV, rfl⟩ := 𝒱
    change sobMap ⁻¹' tilde U ⊆ sobMap ⁻¹' tilde V ↔ tilde U ⊆ tilde V
    rw [sobMap_preimage_tilde hU, sobMap_preimage_tilde hV]
    exact ⟨tilde_mono, fun h x hx => by
      have := h (show sobMap x ∈ tilde U by rwa [← Set.mem_preimage, sobMap_preimage_tilde hU])
      rwa [← Set.mem_preimage, sobMap_preimage_tilde hV] at this⟩

theorem not_mem_tilde_iff (U : Set Z) (Y : Sob Z) : Y ∉ tilde U ↔ (Y : Set Z) ⊆ Uᶜ := by
  simp [tilde, Set.subset_compl_iff_disjoint_right, Set.disjoint_iff_inter_eq_empty,
    Set.not_nonempty_iff_eq_empty]

/-- The closed sets of `X̃` are the sets `{Y | Y ⊆ D}`, `D` closed in `X`. -/
theorem isClosed_sob_iff {𝒵 : Set (Sob Z)} :
    IsClosed 𝒵 ↔ ∃ D : Set Z, IsClosed D ∧ 𝒵 = {Y : Sob Z | (Y : Set Z) ⊆ D} := by
  rw [← isOpen_compl_iff, isOpen_sob_iff]
  constructor
  · rintro ⟨U, hU, h⟩
    refine ⟨Uᶜ, hU.isClosed_compl, ?_⟩
    ext Y
    change Y ∈ 𝒵 ↔ (Y : Set Z) ⊆ Uᶜ
    rw [← not_mem_tilde_iff, ← h, Set.mem_compl_iff, not_not]
  · rintro ⟨D, hD, rfl⟩
    refine ⟨Dᶜ, hD.isOpen_compl, ?_⟩
    ext Y
    change ¬ ((Y : Set Z) ⊆ D) ↔ Y ∈ tilde Dᶜ
    rw [← not_iff_not, not_not, not_mem_tilde_iff, compl_compl]

theorem isClosed_le (D : Set Z) (hD : IsClosed D) : IsClosed {Y : Sob Z | (Y : Set Z) ⊆ D} :=
  isClosed_sob_iff.2 ⟨D, hD, rfl⟩

/-- The closure of a point `Y` of `X̃` is `{Y' | Y' ⊆ Y}`. -/
theorem closure_sob_singleton (Y : Sob Z) :
    closure {Y} = {Y' : Sob Z | (Y' : Set Z) ⊆ Y} := by
  apply le_antisymm
  · exact closure_minimal (Set.singleton_subset_iff.2 (le_refl (Y : Set Z)))
      (isClosed_le _ Y.isClosed)
  · intro Y' hY'
    rw [mem_closure_iff]
    rintro _ ⟨U, hU, rfl⟩ ⟨x, hx, hxU⟩
    exact ⟨Y, ⟨x, hY' hx, hxU⟩, rfl⟩

/-- URU5jgTvjhU-29036 (8:03:56) [prop] `i` is injective iff `X` is `T₀`. -/
theorem sobMap_injective_iff : Function.Injective (sobMap : Z → Sob Z) ↔ T0Space Z := by
  rw [t0Space_iff_inseparable]
  refine ⟨fun h x y hxy => h (Sob.ext ?_), fun h x y hxy => h x y ?_⟩
  · exact inseparable_iff_closure_eq.1 hxy
  · exact inseparable_iff_closure_eq.2 (congrArg (fun Y : Sob Z => (Y : Set Z)) hxy)

/-- URU5jgTvjhU-29101 (8:05:01) [def] `i` is surjective iff every irreducible closed set has a
generic point (Mathlib's `QuasiSober`). -/
theorem sobMap_surjective_iff : Function.Surjective (sobMap : Z → Sob Z) ↔ QuasiSober Z := by
  constructor
  · intro h
    refine ⟨fun {S} hS hS' => ?_⟩
    obtain ⟨x, hx⟩ := h (Sob.mk S hS hS')
    exact ⟨x, congrArg (fun Y : Sob Z => (Y : Set Z)) hx⟩
  · intro h Y
    obtain ⟨x, hx⟩ := QuasiSober.sober Y.isIrreducible Y.isClosed
    exact ⟨x, Sob.ext hx⟩

/-- URU5jgTvjhU-28590 (7:56:30) [def] `i` is bijective if `X` is separated. -/
theorem sobMap_bijective_of_t2 [T2Space Z] : Function.Bijective (sobMap : Z → Sob Z) := by
  refine ⟨sobMap_injective_iff.2 inferInstance, sobMap_surjective_iff.2 ?_⟩
  exact ⟨fun {S} hS _ => by
    obtain ⟨x, rfl⟩ := isIrreducible_iff_singleton.1 hS
    exact ⟨x, by simp [IsGenericPoint]⟩⟩

/-- If `i` is bijective it is a homeomorphism. -/
def sobHomeomorph (h : Function.Bijective (sobMap : Z → Sob Z)) : Z ≃ₜ Sob Z where
  toEquiv := Equiv.ofBijective _ h
  continuous_toFun := continuous_sobMap
  continuous_invFun := by
    rw [continuous_def]
    intro U hU
    refine ⟨U, hU, ?_⟩
    ext Y
    obtain ⟨x, rfl⟩ := h.2 Y
    change (Equiv.ofBijective _ h).symm (sobMap x) ∈ U ↔ sobMap x ∈ tilde U
    rw [show (Equiv.ofBijective _ h).symm (sobMap x) = x from
      (Equiv.ofBijective _ h).symm_apply_apply x, ← Set.mem_preimage, sobMap_preimage_tilde hU]

/-- URU5jgTvjhU-29036 (8:03:56) [prop] If `X` is separated, `i` is a homeomorphism. -/
def sobHomeomorph_of_t2 [T2Space Z] : Z ≃ₜ Sob Z := sobHomeomorph sobMap_bijective_of_t2

/-- URU5jgTvjhU-29234 (8:07:14) [def] `X` is sober (every irreducible closed set has exactly one
generic point: Mathlib's `QuasiSober` and `T0Space`) iff `i : X → X̃` is bijective, hence a
homeomorphism. -/
theorem sober_iff_bijective :
    QuasiSober Z ∧ T0Space Z ↔ Function.Bijective (sobMap : Z → Sob Z) := by
  rw [Function.Bijective, sobMap_injective_iff, sobMap_surjective_iff, and_comm]

/-- URU5jgTvjhU-29166 (8:06:06) [ex] The `K`-rational points of the affine line, with the Zariski
(cofinite) topology, `K` infinite: the whole space is irreducible but has no generic point. -/
theorem cofinite_no_generic_point (K : Type*) [Infinite K] :
    IsIrreducible (Set.univ : Set (CofiniteTopology K)) ∧
      ∀ x : CofiniteTopology K, ¬ IsGenericPoint x Set.univ := by
  refine ⟨⟨Set.univ_nonempty, fun u v hu hv hau hbv => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨a, -, ha⟩ := hau
    obtain ⟨b, -, hb⟩ := hbv
    rw [CofiniteTopology.isOpen_iff] at hu hv
    have hfin : (uᶜ ∪ vᶜ).Finite := (hu ⟨a, ha⟩).union (hv ⟨b, hb⟩)
    obtain ⟨c, hc⟩ := hfin.infinite_compl.nonempty
    simp only [Set.compl_union, compl_compl] at hc
    exact ⟨c, trivial, hc⟩
  · have : closure ({x} : Set (CofiniteTopology K)) = {x} := isClosed_singleton.closure_eq
    rw [IsGenericPoint, this] at hx
    obtain ⟨y, hy⟩ := (Set.infinite_univ (α := CofiniteTopology K)).sdiff
      (Set.finite_singleton x) |>.nonempty
    exact hy.2 (hx ▸ hy.1)

/-! ## `X̃` is sober -/

/-- URU5jgTvjhU-29622 (8:13:42) [thm] `X̃` is `T₀`. -/
instance : T0Space (Sob Z) := by
  rw [t0Space_iff_inseparable]
  intro Y Y' h
  rw [inseparable_iff_forall_isOpen] at h
  apply Sob.ext
  apply closed_eq_of_meets Y.isClosed Y'.isClosed
  intro U hU
  exact h (tilde U) (isOpen_tilde hU)

/-- URU5jgTvjhU-29622 (8:13:42) [thm] `X̃` is quasi-sober: an irreducible closed set
`{Y | Y ⊆ D}` of `X̃` has the generic point `D`. -/
instance : QuasiSober (Sob Z) := by
  refine ⟨fun {𝒵} h𝒵 h𝒵c => ?_⟩
  obtain ⟨D, hD, rfl⟩ := isClosed_sob_iff.1 h𝒵c
  have hDirr : IsIrreducible D := by
    obtain ⟨Y₀, hY₀⟩ := h𝒵.nonempty
    refine ⟨Y₀.isIrreducible.nonempty.mono hY₀, ?_⟩
    rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro z₁ z₂ hz₁ hz₂ hD12
    have hsub : {Y : Sob Z | (Y : Set Z) ⊆ D} ⊆
        {Y : Sob Z | (Y : Set Z) ⊆ z₁} ∪ {Y : Sob Z | (Y : Set Z) ⊆ z₂} := by
      intro Y hY
      exact (isPreirreducible_iff_isClosed_union_isClosed.1 Y.isIrreducible.isPreirreducible
        z₁ z₂ hz₁ hz₂ (hY.trans hD12))
    rcases (isPreirreducible_iff_isClosed_union_isClosed.1 h𝒵.isPreirreducible _ _
        (isClosed_le z₁ hz₁) (isClosed_le z₂ hz₂) hsub) with h' | h'
    · left
      intro x hx
      exact h' (show (sobMap x : Sob Z) ∈ {Y : Sob Z | (Y : Set Z) ⊆ D} from
        closure_minimal (Set.singleton_subset_iff.2 hx) hD) (subset_closure rfl)
    · right
      intro x hx
      exact h' (show (sobMap x : Sob Z) ∈ {Y : Sob Z | (Y : Set Z) ⊆ D} from
        closure_minimal (Set.singleton_subset_iff.2 hx) hD) (subset_closure rfl)
  refine ⟨Sob.mk D hDirr hD, ?_⟩
  rw [IsGenericPoint, closure_sob_singleton]
  rfl

/-- `X̃` is sober. -/
theorem sob_sober : QuasiSober (Sob Z) ∧ T0Space (Sob Z) := ⟨inferInstance, inferInstance⟩

/-- URU5jgTvjhU-30013 (8:20:13) [thm] `i : X → X̃` is a homeomorphism iff `X` is sober. -/
theorem sobMap_homeomorph_iff :
    (∃ h : Z ≃ₜ Sob Z, ⇑h = sobMap) ↔ QuasiSober Z ∧ T0Space Z := by
  rw [sober_iff_bijective]
  exact ⟨fun ⟨h, e⟩ => e ▸ h.bijective, fun hb => ⟨sobHomeomorph hb, rfl⟩⟩

/-- URU5jgTvjhU-30076 (8:21:16) [prop] If `X` is `T₁`, `i` is an embedding whose image is the set
of closed points of `X̃`. -/
theorem sobMap_t1 [T1Space Z] :
    IsEmbedding (sobMap : Z → Sob Z) ∧ Set.range (sobMap : Z → Sob Z) = {Y | IsClosed {Y}} := by
  refine ⟨⟨⟨?_⟩, sobMap_injective_iff.2 inferInstance⟩, ?_⟩
  · ext s
    rw [isOpen_induced_iff]
    constructor
    · intro hs
      exact ⟨tilde s, isOpen_tilde hs, sobMap_preimage_tilde hs⟩
    · rintro ⟨_, ⟨U, hU, rfl⟩, rfl⟩
      rw [sobMap_preimage_tilde hU]
      exact hU
  · ext Y
    constructor
    · rintro ⟨x, rfl⟩
      show IsClosed {sobMap x}
      rw [← closure_subset_iff_isClosed, closure_sob_singleton]
      intro Y' hY'
      have hx : ((sobMap x : Sob Z) : Set Z) = {x} := by simp
      obtain ⟨y, hy⟩ := Y'.isIrreducible.nonempty
      have hY'x : (Y' : Set Z) = {x} := by
        apply le_antisymm (hY'.trans hx.le)
        rintro _ rfl
        have := hx ▸ hY' hy
        rw [Set.mem_singleton_iff.1 this] at hy
        exact hy
      exact Sob.ext (hY'x.trans hx.symm)
    · intro hY
      obtain ⟨x, hx⟩ := Y.isIrreducible.nonempty
      refine ⟨x, ?_⟩
      have : (sobMap x : Sob Z) ∈ closure {Y} := by
        rw [closure_sob_singleton]
        exact closure_minimal (Set.singleton_subset_iff.2 hx) Y.isClosed
      rw [hY.closure_eq] at this
      exact this

/-- URU5jgTvjhU-29622 (8:13:42) [thm] Universal property of `X̃`: for `W` sober, every continuous
`f : X → W` extends uniquely along `i` to a continuous map `X̃ → W`, `Y ↦` generic point of
`closure (f Y)`; that is, `Hom(X, W) ≃ Hom(X̃, W)`. -/
theorem sob_universal {W : Type*} [TopologicalSpace W] [QuasiSober W] [T0Space W] (f : C(Z, W)) :
    ∃! g : C(Sob Z, W), ⇑g ∘ sobMap = f := by
  let F : Sob Z → W := fun Y => (Y.isIrreducible.image f f.continuous.continuousOn).genericPoint
  have hF : ∀ Y : Sob Z, IsGenericPoint (F Y) (closure (f '' Y)) := fun Y =>
    (Y.isIrreducible.image f f.continuous.continuousOn).isGenericPoint_genericPoint_closure
  have hFc : Continuous F := by
    rw [continuous_def]
    intro V hV
    refine ⟨f ⁻¹' V, hV.preimage f.continuous, ?_⟩
    ext Y
    change F Y ∈ V ↔ ((Y : Set Z) ∩ f ⁻¹' V).Nonempty
    rw [(hF Y).mem_open_set_iff hV, closure_inter_open_nonempty_iff hV]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxV⟩
      exact ⟨x, hx, hxV⟩
    · rintro ⟨x, hx, hxV⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, hxV⟩
  have hclos : ∀ Y : Sob Z, closure (sobMap '' (Y : Set Z)) = closure {Y} := by
    intro Y
    rw [closure_sob_singleton]
    apply le_antisymm
    · exact closure_minimal (fun _ ⟨x, hx, e⟩ => e ▸ closure_minimal
        (Set.singleton_subset_iff.2 hx) Y.isClosed) (isClosed_le _ Y.isClosed)
    · intro Y' hY'
      obtain ⟨D, hD, hDe⟩ := isClosed_sob_iff.1 (isClosed_closure (s := sobMap '' (Y : Set Z)))
      rw [hDe]
      have hYD : (Y : Set Z) ⊆ D := by
        intro x hx
        have : sobMap x ∈ closure (sobMap '' (Y : Set Z)) := subset_closure ⟨x, hx, rfl⟩
        rw [hDe] at this
        exact this (subset_closure rfl)
      exact hY'.trans hYD
  refine ⟨⟨F, hFc⟩, ?_, ?_⟩
  · funext x
    change F (sobMap x) = f x
    apply (hF (sobMap x)).eq
    have : closure (f '' closure {x}) = closure {f x} := by
      rw [closure_image_closure f.continuous, Set.image_singleton]
    change IsGenericPoint (f x) (closure (f '' closure {x}))
    rw [this]
    exact isGenericPoint_closure
  · intro g hg
    ext Y
    apply IsGenericPoint.eq _ (hF Y)
    have := (isGenericPoint_closure (x := Y)).image g.continuous
    rwa [← hclos, closure_image_closure g.continuous, ← Set.image_comp, hg] at this

/-! ## Fibre functors and points of `Sh(X)` -/

open GrothendieckTopology

/-- URU5jgTvjhU-29300 (8:08:20) [def] For `Y` irreducible closed, the point of the site `𝒪(X)`
whose fibre over `U` is nonempty iff `U ∩ Y ≠ ∅`: the opens meeting `Y` form a cofiltered family
because `Y` is irreducible. -/
def irrPoint (Y : Sob Z) : Point.{u} (Opens.grothendieckTopology Z) where
  fiber.obj U := ULift.{u} (PLift ((Y : Set Z) ∩ U).Nonempty)
  fiber.map f := ↾fun h ↦ ⟨⟨h.down.down.mono (Set.inter_subset_inter_right _ (leOfHom f))⟩⟩
  isCofiltered :=
    { nonempty := ⟨.mk (obj := ⊤) ⟨⟨by simpa using Y.isIrreducible.nonempty⟩⟩⟩
      cone_objs U V := by
        induction U with | @mk U hU
        induction V with | @mk V hV
        obtain ⟨⟨hU⟩⟩ := hU
        obtain ⟨⟨hV⟩⟩ := hV
        exact ⟨.mk (obj := U ⊓ V) ⟨⟨Y.isIrreducible.isPreirreducible U V U.2 V.2 hU hV⟩⟩,
          Functor.Elements.homMk (homOfLE (by simp)) rfl,
          Functor.Elements.homMk (homOfLE (by simp)) rfl, by tauto⟩
      cone_maps _ _ _ _ := ⟨_, 𝟙 _, rfl⟩ }
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective := by
    rintro U R hR ⟨⟨x, hxY, hxU⟩⟩
    obtain ⟨V, f, hf, hV⟩ := hR x hxU
    exact ⟨_, _, hf, ⟨⟨x, hxY, hV⟩⟩, rfl⟩

/-- URU5jgTvjhU-29300 (8:08:20) [def] The stalk `F_Y = colim_{U ∩ Y ≠ ∅} F(U)` commutes with finite
limits and with colimits. -/
theorem irrPoint_exact (Y : Sob Z) :
    Nonempty (PreservesFiniteLimits ((irrPoint Y).sheafFiber (A := Type u))) ∧
      Nonempty (PreservesColimits ((irrPoint Y).sheafFiber (A := Type u))) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩

/-- Two points of `𝒪(X)` with the same nonempty fibres are isomorphic. -/
def pointIsoOfNonempty (Φ Ψ : Point.{u} (Opens.grothendieckTopology Z))
    (h : ∀ U : Opens Z, Nonempty (Φ.fiber.obj U) ↔ Nonempty (Ψ.fiber.obj U)) : Φ ≅ Ψ where
  hom := ⟨{ app := fun U => ↾fun a => ((h U).2 ⟨a⟩).some
            naturality := fun _ _ _ => by ext; exact Subsingleton.elim _ _ }⟩
  inv := ⟨{ app := fun U => ↾fun a => ((h U).1 ⟨a⟩).some
            naturality := fun _ _ _ => by ext; exact Subsingleton.elim _ _ }⟩
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

theorem nonempty_of_iso {Φ Ψ : Point.{u} (Opens.grothendieckTopology Z)} (e : Φ ≅ Ψ)
    (U : Opens Z) : Nonempty (Φ.fiber.obj U) ↔ Nonempty (Ψ.fiber.obj U) :=
  ⟨fun ⟨a⟩ => ⟨e.inv.hom.app U a⟩, fun ⟨a⟩ => ⟨e.hom.hom.app U a⟩⟩

theorem nonempty_irrPoint (Y : Sob Z) (U : Opens Z) :
    Nonempty ((irrPoint Y).fiber.obj U) ↔ ((Y : Set Z) ∩ U).Nonempty :=
  ⟨fun ⟨a⟩ => a.down.down, fun h => ⟨⟨⟨h⟩⟩⟩⟩

/-- URU5jgTvjhU-29427 (8:10:27) [prop] `F_{closure {x}} = F_x`: the point attached to `closure {x}`
is the point `x`. -/
def irrPoint_sobMap (x : Z) : irrPoint (sobMap x) ≅ Opens.pointGrothendieckTopology x :=
  pointIsoOfNonempty _ _ fun U => by
    rw [nonempty_irrPoint, coe_sobMap]
    exact ((isGenericPoint_closure (x := x)).mem_open_set_iff U.2).symm.trans
      ⟨fun h => ⟨⟨⟨h⟩⟩⟩, fun ⟨⟨⟨h⟩⟩⟩ => h⟩

section PointProperties

variable (Φ : Point.{u} (Opens.grothendieckTopology Z))

theorem point_mono {U V : Opens Z} (h : U ≤ V) (hU : Nonempty (Φ.fiber.obj U)) :
    Nonempty (Φ.fiber.obj V) :=
  ⟨Φ.fiber.map (homOfLE h) hU.some⟩

theorem point_top : Nonempty (Φ.fiber.obj ⊤) := by
  obtain ⟨e⟩ := (inferInstance : IsCofiltered Φ.fiber.Elements).nonempty
  exact point_mono Φ le_top ⟨e.2⟩

theorem point_inf {U V : Opens Z} (hU : Nonempty (Φ.fiber.obj U)) (hV : Nonempty (Φ.fiber.obj V)) :
    Nonempty (Φ.fiber.obj (U ⊓ V)) := by
  let a := Φ.fiber.elementsMk U hU.some
  let b := Φ.fiber.elementsMk V hV.some
  exact point_mono Φ (le_inf (leOfHom (IsCofiltered.minToLeft a b).1)
    (leOfHom (IsCofiltered.minToRight a b).1)) ⟨(IsCofiltered.min a b).2⟩

theorem point_iSup {ι : Type*} (V : ι → Opens Z) (h : Nonempty (Φ.fiber.obj (iSup V))) :
    ∃ i, Nonempty (Φ.fiber.obj (V i)) := by
  let R : Sieve (iSup V) :=
    { arrows := fun W _ => ∃ i, W ≤ V i
      downward_closed := fun {W W'} _ ⟨i, hi⟩ g => ⟨i, (leOfHom g).trans hi⟩ }
  have hR : R ∈ Opens.grothendieckTopology Z (iSup V) := by
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
    exact ⟨V i, homOfLE (le_iSup V i), ⟨i, le_rfl⟩, hi⟩
  obtain ⟨W, f, ⟨i, hi⟩, w, -⟩ := Φ.jointly_surjective R hR h.some
  exact ⟨i, point_mono Φ hi ⟨w⟩⟩

end PointProperties

/-- URU5jgTvjhU-29490 (8:11:30) [thm] `Y ↦ (F ↦ F_Y)` is a bijection from `X̃` onto the
isomorphism classes of fibre functors (points of the site `𝒪(X)`): injective ... -/
theorem irrPoint_injective {Y Y' : Sob Z} (e : irrPoint Y ≅ irrPoint Y') : Y = Y' := by
  apply Sob.ext
  apply closed_eq_of_meets Y.isClosed Y'.isClosed
  intro U hU
  have := nonempty_of_iso e ⟨U, hU⟩
  rwa [nonempty_irrPoint, nonempty_irrPoint] at this

/-- URU5jgTvjhU-29490 (8:11:30) [thm] ... and surjective: every point `Φ` is `F ↦ F_Y` for `Y` the
complement of the largest open set over which `Φ` is empty. -/
theorem irrPoint_surjective (Φ : Point.{u} (Opens.grothendieckTopology Z)) :
    ∃ Y : Sob Z, Nonempty (irrPoint Y ≅ Φ) := by
  let P : Opens Z → Prop := fun U => Nonempty (Φ.fiber.obj U)
  let W : Opens Z := sSup {V | ¬ P V}
  have hW : ¬ P W := by
    intro h
    change Nonempty (Φ.fiber.obj (sSup {V | ¬ P V})) at h
    rw [sSup_eq_iSup'] at h
    obtain ⟨⟨V, hV⟩, h'⟩ := point_iSup Φ _ h
    exact hV h'
  have key : ∀ U : Opens Z, P U ↔ ((W : Set Z)ᶜ ∩ U).Nonempty := by
    intro U
    constructor
    · intro hU
      by_contra hne
      apply hW
      refine point_mono Φ ?_ hU
      intro x hx
      by_contra hxW
      exact hne ⟨x, hxW, hx⟩
    · rintro ⟨x, hxW, hxU⟩
      by_contra hU
      exact hxW (le_sSup (show U ∈ {V | ¬ P V} from hU) hxU)
  have hirr : IsIrreducible (W : Set Z)ᶜ := by
    refine ⟨by simpa using (key ⊤).1 (point_top Φ), fun u v hu hv hu' hv' => ?_⟩
    have := (key (⟨u, hu⟩ ⊓ ⟨v, hv⟩)).1 (point_inf Φ ((key ⟨u, hu⟩).2 hu') ((key ⟨v, hv⟩).2 hv'))
    exact this
  refine ⟨Sob.mk _ hirr W.2.isClosed_compl, ⟨pointIsoOfNonempty _ _ fun U => ?_⟩⟩
  rw [nonempty_irrPoint, Sob.coe_mk]
  exact (key U).symm

/-- URU5jgTvjhU-29559 (8:12:39) [prop] A fibre functor on `Sh(X)` has no nontrivial automorphism
(the points of `𝒪(X)` form a thin category). -/
example (Φ : Point.{u} (Opens.grothendieckTopology Z)) : Subsingleton (Φ ⟶ Φ) := inferInstance

/-- URU5jgTvjhU-29816 (8:16:56) [def] The topology on the points of `Sh(X)` whose open sets are the
`Ũ = {ε | ε(U) ≠ ∅}`, `U ⊂ e` (an open set). -/
abbrev pointsTopology : TopologicalSpace (Point.{u} (Opens.grothendieckTopology Z)) :=
  TopologicalSpace.generateFrom
    {S | ∃ U : Opens Z, S = {Φ | Nonempty (Φ.fiber.obj U)}}

/-- URU5jgTvjhU-29816 (8:16:56) [def] The sets `Ũ` are stable under finite intersections and unions,
so they are exactly the open sets of this topology. -/
theorem pointsTopology_basis (U V : Opens Z) {ι : Type*} (T : ι → Opens Z)
    (Φ : Point.{u} (Opens.grothendieckTopology Z)) :
    (Nonempty (Φ.fiber.obj (U ⊓ V)) ↔ Nonempty (Φ.fiber.obj U) ∧ Nonempty (Φ.fiber.obj V)) ∧
      (Nonempty (Φ.fiber.obj (iSup T)) ↔ ∃ i, Nonempty (Φ.fiber.obj (T i))) :=
  ⟨⟨fun h => ⟨point_mono Φ inf_le_left h, point_mono Φ inf_le_right h⟩,
      fun ⟨h₁, h₂⟩ => point_inf Φ h₁ h₂⟩,
    ⟨point_iSup Φ T, fun ⟨i, h⟩ => point_mono Φ (le_iSup T i) h⟩⟩

/-! ## Points and morphisms of sober spaces -/

/-- URU5jgTvjhU-30280 (8:24:40) [prop] `(f^*F)_x ≃ F_{f(x)}`: the point `f(x)` corresponds to
`ε_x ∘ f^*`. -/
def pullback_stalk' {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Y.Presheaf (Type u)) (x : X) :
    F.stalk (f x) ≅ ((TopCat.Presheaf.pullback (Type u) f).obj F).stalk x :=
  TopCat.Presheaf.stalkPullbackIso (Type u) f F x

/-- URU5jgTvjhU-30471 (8:27:51) [thm] (case `X = pt`) If `Y` is sober, every point of the site `𝒪(Y)`
is isomorphic to the point of a unique `y ∈ Y`. -/
theorem sober_points [QuasiSober Z] [T0Space Z] (Φ : Point.{u} (Opens.grothendieckTopology Z)) :
    ∃! y : Z, Nonempty (Opens.pointGrothendieckTopology y ≅ Φ) := by
  obtain ⟨Y, ⟨e⟩⟩ := irrPoint_surjective Φ
  obtain ⟨y, rfl⟩ := (sober_iff_bijective.1 ⟨inferInstance, inferInstance⟩).2 Y
  refine ⟨y, ⟨(irrPoint_sobMap y).symm ≪≫ e⟩, fun y' ⟨e'⟩ => ?_⟩
  apply (sober_iff_bijective.1 ⟨inferInstance, inferInstance⟩).1
  exact irrPoint_injective (irrPoint_sobMap y' ≪≫ e' ≪≫ e.symm)

/-- URU5jgTvjhU-30793 (8:33:13) [def] Morphisms between the points `x, y` of `X` (morphisms of fibre
functors) correspond to specialisations `x ⤳ y`; if `X` is `T₁` (e.g. separated) there is one only
if `x = y`, and it is the identity. -/
theorem point_hom_t1 [T1Space Z] (x y : Z) :
    (Nonempty (Opens.pointGrothendieckTopology x ⟶ Opens.pointGrothendieckTopology y) ↔ x = y) ∧
      Subsingleton (Opens.pointGrothendieckTopology x ⟶ Opens.pointGrothendieckTopology y) :=
  ⟨⟨fun ⟨f⟩ => specializes_iff_eq.1 (Opens.pointGrothendieckTopologyHomEquiv f),
    fun h => h ▸ ⟨𝟙 _⟩⟩, inferInstance⟩

end

end Buffalo.Topos.Part02
