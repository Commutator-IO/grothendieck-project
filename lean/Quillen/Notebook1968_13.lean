import Mathlib

/-!
# Quillen, notebook 1968-13, pp. 64–69: the one-point extension along a family of supports

Daniel Quillen's notebook 1968-13 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201968/1968-13.pdf>), in December
1968, relates supports and bordism. On p. 64 he takes a family of supports `Φ` on a space `X`:
closed sets, stable under finite unions and closed subsets. On p. 65 he forms the space
`X ∪_Φ {∞}`, in which `X` is open and the neighbourhoods of `∞` are the sets `(X ∖ Z) ∪ {∞}`,
`Z ∈ Φ`. A crossed-out passage on p. 64 notes that it is Hausdorff when `Φ` contains a
neighbourhood of every point. Two special cases follow: for `Φ` the closed sets it is `X` plus an
isolated point, for `Φ` the compact sets the one-point compactification `X⁺`. On pp. 67–68,
after his own « Correction: just gave wrong definition of `X ∧ Y` » (the smash product is the
quotient of `X × Y` by the wedge), he states and proves (pp. 68–69):

  `X⁺ ∧ (Y ∪_Φ {∞}) = (X × Y) ∪_Ψ {∞}`,

where `Ψ` is the family of closed sets `A ⊆ X × Y` lying in `X × F` for some `F ∈ Φ` and proper
over `F`. His proof shows that such an `A` is closed in `X⁺ × F`; this file takes that as the
definition of `Ψ` (`smashSupports`): `A` lies in `X × F` with `F ∈ Φ` and its image in `X⁺ × Y`
is closed.

* `SupportFamily`, `Extension Φ`: the family and the space `X ∪_Φ {∞}`, with `ι : X → Extension Φ`
  and `infty`;
* `isOpenEmbedding_ι`, `isClosed_infty`: `X` is an open subspace and `{∞}` is closed;
* `t2Space_iff`: for `X` Hausdorff, `X ∪_Φ {∞}` is Hausdorff iff every point of `X` has a
  neighbourhood in `Φ` (p. 64);
* `compactSupports`, `homeomorphOnePoint`: for `Φ` the closed compact sets, `X ∪_Φ {∞}` is
  Mathlib's one-point compactification `OnePoint X` (p. 65);
* `closedSupports`, `isOpen_infty_closedSupports`: for `Φ` the closed sets, `∞` is isolated
  (p. 65);
* `smashSupports`, `smashMap`, `isQuotientMap_smashMap`: the lemma of pp. 68–69. The map
  `X⁺ × (Y ∪_Φ {∞}) → (X × Y) ∪_Ψ {∞}` that sends the wedge to `∞` is a quotient map, so the
  target is the smash product with its quotient topology.

No hypothesis on `X` or `Y` is needed for the smash lemma: Quillen assumes `X` locally compact,
which makes `X⁺` Hausdorff; the proof only uses that `X⁺` is compact.

Literature: supports and `Γ_Φ` are Godement's (1958) and Bredon's (*Sheaf theory*); the space
`X ∪_Φ {∞}` and the smash lemma were not found in print (zbMATH, « one-point compactification »
with « supports »); Bredon's book has not been checked page by page. Whyburn's « unified space »
(Trans. AMS 74, 1953) is the fibrewise analogue of pp. 30–31 of the same notebook.
-/

namespace Quillen.Notebook1968_13

open Set Topology

/-- A family of supports on `X` (Quillen, 1968-13, p. 64): closed sets, containing `∅`, stable
under finite unions and under closed subsets. -/
structure SupportFamily (X : Type*) [TopologicalSpace X] where
  /-- The members of the family. -/
  sets : Set (Set X)
  isClosed : ∀ Z ∈ sets, IsClosed Z
  empty_mem : ∅ ∈ sets
  union_mem : ∀ Z ∈ sets, ∀ Z' ∈ sets, Z ∪ Z' ∈ sets
  mem_of_subset : ∀ Z ∈ sets, ∀ Z', IsClosed Z' → Z' ⊆ Z → Z' ∈ sets

variable {X : Type*} [TopologicalSpace X]

/-- The space `X ∪_Φ {∞}`: the points of `X` and one point `∞` (`none`). -/
def Extension (_Φ : SupportFamily X) : Type _ := Option X

namespace Extension

variable {Φ : SupportFamily X}

/-- The inclusion of `X`. -/
def ι (Φ : SupportFamily X) : X → Extension Φ := Option.some

/-- The point at infinity. -/
def infty (Φ : SupportFamily X) : Extension Φ := (none : Option X)

theorem ι_injective : Function.Injective (ι Φ) := Option.some_injective X

theorem ι_ne_infty (x : X) : ι Φ x ≠ infty Φ := Option.some_ne_none x

/-- Every point is `ι x` or `∞`. -/
theorem cases (p : Extension Φ) : p = infty Φ ∨ ∃ x, p = ι Φ x := by
  rcases (p : Option X) with _ | x
  · exact Or.inl rfl
  · exact Or.inr ⟨x, rfl⟩

/-- The topology: `U` is open when its trace on `X` is open and, if it contains `∞`, it contains
the complement of a member of `Φ`. -/
instance : TopologicalSpace (Extension Φ) where
  IsOpen U := IsOpen (ι Φ ⁻¹' U) ∧ (infty Φ ∈ U → ∃ Z ∈ Φ.sets, Zᶜ ⊆ ι Φ ⁻¹' U)
  isOpen_univ := ⟨isOpen_univ, fun _ => ⟨∅, Φ.empty_mem, by simp⟩⟩
  isOpen_inter s t hs ht := by
    refine ⟨hs.1.inter ht.1, fun h => ?_⟩
    obtain ⟨Z, hZ, hZs⟩ := hs.2 h.1
    obtain ⟨Z', hZ', hZt⟩ := ht.2 h.2
    refine ⟨Z ∪ Z', Φ.union_mem _ hZ _ hZ', fun x hx => ?_⟩
    rw [compl_union] at hx
    exact ⟨hZs hx.1, hZt hx.2⟩
  isOpen_sUnion S hS := by
    refine ⟨?_, fun h => ?_⟩
    · rw [preimage_sUnion]
      exact isOpen_biUnion fun t ht => (hS t ht).1
    · obtain ⟨t, ht, hinf⟩ := mem_sUnion.1 h
      obtain ⟨Z, hZ, hZt⟩ := (hS t ht).2 hinf
      exact ⟨Z, hZ, hZt.trans (preimage_mono (subset_sUnion_of_mem ht))⟩

theorem isOpen_iff {U : Set (Extension Φ)} :
    IsOpen U ↔ IsOpen (ι Φ ⁻¹' U) ∧ (infty Φ ∈ U → ∃ Z ∈ Φ.sets, Zᶜ ⊆ ι Φ ⁻¹' U) :=
  Iff.rfl

theorem isOpen_image_ι {V : Set X} (hV : IsOpen V) : IsOpen (ι Φ '' V) := by
  refine ⟨by rwa [ι_injective.preimage_image], fun h => ?_⟩
  obtain ⟨x, _, hx⟩ := h
  exact absurd hx (ι_ne_infty x)

/-- `X` is an open subspace of `X ∪_Φ {∞}`. -/
theorem isOpenEmbedding_ι : IsOpenEmbedding (ι Φ) :=
  .of_continuous_injective_isOpenMap (continuous_def.2 fun _ hU => hU.1) ι_injective
    fun _ hV => isOpen_image_ι hV

/-- `{∞}` is closed. -/
theorem isClosed_infty : IsClosed ({infty Φ} : Set (Extension Φ)) := by
  refine ⟨⟨?_, fun h => absurd rfl h⟩⟩
  have : ι Φ ⁻¹' ({infty Φ} : Set (Extension Φ))ᶜ = univ := by
    ext x; simp [ι_ne_infty]
  rw [this]; exact isOpen_univ

/-- For `Z ∈ Φ`, the set `(X ∖ Z) ∪ {∞}` is open. -/
theorem isOpen_compl_image {Z : Set X} (hZ : Z ∈ Φ.sets) :
    IsOpen (ι Φ '' Zᶜ ∪ {infty Φ}) := by
  refine ⟨?_, fun _ => ⟨Z, hZ, fun x hx => Or.inl ⟨x, hx, rfl⟩⟩⟩
  have : ι Φ ⁻¹' (ι Φ '' Zᶜ ∪ {infty Φ}) = Zᶜ := by
    ext x; simp [ι_injective.eq_iff, ι_ne_infty]
  rw [this]; exact (Φ.isClosed Z hZ).isOpen_compl

/-- The criterion of p. 64: for `X` Hausdorff, `X ∪_Φ {∞}` is Hausdorff iff every point of `X` has
a neighbourhood in `Φ`. -/
theorem t2Space_iff [T2Space X] : T2Space (Extension Φ) ↔ ∀ x : X, ∃ Z ∈ Φ.sets, Z ∈ 𝓝 x := by
  constructor
  · intro _ x
    obtain ⟨U, V, hU, hV, hxU, hinfV, hUV⟩ := t2_separation (ι_ne_infty (Φ := Φ) x)
    obtain ⟨Z, hZ, hZV⟩ := hV.2 hinfV
    refine ⟨Z, hZ, Filter.mem_of_superset (hU.1.mem_nhds hxU) fun y hy => ?_⟩
    by_contra hyZ
    exact hUV.ne_of_mem hy (hZV hyZ) rfl
  · intro h
    refine ⟨fun p q hpq => ?_⟩
    have sep_infty : ∀ x : X, ∃ u v : Set (Extension Φ), IsOpen u ∧ IsOpen v ∧ ι Φ x ∈ u ∧
        infty Φ ∈ v ∧ Disjoint u v := by
      intro x
      obtain ⟨Z, hZ, hZx⟩ := h x
      refine ⟨ι Φ '' interior Z, ι Φ '' Zᶜ ∪ {infty Φ}, isOpen_image_ι isOpen_interior,
        isOpen_compl_image hZ, ⟨x, mem_interior_iff_mem_nhds.2 hZx, rfl⟩, Or.inr rfl, ?_⟩
      rw [Set.disjoint_left]
      rintro _ ⟨y, hy, rfl⟩ (⟨y', hy', hyy'⟩ | hinf)
      · exact hy' (ι_injective hyy' ▸ interior_subset hy)
      · exact ι_ne_infty y hinf
    rcases cases p with rfl | ⟨x, rfl⟩ <;> rcases cases q with rfl | ⟨y, rfl⟩
    · exact absurd rfl hpq
    · obtain ⟨u, v, hu, hv, hyu, hinf, huv⟩ := sep_infty y
      exact ⟨v, u, hv, hu, hinf, hyu, huv.symm⟩
    · exact sep_infty x
    · have hxy : x ≠ y := fun h' => hpq (h' ▸ rfl)
      obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hxy
      exact ⟨ι Φ '' u, ι Φ '' v, isOpen_image_ι hu, isOpen_image_ι hv, ⟨x, hxu, rfl⟩,
        ⟨y, hyv, rfl⟩, huv.image (ι_injective.injOn (s := univ)) (subset_univ _) (subset_univ _)⟩

end Extension

section SpecialCases

open Extension

/-- The family of closed compact sets. -/
def compactSupports (X : Type*) [TopologicalSpace X] : SupportFamily X where
  sets := {Z | IsClosed Z ∧ IsCompact Z}
  isClosed _ h := h.1
  empty_mem := ⟨isClosed_empty, isCompact_empty⟩
  union_mem _ h _ h' := ⟨h.1.union h'.1, h.2.union h'.2⟩
  mem_of_subset _ h _ hc hsub := ⟨hc, h.2.of_isClosed_subset hc hsub⟩

/-- For `Φ` the closed compact sets, `X ∪_Φ {∞}` is the one-point compactification (p. 65): the
identity of `Option X` is a homeomorphism onto `OnePoint X`. -/
def homeomorphOnePoint : Extension (compactSupports X) ≃ₜ OnePoint X where
  toEquiv := Equiv.refl _
  continuous_toFun := by
    refine continuous_def.2 fun U hU => ?_
    rw [OnePoint.isOpen_def] at hU
    refine ⟨hU.2, fun h => ⟨_, ⟨hU.2.isClosed_compl, hU.1 h⟩, ?_⟩⟩
    rw [compl_compl]; exact le_rfl
  continuous_invFun := by
    refine continuous_def.2 fun U hU => ?_
    rw [OnePoint.isOpen_def]
    refine ⟨fun h => ?_, hU.1⟩
    obtain ⟨Z, hZ, hZU⟩ := hU.2 h
    exact hZ.2.of_isClosed_subset hU.1.isClosed_compl (compl_subset_comm.1 hZU)

/-- The family of all closed sets. -/
def closedSupports (X : Type*) [TopologicalSpace X] : SupportFamily X where
  sets := {Z | IsClosed Z}
  isClosed _ h := h
  empty_mem := isClosed_empty
  union_mem _ h _ h' := h.union h'
  mem_of_subset _ _ _ hc _ := hc

/-- For `Φ` the closed sets, `∞` is an isolated point (p. 65: `X ∪_Φ {∞} = X ⊔ pt`). -/
theorem isOpen_infty_closedSupports : IsOpen ({infty (closedSupports X)} : Set (Extension _)) := by
  refine ⟨?_, fun _ => ⟨univ, isClosed_univ, by simp⟩⟩
  have : ι (closedSupports X) ⁻¹' {infty (closedSupports X)} = ∅ := by
    ext x; simp [ι_ne_infty]
  rw [this]; exact isOpen_empty

end SpecialCases

section Smash

open Extension

variable {Y : Type*} [TopologicalSpace Y]

/-- The inclusion `X × Y → X⁺ × Y`. -/
def j : X × Y → OnePoint X × Y := Prod.map (↑) id

theorem isOpenEmbedding_j : IsOpenEmbedding (j : X × Y → OnePoint X × Y) :=
  OnePoint.isOpenEmbedding_coe.prodMap .id

/-- If `f` is inducing, `T` is closed and `f '' T` lies in a closed set contained in the range of
`f`, then `f '' T` is closed. -/
theorem isClosed_image_of_subset {Z W : Type*} [TopologicalSpace Z] [TopologicalSpace W]
    {f : Z → W} (hf : IsInducing f) {T : Set Z} (hT : IsClosed T) {K : Set W} (hK : IsClosed K)
    (hTK : f '' T ⊆ K) (hKr : K ⊆ range f) : IsClosed (f '' T) := by
  refine closure_subset_iff_isClosed.1 fun z hz => ?_
  obtain ⟨w, rfl⟩ := hKr (closure_minimal hTK hK hz)
  have : w ∈ closure T := by
    rw [hf.closure_eq_preimage_closure_image]; exact hz
  exact ⟨w, hT.closure_eq ▸ this, rfl⟩

/-- The family `Ψ` of the lemma of p. 68: the closed `A ⊆ X × Y` that lie in `X × F` for some
`F ∈ Φ` and are closed in `X⁺ × Y`. -/
def smashSupports (Φ : SupportFamily Y) : SupportFamily (X × Y) where
  sets := {A | IsClosed A ∧ (∃ F ∈ Φ.sets, A ⊆ univ ×ˢ F) ∧
    IsClosed ((j : X × Y → OnePoint X × Y) '' A)}
  isClosed _ h := h.1
  empty_mem := ⟨isClosed_empty, ⟨∅, Φ.empty_mem, empty_subset _⟩, by simp⟩
  union_mem A hA B hB := by
    obtain ⟨hAc, ⟨F, hF, hAF⟩, hjA⟩ := hA
    obtain ⟨hBc, ⟨G, hG, hBG⟩, hjB⟩ := hB
    refine ⟨hAc.union hBc, ⟨F ∪ G, Φ.union_mem _ hF _ hG, ?_⟩, ?_⟩
    · exact union_subset (hAF.trans (prod_mono le_rfl subset_union_left))
        (hBG.trans (prod_mono le_rfl subset_union_right))
    · rw [image_union]; exact hjA.union hjB
  mem_of_subset A hA B hB hBA := by
    obtain ⟨_, ⟨F, hF, hAF⟩, hjA⟩ := hA
    refine ⟨hB, ⟨F, hF, hBA.trans hAF⟩, ?_⟩
    exact isClosed_image_of_subset isOpenEmbedding_j.isInducing hB hjA (image_mono hBA)
      (image_subset_range _ _)

variable (X) in
/-- The map `X⁺ × (Y ∪_Φ {∞}) → (X × Y) ∪_Ψ {∞}`: the identity on `X × Y`, the wedge
`X⁺ × {∞} ∪ {∞} × (Y ∪_Φ {∞})` to `∞`. -/
def smashMap (Φ : SupportFamily Y) :
    OnePoint X × Extension Φ → Extension (smashSupports (X := X) Φ)
  | (some x, some y) => ι _ (x, y)
  | _ => infty _

/-- `X × Y → X⁺ × (Y ∪_Φ {∞})`. -/
def e (Φ : SupportFamily Y) : X × Y → OnePoint X × Extension Φ := fun p => (p.1, ι Φ p.2)

theorem isOpenEmbedding_e (Φ : SupportFamily Y) : IsOpenEmbedding (e (X := X) Φ) :=
  OnePoint.isOpenEmbedding_coe.prodMap isOpenEmbedding_ι

@[simp] theorem smashMap_e (Φ : SupportFamily Y) (p : X × Y) :
    smashMap X Φ (e Φ p) = ι _ p := rfl

theorem smashMap_eq_infty_iff (Φ : SupportFamily Y) (z : OnePoint X × Extension Φ) :
    smashMap X Φ z = infty _ ↔ z ∉ range (e (X := X) Φ) := by
  rcases z with ⟨_ | x, _ | y⟩
  · exact ⟨fun _ ⟨p, hp⟩ => OnePoint.coe_ne_infty p.1 (congrArg Prod.fst hp), fun _ => rfl⟩
  · exact ⟨fun _ ⟨p, hp⟩ => OnePoint.coe_ne_infty p.1 (congrArg Prod.fst hp), fun _ => rfl⟩
  · exact ⟨fun _ ⟨p, hp⟩ => ι_ne_infty p.2 (congrArg Prod.snd hp), fun _ => rfl⟩
  · exact ⟨fun h => absurd h (ι_ne_infty _), fun h => absurd ⟨(x, y), rfl⟩ h⟩

/-- The preimage of a set not containing `∞` is the image of its trace under `e`. -/
theorem preimage_smashMap_of_notMem (Φ : SupportFamily Y) {U : Set (Extension (smashSupports Φ))}
    (h : infty _ ∉ U) : smashMap X Φ ⁻¹' U = e Φ '' (ι _ ⁻¹' U) := by
  ext z
  constructor
  · intro hz
    by_cases hr : z ∈ range (e (X := X) Φ)
    · obtain ⟨p, rfl⟩ := hr; exact ⟨p, hz, rfl⟩
    · exact absurd ((smashMap_eq_infty_iff Φ z).2 hr ▸ hz) h
  · rintro ⟨p, hp, rfl⟩; exact hp

/-- The preimage of a set containing `∞` is the complement of the image under `e` of the
complement of its trace. -/
theorem preimage_smashMap_of_mem (Φ : SupportFamily Y) {U : Set (Extension (smashSupports Φ))}
    (h : infty _ ∈ U) : smashMap X Φ ⁻¹' U = (e Φ '' (ι _ ⁻¹' U)ᶜ)ᶜ := by
  ext z
  simp only [mem_preimage, mem_compl_iff, mem_image, not_exists, not_and]
  constructor
  · rintro hz p hp rfl; exact hp hz
  · intro hz
    by_cases hr : z ∈ range (e (X := X) Φ)
    · obtain ⟨p, rfl⟩ := hr
      by_contra hp; exact hz p hp rfl
    · rw [(smashMap_eq_infty_iff Φ z).2 hr]; exact h

/-- The heart of the lemma: a set `C ⊆ X × Y` has a closed image in `X⁺ × (Y ∪_Φ {∞})` iff it
belongs to `Ψ`. -/
theorem isClosed_image_e_iff (Φ : SupportFamily Y) {C : Set (X × Y)} :
    IsClosed (e Φ '' C) ↔ C ∈ (smashSupports (X := X) Φ).sets := by
  -- `g = id × ι : X⁺ × Y → X⁺ × (Y ∪_Φ {∞})`, and `e = g ∘ j`.
  let g : OnePoint X × Y → OnePoint X × Extension Φ := Prod.map id (ι Φ)
  have hg : IsOpenEmbedding g := IsOpenEmbedding.id.prodMap isOpenEmbedding_ι
  have hge : e Φ '' C = g '' (j '' C) := by rw [image_image]; rfl
  constructor
  · intro hC
    refine ⟨?_, ?_, ?_⟩
    · have : C = e Φ ⁻¹' (e Φ '' C) := ((isOpenEmbedding_e Φ).injective.preimage_image C).symm
      rw [this]; exact hC.preimage (isOpenEmbedding_e Φ).continuous
    · -- the tube lemma around the compact `X⁺ × {∞}`
      obtain ⟨u, v, -, hv, hu, hinf, huv⟩ := generalized_tube_lemma (isCompact_univ :
        IsCompact (univ : Set (OnePoint X))) (isCompact_singleton (x := infty Φ))
        hC.isOpen_compl (by
          rintro ⟨p, q⟩ ⟨-, hq⟩ ⟨c, -, hc⟩
          rw [mem_singleton_iff] at hq
          subst hq
          exact ι_ne_infty c.2 (congrArg Prod.snd hc))
      obtain ⟨F, hF, hFv⟩ := hv.2 (hinf rfl)
      refine ⟨F, hF, fun c hc => ⟨trivial, ?_⟩⟩
      by_contra hcF
      exact huv (show e Φ c ∈ u ×ˢ v from ⟨hu (mem_univ _), hFv hcF⟩) ⟨c, hc, rfl⟩
    · have : j '' C = g ⁻¹' (e Φ '' C) := by
        rw [hge, hg.injective.preimage_image]
      rw [this]; exact hC.preimage hg.continuous
  · rintro ⟨-, ⟨F, hF, hCF⟩, hjC⟩
    rw [hge]
    refine isClosed_image_of_subset hg.isInducing hjC (K := univ ×ˢ (ι Φ '' F)) ?_ ?_ ?_
    · refine isClosed_univ.prod ⟨?_⟩
      have : (ι Φ '' F)ᶜ = ι Φ '' Fᶜ ∪ {infty Φ} := by
        ext p
        rcases cases p with rfl | ⟨y, rfl⟩
        · simp [ι_ne_infty]
        · simp [ι_injective.eq_iff, ι_ne_infty]
      rw [this]; exact isOpen_compl_image hF
    · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨trivial, c.2, (hCF hc).2, rfl⟩
    · rintro ⟨p, _⟩ ⟨-, y, -, rfl⟩
      exact ⟨(p, y), rfl⟩

/-- **Quillen's lemma (1968-13, pp. 68–69).** The map `X⁺ × (Y ∪_Φ {∞}) → (X × Y) ∪_Ψ {∞}`
collapsing the wedge is a quotient map: `(X × Y) ∪_Ψ {∞}` is the smash product
`X⁺ ∧ (Y ∪_Φ {∞})` with its quotient topology. -/
theorem isQuotientMap_smashMap (Φ : SupportFamily Y) : IsQuotientMap (smashMap X Φ) := by
  have key : ∀ U : Set (Extension (smashSupports (X := X) Φ)),
      IsOpen U ↔ IsOpen (smashMap X Φ ⁻¹' U) := by
    intro U
    by_cases h : infty _ ∈ U
    · rw [preimage_smashMap_of_mem Φ h, isOpen_compl_iff, isClosed_image_e_iff, isOpen_iff]
      constructor
      · rintro ⟨hU, hU'⟩
        obtain ⟨A, hA, hAU⟩ := hU' h
        exact (smashSupports Φ).mem_of_subset A hA _ hU.isClosed_compl
          (compl_subset_comm.1 hAU)
      · intro hC
        exact ⟨by simpa using ((smashSupports Φ).isClosed _ hC).isOpen_compl,
          fun _ => ⟨_, hC, by rw [compl_compl]⟩⟩
    · rw [preimage_smashMap_of_notMem Φ h, isOpen_iff, (isOpenEmbedding_e Φ).isOpen_iff_image_isOpen]
      exact ⟨fun hU => hU.1, fun hU => ⟨hU, fun h' => absurd h' h⟩⟩
  refine isQuotientMap_iff_isClosed.2 ⟨?_, fun s => ?_⟩
  swap
  · rw [← isOpen_compl_iff, key, preimage_compl, isOpen_compl_iff]
  · intro p
    rcases cases p with rfl | ⟨⟨x, y⟩, rfl⟩
    · exact ⟨(none, infty Φ), rfl⟩
    · exact ⟨e Φ (x, y), rfl⟩

end Smash

end Quillen.Notebook1968_13
