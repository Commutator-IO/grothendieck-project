import Mathlib

/-!
# Buffalo, topos theory, part 5d: corrections, `Setᵒᵖ` and Boolean algebras (10 July 1973)

Entries of `docs/buffalo-topos/index.tex` lines 812–830 (video `4gynb9uTEE4`, 3:35:28–4:11:21):
the lecturer's corrections to the previous lecture (strict cogeneration, two-step constructions),
the example of `Setᵒᵖ`, complete atomic Boolean algebras, and the reduction to `Δ_π`. The status of
each entry is in `docs/buffalo-topos/lean/Part05.json`.

One entry was found imprecise: 4gynb9uTEE4-13448 (« `Setᵒᵖ` admits a strict generator, the
two-element set »). In the course's sense of strict generation (0:06:26, every object a limit of a
diagram of copies of the given object) it fails: limits of diagrams of copies of `2` in sets are
closed under the ternary `xor`, so no such limit has three elements (`no_limit_of_bools`). The
two-element set is a strict cogenerator of `Set` only in the sense of SGA 4 (every set is an
equalizer of two maps between powers of `2`).
-/

universe u

open CategoryTheory Limits

namespace Buffalo.Topos.Part05

noncomputable section

/-! ## A group structure is not determined by its power maps -/

/-- The map of the Klein group sending `0` to `0` and everything else to `(1, 0)`. -/
def kleinMap (x : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 := if x = 0 then 0 else (1, 0)

/-- 4gynb9uTEE4-13056 (3:37:36) [cex, partial] « A group structure is not determined by the maps
`x ↦ xⁿ` »: `kleinMap` commutes with all the power maps `x ↦ n • x`... -/
theorem kleinMap_zsmul (n : ℤ) (x : ZMod 2 × ZMod 2) : kleinMap (n • x) = n • kleinMap x := by
  rw [← Int.cast_smul_eq_zsmul (ZMod 2), ← Int.cast_smul_eq_zsmul (ZMod 2)]
  generalize (n : ZMod 2) = a
  revert a x
  decide

/-- ... but is not a homomorphism. So `{ℤ}` (whose endomorphisms are the power maps) is not
strictly generating in groups (4gynb9uTEE4-13185). -/
theorem kleinMap_not_hom : kleinMap ((1, 0) + (0, 1)) ≠ kleinMap (1, 0) + kleinMap (0, 1) := by
  decide

/-! ## `Setᵒᵖ`: the two-element set is not strictly cogenerating in the course's sense -/

/-- The ternary `xor`. -/
def xor3 (a b c : Bool) : Bool := xor (xor a b) c

/-- Every map `Bool → Bool` commutes with the ternary `xor`. -/
theorem xor3_comm_map : ∀ (g : Bool → Bool) (a b c : Bool),
    g (xor3 a b c) = xor3 (g a) (g b) (g c) := by decide

theorem xor3_eq_left : ∀ a b c : Bool, xor3 a b c = a → b = c := by decide
theorem xor3_eq_mid : ∀ a b c : Bool, xor3 a b c = b → a = c := by decide
theorem xor3_eq_right : ∀ a b c : Bool, xor3 a b c = c → a = b := by decide

/-- The sections of a diagram of copies of `Bool` are closed under the ternary `xor`. -/
def sectionXor3 {K : Type} [SmallCategory K] (F : K ⥤ Type) (e : ∀ k, F.obj k ≃ Bool)
    (s₁ s₂ s₃ : F.sections) : F.sections :=
  ⟨fun k => (e k).symm (xor3 (e k (s₁.1 k)) (e k (s₂.1 k)) (e k (s₃.1 k))), by
    intro j k f
    have hg := xor3_comm_map (fun b => e k (F.map f ((e j).symm b)))
      (e j (s₁.1 j)) (e j (s₂.1 j)) (e j (s₃.1 j))
    simp only [Equiv.symm_apply_apply, s₁.2 f, s₂.2 f, s₃.2 f] at hg
    dsimp only
    rw [← hg, Equiv.symm_apply_apply]⟩

/-- 4gynb9uTEE4-13448 (3:44:08) [ex, imprecise] No limit of a diagram of copies of the two-element
set has exactly three elements: so `3` is not a limit of copies of `2`, and `{2}` is not strictly
cogenerating in `Set` in the sense of 0:06:26 (nor is it codense). -/
theorem no_limit_of_bools {K : Type} [SmallCategory K] (F : K ⥤ Type) (e : ∀ k, F.obj k ≃ Bool)
    {c : Cone F} (hc : IsLimit c) : IsEmpty (c.pt ≃ Fin 3) := by
  refine ⟨fun E => ?_⟩
  let φ : Fin 3 ≃ F.sections := E.symm.trans (Types.isLimitEquivSections hc)
  let t := sectionXor3 F e (φ 0) (φ 1) (φ 2)
  obtain ⟨i, hi⟩ := φ.surjective t
  have key : ∀ k, xor3 (e k ((φ 0).1 k)) (e k ((φ 1).1 k)) (e k ((φ 2).1 k)) = e k ((φ i).1 k) :=
    fun k => by rw [hi]; simp [t, sectionXor3]
  have sec : ∀ a b : Fin 3, (∀ k, e k ((φ a).1 k) = e k ((φ b).1 k)) → a = b := by
    intro a b h
    exact φ.injective (Subtype.ext (funext fun k => (e k).injective (h k)))
  fin_cases i
  · exact absurd (sec 1 2 fun k => xor3_eq_left _ _ _ (key k)) (by decide)
  · exact absurd (sec 0 2 fun k => xor3_eq_mid _ _ _ (key k)) (by decide)
  · exact absurd (sec 0 1 fun k => xor3_eq_right _ _ _ (key k)) (by decide)

/-! ## `Setᵒᵖ` and complete atomic Boolean algebras -/

/-- 4gynb9uTEE4-13577 (3:46:17) [prop, partial] `X ↦ 𝒫(X)` is fully faithful from `Setᵒᵖ` to
complete Boolean algebras: the complete lattice homomorphisms `𝒫(Y) → 𝒫(X)` are exactly the
inverse images of the maps `X → Y`. -/
theorem setPreimage_bijective (X Y : Type u) :
    Function.Bijective (fun f : X → Y => CompleteLatticeHom.setPreimage f) := by
  constructor
  · intro f g h
    funext x
    have h' : f ⁻¹' {f x} = g ⁻¹' {f x} :=
      congrArg (fun φ : CompleteLatticeHom (Set Y) (Set X) => φ {f x}) h
    have : x ∈ g ⁻¹' {f x} := by rw [← h']; exact rfl
    exact (this : g x = f x).symm
  · intro φ
    have hcover : ∀ x : X, ∃ y, x ∈ φ {y} := by
      intro x
      have h1 : φ (⨆ y : Y, ({y} : Set Y)) = ⨆ y, φ {y} := map_iSup φ _
      rw [Set.iSup_eq_iUnion, Set.iSup_eq_iUnion, Set.iUnion_of_singleton] at h1
      have hx : x ∈ φ Set.univ := by
        rw [show (Set.univ : Set Y) = ⊤ from rfl, map_top]; trivial
      rw [h1] at hx
      simpa using hx
    choose f hf using hcover
    refine ⟨f, ?_⟩
    ext A x
    simp only [CompleteLatticeHom.setPreimage_apply, Set.mem_preimage]
    constructor
    · intro hA
      exact OrderHomClass.mono φ (Set.singleton_subset_iff.2 hA) (hf x)
    · intro hx
      by_contra hA
      have : x ∈ φ Aᶜ := OrderHomClass.mono φ (Set.singleton_subset_iff.2 hA) (hf x)
      rw [map_compl] at this
      exact this hx

/-- 4gynb9uTEE4-14825 (4:07:05) [prop] Every complete Boolean algebra `B` falls under the theory of
`π`-complete Boolean algebras for `π = #B`: every supremum is one over a family of at most `#B`
elements. -/
theorem iSup_eq_sSup_small {B : Type u} [CompleteBooleanAlgebra B] {ι : Type*} (f : ι → B) :
    ∃ S : Set B, Cardinal.mk S ≤ Cardinal.mk B ∧ iSup f = sSup S :=
  ⟨Set.range f, Cardinal.mk_set_le _, sSup_range.symm⟩

end

end Buffalo.Topos.Part05
