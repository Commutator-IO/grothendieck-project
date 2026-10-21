import Mathlib

/-!
# Folder 150, page 19: without `Xᵢ ∩ Y = f(Ẋᵢ)`, the reconstruction is not faithful

Page 19 of folder 150 (transcription `transcripts/150/batch-01.fr.tex`) states that the systems
`(X, Y, (Xᵢ), T)`, `T` a conic neighbourhood of `Y` in `X` compatible with the closed `Xᵢ`,
are equivalent — morphisms the isomorphisms — to the systems `(X*, Ẋ, (Xᵢ*), Y, f : Ẋ → Y)`,
where `X* = X ∖ T°`, `Ẋ = Ṫ`, `Xᵢ* = Xᵢ ∩ X*` and `f` is `t ↦ 0 · t`. The modernised reading
`transcripts/150/150.modern.tex` (footnote to the Proposition of page 19) objects that the trace
`Xᵢ ∩ Y` is not recovered from the right-hand data, and gives the edition's counterexample
on `[0, 1]`: `Y = {0}`, `T = [0, 1/2]`, and `X₁ = {0}`, `X₁ = ∅`. The reading therefore puts into
« strictement compatible » the condition `Xᵢ ∩ Y = f(Ẋᵢ)`, `Ẋᵢ = Xᵢ ∩ Ṫ` (the conic part
`Xᵢ ∩ T` is *strict*, the circled `T' ∩ Y = 0 · Ṫ'` of page 16).

What is modelled. Everything is the concrete example, inside `ℝ`: `X = [0, 1]`, `Y = {0}`,
`T = [0, 1/2]` with the action `(λ, t) ↦ λ t` of `I = [0, 1]`, `Ṫ = {1/2}`, `X* = [1/2, 1]`,
and the collar `E = [1/2, 3/4] ≃ Ṫ × [0, 1]`, `(1/2, s) ↦ 1/2 + s/4`. A part `C ⊂ T` is conic
when `C = I · (C ∩ Ṫ) ∪ (C ∩ Y)` (the NB of page 15, which contains stability under `I`).
* `isConic_T`, `T_eq_half_smul`: `T` is conic, and strict (`T = ½ · X`);
* `compatible_not_determined` (the edition's counterexample): `{0}` and `∅` are both compatible
  with `T` and with the collar, have the same trace on `X*`, and `{0}` is nonempty — so no
  isomorphism of systems relates them, while their right-hand data coincide;
* `not_strictlyCompatible_singleton_zero`: `{0}` fails `X₁ ∩ Y = f(Ẋ₁)`;
* `eq_of_strictlyCompatible`: with that condition, `X₁` is determined by `X₁ ∩ X*`.

Not formalised: the categories of page 19 and the functor `X = X* ⊔_Ẋ 𝒞(f)` for general
spaces, transversality and equisingularity; only this example is treated.
-/

open Set

namespace Grothendieck.Folder150

/-- The space `X = [0, 1]`. -/
def X : Set ℝ := Icc 0 1

/-- The closed part `Y = {0}`. -/
def Y : Set ℝ := {0}

/-- The conic neighbourhood `T = [0, 1/2]` of `Y`, for the action `(λ, t) ↦ λ t`. -/
def T : Set ℝ := Icc 0 (1 / 2)

/-- Its boundary `Ṫ = {1/2}`. -/
def Tdot : Set ℝ := {1 / 2}

/-- `X* = X ∖ T° = [1/2, 1]`. -/
def Xstar : Set ℝ := Icc (1 / 2) 1

/-- The cone `I · S = {λ s | λ ∈ [0, 1], s ∈ S}`. -/
def cone (S : Set ℝ) : Set ℝ := (fun p : ℝ × ℝ => p.1 * p.2) '' (Icc 0 1 ×ˢ S)

/-- `C ⊂ T` is conic: `C = I · (C ∩ Ṫ) ∪ (C ∩ Y)` (page 15). -/
def IsConic (C : Set ℝ) : Prop := C ⊆ T ∧ C = cone (C ∩ Tdot) ∪ (C ∩ Y)

/-- `T` is compatible with the closed part `X₁ ⊂ X`: `X₁ ∩ T` is conic. -/
def IsCompatible (X₁ : Set ℝ) : Prop := IsClosed X₁ ∧ X₁ ⊆ X ∧ IsConic (X₁ ∩ T)

/-- `X₁` is compatible with the collar `E = [1/2, 3/4] ≃ Ṫ × [0, 1]`: `X₁ ∩ E = X₁₀ × [0, 1]`
with `X₁₀ = X₁ ∩ Ṫ`. -/
def IsCollarCompatible (X₁ : Set ℝ) : Prop :=
  X₁ ∩ Icc (1 / 2) (3 / 4) = (fun p : ℝ × ℝ => p.1 + p.2 / 4) '' ((X₁ ∩ Tdot) ×ˢ Icc 0 1)

/-- Strict compatibility as the reading defines it: compatible, compatible with the collar,
and `X₁ ∩ Y = f(Ẋ₁)` with `f t = 0 · t` and `Ẋ₁ = X₁ ∩ Ṫ`. -/
def IsStrictlyCompatible (X₁ : Set ℝ) : Prop :=
  IsCompatible X₁ ∧ IsCollarCompatible X₁ ∧ X₁ ∩ Y = (fun t : ℝ => 0 * t) '' (X₁ ∩ Tdot)

lemma cone_half : cone Tdot = T := by
  ext x
  simp only [cone, Tdot, T, mem_image, mem_prod, mem_Icc, mem_singleton_iff, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨h0, h1⟩, rfl⟩, rfl⟩
    constructor <;> linarith
  · rintro ⟨h0, h1⟩
    exact ⟨2 * x, 1 / 2, ⟨⟨by linarith, by linarith⟩, rfl⟩, by ring⟩

theorem isConic_T : IsConic T := ⟨subset_rfl, by
  rw [(inter_eq_right.2 (by norm_num [Tdot, T]) : T ∩ Tdot = Tdot), cone_half,
    union_eq_left.2 inter_subset_left]⟩

/-- `T` is strict: `T = ½ · X`, with `X = [0, 1]` itself conic for the same action. -/
theorem T_eq_half_smul : T = (fun t => 1 / 2 * t) '' X := by
  ext x
  simp only [T, X, mem_image, mem_Icc]
  exact ⟨fun ⟨h0, h1⟩ => ⟨2 * x, ⟨by linarith, by linarith⟩, by ring⟩,
    by rintro ⟨t, ⟨h0, h1⟩, rfl⟩; constructor <;> linarith⟩

/-- A conic part of `T` is `T` if it contains `1/2`, and lies in `Y` otherwise. -/
lemma IsConic.cases {C : Set ℝ} (h : IsConic C) :
    ((1 / 2 : ℝ) ∈ C → C = T) ∧ ((1 / 2 : ℝ) ∉ C → C ⊆ Y) := by
  refine ⟨fun hc => h.1.antisymm ?_, fun hc => ?_⟩
  · rw [h.2, (inter_eq_right.2 (singleton_subset_iff.2 hc) : C ∩ Tdot = Tdot), cone_half]
    exact subset_union_left
  · rw [h.2, Tdot, inter_singleton_eq_empty.2 hc]
    simp [cone]

/-- The edition's counterexample (reading, footnote to page 19): `X₁ = {0}` and `X₁ = ∅` are
both compatible with `T` and with the collar, and have the same trace on `X*` — the same
right-hand data `(X*, Ṫ, X₁*, Y, f)` — but `{0}` is nonempty and `∅` is not, so no
isomorphism of systems takes one to the other. -/
theorem compatible_not_determined :
    IsCompatible {0} ∧ IsCompatible ∅ ∧ IsCollarCompatible {0} ∧ IsCollarCompatible ∅ ∧
      ({0} : Set ℝ) ∩ Xstar = ∅ ∩ Xstar ∧ ({0} : Set ℝ).Nonempty := by
  have h0 : ({0} : Set ℝ) ∩ Tdot = ∅ := by norm_num [Tdot]
  refine ⟨⟨isClosed_singleton, by norm_num [X], ?_, ?_⟩, ⟨isClosed_empty, empty_subset _,
    by simp [IsConic, cone]⟩, ?_, by simp [IsCollarCompatible], ?_, singleton_nonempty 0⟩
  · norm_num [T]
  · rw [show ({0} : Set ℝ) ∩ T = {0} by norm_num [T], h0]
    simp [cone, Y]
  · rw [IsCollarCompatible, h0]
    norm_num
  · norm_num [Xstar]

/-- `{0}` is not strictly compatible: `{0} ∩ Y = {0}`, while `Ẋ₁ = ∅`. -/
theorem not_strictlyCompatible_singleton_zero : ¬ IsStrictlyCompatible {0} := by
  rintro ⟨-, -, h⟩
  rw [show ({0} : Set ℝ) ∩ Tdot = ∅ by norm_num [Tdot], image_empty] at h
  simp [Y] at h

open Classical in
/-- Under strict compatibility, `X₁ ∩ T` is `T` or `∅` according as `1/2 ∈ X₁`. -/
lemma IsStrictlyCompatible.inter_T {X₁ : Set ℝ} (h : IsStrictlyCompatible X₁) :
    X₁ ∩ T = if (1 / 2 : ℝ) ∈ X₁ then T else ∅ := by
  have hc := h.1.2.2.cases
  split_ifs with h2
  · exact hc.1 ⟨h2, by norm_num [T]⟩
  · have hY : X₁ ∩ Y = ∅ := by rw [h.2.2, Tdot, inter_singleton_eq_empty.2 h2, image_empty]
    exact subset_empty_iff.1 fun x hx => hY ▸ ⟨hx.1, hc.2 (fun h' => h2 h'.1) hx⟩

/-- With `X₁ ∩ Y = f(Ẋ₁)`, a strictly compatible `X₁` is determined by its trace on `X*`. -/
theorem eq_of_strictlyCompatible {X₁ X₂ : Set ℝ} (h₁ : IsStrictlyCompatible X₁)
    (h₂ : IsStrictlyCompatible X₂) (h : X₁ ∩ Xstar = X₂ ∩ Xstar) : X₁ = X₂ := by
  have split : ∀ Z : Set ℝ, Z ⊆ X → Z = Z ∩ T ∪ Z ∩ Xstar := fun Z hZ => by
    rw [← inter_union_distrib_left, eq_comm, inter_eq_left]
    refine hZ.trans fun x ⟨h0, h1⟩ => ?_
    by_cases hx : x ≤ 1 / 2
    exacts [Or.inl ⟨h0, hx⟩, Or.inr ⟨by linarith, h1⟩]
  have hm : (1 / 2 : ℝ) ∈ Xstar := by norm_num [Xstar]
  have half : (1 / 2 : ℝ) ∈ X₁ ↔ (1 / 2 : ℝ) ∈ X₂ := ⟨fun a => ((Set.ext_iff.1 h _).1 ⟨a, hm⟩).1,
    fun a => ((Set.ext_iff.1 h _).2 ⟨a, hm⟩).1⟩
  rw [split X₁ h₁.1.2.1, split X₂ h₂.1.2.1, h₁.inter_T, h₂.inter_T, h, half]

end Grothendieck.Folder150
