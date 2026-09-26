import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Folder 106: cofibration categories and Brown's factorisation lemma

The modernised reading `transcripts/106/106.modern.tex` works in a category `𝒞`
with an initial object `∅`, weak equivalences `W` and cofibrations `cof`
satisfying Baues's axioms C1–C3, which its conventions footnote recalls (from
memory) as follows:

> C1, les isomorphismes sont dans `W` et dans `cof`, les composés de
> cofibrations sont des cofibrations, et `W` satisfait au deux-sur-trois ;
> C2, pour une cofibration `c : b → a` et une flèche `u : b → y`, la somme
> amalgamée `a ∨_b y` existe, la flèche `y → a ∨_b y` est une cofibration, et
> une équivalence faible si `c` en est une, et la flèche `a → a ∨_b y` est une
> équivalence faible si `u` en est une ; C3, toute flèche se factorise en une
> cofibration suivie d'une équivalence faible.

These are the fields of `CategorieACofibrations` below, verbatim. C2 is stated
for every pushout square (`IsPushout`) rather than for a chosen pushout; since
C1 puts the isomorphisms in `W` and `cof`, and both are closed under
composition, the two formulations are equivalent.

This file formalises **only what issue #26 names for the folder** — the
cofibration-category axioms and Brown's factorisation — namely three statements
of the reading:

* **Page 1, the « weak lifting lemma »** (`relevementFaible`), in the form the
  reading derives from C1–C3: given `f : x → y`, `α_x : x̃ → x`, `α_y : ỹ → y`
  in `W` with `x̃, ỹ` cofibrant, there are `i : ỹ → ỹ'` in `cof ∩ W`,
  `α'_y : ỹ' → y` in `W` with `α_y = α'_y i`, and `f̃ : x̃ → ỹ'` with
  `α'_y f̃ = f α_x`. The proof is the reading's: factor `(α_y, f α_x)` out of
  `ỹ ∨ x̃`. The formalisation adds that `ỹ'` is cofibrant, which the reading
  uses (it puts `[i]⁻¹[f̃]` in `W_cof⁻¹𝒞_cof`) without saying it.
* **Page 9, Brown's factorisation** (`factorisationDeBrown`): `x, y` cofibrant,
  `f : x → y` in `W`; factoring `(f, 1_y) : x ⊔ y → y` gives `α i = f`,
  `α g = 1_y`, `i, g ∈ cof ∩ W`, `α ∈ W`.
* **Page 11, the doubt lifted** (`inverse_W_of_inverse_W₀`,
  `localisation_W₀_iso_localisation_W`): when every object is cofibrant, a
  functor that inverts `W₀ = W ∩ cof` inverts `W`, and so
  `W₀⁻¹𝒞 → W⁻¹𝒞` is an isomorphism of categories — stated here as a pair of
  mutually inverse functors (equalities of functors, not natural isomorphisms)
  compatible with the two localisation functors.

What the formalisation finds. All three hold as the reading states them, with
no hypothesis added. Two hypotheses are more than the proofs use, and the
general forms are proved alongside:
* in the weak lifting lemma, `α_x ∈ W` is not used, and `ỹ` need not be
  cofibrant for `i` to be a cofibration — only `x̃` must be (as the reading
  itself says: « parce que `x̃` est cofibrant »); `ỹ` cofibrant is used only to
  make `ỹ'` cofibrant;
* in Brown's factorisation, `f ∈ W` is used only for `i ∈ W`; for an arbitrary
  `f` between cofibrant objects one still gets `i ∈ cof`, `g ∈ cof ∩ W`,
  `α ∈ W` (`factorisationDeBrown_general`). Of C2 only the existence of
  pushouts along a cofibration and the stability of cofibrations under cobase
  change are used; the two weak-equivalence clauses of C2, and the clause of C1
  that isomorphisms are cofibrations, are never used.

Not formalised: the Proposition of page 5 (`Ψ` is an equivalence iff `(⋆)`),
the reduction to `𝒞_cof`, the categories `Ch₀`, `Ch'₀`, `𝒞̃`, `𝒞̃'`, the functor
`q` and its fullness, and the criterion `(⋆⋆)` — these are not what the #26 row
names, and `(⋆⋆)`'s sufficiency is not established by the folder either.

What this certifies is that the reading holds together, not that it is what the
page says (issue #26).
-/

namespace Grothendieck.Folder106

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasInitial C]

/-- A *catégorie à cofibrations* in the sense of Baues, as the reading's
conventions footnote recalls axioms C1–C3, on a category with an initial
object `∅`. -/
class CategorieACofibrations (W cof : MorphismProperty C) : Prop where
  /-- C1: isomorphisms are weak equivalences. -/
  iso_W : ∀ {x y : C} (e : x ≅ y), W e.hom
  /-- C1: isomorphisms are cofibrations. -/
  iso_cof : ∀ {x y : C} (e : x ≅ y), cof e.hom
  /-- C1: composites of cofibrations are cofibrations. -/
  cof_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), cof f → cof g → cof (f ≫ g)
  /-- C1, two-out-of-three: the composite of two weak equivalences is one. -/
  W_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), W f → W g → W (f ≫ g)
  /-- C1, two-out-of-three: if `f` and `f ≫ g` are weak equivalences, so is `g`. -/
  W_of_comp_left : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), W f → W (f ≫ g) → W g
  /-- C1, two-out-of-three: if `g` and `f ≫ g` are weak equivalences, so is `f`. -/
  W_of_comp_right : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), W g → W (f ≫ g) → W f
  /-- C2: the pushout along a cofibration exists. -/
  hasPushout : ∀ {b a y : C} (c : b ⟶ a) (u : b ⟶ y), cof c → HasPushout c u
  /-- C2: in a pushout square `c ≫ u' = u ≫ c'` with `c : b → a` a cofibration,
  `c' : y → a ∨_b y` is a cofibration. -/
  pushout_cof : ∀ {b a y p : C} {c : b ⟶ a} {u : b ⟶ y} {u' : a ⟶ p} {c' : y ⟶ p},
    IsPushout c u u' c' → cof c → cof c'
  /-- C2: … and a weak equivalence if `c` is one. -/
  pushout_W_of_W : ∀ {b a y p : C} {c : b ⟶ a} {u : b ⟶ y} {u' : a ⟶ p} {c' : y ⟶ p},
    IsPushout c u u' c' → cof c → W c → W c'
  /-- C2: `u' : a → a ∨_b y` is a weak equivalence if `u` is one. -/
  pushout_W_of_W' : ∀ {b a y p : C} {c : b ⟶ a} {u : b ⟶ y} {u' : a ⟶ p} {c' : y ⟶ p},
    IsPushout c u u' c' → cof c → W u → W u'
  /-- C3: every arrow factors as a cofibration followed by a weak equivalence. -/
  factorisation : ∀ {x y : C} (f : x ⟶ y),
    ∃ (z : C) (i : x ⟶ z) (p : z ⟶ y), cof i ∧ W p ∧ i ≫ p = f

/-- An object `x` is *cofibrant* when `∅ → x` is a cofibration. -/
def Cofibrant (cof : MorphismProperty C) (x : C) : Prop := cof (initial.to x)

variable {W cof : MorphismProperty C} [CategorieACofibrations W cof]

namespace CategorieACofibrations

omit [HasInitial C] in
include cof in
lemma W_id (x : C) : W (𝟙 x) := iso_W (cof := cof) (Iso.refl x)

include W in
/-- Composing a cofibration `∅ → x` with a cofibration `x → z` shows `z`
cofibrant. -/
lemma cofibrant_of_cof {x z : C} (hx : Cofibrant cof x) (i : x ⟶ z) (hi : cof i) :
    Cofibrant cof z := by
  have := cof_comp (W := W) _ _ hx hi
  unfold Cofibrant
  rwa [Subsingleton.elim (initial.to z) (initial.to x ≫ i)]

/-- Cofibrant replacement (page 1): C3 applied to `∅ → x` gives `α_x : x̃ → x`
in `W` with `x̃` cofibrant. -/
theorem remplacementCofibrant (x : C) :
    ∃ (x' : C) (α : x' ⟶ x), Cofibrant cof x' ∧ W α := by
  obtain ⟨z, i, p, hi, hp, -⟩ := factorisation (W := W) (cof := cof) (initial.to x)
  refine ⟨z, p, ?_, hp⟩
  unfold Cofibrant
  rwa [Subsingleton.elim (initial.to z) i]

/-- The common core of pages 1 and 9. Given `p : a → y` and `q : b → y` with
`b` cofibrant, the sum `a ⊔ b` (the pushout of `∅ → b` along `∅ → a`) exists,
and factoring `(p, q) : a ⊔ b → y` by C3 gives `ja : a → z`, `jb : b → z`,
`w : z → y` with `w ∈ W`, `ja ≫ w = p`, `jb ≫ w = q`; `ja` is a cofibration
because `b` is cofibrant, and `jb` is one as soon as `a` is. -/
theorem factorisation_somme {a b y : C} (hb : Cofibrant cof b) (p : a ⟶ y) (q : b ⟶ y) :
    ∃ (z : C) (ja : a ⟶ z) (jb : b ⟶ z) (w : z ⟶ y),
      cof ja ∧ W w ∧ ja ≫ w = p ∧ jb ≫ w = q ∧ (Cofibrant cof a → cof jb) := by
  have := hasPushout (W := W) (initial.to b) (initial.to a) hb
  have hP := IsPushout.of_hasPushout (initial.to b) (initial.to a)
  -- `pushout.inl : b → a ⊔ b`, `pushout.inr : a → a ⊔ b`
  obtain ⟨z, c, w, hc, hw, hcw⟩ := factorisation (W := W) (cof := cof)
    (hP.desc q p (Subsingleton.elim _ _))
  refine ⟨z, pushout.inr _ _ ≫ c, pushout.inl _ _ ≫ c, w,
    cof_comp (W := W) _ _ (pushout_cof (W := W) hP hb) hc, hw, ?_, ?_, ?_⟩
  · rw [Category.assoc, hcw, hP.inr_desc]
  · rw [Category.assoc, hcw, hP.inl_desc]
  · intro ha
    exact cof_comp (W := W) _ _ (pushout_cof (W := W) hP.flip ha) hc

/-- **Page 1, the weak lifting lemma, general form.** Given `f : x → y`,
`α_x : x̃ → x`, `α_y : ỹ → y ∈ W` with `x̃` cofibrant, there are
`i : ỹ → ỹ'` in `cof ∩ W`, `α'_y : ỹ' → y` in `W` with `α_y = α'_y i`, and
`f̃ : x̃ → ỹ'` with `α'_y f̃ = f α_x`; and `ỹ'` is cofibrant if `ỹ` is.
Neither `α_x ∈ W` nor `ỹ` cofibrant is needed for the lifting itself. -/
theorem relevementFaible_general {x y x' y' : C} (f : x ⟶ y) (αx : x' ⟶ x) (αy : y' ⟶ y)
    (hαy : W αy) (hx' : Cofibrant cof x') :
    ∃ (y'' : C) (i : y' ⟶ y'') (α' : y'' ⟶ y) (f' : x' ⟶ y''),
      cof i ∧ W i ∧ W α' ∧ i ≫ α' = αy ∧ f' ≫ α' = αx ≫ f ∧
      (Cofibrant cof y' → Cofibrant cof y'') := by
  obtain ⟨z, ja, jb, w, hja, hw, h1, h2, -⟩ := factorisation_somme (W := W) hx' αy (αx ≫ f)
  refine ⟨z, ja, w, jb, hja, W_of_comp_right (cof := cof) _ _ hw (h1 ▸ hαy), hw, h1, h2,
    fun hy' => cofibrant_of_cof (W := W) hy' ja hja⟩

/-- **Page 1, the weak lifting lemma, as the reading states it**, for cofibrant
replacements `α_x : x̃ → x`, `α_y : ỹ → y` (cofibrant sources, arrows in `W`):
there are `i : ỹ → ỹ'` in `cof ∩ W`, `α'_y : ỹ' → y` in `W` with
`α_y = α'_y i`, and `f̃ : x̃ → ỹ'` with `α'_y f̃ = f α_x`; moreover `ỹ'` is
cofibrant. -/
theorem relevementFaible {x y x' y' : C} (f : x ⟶ y) (αx : x' ⟶ x) (αy : y' ⟶ y)
    (hx' : Cofibrant cof x') (_hαx : W αx) (hy' : Cofibrant cof y') (hαy : W αy) :
    ∃ (y'' : C) (i : y' ⟶ y'') (α' : y'' ⟶ y) (f' : x' ⟶ y''),
      cof i ∧ W i ∧ W α' ∧ i ≫ α' = αy ∧ f' ≫ α' = αx ≫ f ∧ Cofibrant cof y'' := by
  obtain ⟨y'', i, α', f', h1, h2, h3, h4, h5, h6⟩ :=
    relevementFaible_general (W := W) f αx αy hαy hx'
  exact ⟨y'', i, α', f', h1, h2, h3, h4, h5, h6 hy'⟩

/-- **Brown's factorisation, general form.** For any `f : x → y` between
cofibrant objects, factoring `(f, 1_y) : x ⊔ y → y` gives `x̄`, `i : x → x̄`
cofibration, `g : y → x̄` in `cof ∩ W`, `α : x̄ → y` in `W`, with `α i = f` and
`α g = 1_y`. -/
theorem factorisationDeBrown_general {x y : C} (hx : Cofibrant cof x) (hy : Cofibrant cof y)
    (f : x ⟶ y) :
    ∃ (x' : C) (i : x ⟶ x') (g : y ⟶ x') (α : x' ⟶ y),
      cof i ∧ cof g ∧ W g ∧ W α ∧ i ≫ α = f ∧ g ≫ α = 𝟙 y := by
  obtain ⟨z, ja, jb, w, hja, hw, h1, h2, h3⟩ := factorisation_somme (W := W) hy f (𝟙 y)
  refine ⟨z, ja, jb, w, hja, h3 hx, ?_, hw, h1, h2⟩
  exact W_of_comp_right (cof := cof) _ _ hw (h2 ▸ W_id (cof := cof) y)

/-- **Page 9, Brown's factorisation, as the reading states it.** Let `x, y` be
cofibrant and `f : x → y` in `W`. Factoring `(f, 1_y) : x ⊔ y → y` as a
cofibration followed by `α : x̄ → y` in `W`, and writing `i`, `g` for the
composites of `x → x ⊔ y`, `y → x ⊔ y` with `x ⊔ y → x̄`, one has `α i = f`,
`α g = 1_y`, and `i, g ∈ cof ∩ W`. -/
theorem factorisationDeBrown {x y : C} (hx : Cofibrant cof x) (hy : Cofibrant cof y)
    (f : x ⟶ y) (hf : W f) :
    ∃ (x' : C) (i : x ⟶ x') (g : y ⟶ x') (α : x' ⟶ y),
      cof i ∧ W i ∧ cof g ∧ W g ∧ W α ∧ i ≫ α = f ∧ g ≫ α = 𝟙 y := by
  obtain ⟨x', i, g, α, hi, hg, hgW, hα, h1, h2⟩ := factorisationDeBrown_general (W := W) hx hy f
  exact ⟨x', i, g, α, hi, W_of_comp_right (cof := cof) _ _ hα (h1 ▸ hf), hg, hgW, hα, h1, h2⟩

/-- **Page 11, the doubt lifted.** When every object is cofibrant, a functor
inverting the trivial cofibrations `W₀ = W ∩ cof` inverts every weak
equivalence: write `f = α i` with `α g = 1_y` and `i, g ∈ W₀` (page 9); then
`[α] = [g]⁻¹` and `[f] = [α][i]` are invertible. -/
theorem inverse_W_of_inverse_W₀ (hcof : ∀ x : C, Cofibrant cof x) {D : Type*} [Category D]
    (F : C ⥤ D) (hF : (W ⊓ cof).IsInvertedBy F) : W.IsInvertedBy F := by
  intro x y f hf
  obtain ⟨x', i, g, α, hi, hiW, hg, hgW, -, h1, h2⟩ :=
    factorisationDeBrown (W := W) (hcof x) (hcof y) f hf
  have := hF i ⟨hiW, hi⟩
  have := hF g ⟨hgW, hg⟩
  have hα : F.map α = inv (F.map g) := by
    rw [← cancel_epi (F.map g), IsIso.hom_inv_id, ← F.map_comp, h2, F.map_id]
  have : IsIso (F.map α) := by rw [hα]; infer_instance
  rw [← h1, F.map_comp]
  infer_instance

/-- **Page 11: `W₀⁻¹𝒞 → W⁻¹𝒞` is an isomorphism of categories** when every
object is cofibrant, `W₀ = W ∩ cof`. Stated as a pair of functors
`F : W₀⁻¹𝒞 → W⁻¹𝒞`, `G : W⁻¹𝒞 → W₀⁻¹𝒞`, compatible with the localisation
functors, with `F ⋙ G` and `G ⋙ F` *equal* to the identities. -/
theorem localisation_W₀_iso_localisation_W (hcof : ∀ x : C, Cofibrant cof x) :
    ∃ (F : (W ⊓ cof).Localization ⥤ W.Localization)
      (G : W.Localization ⥤ (W ⊓ cof).Localization),
      (W ⊓ cof).Q ⋙ F = W.Q ∧ W.Q ⋙ G = (W ⊓ cof).Q ∧
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ := by
  have hF : (W ⊓ cof).IsInvertedBy W.Q := fun _ _ f hf => W.Q_inverts f hf.1
  have hG : W.IsInvertedBy (W ⊓ cof).Q :=
    inverse_W_of_inverse_W₀ (W := W) hcof _ (W ⊓ cof).Q_inverts
  refine ⟨Localization.Construction.lift _ hF, Localization.Construction.lift _ hG,
    Localization.Construction.fac _ hF, Localization.Construction.fac _ hG, ?_, ?_⟩
  · apply Localization.Construction.uniq
    rw [← Functor.assoc, Localization.Construction.fac, Localization.Construction.fac]
    rfl
  · apply Localization.Construction.uniq
    rw [← Functor.assoc, Localization.Construction.fac, Localization.Construction.fac]
    rfl

end CategorieACofibrations

end Grothendieck.Folder106
