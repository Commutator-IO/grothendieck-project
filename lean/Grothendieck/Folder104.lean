import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.AlgebraicTopology.Reedy.Basic
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum

/-!
# Folder 104: categories of models, their three examples, and the globular complex

The modernised reading `transcripts/104/104.modern.tex` (pages 4 and 6–10)
considers a category `M` such that

> (i) toute flèche de `M` est un monomorphisme ;
> (ii) tout endomorphisme d'un objet de `M` est l'identité

(a direct category all of whose arrows are monic), and states:

* (*) `Hom_M(D', D) → D̃`, `u ↦ u(D')`, is injective (`etoile_injective`);
* the preorder "there is an arrow" on isomorphism classes is an order: two
  arrows `D' → D → D'` are inverse isomorphisms (`isIso_of_aller_retour`);
* two sub-objects `x ⊆ y` of the same type are equal, whence
  `τ_n⁻¹(n) = {d_n}` and the strict monotonicity of `τ_n`
  (`sousObjet_eq_of_meme_type`);
* in the converse construction, `u_{d_n} = id` follows from the composition
  law and bijectivity (`id_of_idempotent_bijective`);
* **Example 1**, the finite total orders `Δ_n` and strictly increasing maps —
  the category whose presheaves are the *semi*-simplicial sets — satisfies (i)
  and (ii) (`DeltaInj`, `deltaInj_mono`, `deltaInj_end`), and
  `Card I_n = 2^{n+1} - 1` (`card_I_simplexe`);
* well-foundedness (the reading's footnote, page 6): in a skeletal category
  satisfying (ii), every non-identity arrow `X → Y` admits no arrow back
  (`strict_of_not_isIso`, `strict_of_not_identities`); if this strict order is
  well founded, the rank is a degree making `M` a direct category, mathlib's
  `ReedyStructure` with `W₁` the identities and `W₂` all arrows
  (`reedyDirecte`), and conversely (`wf_of_degre`); (i) and (ii) alone do not
  suffice — the ordered set `ℤ` satisfies both and is not direct
  (`entiers_relatifs_non_directe`);
* in Example 1, the faces `δ_i` satisfy the simplicial identities
  `δ_i ≫ δ_{j+1} = δ_j ≫ δ_i` for `i ≤ j` (`DeltaInj.δ_comp_δ`, as mathlib's
  `SimplexCategory.δ_comp_δ`), every arrow into `Δ_{n+1}` from a lower `Δ_m`
  factors through a face (`DeltaInj.factorise_face`), and `Δ` is skeletal and
  direct (`deltaInj_skeletal`, `deltaInj_lt`, `deltaInjReedy`);
* **Example 2**, the cube: `Card I_n = Σ_k C(n,k) 2^k = 3^n`
  (`card_I_cube`, `somme_faces_cube`);
* **Example 3**, the hemispherical disc, `I_n = (Δ_{n-1} × {±1}) ⊔ {d_n}` with
  `(k, ε) < (k', ε')` iff `k < k'`: this is an order (`Hemi`), with
  `Card I_n = 2n + 1` (`card_I_hemi`) and two elements of each type `k < n`
  (`card_type_hemi`); with the leaf's « ordre chaotique » on `{±1}` the
  product is only a preorder (`chaotique_non_antisymetrique`);
* page 4: `ℤ[F_{n+1}] → ℤ[F_n] → ℤ[F_{n-1}]`, with differential `t - s`, is a
  complex by the globular identities (`globulaire_complexe`).

All are proved as the reading states them, after its own two corrections
(Example 3: `Δ_{n-1}`, not the leaf's `Δ_n`, and the order, not the chaotic
preorder), which the formalisation confirms: with `Δ_n` the count is
`2n + 3`, and the chaotic product is not antisymmetric.

What the formalisation found: nothing wrong. Two remarks. Property (i) is not
needed for the order on classes nor for `u_{d_n} = id`; (ii) alone gives them.
And (i) is needed in (*) only to make `u ↦ u(D')` land in sub-objects at all.
Well-foundedness is a genuine further hypothesis, as the reading's « dès
que » says: `ℤ` is the counterexample.
Not formalised: the equivalence `M ≃ M₀` and its converse (pages 8–10), the
sphericity claims a) b) of page 10 (geometric realisations), and the
question of page 11.
-/

namespace Grothendieck.Folder104

open CategoryTheory

/-! ### 1. Categories of models -/

section Modeles

variable {M : Type*} [Category M]
  (hmono : ∀ {X Y : M} (f : X ⟶ Y), Mono f)
  (hend : ∀ {X : M} (f : X ⟶ X), f = 𝟙 X)

include hend in
/-- (*) `Hom(D', D) → D̃`, `u ↦ u(D')`, is injective. The `Mono` instances are
what (i) supplies in `M` (`hmono u`); only (ii) is used in the proof. -/
theorem etoile_injective {D' D : M} (u v : D' ⟶ D) [Mono u] [Mono v]
    (h : Subobject.mk u = Subobject.mk v) : u = v := by
  have e := Subobject.ofMkLEMk_comp h.le
  rw [hend (Subobject.ofMkLEMk u v h.le), Category.id_comp] at e
  exact e.symm

include hmono hend in
/-- (*) in `M` itself, where every arrow is monic by (i). -/
theorem etoile_injective' {D' D : M} (u v : D' ⟶ D)
    (h : @Subobject.mk _ _ _ _ u (hmono u) = @Subobject.mk _ _ _ _ v (hmono v)) : u = v :=
  @etoile_injective _ _ hend _ _ u v (hmono u) (hmono v) h

include hend in
/-- Two arrows `D' → D → D'` are inverse isomorphisms: the preorder on classes
is an order. -/
theorem isIso_of_aller_retour {A B : M} (f : A ⟶ B) (g : B ⟶ A) : IsIso f :=
  ⟨g, hend _, hend _⟩

include hend in
/-- Two sub-objects `x ⊆ y` of the same type (there is an arrow `y → x`) are
equal. In particular `τ_n⁻¹(n) = {d_n}`, and `τ_n` is strictly increasing. -/
theorem sousObjet_eq_of_meme_type {D : M} {x y : Subobject D} (hxy : x ≤ y)
    (g : (y : M) ⟶ (x : M)) : x = y := by
  refine le_antisymm hxy (Subobject.le_of_comm g ?_)
  rw [← Subobject.ofLE_arrow hxy, ← Category.assoc, hend (g ≫ Subobject.ofLE x y hxy),
    Category.id_comp]

/-- In the converse construction: the composition law gives `u_d ∘ u_d = u_d`,
and `u_d` being bijective it is the identity. -/
theorem id_of_idempotent_bijective {α : Type*} (f : α → α) (hf : Function.Bijective f)
    (h : f ∘ f = f) : f = id := by
  funext x
  exact hf.1 (congrFun h x)

end Modeles

/-! ### 1b. Well-foundedness: direct categories in Reedy's sense -/

section Reedy

variable {M : Type u} [Category.{v} M]
  (hend : ∀ {X : M} (f : X ⟶ X), f = 𝟙 X)

/-- The strict order on objects: an arrow `X → Y` and none back. -/
def Strict (X Y : M) : Prop := Nonempty (X ⟶ Y) ∧ IsEmpty (Y ⟶ X)

include hend in
/-- Under (ii), a non-invertible arrow `X → Y` admits no arrow back. -/
theorem strict_of_not_isIso {X Y : M} (f : X ⟶ Y) (hf : ¬ IsIso f) : Strict X Y :=
  ⟨⟨f⟩, ⟨fun g => hf ⟨g, hend _, hend _⟩⟩⟩

include hend in
/-- In a skeletal category satisfying (ii), an arrow that is not an identity
is not invertible, hence strict. -/
theorem strict_of_not_identities (hsk : Skeletal M) {X Y : M} (f : X ⟶ Y)
    (hf : ¬ MorphismProperty.identities M f) : Strict X Y := by
  refine strict_of_not_isIso hend f fun hi => hf ?_
  obtain rfl : X = Y := hsk ⟨asIso f⟩
  rw [hend f]
  exact MorphismProperty.ofHoms.mk _

/-- The factorisation of `f` as `𝟙 ≫ f` is the only one with first factor an identity. -/
theorem factorisation_unique {X Y : M} (f : X ⟶ Y) :
    Nonempty (Unique ((MorphismProperty.identities M).MapFactorizationData ⊤ f)) :=
  ⟨{ default := ⟨X, 𝟙 X, f, by simp, MorphismProperty.ofHoms.mk _, trivial⟩
     uniq := by
       rintro ⟨Z, i, p, fac, hi, hp⟩
       cases hi
       simp only [Category.id_comp] at fac
       subst fac
       rfl }⟩

include hend in
/-- **Reedy.** A skeletal category satisfying (ii) whose strict order on
objects is well founded is a direct category: the rank of an object for that
order is a degree that every non-identity arrow strictly raises. -/
noncomputable def reedyDirecte (hsk : Skeletal M) (hwf : WellFounded (Strict (M := M))) :
    HomotopicalAlgebra.ReedyStructure (MorphismProperty.identities M) ⊤ Ordinal.{u} :=
  haveI : IsWellFounded M Strict := ⟨hwf⟩
  { deg := IsWellFounded.rank Strict
    lt₁ := fun _ hf hf' => absurd hf hf'
    lt₂ := fun f _ hf' => IsWellFounded.rank_lt_of_rel (strict_of_not_identities hend hsk f hf')
    nonempty_unique := factorisation_unique }

/-- Conversely, a degree into a well-founded order that every non-identity arrow
raises makes the strict order well founded. -/
theorem wf_of_degre {α : Type*} [Preorder α] [WellFoundedLT α] (deg : M → α)
    (hdeg : ∀ {X Y : M} (f : X ⟶ Y), ¬ MorphismProperty.identities M f → deg X < deg Y) :
    WellFounded (Strict (M := M)) := by
  refine Subrelation.wf (r := InvImage (· < ·) deg) ?_ (InvImage.wf deg wellFounded_lt)
  rintro X Y ⟨⟨f⟩, ⟨e⟩⟩
  refine hdeg f fun hi => ?_
  cases hi
  exact e (𝟙 X)

/-- (i) and (ii) do not make a direct category: the ordered set `ℤ`, as a
category, satisfies both, and its strict order is not well founded. -/
theorem entiers_relatifs_non_directe :
    (∀ {X Y : ℤ} (f : X ⟶ Y), Mono f) ∧ (∀ {X : ℤ} (f : X ⟶ X), f = 𝟙 X) ∧
      ¬ WellFounded (Strict (M := ℤ)) := by
  refine ⟨fun _ => ⟨fun _ _ _ => Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _, ?_⟩
  intro hwf
  obtain ⟨m, -, hm⟩ := hwf.has_min Set.univ ⟨0, trivial⟩
  exact hm (m - 1) trivial ⟨⟨homOfLE (by omega)⟩, ⟨fun f => absurd (leOfHom f) (by omega)⟩⟩

end Reedy

/-! ### 2. The three examples -/

/-- **Example 1.** The finite total orders `Δ_n = {0, …, n}` and the strictly
increasing maps. -/
structure DeltaInj where
  /-- `Δ_n` is `{0, …, n}`. -/
  n : ℕ

instance : Category DeltaInj where
  Hom a b := {f : Fin (a.n + 1) → Fin (b.n + 1) // StrictMono f}
  id _ := ⟨id, strictMono_id⟩
  comp f g := ⟨g.1 ∘ f.1, g.2.comp f.2⟩

/-- (i) for `Δ`: every arrow is a monomorphism. -/
theorem deltaInj_mono {m n : DeltaInj} (f : m ⟶ n) : Mono f :=
  ⟨fun _ _ H => Subtype.ext <| funext fun x =>
    f.2.injective (congrFun (congrArg Subtype.val H) x)⟩

/-- (ii) for `Δ`: every endomorphism is the identity. -/
theorem deltaInj_end {a : DeltaInj} (f : a ⟶ a) : f = 𝟙 a := by
  have hcard : (Finset.univ : Finset (Fin (a.n + 1))).card = a.n + 1 := by simp
  have h1 := Finset.orderEmbOfFin_unique hcard (f := f.1) (fun _ => Finset.mem_univ _) f.2
  have h2 := Finset.orderEmbOfFin_unique hcard (f := id) (fun _ => Finset.mem_univ _)
    strictMono_id
  exact Subtype.ext (h1.trans h2.symm)

/-- The `i`-th face `δ_i : Δ_n → Δ_{n+1}`, the strictly increasing map that
misses `i`. -/
def DeltaInj.δ {n : ℕ} (i : Fin (n + 2)) : DeltaInj.mk n ⟶ DeltaInj.mk (n + 1) :=
  ⟨i.succAbove, Fin.strictMono_succAbove i⟩

/-- **The simplicial identities** (faces): `δ_j δ_i = δ_i δ_{j-1}` for `i < j`,
written `δ_i ≫ δ_{j+1} = δ_j ≫ δ_i` for `i ≤ j`, as in mathlib's
`SimplexCategory.δ_comp_δ`. -/
theorem DeltaInj.δ_comp_δ {n : ℕ} {i j : Fin (n + 2)} (H : i ≤ j) :
    DeltaInj.δ i ≫ DeltaInj.δ j.succ = DeltaInj.δ j ≫ DeltaInj.δ i.castSucc := by
  apply Subtype.ext
  funext k
  change j.succ.succAbove (i.succAbove k) = i.castSucc.succAbove (j.succAbove k)
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  simp only [Fin.le_def] at H
  simp only [Fin.succAbove, Fin.lt_def, Fin.ext_iff]
  split_ifs <;> simp at * <;> omega

/-- Every arrow `Δ_m → Δ_{n+1}` with `m ≤ n` factors through a face: a strictly
increasing map that is not surjective misses some `i`, and is `δ_i ∘ g`. -/
theorem DeltaInj.factorise_face {m n : ℕ} (hmn : m ≤ n)
    (f : DeltaInj.mk m ⟶ DeltaInj.mk (n + 1)) :
    ∃ (i : Fin (n + 2)) (g : DeltaInj.mk m ⟶ DeltaInj.mk n), f = g ≫ DeltaInj.δ i := by
  have hns : ¬ Function.Surjective f.1 := fun hs => by
    have := Fintype.card_le_of_surjective _ hs
    simp at this
    omega
  obtain ⟨i, hi⟩ := not_forall.1 hns
  have hne : ∀ k, f.1 k ≠ i := fun k h => hi ⟨k, h⟩
  choose g hg using fun k => Fin.exists_succAbove_eq (hne k)
  refine ⟨i, ⟨g, fun a b hab => ?_⟩, Subtype.ext (funext fun k => (hg k).symm)⟩
  have := f.2 hab
  rw [← hg a, ← hg b] at this
  exact (Fin.strictMono_succAbove i).lt_iff_lt.1 this


/-- `Δ` is skeletal: `Δ_m ≅ Δ_n` forces `m = n`. -/
theorem deltaInj_skeletal : Skeletal DeltaInj := by
  rintro ⟨m⟩ ⟨n⟩ ⟨e⟩
  have h1 := Fintype.card_le_of_injective _ e.hom.2.injective
  have h2 := Fintype.card_le_of_injective _ e.inv.2.injective
  simp only [Fintype.card_fin] at h1 h2
  rw [show m = n by omega]

/-- In `Δ`, an arrow that is not an identity raises the dimension. -/
theorem deltaInj_lt {X Y : DeltaInj} (f : X ⟶ Y)
    (hf : ¬ MorphismProperty.identities DeltaInj f) : X.n < Y.n := by
  obtain ⟨m⟩ := X
  obtain ⟨n⟩ := Y
  have h := Fintype.card_le_of_injective _ f.2.injective
  simp only [Fintype.card_fin] at h
  refine lt_of_le_of_ne (by simpa using h) fun hmn => hf ?_
  dsimp at hmn
  subst hmn
  rw [deltaInj_end f]
  exact MorphismProperty.ofHoms.mk _

/-- **Example 1 is a direct category**: the strict order of `Δ` is well
founded, and `reedyDirecte` applies. -/
noncomputable def deltaInjReedy :
    HomotopicalAlgebra.ReedyStructure (MorphismProperty.identities DeltaInj) ⊤ Ordinal.{0} :=
  reedyDirecte deltaInj_end deltaInj_skeletal (wf_of_degre DeltaInj.n deltaInj_lt)

/-- **Example 1**: `I_n = 𝔓*(Δ_n)`, the non-empty subsets, has `2^{n+1} - 1`
elements. -/
theorem card_I_simplexe (n : ℕ) :
    ((Finset.univ : Finset (Finset (Fin (n + 1)))).filter (·.Nonempty)).card = 2 ^ (n + 1) - 1 := by
  have : (Finset.univ : Finset (Finset (Fin (n + 1)))).filter (·.Nonempty) =
      Finset.univ.erase ∅ := by
    ext s; simp [Finset.nonempty_iff_ne_empty]
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_finset, Fintype.card_fin]

/-- **Example 2**: a face of `[0,1]^n` fixes some coordinates to `0` or `1` and
leaves the others free — a partial section of `Δ_{n-1} × {±1} → Δ_{n-1}` —
so `Card I_n = 3^n`. -/
theorem card_I_cube (n : ℕ) : Fintype.card (Fin n → Option Bool) = 3 ^ n := by
  simp

/-- Page 5: `1 + n·2 + C(n,2)·2² + ⋯ + 2ⁿ = (1 + 2)ⁿ`. -/
theorem somme_faces_cube (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), n.choose k * 2 ^ k = 3 ^ n := by
  have := (add_pow (2 : ℕ) 1 n).symm
  simp only [one_pow, mul_one] at this
  rw [show (2 : ℕ) + 1 = 3 from rfl] at this
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Example 3**, the hemispherical disc `D_n`: `I_n = (Δ_{n-1} × {±1}) ⊔ {d_n}`
(`none` is `d_n`). -/
def Hemi (n : ℕ) : Type := Option (Fin n × Bool)

instance (n : ℕ) : Fintype (Hemi n) := inferInstanceAs (Fintype (Option (Fin n × Bool)))

instance (n : ℕ) : DecidableEq (Hemi n) := inferInstanceAs (DecidableEq (Option (Fin n × Bool)))

/-- The order of the cells: `(k, ε) < (k', ε')` iff `k < k'`, `d_n` on top. -/
def Hemi.le {n : ℕ} : Hemi n → Hemi n → Prop
  | _, none => True
  | none, some _ => False
  | some a, some b => a = b ∨ a.1 < b.1

instance (n : ℕ) : PartialOrder (Hemi n) where
  le := Hemi.le
  le_refl a := by cases a <;> simp [Hemi.le]
  le_trans a b c := by
    cases a <;> cases b <;> cases c <;> simp only [Hemi.le, imp_self, implies_true,
      IsEmpty.forall_iff]
    rename_i a b c
    rintro (rfl | h₁) (rfl | h₂)
    · exact Or.inl rfl
    · exact Or.inr h₂
    · exact Or.inr h₁
    · exact Or.inr (h₁.trans h₂)
  le_antisymm a b := by
    cases a <;> cases b <;> simp only [Hemi.le, IsEmpty.forall_iff, forall_const]
    · rfl
    rename_i a b
    rintro (rfl | h₁) (h₂ | h₂)
    · rfl
    · rfl
    · exact h₂.symm ▸ rfl
    · exact absurd (h₁.trans h₂) (lt_irrefl _)

/-- `Card I_n = 2n + 1` (with the leaf's `Δ_n` it would be `2n + 3`). -/
theorem card_I_hemi (n : ℕ) : Fintype.card (Hemi n) = 2 * n + 1 := by
  change Fintype.card (Option (Fin n × Bool)) = _
  simp [mul_comm]

/-- For `k < n` there are exactly two sub-objects of type `k`, the two
hemispheres of dimension `k`: `Hom(D_k, D_n)` has two elements (counted on the
carrier `Option (Fin n × Bool)` of `Hemi n`). -/
theorem card_type_hemi (n : ℕ) (k : Fin n) :
    ((Finset.univ : Finset (Option (Fin n × Bool))).filter
      (fun x => ∃ e : Bool, x = some (k, e))).card = 2 := by
  have : (Finset.univ : Finset (Option (Fin n × Bool))).filter (fun x => ∃ e : Bool, x = some (k, e)) =
      Finset.univ.image (fun e : Bool => (some (k, e) : Option (Fin n × Bool))) := by
    refine Finset.ext fun x => ?_
    rw [Finset.mem_filter, Finset.mem_image]
    simp only [Finset.mem_univ, true_and]
    exact ⟨fun ⟨e, h⟩ => ⟨e, h.symm⟩, fun ⟨e, h⟩ => ⟨e, h.symm⟩⟩
  rw [this, Finset.card_image_of_injective _ (fun e e' h => by
    simpa using (Option.some.inj h : ((k, e) : Fin n × Bool) = (k, e')))]
  rfl

/-- With `{±1}` carrying the chaotic preorder, `(k, ε) ≤ (k', ε')` iff `k ≤ k'`,
and the product is not antisymmetric: it is a preorder, not an order. -/
theorem chaotique_non_antisymetrique (n : ℕ) (k : Fin n) :
    let R : Fin n × Bool → Fin n × Bool → Prop := fun a b => a.1 ≤ b.1
    R (k, true) (k, false) ∧ R (k, false) (k, true) ∧ (k, true) ≠ (k, false) := by
  simp

/-! ### 3. Page 4: the globular complex -/

/-- Page 4. For sources and targets `sₙ, tₙ : Fₙ → Fₙ₋₁` satisfying the globular
identities `sₙ₋₁ sₙ = sₙ₋₁ tₙ`, `tₙ₋₁ sₙ = tₙ₋₁ tₙ`, the maps
`tₙ - sₙ : ℤ[Fₙ] → ℤ[Fₙ₋₁]` compose to zero. -/
theorem globulaire_complexe {F₂ F₁ F₀ : Type*} (s₂ t₂ : F₂ → F₁) (s₁ t₁ : F₁ → F₀)
    (hs : s₁ ∘ s₂ = s₁ ∘ t₂) (ht : t₁ ∘ s₂ = t₁ ∘ t₂) :
    (Finsupp.lmapDomain ℤ ℤ t₁ - Finsupp.lmapDomain ℤ ℤ s₁) ∘ₗ
      (Finsupp.lmapDomain ℤ ℤ t₂ - Finsupp.lmapDomain ℤ ℤ s₂) = 0 := by
  simp only [LinearMap.sub_comp, LinearMap.comp_sub, ← Finsupp.lmapDomain_comp, hs, ht]
  exact sub_self _

end Grothendieck.Folder104
