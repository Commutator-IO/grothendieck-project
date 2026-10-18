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
import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Adjunction.Limits

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

**Pages 12–16** (issue #54, finding `104-pinned-posets-nonsingular-presheaves`). For a
skeletal `M` satisfying (i) and (ii):

* page 12's admissible objects (`Admissible`: `X` the supremum of its model sub-objects, and the
  intersection of two models the supremum of the models it contains) are exactly the
  non-singular presheaves, every element `D → X` a monomorphism (`admissible_iff`); the first
  condition alone gives it, using (i), and the second follows;
* the `M`-pinned posets (`Epingle`, with the page's axioms a), b), (1), (2)) and their
  morphisms form a category, and `X ↦ X̃`, the poset of elements `(D, x)` ordered by
  `x' = X(a)(x)`, pinned by `u_{(D,x)}(D', a) = (D', X(a)(x))`, is an equivalence
  `𝔹₀ ≌ (M-pinned posets)` (`versEpingle_isEquivalence`, `equivalence_page13`), with inverse
  `K ↦ X_K`, `X_K(D) = τ⁻¹(D)` acted on by the pinning (`versPrefaisceau`);
* the monomorphisms of `M̂` correspond to the injective maps (`mono_iff_injective_versEpingle`);
* page 16: sums and pushouts along monomorphisms of admissible presheaves are admissible
  (`admissible_coproduit`, `admissible_pushout`), they are sums and pushouts in `𝔹₀`, and
  `X ↦ X̃` sends them to sums and pushouts of pinned posets (`versEpingle_coproduit`,
  `versEpingle_pushout`); a presheaf with a map to an admissible one is admissible
  (`nonSingulier_of_hom`), more than page 16's « sub-object ».

So `X̃` is the category of elements of `X`, which (ii), skeletality and non-singularity make a
poset; the equivalence is the restriction of presheaves ≃ discrete fibrations.
Not formalised: the equivalence `M ≃ M₀` and its converse (pages 8–10), the
sphericity claims a) b) of page 10 (geometric realisations), the
question of page 11, the closed parts and gluing of pages 14–15, and the N.B. of page 16.
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
    (h : f ∘ f = f) : f = id :=
  funext fun x => hf.1 (congrFun h x)

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
  haveI : WellFounded (Strict (M := M)) := hwf
  { deg := WellFounded.rank Strict
    lt₁ := fun _ hf hf' => absurd hf hf'
    lt₂ := fun f _ hf' => WellFounded.rank_lt_of_rel (strict_of_not_identities hend hsk f hf')
    nonempty_unique := factorisation_unique }

/-- Conversely, a degree into a well-founded order that every non-identity arrow
raises makes the strict order well founded. -/
theorem wf_of_degre {α : Type*} [Preorder α] [WellFoundedLT α] (deg : M → α)
    (hdeg : ∀ {X Y : M} (f : X ⟶ Y), ¬ MorphismProperty.identities M f → deg X < deg Y) :
    WellFounded (Strict (M := M)) := by
  refine Subrelation.wf (r := InvImage (· < ·) deg) ?_ (InvImage.wf deg wellFounded_lt)
  rintro X Y ⟨⟨f⟩, ⟨e⟩⟩
  exact hdeg f fun ⟨_⟩ => e (𝟙 X)

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
  refine Subtype.ext (funext fun k => ?_)
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
  rw [show (3 : ℕ) = 2 + 1 from rfl, add_pow]
  exact Finset.sum_congr rfl fun k _ => by rw [one_pow, mul_one, mul_comm, Nat.cast_id]

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
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    exact exists_congr fun _ => eq_comm
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
  simp only [LinearMap.sub_comp, LinearMap.comp_sub, ← Finsupp.lmapDomain_comp, hs, ht, sub_self]

/-! ### 4. Pages 12–16: admissible presheaves and `M`-pinned posets -/

section Epinglage

open Opposite Limits

universe w

variable {M : Type w} [SmallCategory M]

/-- `I_D`: the sub-objects of `D` in a skeletal `M` satisfying (i) and (ii), that is, by (*),
the arrows `D' → D`. -/
abbrev Sous (D : M) : Type w := Σ D' : M, (D' ⟶ D)

/-- The order of `I_D`: `(D', a) ≤ (D'', b)` iff `a` factors through `b`. -/
def Sous.le {D : M} (y y' : Sous D) : Prop := ∃ w : y.1 ⟶ y'.1, w ≫ y'.2 = y.2

variable (M) in
/-- **An `M`-pinned poset** (pages 12–13): a poset `K`, a strictly increasing type map
`τ_K : K → N` (here `N` is the skeletal `M` itself, ordered by the existence of an arrow), and
for each `ξ` of type `n` an isomorphism `u_ξ : I_n ≅ K_{≤ξ}` with `u_ξ(d_n) = ξ`, satisfying
(1) `τ_K ∘ u_ξ = τ_n` and (2) `u_ξ ∘ u^n_y = u_{u_ξ(y)}`. -/
structure Epingle where
  /-- The poset. -/
  K : Type w
  [ordre : PartialOrder K]
  /-- The type map `τ_K`. -/
  τ : K → M
  τ_strict : ∀ ξ η : K, ξ < η → Nonempty (τ ξ ⟶ τ η) ∧ τ ξ ≠ τ η
  /-- The pinning `u_ξ : I_{τ ξ} → K`. -/
  u : (ξ : K) → Sous (τ ξ) → K
  u_top : ∀ ξ, u ξ ⟨τ ξ, 𝟙 _⟩ = ξ
  u_injective : ∀ ξ, Function.Injective (u ξ)
  u_range : ∀ ξ, Set.range (u ξ) = Set.Iic ξ
  u_le : ∀ ξ y y', u ξ y ≤ u ξ y' ↔ Sous.le y y'
  /-- (1) -/
  τ_u : ∀ ξ y, τ (u ξ y) = y.1
  /-- (2) -/
  u_u : ∀ ξ (y : Sous (τ ξ)) (z : Sous y.1),
    u (u ξ y) ⟨z.1, z.2 ≫ eqToHom (τ_u ξ y).symm⟩ = u ξ ⟨z.1, z.2 ≫ y.2⟩

attribute [instance] Epingle.ordre

/-- The morphisms of `M`-pinned posets (page 13): strictly increasing maps `f` with
`τ_L ∘ f = τ_K` making the triangles `u^L_{f ξ} = f ∘ u^K_ξ` commute. -/
@[ext]
structure Epingle.Hom (K L : Epingle M) where
  /-- The underlying map. -/
  f : K.K → L.K
  strictMono : StrictMono f
  τ_f : ∀ ξ, L.τ (f ξ) = K.τ ξ
  u_f : ∀ ξ y, f (K.u ξ y) = L.u (f ξ) ⟨y.1, y.2 ≫ eqToHom (τ_f ξ).symm⟩

instance : Category (Epingle M) where
  Hom := Epingle.Hom
  id K := ⟨id, strictMono_id, fun _ => rfl, fun _ _ => by simp⟩
  comp φ ψ := ⟨ψ.f ∘ φ.f, ψ.strictMono.comp φ.strictMono,
    fun ξ => (ψ.τ_f _).trans (φ.τ_f ξ), fun ξ y => by simp [φ.u_f, ψ.u_f]⟩

@[ext]
lemma Epingle.hom_ext {K L : Epingle M} {φ ψ : K ⟶ L} (h : φ.f = ψ.f) : φ = ψ :=
  Epingle.Hom.ext h

@[simp] lemma Epingle.id_f (K : Epingle M) : Epingle.Hom.f (𝟙 K) = id := rfl

@[simp] lemma Epingle.comp_f {K L N : Epingle M} (φ : K ⟶ L) (ψ : L ⟶ N) :
    (φ ≫ ψ).f = ψ.f ∘ φ.f := rfl

end Epinglage


section Prefaisceaux

open Opposite Limits

universe w

variable {M : Type w} [SmallCategory M]

/-- A presheaf is **non-singular** when each of its elements `x ∈ X(D)` is a monomorphism
`yoneda D → X`, that is, `a ↦ X(a)(x)` is injective. -/
def NonSingulier (X : Mᵒᵖ ⥤ Type w) : Prop :=
  ∀ ⦃D D' : M⦄ (x : X.obj (op D)) (a b : D' ⟶ D), X.map a.op x = X.map b.op x → a = b

/-- A sub-object of `X` is a *model* if it is isomorphic to an object of `M`. -/
def EstModele {X : Mᵒᵖ ⥤ Type w} (S : Subfunctor X) : Prop :=
  ∃ D : M, Nonempty (S.toFunctor ≅ yoneda.obj D)

/-- **The admissible objects** of page 12: `X` is the supremum of its model sub-objects, and the
intersection of two model sub-objects is the supremum of the model sub-objects it contains. -/
def Admissible (X : Mᵒᵖ ⥤ Type w) : Prop :=
  sSup {S : Subfunctor X | EstModele S} = ⊤ ∧
    ∀ S T : Subfunctor X, EstModele S → EstModele T →
      S ⊓ T = sSup {R | EstModele R ∧ R ≤ S ⊓ T}

lemma nonSingulier_iff_mono (X : Mᵒᵖ ⥤ Type w) :
    NonSingulier X ↔ ∀ (D : M) (x : X.obj (op D)), Mono (yonedaEquiv.symm x) := by
  simp only [NatTrans.mono_iff_mono_app, mono_iff_injective]
  refine ⟨fun h D x U a b hab => h x a b hab, fun h D D' x a b hab => h D x (op D') hab⟩

/-- The model sub-object generated by an element of a non-singular presheaf. -/
noncomputable def modeleEngendre {X : Mᵒᵖ ⥤ Type w} {D : M} (x : X.obj (op D)) :
    Subfunctor X :=
  Subfunctor.range (yonedaEquiv.symm x)

lemma mem_modeleEngendre {X : Mᵒᵖ ⥤ Type w} {D : M} (x : X.obj (op D)) :
    x ∈ (modeleEngendre x).obj (op D) :=
  ⟨𝟙 D, by simp [yonedaEquiv_symm_app_apply]⟩

lemma modeleEngendre_le {X : Mᵒᵖ ⥤ Type w} {D : M} (x : X.obj (op D)) (T : Subfunctor X)
    (hx : x ∈ T.obj (op D)) : modeleEngendre x ≤ T := by
  rintro U _ ⟨a, rfl⟩
  exact T.map a.op hx

lemma estModele_modeleEngendre {X : Mᵒᵖ ⥤ Type w} (hX : NonSingulier X) {D : M}
    (x : X.obj (op D)) : EstModele (modeleEngendre x) := by
  have := (nonSingulier_iff_mono X).1 hX D x
  exact ⟨D, ⟨(asIso (Subfunctor.toRange (yonedaEquiv.symm x))).symm⟩⟩

variable (hmono : ∀ {X Y : M} (f : X ⟶ Y), Mono f)

include hmono in
/-- **Page 12, read in the presheaf language.** When every arrow of `M` is a monomorphism, a
presheaf is admissible iff it is non-singular: every element is a monomorphism `yoneda D → X`.
The first condition of page 12 alone implies it; the second then follows. -/
theorem admissible_iff (X : Mᵒᵖ ⥤ Type w) : Admissible X ↔ NonSingulier X := by
  constructor
  · rintro ⟨h1, -⟩ D D' x a b hab
    have hx : x ∈ (sSup {S : Subfunctor X | EstModele S}).obj (op D) := by rw [h1]; trivial
    simp only [Subfunctor.sSup_obj, Set.sSup_eq_sUnion, Set.mem_sUnion, Set.mem_image,
      Set.mem_ofPred_eq] at hx
    obtain ⟨_, ⟨S, ⟨E, ⟨e⟩⟩, rfl⟩, hxS⟩ := hx
    let s : S.toFunctor.obj (op D) := ⟨x, hxS⟩
    have hs : S.toFunctor.map a.op s = S.toFunctor.map b.op s := Subtype.ext hab
    have na := NatTrans.naturality_apply e.hom a.op s
    have nb := NatTrans.naturality_apply e.hom b.op s
    rw [hs, nb] at na
    simp only [yoneda_obj_map, Quiver.Hom.unop_op] at na
    exact (cancel_mono (e.hom.app (op D) s)).1 na.symm
  · intro hX
    refine ⟨eq_top_iff.2 fun U x _ => ?_, fun S T _ _ => le_antisymm (fun U z hz => ?_)
      (sSup_le fun R hR => hR.2)⟩
    · exact (le_sSup (estModele_modeleEngendre hX x) : modeleEngendre x ≤ _) U
        (mem_modeleEngendre x)
    · exact (le_sSup (show modeleEngendre z ∈ {R | EstModele R ∧ R ≤ S ⊓ T} from
        ⟨estModele_modeleEngendre hX z, modeleEngendre_le z _ hz⟩)) U (mem_modeleEngendre z)


/-! ### The equivalence of page 13 -/

variable (hend : ∀ {X : M} (f : X ⟶ X), f = 𝟙 X) (hsk : Skeletal M)

/-- The elements of `X`, pairs `(D, x)` with `x ∈ X(D)`: in a skeletal `M`, the model
sub-objects of a non-singular `X`. -/
abbrev Elem (X : Mᵒᵖ ⥤ Type w) : Type w := Σ D : M, X.obj (op D)

include hend hsk in
lemma eq_of_aller_retour {D E : M} (a : D ⟶ E) (b : E ⟶ D) : D = E :=
  hsk ⟨⟨a, b, hend _, hend _⟩⟩

include hend hsk in
/-- The order of `X̃`: `(D', x') ≤ (D, x)` iff `x' = X(a)(x)` for an arrow `a : D' → D`. -/
@[instance_reducible]
def ordreElem (X : Mᵒᵖ ⥤ Type w) : PartialOrder (Elem X) where
  le p q := ∃ a : p.1 ⟶ q.1, X.map a.op q.2 = p.2
  le_refl p := ⟨𝟙 _, by simp⟩
  le_trans p q r := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a ≫ b, by simp [hb, ha]⟩
  le_antisymm := by
    rintro ⟨D, x⟩ ⟨E, y⟩ ⟨a, ha⟩ ⟨b, hb⟩
    dsimp at a b ha hb
    obtain rfl := eq_of_aller_retour hend hsk a b
    rw [hend a] at ha
    simp only [op_id, Functor.map_id_apply] at ha
    rw [ha]

lemma le_elem_iff (X : Mᵒᵖ ⥤ Type w) (p q : Elem X) :
    (ordreElem hend hsk X).le p q ↔ ∃ a : p.1 ⟶ q.1, X.map a.op q.2 = p.2 := Iff.rfl

lemma sigma_eq_iff {X : Mᵒᵖ ⥤ Type w} {D : M} (x y : X.obj (op D)) :
    (⟨D, x⟩ : Elem X) = ⟨D, y⟩ ↔ x = y := by
  simp

/-- **The `M`-pinned poset `X̃` of a non-singular presheaf** (page 12): its elements with the
type map `(D, x) ↦ D` and the pinning `u_{(D,x)}(D', a) = (D', X(a)(x))`. -/
def versEpingleObj (X : Mᵒᵖ ⥤ Type w) (hX : NonSingulier X) : Epingle M :=
  letI := ordreElem hend hsk X
  { K := Elem X
    τ := Sigma.fst
    τ_strict := by
      rintro ⟨D, x⟩ ⟨E, y⟩ hlt
      obtain ⟨⟨a, ha⟩, hn⟩ := lt_iff_le_not_ge.1 hlt
      refine ⟨⟨a⟩, fun h => hn ?_⟩
      dsimp at h a ha
      subst h
      rw [hend a] at ha
      exact ⟨𝟙 _, by simpa using ha.symm⟩
    u := fun ξ y => ⟨y.1, X.map y.2.op ξ.2⟩
    u_top := fun ξ => by simp
    u_injective := by
      rintro ξ ⟨E, c⟩ ⟨E', c'⟩ h
      obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
      rw [hX ξ.2 c c' (eq_of_heq h)]
    u_range := by
      intro ξ
      ext q
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y.2, rfl⟩
      · rintro ⟨a, ha⟩
        exact ⟨⟨q.1, a⟩, by dsimp only; rw [ha]⟩
    u_le := by
      rintro ξ ⟨E, c⟩ ⟨E', c'⟩
      change (∃ w : E ⟶ E', _) ↔ ∃ w : E ⟶ E', w ≫ c' = c
      refine exists_congr fun w => ⟨fun h => hX ξ.2 _ _ ?_, fun h => ?_⟩
      · simpa using h
      · simp [← h]
    τ_u := fun _ _ => rfl
    u_u := fun ξ y z => by simp }

/-- A natural transformation gives a morphism of pinned posets, `(D, x) ↦ (D, α(x))`. -/
def versEpingleMap {X Y : Mᵒᵖ ⥤ Type w} (hX : NonSingulier X) (hY : NonSingulier Y)
    (α : X ⟶ Y) : versEpingleObj hend hsk X hX ⟶ versEpingleObj hend hsk Y hY where
  f p := ⟨p.1, α.app _ p.2⟩
  strictMono := by
    rintro ⟨D, x⟩ ⟨E, y⟩ hlt
    obtain ⟨⟨a, ha⟩, hn⟩ := lt_iff_le_not_ge.1 hlt
    refine lt_iff_le_not_ge.2
      ⟨⟨a, by rw [← NatTrans.naturality_apply]; exact congrArg _ ha⟩, fun ⟨b, hb⟩ => hn ?_⟩
    dsimp at a b ha hb
    obtain rfl := eq_of_aller_retour hend hsk a b
    rw [hend a] at ha
    exact ⟨𝟙 _, by simpa using ha.symm⟩
  τ_f _ := rfl
  u_f := by
    rintro ⟨D, x⟩ ⟨E, (c : E ⟶ D)⟩
    change (⟨E, α.app _ (X.map c.op x)⟩ : Elem Y) = ⟨E, Y.map (c ≫ 𝟙 D).op (α.app _ x)⟩
    rw [Category.comp_id, NatTrans.naturality_apply]

/-- The category `𝔹₀` of admissible presheaves, a full subcategory of `M̂`. -/
abbrev Adm (M : Type w) [SmallCategory M] :=
  ObjectProperty.FullSubcategory (Admissible (M := M))

include hmono in
/-- **The functor `X ↦ X̃`** from admissible presheaves to `M`-pinned posets. -/
def versEpingle : Adm M ⥤ Epingle M where
  obj X := versEpingleObj hend hsk X.obj ((admissible_iff hmono _).1 X.property)
  map α := versEpingleMap hend hsk _ _ α.hom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

lemma elem_eq_transport {X : Mᵒᵖ ⥤ Type w} {D : M} (q : Elem X) (h : q.1 = D) :
    q = ⟨D, X.map (eqToHom h.symm).op q.2⟩ := by
  obtain ⟨E, y⟩ := q
  subst h
  simp

/-- The component at `D` of the natural transformation a morphism of pinned posets comes from. -/
def appOfHom {X Y : Mᵒᵖ ⥤ Type w} {hX : NonSingulier X} {hY : NonSingulier Y}
    (φ : versEpingleObj hend hsk X hX ⟶ versEpingleObj hend hsk Y hY) (D : M)
    (x : X.obj (op D)) : Y.obj (op D) :=
  Y.map (eqToHom (φ.τ_f ⟨D, x⟩).symm).op (φ.f ⟨D, x⟩).2

lemma f_eq_appOfHom {X Y : Mᵒᵖ ⥤ Type w} {hX : NonSingulier X} {hY : NonSingulier Y}
    (φ : versEpingleObj hend hsk X hX ⟶ versEpingleObj hend hsk Y hY) (p : Elem X) :
    φ.f p = ⟨p.1, appOfHom hend hsk φ p.1 p.2⟩ :=
  elem_eq_transport _ (φ.τ_f p)

lemma appOfHom_naturality {X Y : Mᵒᵖ ⥤ Type w} {hX : NonSingulier X} {hY : NonSingulier Y}
    (φ : versEpingleObj hend hsk X hX ⟶ versEpingleObj hend hsk Y hY) {D D' : M}
    (a : D' ⟶ D) (x : X.obj (op D)) :
    appOfHom hend hsk φ D' (X.map a.op x) = Y.map a.op (appOfHom hend hsk φ D x) := by
  have h := φ.u_f ⟨D, x⟩ ⟨D', a⟩
  change φ.f ⟨D', X.map a.op x⟩ = ⟨D', Y.map (a ≫ eqToHom _).op (φ.f ⟨D, x⟩).2⟩ at h
  rw [f_eq_appOfHom] at h
  obtain ⟨-, h⟩ := Sigma.mk.inj_iff.1 h
  rw [eq_of_heq h, appOfHom, op_comp, Functor.map_comp_apply]
  rfl

include hmono in
instance : (versEpingle hmono hend hsk).Faithful where
  map_injective {X Y α β} h := by
    ext U x
    have := congrFun (congrArg Epingle.Hom.f h) ⟨U.unop, x⟩
    exact eq_of_heq (Sigma.mk.inj_iff.1 this).2

include hmono in
instance : (versEpingle hmono hend hsk).Full where
  map_surjective {X Y} φ := by
    refine ⟨ObjectProperty.homMk
      { app := fun U => TypeCat.ofHom (appOfHom hend hsk
          (hX := (admissible_iff hmono _).1 X.property)
          (hY := (admissible_iff hmono _).1 Y.property) φ U.unop)
        naturality := fun U V g => by
          ext x
          exact appOfHom_naturality hend hsk φ g.unop x }, ?_⟩
    ext p
    exact (f_eq_appOfHom hend hsk φ p).symm

/-- **The presheaf of an `M`-pinned poset**: `X_K(D)` is the set of elements of type `D`, and
`a : D' → D` acts by the pinning, `ξ ↦ u_ξ(D', a)`. -/
def versPrefaisceau (K : Epingle M) : Mᵒᵖ ⥤ Type w where
  obj U := {ξ : K.K // K.τ ξ = U.unop}
  map {U V} g := TypeCat.ofHom fun ξ =>
    ⟨K.u ξ.1 ⟨V.unop, g.unop ≫ eqToHom ξ.2.symm⟩, K.τ_u _ _⟩
  map_id U := by
    ext ⟨ξ, h⟩
    change K.u ξ ⟨U.unop, 𝟙 _ ≫ eqToHom h.symm⟩ = ξ
    obtain ⟨D⟩ := U
    dsimp at h ⊢
    subst h
    simpa using K.u_top ξ
  map_comp {U V W} g g' := by
    ext ⟨ξ, h⟩
    change K.u ξ ⟨W.unop, (g'.unop ≫ g.unop) ≫ eqToHom h.symm⟩ =
      K.u (K.u ξ ⟨V.unop, g.unop ≫ eqToHom h.symm⟩) ⟨W.unop,
        g'.unop ≫ eqToHom (K.τ_u ξ ⟨V.unop, g.unop ≫ eqToHom h.symm⟩).symm⟩
    rw [K.u_u ξ ⟨V.unop, g.unop ≫ eqToHom h.symm⟩ ⟨W.unop, g'.unop⟩, Category.assoc]

lemma versPrefaisceau_nonSingulier (K : Epingle M) : NonSingulier (versPrefaisceau K) := by
  rintro D D' ⟨ξ, h⟩ a b hab
  have := K.u_injective ξ (congrArg Subtype.val hab)
  obtain ⟨-, h'⟩ := Sigma.mk.inj_iff.1 this
  exact (cancel_mono _).1 (eq_of_heq h')

lemma versPrefaisceau_le_iff (K : Epingle M) (p q : Elem (versPrefaisceau K)) :
    (ordreElem hend hsk _).le p q ↔ p.2.1 ≤ q.2.1 := by
  obtain ⟨D, ξ, hξ⟩ := p
  obtain ⟨E, η, hη⟩ := q
  dsimp at hξ hη ⊢
  rw [le_elem_iff]
  constructor
  · rintro ⟨a, ha⟩
    have h1 : K.u η ⟨D, a ≫ eqToHom hη.symm⟩ = ξ := congrArg Subtype.val ha
    rw [← h1, ← Set.mem_Iic, ← K.u_range]
    exact ⟨_, rfl⟩
  · intro hle
    rw [← Set.mem_Iic, ← K.u_range] at hle
    obtain ⟨⟨F, c⟩, hc⟩ := hle
    have hF : F = D := by
      have := K.τ_u η ⟨F, c⟩
      rw [hc] at this
      exact this.symm.trans hξ
    subst hF hξ hη
    refine ⟨c, Subtype.ext ?_⟩
    change K.u η ⟨_, c ≫ 𝟙 _⟩ = ξ
    rw [Category.comp_id, hc]

lemma versPrefaisceau_mk_eq (K : Epingle M) (ζ : K.K) (D : M) (h : K.τ ζ = D) :
    (⟨K.τ ζ, ζ, rfl⟩ : Elem (versPrefaisceau K)) = ⟨D, ζ, h⟩ := by
  subst h
  rfl

/-- `X_K` gives back `K`: the pinned poset of the presheaf of `K` is isomorphic to `K`. -/
def isoVersPrefaisceau (K : Epingle M) :
    versEpingleObj hend hsk (versPrefaisceau K) (versPrefaisceau_nonSingulier K) ≅ K where
  hom :=
    { f := fun p => p.2.1
      strictMono := fun p q hpq => by
        obtain ⟨h1, h2⟩ := lt_iff_le_not_ge.1 hpq
        exact lt_iff_le_not_ge.2 ⟨(versPrefaisceau_le_iff hend hsk K p q).1 h1,
          fun h => h2 ((versPrefaisceau_le_iff hend hsk K q p).2 h)⟩
      τ_f := fun p => p.2.2
      u_f := fun _ _ => rfl }
  inv :=
    { f := fun ξ => ⟨K.τ ξ, ξ, rfl⟩
      strictMono := fun ξ η hξη => by
        obtain ⟨h1, h2⟩ := lt_iff_le_not_ge.1 hξη
        exact lt_iff_le_not_ge.2 ⟨(versPrefaisceau_le_iff hend hsk K _ _).2 h1,
          fun h => h2 ((versPrefaisceau_le_iff hend hsk K _ _).1 h)⟩
      τ_f := fun _ => rfl
      u_f := fun ξ y => by
        rw [versPrefaisceau_mk_eq K (K.u ξ y) y.1 (K.τ_u ξ y)]
        refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
        change K.u ξ y = K.u ξ ⟨y.1, (y.2 ≫ eqToHom _) ≫ eqToHom _⟩
        simp }
  hom_inv_id := by
    ext ⟨D, ξ, h⟩
    exact versPrefaisceau_mk_eq K ξ D h
  inv_hom_id := rfl

include hmono in
instance : (versEpingle hmono hend hsk).EssSurj where
  mem_essImage K :=
    ⟨⟨versPrefaisceau K, (admissible_iff hmono _).2 (versPrefaisceau_nonSingulier K)⟩,
      ⟨isoVersPrefaisceau hend hsk K⟩⟩

include hmono in
/-- **Page 13, « est équivalente à ».** For a skeletal `M` satisfying (i) and (ii), `X ↦ X̃` is
an equivalence between the admissible presheaves on `M` and the `M`-pinned posets. -/
theorem versEpingle_isEquivalence : (versEpingle hmono hend hsk).IsEquivalence where

include hmono hend hsk in
/-- The equivalence of page 13, as an equivalence of categories `𝔹₀ ≌ (M-pinned posets)`. -/
theorem equivalence_page13 : Nonempty (Adm M ≌ Epingle M) :=
  haveI := versEpingle_isEquivalence hmono hend hsk
  ⟨(versEpingle hmono hend hsk).asEquivalence⟩

include hmono in
/-- Page 14: the monomorphisms of `M̂` between admissible presheaves are the morphisms whose
map `X̃ → Ỹ` is injective. -/
theorem mono_iff_injective_versEpingle {X Y : Adm M} (α : X ⟶ Y) :
    Mono α.hom ↔ Function.Injective ((versEpingle hmono hend hsk).map α).f := by
  rw [NatTrans.mono_iff_mono_app]
  simp only [mono_iff_injective]
  constructor
  · rintro h ⟨D, x⟩ ⟨E, y⟩ hxy
    change (⟨D, α.hom.app _ x⟩ : Elem Y.obj) = ⟨E, α.hom.app _ y⟩ at hxy
    obtain ⟨rfl, hxy⟩ := Sigma.mk.inj_iff.1 hxy
    rw [h (op D) (eq_of_heq hxy)]
  · intro h U x y hxy
    have := @h ⟨U.unop, x⟩ ⟨U.unop, y⟩ (by
      change (⟨U.unop, α.hom.app _ x⟩ : Elem Y.obj) = ⟨U.unop, α.hom.app _ y⟩
      rw [hxy])
    exact eq_of_heq (Sigma.mk.inj_iff.1 this).2

/-! ### Page 16: sums and amalgamated sums -/

/-- A presheaf with a morphism to a non-singular one is non-singular; in particular a
sub-object of an admissible object is admissible. -/
lemma nonSingulier_of_hom {Z X : Mᵒᵖ ⥤ Type w} (f : Z ⟶ X) (hX : NonSingulier X) :
    NonSingulier Z := fun _ _ z a b hab =>
  hX (f.app _ z) a b (by rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hab])

include hmono in
/-- **Page 16, sums.** A sum of admissible presheaves is admissible. -/
theorem admissible_coproduit {ι : Type w} (X : ι → Mᵒᵖ ⥤ Type w) (hX : ∀ i, Admissible (X i))
    (c : Cofan X) (hc : IsColimit c) : Admissible c.pt := by
  simp only [admissible_iff hmono] at hX ⊢
  intro D D' p a b hab
  obtain ⟨⟨i⟩, x, rfl⟩ :=
    Types.jointly_surjective_of_isColimit (isColimitOfPreserves ((evaluation _ _).obj (op D)) hc) p
  have hinj := (mono_iff_injective _).1
    ((NatTrans.mono_iff_mono_app _).1 (MonoCoprod.mono_inj X c hc i) (op D'))
  refine hX i x a b (hinj ?_)
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
  exact hab

include hmono in
/-- **Page 16, amalgamated sums.** A pushout of admissible presheaves along monomorphisms is
admissible. -/
theorem admissible_pushout {Z X Y P : Mᵒᵖ ⥤ Type w} {f : Z ⟶ X} {g : Z ⟶ Y} {l : X ⟶ P}
    {r : Y ⟶ P} (h : IsPushout f g l r) [Mono f] [Mono g] (hX : Admissible X)
    (hY : Admissible Y) : Admissible P := by
  rw [admissible_iff hmono] at hX hY ⊢
  have hl : Mono l := Adhesive.mono_of_isPushout_of_mono_right h
  have hr : Mono r := Adhesive.mono_of_isPushout_of_mono_left h
  intro D D' p a b hab
  rcases Types.eq_or_eq_of_isPushout (h.map ((evaluation _ _).obj (op D))) p with
    ⟨x, rfl⟩ | ⟨y, rfl⟩
  · refine hX x a b ((mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hl (op D')) ?_)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact hab
  · refine hY y a b ((mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hr (op D')) ?_)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact hab

include hmono in
/-- **Page 16, « le foncteur `X ↦ X̃` commute à ces opérations », sums.** The sum, computed in
`M̂`, of admissible presheaves is a sum in `𝔹₀`, and `X ↦ X̃` sends it to a sum of pinned
posets. -/
theorem versEpingle_coproduit {ι : Type w} (X : ι → Adm M) (c : Cofan fun i => (X i).obj)
    (hc : IsColimit c) :
    Nonempty (IsColimit ((versEpingle hmono hend hsk).mapCocone
      (Cofan.mk (⟨c.pt, admissible_coproduit hmono _ (fun i => (X i).property) c hc⟩ : Adm M)
        fun i => ObjectProperty.homMk (c.inj i)))) := by
  have := versEpingle_isEquivalence hmono hend hsk
  refine ⟨isColimitOfPreserves _ (Cofan.IsColimit.mk _
    (fun s => ObjectProperty.homMk (Cofan.IsColimit.desc hc fun i => (s.inj i).hom))
    (fun s i => ?_) (fun s m hm => ?_))⟩
  · ext1
    exact Cofan.IsColimit.fac hc _ i
  · ext1
    refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    change _ = c.inj i ≫ Cofan.IsColimit.desc hc _
    rw [Cofan.IsColimit.fac]
    exact congrArg InducedCategory.Hom.hom (hm i)

include hmono in
/-- **Page 16, amalgamated sums.** A pushout in `M̂` of admissible presheaves along
monomorphisms is a pushout in `𝔹₀`, and `X ↦ X̃` sends it to a pushout of pinned posets. -/
theorem versEpingle_pushout {Z X Y P : Adm M} {f : Z ⟶ X} {g : Z ⟶ Y} {l : X ⟶ P}
    {r : Y ⟶ P} (h : IsPushout f.hom g.hom l.hom r.hom) :
    IsPushout ((versEpingle hmono hend hsk).map f) ((versEpingle hmono hend hsk).map g)
      ((versEpingle hmono hend hsk).map l) ((versEpingle hmono hend hsk).map r) := by
  have := versEpingle_isEquivalence hmono hend hsk
  exact (IsPushout.of_map (ObjectProperty.ι _) (by ext1; exact h.w) h).map _

end Prefaisceaux

end Grothendieck.Folder104
