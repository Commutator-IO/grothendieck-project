import Mathlib

/-!
# Folder 118, page 35: stability of `𝒲_A` under products without asphericity

The modernised reading `transcripts/118/118.modern.tex` (« Le lemme des pages 32 à 35 »)
shows that for a small category `A`, (i) « `A` totally aspherical » is equivalent to (ii)
« `𝒲_A` stable under finite products » plus « `A` aspherical », and asks on page 35
whether a connected `A` satisfying (ii) must be aspherical. The page answers « Non »:
for `A` a groupoid, `𝒲_A` consists of the isomorphisms only (for the usual weak
equivalences), hence is stable under finite products, while `A` is not aspherical. The
reading takes `A = BG` connected with `G ≠ 1`. This is the reachable part of finding
`118-groupoid-products-not-totally-aspherical` of `src/content/findings.ts`.

What is formalised, in a 1-truncated model. Presheaves on `BG` are `G`-sets, and for a
`G`-set `X` the category `A/X` is the action groupoid `X//G`. A functor between groupoids
is a weak equivalence (of nerves) iff it is bijective on connected components and an
isomorphism on automorphism groups; for the functor `X//G → Y//G` induced by a map `f` of
`G`-sets, this says that `f` is bijective on orbits and `Stab(f x) = Stab(x)`. That
characterisation of weak equivalences of groupoids is taken as the definition (`IsWeq`), not
proved; similarly `X//G` is aspherical iff it is connected with trivial automorphism groups
(`Aspherical`).

* `isWeq_iff_bijective`: `f ∈ 𝒲_A` iff `f` is bijective — the reading's reason
  (« a map of `G`-sets bijective on orbits and an isomorphism on stabilisers is an
  isomorphism »), and its converse.
* `isWeq_prod`, `isWeq_pi`: `𝒲_A` is stable under binary products and under products of
  any family, finite or not.
* `not_aspherical_point`, `not_aspherical_regular_prod`: for `G ≠ 1`, `A = A/e` is not
  aspherical, nor is `a × a` for the representable `a` (the regular `G`-set).
* `answer_page_35`: the three together.
-/

namespace Grothendieck.Folder118

open MulAction

variable (G : Type*) [Group G]

/-- `f : X → Y` is in `𝒲_A`, `A = BG`, read through the action groupoids: bijective on
orbits, and `Stab(f x) ⊆ Stab(x)` (the other inclusion always holds). -/
def IsWeq {X Y : Type*} [MulAction G X] [MulAction G Y] (f : X →[G] Y) : Prop :=
  (∀ y : Y, ∃ (x : X) (g : G), g • f x = y) ∧
  (∀ (x x' : X) (g : G), g • f x = f x' → ∃ h : G, h • x = x') ∧
  (∀ (x : X) (g : G), g • f x = f x → g • x = x)

/-- `X//G` is aspherical: non-empty, connected, with trivial automorphism groups. -/
def Aspherical (X : Type*) [MulAction G X] : Prop :=
  Nonempty X ∧ (∀ x y : X, ∃ g : G, g • x = y) ∧ ∀ (x : X) (g : G), g • x = x → g = 1

variable {G}

/-- **Page 35**: for `A = BG`, `𝒲_A` consists of the isomorphisms. -/
theorem isWeq_iff_bijective {X Y : Type*} [MulAction G X] [MulAction G Y] (f : X →[G] Y) :
    IsWeq G f ↔ Function.Bijective f := by
  constructor
  · rintro ⟨hs, hi, hst⟩
    refine ⟨fun x x' hxx => ?_, fun y => ?_⟩
    · obtain ⟨h, rfl⟩ := hi x x' 1 (by rw [one_smul, hxx])
      have : h • f x = f x := by rw [← map_smul, hxx]
      rw [hst x h this]
    · obtain ⟨x, g, rfl⟩ := hs y
      exact ⟨g • x, map_smul f g x⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun y => ?_, fun x x' g hg => ⟨g, hinj (by rw [map_smul, hg])⟩,
      fun x g hg => hinj (by rw [map_smul, hg])⟩
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, 1, one_smul _ _⟩

/-- The product of two maps of `G`-sets. -/
def prodHom {X Y X' Y' : Type*} [MulAction G X] [MulAction G Y] [MulAction G X']
    [MulAction G Y'] (f : X →[G] Y) (f' : X' →[G] Y') : X × X' →[G] Y × Y' where
  toFun p := (f p.1, f' p.2)
  map_smul' g p := by simp [map_smul]

/-- `𝒲_A` is stable under binary products (condition (ii)). -/
theorem isWeq_prod {X Y X' Y' : Type*} [MulAction G X] [MulAction G Y] [MulAction G X']
    [MulAction G Y'] {f : X →[G] Y} {f' : X' →[G] Y'} (hf : IsWeq G f) (hf' : IsWeq G f') :
    IsWeq G (prodHom f f') := by
  rw [isWeq_iff_bijective] at *
  exact hf.prodMap hf'

/-- The product of a family of maps of `G`-sets. -/
def piHom {ι : Type*} {X Y : ι → Type*} [∀ i, MulAction G (X i)] [∀ i, MulAction G (Y i)]
    (f : ∀ i, X i →[G] Y i) : (∀ i, X i) →[G] (∀ i, Y i) where
  toFun x i := f i (x i)
  map_smul' g x := by funext i; simp [map_smul]

/-- `𝒲_A` is stable under products of any family, finite or not. -/
theorem isWeq_pi {ι : Type*} {X Y : ι → Type*} [∀ i, MulAction G (X i)]
    [∀ i, MulAction G (Y i)] {f : ∀ i, X i →[G] Y i} (hf : ∀ i, IsWeq G (f i)) :
    IsWeq G (piHom f) := by
  rw [isWeq_iff_bijective]
  simp only [isWeq_iff_bijective] at hf
  exact Function.Bijective.piMap hf

/-- `A = A/e` is not aspherical when `G ≠ 1`. -/
theorem not_aspherical_point [Nontrivial G] : ¬ Aspherical G PUnit := by
  rintro ⟨-, -, h⟩
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact hg (h PUnit.unit g rfl)

/-- `a × a` is not aspherical for the representable `a`, the regular `G`-set, when
`G ≠ 1`: `(1, 1)` and `(1, g)` lie in different orbits. -/
theorem not_aspherical_regular_prod [Nontrivial G] : ¬ Aspherical G (G × G) := by
  rintro ⟨-, h, -⟩
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  obtain ⟨g, hg⟩ := h (1, 1) (1, a)
  simp only [Prod.smul_mk, smul_eq_mul, mul_one, Prod.mk.injEq] at hg
  exact ha (hg.2.symm.trans hg.1)

/-- **The answer « Non » of page 35**, for `A = BG`, `G ≠ 1`: `𝒲_A` is stable under
products, but neither `A` nor `a × a` is aspherical. -/
theorem answer_page_35 [Nontrivial G] :
    (∀ {X Y X' Y' : Type} [MulAction G X] [MulAction G Y] [MulAction G X'] [MulAction G Y']
      (f : X →[G] Y) (f' : X' →[G] Y'), IsWeq G f → IsWeq G f' → IsWeq G (prodHom f f')) ∧
    ¬ Aspherical G PUnit ∧ ¬ Aspherical G (G × G) :=
  ⟨fun _ _ hf hf' => isWeq_prod hf hf', not_aspherical_point, not_aspherical_regular_prod⟩

end Grothendieck.Folder118
