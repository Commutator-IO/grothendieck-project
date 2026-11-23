/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Ring.RingNF

/-!
# Grothendieck topologies on the free category of a cyclic quiver

Let `CyclicQuiver n` be the quiver with vertices `ZMod n` and one arrow `i ⟶ i + 1` for each
vertex `i`. Its representations in sets are the functors `Paths (CyclicQuiver n) ⥤ Type`, that
is, the presheaves on the opposite category `CyclicSite n := (Paths (CyclicQuiver n))ᵒᵖ`. We
classify the Grothendieck topologies on `CyclicSite n`, whose sheaf topoi are the subtopoi of the
topos of representations of the cyclic quiver.

A morphism `op w ⟶ op v` of `CyclicSite n` is a path `v ⟶ w` of the cyclic quiver; there is
exactly one path of each length `k` out of `v`, ending at `v + k` (`exists_hom`, `hom_ext`).
Hence the sieves on `op v` are `⊥` and the sieves `lengthSieve (op v) k` of the morphisms of
length at least `k` (`eq_bot_or_eq_lengthSieve`), and the pullback of `lengthSieve _ k` along a
morphism of length `m` is `lengthSieve _ (k - m)` (`pullback_lengthSieve`).

For `Z : Set (ZMod n)`, the topology `topologyOf Z` declares a sieve on `op v` covering when it
contains the morphisms of length at least `m`, for some `m` such that none of
`v, v + 1, …, v + m - 1` lies in `Z`. Thus `lengthSieve (op v) k` covers exactly when
`k ≤ K_Z(v)`, the distance from `v` to the next element of `Z` going forward
(`lengthSieve_mem_topologyOf_iff`), and `⊥` never covers. We prove:

* `eq_top_or_eq_topologyOf`: every Grothendieck topology on `CyclicSite n` (for `n ≠ 0`) is
  either the degenerate topology `⊤`, in which the empty sieve covers, or `topologyOf Z` for a
  unique `Z`, the set of vertices `v` at which `lengthSieve (op v) 1` does not cover;
* `topologyEquiv : Option (Set (ZMod n)) ≃ GrothendieckTopology (CyclicSite n)`;
* `card_grothendieckTopology`: there are exactly `2 ^ n + 1` Grothendieck topologies, and three
  for the monoid `ℕ` seen as the free category on one loop (`card_grothendieckTopology_one`).

## Proof

If the empty sieve covers some vertex, it covers every vertex since the cyclic quiver is strongly
connected and `⊥` is stable under pullback, so the topology is `⊤`. Otherwise the stability
under pullback gives `K(v + 1) ≥ K(v) - 1`, and transitivity shows that a vertex `v` with
`lengthSieve (op (v + j)) 1` covering for all `j < m` is covered by `lengthSieve (op v) m`
(`lengthSieve_mem_of_forall`), by induction on `m`.

The description of the sheaves for `topologyOf Z` (representations whose maps out of the vertices
outside `Z` are bijective) is not formalised here.
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory Opposite

/-- The vertices of the cyclic quiver on `n` vertices. -/
def CyclicQuiver (n : ℕ) : Type := ZMod n

namespace CyclicQuiver

variable {n : ℕ}

/-- The vertex of `ZMod n` underlying a vertex of the cyclic quiver. -/
def val (a : CyclicQuiver n) : ZMod n := a

/-- The vertex of the cyclic quiver attached to an element of `ZMod n`. -/
def mk (a : ZMod n) : CyclicQuiver n := a

@[simp]
theorem val_mk (a : ZMod n) : val (mk a) = a := rfl

theorem val_injective : Function.Injective (val : CyclicQuiver n → ZMod n) := fun _ _ h => h

/-- The cyclic quiver has exactly one arrow `i ⟶ i + 1` out of each vertex `i`. -/
instance : Quiver (CyclicQuiver n) where
  Hom i j := PLift (val j = val i + 1)

/-- The arrow `a ⟶ a + 1` of the cyclic quiver. -/
def arrow (a : CyclicQuiver n) : a ⟶ mk (val a + 1) := ⟨rfl⟩

theorem arrow_eq {a b : CyclicQuiver n} (e : a ⟶ b) : val b = val a + 1 := e.down

theorem arrow_ext {a b : CyclicQuiver n} (e e' : a ⟶ b) : e = e' := by
  cases e; cases e'; rfl

/-- The target of a path of the cyclic quiver is its source plus its length. -/
theorem target_eq {a b : CyclicQuiver n} (p : Quiver.Path a b) :
    val b = val a + p.length := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Quiver.Path.length_cons, arrow_eq e, ih]
    push_cast
    ring

/-- There is a path of every length out of each vertex of the cyclic quiver. -/
theorem exists_path (a : CyclicQuiver n) (m : ℕ) :
    ∃ (b : CyclicQuiver n) (p : Quiver.Path a b), p.length = m := by
  induction m with
  | zero => exact ⟨a, Quiver.Path.nil, rfl⟩
  | succ m ih =>
    obtain ⟨b, p, hp⟩ := ih
    exact ⟨_, p.cons (arrow b), by rw [Quiver.Path.length_cons, hp]⟩

/-- Two paths of the cyclic quiver with the same endpoints and the same length are equal. -/
theorem path_ext {a b : CyclicQuiver n} (p : Quiver.Path a b) :
    ∀ q : Quiver.Path a b, p.length = q.length → p = q := by
  induction p with
  | nil =>
    intro q h
    exact (Quiver.Path.eq_nil_of_length_zero q h.symm).symm
  | @cons c b p e ih =>
    intro q h
    cases q with
    | nil => simp at h
    | @cons c' _ q e' =>
      simp only [Quiver.Path.length_cons, Nat.add_right_cancel_iff] at h
      obtain rfl : c = c' := val_injective (by rw [target_eq p, target_eq q, h])
      obtain rfl := ih q h
      rw [arrow_ext e e']

end CyclicQuiver

/-- The site whose presheaves are the representations of the cyclic quiver: the opposite of the
free category on `CyclicQuiver n`. -/
abbrev CyclicSite (n : ℕ) : Type := (Paths (CyclicQuiver n))ᵒᵖ

namespace CyclicSite

open CyclicQuiver

variable {n : ℕ}

/-- The object of `CyclicSite n` attached to a vertex. -/
def vtx (a : ZMod n) : CyclicSite n := op (show Paths (CyclicQuiver n) from mk a)

/-- The vertex of an object of `CyclicSite n`. -/
def vert (X : CyclicSite n) : ZMod n := val (show CyclicQuiver n from unop X)

@[simp]
theorem vert_vtx (a : ZMod n) : vert (vtx a) = a := rfl

/-- The path of the cyclic quiver underlying a morphism of `CyclicSite n`. -/
def toPath {X Y : CyclicSite n} (f : X ⟶ Y) :
    @Quiver.Path (CyclicQuiver n) _ (unop Y) (unop X) := f.unop

/-- The length of a morphism of `CyclicSite n`, the length of the underlying path. -/
def len {X Y : CyclicSite n} (f : X ⟶ Y) : ℕ := (toPath f).length

@[simp]
theorem len_id (X : CyclicSite n) : len (𝟙 X) = 0 := rfl

@[simp]
theorem len_comp {X Y Z : CyclicSite n} (f : X ⟶ Y) (g : Y ⟶ Z) :
    len (f ≫ g) = len f + len g := by
  change ((toPath g).comp (toPath f)).length = _
  rw [Quiver.Path.length_comp]
  exact Nat.add_comm _ _

/-- The vertex of the source of a morphism is the vertex of its target plus its length. -/
theorem vert_eq {X Y : CyclicSite n} (f : X ⟶ Y) : vert X = vert Y + len f :=
  target_eq _

/-- Two morphisms of `CyclicSite n` with the same length are equal. -/
theorem hom_ext {X Y : CyclicSite n} (f g : X ⟶ Y) (h : len f = len g) : f = g :=
  Quiver.Hom.unop_inj (path_ext (toPath f) (toPath g) h)

/-- There is a morphism of length `m` from `X` to `Y` when the vertex of `X` is the vertex of `Y`
plus `m`. -/
theorem exists_hom (X Y : CyclicSite n) (m : ℕ) (h : vert X = vert Y + m) :
    ∃ f : X ⟶ Y, len f = m := by
  obtain ⟨y⟩ := Y
  obtain ⟨b, p, hp⟩ := exists_path (show CyclicQuiver n from y) m
  obtain ⟨x⟩ := X
  obtain rfl : (show CyclicQuiver n from x) = b :=
    val_injective (by rw [target_eq p, hp]; exact h)
  exact ⟨Quiver.Hom.op (show y ⟶ x from p), hp⟩

/-- A morphism `g` into `X` factors through every morphism `f` into `X` of smaller length. -/
theorem exists_comp_eq {W Y X : CyclicSite n} (f : Y ⟶ X) (g : W ⟶ X) (h : len f ≤ len g) :
    ∃ k : W ⟶ Y, k ≫ f = g := by
  obtain ⟨k, hk⟩ := exists_hom W Y (len g - len f) (by
    rw [vert_eq g, vert_eq f, Nat.cast_sub h]
    ring)
  exact ⟨k, hom_ext _ _ (by rw [len_comp, hk]; omega)⟩

/-- The sieve on `X` of the morphisms of length at least `k`. -/
def lengthSieve (X : CyclicSite n) (k : ℕ) : Sieve X where
  arrows _ f := k ≤ len f
  downward_closed {Y Z f} hf g := by
    rw [len_comp]
    exact le_add_left hf

@[simp]
theorem lengthSieve_apply {X Y : CyclicSite n} (k : ℕ) (f : Y ⟶ X) :
    lengthSieve X k f ↔ k ≤ len f := Iff.rfl

@[simp]
theorem lengthSieve_zero (X : CyclicSite n) : lengthSieve X 0 = ⊤ := by
  ext Y f
  simp

/-- The pullback of `lengthSieve X k` along a morphism of length `m` is
`lengthSieve Y (k - m)`. -/
theorem pullback_lengthSieve {X Y : CyclicSite n} (k : ℕ) (f : Y ⟶ X) :
    (lengthSieve X k).pullback f = lengthSieve Y (k - len f) := by
  ext Z g
  simp only [Sieve.pullback_apply, lengthSieve_apply, len_comp]
  omega

theorem lengthSieve_le_iff (X : CyclicSite n) (m k : ℕ) :
    lengthSieve X m ≤ lengthSieve X k ↔ k ≤ m := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ := exists_hom (vtx (vert X + (m : ZMod n))) X m rfl
    have := h _ (show lengthSieve X m f from hf.ge)
    rwa [lengthSieve_apply, hf] at this
  · intro h Y f hf
    exact h.trans hf

/-- The sieves of `CyclicSite n` are `⊥` and the sieves `lengthSieve X k`. -/
theorem eq_bot_or_eq_lengthSieve {X : CyclicSite n} (S : Sieve X) :
    S = ⊥ ∨ ∃ k, S = lengthSieve X k := by
  classical
  by_cases hS : ∃ (Y : CyclicSite n) (f : Y ⟶ X), S f
  · right
    have hP : ∃ m, ∃ (Y : CyclicSite n) (f : Y ⟶ X), S f ∧ len f = m :=
      let ⟨Y, f, hf⟩ := hS; ⟨_, Y, f, hf, rfl⟩
    refine ⟨Nat.find hP, ?_⟩
    ext Y g
    refine ⟨fun hg => Nat.find_min' hP ⟨Y, g, hg, rfl⟩, fun hg => ?_⟩
    obtain ⟨Y₀, f₀, hf₀, hlen⟩ := Nat.find_spec hP
    obtain ⟨k, rfl⟩ := exists_comp_eq f₀ g (by rw [hlen]; exact hg)
    exact S.downward_closed hf₀ k
  · left
    ext Y f
    exact iff_of_false (fun hf => hS ⟨Y, f, hf⟩) (fun h => h)

/-- The empty sieve of `CyclicSite n` is not `lengthSieve X m`. -/
theorem lengthSieve_ne_bot (X : CyclicSite n) (m : ℕ) : ¬ lengthSieve X m ≤ ⊥ := by
  intro h
  obtain ⟨f, hf⟩ := exists_hom (vtx (vert X + (m : ZMod n))) X m rfl
  exact h _ (show lengthSieve X m f from hf.ge)

/-! ### The topologies `topologyOf Z` -/

/-- The sieves covering `X` for the topology attached to `Z`: those containing the morphisms of
length at least `m`, for some `m` such that none of the vertices `v, …, v + m - 1` lies in `Z`,
where `v` is the vertex of `X`. -/
def CoversOf (Z : Set (ZMod n)) {X : CyclicSite n} (S : Sieve X) : Prop :=
  ∃ m : ℕ, (∀ j : ℕ, j < m → vert X + (j : ZMod n) ∉ Z) ∧ lengthSieve X m ≤ S

/-- The Grothendieck topology on `CyclicSite n` attached to a set `Z` of vertices: the sieve of
the morphisms of length at least `k` into the vertex `v` covers exactly when the next element of
`Z` after `v`, going forward, is at distance at least `k`. -/
def topologyOf (Z : Set (ZMod n)) : GrothendieckTopology (CyclicSite n) where
  sieves X := {S | CoversOf Z S}
  top_mem' X := ⟨0, by simp, le_top⟩
  pullback_stable' X Y S f := by
    rintro ⟨m, hZ, hS⟩
    refine ⟨m - len f, fun j hj => ?_, ?_⟩
    · rw [vert_eq f, add_assoc, ← Nat.cast_add]
      exact hZ _ (by omega)
    · rw [← pullback_lengthSieve]
      exact Sieve.pullback_monotone f hS
  transitive' X S := by
    rintro ⟨m, hZ, hS⟩ R hR
    obtain ⟨f, hf⟩ := exists_hom (vtx (vert X + (m : ZMod n))) X m rfl
    obtain ⟨m', hZ', hR'⟩ := hR (hS _ (show lengthSieve X m f from hf.ge))
    refine ⟨m + m', fun j hj => ?_, fun W g hg => ?_⟩
    · by_cases hjm : j < m
      · exact hZ j hjm
      · have := hZ' (j - m) (by omega)
        rwa [vert_vtx, add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' (by omega)] at this
    · obtain ⟨k, rfl⟩ := exists_comp_eq f g (by rw [hf]; exact le_of_add_le_left hg)
      apply hR'
      rw [lengthSieve_apply, len_comp, hf] at hg
      exact le_of_add_le_add_right (by omega : m' + m ≤ len k + m)

theorem mem_topologyOf_iff (Z : Set (ZMod n)) {X : CyclicSite n} (S : Sieve X) :
    S ∈ topologyOf Z X ↔
      ∃ m : ℕ, (∀ j : ℕ, j < m → vert X + (j : ZMod n) ∉ Z) ∧ lengthSieve X m ≤ S :=
  Iff.rfl

/-- For the topology attached to `Z`, the sieve of the morphisms of length at least `k` into
`X` covers exactly when none of `v, v + 1, …, v + k - 1` lies in `Z`, where `v` is the vertex of
`X`: that is, when `k` is at most the distance from `v` to the next element of `Z`. -/
theorem lengthSieve_mem_topologyOf_iff (Z : Set (ZMod n)) (X : CyclicSite n) (k : ℕ) :
    lengthSieve X k ∈ topologyOf Z X ↔ ∀ j : ℕ, j < k → vert X + (j : ZMod n) ∉ Z := by
  refine ⟨fun ⟨m, hZ, hS⟩ j hj => hZ j (hj.trans_le ((lengthSieve_le_iff X m k).1 hS)),
    fun h => ⟨k, h, le_rfl⟩⟩

/-- The empty sieve never covers for the topology attached to `Z`. -/
theorem bot_notMem_topologyOf (Z : Set (ZMod n)) (X : CyclicSite n) :
    (⊥ : Sieve X) ∉ topologyOf Z X :=
  fun ⟨m, _, hS⟩ => lengthSieve_ne_bot X m hS

/-- The set of vertices `v` at which the sieve of the morphisms of length at least `1` does not
cover, for a Grothendieck topology on `CyclicSite n`. -/
def zeroSet (J : GrothendieckTopology (CyclicSite n)) : Set (ZMod n) :=
  {v | lengthSieve (vtx v) 1 ∉ J (vtx v)}

theorem zeroSet_topologyOf (Z : Set (ZMod n)) : zeroSet (topologyOf Z) = Z := by
  ext v
  simp only [zeroSet, Set.mem_ofPred_eq, lengthSieve_mem_topologyOf_iff, vert_vtx]
  constructor
  · intro h
    by_contra hv
    refine h fun j hj => ?_
    obtain rfl : j = 0 := by omega
    simpa using hv
  · intro hv h
    exact h 0 one_pos (by simpa using hv)

/-! ### Classification -/

/-- If the sieves of the morphisms of length at least `1` into the vertices `v, …, v + m - 1`
cover them, then the sieve of the morphisms of length at least `m` into `v` covers `v`. -/
theorem lengthSieve_mem_of_forall (J : GrothendieckTopology (CyclicSite n)) (X : CyclicSite n)
    (m : ℕ) (h : ∀ j : ℕ, j < m → vert X + (j : ZMod n) ∉ zeroSet J) :
    lengthSieve X m ∈ J X := by
  induction m with
  | zero => simp
  | succ m ih =>
    refine J.transitive (ih fun j hj => h j (by omega)) _ fun Y f hf => ?_
    rw [pullback_lengthSieve]
    rcases (lengthSieve_apply _ _).1 hf |>.eq_or_lt with hlen | hlen
    · have hY : vert Y ∉ zeroSet J := by
        rw [vert_eq f, ← hlen]
        exact h m (by omega)
      have hY : lengthSieve Y 1 ∈ J Y := not_not.1 hY
      rwa [← hlen, Nat.add_sub_cancel_left]
    · rw [Nat.sub_eq_zero_of_le hlen, lengthSieve_zero]
      exact J.top_mem Y

/-- A Grothendieck topology on `CyclicSite n` in which the empty sieve does not cover is the
topology attached to its `zeroSet`. -/
theorem eq_topologyOf_zeroSet {J : GrothendieckTopology (CyclicSite n)}
    (h : ∀ X : CyclicSite n, (⊥ : Sieve X) ∉ J X) : J = topologyOf (zeroSet J) := by
  refine GrothendieckTopology.ext (funext fun X => Set.ext fun S => ⟨fun hS => ?_, ?_⟩)
  · rcases eq_bot_or_eq_lengthSieve S with rfl | ⟨k, rfl⟩
    · exact absurd hS (h X)
    refine ⟨k, fun j hj => ?_, le_rfl⟩
    obtain ⟨g, hg⟩ := exists_hom (vtx (vert X + (j : ZMod n))) X j rfl
    have := J.pullback_stable g hS
    rw [pullback_lengthSieve, hg] at this
    exact not_not.2 (J.superset_covering ((lengthSieve_le_iff _ _ _).2 (by omega)) this)
  · rintro ⟨m, hZ, hS⟩
    exact J.superset_covering hS (lengthSieve_mem_of_forall J X m hZ)

theorem topologyOf_ne_top (Z : Set (ZMod n)) : topologyOf Z ≠ ⊤ := fun h =>
  bot_notMem_topologyOf Z (vtx 0) (h ▸ GrothendieckTopology.top_covering)

theorem topologyOf_injective : Function.Injective (topologyOf : Set (ZMod n) → _) :=
  fun Z Z' h => by rw [← zeroSet_topologyOf Z, h, zeroSet_topologyOf]

variable [NeZero n]

/-- If the empty sieve covers some object, every sieve covers every object. -/
theorem eq_top_of_bot_mem {J : GrothendieckTopology (CyclicSite n)} {X : CyclicSite n}
    (h : (⊥ : Sieve X) ∈ J X) : J = ⊤ := by
  refine GrothendieckTopology.ext (funext fun Y => Set.eq_univ_of_forall fun S => ?_)
  obtain ⟨f, -⟩ := exists_hom Y X (vert Y - vert X).val
    (by rw [ZMod.natCast_zmod_val]; ring)
  refine J.superset_covering bot_le ?_
  simpa [Sieve.pullback_bot] using J.pullback_stable f h

/-- Every Grothendieck topology on the opposite of the free category of the cyclic quiver is
either the degenerate topology `⊤`, in which the empty sieve covers, or the topology attached to
a set of vertices. -/
theorem eq_top_or_eq_topologyOf (J : GrothendieckTopology (CyclicSite n)) :
    J = ⊤ ∨ ∃ Z : Set (ZMod n), J = topologyOf Z := by
  by_cases h : ∃ X : CyclicSite n, (⊥ : Sieve X) ∈ J X
  · obtain ⟨X, hX⟩ := h
    exact Or.inl (eq_top_of_bot_mem hX)
  · exact Or.inr ⟨_, eq_topologyOf_zeroSet fun X hX => h ⟨X, hX⟩⟩

/-- The Grothendieck topologies on `CyclicSite n` are in bijection with `Option (Set (ZMod n))`:
`none` gives the degenerate topology and `some Z` the topology attached to `Z`. -/
noncomputable def topologyEquiv : Option (Set (ZMod n)) ≃ GrothendieckTopology (CyclicSite n) :=
  Equiv.ofBijective (fun o => o.elim ⊤ topologyOf) ⟨by
    rintro (_ | Z) (_ | Z') h
    · rfl
    · exact absurd h.symm (topologyOf_ne_top Z')
    · exact absurd h (topologyOf_ne_top Z)
    · exact congrArg some (topologyOf_injective h), fun J => by
    rcases eq_top_or_eq_topologyOf J with rfl | ⟨Z, rfl⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some Z, rfl⟩⟩

@[simp]
theorem topologyEquiv_none : topologyEquiv (n := n) none = ⊤ := rfl

@[simp]
theorem topologyEquiv_some (Z : Set (ZMod n)) : topologyEquiv (some Z) = topologyOf Z := rfl

/-- There are exactly `2 ^ n + 1` Grothendieck topologies on the opposite of the free category
of the cyclic quiver on `n ≥ 1` vertices. -/
theorem card_grothendieckTopology : Nat.card (GrothendieckTopology (CyclicSite n)) = 2 ^ n + 1 := by
  rw [← Nat.card_congr topologyEquiv, Finite.card_option, Nat.card_eq_fintype_card,
    Fintype.card_set, ZMod.card]

end CyclicSite

/-- There are exactly three Grothendieck topologies on the opposite of the free category on one
loop, the monoid `ℕ`: the trivial, the dense and the degenerate topology. -/
theorem CyclicSite.card_grothendieckTopology_one :
    Nat.card (GrothendieckTopology (CyclicSite 1)) = 3 :=
  CyclicSite.card_grothendieckTopology

end LeanPool.ToposTheoreticBridges.Examples
