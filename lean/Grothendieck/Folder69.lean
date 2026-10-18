import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.VecNotation

/-!
# Folder 69, pages 25–26: the automorphisms of the 27-line graph fixing a triangle

The modernised reading `transcripts/69/69.modern.tex` (§ 9, « Un triangle marqué »,
pages 25 to 31) describes the graph `C` of the twenty-seven lines of a cubic surface
(two lines joined when they meet) with a marked triangle `t`, and states as a
corollary of the description (page 26)

> `1 → Ψ̃ → W_t → 𝔖_t × 𝔖_{V*} → 1`, `card W_t = 32 · 36 = 1152 = 51 840 / 45`,

`W_t` being the group of automorphisms of `(C, t)`; page 25 gives the subgroup `W'_t`
fixing `t` pointwise, of order `192`.

This is the reachable part of finding `69-triangle-q8-baer-torsor` of
`src/content/findings.ts`: the order, by a finite computation on the graph. Proving it
says only that the count holds; whether the description by a `Q₈`-Baer torsor is in the
literature is a separate question.

What is formalised. The vertices are `Fin 27`: `aᵢ = i`, `bᵢ = 6 + i` (`0 ≤ i < 6`) and
`c_{ij} = 12 + k` for the `k`-th pair `i < j` in lexicographic order; `aᵢ` meets `bⱼ`
iff `i ≠ j`, `aᵢ` and `bᵢ` meet `c_{jk}` iff `i ∈ {j, k}`, `c_{ij}` meets `c_{kl}` iff
`{i, j} ∩ {k, l} = ∅`. The triangle is `t = {a₀, b₁, c₀₁}`.

* `card_Wt`: the permutations of the vertices preserving the graph and `t` form a group
  of order `1152`; `card_aut`: the same for the graph automorphisms `C ≃g C` preserving
  `t`.
* `card_pointwise`: those fixing `t` pointwise form a group of order `192`.
* `degree_eq` (every line meets ten others) and `isTriangle_t`.

The proof is a stabiliser chain: the base `a₀, b₁, a₁, a₂, a₃, a₄` has orbits of sizes
`3, 2, 8, 4, 3, 2` (`3 · 2 · 8 · 4 · 3 · 2 = 1152`); each orbit is contained in the set
of vertices with the same incidences with the points already fixed, and exhausted by
explicit automorphisms (`g0_7`, …, `g5_5`), checked by the kernel; an automorphism
fixing the base fixes everything, since the base separates the vertices.
-/

namespace Grothendieck.Folder69

open Equiv

/-- The fifteen pairs `i < j` of `{0, …, 5}`, in lexicographic order. -/
def pairs : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4),
    (2, 5), (3, 4), (3, 5), (4, 5)]

/-- The pair of `c_{ij}`. -/
def cp (v : Fin 27) : ℕ × ℕ := pairs.getD (v.val - 12) (0, 0)

/-- Do two of the twenty-seven lines meet? -/
def meets (u v : Fin 27) : Bool :=
  if u.val < 12 ∧ v.val < 12 then
    (u.val < 6 ∧ 6 ≤ v.val ∧ u.val + 6 ≠ v.val) || (v.val < 6 ∧ 6 ≤ u.val ∧ v.val + 6 ≠ u.val)
  else if u.val < 12 then (cp v).1 = u.val % 6 || (cp v).2 = u.val % 6
  else if v.val < 12 then (cp u).1 = v.val % 6 || (cp u).2 = v.val % 6
  else (cp u).1 ≠ (cp v).1 ∧ (cp u).1 ≠ (cp v).2 ∧ (cp u).2 ≠ (cp v).1 ∧ (cp u).2 ≠ (cp v).2

/-- The graph `C` of the twenty-seven lines. -/
def C : SimpleGraph (Fin 27) where
  Adj u v := meets u v = true
  symm := ⟨fun u v h =>
    ((show ∀ u v : Fin 27, meets u v = meets v u by decide +kernel) u v).symm.trans h⟩
  loopless := ⟨fun u h => by
    rw [(show ∀ u : Fin 27, meets u u = false by decide +kernel) u] at h
    exact Bool.false_ne_true h⟩

instance : DecidableRel C.Adj := fun u v => inferInstanceAs (Decidable (meets u v = true))

/-- The marked triangle `t = {a₀, b₁, c₀₁}`. -/
def t : Finset (Fin 27) := {0, 7, 12}

theorem isTriangle_t : C.Adj 0 7 ∧ C.Adj 0 12 ∧ C.Adj 7 12 := by decide +kernel

theorem degree_eq (v : Fin 27) : (Finset.univ.filter (C.Adj v)).card = 10 := by
  revert v; decide +kernel

/-- `W_t`: the permutations preserving the graph and the triangle. -/
def Wt : Subgroup (Perm (Fin 27)) where
  carrier := {σ | (∀ u v, meets (σ u) (σ v) = meets u v) ∧ ∀ v, σ v ∈ t ↔ v ∈ t}
  mul_mem' := by
    rintro σ τ ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨fun u v => (h1 _ _).trans (h3 u v), fun v => (h2 _).trans (h4 v)⟩
  one_mem' := ⟨fun _ _ => rfl, fun _ => Iff.rfl⟩
  inv_mem' := by
    rintro σ ⟨h1, h2⟩
    refine ⟨fun u v => ?_, fun v => ?_⟩
    · simpa using (h1 (σ⁻¹ u) (σ⁻¹ v)).symm
    · simpa using (h2 (σ⁻¹ v)).symm

/-- The subgroup of `K` fixing `b`. -/
def fix (K : Subgroup (Perm (Fin 27))) (b : Fin 27) : Subgroup (Perm (Fin 27)) :=
  K ⊓ MulAction.stabilizer (Perm (Fin 27)) b

theorem mem_fix {K : Subgroup (Perm (Fin 27))} {b : Fin 27} {σ : Perm (Fin 27)} :
    σ ∈ fix K b ↔ σ ∈ K ∧ σ b = b := Iff.rfl

/-- Orbit–stabiliser, with the orbit given as a finset. -/
theorem card_step (K : Subgroup (Perm (Fin 27))) (b : Fin 27) (S : Finset (Fin 27))
    (h1 : ∀ σ ∈ K, σ b ∈ S) (h2 : ∀ s ∈ S, ∃ σ ∈ K, σ b = s) :
    Nat.card K = S.card * Nat.card (fix K b) := by
  have horb : MulAction.orbit K b = (S : Set (Fin 27)) := by
    ext x
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨σ, rfl⟩; exact h1 σ σ.2
    · obtain ⟨σ, hσ, e⟩ := h2 x hx; exact ⟨⟨σ, hσ⟩, e⟩
  have h := Subgroup.card_mul_index (MulAction.stabilizer K b)
  rw [MulAction.index_stabilizer, horb, Set.ncard_coe_finset] at h
  rw [← h, mul_comm]
  congr 1
  exact Nat.card_congr
    { toFun := fun σ => ⟨σ.1.1, σ.1.2, σ.2⟩
      invFun := fun σ => ⟨⟨σ.1, σ.2.1⟩, σ.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- A permutation given by its values. -/
noncomputable def ofFun (f : Fin 27 → Fin 27) (hf : Function.Injective f) : Perm (Fin 27) :=
  Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)

theorem ofFun_apply (f : Fin 27 → Fin 27) (hf : Function.Injective f) (x : Fin 27) :
    ofFun f hf x = f x := rfl

theorem ofFun_mem (f : Fin 27 → Fin 27) (hf : Function.Injective f)
    (ha : ∀ u v, meets (f u) (f v) = meets u v) (ht : ∀ v, f v ∈ t ↔ v ∈ t) :
    ofFun f hf ∈ Wt := ⟨ha, ht⟩

/-- What an element of `W_t` fixing the points of `B` does to the incidences of `b`. -/
theorem pattern {σ : Perm (Fin 27)} (hσ : σ ∈ Wt) (B : List (Fin 27)) (hB : ∀ x ∈ B, σ x = x)
    (b : Fin 27) (hb : b ∉ B) :
    (σ b ∈ t ↔ b ∈ t) ∧ ∀ x ∈ B, meets (σ b) x = meets b x ∧ σ b ≠ x := by
  refine ⟨hσ.2 b, fun x hx => ⟨?_, fun h => hb ?_⟩⟩
  · conv_lhs => rw [← hB x hx]
    exact hσ.1 b x
  · rw [← hB x hx] at h
    exact σ.injective h ▸ hx

def g0_7 : Fin 27 → Fin 27 :=
  ![7, 1, 14, 13, 16, 15, 6, 0, 18, 17, 20, 19, 12, 3,
    2, 5, 4, 9, 8, 11, 10, 26, 22, 23, 24, 25, 21]
def g0_12 : Fin 27 → Fin 27 :=
  ![12, 13, 17, 3, 4, 5, 8, 7, 6, 26, 25, 24, 0, 1,
    21, 22, 23, 2, 18, 19, 20, 14, 15, 16, 11, 10, 9]
def g1_12 : Fin 27 → Fin 27 :=
  ![0, 2, 1, 26, 25, 24, 17, 12, 13, 9, 10, 11, 7, 8,
    14, 15, 16, 6, 21, 22, 23, 18, 19, 20, 5, 4, 3]
def g2_6 : Fin 27 → Fin 27 :=
  ![0, 6, 18, 17, 20, 19, 1, 7, 14, 13, 16, 15, 12, 9,
    8, 11, 10, 3, 2, 5, 4, 26, 22, 23, 24, 25, 21]
def g2_21 : Fin 27 → Fin 27 :=
  ![0, 21, 18, 17, 4, 5, 26, 7, 8, 9, 16, 15, 12, 13,
    14, 11, 10, 3, 2, 19, 20, 1, 22, 23, 24, 25, 6]
def g2_22 : Fin 27 → Fin 27 :=
  ![0, 22, 19, 3, 17, 5, 25, 7, 8, 16, 10, 14, 12, 13,
    11, 15, 9, 4, 18, 2, 20, 21, 1, 23, 24, 6, 26]
def g2_23 : Fin 27 → Fin 27 :=
  ![0, 23, 20, 3, 4, 17, 24, 7, 8, 15, 14, 11, 12, 13,
    10, 9, 16, 5, 18, 19, 2, 21, 22, 1, 6, 25, 26]
def g2_24 : Fin 27 → Fin 27 :=
  ![0, 24, 2, 19, 18, 5, 23, 7, 16, 9, 10, 13, 12, 11,
    14, 15, 8, 17, 4, 3, 20, 21, 22, 6, 1, 25, 26]
def g2_25 : Fin 27 → Fin 27 :=
  ![0, 25, 2, 20, 4, 18, 22, 7, 15, 9, 13, 11, 12, 10,
    14, 8, 16, 17, 5, 19, 3, 21, 6, 23, 24, 1, 26]
def g2_26 : Fin 27 → Fin 27 :=
  ![0, 26, 2, 3, 20, 19, 21, 7, 14, 13, 10, 11, 12, 9,
    8, 15, 16, 17, 18, 5, 4, 6, 22, 23, 24, 25, 1]
def g3_3 : Fin 27 → Fin 27 :=
  ![0, 1, 3, 2, 4, 5, 6, 7, 9, 8, 10, 11, 12, 14,
    13, 15, 16, 18, 17, 19, 20, 21, 24, 25, 22, 23, 26]
def g3_4 : Fin 27 → Fin 27 :=
  ![0, 1, 4, 3, 2, 5, 6, 7, 10, 9, 8, 11, 12, 15,
    14, 13, 16, 19, 18, 17, 20, 24, 22, 26, 21, 25, 23]
def g3_5 : Fin 27 → Fin 27 :=
  ![0, 1, 5, 3, 4, 2, 6, 7, 11, 9, 10, 8, 12, 16,
    14, 15, 13, 20, 18, 19, 17, 25, 26, 23, 24, 21, 22]
def g4_4 : Fin 27 → Fin 27 :=
  ![0, 1, 2, 4, 3, 5, 6, 7, 8, 10, 9, 11, 12, 13,
    15, 14, 16, 17, 19, 18, 20, 22, 21, 23, 24, 26, 25]
def g4_5 : Fin 27 → Fin 27 :=
  ![0, 1, 2, 5, 4, 3, 6, 7, 8, 11, 10, 9, 12, 13,
    16, 15, 14, 17, 20, 19, 18, 23, 22, 21, 26, 25, 24]
def g5_5 : Fin 27 → Fin 27 :=
  ![0, 1, 2, 3, 5, 4, 6, 7, 8, 9, 11, 10, 12, 13,
    14, 16, 15, 17, 18, 20, 19, 21, 23, 22, 25, 24, 26]

/-- The stabiliser chain of the base `a₀, b₁, a₁, a₂, a₃, a₄`. -/
def K1 : Subgroup (Perm (Fin 27)) := fix Wt 0
/-- See `K1`. -/
def K2 : Subgroup (Perm (Fin 27)) := fix K1 7
/-- See `K1`. -/
def K3 : Subgroup (Perm (Fin 27)) := fix K2 1
/-- See `K1`. -/
def K4 : Subgroup (Perm (Fin 27)) := fix K3 2
/-- See `K1`. -/
def K5 : Subgroup (Perm (Fin 27)) := fix K4 3
/-- See `K1`. -/
def K6 : Subgroup (Perm (Fin 27)) := fix K5 4

theorem mem_K1 {σ : Perm (Fin 27)} : σ ∈ K1 ↔ σ ∈ Wt ∧ σ 0 = 0 := by
  simp only [K1, mem_fix]

theorem mem_K2 {σ : Perm (Fin 27)} : σ ∈ K2 ↔ σ ∈ Wt ∧ σ 0 = 0 ∧ σ 7 = 7 := by
  simp only [K2, K1, mem_fix, and_assoc]

theorem mem_K3 {σ : Perm (Fin 27)} : σ ∈ K3 ↔ σ ∈ Wt ∧ σ 0 = 0 ∧ σ 7 = 7 ∧ σ 1 = 1 := by
  simp only [K3, K2, K1, mem_fix, and_assoc]

theorem mem_K4 {σ : Perm (Fin 27)} : σ ∈ K4 ↔ σ ∈ Wt ∧ σ 0 = 0 ∧ σ 7 = 7 ∧ σ 1 = 1 ∧ σ 2 = 2 := by
  simp only [K4, K3, K2, K1, mem_fix, and_assoc]

theorem mem_K5 {σ : Perm (Fin 27)} :
    σ ∈ K5 ↔ σ ∈ Wt ∧ σ 0 = 0 ∧ σ 7 = 7 ∧ σ 1 = 1 ∧ σ 2 = 2 ∧ σ 3 = 3 := by
  simp only [K5, K4, K3, K2, K1, mem_fix, and_assoc]

theorem mem_K6 {σ : Perm (Fin 27)} :
    σ ∈ K6 ↔ σ ∈ Wt ∧ σ 0 = 0 ∧ σ 7 = 7 ∧ σ 1 = 1 ∧ σ 2 = 2 ∧ σ 3 = 3 ∧ σ 4 = 4 := by
  simp only [K6, K5, K4, K3, K2, K1, mem_fix, and_assoc]

theorem step0 : Nat.card Wt = 3 * Nat.card K1 := by
  refine card_step Wt 0 {0, 7, 12} (fun σ hσ => ?_) (fun s hs => ?_)
  · have h := (pattern hσ [] (by simp) 0 (by simp)).1
    revert h; generalize σ 0 = v; revert v; decide +kernel
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨ofFun g0_7 (by decide),
        ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl⟩
    · exact ⟨ofFun g0_12 (by decide),
        ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl⟩

theorem step1 : Nat.card K1 = 2 * Nat.card K2 := by
  refine card_step K1 7 {7, 12} (fun σ hσ => ?_) (fun s hs => ?_)
  · obtain ⟨hW, h0⟩ := mem_K1.1 hσ
    have h := pattern hW [0] (by simp [h0]) 7 (by decide)
    revert h; generalize σ 7 = v; revert v; decide +kernel
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨ofFun g1_12 (by decide), mem_K1.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl⟩, rfl⟩

theorem step2 : Nat.card K2 = 8 * Nat.card K3 := by
  refine card_step K2 1 {1, 6, 21, 22, 23, 24, 25, 26} (fun σ hσ => ?_) (fun s hs => ?_)
  · obtain ⟨hW, h0, h1⟩ := mem_K2.1 hσ
    have h := pattern hW [0, 7] (by simp [h0, h1]) 1 (by decide)
    revert h; generalize σ 1 = v; revert v; decide +kernel
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨ofFun g2_6 (by decide), mem_K2.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g2_21 (by decide), mem_K2.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g2_22 (by decide), mem_K2.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g2_23 (by decide), mem_K2.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g2_24 (by decide), mem_K2.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g2_25 (by decide), mem_K2.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g2_26 (by decide), mem_K2.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl⟩, rfl⟩

theorem step3 : Nat.card K3 = 4 * Nat.card K4 := by
  refine card_step K3 2 {2, 3, 4, 5} (fun σ hσ => ?_) (fun s hs => ?_)
  · obtain ⟨hW, h0, h1, h2⟩ := mem_K3.1 hσ
    have h := pattern hW [0, 7, 1] (by simp [h0, h1, h2]) 2 (by decide)
    revert h; generalize σ 2 = v; revert v; decide +kernel
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨ofFun g3_3 (by decide), mem_K3.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g3_4 (by decide), mem_K3.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g3_5 (by decide), mem_K3.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl, rfl⟩, rfl⟩

theorem step4 : Nat.card K4 = 3 * Nat.card K5 := by
  refine card_step K4 3 {3, 4, 5} (fun σ hσ => ?_) (fun s hs => ?_)
  · obtain ⟨hW, h0, h1, h2, h3⟩ := mem_K4.1 hσ
    have h := pattern hW [0, 7, 1, 2] (by simp [h0, h1, h2, h3]) 3 (by decide)
    revert h; generalize σ 3 = v; revert v; decide +kernel
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨ofFun g4_4 (by decide), mem_K4.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl, rfl, rfl⟩, rfl⟩
    · exact ⟨ofFun g4_5 (by decide), mem_K4.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl, rfl, rfl⟩, rfl⟩

theorem step5 : Nat.card K5 = 2 * Nat.card K6 := by
  refine card_step K5 4 {4, 5} (fun σ hσ => ?_) (fun s hs => ?_)
  · obtain ⟨hW, h0, h1, h2, h3, h4⟩ := mem_K5.1 hσ
    have h := pattern hW [0, 7, 1, 2, 3] (by simp [h0, h1, h2, h3, h4]) 4 (by decide)
    revert h; generalize σ 4 = v; revert v; decide +kernel
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨ofFun g5_5 (by decide), mem_K5.2
        ⟨ofFun_mem _ _ (by decide +kernel) (by decide +kernel), rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

theorem K6_eq_bot : K6 = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun σ hσ => Equiv.ext fun v => ?_
  obtain ⟨hW, h0, h1, h2, h3, h4, h5⟩ := mem_K6.1 hσ
  have hB : ∀ x ∈ ([0, 7, 1, 2, 3, 4] : List (Fin 27)), σ x = x := by simp [h0, h1, h2, h3, h4, h5]
  by_cases hv : v ∈ ([0, 7, 1, 2, 3, 4] : List (Fin 27))
  · exact hB v hv
  have h := pattern hW [0, 7, 1, 2, 3, 4] hB v hv
  have hsep : ∀ w u : Fin 27, u ∉ ([0, 7, 1, 2, 3, 4] : List (Fin 27)) →
      ((w ∈ t ↔ u ∈ t) ∧
        ∀ x ∈ ([0, 7, 1, 2, 3, 4] : List (Fin 27)), meets w x = meets u x ∧ w ≠ x) →
        w = u := by
    decide +kernel
  exact hsep _ _ hv h

/-- **Page 26.** `card W_t = 1152`. -/
theorem card_Wt : Nat.card Wt = 1152 := by
  rw [step0, step1, step2, step3, step4, step5, K6_eq_bot, Subgroup.card_bot]

/-- **Page 25.** The automorphisms fixing `t` pointwise form a group of order `192`. -/
theorem card_pointwise :
    Nat.card {σ : Perm (Fin 27) // σ ∈ Wt ∧ ∀ v ∈ t, σ v = v} = 192 := by
  have e : Nat.card {σ : Perm (Fin 27) // σ ∈ Wt ∧ ∀ v ∈ t, σ v = v} = Nat.card K2 := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
    rw [mem_K2]
    refine ⟨fun h => ⟨h.1, h.2 0 (by decide), h.2 7 (by decide)⟩, fun ⟨hW, h0, h7⟩ => ⟨hW, ?_⟩⟩
    have h12 : σ 12 ∈ t := (hW.2 12).2 (by decide)
    have h12' : σ 12 = 12 := by
      simp only [t, Finset.mem_insert, Finset.mem_singleton] at h12
      rcases h12 with h | h | h
      · exact absurd (σ.injective (h.trans h0.symm)) (by decide)
      · exact absurd (σ.injective (h.trans h7.symm)) (by decide)
      · exact h
    intro v hv
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  rw [e, step2, step3, step4, step5, K6_eq_bot, Subgroup.card_bot]

/-- The same count for the graph automorphisms `C ≃g C` that preserve `t`. -/
theorem card_aut : Nat.card {f : C ≃g C // ∀ v, f v ∈ t ↔ v ∈ t} = 1152 := by
  rw [← card_Wt]
  refine Nat.card_congr
    { toFun := fun f => ⟨f.1.toEquiv, fun u v => ?_, f.2⟩
      invFun := fun σ => ⟨⟨σ.1, fun {u v} => ?_⟩, σ.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · have := f.1.map_rel_iff (a := u) (b := v)
    simp only [C] at this
    exact Bool.eq_iff_iff.2 this
  · change meets (σ.1 u) (σ.1 v) = true ↔ meets u v = true
    rw [σ.2.1 u v]

end Grothendieck.Folder69
