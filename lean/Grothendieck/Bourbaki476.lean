import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.ZMod.Basic

/-!
# Bourbaki, rédaction n° 476 (Cartier, 1966), exercises p. 6: two exercises that need a hypothesis

Rédaction 476, « Catégories. Chapitre I. Diagrammes et graphes », closes its first section with
exercises on graphs and orientations. Two of them, as typed, are false.

*Exercise 2* asks to show that every tree with infinitely many vertices has an orientation in
which each vertex is the source of exactly one arrow. The infinite star, a centre joined to
countably many leaves, is a counterexample: a leaf has one edge, which must leave it, so every
edge points to the centre and the centre is the source of none. What holds is the statement for
trees with a ray (an injective infinite path): orient every edge towards the side that contains a
tail of the ray. In a locally finite infinite tree a ray always exists (König's lemma), which is
presumably the case the exercise had in mind.

*Exercise 3* relates the period of a quiver (the gcd of the lengths of its closed paths) to
morphisms onto the cycle `ℤ/d`. Without strong connectivity it fails: the quiver `a → b`,
`a → c`, `c → b` has no closed path, so period `0`, yet no map `h` to `ℤ/d` with
`h(t) = h(s) + 1` on every arrow exists for any `d ≠ 1` (the two paths from `a` to `b` have
lengths `1` and `2`); for `d = 2`, the underlying triangle is not bipartite either.

**What is proved.**
* `Orientation`, `Orientation.OutDegreeOne`: an orientation of a simple graph is a relation
  inside the adjacency that takes exactly one direction on every edge.
* `star_isTree`, `not_exists_outDegreeOne_star`: **Exercise 2 is false.** The star on
  `Option ℕ` centred at `none` is an infinite tree with no orientation of out-degree one.
* `exists_outDegreeOne_of_ray`: **the corrected statement, one direction.** A tree with a ray
  has an orientation of out-degree one (edge `v w` points to `w` when the component of `w` in
  the tree without that edge contains a tail of the ray).
* `ex3_noClosedPath`, `ex3_no_hom_zmod`, `ex3_no_hom_zmod2`, `ex3_not_bipartite`: **Exercise 3
  without strong connectivity.** The quiver `0 → 1`, `0 → 2`, `2 → 1` on `Fin 3` has no closed
  path, admits a morphism to `ℤ/d` only for `d = 1` (to `ℤ/2` and `ℤ = ℤ/0` in particular), and
  its underlying triangle has no 2-colouring.

**Not formalised.** The converse of the corrected Exercise 2 (an orientation of out-degree one
gives a ray, by following the arrows from any vertex) and König's lemma; the general statement
of Exercise 3 for strongly connected quivers.
-/

namespace Grothendieck.Bourbaki476

open SimpleGraph

/-! ### Exercise 2 -/

section Orientation

variable {V : Type*}

/-- An orientation of a simple graph `G`: a relation inside the adjacency of `G` that takes
exactly one of the two directions on every edge. -/
structure Orientation (G : SimpleGraph V) where
  /-- `r v w`: the edge `v w` is oriented from `v` to `w`. -/
  r : V → V → Prop
  le_adj : ∀ v w, r v w → G.Adj v w
  adj : ∀ v w, G.Adj v w → (r v w ↔ ¬ r w v)

/-- Every vertex is the source of exactly one arrow. -/
def Orientation.OutDegreeOne {G : SimpleGraph V} (o : Orientation G) : Prop :=
  ∀ v, ∃! w, o.r v w

end Orientation

/-- The infinite star: the centre `none` joined to the leaves `some n`, `n : ℕ`. -/
abbrev star : SimpleGraph (Option ℕ) := starGraph none

/-- The infinite star is a tree (Mathlib's `isTree_starGraph`), with infinitely many vertices. -/
theorem star_isTree : star.IsTree ∧ Infinite (Option ℕ) :=
  ⟨isTree_starGraph none, inferInstance⟩

/-- **Exercise 2 of rédaction n° 476, p. 6, is false.** The infinite star has no orientation in
which every vertex is the source of exactly one arrow: each leaf must point to the centre, and
then the centre points nowhere. -/
theorem not_exists_outDegreeOne_star : ¬ ∃ o : Orientation star, o.OutDegreeOne := by
  rintro ⟨o, ho⟩
  -- every leaf points to the centre
  have leaf : ∀ n : ℕ, o.r (some n) none := by
    intro n
    obtain ⟨w, hw, -⟩ := ho (some n)
    have hadj := o.le_adj _ _ hw
    rw [starGraph_adj] at hadj
    rcases hadj with ⟨hne, h | h⟩
    · exact absurd h (Option.some_ne_none n)
    · exact h ▸ hw
  obtain ⟨w, hw, -⟩ := ho none
  have hadj := o.le_adj _ _ hw
  obtain ⟨n, rfl⟩ : ∃ n, w = some n := by
    rcases w with _ | n
    · exact (star.irrefl hadj).elim
    · exact ⟨n, rfl⟩
  exact (o.adj _ _ hadj).mp hw (leaf n)

section Ray

variable {V : Type*} {G : SimpleGraph V}

/-- A walk avoiding `v` survives the removal of all the edges at `v`. -/
theorem reachable_deleteEdges_of_notMem_support {K : SimpleGraph V} {a b v : V}
    (q : K.Walk a b) (hv : v ∉ q.support) :
    (K.deleteEdges {e | v ∈ e}).Reachable a b := by
  induction q with
  | nil => exact Reachable.refl _
  | @cons x y z h q ih =>
    rw [Walk.support_cons, List.mem_cons, not_or] at hv
    have hy : v ≠ y := fun e => hv.2 (e ▸ q.start_mem_support)
    have hadj : (K.deleteEdges {e | v ∈ e}).Adj x y := by
      rw [deleteEdges_adj]
      refine ⟨h, ?_⟩
      simp only [Set.mem_ofPred_eq, Sym2.mem_iff, not_or]
      exact ⟨hv.1, hy⟩
    exact hadj.reachable.trans (ih hv.2)

/-- In an acyclic graph, the two ends of an edge are not joined once the edge is removed. -/
theorem not_reachable_deleteEdge (hG : G.IsAcyclic) {v w : V} (h : G.Adj v w) :
    ¬ (G.deleteEdges {s(v, w)}).Reachable v w :=
  isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hG h)

variable (f : ℕ → V)

/-- The orientation towards a ray `f`: `v → w` when, in `G` without the edge `v w`, the vertex
`w` reaches a tail of the ray. -/
def towards (v w : V) : Prop :=
  G.Adj v w ∧ ∃ N, ∀ n ≥ N, (G.deleteEdges {s(v, w)}).Reachable w (f n)

variable {f}

/-- A ray avoids any given vertex from some index on. -/
theorem exists_tail_ne (hf : Function.Injective f) (v : V) : ∃ m, ∀ n ≥ m, f n ≠ v := by
  by_cases h : ∃ k, f k = v
  · obtain ⟨k, hk⟩ := h
    refine ⟨k + 1, fun n hn e => ?_⟩
    have := hf (e.trans hk.symm)
    omega
  · push Not at h
    exact ⟨0, fun n _ => h n⟩

/-- A tail of the ray avoiding `v` stays in one component of `G` without the edges at `v`. -/
theorem tail_reachable (hr : ∀ n, G.Adj (f n) (f (n + 1))) {v : V}
    {m : ℕ} (hm : ∀ n ≥ m, f n ≠ v) :
    ∀ n ≥ m, (G.deleteEdges {e | v ∈ e}).Reachable (f m) (f n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact Reachable.refl _
  | succ n hn ih =>
    refine ih.trans (Adj.reachable ?_)
    rw [deleteEdges_adj]
    refine ⟨hr n, ?_⟩
    simp only [Set.mem_ofPred_eq, Sym2.mem_iff, not_or]
    exact ⟨(hm n hn).symm, (hm (n + 1) (by omega)).symm⟩

/-- Every vertex has a neighbour that reaches a tail of the ray without passing through it. -/
theorem exists_towards (hG : G.Connected) (hf : Function.Injective f)
    (hr : ∀ n, G.Adj (f n) (f (n + 1))) (v : V) :
    ∃ w m, G.Adj v w ∧ ∀ n ≥ m, (G.deleteEdges {e | v ∈ e}).Reachable w (f n) := by
  classical
  obtain ⟨m, hm⟩ := exists_tail_ne hf v
  obtain ⟨p, hp⟩ := (hG.preconnected v (f m)).some.toPath
  have hvx : v ≠ f m := (hm m le_rfl).symm
  cases p with
  | nil => exact absurd rfl hvx
  | @cons _ w _ h q =>
    rw [Walk.cons_isPath_iff] at hp
    exact ⟨w, m, h, fun n hn =>
      (reachable_deleteEdges_of_notMem_support q hp.2).trans (tail_reachable hr hm n hn)⟩

/-- **Exercise 2 corrected, one direction.** A tree with a ray `f` (an injective sequence of
vertices, consecutive ones adjacent) has an orientation in which every vertex is the source of
exactly one arrow. -/
theorem exists_outDegreeOne_of_ray (hG : G.IsTree) (hf : Function.Injective f)
    (hr : ∀ n, G.Adj (f n) (f (n + 1))) : ∃ o : Orientation G, o.OutDegreeOne := by
  classical
  have hA := hG.isAcyclic
  have hC := hG.connected
  -- removing the edges at `v` leaves fewer edges than removing the edge `v w`
  have mono : ∀ {v w : V}, G.deleteEdges {e | v ∈ e} ≤ G.deleteEdges {s(v, w)} := by
    intro v w a b hab
    rw [deleteEdges_adj] at hab ⊢
    refine ⟨hab.1, fun e => hab.2 ?_⟩
    rw [Set.mem_singleton_iff] at e
    simp [e]
  have swap : ∀ v w : V, G.deleteEdges {s(w, v)} = G.deleteEdges {s(v, w)} := by
    intro v w; rw [Sym2.eq_swap]
  refine ⟨⟨towards f, fun v w h => h.1, fun v w hvw => ⟨?_, ?_⟩⟩, ?_⟩
  · rintro ⟨-, N, hN⟩ ⟨-, N', hN'⟩
    have h1 := hN (max N N') (le_max_left _ _)
    have h2 := hN' (max N N') (le_max_right _ _)
    rw [swap] at h2
    exact not_reachable_deleteEdge hA hvw (h2.trans h1.symm)
  · intro hn
    obtain ⟨w₀, m, hw₀, hm⟩ := exists_towards hC hf hr v
    by_cases e : w₀ = w
    · subst e
      exact ⟨hvw, m, fun n hn => (hm n hn).mono mono⟩
    · refine absurd ⟨hvw.symm, m, fun n hn' => ?_⟩ hn
      rw [swap]
      have hadj : (G.deleteEdges {s(v, w)}).Adj v w₀ := by
        rw [deleteEdges_adj]
        refine ⟨hw₀, ?_⟩
        rw [Set.mem_singleton_iff, Sym2.congr_right]
        exact e
      exact hadj.reachable.trans ((hm n hn').mono mono)
  · intro v
    obtain ⟨w, m, hw, hm⟩ := exists_towards hC hf hr v
    refine ⟨w, ⟨hw, m, fun n hn => (hm n hn).mono mono⟩, ?_⟩
    rintro w' ⟨hw', N', hN'⟩
    by_contra hne
    have hx := hN' (max m N') (le_max_right _ _)
    obtain ⟨q⟩ := hx
    by_cases hv : v ∈ q.support
    · -- the walk from `w'` to the ray returns to `v` without the edge `v w'`
      exact not_reachable_deleteEdge hA hw' ⟨(q.takeUntil v hv).reverse⟩
    · have h1 : (G.deleteEdges {s(v, w)}).Reachable w' (f (max m N')) := by
        refine (reachable_deleteEdges_of_notMem_support q hv).mono ?_
        intro a b hab
        simp only [deleteEdges_adj, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hab ⊢
        refine ⟨hab.1.1, fun e => hab.2 ?_⟩
        rw [e]
        exact Sym2.mem_mk_left _ _
      have hadj : (G.deleteEdges {s(v, w)}).Adj v w' := by
        rw [deleteEdges_adj]
        refine ⟨hw', ?_⟩
        rw [Set.mem_singleton_iff, Sym2.congr_right]
        exact hne
      exact not_reachable_deleteEdge hA hw
        ((hadj.reachable.trans h1).trans ((hm _ (le_max_left _ _)).mono mono).symm)

end Ray

/-! ### Exercise 3 -/

/-- The quiver `0 → 1`, `0 → 2`, `2 → 1` on `Fin 3` (`a = 0`, `b = 1`, `c = 2`). -/
def ex3 (s t : Fin 3) : Prop :=
  (s = 0 ∧ t = 1) ∨ (s = 0 ∧ t = 2) ∨ (s = 2 ∧ t = 1)

instance : DecidableRel ex3 := fun s t => by unfold ex3; infer_instance

/-- A height strictly increasing along the arrows. -/
def ex3Height : Fin 3 → ℕ := ![0, 2, 1]

theorem ex3_height_lt : ∀ s t, ex3 s t → ex3Height s < ex3Height t := by decide

/-- The quiver of Exercise 3 has no closed path (so its period is `0`). -/
theorem ex3_noClosedPath (v : Fin 3) : ¬ Relation.TransGen ex3 v v := by
  have key : ∀ s t, Relation.TransGen ex3 s t → ex3Height s < ex3Height t := by
    intro s t h
    induction h with
    | single h => exact ex3_height_lt _ _ h
    | tail _ h ih => exact ih.trans (ex3_height_lt _ _ h)
  exact fun h => lt_irrefl _ (key v v h)

/-- **Exercise 3 of rédaction n° 476 needs strong connectivity.** The quiver of `ex3` has a
morphism to the cycle `ℤ/d` (a map `h` with `h t = h s + 1` on every arrow) only for `d = 1`;
in particular none to `ℤ = ℤ/0`, although its period is `0`. -/
theorem ex3_no_hom_zmod (d : ℕ) :
    (∃ h : Fin 3 → ZMod d, ∀ s t, ex3 s t → h t = h s + 1) ↔ d = 1 := by
  constructor
  · rintro ⟨h, hh⟩
    have h01 := hh 0 1 (by decide)
    have h02 := hh 0 2 (by decide)
    have h21 := hh 2 1 (by decide)
    rw [h21, h02, add_assoc] at h01
    have : (1 : ZMod d) = 0 := by
      have := congrArg (· - h 0 - 1) h01
      simpa using this
    exact ZMod.one_eq_zero_iff.mp this
  · rintro rfl
    exact ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

/-- The case `d = 2` by enumeration: no morphism to the cycle `ℤ/2`. -/
theorem ex3_no_hom_zmod2 : ¬ ∃ h : Fin 3 → ZMod 2, ∀ s t, ex3 s t → h t = h s + 1 := by
  decide

/-- The underlying graph of the quiver of `ex3` (a triangle) has no 2-colouring. -/
theorem ex3_not_bipartite : ¬ ∃ c : Fin 3 → Bool, ∀ s t, ex3 s t → c s ≠ c t := by
  decide

end Grothendieck.Bourbaki476
