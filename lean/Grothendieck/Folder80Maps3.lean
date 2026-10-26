import Mathlib

/-!
# Folder 80, pages 39–54: the skeleton of a bigon-free arrangement, in combinatorial maps

Finding `80-skeleton-full-faithfulness`. Page 54 (« En résumé »):

> Le foncteur canonique du groupoïde des arrangements de pseudo-droites sans bigone vers celui
> des arrangements de dimension 1 de pseudo-droites sans bigone est pleinement fidèle.

**Model.** As in `Folder80Maps2`, an arrangement is a generalised map (flags, three involutions
`a0, a1, a2`) of Euler characteristic `1` whose flags are labelled by lines (page 60), and it is
*bigon-free* when every line carries at least three vertices. Page 60's « aller tout droit » is
the extra hypothesis `Straight`: with `φ = a2 a1` the rotation around a vertex of `ν` lines,
`φ^ν` returns to the same line. The arrangement of dimension `1` (page 40) is the skeleton —
vertices, edges, incidence — with the line of each edge; `SkelIso` is an isomorphism of these.

**What is proved.**
* `faithful`: two isomorphisms of arrangements inducing the same maps on vertices and edges are
  equal — the functor is faithful.
* `lift`, `lift_iff`: page 41's « théorème général des cartes ». A skeleton isomorphism comes
  from an isomorphism of arrangements iff it preserves the three-edge face paths `Path3`
  (a corner continued along an edge to the next corner: the rotation system (19)–(21)).
  Fullness is thus reduced to the statement that these paths are read on the skeleton.
* `finrank_Z1_le`: mod 2, the cycles `Z₁` of the skeleton exceed the boundaries `B₁` of unions
  of faces by at most one dimension — the relation `c₂ = c(K)` of page 42, from `χ = 1`.
* `rot_card`: going straight, half a turn around a vertex meets every other line exactly once.
* `parity`: a closed line crosses the boundary of a union of faces an even number of times.
* `lineChain_mem`, `lineChain_not_mem`, `flip`: a line is a cycle that bounds nothing, so of a
  cycle `z` and `z + D` exactly one bounds (the four of the eight triangle cycles of page 35).
* `triangle_iff`: condition (A5) of page 50. For a triangle of three non-concurrent lines and a
  fourth line `Δ` through none of its vertices, a triangle cycle bounds iff `Δ` crosses an even
  number of its sides. The canonical orientation `ω` of the triangle is therefore read on the
  skeleton, and it does not depend on `Δ`.

**Not formalised.** That the face paths are read on the skeleton: conditions (A1)–(A4) (the
cyclic order around a vertex, its lifts, the transport along an edge) and the cases (A6) and
`III₆` of the canonical orientation, where every other line passes through a vertex of the
triangle. These are what remains of the page 54 theorem.
-/

namespace Grothendieck.Folder80Maps3

open Relation

/-- A relation contained in an equivalence closure has its equivalence closure inside. -/
theorem eqvGen_of_le {α : Type*} {r s : α → α → Prop} (h : ∀ x y, r x y → EqvGen s x y)
    {a b : α} (hab : EqvGen r a b) : EqvGen s a b := by
  induction hab with
  | rel x y h' => exact h x y h'
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ i1 i2 => exact i1.trans _ _ _ i2

/-- A set invariant under the generators of an equivalence closure is invariant under it. -/
theorem eqvGen_iff {α : Type*} {r : α → α → Prop} (S : α → Prop) (h : ∀ x y, r x y → (S x ↔ S y))
    {a b : α} (hab : EqvGen r a b) : S a ↔ S b := by
  induction hab with
  | rel x y h' => exact h x y h'
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ i1 i2 => exact i1.trans i2

/-- A generalised map: flags with three fixed-point-free involutions, `a0` and `a2` commuting
with `a0 a2` fixed-point-free. -/
structure GMap (D : Type*) where
  a0 : D → D
  a1 : D → D
  a2 : D → D
  a0_a0 : ∀ d, a0 (a0 d) = d
  a1_a1 : ∀ d, a1 (a1 d) = d
  a2_a2 : ∀ d, a2 (a2 d) = d
  a0_ne : ∀ d, a0 d ≠ d
  a1_ne : ∀ d, a1 d ≠ d
  a2_ne : ∀ d, a2 d ≠ d
  a0_a2 : ∀ d, a0 (a2 d) = a2 (a0 d)
  a02_ne : ∀ d, a0 (a2 d) ≠ d

namespace GMap

variable {D : Type*} (M : GMap D)

/-- Vertices are the classes of `⟨a1, a2⟩`. -/
def Vtx := Quot fun x y : D => y = M.a1 x ∨ y = M.a2 x
/-- Edges are the classes of `⟨a0, a2⟩`. -/
def Edge := Quot fun x y : D => y = M.a0 x ∨ y = M.a2 x
/-- Faces are the classes of `⟨a0, a1⟩`. -/
def Face := Quot fun x y : D => y = M.a0 x ∨ y = M.a1 x

/-- The vertex of a flag. -/
def vtx (d : D) : M.Vtx := Quot.mk _ d
/-- The edge of a flag. -/
def edge (d : D) : M.Edge := Quot.mk _ d
/-- The face of a flag. -/
def face (d : D) : M.Face := Quot.mk _ d

instance [Finite D] : Finite M.Vtx := Quot.finite _
instance [Finite D] : Finite M.Edge := Quot.finite _
instance [Finite D] : Finite M.Face := Quot.finite _
noncomputable instance [Finite D] : Fintype M.Vtx := Fintype.ofFinite _
noncomputable instance [Finite D] : Fintype M.Edge := Fintype.ofFinite _
noncomputable instance [Finite D] : Fintype M.Face := Fintype.ofFinite _

/-- The Euler characteristic `V − E + F`. -/
noncomputable def euler : ℤ := Nat.card M.Vtx - Nat.card M.Edge + Nat.card M.Face

variable {M}

@[simp] theorem vtx_a1 (d : D) : M.vtx (M.a1 d) = M.vtx d := (Quot.sound (.inl rfl)).symm
@[simp] theorem vtx_a2 (d : D) : M.vtx (M.a2 d) = M.vtx d := (Quot.sound (.inr rfl)).symm
@[simp] theorem edge_a0 (d : D) : M.edge (M.a0 d) = M.edge d := (Quot.sound (.inl rfl)).symm
@[simp] theorem edge_a2 (d : D) : M.edge (M.a2 d) = M.edge d := (Quot.sound (.inr rfl)).symm
@[simp] theorem face_a0 (d : D) : M.face (M.a0 d) = M.face d := (Quot.sound (.inl rfl)).symm
@[simp] theorem face_a1 (d : D) : M.face (M.a1 d) = M.face d := (Quot.sound (.inr rfl)).symm

theorem a0_eq_iff {x y : D} : M.a0 x = y ↔ x = M.a0 y :=
  ⟨fun h => h ▸ (M.a0_a0 x).symm, fun h => h ▸ M.a0_a0 y⟩
theorem a1_eq_iff {x y : D} : M.a1 x = y ↔ x = M.a1 y :=
  ⟨fun h => h ▸ (M.a1_a1 x).symm, fun h => h ▸ M.a1_a1 y⟩
theorem a2_eq_iff {x y : D} : M.a2 x = y ↔ x = M.a2 y :=
  ⟨fun h => h ▸ (M.a2_a2 x).symm, fun h => h ▸ M.a2_a2 y⟩

/-- An edge has exactly the four flags `d, a0 d, a2 d, a0 a2 d`. -/
theorem edge_eq {d e : D} :
    M.edge e = M.edge d ↔ e = d ∨ e = M.a0 d ∨ e = M.a2 d ∨ e = M.a0 (M.a2 d) := by
  constructor
  · intro h
    refine (eqvGen_iff (fun x => x = d ∨ x = M.a0 d ∨ x = M.a2 d ∨ x = M.a0 (M.a2 d)) ?_
      (Quot.eqvGen_exact h)).2 (.inl rfl)
    rintro x y (rfl | rfl)
    · simp only [a0_eq_iff, M.a0_a0]; tauto
    · simp only [a2_eq_iff, ← M.a0_a2, M.a2_a2]; tauto
  · rintro (rfl | rfl | rfl | rfl) <;> simp

theorem edge_four (d : D) : [d, M.a0 d, M.a2 d, M.a0 (M.a2 d)].Nodup := by
  have := M.a0_ne d; have := M.a2_ne d; have := M.a02_ne d
  have := M.a0_ne (M.a2 d)
  have : M.a0 d ≠ M.a2 d := fun h => M.a02_ne d (by rw [← h, M.a0_a0])
  have : M.a0 d ≠ M.a0 (M.a2 d) := fun h => M.a2_ne d (by rw [a0_eq_iff, M.a0_a0] at h; exact h.symm)
  simp_all [eq_comm]

end GMap

open GMap

/-- Every line carries at least three vertices. -/
def BigonFree {P L : Type*} (on : P → L → Prop) : Prop :=
  ∀ l : L, ∃ p q r, on p l ∧ on q l ∧ on r l ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r

/-- A combinatorial pseudoline arrangement (page 60), as in `Folder80Maps2`: a generalised map
with flags labelled by lines, constant on edges; a line through a vertex has there the four
flags of two edge-ends; each line is connected; every vertex is on two lines; two lines meet at
exactly one vertex; `χ = 1`. -/
structure PseudolineMap (D L : Type*) where
  M : GMap D
  line : D → L
  line_a0 : ∀ d, line (M.a0 d) = line d
  line_a2 : ∀ d, line (M.a2 d) = line d
  pass : ∀ d, Nat.card {e // M.vtx e = M.vtx d ∧ line e = line d} = 4
  conn : ∀ d e, line d = line e →
    EqvGen (fun x y => y = M.a0 x ∨ (M.vtx y = M.vtx x ∧ line y = line x)) d e
  two : ∀ d, ∃ e, M.vtx e = M.vtx d ∧ line e ≠ line d
  meet : ∀ l l' : L, l ≠ l' →
    ∃! v, (∃ d, M.vtx d = v ∧ line d = l) ∧ (∃ d, M.vtx d = v ∧ line d = l')
  euler : M.euler = 1

namespace PseudolineMap

variable {D L : Type*} (X : PseudolineMap D L)

/-- The line `l` passes through the vertex `v`. -/
def On (v : X.M.Vtx) (l : L) : Prop := ∃ d, X.M.vtx d = v ∧ X.line d = l

variable {X}

/-- A line whose flags all sit at two vertices `u, w` is not bigon-free. -/
theorem confined (hbf : BigonFree X.On) {l : L} {u w : X.M.Vtx}
    (H : ∀ e, X.line e = l → X.M.vtx e = u ∨ X.M.vtx e = w) : False := by
  obtain ⟨p, q, r, ⟨d1, rfl, h1⟩, ⟨d2, rfl, h2⟩, ⟨d3, rfl, h3⟩, h12, h13, h23⟩ := hbf l
  rcases H _ h1 with h1 | h1 <;> rcases H _ h2 with h2 | h2 <;> rcases H _ h3 with h3 | h3 <;>
    simp_all

/-- The connected line `l` stays in a set of vertices stable under `a0` along `l`. -/
theorem confine {l : L} (Z : X.M.Vtx → Prop)
    (h : ∀ x, X.line x = l → Z (X.M.vtx x) → Z (X.M.vtx (X.M.a0 x))) {d : D} (hd : X.line d = l)
    (hZ : Z (X.M.vtx d)) {e : D} (he : X.line e = l) : Z (X.M.vtx e) := by
  refine (eqvGen_iff (fun x => X.line x = l → Z (X.M.vtx x)) ?_ (X.conn d e (hd.trans he.symm))).1
    (fun _ => hZ) he
  rintro x y (rfl | ⟨h1, h2⟩)
  · rw [X.line_a0]
    exact ⟨fun h' hx => h _ hx (h' hx), fun h' hx => by
      simpa [X.M.a0_a0] using h _ (by rwa [X.line_a0]) (h' hx)⟩
  · rw [h1, h2]

/-- The flags form one orbit of `⟨a0, a1, a2⟩`. -/
theorem connected (d e : D) :
    EqvGen (fun x y => y = X.M.a0 x ∨ y = X.M.a1 x ∨ y = X.M.a2 x) d e := by
  have hv : ∀ {x y : D}, X.M.vtx x = X.M.vtx y →
      EqvGen (fun x y => y = X.M.a0 x ∨ y = X.M.a1 x ∨ y = X.M.a2 x) x y := fun h =>
    eqvGen_of_le (fun _ _ h => .rel _ _ (.inr h)) (Quot.eqvGen_exact h)
  have hl : ∀ {x y : D}, X.line x = X.line y →
      EqvGen (fun x y => y = X.M.a0 x ∨ y = X.M.a1 x ∨ y = X.M.a2 x) x y := fun h =>
    eqvGen_of_le (fun x y h => h.elim (fun h => .rel _ _ (.inl h)) fun h => hv h.1.symm)
      (X.conn _ _ h)
  by_cases h : X.line d = X.line e
  · exact hl h
  obtain ⟨v, ⟨⟨d1, h1, l1⟩, ⟨e1, h2, l2⟩⟩, -⟩ := X.meet _ _ h
  exact ((hl l1.symm).trans _ _ _ (hv (h1.trans h2.symm))).trans _ _ _ (hl l2)

/-- A function invariant under `a0, a1, a2` is constant. -/
theorem const_of_inv {α : Type*} (f : D → α) (h0 : ∀ d, f (X.M.a0 d) = f d)
    (h1 : ∀ d, f (X.M.a1 d) = f d) (h2 : ∀ d, f (X.M.a2 d) = f d) (d e : D) : f d = f e := by
  refine (eqvGen_iff (fun x => f x = f d) ?_ (connected (X := X) d e)).1 rfl |>.symm
  rintro x y (rfl | rfl | rfl) <;> simp [h0, h1, h2]

variable [Fintype D]

open Classical in
/-- The four flags of a line at a vertex. -/
theorem at_four {d x1 x2 x3 x4 : D} (hn : [x1, x2, x3, x4].Nodup)
    (hx : ∀ x ∈ [x1, x2, x3, x4], X.M.vtx x = X.M.vtx d ∧ X.line x = X.line d) {f : D}
    (hf : X.M.vtx f = X.M.vtx d) (hl : X.line f = X.line d) : f ∈ [x1, x2, x3, x4] := by
  have h4 := X.pass d
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
  have hsub : [x1, x2, x3, x4].toFinset ⊆
      Finset.univ.filter fun e => X.M.vtx e = X.M.vtx d ∧ X.line e = X.line d := fun x hx' => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hx _ (List.mem_toFinset.1 hx')
  have := Finset.eq_of_subset_of_card_le hsub (by rw [h4, List.toFinset_card_of_nodup hn]; rfl)
  have hf' : f ∈ Finset.univ.filter fun e => X.M.vtx e = X.M.vtx d ∧ X.line e = X.line d := by
    simp [hf, hl]
  rw [← this] at hf'
  simpa using hf'

/-- No loop: the two ends of an edge are distinct vertices. -/
theorem noLoop (hbf : BigonFree X.On) (d : D) : X.M.vtx (X.M.a0 d) ≠ X.M.vtx d := by
  intro h
  have hall : ∀ x ∈ [d, X.M.a0 d, X.M.a2 d, X.M.a0 (X.M.a2 d)],
      X.M.vtx x = X.M.vtx d ∧ X.line x = X.line d := by
    simp [h, X.line_a0, X.line_a2, X.M.a0_a2]
  refine confined hbf (l := X.line d) (u := X.M.vtx d) (w := X.M.vtx d) fun e he => .inl ?_
  refine confine (fun t => t = X.M.vtx d) (fun x hx hxv => ?_) rfl rfl he
  have := at_four (edge_four d) hall hxv hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl <;> simp [h, X.M.a0_a0, X.M.a0_a2]

/-! ### Faithfulness -/

/-- At a vertex, the two flags of an edge-end are followed by flags of two different edges. -/
theorem edge_a1_a2_ne (hbf : BigonFree X.On) (u : D) :
    X.M.edge (X.M.a1 (X.M.a2 u)) ≠ X.M.edge (X.M.a1 u) := by
  intro e1
  have hn := noLoop hbf
  rcases edge_eq.1 e1 with k | k | k | k
  · exact X.M.a2_ne u (by simpa [X.M.a1_a1] using congrArg X.M.a1 k)
  · exact hn (X.M.a1 u) (by rw [← k]; simp)
  · -- `a1 a2 u = a2 a1 u`: the vertex of `u` has four flags only
    obtain ⟨e, hev, hel⟩ := X.two u
    have hS : ∀ x, X.M.vtx x = X.M.vtx u →
        x = u ∨ x = X.M.a1 u ∨ x = X.M.a2 u ∨ x = X.M.a1 (X.M.a2 u) := fun x hx => by
      refine (eqvGen_iff (fun x => x = u ∨ x = X.M.a1 u ∨ x = X.M.a2 u ∨
        x = X.M.a1 (X.M.a2 u)) ?_ (Quot.eqvGen_exact hx)).2 (.inl rfl)
      have c1 : ∀ x, x = u ∨ x = X.M.a1 u ∨ x = X.M.a2 u ∨ x = X.M.a1 (X.M.a2 u) →
          X.M.a1 x = u ∨ X.M.a1 x = X.M.a1 u ∨ X.M.a1 x = X.M.a2 u ∨
            X.M.a1 x = X.M.a1 (X.M.a2 u) := by
        rintro x (rfl | rfl | rfl | rfl) <;> simp [X.M.a1_a1]
      have c2 : ∀ x, x = u ∨ x = X.M.a1 u ∨ x = X.M.a2 u ∨ x = X.M.a1 (X.M.a2 u) →
          X.M.a2 x = u ∨ X.M.a2 x = X.M.a1 u ∨ X.M.a2 x = X.M.a2 u ∨
            X.M.a2 x = X.M.a1 (X.M.a2 u) := by
        rintro x (rfl | rfl | rfl | rfl) <;> simp [X.M.a2_a2, k]
      rintro x y (rfl | rfl)
      · exact ⟨c1 x, fun h => by simpa [X.M.a1_a1] using c1 _ h⟩
      · exact ⟨c2 x, fun h => by simpa [X.M.a2_a2] using c2 _ h⟩
    have hl1 : X.line (X.M.a1 u) ≠ X.line u := fun hl => hel <| by
      rcases hS e hev with rfl | rfl | rfl | rfl <;> simp_all [X.line_a2]
    classical
    have h4 := X.pass u
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
    have hsub : (Finset.univ.filter fun e => X.M.vtx e = X.M.vtx u ∧ X.line e = X.line u) ⊆
        {u, X.M.a2 u} := fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases hS x hx.1 with rfl | rfl | rfl | rfl
      · simp
      · exact absurd hx.2 hl1
      · simp
      · exact absurd (by rw [k, X.line_a2] at hx; exact hx.2) hl1
    have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    simp only [Finset.card_singleton] at this
    omega
  · exact hn (X.M.a2 (X.M.a1 u)) (by rw [← k]; simp)

omit [Fintype D] in
/-- **Faithfulness.** Two maps of flags `X → X'` commuting with `a1` (for instance two
isomorphisms of arrangements) that induce the same maps on vertices and on edges are equal. -/
theorem faithful {D' L' : Type*} [Fintype D'] {X' : PseudolineMap D' L'}
    (hbf : BigonFree X'.On) {g g' : D → D'}
    (h1 : ∀ d, g (X.M.a1 d) = X'.M.a1 (g d)) (h1' : ∀ d, g' (X.M.a1 d) = X'.M.a1 (g' d))
    (hv : ∀ d, X'.M.vtx (g d) = X'.M.vtx (g' d)) (he : ∀ d, X'.M.edge (g d) = X'.M.edge (g' d)) :
    g = g' := by
  funext d
  have hn := noLoop hbf
  rcases edge_eq.1 (he d) with h | h | h | h
  · exact h
  · exact (hn _ (by rw [← h, hv d])).elim
  · exact (edge_a1_a2_ne hbf _ (by have := he (X.M.a1 d); rwa [h1, h1', h] at this)).elim
  · exact (hn (X'.M.a2 (g' d)) (by rw [vtx_a2, ← hv d, h])).elim

/-! ### Chains mod 2 -/

section Chains

open Matrix

variable (X) in
/-- The vertex `v` is an end of the edge `e`. -/
def Inc (v : X.M.Vtx) (e : X.M.Edge) : Prop := ∃ d, X.M.vtx d = v ∧ X.M.edge d = e

variable (X) in
/-- The line of an edge. -/
def lineE : X.M.Edge → L :=
  Quot.lift X.line fun x _ h => h.elim (fun h => h ▸ (X.line_a0 x).symm) fun h =>
    h ▸ (X.line_a2 x).symm

omit [Fintype D] in
@[simp] theorem lineE_edge (d : D) : X.lineE (X.M.edge d) = X.line d := rfl

open Classical in
variable (X) in
/-- The incidence matrix vertices × edges: the boundary `∂₁`. -/
noncomputable def incM : Matrix X.M.Vtx X.M.Edge (ZMod 2) :=
  Matrix.of fun v e => if X.Inc v e then 1 else 0

open Classical in
variable (X) in
/-- The boundary `∂₂` of faces: an edge is counted once for each of its two sides. -/
noncomputable def bdM : Matrix X.M.Edge X.M.Face (ZMod 2) :=
  Matrix.of fun e f =>
    (if X.M.face e.out = f then 1 else 0) + (if X.M.face (X.M.a2 e.out) = f then 1 else 0)

variable (X) in
/-- The cycles `Z₁ = ker ∂₁`. -/
noncomputable abbrev Z1 := LinearMap.ker X.incM.mulVecLin

variable (X) in
/-- The boundaries `B₁ = im ∂₂`. -/
noncomputable abbrev B1 := LinearMap.range X.bdM.mulVecLin

open Classical in
variable (X) in
/-- The chain of a line: its edges. -/
noncomputable def lineChain (l : L) : X.M.Edge → ZMod 2 := fun e => if X.lineE e = l then 1 else 0

omit [Fintype D] in
theorem edge_surj (e : X.M.Edge) : ∃ d, X.M.edge d = e := Quot.exists_rep e

open Classical in
theorem incM_mulVec (c : X.M.Edge → ZMod 2) (v : X.M.Vtx) :
    (X.incM *ᵥ c) v = ∑ e, if X.Inc v e then c e else 0 := by
  simp [incM, Matrix.mulVec, dotProduct]

theorem bd_apply (S : X.M.Face → ZMod 2) (d : D) :
    (X.bdM *ᵥ S) (X.M.edge d) = S (X.M.face d) + S (X.M.face (X.M.a2 d)) := by
  classical
  have : ∀ e, (X.bdM *ᵥ S) e = S (X.M.face e.out) + S (X.M.face (X.M.a2 e.out)) := fun e => by
    simp only [bdM, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, ite_mul, one_mul,
      zero_mul, Finset.sum_add_distrib]
    have key : ∀ a : X.M.Face, ∑ x, (if a = x then S x else 0) = S a := fun a => by
      rw [Finset.sum_eq_single a (fun b _ hb => ite_eq_right_iff.2 fun h => (hb h.symm).elim) (by simp)]
      simp
    rw [key, key]
  rw [this]
  rcases edge_eq.1 (Quot.out_eq (X.M.edge d)) with h | h | h | h <;> rw [h]
  · simp [← X.M.a0_a2]
  · simp [X.M.a2_a2, add_comm]
  · simp [← X.M.a0_a2, X.M.a2_a2, add_comm]

/-- The flags at a vertex on a given edge are `d` and `a2 d`. -/
theorem at_edge (hbf : BigonFree X.On) {d x : D} :
    X.M.vtx x = X.M.vtx d ∧ X.M.edge x = X.M.edge d ↔ x = d ∨ x = X.M.a2 d := by
  refine ⟨fun ⟨hv, he⟩ => ?_, by rintro (rfl | rfl) <;> simp⟩
  rcases edge_eq.1 he with rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact (noLoop hbf _ hv).elim
  · exact .inr rfl
  · exact (noLoop hbf (X.M.a2 d) (by rw [hv, vtx_a2])).elim

omit [Fintype D] in
theorem inc_iff (d : D) (v : X.M.Vtx) :
    X.Inc v (X.M.edge d) ↔ v = X.M.vtx d ∨ v = X.M.vtx (X.M.a0 d) := by
  constructor
  · rintro ⟨x, rfl, hx⟩
    rcases edge_eq.1 hx with rfl | rfl | rfl | rfl <;> simp [X.M.a0_a2]
  · rintro (rfl | rfl)
    exacts [⟨d, rfl, rfl⟩, ⟨_, rfl, edge_a0 d⟩]

open Classical in
theorem sum_inc (hbf : BigonFree X.On) (d : D) (g : X.M.Vtx → ZMod 2) :
    ∑ v, (if X.Inc v (X.M.edge d) then g v else 0) = g (X.M.vtx d) + g (X.M.vtx (X.M.a0 d)) := by
  rw [← Finset.sum_filter]
  have : Finset.univ.filter (fun v => X.Inc v (X.M.edge d)) = {X.M.vtx d, X.M.vtx (X.M.a0 d)} := by
    ext v; simp [inc_iff]
  rw [this, Finset.sum_pair (noLoop hbf d).symm]

theorem two_eq (a b : ZMod 2) (h : a + b = 0) : a = b := by
  revert a b; decide

theorem add_self' (a : ZMod 2) : a + a = 0 := by revert a; decide

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

omit [Fintype D] in
/-- A function on vertices that is constant across every edge is constant. -/
theorem vtx_const {g : X.M.Vtx → ZMod 2} (h : ∀ d, g (X.M.vtx d) = g (X.M.vtx (X.M.a0 d)))
    (v w : X.M.Vtx) : g v = g w := by
  induction v using Quot.ind; induction w using Quot.ind
  exact const_of_inv (X := X) (fun d => g (X.M.vtx d)) (fun d => (h d).symm) (by simp) (by simp)
    _ _

omit [Fintype D] in
theorem finrank_ker_le {V W : Type*} [Fintype V] [AddCommGroup W] [Module (ZMod 2) W]
    {f : (V → ZMod 2) →ₗ[ZMod 2] W}
    (h : ∀ g ∈ LinearMap.ker f, ∀ v w, g v = g w) : Module.finrank (ZMod 2) (LinearMap.ker f) ≤ 1 := by
  refine (Submodule.finrank_mono (t := Submodule.span (ZMod 2) {fun _ => 1}) fun g hg => ?_).trans
    ((finrank_span_le_card _).trans (by simp))
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v0⟩⟩
  · exact Subsingleton.elim (0 : V → ZMod 2) g ▸ Submodule.zero_mem _
  · exact Submodule.mem_span_singleton.2 ⟨g v0, funext fun v => by simp [h g hg v0 v]⟩

/-- `∂₁ ∂₂ = 0`: boundaries are cycles. -/
theorem B1_le_Z1 (hbf : BigonFree X.On) : X.B1 ≤ X.Z1 := by
  classical
  rintro _ ⟨S, rfl⟩
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext v
  have hsum : ∑ x ∈ Finset.univ.filter (fun x => X.M.vtx x = v), S (X.M.face x) = 0 :=
    Finset.sum_involution (fun x _ => X.M.a1 x) (fun _ _ => by simp [add_self'])
      (fun x _ _ => X.M.a1_ne x) (fun _ hx => by simpa using hx) (fun x _ => X.M.a1_a1 x)
  rw [← Finset.sum_fiberwise_of_maps_to (g := X.M.edge) (t := Finset.univ) (by simp)] at hsum
  rw [incM_mulVec, Pi.zero_apply]
  refine (Finset.sum_congr rfl fun e _ => ?_).trans hsum
  obtain ⟨d, rfl⟩ := edge_surj e
  split_ifs with h
  · obtain ⟨d', rfl, he⟩ := h
    have : Finset.filter (fun x => X.M.edge x = X.M.edge d)
        (Finset.univ.filter fun x => X.M.vtx x = X.M.vtx d') = {d', X.M.a2 d'} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      rw [← at_edge hbf, ← he]
    rw [this, Finset.sum_pair (X.M.a2_ne d').symm, ← bd_apply, he]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact (h ⟨x, hx.1, hx.2⟩).elim

/-- **`Z₁/B₁` has dimension at most `1`** (from `χ = 1`): this is the page 42 relation
`c₂ = c(K)`, the first Betti number of the skeleton. -/
theorem finrank_Z1_le (hbf : BigonFree X.On) :
    Module.finrank (ZMod 2) X.Z1 ≤ Module.finrank (ZMod 2) X.B1 + 1 := by
  classical
  show Module.finrank _ (LinearMap.ker _) ≤ Module.finrank _ (LinearMap.range _) + 1
  have k1 : Module.finrank (ZMod 2) (LinearMap.ker X.incMᵀ.mulVecLin) ≤ 1 := by
    refine finrank_ker_le fun g hg => vtx_const fun d => two_eq _ _ ?_
    have := congrFun (LinearMap.mem_ker.1 hg) (X.M.edge d)
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, incM,
      Matrix.of_apply, ite_mul, one_mul, zero_mul, Pi.zero_apply] at this
    rwa [sum_inc hbf] at this
  have k2 : Module.finrank (ZMod 2) (LinearMap.ker X.bdM.mulVecLin) ≤ 1 := by
    refine finrank_ker_le fun S hS f f' => ?_
    have h : ∀ d, S (X.M.face d) = S (X.M.face (X.M.a2 d)) := fun d => two_eq _ _ <| by
      have := congrFun (LinearMap.mem_ker.1 hS) (X.M.edge d)
      rwa [Matrix.mulVecLin_apply, bd_apply] at this
    obtain ⟨d, rfl⟩ := Quot.exists_rep f
    obtain ⟨d', rfl⟩ := Quot.exists_rep f'
    exact const_of_inv (X := X) (fun d => S (X.M.face d)) (by simp) (by simp) (fun d => (h d).symm)
      d d'
  have r1 := LinearMap.finrank_range_add_finrank_ker X.incM.mulVecLin
  have r2 := LinearMap.finrank_range_add_finrank_ker X.incMᵀ.mulVecLin
  have r3 := LinearMap.finrank_range_add_finrank_ker X.bdM.mulVecLin
  have rt := Matrix.rank_transpose X.incM
  simp only [Module.finrank_fintype_fun_eq_card] at r1 r2 r3
  have he := X.euler
  simp only [GMap.euler, Nat.card_eq_fintype_card] at he
  unfold Matrix.rank at rt
  omega

end Chains

/-! ### The rotation at a vertex -/

variable (X) in
/-- The rotation `φ = a2 a1` around a vertex: from an edge-end to the next one. -/
def phi : Equiv.Perm D :=
  Function.Involutive.toPerm X.M.a2 X.M.a2_a2 * Function.Involutive.toPerm X.M.a1 X.M.a1_a1

omit [Fintype D] in
theorem phi_apply (x : D) : X.phi x = X.M.a2 (X.M.a1 x) := rfl

omit [Fintype D] in
theorem phi_inv_apply (x : D) : X.phi⁻¹ x = X.M.a1 (X.M.a2 x) :=
  (Equiv.Perm.inv_eq_iff_eq).2 (by simp [phi_apply, X.M.a1_a1, X.M.a2_a2])

omit [Fintype D] in
theorem a2_phi (x : D) : X.M.a2 (X.phi x) = X.M.a1 x := X.M.a2_a2 _

omit [Fintype D] in
/-- A function invariant under `φ` is invariant under its powers. -/
theorem zpow_inv {α : Type*} (g : D → α) (h : ∀ x, g (X.phi x) = g x) (k : ℤ) (x : D) :
    g ((X.phi ^ k) x) = g x := by
  induction k with
  | zero => simp
  | succ n ih => rw [show (n : ℤ) + 1 = 1 + n by ring, zpow_one_add, Equiv.Perm.mul_apply, h, ih]
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -n by ring, zpow_add, Equiv.Perm.mul_apply, zpow_neg_one, ← ih,
      ← h (X.phi⁻¹ _)]
    exact congrArg g ((Equiv.eq_symm_apply X.phi).mp rfl)

omit [Fintype D] in
@[simp] theorem vtx_phi1 (x : D) : X.M.vtx (X.phi x) = X.M.vtx x := by simp [phi_apply]

omit [Fintype D] in
@[simp] theorem vtx_phi (k : ℤ) (x : D) : X.M.vtx ((X.phi ^ k) x) = X.M.vtx x :=
  zpow_inv _ (fun x => by simp [phi_apply]) k x

omit [Fintype D] in
@[simp] theorem vtx_phi' (k : ℕ) (x : D) : X.M.vtx ((X.phi ^ k) x) = X.M.vtx x := by
  simpa using vtx_phi (X := X) k x

omit [Fintype D] in
/-- `a2 φ^k = φ^{-k} a2`. -/
theorem a2_zpow (k : ℤ) (x : D) : X.M.a2 ((X.phi ^ k) x) = (X.phi ^ (-k)) (X.M.a2 x) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [show (n : ℤ) + 1 = 1 + n by ring, zpow_one_add, Equiv.Perm.mul_apply, a2_phi,
      show -(1 + (n : ℤ)) = -1 + -n by ring, zpow_add, Equiv.Perm.mul_apply, ← ih, zpow_neg_one,
      phi_inv_apply, X.M.a2_a2]
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -n by ring, zpow_add, Equiv.Perm.mul_apply, zpow_neg_one,
      phi_inv_apply, ← phi_apply, ih, ← Equiv.Perm.mul_apply, ← zpow_one_add]
    congr 2; ring

omit [Fintype D] in
/-- The two orbits of `φ` at a vertex are exchanged by `a2`: `a2 φ^i x ≠ φ^j x`. -/
theorem a2_ne_zpow (i j : ℤ) (x : D) : X.M.a2 ((X.phi ^ i) x) ≠ (X.phi ^ j) x := by
  intro h
  rw [a2_zpow] at h
  have h' : X.M.a2 x = (X.phi ^ (i + j)) x := by
    have := congrArg (X.phi ^ i) h
    rwa [← Equiv.Perm.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Equiv.Perm.one_apply,
      ← Equiv.Perm.mul_apply, ← zpow_add] at this
  obtain ⟨t, ht | ht⟩ := Int.even_or_odd' (i + j)
  · apply X.M.a2_ne ((X.phi ^ t) x)
    rw [a2_zpow, h', ht, ← Equiv.Perm.mul_apply, ← zpow_add]
    congr 2; ring
  · apply X.M.a1_ne ((X.phi ^ t) x)
    rw [← a2_phi, ← Equiv.Perm.mul_apply, ← zpow_one_add, a2_zpow, h', ht, ← Equiv.Perm.mul_apply,
      ← zpow_add]
    congr 2; ring

omit [Fintype D] in
/-- The flags at the vertex of `x` are the `φ^k x` and the `a2 φ^k x`. -/
theorem vtx_orbit {x y : D} (h : X.M.vtx y = X.M.vtx x) :
    ∃ k : ℤ, y = (X.phi ^ k) x ∨ y = X.M.a2 ((X.phi ^ k) x) := by
  let S : D → Prop := fun y => ∃ k : ℤ, y = (X.phi ^ k) x ∨ y = X.M.a2 ((X.phi ^ k) x)
  have c1 : ∀ u, S u → S (X.M.a1 u) := by
    rintro u ⟨k, rfl | rfl⟩
    · exact ⟨1 + k, .inr (by rw [zpow_one_add, Equiv.Perm.mul_apply, a2_phi])⟩
    · exact ⟨-1 + k, .inl (by rw [zpow_add, Equiv.Perm.mul_apply, zpow_neg_one, phi_inv_apply])⟩
  have c2 : ∀ u, S u → S (X.M.a2 u) := by
    rintro u ⟨k, rfl | rfl⟩
    · exact ⟨k, .inr rfl⟩
    · exact ⟨k, .inl (X.M.a2_a2 _)⟩
  refine (eqvGen_iff S ?_ (Quot.eqvGen_exact h)).2 ⟨0, .inl rfl⟩
  rintro u w (rfl | rfl)
  · exact ⟨c1 u, fun h => by simpa [X.M.a1_a1] using c1 _ h⟩
  · exact ⟨c2 u, fun h => by simpa [X.M.a2_a2] using c2 _ h⟩

open Classical in
variable (X) in
/-- The number `ν(v)` of lines through a vertex. -/
noncomputable def nu (v : X.M.Vtx) : ℕ :=
  ((Finset.univ.filter fun d => X.M.vtx d = v).image X.line).card

variable (X) in
/-- **Going straight** (page 60; (22) of page 41): half a turn around a vertex of `ν` lines,
`ν` edge-ends further, one finds the same line. -/
def Straight : Prop := ∀ d, X.line ((X.phi ^ X.nu (X.M.vtx d)) d) = X.line d

open Classical in
theorem card_vtx (x : D) :
    (Finset.univ.filter fun d => X.M.vtx d = X.M.vtx x).card = 4 * X.nu (X.M.vtx x) := by
  rw [Finset.card_eq_sum_card_image X.line, nu, Finset.sum_const_nat (m := 4), mul_comm]
  intro l hl
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hl
  have h4 := X.pass e
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
  rw [Finset.filter_filter, ← h4]
  congr 1; ext a; simp [(Finset.mem_filter.1 he).2]

open Classical in
/-- A period of `φ` at a flag is at least the number `2ν` of edge-ends. -/
theorem four_nu_le (x : D) {q : ℕ} (hq : 0 < q) (h : (X.phi ^ q) x = x) :
    4 * X.nu (X.M.vtx x) ≤ 2 * q := by
  rw [← card_vtx]
  have hsub : (Finset.univ.filter fun d => X.M.vtx d = X.M.vtx x) ⊆
      ((Finset.range q) ×ˢ (Finset.univ : Finset Bool)).image
        fun p => if p.2 then X.M.a2 ((X.phi ^ p.1) x) else (X.phi ^ p.1) x := by
    intro y hy
    obtain ⟨k, hk⟩ := vtx_orbit (Finset.mem_filter.1 hy).2
    have hr : (X.phi ^ k) x = (X.phi ^ (k % q).toNat) x := by
      have h' : ((X.phi ^ (q : ℤ)) ^ (k / q)) x = x :=
        Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (by simpa using h) _
      conv_lhs => rw [← Int.emod_add_mul_ediv k q, zpow_add, Equiv.Perm.mul_apply, zpow_mul, h']
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
    have hlt : (k % q).toNat < q := by
      have := Int.emod_lt_of_pos k (by omega : (0 : ℤ) < q); omega
    rcases hk with rfl | rfl
    exacts [Finset.mem_image.2 ⟨((k % q).toNat, false), by simp [hlt], by simp [hr]⟩,
      Finset.mem_image.2 ⟨((k % q).toNat, true), by simp [hlt], by simp [hr]⟩]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [mul_comm]

omit [Fintype D] in
theorem a2_ne_pow (i j : ℕ) (x : D) : X.M.a2 ((X.phi ^ i) x) ≠ (X.phi ^ j) x := by
  simpa using a2_ne_zpow (X := X) i j x

/-- Distinct powers below `2ν` of `φ` move a flag to distinct flags. -/
theorem pow_ne (y : D) {a b : ℕ} (hab : a < b) (hb : b < 2 * X.nu (X.M.vtx y)) :
    (X.phi ^ a) y ≠ (X.phi ^ b) y := fun h => by
  have := four_nu_le ((X.phi ^ a) y) (q := b - a) (by omega) (by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hab.le, ← h])
  rw [vtx_phi'] at this
  omega

theorem straight_pow (hs : X.Straight) (y : D) (i : ℕ) :
    X.line ((X.phi ^ (i + X.nu (X.M.vtx y))) y) = X.line ((X.phi ^ i) y) := by
  rw [add_comm, pow_add, Equiv.Perm.mul_apply]
  simpa using hs ((X.phi ^ i) y)

open Classical in
/-- The `ν` edge-ends met in half a turn around a vertex carry distinct lines. -/
theorem line_inj (hs : X.Straight) (y : D) {i j : ℕ} (hij : i < j)
    (hj : j < X.nu (X.M.vtx y)) : X.line ((X.phi ^ i) y) ≠ X.line ((X.phi ^ j) y) := by
  intro hl
  set ν := X.nu (X.M.vtx y)
  have hn : [(X.phi ^ i) y, (X.phi ^ j) y, (X.phi ^ (i + ν)) y, (X.phi ^ (j + ν)) y,
      X.M.a2 ((X.phi ^ i) y)].Nodup := by
    have p : ∀ {a b : ℕ}, a < b → b < 2 * ν → (X.phi ^ a) y ≠ (X.phi ^ b) y :=
      fun h h' => pow_ne y h h'
    have q := a2_ne_pow (X := X)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨p hij (by omega), p (by omega) (by omega), p (by omega) (by omega),
      fun h => q i i y h.symm⟩, ⟨p (by omega) (by omega), p (by omega) (by omega),
      fun h => q i j y h.symm⟩, ⟨p (by omega) (by omega), fun h => q i _ y h.symm⟩,
      fun h => q i _ y h.symm⟩
  have h4 := X.pass ((X.phi ^ i) y)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
  have hsub : [(X.phi ^ i) y, (X.phi ^ j) y, (X.phi ^ (i + ν)) y, (X.phi ^ (j + ν)) y,
      X.M.a2 ((X.phi ^ i) y)].toFinset ⊆ Finset.univ.filter fun e =>
        X.M.vtx e = X.M.vtx ((X.phi ^ i) y) ∧ X.line e = X.line ((X.phi ^ i) y) := by
    intro e he
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_insert,
      Finset.mem_singleton] at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases he with rfl | rfl | rfl | rfl | rfl
    · simp
    · simp [hl]
    · exact ⟨by simp, straight_pow hs y i⟩
    · exact ⟨by simp, (straight_pow hs y j).trans hl.symm⟩
    · simp [X.line_a2]
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn, h4] at this
  simp at this

open Classical in
/-- **Half a turn meets every other line once**: in `φ x, …, φ^ν x` each line through the
vertex appears exactly once. -/
theorem rot_card (hs : X.Straight) (y : D) {m : L} (hm : X.On (X.M.vtx y) m) :
    ((Finset.range (X.nu (X.M.vtx y))).filter fun i => X.line ((X.phi ^ i) y) = m).card = 1 := by
  set T := (Finset.univ.filter fun d => X.M.vtx d = X.M.vtx y).image X.line
  have hinj : Set.InjOn (fun i => X.line ((X.phi ^ i) y)) ↑(Finset.range (X.nu (X.M.vtx y))) := by
    intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with hij | rfl | hij
    exacts [(line_inj hs y hij hj h).elim, rfl, (line_inj hs y hij hi h.symm).elim]
  have hsub : (Finset.range (X.nu (X.M.vtx y))).image (fun i => X.line ((X.phi ^ i) y)) ⊆ T :=
    fun l hl => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hl
      exact Finset.mem_image.2 ⟨_, by simp, rfl⟩
  have heq := Finset.eq_of_subset_of_card_le hsub
    (by rw [Finset.card_image_of_injOn hinj, Finset.card_range]; rfl)
  obtain ⟨d, hd, rfl⟩ := hm
  obtain ⟨i, hi, hil⟩ := Finset.mem_image.1 (heq ▸ Finset.mem_image.2 ⟨d, by simp [hd], rfl⟩ :
    X.line d ∈ (Finset.range (X.nu (X.M.vtx y))).image (fun i => X.line ((X.phi ^ i) y)))
  refine Finset.card_eq_one.2 ⟨i, Finset.ext fun k => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨fun ⟨hk, hkl⟩ => hinj hk hi (hkl.trans hil.symm), fun h => h ▸ ⟨hi, hil⟩⟩

open Classical in
/-- The two edges of the line of `x` at the vertex of `x`: those of `x` and of `φ^ν x`. -/
theorem line_edges (hbf : BigonFree X.On) (hs : X.Straight) (x : D) :
    (Finset.univ.filter fun e => X.Inc (X.M.vtx x) e ∧ X.lineE e = X.line x) =
      {X.M.edge x, X.M.edge ((X.phi ^ X.nu (X.M.vtx x)) x)} ∧
    X.M.edge x ≠ X.M.edge ((X.phi ^ X.nu (X.M.vtx x)) x) := by
  set ν := X.nu (X.M.vtx x)
  set x' := (X.phi ^ ν) x
  have hx' : X.line x' = X.line x := hs x
  have hν : 0 < ν := Finset.card_pos.2 ⟨X.line x, Finset.mem_image.2 ⟨x, by simp, rfl⟩⟩
  have hxx' : x ≠ x' := by simpa using pow_ne (X := X) x hν (by omega)
  have hn : [x, X.M.a2 x, x', X.M.a2 x'].Nodup := by
    have q := a2_ne_pow (X := X)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨(X.M.a2_ne x).symm, hxx', fun h => by simpa using q ν 0 x h.symm⟩,
      ⟨by simpa using q 0 ν x, fun h => hxx' (by simpa [X.M.a2_a2] using congrArg X.M.a2 h)⟩,
      (X.M.a2_ne x').symm⟩
  have hee : X.M.edge x ≠ X.M.edge x' := fun h => by
    rcases edge_eq.1 h.symm with h | h | h | h
    · exact hxx' h.symm
    · exact noLoop hbf x (by rw [← h]; simp [x'])
    · exact a2_ne_pow (X := X) 0 ν x (by simpa using h.symm)
    · exact noLoop hbf (X.M.a2 x) (by rw [← h]; simp [x'])
  have hfil : (Finset.univ.filter fun e => X.Inc (X.M.vtx x) e ∧ X.lineE e = X.line x) =
      {X.M.edge x, X.M.edge x'} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨d, hdv, rfl⟩, hdl⟩
      have := at_four hn (by simp [x', hx', X.line_a2]) hdv hdl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl)
      exacts [⟨⟨x, rfl, rfl⟩, rfl⟩, ⟨⟨x', by simp [x'], rfl⟩, hx'⟩]
  exact ⟨hfil, hee⟩

/-! ### The parity lemma -/

section Parity

open Matrix

/-- Turning by `φ` across an edge of the boundary `∂S` changes side of `S`. -/
theorem face_phi (S : X.M.Face → ZMod 2) (y : D) :
    S (X.M.face (X.phi y)) = S (X.M.face y) + (X.bdM *ᵥ S) (X.M.edge (X.phi y)) := by
  rw [show X.M.edge (X.phi y) = X.M.edge (X.M.a1 y) by simp [phi_apply], bd_apply, face_a1,
    ← add_assoc, add_self', zero_add]
  rfl

theorem face_phi_pow (S : X.M.Face → ZMod 2) (y : D) (n : ℕ) :
    S (X.M.face ((X.phi ^ n) y)) =
      S (X.M.face y) + ∑ i ∈ Finset.range n, (X.bdM *ᵥ S) (X.M.edge ((X.phi ^ (i + 1)) y)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, face_phi S, ih, Finset.sum_range_succ,
      add_assoc, ← Equiv.Perm.mul_apply, ← pow_succ']

open Classical in
/-- **The parity lemma.** Let `z = ∂S` be a boundary and `Δ` a line carrying no edge of `z`,
such that at each vertex of `Δ` the cycle `z` either is absent or goes straight across along a
single other line. Then `Δ` meets `z` in an even number of vertices: a closed curve crosses the
boundary of a union of faces an even number of times. -/
theorem parity (hbf : BigonFree X.On) (hs : X.Straight) (S : X.M.Face → ZMod 2) (Δ : L)
    (h1 : ∀ e, X.lineE e = Δ → (X.bdM *ᵥ S) e = 0)
    (h2 : ∀ w, X.On w Δ → (∀ e, X.Inc w e → (X.bdM *ᵥ S) e = 0) ∨
      ∃ m, m ≠ Δ ∧ X.On w m ∧ ∀ e, X.Inc w e → (X.bdM *ᵥ S) e = if X.lineE e = m then 1 else 0) :
    ∑ w, (if X.On w Δ ∧ ∃ e, X.Inc w e ∧ (X.bdM *ᵥ S) e ≠ 0 then (1 : ZMod 2) else 0) = 0 := by
  set z := X.bdM *ᵥ S
  let μ : X.M.Edge → ZMod 2 := fun e => S (X.M.face e.out)
  have hμ : ∀ d, X.line d = Δ → μ (X.M.edge d) = S (X.M.face d) := fun d hd => by
    have h0 : S (X.M.face (X.M.a2 d)) = S (X.M.face d) :=
      (two_eq _ _ (by rw [add_comm, ← bd_apply]; exact h1 _ hd))
    simp only [μ]
    rcases edge_eq.1 (Quot.out_eq (X.M.edge d)) with h | h | h | h <;> rw [h]
    · simp
    · exact h0
    · simpa using h0
  -- the local count at a vertex of `Δ`
  have loc : ∀ w, X.On w Δ → ∑ e, (if X.Inc w e ∧ X.lineE e = Δ then μ e else 0) =
      if ∃ e, X.Inc w e ∧ z e ≠ 0 then 1 else 0 := by
    rintro w ⟨x, rfl, hx⟩
    set ν := X.nu (X.M.vtx x)
    set x' := (X.phi ^ ν) x
    have hx' : X.line x' = Δ := (hs x).trans hx
    obtain ⟨hfil, hee⟩ := line_edges hbf hs x
    rw [hx] at hfil
    rw [← Finset.sum_filter, hfil, Finset.sum_pair hee, hμ x hx, hμ x' hx', face_phi_pow S]
    rcases h2 _ ⟨x, rfl, hx⟩ with h | ⟨m, hm, hmw, hz⟩
    · rw [Finset.sum_eq_zero fun i _ => h _ ⟨_, by simp, rfl⟩, ite_eq_right fun ⟨e, he, hz⟩ => hz (h e he),
        add_zero, add_self']
    · obtain ⟨d, hdv, rfl⟩ := hmw
      rw [ite_eq_left ⟨X.M.edge d, ⟨d, hdv, rfl⟩, by rw [hz _ ⟨d, hdv, rfl⟩]; simp⟩, ← add_assoc,
        add_self', zero_add]
      have hr := rot_card hs (X.phi x) (m := X.line d) ⟨d, by rw [vtx_phi1]; exact hdv, rfl⟩
      rw [vtx_phi1] at hr
      have : ∀ i ∈ Finset.range ν, z (X.M.edge ((X.phi ^ (i + 1)) x)) =
          if X.line ((X.phi ^ i) (X.phi x)) = X.line d then 1 else 0 := fun i _ => by
        rw [hz _ ⟨_, by simp, rfl⟩, lineE_edge, ← Equiv.Perm.mul_apply, ← pow_succ]
      rw [Finset.sum_congr rfl this, Finset.sum_boole, hr]
      simp
  -- the global count: every edge of `Δ` has two ends
  calc ∑ w, (if X.On w Δ ∧ ∃ e, X.Inc w e ∧ z e ≠ 0 then (1 : ZMod 2) else 0)
      = ∑ w, ∑ e, (if X.Inc w e ∧ X.lineE e = Δ then μ e else 0) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        by_cases hw : X.On w Δ
        · rw [loc w hw]; simp [hw]
        · rw [ite_eq_right (fun h => hw h.1), Finset.sum_eq_zero]
          rintro e - 
          rw [ite_eq_right]
          rintro ⟨⟨d, rfl, rfl⟩, hd⟩
          exact hw ⟨d, rfl, hd⟩
    _ = ∑ e, ∑ w, (if X.Inc w e then (if X.lineE e = Δ then μ e else 0) else 0) := by
        rw [Finset.sum_comm]; simp only [ite_and]
    _ = 0 := Finset.sum_eq_zero fun e _ => by
        obtain ⟨d, rfl⟩ := edge_surj e
        rw [sum_inc hbf d (fun _ => if X.lineE (X.M.edge d) = Δ then μ (X.M.edge d) else 0),
          add_self']

omit [Fintype D] in
theorem on_of_inc {w : X.M.Vtx} {e : X.M.Edge} (h : X.Inc w e) : X.On w (X.lineE e) := by
  obtain ⟨d, rfl, rfl⟩ := h; exact ⟨d, rfl, rfl⟩

omit [Fintype D] in
/-- A chain supported on the line `x` vanishes at the edges of a vertex off `x`. -/
theorem off_line {x : L} {P : X.M.Edge → ZMod 2} (hP : ∀ e, P e ≠ 0 → X.lineE e = x)
    {w : X.M.Vtx} (hw : ¬X.On w x) {e : X.M.Edge} (he : X.Inc w e) : P e = 0 :=
  by_contra fun h => hw (hP e h ▸ on_of_inc he)

open Classical in
/-- A line is a cycle. -/
theorem lineChain_mem (hbf : BigonFree X.On) (hs : X.Straight) (l : L) : X.lineChain l ∈ X.Z1 := by
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext v
  rw [incM_mulVec, Pi.zero_apply]
  simp only [lineChain, ← ite_and, Finset.sum_boole]
  by_cases hv : X.On v l
  · obtain ⟨x, rfl, rfl⟩ := hv
    rw [(line_edges hbf hs x).1, Finset.card_pair (line_edges hbf hs x).2]; rfl
  · rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun e _ ⟨h1, h2⟩ => hv (h2 ▸ on_of_inc h1))]
    rfl

open Classical in
/-- **A line does not bound.** Another line `Δ` meets it once, straight across. -/
theorem lineChain_not_mem (hbf : BigonFree X.On) (hs : X.Straight) {a Δ : L} (h : a ≠ Δ) :
    X.lineChain a ∉ X.B1 := by
  rintro ⟨S, hS⟩
  simp only [Matrix.mulVecLin_apply] at hS
  have key := parity hbf hs S Δ (fun e he => by simp [hS, lineChain, he, h.symm]) fun w _ => by
    by_cases hw : X.On w a
    · exact .inr ⟨a, h, hw, fun e _ => by rw [hS]; rfl⟩
    · exact .inl fun e he => by rw [hS]; exact off_line (fun e h' => by
        simp only [lineChain] at h'; by_contra hc; exact h' (by simp [hc])) hw he
  obtain ⟨v, ⟨hva, hvΔ⟩, hu⟩ := X.meet a Δ h
  rw [Finset.sum_eq_single v] at key
  · rw [ite_eq_left] at key
    · exact one_ne_zero key
    obtain ⟨d, hd, rfl⟩ := hva
    exact ⟨hvΔ, X.M.edge d, ⟨d, hd, rfl⟩, by simp [hS, lineChain]⟩
  · rintro w - hw
    refine ite_eq_right fun ⟨h1, e, he, h2⟩ => hw (hu w ⟨?_, h1⟩)
    rw [hS] at h2
    simp only [lineChain, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h2
    exact h2 ▸ on_of_inc he
  · simp

/-- Since `Z₁/B₁` has dimension `≤ 1` and a line does not bound, every cycle bounds, or bounds
after adding any line. -/
theorem Z1_cases (hbf : BigonFree X.On) (hs : X.Straight) {a Δ : L} (h : a ≠ Δ)
    {z : X.M.Edge → ZMod 2} (hz : z ∈ X.Z1) : z ∈ X.B1 ∨ z + X.lineChain a ∈ X.B1 := by
  set c := X.lineChain a
  have hc := lineChain_not_mem hbf hs h
  have hc0 : c ≠ 0 := fun h0 => hc (by rw [show X.lineChain a = 0 from h0]; exact Submodule.zero_mem _)
  have hinf : X.B1 ⊓ Submodule.span (ZMod 2) {c} = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun y ⟨hy, hy'⟩ => ?_
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy'
    by_cases ht : t = 0
    · simp [ht]
    · exact (hc (by simpa [smul_smul, inv_mul_cancel₀ ht] using Submodule.smul_mem _ t⁻¹ hy)).elim
  have hle : X.B1 ⊔ Submodule.span (ZMod 2) {c} ≤ X.Z1 :=
    sup_le (B1_le_Z1 hbf) ((Submodule.span_singleton_le_iff_mem _ _).2 (lineChain_mem hbf hs a))
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq X.B1 (Submodule.span (ZMod 2) {c})
  rw [hinf, finrank_bot, finrank_span_singleton hc0] at hdim
  have heq := Submodule.eq_of_le_of_finrank_le hle (by have := finrank_Z1_le hbf; omega)
  obtain ⟨b, hb, y, hy, rfl⟩ := Submodule.mem_sup.1 (heq ▸ hz)
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rcases zmod2_cases t with rfl | rfl
  · left; rwa [zero_smul, add_zero]
  · right
    rwa [one_smul, add_assoc, show c + c = 0 from funext fun e => add_self' _, add_zero]

omit [Fintype D] in
theorem meet_eq {l l' : L} (h : l ≠ l') {v w : X.M.Vtx} (hv : X.On v l) (hv' : X.On v l')
    (hw : X.On w l) (hw' : X.On w l') : v = w := by
  obtain ⟨u, -, hu⟩ := X.meet l l' h
  exact (hu v ⟨hv, hv'⟩).trans (hu w ⟨hw, hw'⟩).symm

open Classical in
/-- A segment `P` of the line `x` (a chain on `x` with boundary `p + q`) takes the same value on
the two edges of `x` at any vertex other than `p, q`. -/
theorem seg_val (hbf : BigonFree X.On) (hs : X.Straight) {x : L} {p q : X.M.Vtx}
    {P : X.M.Edge → ZMod 2} (hP : ∀ e, P e ≠ 0 → X.lineE e = x)
    (hb : X.incM *ᵥ P = Pi.single p 1 + Pi.single q 1) {w : X.M.Vtx} (hp : w ≠ p) (hq : w ≠ q)
    {ex : X.M.Edge} (hex : X.lineE ex = x) (hw : X.Inc w ex) (e : X.M.Edge) (he : X.Inc w e) :
    P e = if X.lineE e = x then P ex else 0 := by
  have h0 := congrFun hb w
  rw [incM_mulVec] at h0
  simp only [Pi.add_apply, Pi.single_apply, hp, hq, ite_false, add_zero] at h0
  obtain ⟨y, rfl, hy⟩ := hw
  have hyx : X.line y = x := by rw [← hex, ← hy]; rfl
  obtain ⟨hfil, hee⟩ := line_edges hbf hs y
  rw [hyx] at hfil
  rw [Finset.sum_congr rfl (g := fun e => if X.Inc (X.M.vtx y) e ∧ X.lineE e = x then P e else 0)
    (fun e _ => by
      by_cases h1 : X.Inc (X.M.vtx y) e <;> by_cases h2 : X.lineE e = x <;> simp [h1, h2]
      exact by_contra fun h => h2 (hP e h)), ← Finset.sum_filter, hfil,
    Finset.sum_pair hee] at h0
  have h0 := two_eq _ _ h0
  have mem : ∀ e, X.Inc (X.M.vtx y) e → X.lineE e = x →
      e = X.M.edge y ∨ e = X.M.edge ((X.phi ^ X.nu (X.M.vtx y)) y) := fun e h1 h2 => by
    have : e ∈ Finset.univ.filter fun e => X.Inc (X.M.vtx y) e ∧ X.lineE e = x := by simp [h1, h2]
    rw [hfil] at this; simpa using this
  split_ifs with h
  · rcases mem e he h with rfl | rfl <;> rcases mem ex ⟨y, rfl, hy⟩ hex with h' | h' <;>
      rw [h'] <;> simp [h0]
  · exact by_contra fun h' => h (hP e h')

open Classical in
theorem ind_val {Δ x : L} {z : X.M.Edge → ZMod 2} {w : X.M.Vtx} (hw : X.On w Δ) {t : ZMod 2}
    (hz : ∀ e, X.Inc w e → z e = if X.lineE e = x then t else 0) {ex : X.M.Edge}
    (hex : X.Inc w ex) (hx : X.lineE ex = x) :
    (if X.On w Δ ∧ ∃ e, X.Inc w e ∧ z e ≠ 0 then (1 : ZMod 2) else 0) = t := by
  rcases zmod2_cases t with rfl | rfl
  · exact ite_eq_right fun ⟨_, e, he, h⟩ => h (by rw [hz e he]; simp)
  · exact ite_eq_left ⟨hw, ex, hex, by rw [hz ex hex, ite_eq_left hx]; simp⟩

omit [Fintype D] in
open Classical in
theorem cross_of {Δ x : L} {z : X.M.Edge → ZMod 2} {w : X.M.Vtx} (hxΔ : x ≠ Δ) (hwx : X.On w x)
    {t : ZMod 2} (hz : ∀ e, X.Inc w e → z e = if X.lineE e = x then t else 0) :
    (∀ e, X.Inc w e → z e = 0) ∨
      ∃ m, m ≠ Δ ∧ X.On w m ∧ ∀ e, X.Inc w e → z e = if X.lineE e = m then 1 else 0 := by
  rcases zmod2_cases t with rfl | rfl
  · exact .inl fun e he => by rw [hz e he]; simp
  · exact .inr ⟨x, hxΔ, hwx, hz⟩

open Classical in
/-- **A triangle and a fourth line: the bounding direction.** If the triangle cycle
`Pa + Pb + Pc` (segments of three non-concurrent lines between their meeting points) bounds,
the fourth line `Δ`, through none of the three vertices, crosses an even number of its sides. -/
theorem tri_bound (hbf : BigonFree X.On) (hs : X.Straight) {a b c Δ : L}
    {pab pbc pca : X.M.Vtx} (hpab : X.On pab a ∧ X.On pab b) (hpbc : X.On pbc b ∧ X.On pbc c)
    (hpca : X.On pca c ∧ X.On pca a) (hab : a ≠ b) (hnc : ¬X.On pab c)
    (hΔ : ¬X.On pab Δ ∧ ¬X.On pbc Δ ∧ ¬X.On pca Δ) {Pa Pb Pc : X.M.Edge → ZMod 2}
    (sa : ∀ e, Pa e ≠ 0 → X.lineE e = a) (sb : ∀ e, Pb e ≠ 0 → X.lineE e = b)
    (sc : ∀ e, Pc e ≠ 0 → X.lineE e = c)
    (ba : X.incM *ᵥ Pa = Pi.single pab 1 + Pi.single pca 1)
    (bb : X.incM *ᵥ Pb = Pi.single pab 1 + Pi.single pbc 1)
    (bc : X.incM *ᵥ Pc = Pi.single pbc 1 + Pi.single pca 1) {ea eb ec : X.M.Edge}
    (ha : X.lineE ea = a ∧ ∃ w, X.Inc w ea ∧ X.On w Δ)
    (hb : X.lineE eb = b ∧ ∃ w, X.Inc w eb ∧ X.On w Δ)
    (hc : X.lineE ec = c ∧ ∃ w, X.Inc w ec ∧ X.On w Δ) (hz : Pa + Pb + Pc ∈ X.B1) :
    Pa ea + Pb eb + Pc ec = 0 := by
  classical
  obtain ⟨S, hS⟩ := hz
  simp only [Matrix.mulVecLin_apply] at hS
  obtain ⟨hΔ1, hΔ2, hΔ3⟩ := hΔ
  have hac : a ≠ c := fun h => hnc (h ▸ hpab.1)
  have hbc : b ≠ c := fun h => hnc (h ▸ hpab.2)
  have haΔ : a ≠ Δ := fun h => hΔ1 (h ▸ hpab.1)
  have hbΔ : b ≠ Δ := fun h => hΔ1 (h ▸ hpab.2)
  have hcΔ : c ≠ Δ := fun h => hΔ2 (h ▸ hpbc.2)
  obtain ⟨wa, hwa, hwaΔ⟩ := ha.2
  obtain ⟨wb, hwb, hwbΔ⟩ := hb.2
  obtain ⟨wc, hwc, hwcΔ⟩ := hc.2
  have oa : X.On wa a := ha.1 ▸ on_of_inc hwa
  have ob : X.On wb b := hb.1 ▸ on_of_inc hwb
  have oc : X.On wc c := hc.1 ▸ on_of_inc hwc
  have nab : ¬X.On wa b := fun h => hΔ1 (meet_eq hab oa h hpab.1 hpab.2 ▸ hwaΔ)
  have nac : ¬X.On wa c := fun h => hΔ3 (meet_eq hac oa h hpca.2 hpca.1 ▸ hwaΔ)
  have nba : ¬X.On wb a := fun h => hΔ1 (meet_eq hab h ob hpab.1 hpab.2 ▸ hwbΔ)
  have nbc : ¬X.On wb c := fun h => hΔ2 (meet_eq hbc ob h hpbc.1 hpbc.2 ▸ hwbΔ)
  have nca : ¬X.On wc a := fun h => hΔ3 (meet_eq hac h oc hpca.2 hpca.1 ▸ hwcΔ)
  have ncb : ¬X.On wc b := fun h => hΔ2 (meet_eq hbc h oc hpbc.1 hpbc.2 ▸ hwcΔ)
  have ne : ∀ {w v : X.M.Vtx} {l : L}, X.On w l → ¬X.On v l → w ≠ v := fun h h' e => h' (e ▸ h)
  have va : ∀ e, X.Inc wa e → (Pa + Pb + Pc) e = if X.lineE e = a then Pa ea else 0 :=
    fun e he => by
      simp only [Pi.add_apply, off_line sb nab he, off_line sc nac he, add_zero]
      exact seg_val hbf hs sa ba (ne hwaΔ hΔ1) (ne hwaΔ hΔ3) ha.1 hwa e he
  have vb : ∀ e, X.Inc wb e → (Pa + Pb + Pc) e = if X.lineE e = b then Pb eb else 0 :=
    fun e he => by
      simp only [Pi.add_apply, off_line sa nba he, off_line sc nbc he, add_zero, zero_add]
      exact seg_val hbf hs sb bb (ne hwbΔ hΔ1) (ne hwbΔ hΔ2) hb.1 hwb e he
  have vc : ∀ e, X.Inc wc e → (Pa + Pb + Pc) e = if X.lineE e = c then Pc ec else 0 :=
    fun e he => by
      simp only [Pi.add_apply, off_line sa nca he, off_line sb ncb he, zero_add]
      exact seg_val hbf hs sc bc (ne hwcΔ hΔ2) (ne hwcΔ hΔ3) hc.1 hwc e he
  have v0 : ∀ w, ¬X.On w a → ¬X.On w b → ¬X.On w c → ∀ e, X.Inc w e → (Pa + Pb + Pc) e = 0 :=
    fun w h1 h2 h3 e he => by simp [off_line sa h1 he, off_line sb h2 he, off_line sc h3 he]
  have z0 : ∀ {x : L} {P : X.M.Edge → ZMod 2}, (∀ e, P e ≠ 0 → X.lineE e = x) → x ≠ Δ →
      ∀ {e}, X.lineE e = Δ → P e = 0 := fun hP hx e he =>
    by_contra fun h => hx ((hP e h).symm.trans he)
  have key := parity hbf hs S Δ (fun e he => by
      rw [hS, Pi.add_apply, Pi.add_apply, z0 sa haΔ he, z0 sb hbΔ he, z0 sc hcΔ he]; simp)
    (fun w hw => by
      rw [hS]
      by_cases h1 : X.On w a
      · exact cross_of haΔ h1 (meet_eq haΔ h1 hw oa hwaΔ ▸ va)
      by_cases h2 : X.On w b
      · exact cross_of hbΔ h2 (meet_eq hbΔ h2 hw ob hwbΔ ▸ vb)
      by_cases h3 : X.On w c
      · exact cross_of hcΔ h3 (meet_eq hcΔ h3 hw oc hwcΔ ▸ vc)
      exact .inl (v0 w h1 h2 h3))
  rw [hS] at key
  rw [← key, Finset.sum_congr rfl fun w _ => show _ = (if w = wa then Pa ea else 0) +
      (if w = wb then Pb eb else 0) + (if w = wc then Pc ec else 0) from ?_]
  · simp [Finset.sum_add_distrib]
  by_cases h1 : w = wa
  · subst h1
    rw [ite_eq_left rfl, ite_eq_right (ne oa nba), ite_eq_right (ne oa nca), add_zero, add_zero]
    exact ind_val hwaΔ va hwa ha.1
  by_cases h2 : w = wb
  · subst h2
    rw [ite_eq_right (ne ob nab), ite_eq_left rfl, ite_eq_right (ne ob ncb), add_zero, zero_add]
    exact ind_val hwbΔ vb hwb hb.1
  by_cases h3 : w = wc
  · subst h3
    rw [ite_eq_right (ne oc nac), ite_eq_right (ne oc nbc), ite_eq_left rfl, zero_add, zero_add]
    exact ind_val hwcΔ vc hwc hc.1
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, add_zero, add_zero]
  exact ite_eq_right fun ⟨hw, e, he, hz⟩ => hz (v0 w (fun h => h1 (meet_eq haΔ h hw oa hwaΔ))
    (fun h => h2 (meet_eq hbΔ h hw ob hwbΔ)) (fun h => h3 (meet_eq hcΔ h hw oc hwcΔ)) e he)

/-- Exactly one of a cycle `z` and `z + D`, for a line `D`, bounds. -/
theorem flip (hbf : BigonFree X.On) (hs : X.Straight) {a Δ : L} (h : a ≠ Δ)
    {z : X.M.Edge → ZMod 2} (hz : z ∈ X.Z1) : z ∈ X.B1 ↔ z + X.lineChain a ∉ X.B1 :=
  ⟨fun h1 h2 => lineChain_not_mem hbf hs h (by
      have hzz : z + z = 0 := funext fun e => add_self' (z e)
      have := X.B1.add_mem h1 h2
      rwa [← add_assoc, hzz, zero_add] at this),
    fun h1 => (Z1_cases hbf hs h hz).resolve_right h1⟩

open Classical in
/-- **The orientation of a triangle is read on the skeleton** (page 50, condition (A5)).
Let `a, b, c` be three non-concurrent lines meeting at `pab, pbc, pca`, `Pa, Pb, Pc` segments
of `a, b, c` between these points, and `Δ` a fourth line through none of them; let
`ea, eb, ec` be edges of `a, b, c` at their meeting points with `Δ`. The triangle cycle
`Pa + Pb + Pc` bounds a union of faces iff `Δ` crosses an even number of its sides:
`Pa ea + Pb eb + Pc ec = 0`. The right-hand side involves only the skeleton and its lines, so
the canonical orientation of the triangle (which four of its eight cycles bound) is determined
by the skeleton, and does not depend on `Δ`. -/
theorem triangle_iff (hbf : BigonFree X.On) (hs : X.Straight) {a b c Δ : L}
    {pab pbc pca : X.M.Vtx} (hpab : X.On pab a ∧ X.On pab b) (hpbc : X.On pbc b ∧ X.On pbc c)
    (hpca : X.On pca c ∧ X.On pca a) (hab : a ≠ b) (hnc : ¬X.On pab c)
    (hΔ : ¬X.On pab Δ ∧ ¬X.On pbc Δ ∧ ¬X.On pca Δ) {Pa Pb Pc : X.M.Edge → ZMod 2}
    (sa : ∀ e, Pa e ≠ 0 → X.lineE e = a) (sb : ∀ e, Pb e ≠ 0 → X.lineE e = b)
    (sc : ∀ e, Pc e ≠ 0 → X.lineE e = c)
    (ba : X.incM *ᵥ Pa = Pi.single pab 1 + Pi.single pca 1)
    (bb : X.incM *ᵥ Pb = Pi.single pab 1 + Pi.single pbc 1)
    (bc : X.incM *ᵥ Pc = Pi.single pbc 1 + Pi.single pca 1) {ea eb ec : X.M.Edge}
    (ha : X.lineE ea = a ∧ ∃ w, X.Inc w ea ∧ X.On w Δ)
    (hb : X.lineE eb = b ∧ ∃ w, X.Inc w eb ∧ X.On w Δ)
    (hc : X.lineE ec = c ∧ ∃ w, X.Inc w ec ∧ X.On w Δ) :
    Pa + Pb + Pc ∈ X.B1 ↔ Pa ea + Pb eb + Pc ec = 0 := by
  refine ⟨tri_bound hbf hs hpab hpbc hpca hab hnc hΔ sa sb sc ba bb bc ha hb hc, fun h0 => ?_⟩
  have hz : Pa + Pb + Pc ∈ X.Z1 := by
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_add, ba, bb, bc]
    funext v
    simp only [Pi.add_apply, Pi.zero_apply]
    exact (by decide : ∀ p q r : ZMod 2, p + r + (p + q) + (q + r) = 0) _ _ _
  by_contra hn
  have hl := (flip hbf hs (show a ≠ Δ from fun h => hΔ.1 (h ▸ hpab.1)) hz).not.1 hn
  rw [not_not, add_right_comm, add_right_comm Pa] at hl
  have := tri_bound hbf hs hpab hpbc hpca hab hnc hΔ (Pa := Pa + X.lineChain a)
    (fun e he => by_contra fun h => he (by simp [lineChain, h, by_contra fun h' => h (sa e h')]))
    sb sc (by rw [Matrix.mulVec_add, ba, show X.incM *ᵥ X.lineChain a = 0 from
      lineChain_mem hbf hs a, add_zero]) bb bc ha hb hc hl
  rw [Pi.add_apply, show X.lineChain a ea = 1 by simp [lineChain, ha.1]] at this
  exact one_ne_zero (by linear_combination this - h0 : (1 : ZMod 2) = 0)

end Parity

/-! ### Lifting isomorphisms of skeletons (page 41) -/

section Lift

/-- Two edge-ends adjacent around a vertex lie on different lines. -/
theorem line_a1_ne (hs : X.Straight) (d : D) : X.line (X.M.a1 d) ≠ X.line d := by
  classical
  obtain ⟨e, he, hl⟩ := X.two d
  have h2 : 1 < X.nu (X.M.vtx d) := Finset.one_lt_card.2 ⟨_, Finset.mem_image.2 ⟨d, by simp, rfl⟩,
    _, Finset.mem_image.2 ⟨e, by simp [he], rfl⟩, Ne.symm hl⟩
  have := line_inj hs d zero_lt_one h2
  rw [pow_zero, pow_one, Equiv.Perm.one_apply, phi_apply, X.line_a2] at this
  exact Ne.symm this

variable (X) in
/-- `e1, e, e2` are three consecutive sides of a face: the corner `(e1, e)` at one end of `e`
continued along `e` to the corner `(e, e2)` on the same side. These paths are the generalised
rotation system (19)–(21) of page 41. -/
def Path3 (e1 e e2 : X.M.Edge) : Prop :=
  ∃ d, X.M.edge (X.M.a1 d) = e1 ∧ X.M.edge d = e ∧ X.M.edge (X.M.a1 (X.M.a0 d)) = e2

variable {D' L' : Type*} [Fintype D'] {X' : PseudolineMap D' L'}

variable (X X') in
/-- An isomorphism of the skeletons decomposed into lines: bijections of vertices, edges and
lines preserving incidence and the line of each edge (the arrangements of dimension `1` of
page 40). -/
structure SkelIso where
  fV : X.M.Vtx ≃ X'.M.Vtx
  fE : X.M.Edge ≃ X'.M.Edge
  fL : L ≃ L'
  inc : ∀ v e, X.Inc v e ↔ X'.Inc (fV v) (fE e)
  line : ∀ e, X'.lineE (fE e) = fL (X.lineE e)

/-- The inverse isomorphism of skeletons. -/
def SkelIso.symm (f : SkelIso X X') : SkelIso X' X where
  fV := f.fV.symm
  fE := f.fE.symm
  fL := f.fL.symm
  inc v e := by rw [f.inc]; simp
  line e := by rw [Equiv.eq_symm_apply, ← f.line]; simp

/-- A flag is determined by its vertex, its edge and the edge after it. -/
theorem dart_unique (hbf : BigonFree X.On) {y y' : D} (hv : X.M.vtx y' = X.M.vtx y)
    (he : X.M.edge y' = X.M.edge y) (h1 : X.M.edge (X.M.a1 y') = X.M.edge (X.M.a1 y)) :
    y' = y := by
  rcases (at_edge hbf).1 ⟨hv, he⟩ with h | rfl
  · exact h
  · exact (edge_a1_a2_ne hbf y h1).elim

omit [Fintype D'] in
theorem exists_dart (hbf : BigonFree X.On) (hs : X.Straight) (f : SkelIso X X')
    (hT : ∀ e1 e e2, X.Path3 e1 e e2 → X'.Path3 (f.fE e1) (f.fE e) (f.fE e2)) (d : D) :
    ∃ d', X'.M.vtx d' = f.fV (X.M.vtx d) ∧ X'.M.edge d' = f.fE (X.M.edge d) ∧
      X'.M.edge (X'.M.a1 d') = f.fE (X.M.edge (X.M.a1 d)) ∧
      X'.M.edge (X'.M.a1 (X'.M.a0 d')) = f.fE (X.M.edge (X.M.a1 (X.M.a0 d))) := by
  obtain ⟨d', h1, h2, h3⟩ := hT _ _ _ ⟨d, rfl, rfl, rfl⟩
  refine ⟨d', ?_, h2, h1, h3⟩
  have iv := (f.inc _ _).1 (⟨d, rfl, rfl⟩ : X.Inc (X.M.vtx d) (X.M.edge d))
  have iw := (f.inc _ _).1 (⟨_, rfl, edge_a0 d⟩ : X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge d))
  rw [← h2, inc_iff] at iv iw
  have hvw : f.fV (X.M.vtx d) ≠ f.fV (X.M.vtx (X.M.a0 d)) := fun h => noLoop hbf d (f.fV.injective h).symm
  by_contra hne
  have hw : X'.M.vtx d' = f.fV (X.M.vtx (X.M.a0 d)) := by
    rcases iv with h | h
    · exact (hne h.symm).elim
    · rcases iw with h' | h'
      · exact h'.symm
      · exact (hvw (h.trans h'.symm)).elim
  -- the edge after `d` would join both ends of `d`, on another line
  have : X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge (X.M.a1 d)) := by
    rw [f.inc, ← h1, ← hw]; exact ⟨_, vtx_a1 d', rfl⟩
  exact noLoop hbf d (meet_eq (line_a1_ne hs d) (lineE_edge (X := X) (X.M.a1 d) ▸ on_of_inc this)
    ⟨_, rfl, X.line_a0 d⟩ ⟨_, vtx_a1 d, rfl⟩ ⟨d, rfl, rfl⟩)

/-- **The general theorem on maps, page 41.** An isomorphism of decomposed skeletons that
carries the three-edge face paths to face paths is induced by a morphism of the arrangements
(commuting with `a0, a1, a2`, over the given bijections). -/
theorem lift (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight) (f : SkelIso X X')
    (hT : ∀ e1 e e2, X.Path3 e1 e e2 → X'.Path3 (f.fE e1) (f.fE e) (f.fE e2)) :
    ∃ g : D → D', (∀ d, g (X.M.a0 d) = X'.M.a0 (g d)) ∧ (∀ d, g (X.M.a1 d) = X'.M.a1 (g d)) ∧
      (∀ d, g (X.M.a2 d) = X'.M.a2 (g d)) ∧ (∀ d, X'.M.vtx (g d) = f.fV (X.M.vtx d)) ∧
      (∀ d, X'.M.edge (g d) = f.fE (X.M.edge d)) ∧ ∀ d, X'.line (g d) = f.fL (X.line d) := by
  choose g hv he h1 h3 using exists_dart hbf hs f hT
  have hv' : ∀ d, X'.M.vtx (X'.M.a0 (g d)) = f.fV (X.M.vtx (X.M.a0 d)) := fun d => by
    have := (f.inc _ _).1 (⟨_, rfl, edge_a0 d⟩ : X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge d))
    rw [← he, inc_iff] at this
    exact this.resolve_left (fun h => noLoop hbf d (f.fV.injective (h.trans (hv d))))
      |>.symm
  refine ⟨g, fun d => ?_, fun d => ?_, fun d => ?_, hv, he, fun d => ?_⟩
  · exact dart_unique hbf' (by rw [hv, hv']) (by simp [he]) (by rw [h1, h3])
  · exact dart_unique hbf' (by simp [hv]) (by rw [he, h1]) (by rw [h1, X.M.a1_a1, X'.M.a1_a1, he])
  · rcases (at_edge hbf').1 (⟨by simp [hv], by simp [he]⟩ :
      X'.M.vtx (g (X.M.a2 d)) = X'.M.vtx (g d) ∧ X'.M.edge (g (X.M.a2 d)) = X'.M.edge (g d))
      with h | h
    · exact (edge_a1_a2_ne hbf d (f.fE.injective (by rw [← h1, ← h1, h]))).elim
    · exact h
  · rw [← lineE_edge, he, f.line]; rfl

/-- **Fullness reduces to face paths.** An isomorphism of decomposed skeletons of two bigon-free
arrangements comes from an isomorphism of the arrangements (a bijection of flags commuting with
`a0, a1, a2`) iff it preserves the three-edge face paths in both directions; the isomorphism is
then unique (`faithful`). -/
theorem lift_iff (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight)
    (hs' : X'.Straight) (f : SkelIso X X') :
    (∃ g : D ≃ D', (∀ d, g (X.M.a0 d) = X'.M.a0 (g d)) ∧ (∀ d, g (X.M.a1 d) = X'.M.a1 (g d)) ∧
      (∀ d, g (X.M.a2 d) = X'.M.a2 (g d)) ∧ (∀ d, X'.M.vtx (g d) = f.fV (X.M.vtx d)) ∧
      ∀ d, X'.M.edge (g d) = f.fE (X.M.edge d)) ↔
    ∀ e1 e e2, X.Path3 e1 e e2 ↔ X'.Path3 (f.fE e1) (f.fE e) (f.fE e2) := by
  constructor
  · rintro ⟨g, g0, g1, -, -, ge⟩ e1 e e2
    constructor
    · rintro ⟨d, rfl, rfl, rfl⟩
      exact ⟨g d, by rw [← g1, ge], ge d, by rw [← g0, ← g1, ge]⟩
    · rintro ⟨d', h1, h2, h3⟩
      refine ⟨g.symm d', f.fE.injective ?_, f.fE.injective ?_, f.fE.injective ?_⟩
      · rw [← ge, g1, g.apply_symm_apply, h1]
      · rw [← ge, g.apply_symm_apply, h2]
      · rw [← ge, g1, g0, g.apply_symm_apply, h3]
  · intro hT
    obtain ⟨g, g0, g1, g2, gv, ge, -⟩ := lift hbf hbf' hs f fun _ _ _ => (hT _ _ _).1
    obtain ⟨g', -, g1', -, gv', ge', -⟩ := lift hbf' hbf hs' f.symm fun e1 e e2 h =>
      (hT _ _ _).2 (by simpa [SkelIso.symm] using h)
    have l : g' ∘ g = id := faithful hbf (fun d => by simp [g1, g1']) (fun _ => rfl)
      (fun d => by simp [gv, gv', SkelIso.symm]) (fun d => by simp [ge, ge', SkelIso.symm])
    have r : g ∘ g' = id := faithful hbf' (fun d => by simp [g1, g1']) (fun _ => rfl)
      (fun d => by simp [gv, gv', SkelIso.symm]) (fun d => by simp [ge, ge', SkelIso.symm])
    exact ⟨⟨g, g', congrFun l, congrFun r⟩, g0, g1, g2, gv, ge⟩

end Lift

end PseudolineMap

end Grothendieck.Folder80Maps3
