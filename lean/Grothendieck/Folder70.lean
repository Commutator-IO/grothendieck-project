import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Prime

/-!
# Folder 70, pages 74–78 and 89–102: the icosahedron over `ℤ[α]` and modulo 5

The modernised reading `transcripts/70/70.modern.tex` (§ VII, « L'icosaèdre en
coordonnées universelles », pages 73 to 111) writes the regular icosahedron over
`ℤ[α] = ℤ[x]/(x² + x − 1)` by three reflections in the vertex frame
`(s₀, s₁ − s₀, s₂ − s₀, s₃ − s₀)`, with `α' = −1 − α`:

> `σ₀(x, y, z) = (1 − (x + y + z), y, z)`, `σ₁(x, y, z) = (y + α'z, x − α'z, z)`,
> `σ₂(x, y, z) = (x, z, y)`; the twelve vertices `s₀, s₁, s₂, s₃, s'₃ = (α', −α', 1)`,
> `s''₃ = (0, −α', 1)` and their images by `ι(x, y, z) = (α' − x, 1 − α' − y, 1 − α' − z)`
> (pages 74–75, 89–92); the invariant function
> `q = x² + y² + z² − αyz + zx + xy − (x + y + z)` (page 95, (19)) and its quadratic part
> `q₀` (pages 101–102).
>
> **Page 78.** « 6 directions de sommets, 15 d'arêtes, 10 de plans de faces :
> `31 = 5² + 5 + 1` » ; in characteristic 5 the vertex directions are the conic
> `q₀ = 0`, and `125 = 1 + 24 + 60 + 40`, the 24 nonzero isotropic vectors being the
> vertices of « deux icosaèdres ».

This is finding `70-icosahedron-char5-conic` of `src/content/findings.ts`, and the
characteristic-5 case of `70-icosahedron-integral-faithful`. Proving them says only
that the claims hold as stated; whether they stand in the literature is a separate
question.

What is formalised.

* Over any commutative ring `R` with `α² + α − 1 = 0`: `q_vert` (the twelve vertices lie
  on `q = 0`), `sigma0_vert`, `sigma1_vert`, `sigma2_vert` (the three generators
  permute the twelve vertices, by the explicit permutations `perm0`, `perm1`, `perm2`),
  `q0_edge` (the thirty edges, listed in `edge`, have `q₀ = 1`), and `isUnit_z` (the
  nine vertices off the face `(s₀, s₁, s₂)` have a unit `z`-coordinate, page 94), and
  `iota_char_two` (in characteristic 2, `ι` is the translation by `(α', α, α)`).
* Over `𝔽₅`: `alpha_eq_two` (`α = 2` is the only root), `two_centre` (the centre
  `o = (1, 2, 2)`, `2o = (α', 1 − α', 1 − α')`), `centre_fixed`, `vert_isotropic`
  (`q₀(s − o) = 0` at the twelve vertices, equivalently `q(o) = 0`), `isotropic_iff`,
  `isotropic_card` and `twoIcos_injective` (the nonzero isotropic vectors are the
  twelve centred vertices and their doubles, twenty-four in all), `conic_iff` (a point
  of `ℙ²(𝔽₅)` is on the conic `q₀ = 0` iff it is one of the six vertex directions),
  `point_bijective` and `card_proj` (the 6 vertex, 15 edge and 10 face directions are
  the 31 points of `ℙ²(𝔽₅)`), `edgeDir_cover`, `faceDir_cover`, `vertDir_cover` (every
  edge, face, vertex gives one of the chosen directions), `face_orth` (the face
  direction is the barycentre, orthogonal to the face plane for the polar form),
  `edge_tangents` and `face_tangents` (an edge point lies on exactly two tangents of the
  conic, a face point on none), `card_square`, `card_nonsquare` (`60` and `40`).
* Faithfulness in every characteristic (finding `70-icosahedron-integral-faithful`, the
  incidence part), over any nonzero commutative ring with `α² + α − 1 = 0`:
  `vert_injective_any` (twelve distinct vertices), `not_collinear_any` (no three on a
  line), `not_in_face_plane_any` (no vertex in the plane of a face not containing it).
  The proof is the page's « par homogénéité » made explicit: `sigmaOf_vert` and the
  kernel-checked word tables `pairWord`, `faceWord` reduce every case to the lines
  `s₀s₁`, `s₀s''₃`, `s₀ι(s₀)` and the face plane `z = 0`, where a `2 × 2` minor is a unit
  of `ℤ[α]` (`base_line_1`, `base_line_5`, `base_line_6`) and `isUnit_z` applies.
-/

namespace Grothendieck.Folder70

/-! ## The icosahedron over a ring with `α² + α − 1 = 0` -/

section General

variable {R : Type*} [CommRing R] (α : R)

/-- `σ₀` of page 74. -/
def sigma0 (p : R × R × R) : R × R × R := (1 - (p.1 + p.2.1 + p.2.2), p.2.1, p.2.2)

/-- `σ₁` of page 74, with `α' = −1 − α`. -/
def sigma1 (p : R × R × R) : R × R × R :=
  (p.2.1 + (-1 - α) * p.2.2, p.1 - (-1 - α) * p.2.2, p.2.2)

/-- `σ₂` of page 74. -/
def sigma2 (p : R × R × R) : R × R × R := (p.1, p.2.2, p.2.1)

/-- The antipodism `ι` of page 91, (17). -/
def iota (p : R × R × R) : R × R × R :=
  ((-1 - α) - p.1, 1 - (-1 - α) - p.2.1, 1 - (-1 - α) - p.2.2)

/-- The twelve vertices of page 75 in the order `s₀, s₁, s₂, s₃, s'₃, s''₃` and their
antipodes `ι s₀, …, ι s''₃`. -/
def vert : Fin 12 → R × R × R :=
  ![(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (-1 - α, -(-1 - α), 1), (0, -(-1 - α), 1),
    iota α (0, 0, 0), iota α (1, 0, 0), iota α (0, 1, 0), iota α (0, 0, 1),
    iota α (-1 - α, -(-1 - α), 1), iota α (0, -(-1 - α), 1)]

/-- The invariant function `q` of page 95, (19). -/
def q (p : R × R × R) : R :=
  p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - α * p.2.1 * p.2.2 + p.2.2 * p.1 + p.1 * p.2.1
    - (p.1 + p.2.1 + p.2.2)

/-- Its quadratic part `q₀` (pages 75 and 101). -/
def q0 (p : R × R × R) : R :=
  p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 - α * p.2.1 * p.2.2 + p.2.2 * p.1 + p.1 * p.2.1

/-- The polar form of `q₀`, of matrix `[[2, 1, 1], [1, 2, −α], [1, −α, 2]]`. -/
def polar (u v : R × R × R) : R :=
  2 * u.1 * v.1 + 2 * u.2.1 * v.2.1 + 2 * u.2.2 * v.2.2 - α * (u.2.1 * v.2.2 + u.2.2 * v.2.1)
    + (u.2.2 * v.1 + u.1 * v.2.2) + (u.1 * v.2.1 + u.2.1 * v.1)

/-- The permutations of the vertices induced by `σ₀`, `σ₁`, `σ₂`. -/
def perm0 : Fin 12 → Fin 12 := ![1, 0, 2, 3, 5, 4, 7, 6, 8, 9, 11, 10]
/-- See `perm0`. -/
def perm1 : Fin 12 → Fin 12 := ![0, 2, 1, 4, 3, 5, 6, 8, 7, 10, 9, 11]
/-- See `perm0`. -/
def perm2 : Fin 12 → Fin 12 := ![0, 1, 3, 2, 11, 10, 6, 7, 9, 8, 5, 4]

/-- The thirty edges, as pairs of vertex indices (the pairs at `q₀`-distance `1`
over `ℚ(√5)`). -/
def edge : Fin 30 → Fin 12 × Fin 12 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 11), (1, 2), (1, 3), (1, 5), (1, 10), (2, 4),
    (2, 5), (2, 9), (3, 8), (3, 10), (3, 11), (4, 7), (4, 9), (4, 11), (5, 6), (5, 9),
    (5, 10), (6, 7), (6, 8), (6, 9), (6, 10), (7, 8), (7, 9), (7, 11), (8, 10), (8, 11)]

/-- The twenty faces, the triangles of edges. -/
def face : Fin 20 → Fin 12 × Fin 12 × Fin 12 :=
  ![(0, 1, 2), (0, 1, 3), (0, 2, 4), (0, 3, 11), (0, 4, 11), (1, 2, 5), (1, 3, 10),
    (1, 5, 10), (2, 4, 9), (2, 5, 9), (3, 8, 10), (3, 8, 11), (4, 7, 9), (4, 7, 11),
    (5, 6, 9), (5, 6, 10), (6, 7, 8), (6, 7, 9), (6, 8, 10), (7, 8, 11)]

variable {α}

/-- The twelve vertices lie on the quadric `q = 0` (page 101). -/
theorem q_vert (h : α ^ 2 + α - 1 = 0) (i : Fin 12) : q α (vert α i) = 0 := by
  fin_cases i <;> simp [q, vert, iota] <;>
    first | ring1 | linear_combination (-2 - α) * h | linear_combination (-1 - α) * h

theorem sigma0_vert (i : Fin 12) : sigma0 (vert α i) = vert α (perm0 i) := by
  fin_cases i <;> refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp [sigma0, vert, iota, perm0] <;> ring1

theorem sigma1_vert (h : α ^ 2 + α - 1 = 0) (i : Fin 12) :
    sigma1 α (vert α i) = vert α (perm1 i) := by
  fin_cases i <;> refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp [sigma1, vert, iota, perm1] <;>
    first | ring1 | linear_combination (-1 : R) * h | linear_combination h

theorem sigma2_vert (i : Fin 12) : sigma2 (vert α i) = vert α (perm2 i) := by
  fin_cases i <;> refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp [sigma2, vert, iota, perm2] <;> ring1

/-- The thirty edges have `q₀ = 1` (the normalisation of page 75). -/
theorem q0_edge (h : α ^ 2 + α - 1 = 0) (e : Fin 30) :
    q0 α (vert α (edge e).2 - vert α (edge e).1) = 1 := by
  fin_cases e <;> simp [q0, vert, iota, edge] <;>
    first | ring1 | linear_combination (-α) * h | linear_combination (1 + α) * h

/-- Page 94: the nine vertices off the face `(s₀, s₁, s₂)` have a unit `z`-coordinate,
so none lies in its plane `z = 0`, over any base. -/
theorem isUnit_z (h : α ^ 2 + α - 1 = 0) (i : Fin 12) (hi : 3 ≤ i.val) :
    IsUnit (vert α i).2.2 := by
  have u1 : IsUnit (2 + α) := ⟨⟨2 + α, 1 - α, by linear_combination -h, by
    linear_combination -h⟩, rfl⟩
  have u2 : IsUnit (1 + α) := ⟨⟨1 + α, α, by linear_combination h, by
    linear_combination h⟩, rfl⟩
  fin_cases i <;> simp at hi <;> simp [vert, iota] <;> ring_nf <;>
    first | exact u1 | exact u2

/-- Page 91, (17): in characteristic `2` the antipodism is the translation by
`(α', α, α)` (the page reads « `(α', 1, 1)` »). No hypothesis on `α` is needed. -/
theorem iota_char_two (h2 : (2 : R) = 0) (p : R × R × R) :
    iota α p = p + (-1 - α, α, α) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [iota, Prod.fst_add, Prod.snd_add]
  · linear_combination (-p.1) * h2
  · linear_combination (1 - p.2.1) * h2
  · linear_combination (1 - p.2.2) * h2

end General

/-! ## Faithfulness in every characteristic (finding `70-icosahedron-integral-faithful`)

The page's « par homogénéité » (pages 93–94), made explicit: the group generated by the
`σᵢ` permutes the vertices by `perm0`, `perm1`, `perm2`; it carries every pair of distinct
vertices to `(s₀, s₁)`, `(s₀, s''₃)` or `(s₀, ι s₀)` (`pairWord`), and every face, in
order, to `(s₀, s₁, s₂)` (`faceWord`), which the kernel checks on `Fin 12`. The base
cases are a unit `2 × 2` minor of `ℤ[α]`, written as a certificate. -/

section Faithful

variable {R : Type*} [CommRing R] {α : R}

/-- The three vertex permutations. -/
def permOf : Fin 3 → Fin 12 → Fin 12 := ![perm0, perm1, perm2]

/-- The permutation of a word `[k₁, …, kₙ]`: `π_{k₁} ∘ ⋯ ∘ π_{kₙ}`. -/
def app (w : List (Fin 3)) (i : Fin 12) : Fin 12 := w.foldr (fun k i => permOf k i) i

/-- The three generators. -/
def sigmaOf (α : R) : Fin 3 → R × R × R → R × R × R := ![sigma0, sigma1 α, sigma2]

theorem sigmaOf_vert (h : α ^ 2 + α - 1 = 0) (k : Fin 3) (i : Fin 12) :
    sigmaOf α k (vert α i) = vert α (permOf k i) := by
  fin_cases k
  · exact sigma0_vert i
  · exact sigma1_vert h i
  · exact sigma2_vert i

/-- `p` is in the affine plane spanned by `r, u, w` (with these parameters). -/
def InPlane (p r u w : R × R × R) : Prop := ∃ s t : R, p - r = s • (u - r) + t • (w - r)

/-- `p` is on the line through `r` and `u`. -/
def OnLine (p r u : R × R × R) : Prop := ∃ a : R, p - r = a • (u - r)

theorem sigmaOf_plane (k : Fin 3) {p r u w : R × R × R} (H : InPlane p r u w) :
    InPlane (sigmaOf α k p) (sigmaOf α k r) (sigmaOf α k u) (sigmaOf α k w) := by
  obtain ⟨s, t, hst⟩ := H
  simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hst
  obtain ⟨h1, h2, h3⟩ := hst
  refine ⟨s, t, ?_⟩
  fin_cases k
  · show sigma0 p - sigma0 r = s • (sigma0 u - sigma0 r) + t • (sigma0 w - sigma0 r)
    simp only [sigma0, Prod.ext_iff, Prod.fst_sub,
      Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exact ⟨by linear_combination -h1 - h2 - h3, by linear_combination h2,
      by linear_combination h3⟩
  · show sigma1 α p - sigma1 α r = s • (sigma1 α u - sigma1 α r) + t • (sigma1 α w - sigma1 α r)
    simp only [sigma1, Prod.ext_iff, Prod.fst_sub,
      Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exact ⟨by linear_combination h2 + (-1 - α) * h3, by linear_combination h1 - (-1 - α) * h3,
      by linear_combination h3⟩
  · show sigma2 p - sigma2 r = s • (sigma2 u - sigma2 r) + t • (sigma2 w - sigma2 r)
    simp only [sigma2, Prod.ext_iff, Prod.fst_sub,
      Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    exact ⟨by linear_combination h1, by linear_combination h3,
      by linear_combination h2⟩

theorem sigmaOf_line (k : Fin 3) {p r u : R × R × R} (H : OnLine p r u) :
    OnLine (sigmaOf α k p) (sigmaOf α k r) (sigmaOf α k u) := by
  obtain ⟨a, ha⟩ := H
  obtain ⟨s, t, hst⟩ := sigmaOf_plane (α := α) (p := p) (r := r) (u := u) (w := r) k
    ⟨a, 0, by simp [ha]⟩
  exact ⟨s, by simpa using hst⟩

theorem plane_of_word (h : α ^ 2 + α - 1 = 0) (w : List (Fin 3)) {m a b c : Fin 12}
    (H : InPlane (vert α m) (vert α a) (vert α b) (vert α c)) :
    InPlane (vert α (app w m)) (vert α (app w a)) (vert α (app w b)) (vert α (app w c)) := by
  induction w with
  | nil => exact H
  | cons k w ih =>
    have := sigmaOf_plane (α := α) k ih
    simp only [sigmaOf_vert h] at this
    exact this

theorem line_of_word (h : α ^ 2 + α - 1 = 0) (w : List (Fin 3)) {i j k : Fin 12}
    (H : OnLine (vert α k) (vert α i) (vert α j)) :
    OnLine (vert α (app w k)) (vert α (app w i)) (vert α (app w j)) := by
  induction w with
  | nil => exact H
  | cons c w ih =>
    have := sigmaOf_line (α := α) c ih
    simp only [sigmaOf_vert h] at this
    exact this

theorem eq_of_word (h : α ^ 2 + α - 1 = 0) (w : List (Fin 3)) {i j : Fin 12}
    (H : vert α i = vert α j) : vert α (app w i) = vert α (app w j) := by
  induction w with
  | nil => exact H
  | cons c w ih =>
    have := congrArg (sigmaOf α c) ih
    simp only [sigmaOf_vert h] at this
    exact this

theorem app_injective (w : List (Fin 3)) : Function.Injective (app w) := by
  have hp : ∀ k : Fin 3, Function.Injective (permOf k) := by
    unfold Function.Injective; decide +kernel
  induction w with
  | nil => exact fun _ _ h => h
  | cons c w ih => exact fun x y hxy => ih (hp c hxy)

/-- For `i ≠ j`, a word sending `i` to `s₀` and `j` to `s₁`, `s''₃` or `ι s₀`. -/
def pairWord : Fin 12 → Fin 12 → List (Fin 3) :=
  ![![[], [], [1], [1, 2], [1, 2, 1], [], [], [2, 1, 2, 1], [2, 1, 2], [2, 1], [2], [1, 2, 1, 2]],
    ![[0], [], [1, 0], [1, 2, 0], [0], [1, 2, 1, 0], [2, 1, 2, 1, 0], [0], [2, 1, 2, 0], [2, 1, 0], [1, 2, 1, 2, 0], [2, 0]],
    ![[0, 1], [0, 1, 0], [], [0, 1], [1, 2, 0, 1], [1, 2, 0, 1, 0], [2, 1, 2, 0, 1, 0], [2, 1, 2, 0, 1], [0, 1], [1, 2, 1, 2, 0, 1], [2, 0, 1, 0], [2, 0, 1]],
    ![[0, 1, 2], [0, 1, 2, 0], [0, 1, 2], [], [2, 0, 1, 2], [2, 0, 1, 2, 0], [2, 1, 2, 0, 1, 2, 0], [2, 1, 2, 0, 1, 2], [1, 2, 1, 2, 0, 1, 2], [0, 1, 2], [1, 2, 0, 1, 2, 0], [1, 2, 0, 1, 2]],
    ![[0, 1, 2, 1], [0, 1, 2, 1], [0, 1, 2, 0, 1], [2, 0, 1, 2, 1], [], [2, 0, 1, 2, 0, 1], [2, 1, 2, 0, 1, 2, 0, 1], [1, 2, 1, 2, 0, 1, 2, 1], [2, 1, 2, 0, 1, 2, 1], [1, 2, 0, 1, 2, 0, 1], [0, 1, 2, 1], [1, 2, 0, 1, 2, 1]],
    ![[0, 1, 2, 1, 0], [0, 1, 2, 1, 0], [0, 1, 2, 0, 1, 0], [2, 0, 1, 2, 1, 0], [2, 0, 1, 2, 0, 1, 0], [], [1, 2, 1, 2, 0, 1, 2, 1, 0], [2, 1, 2, 0, 1, 2, 0, 1, 0], [2, 1, 2, 0, 1, 2, 1, 0], [1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 1, 0], [0, 1, 2, 1, 0]],
    ![[0, 1, 2, 1, 2, 0, 1, 2, 1, 0], [0, 1, 2, 1, 2, 0, 1, 2, 1, 0], [0, 1, 2, 1, 2, 0, 1, 2, 0, 1, 0], [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0], [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [0, 1, 2, 1, 2, 0, 1, 2, 1, 0], [], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0], [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0], [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0]],
    ![[0, 1, 2, 1, 2, 0, 1, 2, 1], [0, 1, 2, 1, 2, 0, 1, 2, 1], [0, 1, 2, 1, 2, 0, 1, 2, 0, 1], [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1], [0, 1, 2, 1, 2, 0, 1, 2, 1], [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1], [], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1], [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1], [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1], [0, 1, 2, 0, 1, 2, 0, 1, 2, 1]],
    ![[0, 1, 2, 1, 2, 0, 1, 2], [0, 1, 2, 1, 2, 0, 1, 2, 0], [0, 1, 2, 1, 2, 0, 1, 2], [0, 1, 2, 1, 2, 0, 1, 2], [2, 0, 1, 2, 0, 1, 2, 0, 1, 2], [2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2], [], [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2, 0, 1, 2, 0], [0, 1, 2, 0, 1, 2, 0, 1, 2]],
    ![[0, 1, 2, 1, 2, 0, 1], [0, 1, 2, 1, 2, 0, 1, 0], [0, 1, 2, 1, 2, 0, 1], [0, 1, 2, 1, 2, 0, 1], [0, 1, 2, 0, 1, 2, 0, 1], [0, 1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1], [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1], [], [2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [2, 0, 1, 2, 0, 1, 2, 0, 1]],
    ![[0, 1, 2, 1, 2, 0], [0, 1, 2, 1, 2, 0], [0, 1, 2, 1, 2, 1, 0], [0, 1, 2, 0, 1, 2, 0], [0, 1, 2, 1, 2, 0], [0, 1, 2, 0, 1, 2, 1, 0], [1, 2, 0, 1, 2, 0, 1, 2, 1, 0], [2, 1, 2, 0, 1, 2, 0, 1, 2, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0], [2, 0, 1, 2, 0, 1, 2, 1, 0], [], [2, 0, 1, 2, 0, 1, 2, 0]],
    ![[0, 1, 2, 1, 2], [0, 1, 2, 1, 2], [0, 1, 2, 1, 2, 1], [0, 1, 2, 0, 1, 2], [0, 1, 2, 0, 1, 2, 1], [0, 1, 2, 1, 2], [2, 1, 2, 0, 1, 2, 0, 1, 2], [1, 2, 0, 1, 2, 0, 1, 2, 1], [1, 2, 0, 1, 2, 0, 1, 2], [2, 0, 1, 2, 0, 1, 2, 1], [2, 0, 1, 2, 0, 1, 2], []]]
/-- A word sending the face `f`, in order, to `(s₀, s₁, s₂)`. -/
def faceWord : Fin 20 → List (Fin 3) :=
  ![[], [2], [2, 1], [2, 1, 2], [2, 1, 2, 1], [2, 1, 0], [2, 1, 2, 0], [2, 1, 2, 1, 0], [2, 1, 2, 0, 1], [2, 1, 2, 0, 1, 0], [1, 2, 1, 2, 0, 1, 2, 0], [1, 2, 1, 2, 0, 1, 2], [1, 2, 1, 2, 0, 1, 2, 0, 1], [1, 2, 1, 2, 0, 1, 2, 1], [1, 2, 1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 1, 2, 0, 1, 2, 1, 0], [2, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1, 0], [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 1]]

theorem pairWord_spec : ∀ i j : Fin 12, i ≠ j → app (pairWord i j) i = 0 ∧
    (app (pairWord i j) j = 1 ∨ app (pairWord i j) j = 5 ∨ app (pairWord i j) j = 6) := by
  decide +kernel

theorem faceWord_spec : ∀ f : Fin 20, app (faceWord f) (face f).1 = 0 ∧
    app (faceWord f) (face f).2.1 = 1 ∧ app (faceWord f) (face f).2.2 = 2 := by
  decide +kernel

variable [Nontrivial R]

private theorem bl_1_2 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 2 ≠ a • vert α 1 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1) * (0 * h1 - (1) * h2) + 0 * h)

private theorem bl_1_3 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 3 ≠ a • vert α 1 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1) * (0 * h1 - (1) * h3) + 0 * h)

private theorem bl_1_4 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 4 ≠ a • vert α 1 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 * α) * (0 * h1 - (1) * h2) + (-1) * h)

private theorem bl_1_5 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 5 ≠ a • vert α 1 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 * α) * (0 * h1 - (1) * h2) + (-1) * h)

private theorem bl_1_6 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 6 ≠ a • vert α 1 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 + α) * (0 * h1 - (1) * h2) + (1) * h)

private theorem bl_1_7 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 7 ≠ a • vert α 1 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 + α) * (0 * h1 - (1) * h2) + (1) * h)

private theorem bl_1_8 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 8 ≠ a • vert α 1 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 * α) * (0 * h1 - (1) * h2) + (-1) * h)

private theorem bl_1_9 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 9 ≠ a • vert α 1 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 + α) * (0 * h1 - (1) * h2) + (1) * h)

private theorem bl_1_10 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 10 ≠ a • vert α 1 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1) * (0 * h1 - (1) * h2) + 0 * h)

private theorem bl_1_11 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 11 ≠ a • vert α 1 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1) * (0 * h1 - (1) * h2) + 0 * h)

theorem base_line_1 (h : α ^ 2 + α - 1 = 0) (k : Fin 12) (hk0 : k ≠ 0) (hkj : k ≠ 1)
    (a : R) : vert α k ≠ a • vert α 1 := by
  fin_cases k
  · exact absurd rfl hk0
  · exact absurd rfl hkj
  · exact bl_1_2 h a
  · exact bl_1_3 h a
  · exact bl_1_4 h a
  · exact bl_1_5 h a
  · exact bl_1_6 h a
  · exact bl_1_7 h a
  · exact bl_1_8 h a
  · exact bl_1_9 h a
  · exact bl_1_10 h a
  · exact bl_1_11 h a

private theorem bl_5_1 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 1 ≠ a • vert α 5 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (α) * ((1 + α) * h1 - 0 * h2) + (-1) * h)

private theorem bl_5_2 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 2 ≠ a • vert α 5 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (1) * ((1) * h2 - (1 + α) * h3) + 0 * h)

private theorem bl_5_3 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 3 ≠ a • vert α 5 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 * α) * ((1) * h2 - (1 + α) * h3) + (-1) * h)

private theorem bl_5_4 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 4 ≠ a • vert α 5 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 + α) * ((1 + α) * h1 - 0 * h2) + (α) * h)

private theorem bl_5_6 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 6 ≠ a • vert α 5 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 + α) * ((1 + α) * h1 - 0 * h2) + (α) * h)

private theorem bl_5_7 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 7 ≠ a • vert α 5 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (1 + -2 * α) * ((1 + α) * h1 - 0 * h2) + (-3 + -2 * α) * h)

private theorem bl_5_8 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 8 ≠ a • vert α 5 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 + α) * ((1 + α) * h1 - 0 * h2) + (α) * h)

private theorem bl_5_9 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 9 ≠ a • vert α 5 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 + α) * ((1 + α) * h1 - 0 * h2) + (α) * h)

private theorem bl_5_10 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 10 ≠ a • vert α 5 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 * α) * ((1) * h2 - (1 + α) * h3) + (-1 + -1 * α) * h)

private theorem bl_5_11 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 11 ≠ a • vert α 5 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 + α) * ((1 + α) * h1 - 0 * h2) + (α) * h)

theorem base_line_5 (h : α ^ 2 + α - 1 = 0) (k : Fin 12) (hk0 : k ≠ 0) (hkj : k ≠ 5)
    (a : R) : vert α k ≠ a • vert α 5 := by
  fin_cases k
  · exact absurd rfl hk0
  · exact bl_5_1 h a
  · exact bl_5_2 h a
  · exact bl_5_3 h a
  · exact bl_5_4 h a
  · exact absurd rfl hkj
  · exact bl_5_6 h a
  · exact bl_5_7 h a
  · exact bl_5_8 h a
  · exact bl_5_9 h a
  · exact bl_5_10 h a
  · exact bl_5_11 h a

private theorem bl_6_1 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 1 ≠ a • vert α 6 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (1 + -1 * α) * ((2 + α) * h1 - (-1 + -1 * α) * h2) + (1) * h)

private theorem bl_6_2 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 2 ≠ a • vert α 6 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (α) * ((2 + α) * h1 - (-1 + -1 * α) * h2) + (-1) * h)

private theorem bl_6_3 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 3 ≠ a • vert α 6 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (α) * ((2 + α) * h1 - (-1 + -1 * α) * h3) + (-1) * h)

private theorem bl_6_4 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 4 ≠ a • vert α 6 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 * α) * ((2 + α) * h1 - (-1 + -1 * α) * h2) + (-1) * h)

private theorem bl_6_5 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 5 ≠ a • vert α 6 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (1 + -1 * α) * ((2 + α) * h1 - (-1 + -1 * α) * h2) + (α) * h)

private theorem bl_6_7 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 7 ≠ a • vert α 6 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 + α) * ((2 + α) * h1 - (-1 + -1 * α) * h2) + (1) * h)

private theorem bl_6_8 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 8 ≠ a • vert α 6 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 * α) * ((2 + α) * h1 - (-1 + -1 * α) * h2) + (-1) * h)

private theorem bl_6_9 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 9 ≠ a • vert α 6 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 * α) * ((2 + α) * h1 - (-1 + -1 * α) * h3) + (-1) * h)

private theorem bl_6_10 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 10 ≠ a • vert α 6 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (α) * ((2 + α) * h1 - (-1 + -1 * α) * h2) + (-1) * h)

private theorem bl_6_11 (h : α ^ 2 + α - 1 = 0) (a : R) : vert α 11 ≠ a • vert α 6 := by
  intro H
  have h1 := congrArg Prod.fst H
  have h2 := congrArg (fun p => p.2.1) H
  have h3 := congrArg (fun p => p.2.2) H
  simp only [vert, iota, Matrix.cons_val, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 h3
  exact one_ne_zero (show (1 : R) = 0 by linear_combination (-1 + α) * ((2 + α) * h1 - (-1 + -1 * α) * h2) + (α) * h)

theorem base_line_6 (h : α ^ 2 + α - 1 = 0) (k : Fin 12) (hk0 : k ≠ 0) (hkj : k ≠ 6)
    (a : R) : vert α k ≠ a • vert α 6 := by
  fin_cases k
  · exact absurd rfl hk0
  · exact bl_6_1 h a
  · exact bl_6_2 h a
  · exact bl_6_3 h a
  · exact bl_6_4 h a
  · exact bl_6_5 h a
  · exact absurd rfl hkj
  · exact bl_6_7 h a
  · exact bl_6_8 h a
  · exact bl_6_9 h a
  · exact bl_6_10 h a
  · exact bl_6_11 h a

omit [Nontrivial R] in
theorem vert_zero : vert α 0 = 0 := by simp [vert]

theorem base_line (h : α ^ 2 + α - 1 = 0) {j k : Fin 12} (hj : j = 1 ∨ j = 5 ∨ j = 6)
    (hk0 : k ≠ 0) (hkj : k ≠ j) (a : R) : vert α k ≠ a • vert α j := by
  rcases hj with rfl | rfl | rfl
  · exact base_line_1 h k hk0 hkj a
  · exact base_line_5 h k hk0 hkj a
  · exact base_line_6 h k hk0 hkj a

/-- The twelve vertices are distinct, over any nonzero ring with `α² + α = 1`. -/
theorem vert_injective_any (h : α ^ 2 + α - 1 = 0) : Function.Injective (vert α) := by
  intro i j hij
  by_contra hne
  obtain ⟨h0, hj⟩ := pairWord_spec i j hne
  have e := eq_of_word h (pairWord i j) hij
  rw [h0, vert_zero] at e
  rcases hj with hj | hj | hj <;> rw [hj] at e
  · simp [vert, Prod.ext_iff] at e
  · simp [vert, Prod.ext_iff] at e
  · have e3 := congrArg (fun p => p.2.2) e
    simp only [vert, iota, Matrix.cons_val, Prod.snd_zero] at e3
    exact one_ne_zero (show (1 : R) = 0 by linear_combination (α - 1) * e3 + h)

/-- Page 93, a)–c) « par homogénéité »: no three distinct vertices are collinear, over
any nonzero ring with `α² + α = 1` (over a field, `OnLine` is collinearity). -/
theorem not_collinear_any (h : α ^ 2 + α - 1 = 0) {i j k : Fin 12} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : ¬ OnLine (vert α k) (vert α i) (vert α j) := by
  intro H
  obtain ⟨h0, hj⟩ := pairWord_spec i j hij
  obtain ⟨a, ha⟩ := line_of_word h (pairWord i j) H
  rw [h0, vert_zero, sub_zero, sub_zero] at ha
  refine base_line h hj ?_ ?_ a ha
  · rw [← h0]; exact fun h' => hik (app_injective _ h').symm
  · exact fun h' => hjk (app_injective _ h').symm

/-- Page 94 « par homogénéité »: no vertex is in the plane of a face not containing it,
over any nonzero ring with `α² + α = 1`. -/
theorem not_in_face_plane_any (h : α ^ 2 + α - 1 = 0) (f : Fin 20) {m : Fin 12}
    (h1 : m ≠ (face f).1) (h2 : m ≠ (face f).2.1) (h3 : m ≠ (face f).2.2) :
    ¬ InPlane (vert α m) (vert α (face f).1) (vert α (face f).2.1) (vert α (face f).2.2) := by
  intro H
  obtain ⟨e0, e1, e2⟩ := faceWord_spec f
  obtain ⟨s, t, hst⟩ := plane_of_word h (faceWord f) H
  rw [e0, e1, e2] at hst
  have hm : 3 ≤ (app (faceWord f) m).val := by
    have n0 : app (faceWord f) m ≠ 0 := by
      rw [← e0]; exact fun h' => h1 (app_injective _ h')
    have n1 : app (faceWord f) m ≠ 1 := by
      rw [← e1]; exact fun h' => h2 (app_injective _ h')
    have n2 : app (faceWord f) m ≠ 2 := by
      rw [← e2]; exact fun h' => h3 (app_injective _ h')
    revert n0 n1 n2
    generalize app (faceWord f) m = x
    revert x; decide
  have hz := congrArg (fun p => p.2.2) hst
  have z0 : (vert α 0).2.2 = 0 := by simp [vert]
  have z1 : (vert α 1).2.2 = 0 := by simp [vert]
  have z2 : (vert α 2).2.2 = 0 := by simp [vert]
  simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul, z0, z1, z2] at hz
  have hu := isUnit_z h _ hm
  rw [show (vert α (app (faceWord f) m)).2.2 = 0 by linear_combination hz] at hu
  exact not_isUnit_zero hu

end Faithful

/-! ## Modulo 5 -/

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `𝔽₅³`, the affine space of the reduction. -/
abbrev V5 := ZMod 5 × ZMod 5 × ZMod 5

/-- In `𝔽₅`, `α² + α − 1 = (α − 2)²`: the only root is `2` (page 78). -/
theorem alpha_eq_two (a : ZMod 5) : a ^ 2 + a - 1 = 0 ↔ a = 2 := by
  revert a; decide +kernel

/-- The centre `o = ½(α', 1 − α', 1 − α')` at `α = 2`. -/
def o : V5 := (1, 2, 2)

theorem two_centre : (2 : ZMod 5) • o = ((-1 - 2), 1 - (-1 - 2), 1 - (-1 - 2)) := by
  decide +kernel

theorem centre_fixed :
    sigma0 o = o ∧ sigma1 (2 : ZMod 5) o = o ∧ sigma2 o = o ∧ iota (2 : ZMod 5) o = o := by
  decide +kernel

/-- The centred vertex `s − o`. -/
def cv (i : Fin 12) : V5 := vert (2 : ZMod 5) i - o

/-- Page 78: in characteristic 5 the vertices are isotropic for `q₀` centred at `o`. -/
theorem vert_isotropic (i : Fin 12) : q0 (2 : ZMod 5) (cv i) = 0 := by
  revert i; decide +kernel

/-- `q(o) = 0`: the circumscribed quadric is a cone of vertex `o`. -/
theorem q_centre : q (2 : ZMod 5) o = 0 := by decide +kernel

/-- The nonzero isotropic vectors are the twelve centred vertices and their doubles. -/
theorem isotropic_iff (v : V5) :
    (v ≠ 0 ∧ q0 (2 : ZMod 5) v = 0) ↔ ∃ i, v = cv i ∨ v = (2 : ZMod 5) • cv i := by
  revert v; decide +kernel

/-- « Deux icosaèdres » : the vertices `s − o` and `2(s − o)`. -/
def twoIcos : Fin 12 ⊕ Fin 12 → V5
  | .inl i => cv i
  | .inr i => (2 : ZMod 5) • cv i

theorem twoIcos_injective : Function.Injective twoIcos := by
  unfold Function.Injective; decide +kernel

theorem isotropic_card :
    (Finset.univ.filter fun v : V5 => v ≠ 0 ∧ q0 (2 : ZMod 5) v = 0).card = 24 := by
  decide +kernel

theorem card_square :
    (Finset.univ.filter fun v : V5 => q0 (2 : ZMod 5) v = 1 ∨ q0 (2 : ZMod 5) v = 4).card
      = 60 := by
  decide +kernel

theorem card_nonsquare :
    (Finset.univ.filter fun v : V5 => q0 (2 : ZMod 5) v = 2 ∨ q0 (2 : ZMod 5) v = 3).card
      = 40 := by
  decide +kernel

/-! ### The 31 points of `ℙ²(𝔽₅)` -/

/-- The edge vector of an edge. -/
def ev (e : Fin 30) : V5 := vert (2 : ZMod 5) (edge e).2 - vert (2 : ZMod 5) (edge e).1

/-- The centred barycentre (tripled) of a face. -/
def fv (f : Fin 20) : V5 := cv (face f).1 + cv (face f).2.1 + cv (face f).2.2

/-- One edge for each of the fifteen edge directions. -/
def edgeRep : Fin 15 → Fin 30 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 17]

/-- The representative vectors: six vertex directions `s₀ − o, …, s''₃ − o`, fifteen
edge directions, ten face directions (faces `0, …, 9`). -/
def rep : Fin 6 ⊕ Fin 15 ⊕ Fin 10 → V5
  | .inl i => cv (Fin.castLE (by norm_num) i)
  | .inr (.inl k) => ev (edgeRep k)
  | .inr (.inr k) => fv (Fin.castLE (by norm_num) k)

theorem rep_ne_zero (x : Fin 6 ⊕ Fin 15 ⊕ Fin 10) : rep x ≠ 0 := by
  revert x; decide +kernel

/-- The point of `ℙ²(𝔽₅)` of a representative. -/
def point (x : Fin 6 ⊕ Fin 15 ⊕ Fin 10) : Projectivization (ZMod 5) V5 :=
  Projectivization.mk (ZMod 5) (rep x) (rep_ne_zero x)

theorem rep_prop_iff : ∀ x y : Fin 6 ⊕ Fin 15 ⊕ Fin 10,
    (∃ a : ZMod 5, a • rep y = rep x) → x = y := by
  decide +kernel

theorem rep_cover : ∀ v : V5, v ≠ 0 → ∃ x, ∃ a : ZMod 5, a • rep x = v := by
  decide +kernel

/-- Page 78: the 6 + 15 + 10 vertex, edge and face directions are the 31 points of
`ℙ²(𝔽₅)`, each once. -/
theorem point_bijective : Function.Bijective point := by
  refine ⟨fun x y hxy => ?_, fun p => ?_⟩
  · unfold point at hxy
    rw [Projectivization.mk_eq_mk_iff'] at hxy
    exact rep_prop_iff x y hxy
  · obtain ⟨x, a, ha⟩ := rep_cover p.rep p.rep_nonzero
    refine ⟨x, ?_⟩
    rw [← Projectivization.mk_rep p]
    unfold point
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨a⁻¹, by rw [← ha, smul_smul, inv_mul_cancel₀]; · simp
                   rintro rfl; exact p.rep_nonzero (by rw [← ha, zero_smul])⟩

theorem card_proj : Nat.card (Projectivization (ZMod 5) V5) = 31 := by
  rw [← Nat.card_eq_of_bijective point point_bijective]
  simp

/-- Every vertex direction is one of the six. -/
theorem vertDir_cover : ∀ i : Fin 12, ∃ k : Fin 6, ∃ a : ZMod 5, cv i = a • rep (.inl k) := by
  decide +kernel

/-- Each of the thirty edges is along one of the fifteen chosen edge directions. -/
theorem edgeDir_cover :
    ∀ e : Fin 30, ∃ k : Fin 15, ∃ a : ZMod 5, ev e = a • rep (.inr (.inl k)) := by
  decide +kernel

/-- Each of the twenty faces gives one of the ten chosen face directions. -/
theorem faceDir_cover :
    ∀ f : Fin 20, ∃ k : Fin 10, ∃ a : ZMod 5, fv f = a • rep (.inr (.inr k)) := by
  decide +kernel

/-- The face direction is the barycentre, polar-orthogonal to the plane of the face. -/
theorem face_orth : ∀ f : Fin 20,
    polar (2 : ZMod 5) (fv f) (cv (face f).2.1 - cv (face f).1) = 0 ∧
    polar (2 : ZMod 5) (fv f) (cv (face f).2.2 - cv (face f).1) = 0 := by
  decide +kernel

/-- Page 78: a point of `ℙ²(𝔽₅)` lies on the conic `q₀ = 0` iff it is a vertex
direction. -/
theorem conic_iff (v : V5) (hv : v ≠ 0) :
    q0 (2 : ZMod 5) v = 0 ↔ Projectivization.mk (ZMod 5) v hv ∈ Set.range (point ∘ .inl) := by
  have key : ∀ v : V5, v ≠ 0 →
      (q0 (2 : ZMod 5) v = 0 ↔ ∃ k : Fin 6, ∃ a : ZMod 5, a • rep (.inl k) = v) := by
    decide +kernel
  rw [key v hv]
  constructor
  · rintro ⟨k, a, ha⟩
    exact ⟨k, by
      simp only [Function.comp, point]
      rw [Projectivization.mk_eq_mk_iff']
      refine ⟨a⁻¹, ?_⟩
      have ha0 : a ≠ 0 := by rintro rfl; exact hv (by rw [← ha, zero_smul])
      rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩
  · rintro ⟨k, hk⟩
    simp only [Function.comp, point] at hk
    rw [Projectivization.mk_eq_mk_iff'] at hk
    obtain ⟨a, ha⟩ := hk
    have ha0 : a ≠ 0 := by
      rintro rfl; exact rep_ne_zero (.inl k) (by rw [← ha, zero_smul])
    exact ⟨k, a⁻¹, by rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

/-- The tangent to the conic at the vertex direction `k` passes through `rep x`. -/
def onTangent (k : Fin 6) (x : Fin 6 ⊕ Fin 15 ⊕ Fin 10) : Prop :=
  polar (2 : ZMod 5) (rep (.inl k)) (rep x) = 0

instance (k : Fin 6) (x : Fin 6 ⊕ Fin 15 ⊕ Fin 10) : Decidable (onTangent k x) := by
  unfold onTangent; infer_instance

/-- An edge direction lies on exactly two tangents of the conic (an exterior point). -/
theorem edge_tangents :
    ∀ k : Fin 15, (Finset.univ.filter fun j => onTangent j (.inr (.inl k))).card = 2 := by
  decide +kernel

/-- A face direction lies on no tangent of the conic (an interior point). -/
theorem face_tangents :
    ∀ k : Fin 10, (Finset.univ.filter fun j => onTangent j (.inr (.inr k))).card = 0 := by
  decide +kernel

end Grothendieck.Folder70

namespace Grothendieck.Folder70

/-! ## The universal formulae (finding `70-universal-formulae-double-cosines`)

Pages 9–25 of the reading write a regular affine realisation by reflections of
`{p₁, …, pₙ}` in its vertex frame `(s₀, …, s_{n+1})`: in barycentric coordinates,
`σᵢ = id + ℓᵢ ⊗ (s_{i+1} − sᵢ)` with `ℓᵢ = tᵢ − tᵢ₊₁ + (1 + αᵢ)(tᵢ₊₂ + ⋯ + t_{n+1})`
(pages 23–25), and page 67 states, for `n = 2` and without proof,
« `ρ_s^p = id ⇔ F_p(α) = 0` ». Here `usig n α i` is that `σᵢ`, acting linearly on
`ℕ → R` (homogeneous barycentric coordinates; `sum_usig`: the affine space `Σ tⱼ = 1`
is preserved), over any commutative ring and for every `n`.

* `usig_mul_self`, `usig_comm`: the relations of the string Coxeter group,
  `σᵢ² = 1` and `σᵢσⱼ = σⱼσᵢ` for `j ≥ i + 2`, whatever the `αᵢ` (page 19);
  `usig_sv_self`, `usig_sv_succ`, `usig_sv_of_lt`, `usig_sv_of_le`: the table of page 25.
* `rho_apply`, `rho_cubic`: `σₖσₖ₊₁ − 1` has its image in the plane of
  `sₖ₊₁ − sₖ, sₖ₊₂ − sₖ₊₁`, and `(t − 1)(t² − αₖt + 1)` kills `σₖσₖ₊₁`.
* `orderOf_rho_eq_three`, `orderOf_rho_eq_four`, `orderOf_rho_eq_five`: over every
  nonzero commutative ring, `σₖσₖ₊₁` has order exactly `3`, `4`, `5` iff `αₖ = −1`,
  `αₖ = 0`, `αₖ² + αₖ − 1 = 0` — the minimal polynomials of `2cos(2π/p)` for the
  values of `p` that occur in the finite regular polytopes. No field, no `p` invertible.
* `usig_emb`, `ico_orderOf`: the generators of pages 74–75 above are the case
  `n = 2`, `(α₀, α₁) = (−1, α)`; tetrahedron `(−1, −1)`, cube `(0, −1)`, octahedron
  `(−1, 0)` and dodecahedron `(α, −1)` are the other Platonic cases of the same theorems.

Not formalised: the criterion for general `p` (it needs the minimal polynomial of
`2cos(2π/p)`), the passage from the definition of a regular realisation to the normal
form (pages 7–18). -/

section Universal

variable {R : Type*} [CommRing R] (n : ℕ) (α : ℕ → R)

/-- The vertex `s_j` of the frame, in barycentric coordinates `(t₀, …, t_{n+1})`. -/
def sv (j : ℕ) : ℕ → R := Pi.single j 1

/-- The affine form `ℓᵢ = tᵢ − tᵢ₊₁ + (1 + αᵢ)(tᵢ₊₂ + ⋯ + t_{n+1})` of page 23. -/
def ell (i : ℕ) : (ℕ → R) →ₗ[R] R :=
  LinearMap.proj (R := R) (φ := fun _ : ℕ => R) i - LinearMap.proj (i + 1) +
    (1 + α i) • ∑ j ∈ Finset.Ico (i + 2) (n + 2), LinearMap.proj j

/-- The edge vector `s_{i+1} − sᵢ`. -/
def wv (i : ℕ) : ℕ → R := sv (i + 1) - sv i

/-- The universal reflection `σᵢ = id + ℓᵢ ⊗ (s_{i+1} − sᵢ)` of pages 23–25. -/
def usig (i : ℕ) : Module.End R (ℕ → R) := 1 + (ell n α i).smulRight (wv i)

variable {n α}

theorem ell_apply (i : ℕ) (x : ℕ → R) :
    ell n α i x = x i - x (i + 1) + (1 + α i) * ∑ j ∈ Finset.Ico (i + 2) (n + 2), x j := by
  simp [ell]

theorem usig_apply (i : ℕ) (x : ℕ → R) :
    usig n α i x = x + ell n α i x • wv i := by
  simp [usig]

theorem ell_sv (i j : ℕ) : ell n α i (sv j) =
    (if i = j then 1 else 0) - (if i + 1 = j then 1 else 0) +
      (1 + α i) * (if i + 2 ≤ j ∧ j < n + 2 then 1 else 0) := by
  simp [ell_apply, sv, Pi.single_apply]

theorem ell_wv_self (i : ℕ) : ell n α i (wv i) = -2 := by
  simp only [wv, map_sub, ell_sv]; simp; ring

theorem ell_wv_of_le {i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n) : ell n α i (wv j) = 0 := by
  simp only [wv, map_sub, ell_sv]
  split_ifs <;> first | omega | ring

theorem ell_wv_of_lt {i j : ℕ} (hij : i + 1 < j) : ell n α j (wv i) = 0 := by
  simp only [wv, map_sub, ell_sv]
  split_ifs <;> first | omega | ring

theorem usig_wv_self (i : ℕ) : usig n α i (wv i) = -wv i := by
  rw [usig_apply, ell_wv_self]; module

/-- `σᵢ² = 1`, whatever the `αⱼ` (page 19). -/
theorem usig_mul_self (i : ℕ) : usig n α i * usig n α i = 1 := by
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply, Module.End.one_apply, usig_apply (x := x), map_add, map_smul,
    usig_wv_self, usig_apply]
  module

/-- `σᵢ σⱼ = σⱼ σᵢ` for `j ≥ i + 2`, whatever the `αₖ` (page 19). -/
theorem usig_comm {i j : ℕ} (hij : i + 2 ≤ j) (hj : j ≤ n) :
    usig n α i * usig n α j = usig n α j * usig n α i := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, usig_apply, map_add, map_smul,
    ell_wv_of_le hij hj, ell_wv_of_lt (show i + 1 < j by omega)]
  module

/-- `σᵢ` preserves `t₀ + ⋯ + t_{n+1}`: it acts on the affine space `Σ tⱼ = 1`. -/
theorem sum_usig (i : ℕ) (hi : i ≤ n) (x : ℕ → R) :
    ∑ j ∈ Finset.range (n + 2), usig n α i x j = ∑ j ∈ Finset.range (n + 2), x j := by
  simp only [usig_apply, wv, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, sv, Pi.single_apply,
    smul_eq_mul, Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq', Finset.mem_range, show i + 1 < n + 2 by omega,
    show i < n + 2 by omega]

/-- The table of page 25: `σᵢ sⱼ = sⱼ` for `j < i`. -/
theorem usig_sv_of_lt {i j : ℕ} (h : j < i) : usig n α i (sv j) = sv j := by
  rw [usig_apply, ell_sv, wv]; split_ifs <;> (try omega); simp

/-- `σᵢ sᵢ = sᵢ₊₁`. -/
theorem usig_sv_self (i : ℕ) : usig n α i (sv i) = sv (i + 1) := by
  rw [usig_apply, ell_sv, wv]; split_ifs <;> (try omega); simp

/-- `σᵢ sᵢ₊₁ = sᵢ`. -/
theorem usig_sv_succ (i : ℕ) : usig n α i (sv (i + 1)) = sv i := by
  rw [usig_apply, ell_sv, wv]; split_ifs <;> (try omega); simp

/-- `σᵢ sⱼ = −(1 + αᵢ) sᵢ + (1 + αᵢ) sᵢ₊₁ + sⱼ` for `i + 2 ≤ j ≤ n + 1` (page 25). -/
theorem usig_sv_of_le {i j : ℕ} (h1 : i + 2 ≤ j) (h2 : j ≤ n + 1) :
    usig n α i (sv j) = sv j + (1 + α i) • wv i := by
  rw [usig_apply, ell_sv, wv]; split_ifs <;> (try omega); simp

/-! ### The rotations `σₖ σₖ₊₁` -/

/-- The rotation `σₖ σₖ₊₁` of the polygon in `f_{k+2}`. -/
def rho (k : ℕ) : Module.End R (ℕ → R) := usig n α k * usig n α (k + 1)

theorem ell_succ_wv (k : ℕ) : ell n α (k + 1) (wv k) = 1 := by
  simp only [wv, map_sub, ell_sv]
  split_ifs <;> first | omega | ring

theorem ell_wv_succ {k : ℕ} (hk : k + 1 ≤ n) : ell n α k (wv (k + 1)) = 2 + α k := by
  simp only [wv, map_sub, ell_sv]
  split_ifs <;> first | omega | ring

theorem rho_wv {k : ℕ} (hk : k + 1 ≤ n) :
    rho (n := n) (α := α) k (wv k) = (1 + α k) • wv k + wv (k + 1) := by
  rw [rho, Module.End.mul_apply, usig_apply (i := k + 1), ell_succ_wv, one_smul, map_add,
    usig_wv_self, usig_apply, ell_wv_succ hk]
  module

theorem rho_wv_succ {k : ℕ} (hk : k + 1 ≤ n) :
    rho (n := n) (α := α) k (wv (k + 1)) = -((2 + α k) • wv k) - wv (k + 1) := by
  rw [rho, Module.End.mul_apply, usig_wv_self, map_neg, usig_apply, ell_wv_succ hk]
  module

/-- `σₖ σₖ₊₁ − 1` takes its values in the plane of `sₖ₊₁ − sₖ` and `sₖ₊₂ − sₖ₊₁`. -/
theorem rho_apply (k : ℕ) (x : ℕ → R) :
    rho (n := n) (α := α) k x =
      x + ell n α k (usig n α (k + 1) x) • wv k + ell n α (k + 1) x • wv (k + 1) := by
  rw [rho, Module.End.mul_apply, usig_apply (i := k), usig_apply (i := k + 1)]
  module

/-- `f^m x = x + Σ_{j<m} f^j (f x − x)`. -/
theorem pow_apply_eq (f : Module.End R (ℕ → R)) (m : ℕ) (x : ℕ → R) :
    (f ^ m) x = x + ∑ j ∈ Finset.range m, (f ^ j) (f x - x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, show f x = x + (f x - x) by abel, map_add, ih,
      Finset.sum_range_succ]
    abel_nf

/-- A vector of the plane of `sₖ₊₁ − sₖ` and `sₖ₊₂ − sₖ₊₁`. -/
def pl (k : ℕ) (a b : R) : ℕ → R := a • wv k + b • wv (k + 1)

theorem rho_pl {k : ℕ} (hk : k + 1 ≤ n) (a b : R) :
    rho (n := n) (α := α) k (pl k a b) = pl k ((1 + α k) * a - (2 + α k) * b) (a - b) := by
  simp only [pl, map_add, map_smul, rho_wv hk, rho_wv_succ hk]
  module

theorem pl_add (k : ℕ) (a b c d : R) : pl k a b + pl k c d = pl k (a + c) (b + d) := by
  simp only [pl]; module

theorem pl_eq_zero {k : ℕ} {a b : R} (ha : a = 0) (hb : b = 0) : pl k a b = 0 := by
  simp [pl, ha, hb]

theorem rho_pow_eq_one {k : ℕ} (m : ℕ)
    (h : ∀ a b : R, ∑ j ∈ Finset.range m, (rho (n := n) (α := α) k ^ j) (pl k a b) = 0) :
    rho (n := n) (α := α) k ^ m = 1 := by
  refine LinearMap.ext fun x => ?_
  rw [pow_apply_eq, Module.End.one_apply, show rho k x - x = pl k _ _ by
    rw [rho_apply, pl]; abel, h, add_zero]

/-- A vector of the plane `⟨sₖ, sₖ₊₁, sₖ₊₂⟩`. -/
def tri (k : ℕ) (a b c : R) : ℕ → R := a • sv k + b • sv (k + 1) + c • sv (k + 2)

theorem rho_tri {k : ℕ} (hk : k + 1 ≤ n) (a b c : R) :
    rho (n := n) (α := α) k (tri k a b c) =
      tri k (c - (1 + α k) * b) (a + (1 + α k) * b) b := by
  have h0 : rho (n := n) (α := α) k (sv k) = sv (k + 1) := by
    rw [rho, Module.End.mul_apply, usig_sv_of_lt (by omega), usig_sv_self]
  have h1 : rho (n := n) (α := α) k (sv (k + 1)) = sv (k + 2) + (1 + α k) • wv k := by
    rw [rho, Module.End.mul_apply, usig_sv_self, usig_sv_of_le (by omega) (by omega)]
  have h2 : rho (n := n) (α := α) k (sv (k + 2)) = sv k := by
    rw [rho, Module.End.mul_apply, usig_sv_succ, usig_sv_succ]
  simp only [tri, map_add, map_smul, h0, h1, h2, wv]
  module

theorem tri_apply (k : ℕ) (a b c : R) :
    tri k a b c k = a ∧ tri k a b c (k + 1) = b ∧ tri k a b c (k + 2) = c := by
  simp [tri, sv]

/-- `σₖ σₖ₊₁` on `⟨sₖ, sₖ₊₁, sₖ₊₂⟩`, in coordinates. -/
def step (α : ℕ → R) (k : ℕ) (t : R × R × R) : R × R × R :=
  (t.2.2 - (1 + α k) * t.2.1, t.1 + (1 + α k) * t.2.1, t.2.1)

theorem rho_pow_tri {k : ℕ} (hk : k + 1 ≤ n) (m : ℕ) (t : R × R × R) :
    (rho (n := n) (α := α) k ^ m) (tri k t.1 t.2.1 t.2.2) =
      tri k ((step α k)^[m] t).1 ((step α k)^[m] t).2.1 ((step α k)^[m] t).2.2 := by
  induction m generalizing t with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, rho_tri hk, Function.iterate_succ_apply]
    exact ih (step α k t)

/-- If `(σₖ σₖ₊₁)^m = 1`, the orbit of `sₖ` closes after `m` steps. -/
theorem step_pow_of_rho_pow {k : ℕ} (hk : k + 1 ≤ n) {m : ℕ}
    (h : rho (n := n) (α := α) k ^ m = 1) : (step α k)^[m] (1, 0, 0) = (1, 0, 0) := by
  have e := rho_pow_tri (α := α) hk m (1, 0, 0)
  rw [h, Module.End.one_apply] at e
  have h1 := tri_apply k (1 : R) 0 0
  have h2 := tri_apply k ((step α k)^[m] (1, 0, 0)).1 ((step α k)^[m] (1, 0, 0)).2.1
    ((step α k)^[m] (1, 0, 0)).2.2
  rw [← e] at h2
  exact Prod.ext (h2.1.symm.trans h1.1) (Prod.ext (h2.2.1.symm.trans h1.2.1)
    (h2.2.2.symm.trans h1.2.2))

/-- If the orbit of `sₖ` does not close after `m` steps, `(σₖ σₖ₊₁)^m ≠ 1`. -/
theorem rho_pow_ne_one {k : ℕ} (hk : k + 1 ≤ n) {m : ℕ}
    (h : (step α k)^[m] (1, 0, 0) ≠ (1, 0, 0)) : rho (n := n) (α := α) k ^ m ≠ 1 :=
  fun h' => h (step_pow_of_rho_pow hk h')

/-- `(t − 1)(t² − αₖ t + 1)` kills `σₖ σₖ₊₁`, for every `n` and every ring. -/
theorem rho_cubic {k : ℕ} (hk : k + 1 ≤ n) (x : ℕ → R) :
    (rho (n := n) (α := α) k ^ 3) x - (1 + α k) • (rho (n := n) (α := α) k ^ 2) x +
      (1 + α k) • (rho (n := n) (α := α) k ^ 1) x - x = 0 := by
  have hy : rho (n := n) (α := α) k x - x =
      pl k (ell n α k (usig n α (k + 1) x)) (ell n α (k + 1) x) := by
    rw [rho_apply, pl]; abel
  rw [pow_apply_eq _ 3, pow_apply_eq _ 2, pow_apply_eq _ 1, hy]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_succ, pow_zero,
    Module.End.mul_apply, Module.End.one_apply, rho_pl hk, zero_add]
  simp only [pl]
  module

theorem orderOf_rho_eq_three [Nontrivial R] {k : ℕ} (hk : k + 1 ≤ n) :
    orderOf (rho (n := n) (α := α) k) = 3 ↔ α k = -1 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rintro ⟨h, -⟩
    have e := step_pow_of_rho_pow hk h
    simp only [step, Function.iterate_succ_apply', Function.iterate_zero_apply,
      Prod.mk.injEq] at e
    linear_combination e.2.2
  · intro h
    refine ⟨rho_pow_eq_one 3 fun a b => ?_, fun m hm h0 => rho_pow_ne_one hk ?_⟩
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_succ, pow_zero,
        Module.End.mul_apply, Module.End.one_apply, rho_pl hk, pl_add, zero_add]
      apply pl_eq_zero
      · linear_combination ((1 + α k) * a - (2 + α k) * b) * h
      · linear_combination (a - b) * h
    · obtain rfl | rfl : m = 1 ∨ m = 2 := by omega
      all_goals simp [step, Function.iterate_succ_apply', Prod.ext_iff]

theorem orderOf_rho_eq_four [Nontrivial R] {k : ℕ} (hk : k + 1 ≤ n) :
    orderOf (rho (n := n) (α := α) k) = 4 ↔ α k = 0 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rintro ⟨h, -⟩
    have e := step_pow_of_rho_pow hk h
    simp only [step, Function.iterate_succ_apply', Function.iterate_zero_apply,
      Prod.mk.injEq] at e
    linear_combination α k * e.2.2 - e.2.1
  · intro h
    refine ⟨rho_pow_eq_one 4 fun a b => ?_, fun m hm h0 => rho_pow_ne_one hk ?_⟩
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_succ, pow_zero,
        Module.End.mul_apply, Module.End.one_apply, rho_pl hk, pl_add, zero_add]
      apply pl_eq_zero <;> rw [h] <;> ring
    · obtain rfl | rfl | rfl : m = 1 ∨ m = 2 ∨ m = 3 := by omega
      all_goals
        simp only [step, Function.iterate_succ_apply', Function.iterate_zero_apply, ne_eq,
          Prod.mk.injEq]
        intro e
        apply one_ne_zero (α := R)
      · linear_combination -e.1
      · linear_combination e.2.2
      · linear_combination e.2.2 - h

theorem orderOf_rho_eq_five [Nontrivial R] {k : ℕ} (hk : k + 1 ≤ n) :
    orderOf (rho (n := n) (α := α) k) = 5 ↔ α k ^ 2 + α k - 1 = 0 := by
  rw [orderOf_eq_iff (by norm_num)]
  constructor
  · rintro ⟨h, -⟩
    have e := step_pow_of_rho_pow hk h
    simp only [step, Function.iterate_succ_apply', Function.iterate_zero_apply,
      Prod.mk.injEq] at e
    linear_combination α k * e.2.2 - e.2.1
  · intro h
    refine ⟨rho_pow_eq_one 5 fun a b => ?_, fun m hm h0 => rho_pow_ne_one hk ?_⟩
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_succ, pow_zero,
        Module.End.mul_apply, Module.End.one_apply, rho_pl hk, pl_add, zero_add]
      apply pl_eq_zero
      · linear_combination (α k * ((1 + α k) * a - (2 + α k) * b) - a) * h
      · linear_combination (α k * (a - b) - b) * h
    · obtain rfl | rfl | rfl | rfl : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
      all_goals
        simp only [step, Function.iterate_succ_apply', Function.iterate_zero_apply, ne_eq,
          Prod.mk.injEq]
        intro e
        apply one_ne_zero (α := R)
      · linear_combination -e.1
      · linear_combination e.2.2
      · linear_combination e.2.1 - h
      · linear_combination e.2.2 - h

/-! ### The icosahedron of pages 74–75 is the case `(α₀, α₁) = (−1, α)` -/

/-- A point `(x, y, z)` of page 74 in barycentric coordinates `(1 − x − y − z, x, y, z)`. -/
def emb (p : R × R × R) : ℕ → R := fun j =>
  if j = 0 then 1 - p.1 - p.2.1 - p.2.2 else if j = 1 then p.1 else if j = 2 then p.2.1
  else if j = 3 then p.2.2 else 0

/-- The parameters of the icosahedron `{3, 5}`. -/
def icoα (a : R) : ℕ → R := fun i => if i = 0 then -1 else a

theorem usig_emb (a : R) (p : R × R × R) :
    usig 2 (icoα a) 0 (emb p) = emb (sigma0 p) ∧
      usig 2 (icoα a) 1 (emb p) = emb (sigma1 a p) ∧
      usig 2 (icoα a) 2 (emb p) = emb (sigma2 p) := by
  have e0 : Finset.Ico 2 4 = {2, 3} := by decide
  have e1 : Finset.Ico 3 4 = {3} := by decide
  refine ⟨funext fun j => ?_, funext fun j => ?_, funext fun j => ?_⟩ <;>
    rcases j with _ | _ | _ | _ | j <;>
    simp [usig_apply, ell_apply, wv, sv, emb, icoα, sigma0, sigma1, sigma2, e0, e1] <;> ring

/-- The icosahedron's rotations have orders `3` and `5` exactly, over every nonzero ring
with `α² + α − 1 = 0`. -/
theorem ico_orderOf [Nontrivial R] {a : R} (h : a ^ 2 + a - 1 = 0) :
    orderOf (rho (n := 2) (α := icoα a) 0) = 3 ∧ orderOf (rho (n := 2) (α := icoα a) 1) = 5 :=
  ⟨(orderOf_rho_eq_three (by norm_num)).2 (by simp [icoα]),
    (orderOf_rho_eq_five (by norm_num)).2 (by simpa [icoα] using h)⟩

end Universal
end Grothendieck.Folder70
