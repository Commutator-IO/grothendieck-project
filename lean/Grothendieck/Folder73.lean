import Mathlib

/-!
# Folder 73 (« Polygones », [from 1976]): ear areas of plane polygons

The modernised reading `transcripts/73/73.modern.tex` studies the map sending a plane
`n`-gon, given by its sides `u_i = s_{i+1} - s_i`, to the doubled signed areas of its
« ears », `μ_i = u_{i-1} ∧ u_i`. Two of its statements are proved here; they are findings
`73-quadrilateral-projective-frame` and `73-zero-multiplier-criterion` of
`src/content/findings.ts`. Proving them says only that the claims hold as stated; whether
they stand in the literature is a separate question.

The plane is `k²` (`Fin 2 → k`) with the volume form `a ∧ b = a₀b₁ - a₁b₀`; an affine map
acts on sides through its linear part, a `2 × 2` matrix.

## Pages 5–6: closed quadrilaterals form a projective plane

* `mu_relation`: `μ₀ + μ₂ = μ₁ + μ₃` for a closed quadrilateral, over any commutative ring,
  from `wedge_diag`: `u₀ ∧ u₂ = μ₀ - μ₁ = μ₃ - μ₂` and `u₁ ∧ u₃ = μ₁ - μ₂ = μ₀ - μ₃`. The
  page's second line `u₁ ∧ u₃ = μ₀ - μ₂`, copied by the reading, is false
  (`not_wedge13_eq`); the page's own fourth line has the right value. The six products
  `u_i ∧ u_j` are combinations of the `μ_i` (`wedge_eq_zero_of_mu`), so a quadrilateral not
  contained in a line has some `μ_i ≠ 0`.
* `mu_mulVec`: a linear map `M` multiplies every `μ_i` by `det M`.
* `quad_moduli` (injectivity on affine classes): two closed non-collinear quadrilaterals
  have proportional ear areas if and only if one is the image of the other by an invertible
  linear map; `exists_quad_of_mu` (surjectivity, the page's « épi ? »): every nonzero point
  of the plane `μ₀ + μ₂ = μ₁ + μ₃` is the ear-area vector of a closed quadrilateral.
* `side_eq_zero_iff`, `mu_eq_smul_framePt`: for a closed non-collinear quadrilateral,
  `u_i = 0 ⇔ μ_i = μ_{i+1} = 0`, and then `μ` is a nonzero multiple of the point `p_i`
  (`(0,0,1,1)`, `(1,0,0,1)`, `(1,1,0,0)`, `(0,1,1,0)` for `i = 0, 1, 2, 3`).
* `sum_smul_framePt_eq_zero_iff`, `framePt_three_indep`: the only relation among the
  `p_i` is the alternating one, so any three are independent (a projective frame);
  `frame_canonical`: `k⁴ / k·(1,1,1,1)` is linearly isomorphic to the plane, the class of
  the `i`-th basis vector going to `(-1)ⁱ p_i` — the plane is `P(k^A / k·(1,1,1,1))`. The
  sign is needed: `e_i ↦ p_i` has kernel `k·(1,-1,1,-1)`.

Proved over a field (the identities over any commutative ring); the page's `P²_ℤ`, the
statement over `Spec ℤ` as an isomorphism of schemes, is not formalised.

## Pages 15, 18, 28: the zero-multiplier criterion

For `u : ZMod n → k²` with all `u_i ≠ 0`, the multipliers are the `λ` with
`λ_i u_{i-1} - λ_{i+1}(u_i + u_{i+1}) + λ_{i+2} u_{i+2} = 0` for all `i` (`IsMult`). The
juxtaposition `u·v` of the page is read in `Sym² V`, here `k³` through
`a·b ↦ (a₀b₀, a₀b₁ + a₁b₀, a₁b₁)` (`symProd`).

* `zero_multiplier_criterion`: a multiplier with `λ₀ = 0`, `λ₁ = 1` exists if and only if
  `Σ u_i = 0` and, for `2 ≤ i ≤ n - 1`, either `s_i = s_0` (`u_{0i} = 0`) or the pair of
  directions of `{u_{i-1}, u_i}` is that of `{u_1, u_{0i}}`.
* `symProd_formula`: it then satisfies `λ_i u_{i-1}·u_i = u_1·u_{0i}` for every `i ≥ 1`;
  `mult_eq_zero_iff`: `λ_i = 0 ⇔ s_i = s_0`; `mult_unique`: it is unique.
* `eq_zero_of_consecutive`: a multiplier with two consecutive zero components is zero,
  which justifies the normalisation `λ₁ = 1`.
* `symProd_proportional_iff`: for nonzero vectors of a plane, `c·d ∈ k·(a·b)` if and only if
  `{[a], [b]} = {[c], [d]}` — the factorisation fact the « pair of directions » rests on.
-/

namespace Folder73

open Matrix

variable {k : Type*}

/-- The volume form on `k²`: `a ∧ b = a₀b₁ - a₁b₀`. -/
def wedge [CommRing k] (a b : Fin 2 → k) : k := a 0 * b 1 - a 1 * b 0

section Basic

variable [CommRing k]

theorem wedge_swap (a b : Fin 2 → k) : wedge b a = -wedge a b := by
  unfold wedge; ring

theorem wedge_self (a : Fin 2 → k) : wedge a a = 0 := by
  unfold wedge; ring

/-- Cramer's rule in the plane. -/
theorem cramer (a b x : Fin 2 → k) :
    wedge a b • x = wedge x b • a + wedge a x • b := by
  funext j; fin_cases j <;> simp [wedge] <;> ring

theorem wedge_mulVec (M : Matrix (Fin 2) (Fin 2) k) (a b : Fin 2 → k) :
    wedge (M *ᵥ a) (M *ᵥ b) = M.det * wedge a b := by
  simp [wedge, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]; ring

end Basic

/-! ## Quadrilaterals (pages 5–6) -/

section Quadrilateral

variable [CommRing k]

/-- The ear areas of a quadrilateral given by its sides: `μ_i = u_{i-1} ∧ u_i`. -/
def mu (u : Fin 4 → Fin 2 → k) (i : Fin 4) : k := wedge (u (i - 1)) (u i)

/-- A quadrilateral given by its sides is closed when they add up to zero. -/
def Closed (u : Fin 4 → Fin 2 → k) : Prop := ∑ i, u i = 0

theorem mu_zero (u : Fin 4 → Fin 2 → k) : mu u 0 = wedge (u 3) (u 0) := rfl
theorem mu_one (u : Fin 4 → Fin 2 → k) : mu u 1 = wedge (u 0) (u 1) := rfl
theorem mu_two (u : Fin 4 → Fin 2 → k) : mu u 2 = wedge (u 1) (u 2) := rfl
theorem mu_three (u : Fin 4 → Fin 2 → k) : mu u 3 = wedge (u 2) (u 3) := rfl

theorem closed_iff (u : Fin 4 → Fin 2 → k) : Closed u ↔ u 3 = -(u 0 + u 1 + u 2) := by
  unfold Closed
  rw [Fin.sum_univ_four]
  constructor
  · intro h; rw [← sub_eq_zero, sub_neg_eq_add, ← h]; abel
  · intro h; rw [h]; abel

/-- The two diagonal products of a closed quadrilateral (page 5): `u₀ ∧ u₂ = μ₀ - μ₁ =
μ₃ - μ₂` and `u₁ ∧ u₃ = μ₁ - μ₂ = μ₀ - μ₃`. -/
theorem wedge_diag (u : Fin 4 → Fin 2 → k) (h : Closed u) :
    wedge (u 0) (u 2) = mu u 0 - mu u 1 ∧ wedge (u 0) (u 2) = mu u 3 - mu u 2 ∧
      wedge (u 1) (u 3) = mu u 1 - mu u 2 ∧ wedge (u 1) (u 3) = mu u 0 - mu u 3 := by
  rw [closed_iff] at h
  simp only [mu_zero, mu_one, mu_two, mu_three, h, wedge, Pi.neg_apply, Pi.add_apply]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- The second line of the page-5 table, `u₁ ∧ u₃ = μ₀ - μ₂`, copied by the reading, is
false: the square `u = (e₁, e₂, e₂, -e₁ - 2e₂)` has `u₁ ∧ u₃ = 1` and `μ₀ - μ₂ = 2`. The
true value, `μ₁ - μ₂ = μ₀ - μ₃`, is the one the page's fourth line gives for `u₃ ∧ u₁`. -/
theorem not_wedge13_eq :
    ¬ ∀ u : Fin 4 → Fin 2 → ℚ, Closed u → wedge (u 1) (u 3) = mu u 0 - mu u 2 := by
  intro h
  have := h ![![1, 0], ![0, 1], ![0, 1], ![-1, -2]] (by
    rw [closed_iff]; funext j; fin_cases j <;> norm_num)
  norm_num [mu_zero, mu_two, wedge] at this

/-- Page 5: `μ₀ + μ₂ = μ₁ + μ₃`. -/
theorem mu_relation (u : Fin 4 → Fin 2 → k) (h : Closed u) :
    mu u 0 + mu u 2 = mu u 1 + mu u 3 := by
  obtain ⟨h1, h2, -⟩ := wedge_diag u h
  linear_combination h2 - h1

/-- All six products `u_i ∧ u_j` of a closed quadrilateral vanish when its ear areas do:
a closed quadrilateral not contained in a line has a nonzero ear area. -/
theorem wedge_eq_zero_of_mu (u : Fin 4 → Fin 2 → k) (h : Closed u)
    (hμ : ∀ i, mu u i = 0) (i j : Fin 4) : wedge (u i) (u j) = 0 := by
  obtain ⟨h02, -, h13, -⟩ := wedge_diag u h
  have e0 := hμ 0; have e1 := hμ 1; have e2 := hμ 2; have e3 := hμ 3
  rw [mu_zero] at e0; rw [mu_one] at e1; rw [mu_two] at e2; rw [mu_three] at e3
  rw [hμ 0, hμ 1, sub_zero] at h02
  rw [hμ 1, hμ 2, sub_zero] at h13
  have s := fun a b : Fin 4 => wedge_swap (u a) (u b)
  fin_cases i <;> fin_cases j <;>
    simp [wedge_self, e0, e1, e2, e3, h02, h13, s 0 1, s 0 2, s 1 2, s 1 3, s 2 3, s 3 0]

/-- Affine invariance: a linear map multiplies every ear area by its determinant. -/
theorem mu_mulVec (M : Matrix (Fin 2) (Fin 2) k) (u : Fin 4 → Fin 2 → k) (i : Fin 4) :
    mu (fun j => M *ᵥ u j) i = M.det * mu u i :=
  wedge_mulVec M _ _

theorem closed_mulVec (M : Matrix (Fin 2) (Fin 2) k) (u : Fin 4 → Fin 2 → k)
    (h : Closed u) : Closed (fun j => M *ᵥ u j) := by
  unfold Closed at *
  rw [← Matrix.mulVec_sum, h, Matrix.mulVec_zero]

/-- The chart `μ₁ ≠ 0` of page 5: `μ₁ u₂ = -μ₂ u₀ + (μ₃ - μ₂) u₁`. -/
theorem chart (u : Fin 4 → Fin 2 → k) (h : Closed u) :
    mu u 1 • u 2 = -mu u 2 • u 0 + (mu u 3 - mu u 2) • u 1 := by
  rw [mu_one, cramer, wedge_swap, ← mu_two, (wedge_diag u h).2.1]

/-- Rotating the labels of a quadrilateral. -/
def rot (r : Fin 4) (u : Fin 4 → Fin 2 → k) : Fin 4 → Fin 2 → k := fun j => u (j + r)

theorem mu_rot (r : Fin 4) (u : Fin 4 → Fin 2 → k) (j : Fin 4) :
    mu (rot r u) j = mu u (j + r) := by
  simp only [mu, rot]
  rw [sub_add_eq_add_sub]

theorem closed_rot (r : Fin 4) (u : Fin 4 → Fin 2 → k) (h : Closed u) :
    Closed (rot r u) := by
  unfold Closed rot at *
  rw [← h]
  exact Equiv.sum_comp (Equiv.addRight r) u

end Quadrilateral

section QuadField

variable [Field k]

/-- Injectivity in the chart `μ₁ ≠ 0`. -/
theorem exists_matrix_of_mu_one (u u' : Fin 4 → Fin 2 → k) (hu : Closed u) (hu' : Closed u')
    (c : k) (hc : c ≠ 0) (hμ : ∀ i, mu u' i = c * mu u i) (h1 : mu u 1 ≠ 0) :
    ∃ M : Matrix (Fin 2) (Fin 2) k, M.det = c ∧ ∀ i, u' i = M *ᵥ u i := by
  set m := mu u 1 with hm
  let M : Matrix (Fin 2) (Fin 2) k := m⁻¹ •
    !![u' 0 0 * u 1 1 - u' 1 0 * u 0 1, -(u' 0 0 * u 1 0) + u' 1 0 * u 0 0;
       u' 0 1 * u 1 1 - u' 1 1 * u 0 1, -(u' 0 1 * u 1 0) + u' 1 1 * u 0 0]
  have hm' : m = u 0 0 * u 1 1 - u 0 1 * u 1 0 := by rw [hm, mu_one]; rfl
  have e0 : M *ᵥ u 0 = u' 0 := by
    funext r; fin_cases r <;>
      · simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        rw [hm']; ring
  have e1 : M *ᵥ u 1 = u' 1 := by
    funext r; fin_cases r <;>
      · simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        rw [hm']; ring
  -- u'₂ from the chart of u'
  have e2 : M *ᵥ u 2 = u' 2 := by
    have c1 := chart u hu
    have c2 := chart u' hu'
    rw [hμ 1, hμ 2, hμ 3, ← hm] at c2
    have : m • (M *ᵥ u 2) = m • u' 2 := by
      rw [← Matrix.mulVec_smul, c1, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, e0, e1]
      apply smul_right_injective _ hc
      simp only [smul_add, smul_smul] at c2 ⊢
      rw [c2]; congr 1 <;> congr 1 <;> ring
    exact smul_right_injective _ h1 this
  have e3 : M *ᵥ u 3 = u' 3 := by
    rw [(closed_iff u).1 hu, (closed_iff u').1 hu', Matrix.mulVec_neg, Matrix.mulVec_add,
      Matrix.mulVec_add, e0, e1, e2]
  refine ⟨M, ?_, fun i => ?_⟩
  · have := mu_mulVec M u 1
    have hfun : (fun j => M *ᵥ u j) = u' := by
      funext j; fin_cases j
      · exact e0
      · exact e1
      · exact e2
      · exact e3
    rw [hfun, hμ 1, ← hm] at this
    exact (mul_right_cancel₀ h1 this).symm
  · fin_cases i
    · exact e0.symm
    · exact e1.symm
    · exact e2.symm
    · exact e3.symm

/-- Injectivity on affine classes (page 5, « mono »): closed quadrilaterals with
proportional ear areas, the first not contained in a line, differ by a linear map of
determinant the ratio. -/
theorem exists_matrix_of_mu (u u' : Fin 4 → Fin 2 → k) (hu : Closed u) (hu' : Closed u')
    (c : k) (hc : c ≠ 0) (hμ : ∀ i, mu u' i = c * mu u i) (hne : ∃ i, mu u i ≠ 0) :
    ∃ M : Matrix (Fin 2) (Fin 2) k, M.det = c ∧ ∀ i, u' i = M *ᵥ u i := by
  obtain ⟨i, hi⟩ := hne
  set r : Fin 4 := i - 1
  have h1 : mu (rot r u) 1 ≠ 0 := by
    rw [mu_rot]; convert hi using 2; simp [r]
  obtain ⟨M, hM, hM'⟩ := exists_matrix_of_mu_one (rot r u) (rot r u') (closed_rot r u hu)
    (closed_rot r u' hu') c hc (fun j => by rw [mu_rot, mu_rot, hμ]) h1
  refine ⟨M, hM, fun j => ?_⟩
  have := hM' (j - r)
  simpa [rot] using this

/-- Pages 5–6, the bijection on affine classes: two closed quadrilaterals not contained in
a line have proportional ear areas exactly when one is the image of the other by an
invertible linear map. -/
theorem quad_moduli (u u' : Fin 4 → Fin 2 → k) (hu : Closed u) (hu' : Closed u')
    (hne : ∃ i, mu u i ≠ 0) :
    (∃ M : Matrix (Fin 2) (Fin 2) k, M.det ≠ 0 ∧ ∀ i, u' i = M *ᵥ u i) ↔
      ∃ c : k, c ≠ 0 ∧ ∀ i, mu u' i = c * mu u i := by
  constructor
  · rintro ⟨M, hM, hM'⟩
    refine ⟨M.det, hM, fun i => ?_⟩
    have : u' = fun j => M *ᵥ u j := funext hM'
    rw [this, mu_mulVec]
  · rintro ⟨c, hc, hμ⟩
    obtain ⟨M, hM, hM'⟩ := exists_matrix_of_mu u u' hu hu' c hc hμ hne
    exact ⟨M, hM ▸ hc, hM'⟩

/-- Surjectivity in the chart `m₁ ≠ 0`. -/
theorem exists_quad_of_mu_one (m : Fin 4 → k) (hrel : m 0 + m 2 = m 1 + m 3) (h1 : m 1 ≠ 0) :
    ∃ u : Fin 4 → Fin 2 → k, Closed u ∧ mu u = m := by
  let u0 : Fin 2 → k := ![m 1, 0]
  let u1 : Fin 2 → k := ![0, 1]
  let u2 : Fin 2 → k := ![-m 2, (m 3 - m 2) / m 1]
  refine ⟨![u0, u1, u2, -(u0 + u1 + u2)], ?_, ?_⟩
  · rw [closed_iff]; rfl
  · funext i
    fin_cases i
    · show wedge _ _ = _
      simp [wedge, u0, u1, u2]
      field_simp
      first | linear_combination hrel | linear_combination -hrel
    · show wedge _ _ = _
      simp [wedge, u0, u1]
    · show wedge _ _ = _
      simp [wedge, u1, u2]
    · show wedge _ _ = _
      simp [wedge, u0, u1, u2]
      field_simp
      ring

/-- Page 5, « épi ? »: every nonzero point of the plane `μ₀ + μ₂ = μ₁ + μ₃` is the
ear-area vector of a closed quadrilateral. -/
theorem exists_quad_of_mu (m : Fin 4 → k) (hrel : m 0 + m 2 = m 1 + m 3) (hm : m ≠ 0) :
    ∃ u : Fin 4 → Fin 2 → k, Closed u ∧ mu u = m := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h; push Not at h; exact hm (funext h)
  have hA : ∀ i : Fin 4, 1 + (i - 1) = i := by decide
  have hrot : ∀ r : Fin 4, m (0 + r) + m (2 + r) = m (1 + r) + m (3 + r) := by
    intro r
    fin_cases r <;> simp <;> first | linear_combination hrel | linear_combination -hrel
  set r : Fin 4 := i - 1
  have h1 : m (1 + r) ≠ 0 := by rw [show (1 : Fin 4) + r = i by simp only [r]; exact hA i]; exact hi
  have hrel' := hrot r
  obtain ⟨u, hu, hmu⟩ := exists_quad_of_mu_one (fun j => m (j + r)) hrel' h1
  refine ⟨rot (-r) u, closed_rot _ u hu, funext fun j => ?_⟩
  rw [mu_rot, hmu]
  simp

/-- A side is zero exactly when the two ears containing it are flat (page 5, boxed for
`u₂`), for a closed quadrilateral not contained in a line. -/
theorem side_eq_zero_iff (u : Fin 4 → Fin 2 → k) (hu : Closed u) (hne : ∃ j, mu u j ≠ 0)
    (i : Fin 4) : u i = 0 ↔ mu u i = 0 ∧ mu u (i + 1) = 0 := by
  constructor
  · intro h
    simp only [mu, h, add_sub_cancel_right]
    constructor <;> simp [wedge]
  · rintro ⟨h0, h1⟩
    by_contra hi
    obtain ⟨j, hj⟩ := hne
    have hA : ∀ i : Fin 4, 1 + (i - 1) = i := by decide
    have hB : ∀ i : Fin 4, 2 + (i - 1) = i + 1 := by decide
    -- rotate so that `i` becomes `1`
    set r : Fin 4 := i - 1
    set v := rot r u
    have hv : Closed v := closed_rot r u hu
    have hv1 : v 1 ≠ 0 := by
      simp only [v, rot]; rw [show (1 : Fin 4) + r = i by simp only [r]; exact hA i]; exact hi
    have e1 : wedge (v 0) (v 1) = 0 := by
      rw [← mu_one, mu_rot, show (1 : Fin 4) + r = i by simp only [r]; exact hA i]; exact h0
    have e2 : wedge (v 1) (v 2) = 0 := by
      rw [← mu_two, mu_rot, show (2 : Fin 4) + r = i + 1 by simp only [r]; exact hB i]; exact h1
    -- Plücker: `(v₀ ∧ v₁) v₂ + (v₁ ∧ v₂) v₀ + (v₂ ∧ v₀) v₁ = 0`
    have e02 : wedge (v 0) (v 2) = 0 := by
      have hc := cramer (v 0) (v 1) (v 2)
      rw [e1, wedge_swap (v 1) (v 2), e2, neg_zero, zero_smul, zero_smul, zero_add, eq_comm,
        smul_eq_zero] at hc
      rcases hc with hc | hc
      · exact hc
      · exact absurd hc hv1
    obtain ⟨d1, d2, -, -⟩ := wedge_diag v hv
    have hall : ∀ l, mu v l = 0 := by
      have m1 : mu v 1 = 0 := e1
      have m2 : mu v 2 = 0 := e2
      have m0 : mu v 0 = 0 := by linear_combination -d1 + e02 + m1
      have m3 : mu v 3 = 0 := by linear_combination -d2 + e02 + m2
      intro l; fin_cases l
      · exact m0
      · exact m1
      · exact m2
      · exact m3
    apply hj
    have := hall (j - r)
    rw [mu_rot] at this
    simpa using this

/-- The four degenerate quadrilaterals: `p_i` is the ear-area point of the quadrilateral
whose side `u_i` is a point. -/
def framePt : Fin 4 → Fin 4 → k :=
  ![![0, 0, 1, 1], ![1, 0, 0, 1], ![1, 1, 0, 0], ![0, 1, 1, 0]]

theorem framePt_mem (i : Fin 4) :
    framePt (k := k) i 0 + framePt i 2 = framePt i 1 + framePt i 3 := by
  fin_cases i <;> simp [framePt]

/-- A closed quadrilateral with `u_i = 0` has ear areas `μ = μ_{i+2} • p_i`, and
`μ_{i+2} ≠ 0` when it is not contained in a line. -/
theorem mu_eq_smul_framePt (u : Fin 4 → Fin 2 → k) (hu : Closed u) (i : Fin 4)
    (h : u i = 0) : mu u = mu u (i + 2) • framePt i := by
  have hrel := mu_relation u hu
  have z : ∀ a, wedge a (0 : Fin 2 → k) = 0 ∧ wedge 0 a = 0 := fun a => by
    simp [wedge]
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [framePt, mu_zero, mu_one, mu_two, mu_three] at h ⊢ <;>
    simp only [h, z, mu_zero, mu_one, mu_two, mu_three] at hrel ⊢ <;>
    first | linear_combination hrel | linear_combination -hrel

theorem mu_degenerate_ne_zero (u : Fin 4 → Fin 2 → k) (hu : Closed u) (i : Fin 4)
    (h : u i = 0) (hne : ∃ j, mu u j ≠ 0) : mu u (i + 2) ≠ 0 := by
  intro h0
  obtain ⟨j, hj⟩ := hne
  apply hj
  rw [mu_eq_smul_framePt u hu i h, h0, zero_smul, Pi.zero_apply]

/-- The only linear relation among the four degenerate points is the alternating one. -/
theorem sum_smul_framePt_eq_zero_iff (c : Fin 4 → k) :
    ∑ i, c i • framePt i = (0 : Fin 4 → k) ↔
      ∃ t : k, c = t • (![1, -1, 1, -1] : Fin 4 → k) := by
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3
    simp [Fin.sum_univ_four, framePt] at h0 h1 h2 h3
    refine ⟨c 0, funext fun i => ?_⟩
    fin_cases i <;> simp
    · linear_combination h3
    · linear_combination h0 - h3
    · linear_combination h2
  · rintro ⟨t, rfl⟩
    funext j; fin_cases j <;> simp [Fin.sum_univ_four, framePt]

/-- Any three of the degenerate points are linearly independent: with the alternating
relation, the four points form a projective frame of the plane. -/
theorem framePt_three_indep (c : Fin 4 → k) (h : ∑ i, c i • framePt i = (0 : Fin 4 → k))
    (i : Fin 4)
    (hi : c i = 0) : c = 0 := by
  obtain ⟨t, rfl⟩ := (sum_smul_framePt_eq_zero_iff c).1 h
  have ht : t = 0 := by
    fin_cases i <;> simpa using hi
  rw [ht, zero_smul]

/-- The plane `μ₀ + μ₂ = μ₁ + μ₃` of `k⁴`. -/
def plane : Submodule k (Fin 4 → k) where
  carrier := {m | m 0 + m 2 = m 1 + m 3}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply] at *; linear_combination ha + hb
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at *
    linear_combination c * ha

/-- The ear areas of a closed quadrilateral lie in `plane`. -/
theorem mu_mem_plane (u : Fin 4 → Fin 2 → k) (hu : Closed u) : mu u ∈ plane :=
  mu_relation u hu

/-- `e_i ↦ (-1)ⁱ p_i`. -/
def frameMap : (Fin 4 → k) →ₗ[k] (Fin 4 → k) where
  toFun c := ![-c 1 + c 2, c 2 - c 3, c 0 - c 3, c 0 - c 1]
  map_add' a b := by funext j; fin_cases j <;> simp <;> ring
  map_smul' t a := by funext j; fin_cases j <;> simp <;> ring

theorem frameMap_single (i : Fin 4) :
    frameMap (Pi.single i 1) = ((-1 : k) ^ (i : ℕ)) • framePt (k := k) i := by
  funext j; fin_cases i <;> fin_cases j <;> norm_num [frameMap, framePt]

theorem frameMap_ker : LinearMap.ker (frameMap (k := k)) = k ∙ (fun _ => (1 : k)) := by
  ext c
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    have h2 := congrFun h 2; have h3 := congrFun h 3
    simp [frameMap] at h0 h1 h2 h3
    refine ⟨c 0, funext fun i => ?_⟩
    fin_cases i <;> simp
    · linear_combination h3
    · linear_combination h3 - h0
    · linear_combination h2
  · rintro ⟨t, rfl⟩
    funext j; fin_cases j <;> simp [frameMap]

theorem frameMap_range : LinearMap.range (frameMap (k := k)) = plane := by
  ext m
  constructor
  · rintro ⟨c, rfl⟩
    show _ = _
    simp [frameMap]; ring
  · intro hm
    change m 0 + m 2 = m 1 + m 3 at hm
    refine ⟨![m 2, m 2 - m 3, m 2 - m 3 + m 0, m 2 - m 3 + m 0 - m 1], funext fun j => ?_⟩
    fin_cases j <;> simp [frameMap] <;> first | ring1 | linear_combination hm

/-- Page 6, the plane is canonically `P(k^A / k·(1,1,1,1))`: a linear isomorphism
`k⁴ / k·(1,1,1,1) ≃ plane` sending the class of the edge `i` to `(-1)ⁱ p_i`, whose line
is the point of the degenerate quadrilateral `u_i = 0`. -/
theorem frame_canonical :
    ∃ e : ((Fin 4 → k) ⧸ (k ∙ (fun _ => (1 : k)))) ≃ₗ[k] plane,
      ∀ i : Fin 4, (e (Submodule.Quotient.mk (Pi.single i 1))).1 =
        ((-1 : k) ^ (i : ℕ)) • framePt (k := k) i := by
  have hmem : ∀ c, frameMap (k := k) c ∈ plane := fun c => by
    rw [← frameMap_range]; exact LinearMap.mem_range_self _ c
  let f : (Fin 4 → k) →ₗ[k] plane := LinearMap.codRestrict plane frameMap hmem
  have hf : Function.Surjective f := by
    rintro ⟨m, hm⟩
    rw [← frameMap_range] at hm
    obtain ⟨c, hc⟩ := hm
    exact ⟨c, Subtype.ext hc⟩
  have hker : LinearMap.ker f = k ∙ (fun _ => (1 : k)) := by
    rw [LinearMap.ker_codRestrict, frameMap_ker]
  refine ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf),
    fun i => ?_⟩
  simp only [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  exact frameMap_single i

end QuadField

/-! ## The zero-multiplier criterion (pages 15, 18, 28) -/

section SymSquare

variable [Field k]

/-- The product `a·b` in the symmetric square `Sym² k²`, in the basis `X², XY, Y²`. -/
def symProd (a b : Fin 2 → k) : Fin 3 → k :=
  ![a 0 * b 0, a 0 * b 1 + a 1 * b 0, a 1 * b 1]

theorem symProd_apply0 (a b : Fin 2 → k) : symProd a b 0 = a 0 * b 0 := rfl
theorem symProd_apply1 (a b : Fin 2 → k) : symProd a b 1 = a 0 * b 1 + a 1 * b 0 := rfl
theorem symProd_apply2 (a b : Fin 2 → k) : symProd a b 2 = a 1 * b 1 := rfl

theorem symProd_comm (a b : Fin 2 → k) : symProd a b = symProd b a := by
  funext j; fin_cases j <;> simp [symProd] <;> ring

theorem symProd_add_right (a b c : Fin 2 → k) :
    symProd a (b + c) = symProd a b + symProd a c := by
  funext j; fin_cases j <;> simp [symProd] <;> ring

theorem symProd_sub_right (a b c : Fin 2 → k) :
    symProd a (b - c) = symProd a b - symProd a c := by
  funext j; fin_cases j <;> simp [symProd] <;> ring

theorem symProd_smul_right (a b : Fin 2 → k) (t : k) :
    symProd a (t • b) = t • symProd a b := by
  funext j; fin_cases j <;> simp [symProd] <;> ring

theorem symProd_smul_left (a b : Fin 2 → k) (t : k) :
    symProd (t • a) b = t • symProd a b := by
  rw [symProd_comm, symProd_smul_right, symProd_comm]

theorem symProd_zero_right (a : Fin 2 → k) : symProd a 0 = 0 := by
  funext j; fin_cases j <;> simp [symProd]

/-- `Sym² k²` has no zero divisors among products of vectors. -/
theorem symProd_eq_zero_iff (a b : Fin 2 → k) : symProd a b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    rw [symProd_apply0, Pi.zero_apply] at h0
    rw [symProd_apply1, Pi.zero_apply] at h1
    rw [symProd_apply2, Pi.zero_apply] at h2
    by_cases ha0 : a 0 = 0
    · rw [ha0, zero_mul, zero_add] at h1
      by_cases ha1 : a 1 = 0
      · left; funext j; fin_cases j
        · exact ha0
        · exact ha1
      · right; funext j; fin_cases j
        · exact (mul_eq_zero.1 h1).resolve_left ha1
        · exact (mul_eq_zero.1 h2).resolve_left ha1
    · right
      have hb0 : b 0 = 0 := (mul_eq_zero.1 h0).resolve_left ha0
      rw [hb0, mul_zero, add_zero] at h1
      funext j; fin_cases j
      · exact hb0
      · exact (mul_eq_zero.1 h1).resolve_left ha0
  · rintro (rfl | rfl) <;> funext j <;> fin_cases j <;> simp [symProd]

/-- An element of `Sym² k²` as a quadratic form, evaluated at `x`. -/
def qeval (s : Fin 3 → k) (x : Fin 2 → k) : k :=
  s 0 * x 0 ^ 2 + s 1 * (x 0 * x 1) + s 2 * x 1 ^ 2

theorem qeval_smul (t : k) (s : Fin 3 → k) (x : Fin 2 → k) :
    qeval (t • s) x = t * qeval s x := by
  simp [qeval]; ring

/-- `a·b` evaluated at the vector `x = (c₁, -c₀)` orthogonal to `c` is `(a ∧ c)(b ∧ c)`. -/
theorem qeval_symProd_perp (a b c : Fin 2 → k) :
    qeval (symProd a b) ![c 1, -c 0] = wedge a c * wedge b c := by
  simp [qeval, symProd, wedge]; ring

theorem wedge_eq_zero_comm (a b : Fin 2 → k) : wedge a b = 0 ↔ wedge b a = 0 := by
  rw [wedge_swap, neg_eq_zero]

theorem exists_smul_of_wedge {a c : Fin 2 → k} (ha : a ≠ 0) (h : wedge a c = 0) :
    ∃ α : k, c = α • a := by
  unfold wedge at h
  by_cases h0 : a 0 = 0
  · have h1 : a 1 ≠ 0 := by
      intro h1; apply ha; funext j; fin_cases j
      · exact h0
      · exact h1
    rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
    refine ⟨c 1 / a 1, funext fun j => ?_⟩
    fin_cases j
    · simp [h0]; exact (mul_eq_zero.1 h).resolve_left h1
    · simp; field_simp
  · refine ⟨c 0 / a 0, funext fun j => ?_⟩
    fin_cases j
    · simp; field_simp
    · simp; field_simp; linear_combination h

/-- Page 28, the « pair of directions »: for nonzero vectors of a plane, `c·d` is a
multiple of `a·b` in `Sym² k²` if and only if `{[a], [b]} = {[c], [d]}` as pairs of lines. -/
theorem symProd_proportional_iff {a b c d : Fin 2 → k} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    (∃ t : k, symProd c d = t • symProd a b) ↔
      (wedge a c = 0 ∧ wedge b d = 0) ∨ (wedge a d = 0 ∧ wedge b c = 0) := by
  constructor
  · rintro ⟨t, h⟩
    have ht : t ≠ 0 := by
      rintro rfl
      rw [zero_smul, symProd_eq_zero_iff] at h
      exact h.elim hc hd
    have E : ∀ x, qeval (symProd c d) x = t * qeval (symProd a b) x := fun x => by
      rw [h, qeval_smul]
    have A := E ![a 1, -a 0]
    have C := E ![c 1, -c 0]
    have B := E ![b 1, -b 0]
    have D := E ![d 1, -d 0]
    simp only [qeval_symProd_perp, wedge_self, zero_mul, mul_zero, mul_eq_zero,
      zero_eq_mul] at A B C D
    rw [wedge_eq_zero_comm c a, wedge_eq_zero_comm d a] at A
    rw [wedge_eq_zero_comm c b, wedge_eq_zero_comm d b] at B
    rcases C with C | C | C
    · exact absurd C ht
    · -- `a ∧ c = 0`
      by_cases hbd : wedge b d = 0
      · exact Or.inl ⟨C, hbd⟩
      · rcases D with D | D | D
        · exact absurd D ht
        · rcases B with B | B
          · exact Or.inr ⟨D, B⟩
          · exact absurd B hbd
        · exact absurd D hbd
    · -- `b ∧ c = 0`
      rcases A with A | A
      · by_cases hbd : wedge b d = 0
        · exact Or.inl ⟨A, hbd⟩
        · rcases D with D | D | D
          · exact absurd D ht
          · exact Or.inr ⟨D, C⟩
          · exact absurd D hbd
      · exact Or.inr ⟨A, C⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · obtain ⟨α, rfl⟩ := exists_smul_of_wedge ha h1
      obtain ⟨β, rfl⟩ := exists_smul_of_wedge hb h2
      exact ⟨α * β, by rw [symProd_smul_left, symProd_smul_right, smul_smul, mul_comm]⟩
    · obtain ⟨α, rfl⟩ := exists_smul_of_wedge ha h1
      obtain ⟨β, rfl⟩ := exists_smul_of_wedge hb h2
      exact ⟨α * β, by rw [symProd_smul_left, symProd_smul_right, smul_smul, symProd_comm b a, mul_comm]⟩

end SymSquare

section Polygon

variable [Field k] {n : ℕ} [NeZero n]

/-- The multipliers of an `n`-gon given by its sides (page 25, the relation `(∗)`):
`λ_i u_{i-1} - λ_{i+1}(u_i + u_{i+1}) + λ_{i+2} u_{i+2} = 0` for all `i`. -/
def IsMult (u : ZMod n → Fin 2 → k) (l : ZMod n → k) : Prop :=
  ∀ i, l i • u (i - 1) - l (i + 1) • (u i + u (i + 1)) + l (i + 2) • u (i + 2) = 0

/-- `u_{0m} = u_0 + ⋯ + u_{m-1} = s_m - s_0`. -/
def partialSum (u : ZMod n → Fin 2 → k) (m : ℕ) : Fin 2 → k :=
  ∑ j ∈ Finset.range m, u j

/-- The Lagrange form `(L)`: `L_i = λ_i u_{i-1} - λ_{i+1} u_{i+1}`. -/
def lagr (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (i : ZMod n) : Fin 2 → k :=
  l i • u (i - 1) - l (i + 1) • u (i + 1)

omit [NeZero n] in
theorem isMult_iff_lagr (u : ZMod n → Fin 2 → k) (l : ZMod n → k) :
    IsMult u l ↔ ∀ i, lagr u l i = lagr u l (i + 1) := by
  have key : ∀ i, lagr u l i - lagr u l (i + 1) =
      l i • u (i - 1) - l (i + 1) • (u i + u (i + 1)) + l (i + 2) • u (i + 2) := by
    intro i
    simp only [lagr, add_sub_cancel_right, add_assoc, one_add_one_eq_two, smul_add]
    abel
  simp only [IsMult, ← key, sub_eq_zero]

theorem sum_range_eq_sum (f : ZMod n → Fin 2 → k) :
    ∑ j ∈ Finset.range n, f j = ∑ i, f i := by
  refine Finset.sum_nbij' (fun j => (j : ZMod n)) (fun i => i.val) ?_ ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_univ _
  · intro i _; exact Finset.mem_range.2 (ZMod.val_lt i)
  · intro j hj; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hj)
  · intro i _; exact ZMod.natCast_zmod_val i
  · intro j _; rfl

/-- With `λ₀ = 0` and `λ₁ = 1`, `(∗)` says `L_i = -u₁` for every `i`. -/
theorem isMult_iff_lagr_eq (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (h0 : l 0 = 0)
    (h1 : l 1 = 1) : IsMult u l ↔ ∀ i, lagr u l i = -u 1 := by
  have hL0 : lagr u l 0 = -u 1 := by simp [lagr, h0, h1]
  rw [isMult_iff_lagr]
  constructor
  · intro h i
    have : ∀ m : ℕ, lagr u l (m : ZMod n) = lagr u l 0 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Nat.cast_succ, ← h, ih]
    rw [← ZMod.natCast_zmod_val i, this, hL0]
  · intro h i; rw [h, h]

/-- The identity `(S_{m+1})`: `λ_{m+1} u_m·u_{m+1} = u_1·u_{0,m+1}` in `Sym² V`. -/
def SymId (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (m : ℕ) : Prop :=
  l ((m + 1 : ℕ) : ZMod n) • symProd (u m) (u ((m + 1 : ℕ) : ZMod n)) =
    symProd (u 1) (partialSum u (m + 1))

omit [NeZero n] in
private theorem alg_fwd (A B : k) (x y z u1 P : Fin 2 → k) (hL : A • x - B • z = -u1)
    (hS : A • symProd x y = symProd u1 P) : B • symProd y z = symProd u1 (P + y) := by
  have hz : B • z = A • x + u1 := by
    rw [show B • z = A • x - (A • x - B • z) by abel, hL, sub_neg_eq_add]
  rw [← symProd_smul_right, hz, symProd_add_right, symProd_smul_right, symProd_comm y x, hS,
    symProd_comm y u1, symProd_add_right]

omit [NeZero n] in
private theorem alg_bwd (A B : k) (x y z u1 P : Fin 2 → k) (hy : y ≠ 0)
    (hS : A • symProd x y = symProd u1 P) (hS' : B • symProd y z = symProd u1 (P + y)) :
    A • x - B • z = -u1 := by
  have : symProd y (A • x - B • z + u1) = 0 := by
    rw [symProd_add_right, symProd_sub_right, symProd_smul_right, symProd_smul_right,
      symProd_comm y x, hS, hS', symProd_comm y u1, symProd_add_right]
    abel
  rw [symProd_eq_zero_iff] at this
  exact eq_neg_of_add_eq_zero_left (this.resolve_left hy)

omit [NeZero n] in
private theorem lagr_succ (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (m : ℕ) :
    lagr u l ((m + 1 : ℕ) : ZMod n) =
      l ((m + 1 : ℕ) : ZMod n) • u m - l ((m + 2 : ℕ) : ZMod n) • u ((m + 2 : ℕ) : ZMod n) := by
  simp only [lagr]
  push_cast
  rw [add_sub_cancel_right, add_assoc, one_add_one_eq_two]

omit [NeZero n] in
private theorem partialSum_succ (u : ZMod n → Fin 2 → k) (m : ℕ) :
    partialSum u (m + 1) = partialSum u m + u m := Finset.sum_range_succ _ _

omit [NeZero n] in
theorem symId_zero (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (h1 : l 1 = 1) :
    SymId u l 0 := by
  simp [SymId, partialSum, h1, symProd_comm]

omit [NeZero n] in
/-- `(L)` at `m + 1` carries `(S_{m+1})` to `(S_{m+2})` (page 28, the edition's proof). -/
theorem symId_succ (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (m : ℕ)
    (hL : lagr u l ((m + 1 : ℕ) : ZMod n) = -u 1) (hS : SymId u l m) : SymId u l (m + 1) := by
  rw [lagr_succ] at hL
  unfold SymId at *
  rw [partialSum_succ u (m + 1)]
  exact alg_fwd _ _ _ _ _ _ _ hL hS

/-- A multiplier with `λ₀ = 0`, `λ₁ = 1` satisfies `(S_i)` for every `i ≥ 1`. -/
theorem symId_of_isMult (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (h0 : l 0 = 0)
    (h1 : l 1 = 1) (h : IsMult u l) (m : ℕ) : SymId u l m := by
  rw [isMult_iff_lagr_eq u l h0 h1] at h
  induction m with
  | zero => exact symId_zero u l h1
  | succ m ih => exact symId_succ u l m (h _) ih

/-- Conversely, `(S_i)` for every `i ≥ 1` gives `(∗)`, the sides being nonzero. -/
theorem isMult_of_symId (u : ZMod n → Fin 2 → k) (hu : ∀ i, u i ≠ 0) (l : ZMod n → k)
    (h0 : l 0 = 0) (h1 : l 1 = 1) (hS : ∀ m, SymId u l m) : IsMult u l := by
  rw [isMult_iff_lagr_eq u l h0 h1]
  intro i
  have hn : 1 ≤ n := NeZero.one_le
  set m := i.val + (n - 1)
  have hi : ((m + 1 : ℕ) : ZMod n) = i := by
    rw [show m + 1 = i.val + n by omega]
    push_cast
    rw [ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]
  rw [← hi, lagr_succ]
  have h2 := hS (m + 1)
  unfold SymId at h2
  rw [partialSum_succ u (m + 1)] at h2
  exact alg_bwd _ _ _ _ _ _ _ (hu _) (hS m) h2

omit [NeZero n] in
private theorem cast_n_add (j : ℕ) : ((n + j : ℕ) : ZMod n) = j := by
  push_cast; rw [ZMod.natCast_self, zero_add]

omit [NeZero n] in
private theorem partialSum_n_add (u : ZMod n → Fin 2 → k) (j : ℕ) :
    partialSum u (n + j) = partialSum u n + partialSum u j := by
  unfold partialSum
  rw [Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [cast_n_add]

omit [NeZero n] in
/-- For a closed polygon, `(S_i)` is periodic in `i`. -/
theorem symId_n_add (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (hcl : partialSum u n = 0)
    (m : ℕ) : SymId u l (n + m) ↔ SymId u l m := by
  unfold SymId
  rw [show n + m + 1 = n + (m + 1) by ring, cast_n_add, cast_n_add, partialSum_n_add, hcl,
    zero_add]

/-- **Page 28, the criterion of the special case II.** An `n`-gon with nonzero sides has a
multiplier with `λ₀ = 0` and `λ₁ = 1` if and only if it is closed and, for
`2 ≤ i ≤ n - 1`, either `s_i = s_0` or the pair of directions of `{u_{i-1}, u_i}` is that
of `{u_1, u_{0i}}`. -/
theorem zero_multiplier_criterion (hn : 3 ≤ n) (u : ZMod n → Fin 2 → k)
    (hu : ∀ i, u i ≠ 0) :
    (∃ l : ZMod n → k, l 0 = 0 ∧ l 1 = 1 ∧ IsMult u l) ↔
      (∑ i, u i = 0 ∧ ∀ i : ℕ, 2 ≤ i → i ≤ n - 1 →
        partialSum u i = 0 ∨
          ((wedge (u (i - 1 : ℕ)) (u 1) = 0 ∧ wedge (u i) (partialSum u i) = 0) ∨
            (wedge (u (i - 1 : ℕ)) (partialSum u i) = 0 ∧ wedge (u i) (u 1) = 0))) := by
  rw [← sum_range_eq_sum]
  constructor
  · rintro ⟨l, h0, h1, h⟩
    have hS := symId_of_isMult u l h0 h1 h
    refine ⟨?_, fun i hi2 hin => ?_⟩
    · have := hS (n - 1)
      unfold SymId at this
      rw [show n - 1 + 1 = n by omega, ZMod.natCast_self, h0, zero_smul, eq_comm,
        symProd_eq_zero_iff] at this
      exact this.resolve_left (hu 1)
    · by_cases hP : partialSum u i = 0
      · exact Or.inl hP
      · right
        have := hS (i - 1)
        unfold SymId at this
        rw [show i - 1 + 1 = i by omega] at this
        exact (symProd_proportional_iff (hu _) (hu _) (hu 1) hP).1 ⟨_, this.symm⟩
  · rintro ⟨hcl, hcond⟩
    have hex : ∀ i : ℕ, ∃ t : k, 2 ≤ i → i ≤ n - 1 →
        symProd (u 1) (partialSum u i) = t • symProd (u (i - 1 : ℕ)) (u i) := by
      intro i
      by_cases hi : 2 ≤ i ∧ i ≤ n - 1
      · rcases hcond i hi.1 hi.2 with hP | hpair
        · exact ⟨0, fun _ _ => by rw [hP, symProd_zero_right, zero_smul]⟩
        · by_cases hP : partialSum u i = 0
          · exact ⟨0, fun _ _ => by rw [hP, symProd_zero_right, zero_smul]⟩
          · obtain ⟨t, ht⟩ := (symProd_proportional_iff (hu _) (hu _) (hu 1) hP).2 hpair
            exact ⟨t, fun _ _ => ht⟩
      · exact ⟨0, fun h2 h3 => absurd ⟨h2, h3⟩ hi⟩
    choose f hf using hex
    let l : ZMod n → k := fun j => if j.val = 0 then 0 else if j.val = 1 then 1 else f j.val
    have hval1 : (1 : ZMod n).val = 1 := by
      rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
    have h0 : l 0 = 0 := by simp [l]
    have h1 : l 1 = 1 := by simp only [l, hval1]; norm_num
    have hcl' : partialSum u n = 0 := hcl
    refine ⟨l, h0, h1, isMult_of_symId u hu l h0 h1 ?_⟩
    have hlt : ∀ m, m < n → SymId u l m := by
      intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · exact symId_zero u l h1
      · by_cases hmn : m + 1 = n
        · unfold SymId
          rw [hmn, ZMod.natCast_self, h0, zero_smul, hcl', symProd_zero_right]
        · have hv : ((m + 1 : ℕ) : ZMod n).val = m + 1 := ZMod.val_cast_of_lt (by omega)
          have hl : l ((m + 1 : ℕ) : ZMod n) = f (m + 1) := by
            simp only [l, hv]
            rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
              ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
          have e := hf (m + 1) (by omega) (by omega)
          rw [Nat.add_sub_cancel] at e
          unfold SymId
          rw [hl, ← e]
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases hm : m < n
      · exact hlt m hm
      · obtain ⟨j, rfl⟩ : ∃ j, m = n + j := ⟨m - n, by omega⟩
        exact (symId_n_add u l hcl' j).2 (ih j (by omega))

/-- The multiplier is given by `λ_i u_{i-1}·u_i = u_1·u_{0i}` in `Sym² V`, for every
`i ≥ 1` (the page's « on aura λ_i défini par u_1 u_{0i} = λ_i u_i u_{i-1} »). -/
theorem symProd_formula (u : ZMod n → Fin 2 → k) (l : ZMod n → k) (h0 : l 0 = 0)
    (h1 : l 1 = 1) (h : IsMult u l) (i : ℕ) (hi : 1 ≤ i) :
    l i • symProd (u (i - 1 : ℕ)) (u i) = symProd (u 1) (partialSum u i) := by
  have := symId_of_isMult u l h0 h1 h (i - 1)
  unfold SymId at this
  rwa [show i - 1 + 1 = i by omega] at this

/-- Page 28: `λ_i = 0` exactly at the vertices `s_i = s_0` (`u_{0i} = 0`). -/
theorem mult_eq_zero_iff (u : ZMod n → Fin 2 → k) (hu : ∀ i, u i ≠ 0) (l : ZMod n → k)
    (h0 : l 0 = 0) (h1 : l 1 = 1) (h : IsMult u l) (i : ℕ) (hi : 1 ≤ i) :
    l i = 0 ↔ partialSum u i = 0 := by
  have hf := symProd_formula u l h0 h1 h i hi
  constructor
  · intro hl
    rw [hl, zero_smul, eq_comm, symProd_eq_zero_iff] at hf
    exact hf.resolve_left (hu 1)
  · intro hP
    rw [hP, symProd_zero_right, smul_eq_zero, symProd_eq_zero_iff] at hf
    rcases hf with hf | hf | hf
    · exact hf
    · exact absurd hf (hu _)
    · exact absurd hf (hu _)

/-- The multiplier with `λ₀ = 0`, `λ₁ = 1` is unique. -/
theorem mult_unique (u : ZMod n → Fin 2 → k) (hu : ∀ i, u i ≠ 0) (l l' : ZMod n → k)
    (h0 : l 0 = 0) (h1 : l 1 = 1) (h : IsMult u l) (h0' : l' 0 = 0) (h1' : l' 1 = 1)
    (h' : IsMult u l') : l = l' := by
  funext j
  have hn : 1 ≤ n := NeZero.one_le
  have hj : ((j.val + n : ℕ) : ZMod n) = j := by
    push_cast; rw [ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]
  have e := symProd_formula u l h0 h1 h (j.val + n) (by omega)
  have e' := symProd_formula u l' h0' h1' h' (j.val + n) (by omega)
  rw [← e'] at e
  have hne : symProd (u ((j.val + n - 1 : ℕ) : ZMod n)) (u ((j.val + n : ℕ) : ZMod n)) ≠ 0 := by
    rw [Ne, symProd_eq_zero_iff, not_or]; exact ⟨hu _, hu _⟩
  have := smul_left_injective k hne e
  rwa [hj] at this

/-- Two consecutive zero components force a multiplier to vanish: hence the normalisation
`λ₁ = 1` once `λ₀ = 0`. -/
theorem eq_zero_of_consecutive (u : ZMod n → Fin 2 → k) (hu : ∀ i, u i ≠ 0)
    (l : ZMod n → k) (h : IsMult u l) (i : ZMod n) (h0 : l i = 0) (h1 : l (i + 1) = 0) :
    l = 0 := by
  have step : ∀ m : ℕ, l (i + m) = 0 ∧ l (i + m + 1) = 0 := by
    intro m
    induction m with
    | zero => simpa using ⟨h0, h1⟩
    | succ m ih =>
      have e := h (i + m)
      rw [ih.1, ih.2, zero_smul, zero_smul, sub_zero, zero_add, smul_eq_zero] at e
      have e2 : l (i + m + 2) = 0 := e.resolve_right (hu _)
      push_cast
      refine ⟨by rw [← add_assoc]; exact ih.2, ?_⟩
      rw [← add_assoc, add_assoc (i + m), one_add_one_eq_two]; exact e2
  funext j
  have := (step (j - i).val).1
  rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this

end Polygon

end Folder73
