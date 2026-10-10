import Mathlib

/-!
# Folder 77, pages 65–71 and 87: the universal discriminant mod 2 and mod 4

The modernised reading `transcripts/77/77.modern.tex` (« Discriminant des formes
quadratiques », pages 64 to 87) takes the universal quadratic form
`Σ Yᵢ xᵢ² + Σ_{i<j} Yᵢⱼ xᵢ xⱼ` over `ℤ[Y]`, whose polar matrix has `2Yᵢ` on the
diagonal and `Yᵢⱼ` off it, and its determinant `Δ`. It states:

> **Page 68.** `Δ ≡ 0 (mod 2)` if `card I` is odd, so that the half-discriminant
> `δ' = δ/2` is defined over any base in odd rank.
>
> **Pages 68–71.** In even rank `2n`, with `B` the sum over the perfect matchings
> of `I` of the products of the `Yᵢⱼ` (the hafnian of the off-diagonal
> coefficients), `(-1)ⁿ Δ = B² - 4C` for some `C ∈ ℤ[Y]`.

These are findings `77-odd-rank-half-discriminant` and
`77-universal-even-rank-discriminant-mod-4` of `src/content/findings.ts`.
Proving them says only that the claims hold as stated; whether they stand in the
literature is a separate question.

What is formalised.

* Odd rank, every odd `n` (`two_dvd_det_polar`): the variables are indexed by
  `Sym2 (Fin n)`, `s(i, i)` for `Yᵢ` and `s(i, j)` for `Yᵢⱼ`. The proof does not
  follow the graph expansion of the page: modulo `2` the polar matrix agrees with
  the skew-symmetric matrix `K` (`Yᵢⱼ` above the diagonal, `-Yᵢⱼ` below, `0` on
  it), and `det K = 0` over `ℤ[Y]` in odd size since `det Kᵀ = det (-K) = -det K`
  and `ℤ[Y]` has no `2`-torsion. The quotient `halfDisc n` is unique, and its
  value at the coefficients of a form over any commutative ring halves the
  determinant there (`det_polarOf_eq`).
* Even rank, ranks `2` and `4` (`disc_rank_two`, `disc_rank_four`): the identity
  `(-1)ⁿ Δ = B² - 4C` over any commutative ring, with `C` written out. In rank 2
  it is `-Δ = b² - 4ac`. The sign `-(-1)ⁿ` fails in both ranks
  (`not_dvd_rank_two`, `not_dvd_rank_four`).
* Even rank, every `n` (`four_dvd_disc_sub_hafnian_sq`, `disc_even_rank`): `4` divides
  `(-1)ⁿ Δ - B²` in `ℤ[Y]`, `B` the hafnian (`hafnian`). No Pfaffian is used. With `U`
  the upper half of the polar matrix, `P = U + Uᵀ` and the skew matrix is
  `K = U - Uᵀ = P - 2Uᵀ`; the first-order term of `det (P - t Uᵀ)`, computed in the
  fraction field, gives `det K ≡ (1 - 2n) det P (mod 4)` (`det_skew_eq_first_order`).
  Next `det K = r²` in `ℤ[Y]` (`det_skew_eq_sq`): over a field of characteristic `≠ 2` an
  antisymmetric matrix of even size has a square determinant (Schur complement on a
  `2 × 2` block), and `ℤ[Y]` is integrally closed. Modulo `2`, the determinant of a
  symmetric matrix with zero diagonal is the square of its matching sum
  (`det_eq_hafSum_sq`), so `r ≡ B (mod 2)` and `det K ≡ B² (mod 4)`. Finally
  `(-1)ⁿ ≡ 1 - 2n (mod 4)`.

# Folder 77, pages 117–125: the canonical symmetry of a biregular affine quadric

The reading (§ 1'' and § 2) attaches to `(T, q, a)`, `q(a) = 1`, `π = φ(a, ·)`, the map
`σ = id - π ⊗ a` and states (marginal Proposition, p. 123) that it is the only reflection
fixing the hyperplane at infinity and preserving the quadric; it is a symmetry of centre
`a/2` if `2` is invertible and a transvection in characteristic `2` (finding
`77-biregular-affine-quadric-symmetry`). Formalised over any commutative ring:
`piForm_self` (`π(a) = 2`), `canSym_isometry`, `canSym_canSym` (`σ² = id`),
`eq_of_isometry_fix` (with `φ` nondegenerate and `π` onto, a linear isometry fixing `ker π`
pointwise is `x ↦ x - e π(x) a` with `e` idempotent; conversely `isometry_of_idem`),
`eq_id_or_canSym` (no nontrivial idempotent: `id` or `σ`), `canSym_center` (`2`
invertible), `canSym_char_two` (`2 = 0`), and `det_polar_one` (the example `M₂`, `det`, `1`
of p. 124, where `π` is the trace).
-/

namespace Grothendieck.Folder77

open MvPolynomial Matrix

/-! ## Odd rank: the determinant is even -/

/-- The polar matrix of the universal quadratic form of rank `n`: `2 Yᵢ` on the
diagonal, `Yᵢⱼ` off it, the variable `Y_J` being indexed by `J = s(i, j)`
(page 65). -/
noncomputable def polar (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Sym2 (Fin n)) ℤ) :=
  fun i j => if i = j then 2 * X s(i, i) else X s(i, j)

/-- The skew-symmetric matrix that agrees with `polar n` modulo `2`. -/
noncomputable def skew (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Sym2 (Fin n)) ℤ) :=
  fun i j => if i < j then X s(i, j) else if j < i then -X s(i, j) else 0

theorem skew_transpose (n : ℕ) : (skew n)ᵀ = -skew n := by
  refine Matrix.ext fun i j => ?_
  show skew n j i = -skew n i j
  simp only [skew]
  rw [Sym2.eq_swap (a := j) (b := i)]
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [if_pos h, if_neg (not_lt_of_gt h)]
  · simp
  · simp only [if_pos h, if_neg (not_lt_of_gt h), neg_neg]

theorem det_skew_of_odd {n : ℕ} (hn : Odd n) : (skew n).det = 0 := by
  have h := det_transpose (skew n)
  rw [skew_transpose, det_neg, Fintype.card_fin, hn.neg_one_pow, neg_one_mul,
    neg_eq_iff_add_eq_zero, ← two_mul] at h
  exact (mul_eq_zero.mp h).resolve_left two_ne_zero

/-- Reduction of the coefficients modulo `2`. -/
noncomputable abbrev red (n : ℕ) :
    MvPolynomial (Sym2 (Fin n)) ℤ →+* MvPolynomial (Sym2 (Fin n)) (ZMod 2) :=
  MvPolynomial.map (Int.castRingHom (ZMod 2))

theorem polar_map_red (n : ℕ) : (polar n).map (red n) = (skew n).map (red n) := by
  refine Matrix.ext fun i j => ?_
  simp only [map_apply, polar, skew]
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [if_neg h.ne, if_pos h]
  · rw [if_pos rfl, if_neg (lt_irrefl i), if_neg (lt_irrefl i)]
    simp only [map_mul, map_zero, map_ofNat,
      CharTwo.two_eq_zero (R := MvPolynomial (Sym2 (Fin n)) (ZMod 2)), zero_mul]
  · simp only [if_neg h.ne', if_neg (not_lt_of_gt h), if_pos h, map_neg]
    exact (CharTwo.neg_eq (R := MvPolynomial (Sym2 (Fin n)) (ZMod 2)) _).symm

/-- An integer polynomial whose reduction modulo `2` vanishes is divisible by `2`. -/
theorem two_dvd_of_red_eq_zero {n : ℕ} {p : MvPolynomial (Sym2 (Fin n)) ℤ}
    (hp : red n p = 0) : (2 : MvPolynomial (Sym2 (Fin n)) ℤ) ∣ p := by
  have : p ∈ RingHom.ker (red n) := hp
  rw [MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at this
  simpa using this

/-- **Page 68.** In odd rank the universal discriminant is divisible by `2`
in `ℤ[Y]`. -/
theorem two_dvd_det_polar {n : ℕ} (hn : Odd n) :
    (2 : MvPolynomial (Sym2 (Fin n)) ℤ) ∣ (polar n).det := by
  apply two_dvd_of_red_eq_zero
  rw [RingHom.map_det, RingHom.mapMatrix_apply, polar_map_red, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, det_skew_of_odd hn, map_zero]

/-- The universal half-discriminant `δ' = Δ / 2` in odd rank. -/
noncomputable def halfDisc {n : ℕ} (hn : Odd n) : MvPolynomial (Sym2 (Fin n)) ℤ :=
  (two_dvd_det_polar hn).choose

theorem det_polar_eq {n : ℕ} (hn : Odd n) : (polar n).det = 2 * halfDisc hn :=
  (two_dvd_det_polar hn).choose_spec

/-- The half-discriminant is the only polynomial with `Δ = 2 δ'`. -/
theorem halfDisc_unique {n : ℕ} (hn : Odd n) {d : MvPolynomial (Sym2 (Fin n)) ℤ}
    (hd : (polar n).det = 2 * d) : d = halfDisc hn := by
  rw [det_polar_eq hn] at hd
  exact (mul_left_cancel₀ two_ne_zero hd).symm

/-- The polar matrix of the quadratic form `Σ yᵢ xᵢ² + Σ_{i<j} yᵢⱼ xᵢ xⱼ` over a
commutative ring `R`. -/
def polarOf {R : Type*} [CommRing R] {n : ℕ} (y : Sym2 (Fin n) → R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if i = j then 2 * y s(i, i) else y s(i, j)

/-- Over any commutative ring, in odd rank, the determinant of the polar form is
twice the value of the universal half-discriminant: `δ'` is defined over any
base. -/
theorem det_polarOf_eq {R : Type*} [CommRing R] {n : ℕ} (hn : Odd n)
    (y : Sym2 (Fin n) → R) : (polarOf y).det = 2 * aeval y (halfDisc hn) := by
  have h : (polar n).map (aeval y) = polarOf y := by
    ext i j
    simp only [map_apply, polar, polarOf]
    split_ifs <;> simp
  have := AlgHom.map_det (aeval (R := ℤ) y) (polar n)
  rw [det_polar_eq hn, map_mul, map_ofNat] at this
  rw [← h]
  exact this.symm

/-! ## Even rank: `(-1)ⁿ Δ = B² - 4C` in ranks 2 and 4 -/

/-- **Rank 2.** `-Δ = b² - 4ac`; here `B = b` and `C = ac`. -/
theorem disc_rank_two {R : Type*} [CommRing R] (a₁ a₂ b₁₂ : R) :
    -(!![2 * a₁, b₁₂; b₁₂, 2 * a₂]).det = b₁₂ ^ 2 - 4 * (a₁ * a₂) := by
  rw [det_fin_two_of]; ring

/-- The polar matrix of the quadratic form of rank `4`. -/
def polar4 {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ b₁₂ b₁₃ b₁₄ b₂₃ b₂₄ b₃₄ : R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![2 * a₁, b₁₂, b₁₃, b₁₄;
     b₁₂, 2 * a₂, b₂₃, b₂₄;
     b₁₃, b₂₃, 2 * a₃, b₃₄;
     b₁₄, b₂₄, b₃₄, 2 * a₄]

theorem det_polar4 {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ b₁₂ b₁₃ b₁₄ b₂₃ b₂₄ b₃₄ : R) :
    (polar4 a₁ a₂ a₃ a₄ b₁₂ b₁₃ b₁₄ b₂₃ b₂₄ b₃₄).det =
      16 * a₁ * a₂ * a₃ * a₄
      - 4 * (a₁ * a₂ * b₃₄ ^ 2 + a₁ * a₃ * b₂₄ ^ 2 + a₁ * a₄ * b₂₃ ^ 2
        + a₂ * a₃ * b₁₄ ^ 2 + a₂ * a₄ * b₁₃ ^ 2 + a₃ * a₄ * b₁₂ ^ 2)
      + 4 * (a₁ * b₂₃ * b₂₄ * b₃₄ + a₂ * b₁₃ * b₁₄ * b₃₄ + a₃ * b₁₂ * b₁₄ * b₂₄
        + a₄ * b₁₂ * b₁₃ * b₂₃)
      + b₁₂ ^ 2 * b₃₄ ^ 2 + b₁₃ ^ 2 * b₂₄ ^ 2 + b₁₄ ^ 2 * b₂₃ ^ 2
      - 2 * (b₁₂ * b₁₃ * b₂₄ * b₃₄ + b₁₂ * b₁₄ * b₂₃ * b₃₄ + b₁₃ * b₁₄ * b₂₃ * b₂₄) := by
  rw [polar4, det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_fin_three, Fin.succAbove]
  ring

/-- **Rank 4.** `Δ = B² - 4C`, with `B = b₁₂b₃₄ + b₁₃b₂₄ + b₁₄b₂₃` the sum over the
three perfect matchings of `{1, 2, 3, 4}`. -/
theorem disc_rank_four {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ b₁₂ b₁₃ b₁₄ b₂₃ b₂₄ b₃₄ : R) :
    (polar4 a₁ a₂ a₃ a₄ b₁₂ b₁₃ b₁₄ b₂₃ b₂₄ b₃₄).det =
      (b₁₂ * b₃₄ + b₁₃ * b₂₄ + b₁₄ * b₂₃) ^ 2
      - 4 * (-4 * a₁ * a₂ * a₃ * a₄
        + a₁ * a₂ * b₃₄ ^ 2 + a₁ * a₃ * b₂₄ ^ 2 + a₁ * a₄ * b₂₃ ^ 2
        + a₂ * a₃ * b₁₄ ^ 2 + a₂ * a₄ * b₁₃ ^ 2 + a₃ * a₄ * b₁₂ ^ 2
        - (a₁ * b₂₃ * b₂₄ * b₃₄ + a₂ * b₁₃ * b₁₄ * b₃₄ + a₃ * b₁₂ * b₁₄ * b₂₄
          + a₄ * b₁₂ * b₁₃ * b₂₃)
        + b₁₂ * b₁₃ * b₂₄ * b₃₄ + b₁₂ * b₁₄ * b₂₃ * b₃₄ + b₁₃ * b₁₄ * b₂₃ * b₂₄) := by
  rw [det_polar4]; ring

/-- The other sign fails in rank 2: at `a = c = 0`, `b = 1`, `B² - Δ = 2` is not
divisible by `4`. -/
theorem not_dvd_rank_two :
    ¬ (4 : ℤ) ∣ (1 : ℤ) ^ 2 - (!![2 * 0, 1; 1, 2 * 0] : Matrix (Fin 2) (Fin 2) ℤ).det := by
  rw [det_fin_two_of]; decide

/-- The other sign fails in rank 4: at `b₁₂ = b₃₄ = 1`, all other coefficients
`0`, `B² + Δ = 2` is not divisible by `4`. -/
theorem not_dvd_rank_four :
    ¬ (4 : ℤ) ∣ (1 : ℤ) ^ 2 + (polar4 (0 : ℤ) 0 0 0 1 0 0 0 0 1).det := by
  rw [det_polar4]; decide

/-! ## Even rank, every `n`: `(-1)ⁿ Δ ≡ B² (mod 4)` -/

/-- The upper-triangular half of the universal polar matrix. -/
noncomputable def upper (m : ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial (Sym2 (Fin m)) ℤ) :=
  fun i j => if i ≤ j then X s(i, j) else 0

theorem polar_eq_upper (m : ℕ) : polar m = upper m + (upper m)ᵀ := by
  refine Matrix.ext fun i j => ?_
  simp only [polar, upper, Matrix.add_apply, transpose_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h.ne, h.le, not_le.mpr h]
  · simp [two_mul]
  · simp [h.ne', h.le, not_le.mpr h, Sym2.eq_swap]

theorem skew_eq_upper (m : ℕ) : skew m = upper m - (upper m)ᵀ := by
  refine Matrix.ext fun i j => ?_
  simp only [skew, upper, Matrix.sub_apply, transpose_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.le, not_le.mpr h]
  · simp
  · simp [h, h.le, not_le.mpr h, not_lt.mpr h.le, Sym2.eq_swap]

theorem polar_map_aeval {R : Type*} [CommRing R] {n : ℕ} (y : Sym2 (Fin n) → R) :
    (polar n).map (aeval y) = polarOf y := by
  ext i j
  simp only [map_apply, polar, polarOf]
  split_ifs <;> simp

/-- `Δ ≠ 0`: at `Yᵢ = 1`, `Yᵢⱼ = 0` it is `2 ^ m`. -/
theorem det_polar_ne_zero (m : ℕ) : (polar m).det ≠ 0 := by
  intro h
  let y : Sym2 (Fin m) → ℤ := fun z => if z.IsDiag then 1 else 0
  have hy : polarOf y = diagonal fun _ => 2 := by
    ext i j
    simp only [polarOf, diagonal_apply, y]
    split_ifs with h1 h2 <;> simp_all [Sym2.mk_isDiag_iff]
  have := AlgHom.map_det (aeval (R := ℤ) y) (polar m)
  rw [h, map_zero, AlgHom.mapMatrix_apply, polar_map_aeval, hy, det_diagonal] at this
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  exact pow_ne_zero m two_ne_zero this.symm


theorem polar_transpose (m : ℕ) : (polar m)ᵀ = polar m := by
  rw [polar_eq_upper, transpose_add, transpose_transpose, add_comm]

/-- First-order expansion of `det (P - t Uᵀ)` at `t = 2`: `det K = det P + 2 c₁ + 4 q` with
`2 c₁ = -m det P`, hence `det K ≡ (1 - m) det P (mod 4)`. -/
theorem det_skew_eq_first_order (m : ℕ) :
    ∃ c₁ q : MvPolynomial (Sym2 (Fin m)) ℤ,
      (skew m).det = (polar m).det + 2 * c₁ + 4 * q ∧
        2 * c₁ = -(m : MvPolynomial (Sym2 (Fin m)) ℤ) * (polar m).det := by
  set P := polar m
  set U := upper m
  let f : Polynomial (MvPolynomial (Sym2 (Fin m)) ℤ) :=
    det (P.map Polynomial.C -
      (Polynomial.X : Polynomial (MvPolynomial (Sym2 (Fin m)) ℤ)) • Uᵀ.map Polynomial.C)
  have hdecomp : f = Polynomial.C (f.coeff 0) + Polynomial.X * (Polynomial.C (f.coeff 1) +
      Polynomial.X * f.divX.divX) := by
    conv_lhs => rw [← Polynomial.divX_mul_X_add f, ← Polynomial.divX_mul_X_add f.divX]
    rw [Polynomial.coeff_divX, zero_add]; ring
  have heval : (Polynomial.evalRingHom 2) f = (skew m).det := by
    rw [RingHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp [P, U, skew_eq_upper, polar_eq_upper]
    ring
  have h0 : f.coeff 0 = P.det := by
    rw [Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp
  refine ⟨f.coeff 1, Polynomial.eval 2 f.divX.divX, ?_, ?_⟩
  · rw [← heval, ← h0]
    conv_lhs => rw [hdecomp]
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    ring
  · let F := FractionRing (MvPolynomial (Sym2 (Fin m)) ℤ)
    let φ := algebraMap (MvPolynomial (Sym2 (Fin m)) ℤ) F
    apply IsFractionRing.injective (MvPolynomial (Sym2 (Fin m)) ℤ) F
    set PF := P.map φ
    set UF := U.map φ
    have hdet : φ P.det = PF.det := by rw [RingHom.map_det]; rfl
    have hPF : IsUnit PF.det := by
      rw [isUnit_iff_ne_zero, ← hdet]
      exact (map_ne_zero_iff φ (IsFractionRing.injective _ F)).mpr (det_polar_ne_zero m)
    have hfmap : f.map φ =
        det (PF.map Polynomial.C - (Polynomial.X : Polynomial F) • UFᵀ.map Polynomial.C) := by
      rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
      congr 1
      refine Matrix.ext fun i j => ?_
      simp [PF, UF]
    have hfac : PF.map Polynomial.C - (Polynomial.X : Polynomial F) • UFᵀ.map Polynomial.C =
        PF.map Polynomial.C *
          (1 + (Polynomial.X : Polynomial F) • (-(PF⁻¹ * UFᵀ)).map Polynomial.C) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_neg,
        ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPF, Matrix.one_mul,
        Matrix.map_neg _ (map_neg Polynomial.C),
        smul_neg, sub_eq_add_neg]
    have hc1 : φ (f.coeff 1) = PF.det * trace (-(PF⁻¹ * UFᵀ)) := by
      rw [← Polynomial.coeff_map, hfmap, hfac, det_mul, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det, Polynomial.coeff_C_mul, coeff_det_one_add_X_smul_one]
    have hPFsym : PFᵀ = PF := by rw [← transpose_map, polar_transpose]
    have hPU : P = U + Uᵀ := polar_eq_upper m
    have hPFeq : PF = UF + UFᵀ := by
      simp only [PF, UF, hPU]
      rw [Matrix.map_add _ (map_add φ), transpose_map]
    have htr : trace (PF⁻¹ * UFᵀ) = trace (PF⁻¹ * UF) := by
      rw [← trace_transpose (PF⁻¹ * UF), transpose_mul, transpose_nonsing_inv, hPFsym,
        trace_mul_comm]
    have hsum : trace (PF⁻¹ * UFᵀ) + trace (PF⁻¹ * UF) = m := by
      rw [← trace_add, ← Matrix.mul_add, add_comm, ← hPFeq, Matrix.nonsing_inv_mul _ hPF,
        trace_one, Fintype.card_fin]
    rw [map_mul, map_mul, hc1, map_neg, map_natCast, hdet, trace_neg, map_ofNat]
    linear_combination (-PF.det) * hsum - PF.det * htr

section
open Finset

/-- The fixed-point-free involutions of `Fin m`, that is, the perfect matchings. -/
def fpfInv (m : ℕ) : Finset (Equiv.Perm (Fin m)) :=
  univ.filter fun σ => σ * σ = 1 ∧ ∀ i, σ i ≠ i

/-- The matching sum (hafnian) of a matrix: over the perfect matchings `σ`, the product of
the entries `M i (σ i)` for `i < σ i`. -/
def hafSum {S : Type*} [CommRing S] {m : ℕ} (M : Matrix (Fin m) (Fin m) S) : S :=
  ∑ σ ∈ fpfInv m, ∏ i ∈ univ.filter (fun i => i < σ i), M i (σ i)

/-- For a symmetric matrix and a perfect matching `σ`, `∏ᵢ M (σ i) i` is the square of the
product over the edges. -/
theorem prod_fpf_eq_sq {S : Type*} [CommRing S] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) S) (hM : Mᵀ = M) {σ : Equiv.Perm (Fin m)}
    (hσ : σ ∈ fpfInv m) :
    ∏ i, M (σ i) i = (∏ i ∈ univ.filter (fun i => i < σ i), M i (σ i)) ^ 2 := by
  simp only [fpfInv, mem_filter, mem_univ, true_and] at hσ
  obtain ⟨hinv, hfix⟩ := hσ
  have hss : ∀ i, σ (σ i) = i := fun i => by
    have := congrArg (fun τ : Equiv.Perm (Fin m) => τ i) hinv
    simpa using this
  have hsym : ∀ i j, M i j = M j i := fun i j => by
    simpa using congrFun (congrFun hM j) i
  rw [← prod_filter_mul_prod_filter_not univ (fun i => i < σ i), sq]
  congr 1
  · exact prod_congr rfl fun i _ => hsym _ _
  · refine prod_nbij' σ σ ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [mem_filter, mem_univ, true_and, not_lt] at hi ⊢
      rw [hss]
      exact lt_of_le_of_ne hi (hfix i)
    · intro i hi
      simp only [mem_filter, mem_univ, true_and, not_lt] at hi ⊢
      rw [hss]; exact hi.le
    · intro i _; exact hss i
    · intro i _; exact hss i
    · intro i _; rw [hss]

/-- In characteristic `2`, the determinant of a symmetric matrix with zero diagonal is the
square of its matching sum: signs disappear, `σ` and `σ⁻¹` give the same product so the
non-involutions cancel in pairs, and involutions with a fixed point give `0`. -/
theorem det_eq_hafSum_sq {S : Type*} [CommRing S] [CharP S 2] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) S) (hM : Mᵀ = M) (hd : ∀ i, M i i = 0) :
    M.det = hafSum M ^ 2 := by
  have h2 : (2 : S) = 0 := by exact_mod_cast CharP.cast_eq_zero S 2
  have hsym : ∀ i j, M i j = M j i := fun i j => by
    simpa using congrFun (congrFun hM j) i
  rw [det_apply]
  have hsign : ∀ σ : Equiv.Perm (Fin m),
      (Equiv.Perm.sign σ) • (∏ i, M (σ i) i) = ∏ i, M (σ i) i := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]
    · rw [h, Units.neg_smul, one_smul]; exact CharTwo.neg_eq _
  simp_rw [hsign]
  rw [← sum_filter_add_sum_filter_not univ (fun σ => σ ∈ fpfInv m)]
  have hzero : ∑ σ ∈ univ.filter (fun σ => σ ∉ fpfInv m), ∏ i, M (σ i) i = 0 := by
    have hinvp : ∀ σ : Equiv.Perm (Fin m), ∏ i, M (σ⁻¹ i) i = ∏ i, M (σ i) i := by
      intro σ
      rw [← Equiv.prod_comp σ]
      exact prod_congr rfl fun i _ => by simp [hsym]
    refine sum_involution (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_
    · intro σ _
      rw [hinvp, ← two_mul, h2, zero_mul]
    · intro σ hσ hne heq
      apply hne
      simp only [fpfInv, mem_filter, mem_univ, true_and, not_and, not_forall,
        not_not] at hσ
      have hinv : σ * σ = 1 := by
        rw [← mul_inv_cancel σ, heq]
      obtain ⟨i, hi⟩ := hσ hinv
      exact prod_eq_zero (mem_univ i) (by rw [hi, hd])
    · intro σ hσ
      simp only [fpfInv, mem_filter, mem_univ, true_and] at hσ ⊢
      intro h
      apply hσ
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, fun i hi => h2 i ?_⟩
      · simpa [_root_.mul_inv_rev] using congrArg (·⁻¹) h1
      · rw [Equiv.Perm.inv_eq_iff_eq]; exact hi.symm
    · intro σ _; exact inv_inv σ
  rw [hzero, add_zero, filter_mem_eq_inter, univ_inter, hafSum, sum_pow_char]
  exact sum_congr rfl fun σ hσ => prod_fpf_eq_sq M hM hσ


end

theorem inv_transpose_of_skew {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι k) (hA : Aᵀ = -A) (hu : IsUnit A.det) : A⁻¹ᵀ = -A⁻¹ := by
  rw [transpose_nonsing_inv, hA]
  apply Matrix.inv_eq_right_inv
  rw [neg_mul_neg, Matrix.mul_nonsing_inv _ hu]

/-- Induction step: an antisymmetric matrix of size `m + 2` over a field of characteristic
`≠ 2` has a square determinant if those of size `m` do (Schur complement on the `2 × 2`
block of a nonzero coefficient of the first row). -/
theorem det_skew_step {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (m : ℕ)
    (ih : ∀ K : Matrix (Fin m) (Fin m) k, Kᵀ = -K → ∃ s, K.det = s ^ 2)
    (K : Matrix (Fin (m + 2)) (Fin (m + 2)) k) (hK : Kᵀ = -K) : ∃ s, K.det = s ^ 2 := by
  have hskew : ∀ i j, K j i = -K i j := fun i j => by
    simpa using congrFun (congrFun hK i) j
  have hdiag : ∀ i, K i i = 0 := fun i => by
    have h := hskew i i
    have : (2 : k) * K i i = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h2
  by_cases hrow : ∀ j, K 0 j = 0
  · exact ⟨0, by rw [det_eq_zero_of_row_eq_zero 0 hrow]; ring⟩
  simp only [not_forall] at hrow
  obtain ⟨j, hj⟩ := hrow
  have hj0 : j ≠ 0 := fun h => hj (h ▸ hdiag 0)
  let e := Equiv.swap (1 : Fin (m + 2)) j
  let g : Fin 2 ⊕ Fin m ≃ Fin (m + 2) := finSumFinEquiv.trans (finCongr (Nat.add_comm 2 m))
  have hg0 : g (Sum.inl 0) = 0 := by ext; simp [g]
  have hg1 : g (Sum.inl 1) = 1 := by ext; simp [g]
  have he0 : e 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by simp) hj0.symm
  have he1 : e 1 = j := Equiv.swap_apply_left _ _
  let N := K.submatrix (g.trans e) (g.trans e)
  have hdetN : N.det = K.det := det_submatrix_equiv_self (g.trans e) K
  have hNskew : ∀ i j, N j i = -N i j := fun i j => hskew _ _
  have hA : N.toBlocks₁₁ = !![0, K 0 j; -K 0 j, 0] := by
    conv_lhs => rw [Matrix.eta_fin_two N.toBlocks₁₁]
    simp only [toBlocks₁₁, of_apply, N, submatrix_apply, Equiv.trans_apply, hg0, hg1, he0, he1,
      hdiag, hskew 0 j]
  have hdetA : N.toBlocks₁₁.det = K 0 j ^ 2 := by rw [hA, det_fin_two_of]; ring
  have hu : IsUnit N.toBlocks₁₁.det := by
    rw [hdetA]; exact (pow_ne_zero 2 hj).isUnit
  let _ : Invertible N.toBlocks₁₁ := invertibleOfIsUnitDet _ hu
  have hAskew : N.toBlocks₁₁ᵀ = -N.toBlocks₁₁ := by
    rw [hA]; ext a b; fin_cases a <;> fin_cases b <;> simp
  have hC : N.toBlocks₂₁ = -N.toBlocks₁₂ᵀ := by
    ext a b; simpa [toBlocks₂₁, toBlocks₁₂] using hNskew (Sum.inl b) (Sum.inr a)
  have hD : N.toBlocks₂₂ᵀ = -N.toBlocks₂₂ := by
    ext a b; simpa [toBlocks₂₂] using hNskew (Sum.inr a) (Sum.inr b)
  have hinv : (⅟N.toBlocks₁₁)ᵀ = -⅟N.toBlocks₁₁ := by
    rw [invOf_eq_nonsing_inv]; exact inv_transpose_of_skew _ hAskew hu
  have hS : (N.toBlocks₂₂ - N.toBlocks₂₁ * ⅟N.toBlocks₁₁ * N.toBlocks₁₂)ᵀ =
      -(N.toBlocks₂₂ - N.toBlocks₂₁ * ⅟N.toBlocks₁₁ * N.toBlocks₁₂) := by
    rw [transpose_sub, transpose_mul, transpose_mul, hD, hinv, hC, transpose_neg,
      transpose_transpose]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, neg_sub, Matrix.mul_assoc]
    abel
  obtain ⟨s, hs⟩ := ih _ hS
  refine ⟨K 0 j * s, ?_⟩
  have key : N.det = N.toBlocks₁₁.det *
      (N.toBlocks₂₂ - N.toBlocks₂₁ * ⅟N.toBlocks₁₁ * N.toBlocks₁₂).det := by
    conv_lhs => rw [← fromBlocks_toBlocks N]
    exact det_fromBlocks₁₁ _ _ _ _
  rw [← hdetN, key, hdetA, hs]
  ring

/-- Over a field of characteristic `≠ 2`, an antisymmetric matrix of even size has a square
determinant. -/
theorem det_skew_sq_field {k : Type*} [Field k] (h2 : (2 : k) ≠ 0) (n : ℕ)
    (K : Matrix (Fin (2 * n)) (Fin (2 * n)) k) (hK : Kᵀ = -K) : ∃ s, K.det = s ^ 2 := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih => exact det_skew_step h2 (2 * n) ih K hK


theorem skew_map_transpose {k : Type*} [CommRing k] (m : ℕ)
    (φ : MvPolynomial (Sym2 (Fin m)) ℤ →+* k) : ((skew m).map φ)ᵀ = -(skew m).map φ := by
  rw [← transpose_map, skew_transpose, Matrix.map_neg _ (map_neg φ)]

/-- **Even rank.** The universal skew-symmetric determinant is a square in `ℤ[Y]`. -/
theorem det_skew_eq_sq (n : ℕ) : ∃ r, (skew (2 * n)).det = r ^ 2 := by
  let A := MvPolynomial (Sym2 (Fin (2 * n))) ℤ
  let F := FractionRing A
  have h2 : (2 : F) ≠ 0 := by simp
  obtain ⟨s, hs⟩ := det_skew_sq_field h2 n _ (skew_map_transpose (2 * n) (algebraMap A F))
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hs
  have hint : IsIntegral A s := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (skew (2 * n)).det,
      Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [Polynomial.eval₂_sub, hs]
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨r, IsFractionRing.injective A F ?_⟩
  rw [map_pow, hr, hs]

/-- The hafnian of the off-diagonal variables: the sum over the perfect matchings of
`Fin m` (the fixed-point-free involutions) of the products of the `Yᵢⱼ`. -/
noncomputable def hafnian (m : ℕ) : MvPolynomial (Sym2 (Fin m)) ℤ :=
  ∑ σ ∈ fpfInv m, ∏ i ∈ Finset.univ.filter (fun i => i < σ i), X s(i, σ i)

/-- Modulo `2`, `det K` is the square of the hafnian. -/
theorem red_det_skew (m : ℕ) : red m (skew m).det = (red m (hafnian m)) ^ 2 := by
  have hT : ((skew m).map (red m))ᵀ = (skew m).map (red m) := by
    rw [skew_map_transpose]; ext i j; exact CharTwo.neg_eq _
  have hd : ∀ i, (skew m).map (red m) i i = 0 := fun i => by simp [skew]
  rw [RingHom.map_det, RingHom.mapMatrix_apply, det_eq_hafSum_sq _ hT hd, hafSum, hafnian,
    map_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp [skew, hi]

/-- **Even rank.** `det K ≡ B² (mod 4)` for the universal skew-symmetric matrix. -/
theorem four_dvd_det_skew_sub (n : ℕ) :
    (4 : MvPolynomial (Sym2 (Fin (2 * n))) ℤ) ∣ (skew (2 * n)).det - hafnian (2 * n) ^ 2 := by
  obtain ⟨r, hr⟩ := det_skew_eq_sq n
  have h : red (2 * n) (r - hafnian (2 * n)) = 0 := by
    have h1 := red_det_skew (2 * n)
    rw [hr, map_pow] at h1
    have : red (2 * n) (r - hafnian (2 * n)) ^ 2 = 0 := by
      rw [map_sub, sub_pow_char, h1, sub_self]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  obtain ⟨g, hg⟩ := two_dvd_of_red_eq_zero h
  refine ⟨hafnian (2 * n) * g + g ^ 2, ?_⟩
  rw [hr, sub_eq_iff_eq_add.mp hg]
  ring

/-- `(-1)ⁿ ≡ 1 - 2n (mod 4)`. -/
theorem four_dvd_neg_one_pow (n : ℕ) : (4 : ℤ) ∣ (-1) ^ n - (1 - 2 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨-c + n, by push_cast; rw [pow_succ]; linear_combination (-1 : ℤ) * hc⟩

/-- **Pages 68–71, every even rank.** In `ℤ[Y]`, `4` divides `(-1)ⁿ Δ - B²`, `Δ` the
determinant of the polar matrix of rank `2n` and `B` the hafnian of the `Yᵢⱼ`. -/
theorem four_dvd_disc_sub_hafnian_sq (n : ℕ) :
    (4 : MvPolynomial (Sym2 (Fin (2 * n))) ℤ) ∣
      (-1) ^ n * (polar (2 * n)).det - hafnian (2 * n) ^ 2 := by
  obtain ⟨c₁, q, hK, hc⟩ := det_skew_eq_first_order (2 * n)
  obtain ⟨d, hd⟩ := four_dvd_neg_one_pow n
  have hd' : ((-1) ^ n : MvPolynomial (Sym2 (Fin (2 * n))) ℤ) = 1 - 2 * n + 4 * d := by
    have := congrArg (Int.cast : ℤ → MvPolynomial (Sym2 (Fin (2 * n))) ℤ) hd
    push_cast at this
    linear_combination this
  obtain ⟨e, he⟩ := four_dvd_det_skew_sub n
  refine ⟨d * (polar (2 * n)).det - q + e, ?_⟩
  push_cast at hc
  rw [hd']
  linear_combination he - hK - hc

/-- **Pages 68–71, every even rank, over any base.** There is `C ∈ ℤ[Y]` such that for every
commutative ring `R` and every form `Σ yᵢ xᵢ² + Σ_{i<j} yᵢⱼ xᵢ xⱼ` of rank `2n` over `R`,
`(-1)ⁿ det P(y) = B(y)² - 4 C(y)`. -/
theorem disc_even_rank (n : ℕ) :
    ∃ C : MvPolynomial (Sym2 (Fin (2 * n))) ℤ, ∀ {R : Type*} [CommRing R]
      (y : Sym2 (Fin (2 * n)) → R),
        (-1) ^ n * (polarOf y).det = aeval y (hafnian (2 * n)) ^ 2 - 4 * aeval y C := by
  obtain ⟨C, hC⟩ := four_dvd_disc_sub_hafnian_sq n
  refine ⟨-C, fun y => ?_⟩
  have h := congrArg (aeval (R := ℤ) y) hC
  rw [map_sub, map_mul, map_pow, map_pow, map_neg, map_one, AlgHom.map_det,
    AlgHom.mapMatrix_apply, polar_map_aeval, map_mul, map_ofNat] at h
  rw [map_neg]
  linear_combination h

/-! ## Pages 117–125: the canonical symmetry of a biregular affine quadric -/

section Symmetry

open QuadraticMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The linear form `π = φ(a, ·)`, `φ` the polar form of `Q` (page 117, (9)). -/
def piForm (Q : QuadraticForm R M) (a : M) : M →ₗ[R] R := polarBilin Q a

theorem piForm_apply (Q : QuadraticForm R M) (a x : M) : piForm Q a x = QuadraticMap.polar Q a x := rfl

/-- The canonical symmetry `σ = id - π ⊗ a` (page 123, (20)). -/
def canSym (Q : QuadraticForm R M) (a : M) : M →ₗ[R] M :=
  LinearMap.id - (piForm Q a).smulRight a

theorem canSym_apply (Q : QuadraticForm R M) (a x : M) :
    canSym Q a x = x - QuadraticMap.polar Q a x • a := rfl

/-- `Q (x + y) = Q x + Q y + φ(x, y)`. -/
theorem quad_map_add (Q : QuadraticForm R M) (x y : M) : Q (x + y) = Q x + Q y + QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar]; ring

variable {Q : QuadraticForm R M} {a : M}

/-- **Page 117, (10).** `π(a) = 2`. -/
theorem piForm_self (ha : Q a = 1) : piForm Q a a = 2 := by
  rw [piForm_apply, polar_self, ha, two_smul, one_add_one_eq_two]

/-- `Q (x + t a) = Q x + t (φ(a, x) + t Q a)` (page 122). -/
theorem quad_map_add_smul (x : M) (t : R) : Q (x + t • a) = Q x + t * (QuadraticMap.polar Q a x + t * Q a) := by
  rw [quad_map_add, QuadraticMap.map_smul, polar_smul_right, polar_comm, smul_eq_mul, smul_eq_mul]
  ring

/-- **Page 123, (19)–(20).** `σ` preserves `Q`. -/
theorem canSym_isometry (ha : Q a = 1) (x : M) : Q (canSym Q a x) = Q x := by
  rw [canSym_apply, sub_eq_add_neg, ← neg_smul, quad_map_add_smul, ha]; ring

/-- **Page 123, (21).** `σ² = id`, because `π(a) = 2`. -/
theorem canSym_canSym (ha : Q a = 1) (x : M) : canSym Q a (canSym Q a x) = x := by
  have h := piForm_self ha
  rw [piForm_apply] at h
  simp only [canSym_apply, polar_sub_right, polar_smul_right, h, smul_eq_mul]
  module


/-- For `e` idempotent, `x ↦ x - e π(x) a` preserves `Q` (and fixes `ker π`). -/
theorem isometry_of_idem (ha : Q a = 1) {e : R} (he : IsIdempotentElem e) (x : M) :
    Q (x - (e * QuadraticMap.polar Q a x) • a) = Q x := by
  rw [sub_eq_add_neg, ← neg_smul, quad_map_add_smul, ha]
  have h : e * e = e := he
  linear_combination (QuadraticMap.polar Q a x) ^ 2 * h

/-- **Page 123, the marginal Proposition, over any base.** If `φ` is nondegenerate and `π`
is onto, a linear map fixing `ker π` pointwise and preserving `Q` is `x ↦ x - e π(x) a`
with `e` idempotent (the page's `λ(λ + 1) = 0`, with `e = -λ`). -/
theorem eq_of_isometry_fix (ha : Q a = 1)
    (hnd : ∀ y, (∀ x, QuadraticMap.polar Q y x = 0) → y = 0) {b : M} (hb : QuadraticMap.polar Q a b = 1)
    (u : M →ₗ[R] M) (hu : ∀ v, QuadraticMap.polar Q a v = 0 → u v = v) (hQ : ∀ x, Q (u x) = Q x) :
    ∃ e : R, IsIdempotentElem e ∧ ∀ x, u x = x - (e * QuadraticMap.polar Q a x) • a := by
  set c := u b - b with hcdef
  have hux : ∀ x, u x = x + QuadraticMap.polar Q a x • c := by
    intro x
    have h := hu (x - QuadraticMap.polar Q a x • b) (by
      rw [polar_sub_right, polar_smul_right, hb, smul_eq_mul, mul_one, sub_self])
    rw [map_sub, map_smul] at h
    rw [hcdef, smul_sub]
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  have hg : ∀ x, QuadraticMap.polar Q a x * (QuadraticMap.polar Q a x * Q c + QuadraticMap.polar Q x c) = 0 := by
    intro x
    have := hQ x
    rw [hux, quad_map_add, QuadraticMap.map_smul, polar_smul_right, smul_eq_mul,
      smul_eq_mul] at this
    linear_combination this
  have hfb : Q c + QuadraticMap.polar Q b c = 0 := by
    have := hg b
    rw [hb] at this
    linear_combination this
  have hf : ∀ x, QuadraticMap.polar Q a x * Q c + QuadraticMap.polar Q x c = 0 := by
    intro x
    have := hg (x + b)
    rw [polar_add_right, hb, polar_add_left] at this
    linear_combination this - hg x - (QuadraticMap.polar Q a x + 1) * hfb
  have h0 : c + Q c • a = 0 := by
    apply hnd
    intro x
    rw [polar_add_left, polar_smul_left, smul_eq_mul, polar_comm Q c x]
    linear_combination hf x
  have hc : c = (-Q c) • a := by
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h0
  have hidem : Q c * Q c = Q c := by
    conv_rhs => rw [hc]
    rw [QuadraticMap.map_smul, ha, smul_eq_mul, mul_one, neg_mul_neg]
  refine ⟨Q c, hidem, fun x => ?_⟩
  rw [hux]
  conv_lhs => rw [hc]
  rw [smul_smul, sub_eq_add_neg, ← neg_smul]
  congr 2
  ring

/-- Over a base with no nontrivial idempotent, the isometries fixing `ker π` are `id`
and `σ`. -/
theorem eq_id_or_canSym (ha : Q a = 1)
    (hnd : ∀ y, (∀ x, QuadraticMap.polar Q y x = 0) → y = 0) {b : M} (hb : QuadraticMap.polar Q a b = 1)
    (hR : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (u : M →ₗ[R] M) (hu : ∀ v, QuadraticMap.polar Q a v = 0 → u v = v) (hQ : ∀ x, Q (u x) = Q x) :
    u = LinearMap.id ∨ u = canSym Q a := by
  obtain ⟨e, he, hux⟩ := eq_of_isometry_fix ha hnd hb u hu hQ
  rcases hR e he with rfl | rfl
  · left; ext x; rw [hux]; simp
  · right; ext x; rw [hux, canSym_apply, one_mul]

/-- **Page 123.** If `2` is invertible, `a/2 ∈ E = π⁻¹(1)` and on `E` the projective map `σ`
(represented by `-σ`, which preserves `E`) is the symmetry of centre `a/2`. -/
theorem canSym_center [Invertible (2 : R)] (ha : Q a = 1) (x : M) (hx : QuadraticMap.polar Q a x = 1) :
    QuadraticMap.polar Q a (⅟(2 : R) • a) = 1 ∧ QuadraticMap.polar Q a (-canSym Q a x) = 1 ∧
      -canSym Q a x - ⅟(2 : R) • a = -(x - ⅟(2 : R) • a) := by
  have h := piForm_self ha
  rw [piForm_apply] at h
  refine ⟨?_, ?_, ?_⟩
  · rw [polar_smul_right, h, smul_eq_mul, invOf_mul_self]
  · rw [canSym_apply, polar_neg_right, polar_sub_right, polar_smul_right, hx, h]; norm_num
  · rw [canSym_apply, hx, one_smul]
    rw [show -(x - a) - ⅟(2 : R) • a = -(x - ⅟(2 : R) • a) + (a - (2 : R) • ⅟(2 : R) • a) by
      rw [two_smul]; abel, smul_smul, mul_invOf_self, one_smul, sub_self, add_zero]

/-- **Page 123.** If `2 = 0`, `π(a) = 0`: `a ∈ ker π`, `σ` preserves each level of `π` and
acts on `E` as `x ↦ x - a`; `σ` is the transvection `id - π ⊗ a`. -/
theorem canSym_char_two (h2 : (2 : R) = 0) (ha : Q a = 1) :
    QuadraticMap.polar Q a a = 0 ∧ (∀ x, QuadraticMap.polar Q a (canSym Q a x) = QuadraticMap.polar Q a x) ∧
      ∀ x, QuadraticMap.polar Q a x = 1 → canSym Q a x = x - a := by
  have h := piForm_self ha
  rw [piForm_apply, h2] at h
  refine ⟨h, fun x => ?_, fun x hx => ?_⟩
  · rw [canSym_apply, polar_sub_right, polar_smul_right, h, smul_zero, sub_zero]
  · rw [canSym_apply, hx, one_smul]

/-- **Page 124.** For `T = M₂(R)`, `q = det`, `a = 1`: `φ(x, 1) = tr x`, so `π` is the trace
(the page has `-tr`, from the opposite polar form). -/
theorem det_polar_one (x : Matrix (Fin 2) (Fin 2) R) :
    (x + 1).det - x.det - (1 : Matrix (Fin 2) (Fin 2) R).det = x.trace := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.det_one, Matrix.trace_fin_two]
  simp
  ring

end Symmetry

end Grothendieck.Folder77
