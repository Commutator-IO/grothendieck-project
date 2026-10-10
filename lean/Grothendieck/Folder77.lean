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
* The general even rank is not proved here.
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

end Grothendieck.Folder77
