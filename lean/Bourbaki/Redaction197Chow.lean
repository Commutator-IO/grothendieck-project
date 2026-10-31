import Mathlib

/-!
# Bourbaki rédaction n° 197: Chow coordinates of a product are not integral polynomials

Rédaction n° 197 of the Bourbaki archive (P. Samuel, May 1954; Archives Henri Poincaré, item
<https://archives-bourbaki.ahp-numerique.fr/items/show/612>) treats the Chow coordinates of
cycles in projective space. On p. 82 it is put forward as probable that the Chow coordinates of
a product `X × Y`, embedded by Segre, are universal polynomials with integer coefficients in the
Chow coordinates of `X` and of `Y`. This file shows that this fails already for zero-cycles of
three points in the plane, over `ℤ`.

**Setting.** A zero-cycle of three points `(xⱼ, yⱼ)` of the affine plane has the Chow form
`∏ⱼ (v₀ + v₁ xⱼ + v₂ yⱼ)`; its coefficients are the elementary multisymmetric polynomials
`e p q`, the sum over the ways of letting `p` of the points contribute their `x` and `q` others
their `y` (`e 0 0 = 1`, and `e p q = 0` for `p + q > 3`). For two such cycles, with points
`(cᵢ, dᵢ)` and `(aⱼ, bⱼ)`, the Chow form of the Segre product, dehomogenised in the same way,
is `T = ∏ᵢⱼ (1 + cᵢ aⱼ + dᵢ bⱼ)`. The guess would give a polynomial `G` with integer
coefficients in the `9 + 9` nonconstant `e`'s of both sides with `T = G(e(c,d), e(a,b))`.

**Certificate.** A `ℤ`-linear form `α` reads eight coefficients of a polynomial in
`x₁, y₁, …, y₃` (the sorted representatives of the monomial multisymmetric functions of
bidegree `(2,2)`) with weights `1, -1, -2, -1, -2, -1, -1, -2`. It takes values divisible by
`3` on every polynomial in the `e`'s: on a product of `e`'s of bidegree `(2,2)` by computation
(eight products), on every other product because the `e`'s are bihomogeneous and `α` reads only
bidegree `(2,2)`. Applying `α` on both sides, `β = α ⊗ α` is then divisible by `9` on every
`G(e(c,d), e(a,b))`, while `β T = 39`.

The ring `ℤ[a, b, c, d]` is written `MvPolynomial V (MvPolynomial V ℤ)`: the inner variables
are the `(cᵢ, dᵢ)`, the outer ones the `(aⱼ, bⱼ)`.

* `prod_eq_sum_e`: `∏ᵢ (1 + cᵢ U + dᵢ W) = ∑ e p q Uᵖ W^q`, which characterises the `e`'s;
* `alpha_e_products`: the eight values of `α` on the products of bidegree `(2,2)`;
* `three_dvd_alpha_aeval`: `3 ∣ α (G(e))` for every integral polynomial `G` in the nine `e`'s;
* `nine_dvd_beta_aeval`: `9 ∣ β (G(e(c,d), e(a,b)))`;
* `beta_T`: `β T = 39`;
* `not_exists_integral_formula`, `T_not_mem_adjoin`: no such `G` exists.

Computations of coefficients go through a small reflection layer: polynomials given by explicit
lists of monomials (`PL`, `interp`), multiplied as lists (`mulL`), so that the kernel evaluates
the values of `α` by `decide +kernel`. Positive-dimensional cycles are not treated.
-/

open MvPolynomial

namespace Bourbaki.Redaction197Chow

/-- The variables: point `j : Fin 3`, coordinate `0` (the `x`) or `1` (the `y`). -/
abbrev V := Fin 3 × Fin 2

/-- An exponent: for each of the three points, the pair (degree in `x`, degree in `y`). -/
abbrev Exp := Fin 3 → ℕ × ℕ

section Mon

variable (R : Type*) [CommRing R]

/-- The monomial `∏ⱼ xⱼ^{aⱼ} yⱼ^{bⱼ}` of exponent `f = ((a₀,b₀),(a₁,b₁),(a₂,b₂))`. -/
noncomputable def mon (f : Exp) : MvPolynomial V R :=
  ∏ j, X (j, 0) ^ (f j).1 * X (j, 1) ^ (f j).2

/-- The exponent `f` as a finitely supported function on the variables. -/
noncomputable def mono (f : Exp) : V →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => if v.2 = 0 then (f v.1).1 else (f v.1).2

/-- `mon f` is the monomial of exponent `mono f`. -/
theorem mon_eq_monomial (f : Exp) : mon R f = monomial (mono f) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [mon, mono, Fintype.prod_prod_type, Fin.prod_univ_two]

/-- Distinct exponents give distinct monomials. -/
theorem mono_injective : Function.Injective mono := by
  intro f g h
  funext j
  have h0 := DFunLike.congr_fun h (j, 0)
  have h1 := DFunLike.congr_fun h (j, 1)
  simp [mono] at h0 h1
  exact Prod.ext h0 h1

/-- The coefficient of a monomial `mon f` at the exponent `g`. -/
theorem coeff_mon (f g : Exp) : (mon R f).coeff (mono g) = if f = g then 1 else 0 := by
  rw [mon_eq_monomial, coeff_monomial]
  by_cases h : f = g
  · simp [h]
  · rw [ite_eq_right (fun h' => h (mono_injective h')), ite_eq_right h]

/-- Monomials multiply by adding exponents. -/
theorem mon_add (f g : Exp) : mon R (f + g) = mon R f * mon R g := by
  simp only [mon, Pi.add_apply, Prod.fst_add, Prod.snd_add, pow_add, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun _ _ => by ring

/-- The monomial of exponent `0` is `1`. -/
theorem mon_zero : mon R 0 = 1 := by simp [mon]

end Mon

/-! ### Polynomials as lists of monomials -/

/-- A polynomial with integer coefficients given as a list of (exponent, coefficient). -/
abbrev PL := List (Exp × ℤ)

/-- The polynomial that a list stands for. -/
noncomputable def interp (l : PL) : MvPolynomial V ℤ := (l.map fun t => C t.2 * mon ℤ t.1).sum

/-- Product of two lists, term by term. -/
def mulL (l₁ l₂ : PL) : PL := l₁.flatMap fun a => l₂.map fun b => (a.1 + b.1, a.2 * b.2)

/-- The list of the polynomial `1`. -/
def oneL : PL := [(0, 1)]

/-- Powers of a list. -/
def powL (l : PL) : ℕ → PL
  | 0 => oneL
  | k + 1 => mulL l (powL l k)

/-- Product of a list of lists. -/
def prodL : List PL → PL
  | [] => oneL
  | l :: ls => mulL l (prodL ls)

/-- The coefficient of the exponent `m` in a list. -/
def coeffL (m : Exp) (l : PL) : ℤ := (l.map fun t => if t.1 = m then t.2 else 0).sum

/-- `interp` of a concatenation. -/
theorem interp_append (l₁ l₂ : PL) : interp (l₁ ++ l₂) = interp l₁ + interp l₂ := by
  simp [interp]

/-- `interp` of a cons. -/
theorem interp_cons (a : Exp × ℤ) (l : PL) : interp (a :: l) = C a.2 * mon ℤ a.1 + interp l := by
  simp [interp]

/-- Multiplying a list by one monomial. -/
theorem interp_map_mul (a : Exp × ℤ) (l : PL) :
    interp (l.map fun b => (a.1 + b.1, a.2 * b.2)) = C a.2 * mon ℤ a.1 * interp l := by
  induction l with
  | nil => simp [interp]
  | cons b l ih =>
    rw [List.map_cons, interp_cons, ih, interp_cons, mon_add, map_mul]
    ring

/-- `mulL` computes the product. -/
theorem interp_mulL (l₁ l₂ : PL) : interp (mulL l₁ l₂) = interp l₁ * interp l₂ := by
  induction l₁ with
  | nil => simp [mulL, interp]
  | cons a l ih =>
    rw [show mulL (a :: l) l₂ = (l₂.map fun b => (a.1 + b.1, a.2 * b.2)) ++ mulL l l₂ from rfl,
      interp_append, interp_map_mul, ih, interp_cons]
    ring

/-- `oneL` stands for `1`. -/
theorem interp_oneL : interp oneL = 1 := by simp [interp, oneL, mon_zero]

/-- `powL` computes powers. -/
theorem interp_powL (l : PL) (k : ℕ) : interp (powL l k) = interp l ^ k := by
  induction k with
  | zero => simp [powL, interp_oneL]
  | succ k ih => rw [powL, interp_mulL, ih, pow_succ']

/-- `prodL` computes products. -/
theorem interp_prodL (ls : List PL) : interp (prodL ls) = (ls.map interp).prod := by
  induction ls with
  | nil => simp [prodL, interp_oneL]
  | cons l ls ih => rw [prodL, interp_mulL, ih, List.map_cons, List.prod_cons]

/-- `coeffL` computes coefficients. -/
theorem coeff_interp (m : Exp) (l : PL) : (interp l).coeff (mono m) = coeffL m l := by
  induction l with
  | nil => simp [interp, coeffL]
  | cons a l ih =>
    rw [interp_cons, coeffL, List.map_cons, List.sum_cons, ← coeffL, ← ih,
      show ∀ p q : MvPolynomial V ℤ, (p + q).coeff (mono m) = p.coeff (mono m) + q.coeff (mono m)
        from fun p q => by simp, coeff_C_mul, coeff_mon]
    simp

/-! ### The elementary multisymmetric polynomials -/

/-- The list of the elementary multisymmetric polynomial `e p q` of three points: one monomial
for each way of letting `p` points contribute `x` and `q` other points contribute `y`. -/
def le : ℕ → ℕ → PL
  | 0, 0 => oneL
  | 1, 0 => [(![(1,0), (0,0), (0,0)], 1), (![(0,0), (1,0), (0,0)], 1), (![(0,0), (0,0), (1,0)], 1)]
  | 0, 1 => [(![(0,1), (0,0), (0,0)], 1), (![(0,0), (0,1), (0,0)], 1), (![(0,0), (0,0), (0,1)], 1)]
  | 2, 0 => [(![(1,0), (1,0), (0,0)], 1), (![(1,0), (0,0), (1,0)], 1), (![(0,0), (1,0), (1,0)], 1)]
  | 0, 2 => [(![(0,1), (0,1), (0,0)], 1), (![(0,1), (0,0), (0,1)], 1), (![(0,0), (0,1), (0,1)], 1)]
  | 1, 1 => [(![(1,0), (0,1), (0,0)], 1), (![(1,0), (0,0), (0,1)], 1), (![(0,1), (1,0), (0,0)], 1),
      (![(0,0), (1,0), (0,1)], 1), (![(0,1), (0,0), (1,0)], 1), (![(0,0), (0,1), (1,0)], 1)]
  | 3, 0 => [(![(1,0), (1,0), (1,0)], 1)]
  | 0, 3 => [(![(0,1), (0,1), (0,1)], 1)]
  | 2, 1 => [(![(1,0), (1,0), (0,1)], 1), (![(1,0), (0,1), (1,0)], 1), (![(0,1), (1,0), (1,0)], 1)]
  | 1, 2 => [(![(1,0), (0,1), (0,1)], 1), (![(0,1), (1,0), (0,1)], 1), (![(0,1), (0,1), (1,0)], 1)]
  | _, _ => []

/-- The elementary multisymmetric polynomial `e p q` in `x₀, y₀, x₁, y₁, x₂, y₂`. -/
noncomputable def e (p q : ℕ) : MvPolynomial V ℤ := interp (le p q)

/-- The polynomials in the `(cᵢ, dᵢ)`, coefficients of the outer ring. -/
abbrev Rcd := MvPolynomial V ℤ

/-- The ring `ℤ[c, d][a, b]`. -/
abbrev S := MvPolynomial V Rcd

/-- The generating identity `∏ᵢ (1 + cᵢ U + dᵢ W) = ∑_{p,q} e p q Uᵖ W^q`, which determines the
`e p q` and checks the lists `le`. -/
theorem prod_eq_sum_e (U W : S) :
    ∏ i : Fin 3, (1 + C (X (i, 0)) * U + C (X (i, 1)) * W) =
      ∑ pq : Fin 4 × Fin 4, C (e pq.1 pq.2) * U ^ (pq.1 : ℕ) * W ^ (pq.2 : ℕ) := by
  simp [Fin.prod_univ_three, Fintype.sum_prod_type, Fin.sum_univ_four, e, le, interp, oneL, mon]
  ring

/-! ### The certificate -/

/-- The eight exponents read by `α`, with entries in `Fin 4`. -/
def certσ : Fin 8 → Fin 3 → Fin 4 × Fin 4 :=
  ![![(1,0), (1,0), (0,2)], ![(1,1), (1,0), (0,1)], ![(1,1), (1,1), (0,0)],
    ![(1,2), (1,0), (0,0)], ![(2,0), (0,1), (0,1)], ![(2,0), (0,2), (0,0)],
    ![(2,1), (0,1), (0,0)], ![(2,2), (0,0), (0,0)]]

/-- The weights of `α`. -/
def certW : Fin 8 → ℤ := ![1, -1, -2, -1, -2, -1, -1, -2]

/-- An exponent with entries in `Fin 4`, as an exponent. -/
def toExp (σ : Fin 3 → Fin 4 × Fin 4) : Exp := fun j => ((σ j).1, (σ j).2)

/-- `toExp` is injective. -/
theorem toExp_injective : Function.Injective toExp := by
  intro σ τ h
  funext j
  have := congr_fun h j
  simp only [toExp, Prod.mk.injEq] at this
  exact Prod.ext (Fin.ext this.1) (Fin.ext this.2)

/-- The linear form `α`: the weighted sum of the eight coefficients, for any coefficient ring. -/
noncomputable def alpha (R : Type*) [CommRing R] : MvPolynomial V R →ₗ[R] R where
  toFun P := ∑ i, (certW i : R) * P.coeff (mono (toExp (certσ i)))
  map_add' P Q := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [coeff_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- `α` as the weighted sum of eight coefficients. -/
theorem alpha_apply (R : Type*) [CommRing R] (P : MvPolynomial V R) :
    alpha R P = ∑ i, (certW i : R) * P.coeff (mono (toExp (certσ i))) := rfl

/-- `α` on lists. -/
def alphaL (l : PL) : ℤ := ∑ i, certW i * coeffL (toExp (certσ i)) l

/-- `alphaL` computes `α`. -/
theorem alpha_interp (l : PL) : alpha ℤ (interp l) = alphaL l := by
  simp [alpha_apply, alphaL, coeff_interp]

/-- The eight values of `α` on the products of `e`'s of bidegree `(2,2)`, all divisible
by `3`. -/
theorem alpha_e_products :
    alpha ℤ (e 0 1 ^ 2 * e 1 0 ^ 2) = -21 ∧ alpha ℤ (e 0 1 ^ 2 * e 2 0) = -6 ∧
    alpha ℤ (e 0 1 * e 1 0 * e 1 1) = -12 ∧ alpha ℤ (e 0 1 * e 2 1) = 0 ∧
    alpha ℤ (e 0 2 * e 1 0 ^ 2) = -9 ∧ alpha ℤ (e 0 2 * e 2 0) = -3 ∧
    alpha ℤ (e 1 0 * e 1 2) = -3 ∧ alpha ℤ (e 1 1 ^ 2) = -9 := by
  simp only [e, ← interp_powL, ← interp_mulL, alpha_interp]
  decide +kernel

/-! ### Bidegrees -/

/-- The bidegree of an exponent: total degree in the `x`'s and in the `y`'s. -/
def tot (f : Exp) : ℕ × ℕ := f 0 + f 1 + f 2

/-- Every monomial of the list has bidegree `δ`. -/
def Homog (l : PL) (δ : ℕ × ℕ) : Prop := ∀ t ∈ l, tot t.1 = δ

/-- Bidegrees add under `mulL`. -/
theorem homog_mulL {l₁ l₂ : PL} {δ₁ δ₂ : ℕ × ℕ} (h₁ : Homog l₁ δ₁) (h₂ : Homog l₂ δ₂) :
    Homog (mulL l₁ l₂) (δ₁ + δ₂) := by
  intro t ht
  simp only [mulL, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨a, ha, b, hb, rfl⟩ := ht
  rw [← h₁ a ha, ← h₂ b hb]
  simp only [tot, Pi.add_apply]
  abel

/-- `oneL` has bidegree `0`. -/
theorem homog_oneL : Homog oneL 0 := by simp [Homog, oneL, tot]

/-- Bidegrees multiply under `powL`. -/
theorem homog_powL {l : PL} {δ : ℕ × ℕ} (h : Homog l δ) (k : ℕ) : Homog (powL l k) (k • δ) := by
  induction k with
  | zero => simpa [powL] using homog_oneL
  | succ k ih => rw [powL, succ_nsmul']; exact homog_mulL h ih

/-- Bidegrees add under `prodL`. -/
theorem homog_prodL {ι : Type*} (l : List ι) (F : ι → PL) (D : ι → ℕ × ℕ)
    (h : ∀ x ∈ l, Homog (F x) (D x)) : Homog (prodL (l.map F)) ((l.map D).sum) := by
  induction l with
  | nil => simpa [prodL] using homog_oneL
  | cons x l ih =>
    simp only [List.map_cons, prodL, List.sum_cons]
    exact homog_mulL (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- `α` vanishes on a list all of whose monomials have a bidegree other than `(2,2)`. -/
theorem alphaL_eq_zero {l : PL} {δ : ℕ × ℕ} (h : Homog l δ) (hδ : δ ≠ (2, 2)) : alphaL l = 0 := by
  have hc : ∀ i : Fin 8, tot (toExp (certσ i)) = (2, 2) := by decide +kernel
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [coeffL, List.sum_eq_zero, mul_zero]
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  refine ite_eq_right_iff.2 fun heq => absurd ((h t ht).symm.trans (by rw [heq]; exact hc i)) hδ

/-! ### The nine generators and the divisibility by `3` -/

/-- The bidegrees of the nine nonconstant elementary multisymmetric polynomials. -/
def deg : Fin 9 → ℕ × ℕ := ![(1,0), (0,1), (2,0), (1,1), (0,2), (3,0), (2,1), (1,2), (0,3)]

/-- The nine nonconstant elementary multisymmetric polynomials. -/
noncomputable def eJ (j : Fin 9) : MvPolynomial V ℤ := e (deg j).1 (deg j).2

/-- The list of `∏ⱼ eJ j ^ n j`. -/
def bigL (n : Fin 9 → ℕ) : PL :=
  prodL ((List.finRange 9).map fun j => powL (le (deg j).1 (deg j).2) (n j))

/-- `α` of a product of the generators, computed on lists. -/
theorem alpha_prod_eJ (n : Fin 9 → ℕ) : alpha ℤ (∏ j, eJ j ^ n j) = alphaL (bigL n) := by
  rw [Fin.prod_univ_def, ← alpha_interp, bigL, interp_prodL, List.map_map]
  refine congrArg (fun L => alpha ℤ L.prod) (List.map_congr_left fun j _ => ?_)
  simp [eJ, e, interp_powL]

/-- `∏ⱼ eJ j ^ n j` has bidegree `∑ⱼ n j • deg j`. -/
theorem homog_bigL (n : Fin 9 → ℕ) : Homog (bigL n) (∑ j, n j • deg j) := by
  rw [Fin.sum_univ_def]
  have hl : ∀ j : Fin 9, Homog (le (deg j).1 (deg j).2) (deg j) := by
    unfold Homog; decide +kernel
  exact homog_prodL _ _ _ fun j _ => homog_powL (hl j) (n j)

/-- `α` of any product of the `e`'s is divisible by `3`. -/
theorem three_dvd_alpha_prod (n : Fin 9 → ℕ) : 3 ∣ alpha ℤ (∏ j, eJ j ^ n j) := by
  rw [alpha_prod_eJ]
  by_cases h : ∑ j, n j • deg j = (2, 2)
  · have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    simp [Fin.sum_univ_succ, deg] at hx hy
    -- the eight solutions of the two equations, found by splitting on `n 3`, `n 7`, `n 6`,
    -- `n 2` and `n 4`; in each, `n` is determined and the value of `α` is computed
    have leaf : ∀ v : Fin 9 → ℕ, (n 0 = v 0 ∧ n 1 = v 1 ∧ n 2 = v 2 ∧ n 3 = v 3 ∧ n 4 = v 4 ∧
        n 5 = v 5 ∧ n 6 = v 6 ∧ n 7 = v 7 ∧ n 8 = v 8) → 3 ∣ alphaL (bigL v) →
        3 ∣ alphaL (bigL n) := by
      rintro v ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ h
      rwa [show n = v by funext j; fin_cases j <;> assumption]
    have h5 : n 5 = 0 := by omega
    have h8 : n 8 = 0 := by omega
    rcases (show n 3 = 0 ∨ n 3 = 1 ∨ n 3 = 2 by omega) with h3 | h3 | h3
    · rcases (show n 7 = 0 ∨ n 7 = 1 by omega) with h7 | h7
      · rcases (show n 6 = 0 ∨ n 6 = 1 by omega) with h6 | h6
        · rcases (show n 2 = 0 ∨ n 2 = 1 by omega) with h2 | h2 <;>
          rcases (show n 4 = 0 ∨ n 4 = 1 by omega) with h4 | h4
          · refine leaf ![2, 2, 0, 0, 0, 0, 0, 0, 0] ?_ (by decide +kernel)
            simp
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
          · refine leaf ![2, 0, 0, 0, 1, 0, 0, 0, 0] ?_ (by decide +kernel)
            simp
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
          · refine leaf ![0, 2, 1, 0, 0, 0, 0, 0, 0] ?_ (by decide +kernel)
            simp
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
          · refine leaf ![0, 0, 1, 0, 1, 0, 0, 0, 0] ?_ (by decide +kernel)
            simp
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
        · refine leaf ![0, 1, 0, 0, 0, 0, 1, 0, 0] ?_ (by decide +kernel)
          simp
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
      · refine leaf ![1, 0, 0, 0, 0, 0, 0, 1, 0] ?_ (by decide +kernel)
        simp
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    · have h7 : n 7 = 0 := by omega
      have h0 : n 0 = 1 := by omega
      refine leaf ![1, 1, 0, 1, 0, 0, 0, 0, 0] ?_ (by decide +kernel)
      simp
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
    · refine leaf ![0, 0, 0, 2, 0, 0, 0, 0, 0] ?_ (by decide +kernel)
      simp
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · rw [alphaL_eq_zero (homog_bigL n) h]
    exact dvd_zero 3

/-- `α` is divisible by `3` on every integral polynomial in the `e`'s. -/
theorem three_dvd_alpha_aeval (G : MvPolynomial (Fin 9) ℤ) : 3 ∣ alpha ℤ (aeval eJ G) := by
  rw [G.as_sum, map_sum, map_sum]
  refine Finset.dvd_sum fun s _ => ?_
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ← Algebra.smul_def,
    map_smul, smul_eq_mul]
  exact Dvd.dvd.mul_left (three_dvd_alpha_prod _) _

/-! ### The product -/

/-- The Chow form of the Segre product, dehomogenised: `T = ∏ᵢⱼ (1 + cᵢ aⱼ + dᵢ bⱼ)`. -/
noncomputable def T : S :=
  ∏ i : Fin 3, ∏ j : Fin 3, (1 + C (X (i, 0)) * X (j, 0) + C (X (i, 1)) * X (j, 1))

/-- `T = ∏ⱼ (∑ e p q (c, d) aⱼᵖ bⱼ^q)`, expanded. -/
theorem T_eq_sum : T = ∑ σ : Fin 3 → Fin 4 × Fin 4,
    C (∏ j, e (σ j).1 (σ j).2) * mon Rcd (toExp σ) := by
  rw [T, Finset.prod_comm]
  simp_rw [prod_eq_sum_e]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [mon, toExp, map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun _ _ => by ring

-- the kernel check of this proof unfolds the nested polynomial instances deeply
set_option maxRecDepth 100000 in
/-- The coefficient of `T` at an exponent with entries `< 4` is the product of the `e`'s of the
cycle `(c, d)` indexed by it. -/
theorem coeff_T (σ₀ : Fin 3 → Fin 4 × Fin 4) :
    T.coeff (mono (toExp σ₀)) = ∏ j, e (σ₀ j).1 (σ₀ j).2 := by
  rw [T_eq_sum, coeff_sum, Finset.sum_eq_single σ₀]
  · rw [coeff_C_mul, coeff_mon, ite_eq_left rfl, mul_one]
  · intro σ _ hne
    rw [coeff_C_mul, coeff_mon, ite_eq_right (fun h => hne (toExp_injective h)), mul_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- The linear form `β = α ⊗ α` on `ℤ[c, d][a, b]`. -/
noncomputable def beta : S →ₗ[ℤ] ℤ := alpha ℤ ∘ₗ (alpha Rcd).restrictScalars ℤ

/-- `α` of a product of three `e`'s, computed on lists. -/
theorem alpha_prod_e (σ : Fin 3 → Fin 4 × Fin 4) :
    alpha ℤ (∏ j, e (σ j).1 (σ j).2) =
      alphaL (prodL ((List.finRange 3).map fun j => le (σ j).1 (σ j).2)) := by
  rw [Fin.prod_univ_def, ← alpha_interp, interp_prodL, List.map_map]
  rfl

/-- `β T = 39`. -/
theorem beta_T : beta T = 39 := by
  have h : alpha Rcd T = ∑ i, (certW i : Rcd) * ∏ j, e (certσ i j).1 (certσ i j).2 := by
    simp only [alpha_apply, coeff_T]
  simp only [beta, LinearMap.comp_apply, LinearMap.restrictScalars_apply, h, map_sum,
    ← zsmul_eq_mul, map_zsmul, smul_eq_mul, alpha_prod_e]
  decide +kernel

/-- The `e`'s of the cycle `(c, d)`. -/
noncomputable def gA (j : Fin 9) : S := C (eJ j)

/-- The `e`'s of the cycle `(a, b)`. -/
noncomputable def gB (j : Fin 9) : S := map (algebraMap ℤ Rcd) (eJ j)

/-- `β` of a product of a polynomial in `(c, d)` and a polynomial in `(a, b)`. -/
theorem beta_C_mul_map (a b : Rcd) :
    beta (C a * map (algebraMap ℤ Rcd) b) = alpha ℤ a * alpha ℤ b := by
  have h : alpha Rcd (C a * map (algebraMap ℤ Rcd) b) = a * C (alpha ℤ b) := by
    simp only [alpha_apply, coeff_C_mul, coeff_map, map_sum, Finset.mul_sum, map_mul, map_intCast,
      eq_intCast]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [beta, LinearMap.comp_apply, LinearMap.restrictScalars_apply, h, alpha_apply,
    mul_comm a, coeff_C_mul, Finset.sum_mul, Int.cast_id]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [← Finset.sum_mul]
  ring

/-- `β` is divisible by `9` on every integral polynomial in the `e`'s of both cycles. -/
theorem nine_dvd_beta_aeval (G : MvPolynomial (Fin 9 ⊕ Fin 9) ℤ) :
    9 ∣ beta (aeval (Sum.elim gA gB) G) := by
  rw [G.as_sum, map_sum, map_sum]
  refine Finset.dvd_sum fun s _ => ?_
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, gA, gB, ← map_pow, ← map_prod]
  rw [← Algebra.smul_def, map_smul, smul_eq_mul, beta_C_mul_map]
  exact Dvd.dvd.mul_left (mul_dvd_mul (three_dvd_alpha_prod _) (three_dvd_alpha_prod _)) _

/-- **The guess of p. 82 fails for zero-cycles over `ℤ`.** No polynomial with integer
coefficients in the elementary multisymmetric functions of two cycles of three points gives the
Chow form of their product. -/
theorem not_exists_integral_formula :
    ¬ ∃ G : MvPolynomial (Fin 9 ⊕ Fin 9) ℤ, aeval (Sum.elim gA gB) G = T := by
  rintro ⟨G, hG⟩
  have := nine_dvd_beta_aeval G
  rw [hG, beta_T] at this
  omega

/-- The same statement: `T` is not in the subring generated by the `e`'s of both cycles. -/
theorem T_not_mem_adjoin : T ∉ Algebra.adjoin ℤ (Set.range (Sum.elim gA gB)) := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  rintro ⟨G, hG⟩
  exact not_exists_integral_formula ⟨G, hG⟩

end Bourbaki.Redaction197Chow
