import Bourbaki.Upstream.ResultantProdXSubC

/-!
# Bourbaki rédaction n° 197: the Chow form of a product of point sets as a resultant

Rédaction n° 197 of the Bourbaki archive (P. Samuel, May 1954; Archives Henri Poincaré, item
<https://archives-bourbaki.ahp-numerique.fr/items/show/612>) treats the Chow coordinates of
cycles in projective space. Page 82 first completes a proof: the equation of the semi-generic
projection of a product `X × Y` is obtained from those of `X` and of `Y` as a resultant, after an
affine change of variable that makes the roots add up. The companion file
`Bourbaki/Redaction197Chow.lean` shows that the Chow coordinates of the Segre product are not
integral polynomials in those of the factors; this file proves the identity behind the
resultant, which for zero-cycles of affine space does give a universal integral formula (for the
projective closure of `X × Y` in `𝔸ⁿ⁺ᵐ`, not for its Segre embedding).

For finite sets `X = {xᵢ} ⊂ 𝔸ⁿ` and `Y = {yⱼ} ⊂ 𝔸ᵐ`, write `R_X(t, u) = ∏ᵢ (t + u·xᵢ)` and
`R_Y(t, v) = ∏ⱼ (t + v·yⱼ)`. The Chow form of the product is
`∏ᵢⱼ (u₀ + u·xᵢ + v·yⱼ) = Res_z(R_X(z, u), R_Y(u₀ − z, v))`. The question whether such a
formula exists is asked on MathOverflow, question 354568.

Mathlib's `Polynomial.resultant f g m n` is the determinant of the Sylvester matrix of `f` and
`g` taken as polynomials of formal degrees `m` and `n` (by default their `natDegree`s), with the
convention `Res(X - r, g) = g(r)` (`Polynomial.resultant_X_sub_C_left`).

* `resultant_prod_X_sub_C`: over any commutative ring, for `P = ∏ᵢ (X − αᵢ)` and any `Q` of
  formal degree `n ≥ deg Q`, `Res(P, Q) = ∏ᵢ Q(αᵢ)`. Mathlib proves this over a domain for a
  split polynomial (`Polynomial.resultant_eq_prod_eval`); here it follows from multiplicativity
  (`Polynomial.resultant_prod_left`) with no hypothesis on the ring.
* `prod_add_add_eq_resultant`: the composed-sum identity
  `∏ᵢⱼ (t + aᵢ + bⱼ) = Res_z(∏ᵢ (z + aᵢ), ∏ⱼ (t − z + bⱼ))` for `t` in the ring;
* `prod_X_add_add_eq_resultant`: the same identity over the polynomial ring in `t`;
* `chowForm_product_eq_resultant`: the identity of the page for point sets, with `u·xᵢ` and
  `v·yⱼ` the linear forms `∑ₖ uₖ xᵢₖ` and `∑ₗ vₗ yⱼₗ`.

The link between `∏ᵢⱼ (u₀ + u·xᵢ + v·yⱼ)` and the Chow form of the projective closure of the
product (the dehomogenised Chow form of a zero-cycle is the product of the linear forms at its
points) is not formalised.

The general statements live in `Bourbaki/Upstream/ResultantProdXSubC.lean`
(`Polynomial.resultant_prod_X_sub_C_left`, `Polynomial.resultant_prod_X_sub_C_left'`,
`Polynomial.prod_add_add_eq_resultant`, `Polynomial.prod_X_add_add_eq_resultant`); the degree
of `∏ᵢ (X − αᵢ)` is Mathlib's `Polynomial.natDegree_finsetProd_X_sub_C_eq_card`. The names below
are kept for the articles.
-/

open Polynomial

namespace Bourbaki.Redaction197Resultant

variable {R : Type*} [CommRing R] {ι κ : Type*}

/-- The polynomial `∏ᵢ (X − αᵢ)` has degree the number of factors (over a nontrivial ring). -/
theorem natDegree_prod_X_sub_C [Nontrivial R] (s : Finset ι) (α : ι → R) :
    (∏ i ∈ s, (X - C (α i))).natDegree = s.card :=
  natDegree_finsetProd_X_sub_C_eq_card s α

/-- **Resultant against a product of linear factors**, over any commutative ring:
`Res(∏ᵢ (X − αᵢ), Q) = ∏ᵢ Q(αᵢ)` for a formal degree `n ≥ deg Q`. -/
theorem resultant_prod_X_sub_C (s : Finset ι) (α : ι → R) (Q : R[X]) (n : ℕ)
    (hn : Q.natDegree ≤ n) :
    (∏ i ∈ s, (X - C (α i))).resultant Q (∏ i ∈ s, (X - C (α i))).natDegree n =
      ∏ i ∈ s, Q.eval (α i) :=
  resultant_prod_X_sub_C_left s α Q n hn

/-- The same, with the formal degrees left at their defaults. -/
theorem resultant_prod_X_sub_C' (s : Finset ι) (α : ι → R) (Q : R[X]) :
    (∏ i ∈ s, (X - C (α i))).resultant Q = ∏ i ∈ s, Q.eval (α i) :=
  resultant_prod_X_sub_C_left' s α Q

/-- **Composed sum as a resultant** (énoncé de l'édition): for `t` and families `aᵢ`, `bⱼ` of a
commutative ring, `∏ᵢⱼ (t + aᵢ + bⱼ) = Res_z(∏ᵢ (z + aᵢ), ∏ⱼ (t − z + bⱼ))`. The roots
`−aᵢ` of the first factor are carried by the second to `∏ⱼ (t + aᵢ + bⱼ)`: the roots add up. -/
theorem prod_add_add_eq_resultant (s : Finset ι) (t' : Finset κ) (a : ι → R) (b : κ → R)
    (t : R) :
    ∏ i ∈ s, ∏ j ∈ t', (t + a i + b j) =
      (∏ i ∈ s, (X + C (a i))).resultant (∏ j ∈ t', (C t - X + C (b j))) :=
  Polynomial.prod_add_add_eq_resultant s t' a b t

/-- **Composed sum over the polynomial ring in `t`**: in `R[t]`, with `t = X`,
`∏ᵢⱼ (t + aᵢ + bⱼ) = Res_z(∏ᵢ (z + aᵢ), ∏ⱼ (t − z + bⱼ))`, the resultant being taken in
`R[t][z]`. -/
theorem prod_X_add_add_eq_resultant (s : Finset ι) (t' : Finset κ) (a : ι → R) (b : κ → R) :
    ∏ i ∈ s, ∏ j ∈ t', (X + C (a i) + C (b j) : R[X]) =
      (∏ i ∈ s, (X + C (C (a i)) : R[X][X])).resultant
        (∏ j ∈ t', (C X - X + C (C (b j)))) :=
  Polynomial.prod_X_add_add_eq_resultant s t' a b

/-- **The identity of the page for point sets** (énoncé de l'édition): for points `xᵢ ∈ Rⁿ`
and `yⱼ ∈ Rᵐ`, coefficients `u ∈ Rⁿ`, `v ∈ Rᵐ` and `u₀ ∈ R`, with `R_X(z) = ∏ᵢ (z + u·xᵢ)` and
`R_Y(z) = ∏ⱼ (z + v·yⱼ)`, the product `∏ᵢⱼ (u₀ + u·xᵢ + v·yⱼ)` is the resultant
`Res_z(R_X(z), R_Y(u₀ − z))`. Taking `R` a polynomial ring in the `u`, `v` and `u₀`, this is
the identity between polynomials. -/
theorem chowForm_product_eq_resultant {n m : ℕ} (s : Finset ι) (t' : Finset κ)
    (x : ι → Fin n → R) (y : κ → Fin m → R) (u₀ : R) (u : Fin n → R) (v : Fin m → R) :
    ∏ i ∈ s, ∏ j ∈ t', (u₀ + ∑ k, u k * x i k + ∑ l, v l * y j l) =
      (∏ i ∈ s, (X + C (∑ k, u k * x i k))).resultant
        ((∏ j ∈ t', (X + C (∑ l, v l * y j l))).comp (C u₀ - X)) := by
  have h : (∏ j ∈ t', (X + C (∑ l, v l * y j l))).comp (C u₀ - X) =
      ∏ j ∈ t', (C u₀ - X + C (∑ l, v l * y j l)) := by
    simp only [prod_comp, add_comp, X_comp, C_comp]
  rw [h, prod_add_add_eq_resultant]

end Bourbaki.Redaction197Resultant
