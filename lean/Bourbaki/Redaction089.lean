import Mathlib

/-!
# Bourbaki rédaction n° 089: positive forms that are not integrals over the spectrum

Rédaction n° 089 of the Bourbaki archive (R. Godement, *Rapport sur la théorie des algèbres
normées*, c. 1948; Archives Henri Poincaré, item
<https://archives-bourbaki.ahp-numerique.fr/items/show/497>) proves, in its chapter II
(pp. 130–133 of the facsimile), that a continuous positive linear form `f` on a complete
commutative normed `*`-algebra with continuous involution is represented on triple products by
a positive measure `μ_f` on the spectrum: `f (x * y * z) = ∫ x̂ ŷ ẑ dμ_f` (formula (52)). The
reporter then asks whether the same holds already for products of two elements (formula (53)),
that is, whether the theorem is stated in its strongest form, and leaves the question open.

The answer is no. In the two-dimensional algebra spanned by `ε` and `ε²` with `ε³ = 0`, with
the involution fixing `ε`, the form « coefficient of `ε²` » is continuous and positive, every
triple product vanishes, and there is no character at all; so (52) holds for every measure,
while `f (ε * ε) = 1` and any integral over the (empty) spectrum is `0`.

* `Nil3`: the space `ℂ × ℂ`, a pair `(a, b)` standing for `a ε + b ε²`, with the product
  `(a ε + b ε²) (c ε + d ε²) = a c ε²`; a complete normed commutative non-unital `ℂ`-algebra
  (`Nil3.instNonUnitalNormedCommRing`) with the involution conjugating both coordinates, which
  is continuous (`Nil3.continuous_star_nil3`);
* `Nil3.mul_mul_eq_zero`: every triple product vanishes;
* `Nil3.characterSpace_eq_empty`: there is no character;
* `Nil3.coeff`: the coefficient of `ε²`, a continuous linear form, positive
  (`Nil3.coeff_star_mul_self_nonneg`) and hermitian (`Nil3.coeff_star`);
* `Nil3.formula52`: formula (52) holds for every measure on the character space;
* `Nil3.not_formula53`: formula (53) fails for every such measure at `x = y = ε`;
* `not_formula53_always`: the strengthened theorem, read as « for every such algebra and form
  there is a measure on the character space satisfying (53) », is false.

The algebra used is radical. The question remains negative for semisimple algebras: on the
functions of class `C²` on `[0, 1]` vanishing at `0`, the form `x ↦ x''(0)` is positive,
kills triple products, and takes the value `2` on `t ↦ t²`; this is not formalised here.
-/

open WeakDual MeasureTheory ComplexOrder

noncomputable section

namespace Bourbaki.Redaction089

/-- The algebra spanned by `ε` and `ε²`, `ε³ = 0`: the pair `(a, b)` stands for `a ε + b ε²`. -/
def Nil3 : Type := ℂ × ℂ

namespace Nil3

/-- The pair of coordinates of an element. -/
def toProd : Nil3 → ℂ × ℂ := id

/-- The element with given coordinates. -/
def mk : ℂ × ℂ → Nil3 := id

instance : NormedAddCommGroup Nil3 := inferInstanceAs (NormedAddCommGroup (ℂ × ℂ))

instance : NormedSpace ℂ Nil3 := inferInstanceAs (NormedSpace ℂ (ℂ × ℂ))

instance : CompleteSpace Nil3 := inferInstanceAs (CompleteSpace (ℂ × ℂ))

@[ext] theorem ext {x y : Nil3} (h1 : (toProd x).1 = (toProd y).1)
    (h2 : (toProd x).2 = (toProd y).2) : x = y :=
  Prod.ext h1 h2

@[simp] theorem toProd_add (x y : Nil3) : toProd (x + y) = toProd x + toProd y := rfl

@[simp] theorem toProd_zero : toProd 0 = 0 := rfl

@[simp] theorem toProd_smul (c : ℂ) (x : Nil3) : toProd (c • x) = c • toProd x := rfl

@[simp] theorem toProd_mk (p : ℂ × ℂ) : toProd (mk p) = p := rfl

/-- The product `(a ε + b ε²) (c ε + d ε²) = a c ε²`. -/
instance : Mul Nil3 := ⟨fun x y => mk (0, (toProd x).1 * (toProd y).1)⟩

@[simp] theorem toProd_mul (x y : Nil3) :
    toProd (x * y) = (0, (toProd x).1 * (toProd y).1) := rfl

instance instNonUnitalNormedCommRing : NonUnitalNormedCommRing Nil3 where
  left_distrib x y z := by ext <;> simp [mul_add]
  right_distrib x y z := by ext <;> simp [add_mul]
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  mul_assoc x y z := by ext <;> simp
  mul_comm x y := by ext <;> simp [mul_comm]
  dist_eq x y := by rw [dist_eq_norm', sub_eq_neg_add]
  norm_mul_le x y := by
    change ‖((0 : ℂ), (toProd x).1 * (toProd y).1)‖ ≤ ‖toProd x‖ * ‖toProd y‖
    rw [Prod.norm_def, norm_zero, norm_mul, max_eq_right (by positivity)]
    exact mul_le_mul (norm_fst_le _) (norm_fst_le _) (norm_nonneg _) (norm_nonneg _)

instance : IsScalarTower ℂ Nil3 Nil3 :=
  ⟨fun c x y => by ext <;> simp [mul_assoc]⟩

instance : SMulCommClass ℂ Nil3 Nil3 :=
  ⟨fun c x y => by ext <;> simp [mul_left_comm]⟩

/-- The involution conjugates both coordinates; it fixes `ε`. -/
instance : StarRing Nil3 where
  star x := mk (star (toProd x).1, star (toProd x).2)
  star_involutive x := by ext <;> simp
  star_mul x y := by ext <;> simp [mul_comm]
  star_add x y := by ext <;> simp

@[simp] theorem toProd_star (x : Nil3) :
    toProd (star x) = (star (toProd x).1, star (toProd x).2) := rfl

instance : StarModule ℂ Nil3 :=
  ⟨fun c x => by ext <;> simp⟩

/-- The involution is continuous. -/
theorem continuous_star_nil3 : Continuous (star : Nil3 → Nil3) := by
  change Continuous fun p : ℂ × ℂ => (star p.1, star p.2)
  exact (Complex.continuous_conj.comp continuous_fst).prodMk
    (Complex.continuous_conj.comp continuous_snd)

instance : ContinuousStar Nil3 := ⟨continuous_star_nil3⟩

/-- The generator `ε`. -/
def eps : Nil3 := mk (1, 0)

/-- **Every triple product vanishes.** -/
theorem mul_mul_eq_zero (x y z : Nil3) : x * y * z = 0 := by
  ext <;> simp

/-- **There is no character**: a character `φ` satisfies `φ x ^ 3 = φ (x * x * x) = 0`. -/
theorem characterSpace_eq_empty : characterSpace ℂ Nil3 = ∅ := by
  ext φ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hφ, hmul⟩
  apply hφ
  refine DFunLike.ext _ _ fun x => ?_
  have h := hmul (x * x) x
  rw [hmul x x, mul_mul_eq_zero, map_zero] at h
  have h3 : (φ x) ^ 3 = 0 := by rw [h]; ring
  exact pow_eq_zero_iff (by norm_num) |>.mp h3

instance : IsEmpty (characterSpace ℂ Nil3) := by
  rw [characterSpace_eq_empty]
  exact Set.isEmpty_coe_sort.mpr rfl

/-- The coefficient of `ε²`, a continuous linear form. -/
def coeff : Nil3 →L[ℂ] ℂ := ContinuousLinearMap.snd ℂ ℂ ℂ

@[simp] theorem coeff_apply (x : Nil3) : coeff x = (toProd x).2 := rfl

/-- The form `coeff` is positive: `coeff (x* x) = |a|²` for `x = a ε + b ε²`. -/
theorem coeff_star_mul_self_nonneg (x : Nil3) : 0 ≤ coeff (star x * x) := by
  simpa using star_mul_self_nonneg (toProd x).1

/-- The form `coeff` is hermitian. -/
theorem coeff_star (x : Nil3) : coeff (star x) = star (coeff x) := rfl

/-- `coeff (ε * ε) = 1`. -/
theorem coeff_eps_mul_eps : coeff (eps * eps) = 1 := by
  simp [eps]

variable [MeasurableSpace (characterSpace ℂ Nil3)]

/-- Any integral over the character space vanishes, the space being empty. -/
theorem integral_eq_zero (μ : Measure (characterSpace ℂ Nil3)) (x : Nil3) :
    ∫ φ, (φ : WeakDual ℂ Nil3) x ∂μ = 0 := by
  rw [Measure.eq_zero_of_isEmpty μ, integral_zero_measure]

/-- **Formula (52) holds for every measure**, both sides being `0`. -/
theorem formula52 (μ : Measure (characterSpace ℂ Nil3)) (x y z : Nil3) :
    coeff (x * y * z) = ∫ φ, (φ : WeakDual ℂ Nil3) (x * y * z) ∂μ := by
  rw [integral_eq_zero, mul_mul_eq_zero, map_zero]

/-- **Formula (53) fails for every measure**, at `x = y = ε`. -/
theorem not_formula53 (μ : Measure (characterSpace ℂ Nil3)) :
    coeff (eps * eps) ≠ ∫ φ, (φ : WeakDual ℂ Nil3) (eps * eps) ∂μ := by
  rw [integral_eq_zero, coeff_eps_mul_eps]
  exact one_ne_zero

end Nil3

open Nil3 in
/-- **The question of p. 133 has a negative answer**: it is not true that for every complete
normed commutative `*`-algebra with continuous involution and every continuous positive form
`f` there is a measure on the character space representing `f` on products of two elements. -/
theorem not_formula53_always :
    ¬ ∀ (A : Type) [NonUnitalNormedCommRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A]
      [SMulCommClass ℂ A A] [CompleteSpace A] [StarRing A] [StarModule ℂ A] [ContinuousStar A]
      [MeasurableSpace (characterSpace ℂ A)] (f : A →L[ℂ] ℂ),
      (∀ x, 0 ≤ f (star x * x)) →
        ∃ μ : Measure (characterSpace ℂ A),
          ∀ x y : A, f (x * y) = ∫ φ, (φ : WeakDual ℂ A) (x * y) ∂μ := by
  intro h
  let _ : MeasurableSpace (characterSpace ℂ Nil3) := ⊤
  obtain ⟨μ, hμ⟩ := h Nil3 coeff coeff_star_mul_self_nonneg
  exact not_formula53 μ (hμ eps eps)

end Bourbaki.Redaction089

end
