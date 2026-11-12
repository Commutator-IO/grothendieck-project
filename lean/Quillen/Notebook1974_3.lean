import Mathlib

/-!
# Quillen, notebook 1974-3, p. 5: the unique Bézout partner of degree less than `deg f`

Daniel Quillen's research notebook 1974-3 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201974/1974-3.pdf>) proves, on
pp. 4–6 (February 1974), that the poset of unimodular subspaces of `k[t]²` is contractible, by
retracting the subspaces whose lines have denominators of degree `n + 1` onto those of degree
`≤ n`. A line other than the base line is spanned by `(f, g)`, with `f, g ∈ k[t]` coprime and
`f ≠ 0`. On p. 5 he proves that there is a unique pair `(f', g')` with `f g' − f' g = 1` and
`deg f' < deg f`: existence from Bézout after reducing `f'` modulo `f`; uniqueness because a
second pair gives `f (g'₁ − g'₂) = (f'₁ − f'₂) g`, so `f ∣ f'₁ − f'₂`. A struck-out clause adds
« in fact `deg f' = n − 1` »; it is false in general.

* `exists_unique_bezout`: **the statement of the page**, over any field;
* `not_degree_eq_pred`: the struck clause fails: for `f = t²`, `g = 1` the pair is `(−1, 0)`,
  and `deg f' = 0 ≠ 1`.
-/

namespace Quillen.Notebook1974_3

open Polynomial

variable {k : Type*} [Field k]

/-- **Quillen, notebook 1974-3, p. 5.** For coprime `f, g ∈ k[t]` with `f ≠ 0` there is a
unique pair `(f', g')` with `f g' − f' g = 1` and `deg f' < deg f`. -/
theorem exists_unique_bezout {f g : k[X]} (hfg : IsCoprime f g) (hf : f ≠ 0) :
    ∃! p : k[X] × k[X], f * p.2 - p.1 * g = 1 ∧ p.1.degree < f.degree := by
  obtain ⟨a, b, hab⟩ := hfg
  refine ⟨((-b) % f, a - ((-b) / f) * g), ⟨?_, degree_mod_lt _ hf⟩, ?_⟩
  · have h := EuclideanDomain.div_add_mod (-b) f
    have : (-b) % f = -b - f * ((-b) / f) := by linear_combination h
    simp only
    rw [this]
    linear_combination hab
  · rintro ⟨f', g'⟩ ⟨h1, h2⟩
    have h := EuclideanDomain.div_add_mod (-b) f
    set f₀ := (-b) % f
    set g₀ := a - ((-b) / f) * g
    have h0 : f * g₀ - f₀ * g = 1 := by
      have : f₀ = -b - f * ((-b) / f) := by linear_combination h
      simp only [g₀]; rw [this]; linear_combination hab
    have hdvd : f ∣ (f' - f₀) * g := ⟨g' - g₀, by linear_combination h0 - h1⟩
    have hcop : IsCoprime f g := ⟨a, b, hab⟩
    have hd : f ∣ f' - f₀ := hcop.dvd_of_dvd_mul_right hdvd
    have hlt : (f' - f₀).degree < f.degree :=
      lt_of_le_of_lt (degree_sub_le _ _) (max_lt h2 (degree_mod_lt _ hf))
    have hf' : f' = f₀ := sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt hd hlt)
    have hg' : g' = g₀ := by
      have : f * (g' - g₀) = 0 := by rw [hf'] at h1; linear_combination h1 - h0
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hf)
    rw [hf', hg']

/-- **The struck clause fails**: for `f = t²` and `g = 1`, the pair of the page is `(−1, 0)`,
whose first entry has degree `0`, not `deg f − 1 = 1`. -/
theorem not_degree_eq_pred :
    (X ^ 2 : k[X]) * 0 - (-1) * 1 = 1 ∧ (-1 : k[X]).degree < (X ^ 2 : k[X]).degree ∧
      (-1 : k[X]).degree ≠ 1 := by
  refine ⟨by ring, ?_, ?_⟩
  · rw [degree_neg, degree_one, degree_X_pow]; exact_mod_cast (by norm_num : (0 : ℕ) < 2)
  · rw [degree_neg, degree_one]; exact_mod_cast (by norm_num : (0 : ℕ) ≠ 1)

end Quillen.Notebook1974_3
