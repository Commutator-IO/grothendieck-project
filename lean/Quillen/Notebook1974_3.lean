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
  obtain ⟨a, b, hab⟩ := id hfg
  have h0 : f * (a - (-b) / f * g) - (-b) % f * g = 1 := by
    linear_combination hab - g * EuclideanDomain.div_add_mod (-b) f
  refine ⟨((-b) % f, a - (-b) / f * g), ⟨h0, degree_mod_lt _ hf⟩, ?_⟩
  rintro ⟨f', g'⟩ ⟨h1, h2⟩
  have hf' : f' = (-b) % f := sub_eq_zero.mp <| eq_zero_of_dvd_of_degree_lt
    (hfg.dvd_of_dvd_mul_right ⟨g' - (a - (-b) / f * g), by linear_combination h0 - h1⟩)
    ((degree_sub_le _ _).trans_lt (max_lt h2 (degree_mod_lt _ hf)))
  have : f * (g' - (a - (-b) / f * g)) = 0 := by rw [hf'] at h1; linear_combination h1 - h0
  rw [hf', sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hf)]

/-- **The struck clause fails**: for `f = t²` and `g = 1`, the pair of the page is `(−1, 0)`,
whose first entry has degree `0`, not `deg f − 1 = 1`. -/
theorem not_degree_eq_pred :
    (X ^ 2 : k[X]) * 0 - (-1) * 1 = 1 ∧ (-1 : k[X]).degree < (X ^ 2 : k[X]).degree ∧
      (-1 : k[X]).degree ≠ 1 := by
  refine ⟨by ring, ?_, ?_⟩ <;> norm_num [degree_X_pow]

end Quillen.Notebook1974_3
