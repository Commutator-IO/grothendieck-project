import Mathlib

/-!
# Quillen, notebook 1988-10, pp. 54-55: the contracting homotopy for the tensor algebra

Daniel Quillen's research notebook 1988-10 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201988/1988-10.pdf>),
pp. 54-55. For the tensor algebra `R = T(V)`, the sequence of bimodules
`R^{⊗4} → R^{⊗3} → R ⊗ V ⊗ R → 0`, with the bar differential
`b'(x, y, z, w) = (xy, z, w) − (x, yz, w) + (x, y, zw)` and
`p(x, v₁⋯vₙ, y) = Σᵢ (x v₁⋯v_{i−1}, vᵢ, v_{i+1}⋯vₙ y)`, is exact; Quillen's second proof writes
down bimodule maps `s(1, v, 1) = (1, v, 1)` and
`h(1, v₁⋯vₙ, 1) = (1, v₁⋯vₙ, 1, 1) − Σᵢ (v₁⋯v_{i−1}, vᵢ, v_{i+1}⋯vₙ, 1)` and checks
`pb' = 0`, `ps = id`, `b'h + sp = id`.

*The model.* `V` is free on a type `X` of letters (the case on which the general one rests by
choosing a basis), so `R = T(V)` is free on the words `List X`, `R^{⊗n}` is free on the
`n`-tuples of words, and `R ⊗ V ⊗ R` on the triples (word, letter, word); the coefficients lie in
any commutative ring `k`. A bimodule map is given by its values on the basis, which carry the
outer factors `x`, `y` along (`b'`, `p`, `s`, `h` below). The sums over `i` are written as a
recursion on the word.

* `p_b'` : `p ∘ b' = 0`; `p_s` : `p ∘ s = id`;
* `b'_h_add_s_p` (p. 55): `b' ∘ h + s ∘ p = id`, Quillen's check, by a telescoping induction;
* `exact_at_middle`, `p_surjective` : hence `Im b' = Ker p` and `p` onto, the Proposition.
-/

noncomputable section

namespace Quillen.Notebook1988_10Bar

open Finsupp

variable (k : Type*) [CommRing k] (X : Type*)

/-- `R^{⊗3}`, free on triples of words. -/
abbrev C3 := (List X × List X × List X) →₀ k
/-- `R^{⊗4}`, free on quadruples of words. -/
abbrev C4 := (List X × List X × List X × List X) →₀ k
/-- `R ⊗ V ⊗ R`, free on (word, letter, word). -/
abbrev P := (List X × X × List X) →₀ k

variable {k X}

/-- The basis element `(x, y, z)`. -/
abbrev e3 (x y z : List X) : C3 k X := single (x, y, z) 1
/-- The basis element `(x, y, z, w)`. -/
abbrev e4 (x y z w : List X) : C4 k X := single (x, y, z, w) 1
/-- The basis element `(x, v, y)`. -/
abbrev eP (x : List X) (v : X) (y : List X) : P k X := single (x, v, y) 1

/-- `Σᵢ (x v₁⋯v_{i−1}, vᵢ, v_{i+1}⋯vₙ y)`, by recursion on `w = v₁⋯vₙ`. -/
def pw (x : List X) : List X → List X → P k X
  | [], _ => 0
  | v :: w, y => eP x v (w ++ y) + pw (x ++ [v]) w y

/-- `Σᵢ (x v₁⋯v_{i−1}, vᵢ, v_{i+1}⋯vₙ, y)`. -/
def gw (x : List X) : List X → List X → C4 k X
  | [], _ => 0
  | v :: w, y => e4 x [v] w y + gw (x ++ [v]) w y

variable (k X)

/-- The bar differential `b'`. -/
def b' : C4 k X →ₗ[k] C3 k X :=
  linearCombination k fun q => e3 (q.1 ++ q.2.1) q.2.2.1 q.2.2.2 -
    e3 q.1 (q.2.1 ++ q.2.2.1) q.2.2.2 + e3 q.1 q.2.1 (q.2.2.1 ++ q.2.2.2)

/-- `p : R^{⊗3} → R ⊗ V ⊗ R`. -/
def p : C3 k X →ₗ[k] P k X := linearCombination k fun q => pw q.1 q.2.1 q.2.2

/-- `s(x, v, y) = (x, v, y)`. -/
def s : P k X →ₗ[k] C3 k X := linearCombination k fun q => e3 q.1 [q.2.1] q.2.2

/-- `h(x, w, y) = (x, w, 1, y) − Σᵢ (x v₁⋯v_{i−1}, vᵢ, v_{i+1}⋯vₙ, y)`. -/
def h : C3 k X →ₗ[k] C4 k X := linearCombination k fun q => e4 q.1 q.2.1 [] q.2.2 - gw q.1 q.2.1 q.2.2

variable {k X}

theorem b'_e4 (x y z w : List X) :
    b' k X (e4 x y z w) = e3 (x ++ y) z w - e3 x (y ++ z) w + e3 x y (z ++ w) := by
  simp [b']

theorem p_e3 (x w y : List X) : p k X (e3 x w y) = pw x w y := by simp [p]

theorem s_eP (x : List X) (v : X) (y : List X) : s k X (eP x v y) = e3 x [v] y := by simp [s]

theorem h_e3 (x w y : List X) : h k X (e3 x w y) = e4 x w [] y - gw x w y := by simp [h]

/-- `p(x, yz, w) = p(x, y, zw) + p(xy, z, w)`. -/
theorem pw_append (x : List X) : ∀ (y z w : List X), pw (k := k) x (y ++ z) w =
    pw x y (z ++ w) + pw (x ++ y) z w
  | [], z, w => by simp [pw]
  | v :: y, z, w => by
    simp only [List.cons_append, pw, List.append_assoc, pw_append (x ++ [v]) y z w,
      List.nil_append]
    abel

/-- `p ∘ b' = 0`. -/
theorem p_b' : p k X ∘ₗ b' k X = 0 := by
  apply Finsupp.lhom_ext'
  rintro ⟨x, y, z, w⟩
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply]
  rw [show (single (x, y, z, w) (1 : k)) = e4 x y z w from rfl, b'_e4, map_add, map_sub, p_e3,
    p_e3, p_e3, pw_append]
  abel

/-- `p ∘ s = id`. -/
theorem p_s : p k X ∘ₗ s k X = LinearMap.id := by
  apply Finsupp.lhom_ext'
  rintro ⟨x, v, y⟩
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.id_apply]
  rw [show (single (x, v, y) (1 : k)) = eP x v y from rfl, s_eP, p_e3]
  simp [pw]

/-- The telescoping step: `b'(Σᵢ (x v_{<i}, vᵢ, v_{>i}, y)) = (xw, 1, y) − (x, w, y) + sp(x, w, y)`. -/
theorem b'_gw (x : List X) : ∀ (w y : List X), b' k X (gw x w y) =
    e3 (x ++ w) [] y - e3 x w y + s k X (pw x w y)
  | [], y => by simp [gw, pw]
  | v :: w, y => by
    simp only [gw, pw, map_add, b'_e4, b'_gw (x ++ [v]) w y, s_eP]
    rw [show x ++ [v] ++ w = x ++ v :: w by simp, show [v] ++ w = v :: w from rfl]
    abel

/-- **Quillen, notebook 1988-10, p. 55**: `b' ∘ h + s ∘ p = id` on `R^{⊗3}`, `R = T(V)`. -/
theorem b'_h_add_s_p : b' k X ∘ₗ h k X + s k X ∘ₗ p k X = LinearMap.id := by
  apply Finsupp.lhom_ext'
  rintro ⟨x, w, y⟩
  apply LinearMap.ext_ring
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.id_apply]
  rw [show (single (x, w, y) (1 : k)) = e3 x w y from rfl, h_e3, p_e3, map_sub, b'_e4, b'_gw]
  simp only [List.append_nil]
  abel

/-- **The Proposition of p. 54**: `R^{⊗4} → R^{⊗3} → R ⊗ V ⊗ R` is exact at `R^{⊗3}`. -/
theorem exact_at_middle : LinearMap.range (b' k X) = LinearMap.ker (p k X) := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, p_b', LinearMap.zero_apply]
  · intro c hc
    refine ⟨h k X c, ?_⟩
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mem_ker.1 hc, map_zero,
      add_zero, LinearMap.id_apply] using LinearMap.congr_fun (b'_h_add_s_p (k := k) (X := X)) c

/-- … and `p` is onto, split by `s`. -/
theorem p_surjective : Function.Surjective (p k X) := fun c =>
  ⟨s k X c, by rw [← LinearMap.comp_apply, p_s, LinearMap.id_apply]⟩

end Quillen.Notebook1988_10Bar

end
