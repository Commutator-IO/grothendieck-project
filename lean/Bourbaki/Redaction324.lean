import Mathlib

/-!
# Bourbaki rédaction n° 324: constant rank in characteristic `p`, over an imperfect field

Rédaction n° 324 of the Bourbaki archive (J.-P. Serre, *Variétés différentiables et
analytiques, fascicule de résultats (état 1)*, June 1959; Archives Henri Poincaré, item
<https://archives-bourbaki.ahp-numerique.fr/items/show/755>) states in § 4, n° 9 (p. 44–45 of
the facsimile), for analytic manifolds over a complete valued field of characteristic zero,
that a map has rank `r` near a point if and only if it reads `z'ᵢ = zᵢ` (`i ≤ r`), `z'ᵢ = 0`
(`i > r`) in suitable local coordinates. The rédacteur's end note to that number (p. 94)
observes that in characteristic `p` the first condition no longer implies the second
(`x ↦ x ^ p` has rank zero everywhere), proposes to characterise instead the maps that read
`z'ᵢ = zᵢ ^ (p ^ k(i))` (`i ≤ r`), `z'ᵢ = 0` (`i > r`) in local coordinates, and asks whether
they are exactly the maps of locally constant rank « for derivations of every height ».

Over an imperfect field the answer is no. Let `K` have characteristic `2` and let `t ∈ K` not be
a square (for instance `K = 𝔽₂((t))`). The polynomial map `f (x, y) = x ² + t y ²` from `K²` to
`K` is additive, so it looks the same at every point (`f (P + h) = f P + f h`): any local
invariant built from its derivatives of any order, invariant under translations, is constant.
Its differential vanishes everywhere. But it is injective, whereas a map of the proposed
normal form from a 2-dimensional source to a 1-dimensional target only depends, near a point,
on one coordinate, and so is not injective on any neighbourhood.

* `sqForm t`: the map `(x, y) ↦ x ^ 2 + t * y ^ 2`;
* `sqForm_add`: in characteristic `2` it is additive, hence translation-homogeneous;
* `hasFDerivAt_sqForm`: over a nontrivially normed field of characteristic `2`, its
  derivative is zero at every point;
* `sqForm_injective`: if `t` is not a square, it is injective;
* `not_injOn_of_factor_fst`: over a field without isolated points, a map `f` on an open set
  `U` such that `ψ ∘ f = g ∘ fst ∘ φ` on `U`, with `ψ` injective on `f '' U` and `φ '' U`
  open, is not injective on `U` (this covers the normal form with `r ≤ 1`, the only case for
  a 1-dimensional target: `g z = z ^ (2 ^ k)` or `g = 0`);
* `sqForm_not_normalForm`: hence `sqForm t` admits no such local expression near any point;
* `laurent_X_not_square`, `sqForm_laurent_injective`: the example `K = 𝔽₂((X))`, `t = X`.

Here a chart is modelled only by what the argument uses (`φ` with open image of `U`); the
analytic manifold structure is not formalised.
-/

open Filter Topology

noncomputable section

namespace Bourbaki.Redaction324

variable {K : Type*}

/-- The map `(x, y) ↦ x ^ 2 + t * y ^ 2`. -/
def sqForm [Field K] (t : K) (p : K × K) : K := p.1 ^ 2 + t * p.2 ^ 2

/-- **The map is additive** in characteristic `2`, hence the same at every point up to
translations. -/
theorem sqForm_add [Field K] [CharP K 2] (t : K) (p q : K × K) :
    sqForm t (p + q) = sqForm t p + sqForm t q := by
  simp only [sqForm, Prod.fst_add, Prod.snd_add, CharTwo.add_sq]
  ring

/-- **The derivative vanishes everywhere.** -/
theorem hasFDerivAt_sqForm [NontriviallyNormedField K] [CharP K 2] (t : K) (P : K × K) :
    HasFDerivAt (sqForm t) (0 : K × K →L[K] K) P := by
  have h := ((hasFDerivAt_fst (𝕜 := K) (p := P)).pow 2).add
    (((hasFDerivAt_snd (𝕜 := K) (p := P)).pow 2).const_mul t)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  convert h using 1
  · funext v
    rfl
  · ext <;> simp [nsmul_eq_mul, h2]

/-- **The map is injective** when `t` is not a square. -/
theorem sqForm_injective [Field K] [CharP K 2] {t : K} (ht : ∀ s : K, s ^ 2 ≠ t) :
    Function.Injective (sqForm t) := by
  have h0 : ∀ p : K × K, sqForm t p = 0 → p = 0 := by
    rintro ⟨x, y⟩ hp
    simp only [sqForm] at hp
    by_cases hy : y = 0
    · subst hy
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        add_zero, pow_eq_zero_iff] at hp
      simp [hp]
    · exfalso
      apply ht (x / y)
      have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
      have hx : x ^ 2 = -(t * y ^ 2) := eq_neg_of_add_eq_zero_left hp
      rw [div_pow, hx, CharTwo.neg_eq, mul_div_assoc, div_self hy2, mul_one]
  intro p q hpq
  have : sqForm t (p + q) = 0 := by
    rw [sqForm_add, hpq, CharTwo.add_self_eq_zero]
  have hpq0 := h0 _ this
  rw [← CharTwo.sub_eq_add, sub_eq_zero] at hpq0
  exact hpq0

/-- **A map that only depends on one coordinate of a chart is not injective**: over a field
without isolated points, if `ψ (f p) = g (φ p).1` for `p ∈ U`, with `U` nonempty, `ψ` injective
on `f '' U` and `φ '' U` open, then `f` is not injective on `U`. -/
theorem not_injOn_of_factor_fst [TopologicalSpace K] [∀ x : K, NeBot (𝓝[≠] x)]
    {Y Z : Type*} (f : K × K → Y) (U : Set (K × K)) (hU : U.Nonempty)
    (φ : K × K → K × K) (hφU : IsOpen (φ '' U)) (ψ : Y → Z) (hψ : Set.InjOn ψ (f '' U))
    (g : K → Z) (hfac : ∀ p ∈ U, ψ (f p) = g (φ p).1) : ¬ Set.InjOn f U := by
  intro hf
  obtain ⟨p, hp⟩ := hU
  set a := (φ p).1
  set b := (φ p).2
  have hab : (a, b) ∈ φ '' U := ⟨p, hp, rfl⟩
  have hs : {c : K | (a, c) ∈ φ '' U} ∈ 𝓝 b :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hφU.mem_nhds hab)
  have hs' : {c : K | (a, c) ∈ φ '' U} ∈ 𝓝[≠] b := mem_nhdsWithin_of_mem_nhds hs
  obtain ⟨c, hc, hcb⟩ := Filter.nonempty_of_mem (Filter.inter_mem hs' self_mem_nhdsWithin)
  obtain ⟨q, hq, hφq⟩ := hc
  have hfq : f p = f q :=
    hψ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩ (by rw [hfac p hp, hfac q hq, hφq])
  have hpq : p = q := hf hp hq hfq
  apply hcb
  change c = b
  rw [show c = (φ q).2 by rw [hφq], ← hpq]

/-- **The proposed normal form fails for `sqForm t`**: over a nontrivially normed field of
characteristic `2` where `t` is not a square, `sqForm t` has, on no nonempty open set, an
expression `ψ ∘ sqForm t = g ∘ fst ∘ φ` with `ψ` injective on the image and `φ` open on it. -/
theorem sqForm_not_normalForm [NontriviallyNormedField K] [CharP K 2] {t : K}
    (ht : ∀ s : K, s ^ 2 ≠ t) {Z : Type*} (U : Set (K × K)) (hU : U.Nonempty)
    (φ : K × K → K × K) (hφU : IsOpen (φ '' U)) (ψ : K → Z)
    (hψ : Set.InjOn ψ (sqForm t '' U)) (g : K → Z) :
    ¬ ∀ p ∈ U, ψ (sqForm t p) = g (φ p).1 := fun hfac =>
  not_injOn_of_factor_fst (sqForm t) U hU φ hφU ψ hψ g hfac
    (sqForm_injective ht).injOn

/-- In `𝔽₂((X))`, the variable `X` is not a square: a square has even order. -/
theorem laurent_X_not_square (s : LaurentSeries (ZMod 2)) :
    s ^ 2 ≠ HahnSeries.single 1 1 := by
  intro h
  have h1 := congrArg HahnSeries.order h
  rw [HahnSeries.order_pow, HahnSeries.order_single one_ne_zero, nsmul_eq_mul] at h1
  push_cast at h1
  omega

instance : CharP (LaurentSeries (ZMod 2)) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) _).injective 2

/-- Over `𝔽₂((X))`, the map `(x, y) ↦ x ^ 2 + X y ^ 2` is injective. -/
theorem sqForm_laurent_injective :
    Function.Injective (sqForm (HahnSeries.single 1 1 : LaurentSeries (ZMod 2))) :=
  sqForm_injective laurent_X_not_square

end Bourbaki.Redaction324

end
