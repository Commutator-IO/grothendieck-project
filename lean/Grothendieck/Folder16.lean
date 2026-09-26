import Mathlib.Algebra.Lie.Sl2
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Folder 16: the `𝔰𝔩₂` side of hard Lefschetz, against the folder's pseudo-inverse `Λ`

Issue #26 lists folder 16 in tier 2: « Hard Lefschetz via `𝔰𝔩₂`-representations;
the representation theory is partly there, the geometry is not ». Only the
algebraic `𝔰𝔩₂` statements of `transcripts/16/16.modern.tex` are formalised
here; none of the geometry (hyperplane sections, standard conjectures).

The folder itself never uses `𝔰𝔩₂`: its `Λ` is a *pseudo-inverse* of `L`,
normalised by `(6.7)`, `LΛ = 1 - ∑_{i ≤ n} π_{i,0}`, `ΛL = 1 - ∑_{i ≥ n} π_{i,0}`,
so as to stay over `ℤ`. The reading states three things about how this differs
from the `𝔰𝔩₂` (Hodge) normalisation, and a fourth about the manuscript's model:

> (page 9) … l'adjoint de `L` pour la métrique, lequel satisfait `[L,Λ] = H` et
> agit sur `L^k P^i` par des scalaires entiers non triviaux — sur une classe
> primitive de degré `i` on a `Λ L x = (n-i) x` et non `x`.
>
> (page 16) avec un `Λ` normalisé en pseudo-inverse, ce commutateur vaut
> `∑_{i ≥ n} π_{i,0} - ∑_{i ≤ n} π_{i,0}` et ne retient que les extrémités des
> chaînes.
>
> (page 16) Le couple `(L₀, Λ₀)` formé de `ξ₀ ∧ -` et de `ξ₀* ⌟ -` … Sur
> l'unité, qui est primitive de degré `0`, `Λ₀ L₀ (1) = ⟨ξ₀*, ξ₀⟩ = n`, alors que
> `(6.15)` exige `1` … l'identification ne vaut donc que pour `n = 1`.

* `sl2_normalisation` — in any representation with an `𝔰𝔩₂`-triple, on a
  primitive vector of weight `μ` (`= n - i` in degree `i`): `ΛLx = μx`,
  `Λ L^{k+1} x = (k+1)(μ-k) L^k x`, `⁅H, L^k x⁆ = (μ-2k) L^k x`. From mathlib
  (`IsSl2Triple.HasPrimitiveVectorWith`). mathlib's `H = ⁅Λ, L⁆` is minus the
  reading's `[L, Λ]`.
* `identification_seulement_si` — if the `𝔰𝔩₂` `Λ` also satisfied `ΛLx = x` on a
  primitive class, as `(6.7)` asks at the bottom of a chain, then `μ = 1`
  (over a domain acting without torsion).
* `commutateur_pseudo_inverse` — the commutator formula, from `(6.7)` alone.
* `lambda0_L0_un`, `lambda0_L0_un_ne_un` — in the exterior algebra `Λ M₀`,
  `M₀ = R^{2n}`, `ξ₀ = ∑ e_{2k-1} ∧ e_{2k}`: `Λ₀ L₀ (1) = n`, hence `≠ 1` for
  `n ≠ 1` in characteristic `0`. This is the reading's correction of page 13,
  where the manuscript identifies the contraction `Λ₀` with the `Λ₀` of `(6.15)`.

**What the formalisation finds.** Nothing false: the reading's comparison of the
two normalisations holds as stated, and its correction of the manuscript (the two
`Λ₀` differ as soon as `n ≥ 2`) is confirmed by the computation `Λ₀ L₀ (1) = n`.
The `𝔰𝔩₂` facts themselves are already in mathlib.

**Not formalised.** That `(L₀, Λ₀)` generate an `𝔰𝔩₂`-representation on all of
`Λ M₀` (only its value on `1` is computed); the derivation of hard Lefschetz from
`𝔰𝔩₂` (the reading does not state it; the folder takes the primitive
decomposition as known); the theorem of n° 6, the universal ring `Φ₀` and its
Proposition; the dimension-6 counterexample of page 21; everything geometric.

What this certifies is that the reading holds together, not that it is what the
pages say (issue #26).
-/

namespace Grothendieck.Folder16

open LieModule

section Sl2

variable {R 𝔤 M : Type*} [CommRing R] [LieRing 𝔤] [LieAlgebra R 𝔤]
  [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
variable {H Λ L : 𝔤} (t : IsSl2Triple H Λ L)

/-- **Page 9 (the editor's comparison), Hodge normalisation.** In a representation
of `𝔰𝔩₂` with `Λ` lowering and `L` raising (mathlib's `e` and `f`), let `x` be a
primitive class (`Λ x = 0`) of weight `μ` (for a class of degree `i` with top
degree `2n`, `μ = n - i`; mathlib's `H = ⁅Λ, L⁆` is minus the reading's
`[L, Λ]`). Then `Λ L x = μ x` — « sur une classe primitive de degré `i` on a
`Λ L x = (n-i) x` et non `x` » — and more generally `Λ` acts on `L^{k+1} x` by
the integer `(k+1)(μ-k)`, while the commutator restores the degree:
`⁅H, L^k x⁆ = (μ - 2k) L^k x`. -/
theorem sl2_normalisation {x : M} {μ : R} (P : t.HasPrimitiveVectorWith x μ) (k : ℕ) :
    ⁅Λ, ⁅L, x⁆⁆ = μ • x ∧
      ⁅Λ, (toEnd R 𝔤 M L ^ (k + 1)) x⁆ = ((k + 1) * (μ - k)) • (toEnd R 𝔤 M L ^ k) x ∧
      ⁅H, (toEnd R 𝔤 M L ^ k) x⁆ = (μ - 2 * k) • (toEnd R 𝔤 M L ^ k) x := by
  refine ⟨?_, P.lie_e_pow_succ_toEnd_f k, P.lie_h_pow_toEnd_f k⟩
  simpa using P.lie_e_pow_succ_toEnd_f 0

/-- **Page 16, « l'identification ne vaut donc que pour `n = 1` ».** If the `𝔰𝔩₂`
operator `Λ` were also the pseudo-inverse of `(6.7)`, so that `Λ L x = x` on a
primitive class `x` of the bottom of a chain, then `(μ - 1) x = 0`; over a
domain acting without torsion, `μ = 1`. For the unit of the exterior algebra,
primitive of degree `0`, `μ = n`: the two normalisations agree only for
`n = 1`. -/
theorem identification_seulement_si [IsDomain R] [Module.IsTorsionFree R M] {x : M} {μ : R}
    (P : t.HasPrimitiveVectorWith x μ) (h : ⁅Λ, ⁅L, x⁆⁆ = x) : μ = 1 := by
  have h1 := (sl2_normalisation t P 0).1
  rw [h] at h1
  have : (μ - 1) • x = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
  rcases smul_eq_zero.1 this with h2 | h2
  · exact sub_eq_zero.1 h2
  · exact absurd h2 P.ne_zero

end Sl2

section PseudoInverse

variable {E : Type*} [Ring E]

/-- **Page 16 (the editor's computation from `(6.7)`).** With `Λ` normalised as a
two-sided pseudo-inverse, `LΛ = 1 - ∑_{0 ≤ i ≤ n} π_{i,0}` and
`ΛL = 1 - ∑_{n ≤ i ≤ 2n} π_{i,0}`, the commutator is
`[L, Λ] = ∑_{i ≥ n} π_{i,0} - ∑_{i ≤ n} π_{i,0}`: it only sees the ends of the
chains, and does not restore the grading. -/
theorem commutateur_pseudo_inverse (n : ℕ) (Lf Λf : E) (π : ℕ → E)
    (h₁ : Lf * Λf = 1 - ∑ i ∈ Finset.range (n + 1), π i)
    (h₂ : Λf * Lf = 1 - ∑ i ∈ Finset.Icc n (2 * n), π i) :
    Lf * Λf - Λf * Lf = ∑ i ∈ Finset.Icc n (2 * n), π i - ∑ i ∈ Finset.range (n + 1), π i := by
  rw [h₁, h₂]
  abel

end PseudoInverse

section ModeleExterieur

open CliffordAlgebra

variable (R : Type*) [CommRing R] (n : ℕ)

/-- `M₀ = R^{2n}`, with basis `e_{k,0}, e_{k,1}` (`k < n`), i.e. `e_{2k-1}, e_{2k}`. -/
abbrev M₀ := Fin n × Fin 2 → R

/-- The basis vector `e_{k,b}` of `M₀`. -/
noncomputable def base (k : Fin n) (b : Fin 2) : M₀ R n := Pi.single (k, b) 1

/-- `ξ₀ = ∑_k e_{k,0} ∧ e_{k,1}` in `Λ M₀`. -/
noncomputable def xi₀ : ExteriorAlgebra R (M₀ R n) :=
  ∑ k : Fin n, ExteriorAlgebra.ι R (base R n k 0) * ExteriorAlgebra.ι R (base R n k 1)

/-- `L₀ x = ξ₀ ∧ x`. -/
noncomputable def L₀ (x : ExteriorAlgebra R (M₀ R n)) : ExteriorAlgebra R (M₀ R n) := xi₀ R n * x

/-- `Λ₀ x = ξ₀* ⌟ x`, contraction by the dual form `ξ₀* = ∑_k e*_{k,0} ∧ e*_{k,1}`,
with the convention that `a ∧ b` contracts as `ι_b ∘ ι_a`. -/
noncomputable def Λ₀ (x : ExteriorAlgebra R (M₀ R n)) : ExteriorAlgebra R (M₀ R n) :=
  ∑ k : Fin n, contractLeft (Q := 0) (LinearMap.proj (R := R) (φ := fun _ => R) (k, 1))
    (contractLeft (Q := 0) (LinearMap.proj (R := R) (φ := fun _ => R) (k, 0)) x)

/-- **Page 16 (the reading's footnote).** « Sur l'unité, qui est primitive de
degré `0`, `Λ₀ L₀ (1) = ⟨ξ₀*, ξ₀⟩ = n`. » -/
theorem lambda0_L0_un : Λ₀ R n (L₀ R n 1) = (n : ExteriorAlgebra R (M₀ R n)) := by
  simp only [L₀, mul_one, xi₀, Λ₀, map_sum]
  have key : ∀ k j : Fin n,
      contractLeft (Q := 0) (LinearMap.proj (R := R) (φ := fun _ => R) (k, 1))
        (contractLeft (Q := 0) (LinearMap.proj (R := R) (φ := fun _ => R) (k, 0))
          (ExteriorAlgebra.ι R (base R n j 0) * ExteriorAlgebra.ι R (base R n j 1))) =
        if k = j then 1 else 0 := by
    intro k j
    rw [contractLeft_ι_mul, contractLeft_ι]
    simp only [base, LinearMap.proj_apply, Pi.single_apply, Prod.mk.injEq]
    have h01 : ((0 : Fin 2) = 1) = False := by decide
    simp only [h01, and_false, if_false, map_zero, mul_zero, sub_zero, and_true, map_smul]
    rw [ExteriorAlgebra.ι, contractLeft_ι]
    simp only [LinearMap.proj_apply, Pi.single_apply, Prod.mk.injEq, and_true]
    split_ifs <;> simp
  simp_rw [key]
  simp

/-- **Page 16.** « `Λ₀ L₀ (1) = n`, alors que `(6.15)` exige `1` … l'identification
ne vaut donc que pour `n = 1` »: in characteristic zero, the contraction `Λ₀`
satisfies `Λ₀ L₀ (1) = 1` only if `n = 1`. -/
theorem lambda0_L0_un_ne_un [CharZero R] (hn : n ≠ 1) :
    Λ₀ R n (L₀ R n 1) ≠ 1 := by
  rw [lambda0_L0_un]
  intro h
  have := congrArg (ExteriorAlgebra.algebraMapInv (R := R) (M := M₀ R n)) h
  simp only [map_natCast, map_one] at this
  exact hn (by exact_mod_cast this)

end ModeleExterieur

end Grothendieck.Folder16
