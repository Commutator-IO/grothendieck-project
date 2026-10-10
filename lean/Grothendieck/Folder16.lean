import Mathlib.Algebra.Lie.Sl2
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.Data.Int.Interval

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

* `inverse_mem_of_charpoly`, `inverse_Lefschetz_algebrique` — pages 47–48 (finding
  `16-algebraic-iso-suffices`): under `D(X)` (characteristic polynomials of algebraic
  endomorphisms with coefficients in `F`), any algebraic isomorphism `u : H^{2n-i} → H^i`
  makes the inverse of the isomorphism `v` induced by `L^{n-i}` algebraic. « Algebraic » is
  membership in given sets of maps, stable under composition and `F`-scalars.
* `projecteurs_mem`, `projecteurs_mem_lefschetz` — pages 6–8 (no. 5 and `(6.3)ᵢ`, the first
  part of finding `16-graded-ring-lefschetz-criterion`): in a ring with grading idempotents,
  one-sided inverses `wᵢ ∈ ℰ` of `L^{n-i}` put every `πᵢ` in the subring `ℰ`, over `ℤ`.
* `not_exists_xi₀_pow_mul_eq_vol`, `L₀_pow_ne_vol` — page 13 over `ℤ` (finding
  `16-universal-lefschetz-ring`): for `n ≥ 2`, `ξ₀ⁿ ∧ y` is never the top class `vol` of
  `Λ ℤ^{2n}` (`ξ₀²` is even), so `(6.3)₀` fails in the exterior model over `ℤ` and no `Λ₀`
  in the sense of `(6.15)` exists in `End_ℤ(Λ M₀)`.
* `pseudo_inverse_unique` — a pseudo-inverse with `ΛLΛ = Λ` is determined by `ΛL` and `LΛ`.

**What the formalisation finds.** The reading's comparison of the two normalisations holds
as stated, and its correction of the manuscript (the two `Λ₀` differ as soon as `n ≥ 2`) is
confirmed by `Λ₀ L₀ (1) = n`; the `𝔰𝔩₂` facts themselves are already in mathlib. The
Cayley–Hamilton argument of page 47 and the projector argument of no. 5 hold as stated.
But the reading's repair of page 13 — keep `Φ₀ = ℤ[L₀, Λ₀] ⊂ End(Λ M₀)` with `Λ₀` in the
sense of `(6.15)` — fails over `ℤ` for `n ≥ 2`: `L₀ⁿ : Λ⁰ → Λ^{2n}` is multiplication by
`n!` (here: by an even number), so the exterior model over `ℤ` does not satisfy the
Lefschetz conditions. Over `ℚ` the obstruction disappears.

**Not formalised.** That `(L₀, Λ₀)` generate an `𝔰𝔩₂`-representation on all of
`Λ M₀` (only its value on `1` is computed); the derivation of hard Lefschetz from
`𝔰𝔩₂` (the folder takes the primitive decomposition as known); in the theorem of no. 6,
that `Λ` and the projectors `π_{i,α}` given by the formulas of pages 10–12 satisfy `(6.7)`
and are the projectors of the primitive decomposition; the existence and uniqueness of the
homomorphism `Φ₀ → ℰ`; the Corollary of page 48; the dimension-6 counterexample of page
21; everything geometric.

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

section CayleyHamilton

open Polynomial

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]

/-- **Page 47, the Cayley–Hamilton step.** Let `V` be finite-dimensional over a field `K`
(`H^i(X)` over `ℚ_ℓ`), `F ⊆ K` a subfield (`ℚ`), and `𝒜` a ring of endomorphisms stable under
`F`-scalars (the algebraic ones), whose characteristic polynomials have coefficients in `F`
(the hypothesis `D(X)` of the letter). Then the inverse of an invertible `w ∈ 𝒜` is in `𝒜`:
Cayley–Hamilton writes `w⁻¹` as `-σ_b(w)⁻¹ ∑ ± σ_j(w) w^{j}`, with coefficients in `F`. -/
theorem inverse_mem_of_charpoly (F : Subfield K) (𝒜 : Subring (Module.End K V))
    (hsmul : ∀ c ∈ F, ∀ g ∈ 𝒜, c • g ∈ 𝒜)
    (hD : ∀ g ∈ 𝒜, ∀ j, g.charpoly.coeff j ∈ F)
    {w : Module.End K V} (hw : w ∈ 𝒜) (hunit : IsUnit w) :
    ∃ g ∈ 𝒜, g * w = 1 ∧ w * g = 1 := by
  set p := w.charpoly with hp
  have hCH : aeval w p = 0 := LinearMap.aeval_self_charpoly w
  have hc0 : p.coeff 0 ≠ 0 := by
    have hdet := LinearMap.det_eq_sign_charpoly_coeff w
    have hu : IsUnit (LinearMap.det w) := (LinearMap.isUnit_iff_isUnit_det w).1 hunit
    intro h
    rw [← hp, h, mul_zero] at hdet
    exact hu.ne_zero hdet
  set q := aeval w p.divX with hq
  have hqw : q * w = -algebraMap K _ (p.coeff 0) := by
    have := congrArg (aeval w) (divX_mul_X_add p)
    rw [map_add, map_mul, aeval_X, aeval_C, hCH] at this
    exact eq_neg_of_add_eq_zero_left this
  have hwq : w * q = q * w := by
    have := ((commute_X p.divX).map (aeval w)).eq
    rwa [aeval_X] at this
  have hqmem : q ∈ 𝒜 := by
    rw [hq, aeval_eq_sum_range]
    refine Subring.sum_mem _ fun j _ => ?_
    exact hsmul _ (by rw [coeff_divX]; exact hD w hw _) _ (Subring.pow_mem _ hw _)
  have key : (-(p.coeff 0)⁻¹ • q) * w = 1 := by
    rw [smul_mul_assoc, hqw, smul_neg, neg_smul, neg_neg, Algebra.algebraMap_eq_smul_one,
      smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨-(p.coeff 0)⁻¹ • q, ?_, key, ?_⟩
  · exact hsmul _ (F.neg_mem (F.inv_mem (hD w hw 0))) _ hqmem
  · rw [mul_smul_comm, hwq, ← smul_mul_assoc, key]

/-- **Pages 47–48, « un isomorphisme algébrique quelconque ».** With `V = H^i(X)`,
`W = H^{2n-i}(X)` and « algebraic » read as membership in given sets of maps
(`𝒜V` a ring as above, satisfying `D(X)`; `𝒜WV`, `𝒜VW` the algebraic maps between the two
degrees, stable under composition): if `u : W → V` is *some* algebraic isomorphism and `v`
(induced by `L^{n-i}`) is an algebraic isomorphism, then `v⁻¹` is algebraic. The proof is the
letter's: `w = u ∘ v` is an algebraic automorphism of `V`, `w⁻¹` is algebraic by
Cayley–Hamilton, and `v⁻¹ = w⁻¹ ∘ u`. -/
theorem inverse_Lefschetz_algebrique (F : Subfield K) (𝒜V : Subring (Module.End K V))
    (𝒜WV : Set (W →ₗ[K] V)) (𝒜VW : Set (V →ₗ[K] W))
    (hsmul : ∀ c ∈ F, ∀ g ∈ 𝒜V, c • g ∈ 𝒜V)
    (hD : ∀ g ∈ 𝒜V, ∀ j, g.charpoly.coeff j ∈ F)
    (hcomp₁ : ∀ g ∈ 𝒜V, ∀ h ∈ 𝒜WV, g ∘ₗ h ∈ 𝒜WV)
    (hcomp₂ : ∀ h ∈ 𝒜WV, ∀ k ∈ 𝒜VW, h ∘ₗ k ∈ 𝒜V)
    {u : W →ₗ[K] V} (hu : u ∈ 𝒜WV) (hub : Function.Bijective u)
    {v : V →ₗ[K] W} (hv : v ∈ 𝒜VW) (hvb : Function.Bijective v) :
    ∃ v' ∈ 𝒜WV, v' ∘ₗ v = LinearMap.id ∧ v ∘ₗ v' = LinearMap.id := by
  have hw : u ∘ₗ v ∈ 𝒜V := hcomp₂ _ hu _ hv
  have hunit : IsUnit (u ∘ₗ v : Module.End K V) :=
    (Module.End.isUnit_iff _).2 (hub.comp hvb)
  obtain ⟨g, hg, hgw, -⟩ := inverse_mem_of_charpoly F 𝒜V hsmul hD hw hunit
  have hleft : (g ∘ₗ u) ∘ₗ v = LinearMap.id := by
    rw [LinearMap.comp_assoc]; exact hgw
  refine ⟨g ∘ₗ u, hcomp₁ _ hg _ hu, hleft, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := hvb.2 y
  have := congrArg (fun f => f x) hleft
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this ⊢
  rw [this]

end CayleyHamilton

section Projecteurs

variable {E : Type*} [Ring E]

/-- `x` is homogeneous of degree `d` for the grading given by the idempotents `π`:
`π_b x π_a = 0` unless `b = a + d`. -/
def Homogene (π : ℤ → E) (d : ℤ) (x : E) : Prop :=
  ∀ a b, b ≠ a + d → π b * x * π a = 0

/-- The grading data: `π` orthogonal idempotents of sum `1`, zero outside `[0, 2n]`. -/
structure Graduation (π : ℤ → E) (n : ℕ) : Prop where
  idem : ∀ a, π a * π a = π a
  orth : ∀ a b, a ≠ b → π a * π b = 0
  supp : ∀ a, a ∉ Finset.Icc (0 : ℤ) (2 * n) → π a = 0
  sum : ∑ a ∈ Finset.Icc (0 : ℤ) (2 * n), π a = 1

variable {π : ℤ → E} {n : ℕ}

/-- `x π_a = π_{a+d} x π_a` for `x` homogeneous of degree `d`. -/
theorem Graduation.mul_proj (G : Graduation π n) {d : ℤ} {x : E} (hx : Homogene π d x) (a : ℤ) :
    x * π a = π (a + d) * x * π a := by
  calc x * π a = (∑ b ∈ Finset.Icc (0 : ℤ) (2 * n), π b) * x * π a := by rw [G.sum, one_mul]
    _ = ∑ b ∈ Finset.Icc (0 : ℤ) (2 * n), π b * x * π a := by rw [Finset.sum_mul, Finset.sum_mul]
    _ = π (a + d) * x * π a := by
      refine Finset.sum_eq_single (a + d) (fun b _ hb => hx a b hb) (fun h => ?_)
      rw [G.supp _ h, zero_mul, zero_mul]

theorem Graduation.homogene_one (G : Graduation π n) : Homogene π 0 (1 : E) := by
  intro a b hab
  rw [mul_one]; exact G.orth b a (by omega)

theorem Graduation.homogene_mul (G : Graduation π n) {d e : ℤ} {x y : E}
    (hx : Homogene π d x) (hy : Homogene π e y) : Homogene π (d + e) (x * y) := by
  intro a b hab
  rw [← mul_assoc, mul_assoc _ y, G.mul_proj hy, ← mul_assoc, ← mul_assoc,
    hx (a + e) b (by omega), zero_mul, zero_mul]

theorem Graduation.homogene_pow (G : Graduation π n) {L : E} (hL : Homogene π 2 L) (k : ℕ) :
    Homogene π (2 * k) (L ^ k) := by
  induction k with
  | zero => simpa using G.homogene_one
  | succ k ih =>
    rw [pow_succ]
    have := G.homogene_mul ih hL
    rwa [show 2 * (k : ℤ) + 2 = 2 * ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this

/-- The computation of no. 5: `ψ v φ = π_{2n-i} v π_i` when only one pair of degrees survives. -/
theorem sandwich {d : ℤ} {x : E} (hx : Homogene π d x) (A B : Finset ℤ) {a₀ : ℤ}
    (ha₀ : a₀ ∈ A) (hb₀ : a₀ + d ∈ B) (huniq : ∀ a ∈ A, a + d ∈ B → a = a₀) :
    (∑ b ∈ B, π b) * x * (∑ a ∈ A, π a) = π (a₀ + d) * x * π a₀ := by
  rw [Finset.sum_mul, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_eq_single (a₀ + d)]
  · refine Finset.sum_eq_single a₀ (fun a _ ha => hx a _ (fun h => ha (by omega))) ?_
    intro h; exact absurd ha₀ h
  · intro b hb hne
    refine Finset.sum_eq_zero fun a ha => hx a b fun h => hne ?_
    have := huniq a ha (h ▸ hb); subst this; exact h
  · intro h; exact absurd hb₀ h

/-- The complement of a sum of known projectors. -/
theorem Graduation.sum_filter_not (G : Graduation π n) (P : ℤ → Prop) [DecidablePred P] :
    ∑ a ∈ (Finset.Icc (0 : ℤ) (2 * n)).filter (fun a => ¬ P a), π a =
      1 - ∑ a ∈ (Finset.Icc (0 : ℤ) (2 * n)).filter P, π a := by
  have := Finset.sum_filter_add_sum_filter_not (Finset.Icc (0 : ℤ) (2 * n)) P π
  rw [G.sum] at this
  rw [← this]; abel

/-- **Pages 6–7 (`(4.4)ᵢ` and no. 5, on the leaf « 5 bis »), over `ℤ`.** Let `ℰ` be a
subring of a ring `E` in which orthogonal idempotents `π_a` of sum `1`, zero outside
`[0, 2n]`, define the
grading. If for each `i ≤ n` there are `vᵢ ∈ ℰ` of degree `2n - 2i` and `wᵢ ∈ ℰ` of degree
`-(2n - 2i)` with `(wᵢvᵢ - 1)πᵢ = 0` and `(vᵢwᵢ - 1)π_{2n-i} = 0`, then every `π_a` is in `ℰ`.
Descending induction: `φᵢ = ∑_{a ≥ i} π_a` and `ψ_{2n-i} = ∑_{a ≤ 2n-i} π_a` are in `ℰ`,
`v'ᵢ = ψ vᵢ φ = π_{2n-i} vᵢ πᵢ`, `w'ᵢ = φ wᵢ ψ = πᵢ wᵢ π_{2n-i}`, and
`w'ᵢ v'ᵢ = πᵢ`, `v'ᵢ w'ᵢ = π_{2n-i}`. No module is used, and `ℰ` is only a ring. -/
theorem projecteurs_mem (ℰ : Subring E) (G : Graduation π n) (v w : ℕ → E)
    (hvE : ∀ i ≤ n, v i ∈ ℰ) (hwE : ∀ i ≤ n, w i ∈ ℰ)
    (hv : ∀ i ≤ n, Homogene π (2 * ((n : ℤ) - i)) (v i))
    (hw : ∀ i ≤ n, Homogene π (-(2 * ((n : ℤ) - i))) (w i))
    (h₁ : ∀ i ≤ n, w i * v i * π i = π i)
    (h₂ : ∀ i ≤ n, v i * w i * π (2 * n - i) = π (2 * n - i)) :
    ∀ a, π a ∈ ℰ := by
  have step : ∀ i : ℕ, i ≤ n + 1 → ∀ a : ℤ, (a < i ∨ 2 * n - i < a) → π a ∈ ℰ := by
    intro i
    induction i with
    | zero =>
      intro _ a ha
      rw [G.supp a (by simp only [Finset.mem_Icc]; omega)]; exact ℰ.zero_mem
    | succ i ih =>
      intro hi
      have hin : i ≤ n := by omega
      have ih := ih (by omega)
      -- φ = ∑_{a ≥ i} π a and ψ = ∑_{a ≤ 2n - i} π a are in ℰ
      set A := (Finset.Icc (0 : ℤ) (2 * n)).filter (fun a : ℤ => ¬ a < (i : ℤ))
      set B := (Finset.Icc (0 : ℤ) (2 * n)).filter (fun a : ℤ => ¬ (2 * n - i : ℤ) < a)
      have hφ : ∑ a ∈ A, π a ∈ ℰ := by
        rw [G.sum_filter_not (fun a : ℤ => a < i)]
        exact ℰ.sub_mem ℰ.one_mem (ℰ.sum_mem fun a ha => ih a (Or.inl (Finset.mem_filter.1 ha).2))
      have hψ : ∑ a ∈ B, π a ∈ ℰ := by
        rw [G.sum_filter_not (fun a : ℤ => (2 * n - i : ℤ) < a)]
        exact ℰ.sub_mem ℰ.one_mem (ℰ.sum_mem fun a ha => ih a (Or.inr (Finset.mem_filter.1 ha).2))
      have hv' : π (2 * n - i) * v i * π i ∈ ℰ := by
        have := sandwich (hv i hin) A B (a₀ := i) (by simp [A]; omega) (by simp [B]; omega)
          (fun a ha hb => by simp [A, B] at ha hb; omega)
        rw [show (i : ℤ) + 2 * ((n : ℤ) - i) = 2 * n - i by ring] at this
        rw [← this]; exact ℰ.mul_mem (ℰ.mul_mem hψ (hvE i hin)) hφ
      have hw' : π i * w i * π (2 * n - i) ∈ ℰ := by
        have := sandwich (hw i hin) B A (a₀ := 2 * n - i) (by simp [B]; omega) (by simp [A]; omega)
          (fun a ha hb => by simp [A, B] at ha hb; omega)
        rw [show (2 * n - i : ℤ) + -(2 * ((n : ℤ) - i)) = i by ring] at this
        rw [← this]; exact ℰ.mul_mem (ℰ.mul_mem hφ (hwE i hin)) hψ
      have hvπ : π (2 * n - i) * v i * π i = v i * π i := by
        rw [G.mul_proj (hv i hin) i, show (i : ℤ) + 2 * ((n : ℤ) - i) = 2 * n - i by ring]
      have hwπ : π i * w i * π (2 * n - i) = w i * π (2 * n - i) := by
        rw [G.mul_proj (hw i hin) (2 * n - i),
          show (2 * n - i : ℤ) + -(2 * ((n : ℤ) - i)) = i by ring]
      have hπi : π i ∈ ℰ := by
        have : (π i * w i * π (2 * n - i)) * (π (2 * n - i) * v i * π i) = π i := by
          calc _ = π i * w i * (π (2 * n - i) * π (2 * n - i) * v i * π i) := by noncomm_ring
            _ = π i * (w i * v i * π i) := by rw [G.idem, hvπ]; noncomm_ring
            _ = π i := by rw [h₁ i hin, G.idem]
        rw [← this]; exact ℰ.mul_mem hw' hv'
      have hπi' : π (2 * n - i) ∈ ℰ := by
        have : (π (2 * n - i) * v i * π i) * (π i * w i * π (2 * n - i)) = π (2 * n - i) := by
          calc _ = π (2 * n - i) * v i * (π i * π i * w i * π (2 * n - i)) := by noncomm_ring
            _ = π (2 * n - i) * (v i * w i * π (2 * n - i)) := by rw [G.idem, hwπ]; noncomm_ring
            _ = π (2 * n - i) := by rw [h₂ i hin, G.idem]
        rw [← this]; exact ℰ.mul_mem hv' hw'
      intro a ha
      push_cast at ha
      rcases lt_trichotomy a i with h | h | h
      · exact ih a (Or.inl h)
      · exact h ▸ hπi
      · rcases lt_trichotomy a (2 * n - i) with h' | h' | h'
        · omega
        · exact h' ▸ hπi'
        · exact ih a (Or.inr h')
  intro a
  exact step (n + 1) le_rfl a (by push_cast; omega)

/-- **Page 8 (no. 6, `(6.3)ᵢ`).** The case `vᵢ = L^{n-i}`, `L ∈ ℰ` of degree `2`: one-sided
inverses `wᵢ ∈ ℰ` of `L^{n-i}` (on `πᵢ` and on `π_{2n-i}`) put all the grading projectors
in `ℰ`. -/
theorem projecteurs_mem_lefschetz (ℰ : Subring E) (G : Graduation π n) {L : E} (hLE : L ∈ ℰ)
    (hL : Homogene π 2 L) (w : ℕ → E) (hwE : ∀ i ≤ n, w i ∈ ℰ)
    (hw : ∀ i ≤ n, Homogene π (-(2 * ((n : ℤ) - i))) (w i))
    (h₁ : ∀ i ≤ n, w i * L ^ (n - i) * π i = π i)
    (h₂ : ∀ i ≤ n, L ^ (n - i) * w i * π (2 * n - i) = π (2 * n - i)) :
    ∀ a, π a ∈ ℰ :=
  projecteurs_mem ℰ G (fun i => L ^ (n - i)) w (fun i _ => ℰ.pow_mem hLE _) hwE
    (fun i hi => by
      have := G.homogene_pow hL (n - i)
      rwa [Nat.cast_sub hi] at this) hw h₁ h₂

end Projecteurs

section Entiers

open ExteriorAlgebra

variable {R : Type*} [CommRing R] {n : ℕ}

/-- `ι x ι y = -(ι y ι x)`. -/
theorem ι_mul_ι_anticomm {M : Type*} [AddCommGroup M] [Module R M] (x y : M) :
    ι R x * ι R y = -(ι R y * ι R x) :=
  eq_neg_of_add_eq_zero_left (ι_add_mul_swap x y)

/-- A product of two vectors commutes with every vector up to two sign changes. -/
theorem commute_paire_ι {M : Type*} [AddCommGroup M] [Module R M] (x y z : M) :
    Commute (ι R x * ι R y) (ι R z) := by
  show ι R x * ι R y * ι R z = ι R z * (ι R x * ι R y)
  rw [mul_assoc, ι_mul_ι_anticomm y z, mul_neg, ← mul_assoc, ι_mul_ι_anticomm x z, neg_mul,
    neg_neg, mul_assoc]

/-- Two products of two vectors commute. -/
theorem commute_paires {M : Type*} [AddCommGroup M] [Module R M] (x y z t : M) :
    Commute (ι R x * ι R y) (ι R z * ι R t) :=
  (commute_paire_ι x y z).mul_right (commute_paire_ι x y t)

/-- `(x ∧ y)² = 0`. -/
theorem paire_sq {M : Type*} [AddCommGroup M] [Module R M] (x y : M) :
    (ι R x * ι R y) * (ι R x * ι R y) = 0 := by
  rw [← mul_assoc, (commute_paire_ι x y x).eq, ← mul_assoc, ι_sq_zero, zero_mul, zero_mul]

/-- Over any ring, `ξ₀²` is twice an element: the cross terms come in equal pairs. -/
theorem xi₀_sq_two_mul : ∃ c : ExteriorAlgebra R (M₀ R n), xi₀ R n * xi₀ R n = c + c := by
  unfold xi₀
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert k s hk ih =>
    obtain ⟨c, hc⟩ := ih
    set a := ι R (base R n k 0) * ι R (base R n k 1)
    set S := ∑ j ∈ s, ι R (base R n j 0) * ι R (base R n j 1)
    have hcomm : S * a = a * S :=
      (Commute.sum_left _ _ _ fun j _ => commute_paires _ _ _ _).eq
    refine ⟨a * S + c, ?_⟩
    rw [Finset.sum_insert hk, add_mul, mul_add, mul_add, paire_sq, hc, hcomm]
    abel

/-- The basis of `M₀ = ℤ^{2n}` indexed by `Fin (n * 2)`. -/
noncomputable def baseFin : Module.Basis (Fin (n * 2)) R (M₀ R n) :=
  (Pi.basisFun R (Fin n × Fin 2)).reindex finProdFinEquiv

/-- The top exterior product `e₁ ∧ ⋯ ∧ e_{2n}`, a generator of `Λ^{2n} M₀`. -/
noncomputable def vol : ⋀[R]^(n * 2) (M₀ R n) :=
  exteriorPower.ιMulti_family R (n * 2) (baseFin (R := R) (n := n))
    ⟨Finset.univ, by simp⟩

/-- **Page 13, over `ℤ`.** For `n ≥ 2`, the top class of `Λ M₀` is not of the form
`ξ₀ⁿ ∧ y`, whatever `y`: `L₀ⁿ` does not reach `Λ^{2n} M₀` over `ℤ`. -/
theorem not_exists_xi₀_pow_mul_eq_vol (hn : 2 ≤ n) :
    ¬ ∃ y : ExteriorAlgebra ℤ (M₀ ℤ n),
      xi₀ ℤ n ^ n * y = ((vol (R := ℤ) (n := n) : ⋀[ℤ]^(n * 2) (M₀ ℤ n)) :
        ExteriorAlgebra ℤ (M₀ ℤ n)) := by
  rintro ⟨y, hy⟩
  obtain ⟨c, hc⟩ := xi₀_sq_two_mul (R := ℤ) (n := n)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  set z := xi₀ ℤ (2 + m) ^ m * c * y
  have h2 : ((vol (R := ℤ) (n := 2 + m)) : ExteriorAlgebra ℤ (M₀ ℤ (2 + m))) = z + z := by
    rw [← hy, show xi₀ ℤ (2 + m) ^ (2 + m) = xi₀ ℤ (2 + m) ^ m * (xi₀ ℤ (2 + m) * xi₀ ℤ (2 + m)) by
      rw [← sq, ← pow_add, add_comm], hc]
    simp only [z]; noncomm_ring
  let φ : ExteriorAlgebra ℤ (M₀ ℤ (2 + m)) → ℤ := fun x =>
    exteriorPower.ιMultiDual ℤ ((2 + m) * 2) (baseFin (R := ℤ) (n := 2 + m)) ⟨Finset.univ, by simp⟩
      (DirectSum.decompose (fun i : ℕ => ⋀[ℤ]^i (M₀ ℤ (2 + m))) x ((2 + m) * 2))
  have hφadd : ∀ x x', φ (x + x') = φ x + φ x' := by
    intro x x'
    simp only [φ, DirectSum.decompose_add, DirectSum.add_apply, map_add]
  have hφvol : φ (vol (R := ℤ) (n := 2 + m)) = 1 := by
    simp only [φ]
    have : DirectSum.decompose (fun i : ℕ => ⋀[ℤ]^i (M₀ ℤ (2 + m)))
        ((vol (R := ℤ) (n := 2 + m)) : ExteriorAlgebra ℤ (M₀ ℤ (2 + m))) ((2 + m) * 2) = vol :=
      Subtype.ext (DirectSum.decompose_of_mem_same _ (vol (R := ℤ) (n := 2 + m)).2)
    rw [this]
    exact exteriorPower.ιMultiDual_apply_diag ℤ _ _ _
  have := congrArg φ h2
  rw [hφadd, hφvol] at this
  omega

/-- **Page 13, over `ℤ`: no `Λ₀` of `(6.15)` in `End_ℤ(Λ M₀)` for `n ≥ 2`.** Whatever the map
`w` (in particular `w = Λ₀ⁿ`, which the Remarque of page 12 requires to satisfy
`(L₀ⁿ Λ₀ⁿ - 1) π_{2n} = 0`), `L₀ⁿ (w (vol)) ≠ vol`: `(6.3)₀` fails in the exterior model
over `ℤ`, because `ξ₀ⁿ = n! · vol`. -/
theorem L₀_pow_ne_vol (hn : 2 ≤ n)
    (w : ExteriorAlgebra ℤ (M₀ ℤ n) → ExteriorAlgebra ℤ (M₀ ℤ n)) :
    (L₀ ℤ n)^[n] (w (vol (R := ℤ) (n := n))) ≠ (vol (R := ℤ) (n := n)) := by
  have hit : ∀ (k : ℕ) (x : ExteriorAlgebra ℤ (M₀ ℤ n)), (L₀ ℤ n)^[k] x = xi₀ ℤ n ^ k * x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih => intro x; rw [Function.iterate_succ_apply', ih, L₀, pow_succ', mul_assoc]
  rw [hit]
  exact fun h => not_exists_xi₀_pow_mul_eq_vol hn ⟨_, h⟩

end Entiers

section Unicite

variable {E : Type*} [Ring E]

/-- **Pages 14–15, « unique quand il existe » (the algebraic step).** A pseudo-inverse `Λ` of
`L` with `ΛLΛ = Λ` is determined by the two idempotents `ΛL` and `LΛ`. -/
theorem pseudo_inverse_unique {L Λ Λ' : E} (h : Λ * L * Λ = Λ) (h' : Λ' * L * Λ' = Λ')
    (hl : Λ * L = Λ' * L) (hr : L * Λ = L * Λ') : Λ = Λ' :=
  calc Λ = Λ * L * Λ := h.symm
    _ = Λ' * (L * Λ) := by rw [hl, mul_assoc]
    _ = Λ' * L * Λ' := by rw [hr, mul_assoc]
    _ = Λ' := h'

end Unicite

end Grothendieck.Folder16
