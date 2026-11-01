import Bourbaki.Upstream.SemiCartesianSquare

/-!
# Bourbaki, rédaction n° 461 (Chevalley, 1966), § 2.6: semi-cartesian squares

Rédaction 461, « Catégories abéliennes », studies in § 2.6 (pp. 65–77 of the scan) the
commutative squares of an abelian category `C`
```
 a ──α₁──▶ a₁
 │α₂       │β₁
 ▼         ▼
 a₂ ──β₂─▶ b
```
for which the map `μ` from the pushout of `(α₁, α₂)` to `b` is a monomorphism and the map `ν`
from `a` to the pullback of `(β₁, β₂)` is an epimorphism. Proposition 13 (p. 65) shows that the
two conditions are equivalent, and equivalent to the exactness of the sequence
`0 ⟶ pullback ⟶ a₁ ⊞ a₂ ⟶ pushout ⟶ 0` (maps `ζ = σ₁ω₁ + σ₂ω₂` and `ρ = φ₁π₁ − φ₂π₂` on the
page), restated in Remark 1 (p. 66); Definition 3 (p. 66) calls such squares semi-cartesian.
The characterisation proved here, by the exactness of `a ⟶ a₁ ⊞ a₂ ⟶ b` in the middle, is an
equivalent reformulation chosen by the edition, not the page's statement.
Cartesian and cocartesian squares are semi-cartesian.

Proposition 14 (pp. 66–67): a semi-cartesian square with `α₁` mono is cartesian and `β₂` is
then mono; dually, with `β₂` epi it is cocartesian and `α₁` is epi. Proposition 15 (p. 67): a
cocartesian square followed by a cartesian one is semi-cartesian; Corollary 2 (p. 70): a square
is semi-cartesian if and only if it is such a composite. Corollary 4 of Proposition 16
(pp. 73–74): the square is semi-cartesian if and only if the two sequences
`ker α₁ ⟶ a₂ ⟶ b` and `a ⟶ a₁ ⟶ coker β₂` are exact.

The proofs here chase elements up to refinements (Mathlib's `Abelian/Refinements.lean`), through
one lemma, `exact_iff`, which turns the exactness of `a ⟶ a₁ ⊞ a₂ ⟶ b` into a statement on
pairs of morphisms `x₁ : T ⟶ a₁`, `x₂ : T ⟶ a₂`. The short complex is Mathlib's
`CommSq.shortComplex`, with maps `(α₁, -α₂)` and `(β₁, β₂)`. For the necessity in Corollary 2
the factorisation used is not the rédaction's (epimorphism then monomorphism in the arrow
category): it is the pushout square of `(α₁, α₂)` followed by the square with sides `pushout.inr`,
`𝟙`, `μ`, `β₂`, which is cartesian because `μ` is mono.

**What is proved.**
* `IsSemiCartesian` (Definition 3, p. 66): `μ` is mono and `ν` is epi.
* `exact_iff`: exactness of `CommSq.shortComplex` in terms of morphisms, up to refinements.
* `mono_fromPushout_iff_exact`, `epi_toPullback_iff_exact`, `mono_fromPushout_iff_epi_toPullback`,
  `isSemiCartesian_iff_exact`, `isSemiCartesian_iff_mono`, `isSemiCartesian_iff_epi`:
  **Proposition 13, p. 65**, the equivalence of `μ` mono and `ν` epi as on the page; the third
  condition is the edition's reformulation (exactness of `a ⟶ a₁ ⊞ a₂ ⟶ b`), not the page's
  sequence `0 ⟶ pullback ⟶ a₁ ⊞ a₂ ⟶ pushout ⟶ 0`, which is not formalised.
* `IsPushout.isSemiCartesian`, `IsPullback.isSemiCartesian`: cocartesian and cartesian squares
  are semi-cartesian (p. 66).
* `IsSemiCartesian.flip`: the symmetric square is semi-cartesian (p. 67).
* `IsSemiCartesian.isPullback_of_mono`, `IsSemiCartesian.isPushout_of_epi`:
  **Proposition 14, pp. 66–67.**
* `isSemiCartesian_of_isPushout_of_isPullback`: **Proposition 15, first assertion, p. 67**, a
  cocartesian square followed by a cartesian square is semi-cartesian.
* `IsSemiCartesian.left_of_comp`, `IsSemiCartesian.right_of_comp`: **Proposition 15, second
  and third assertions, p. 67**, with weaker hypotheses (one component mono, resp. epi).
* `IsSemiCartesian.isPushout_isPullback_of_comp`: **Corollary 1 of Proposition 15, p. 69.**
* `isSemiCartesian_iff_exists_factorisation`: **Corollary 2 of Proposition 15, p. 70.**
* `isSemiCartesian_iff_exact_kernel_cokernel`: **Corollary 4 of Proposition 16, pp. 73–74.**

**Not formalised.** The page's form of Proposition 13 and Remark 1 (p. 66), the exactness of
`0 ⟶ pullback ⟶ a₁ ⊞ a₂ ⟶ pushout ⟶ 0`; the corollary of Proposition 14 (p. 67: monomorphisms
and epimorphisms are universal); the rédaction's own proof of the necessity in Corollary 2
(epi-mono factorisation in the arrow category, then Corollary 1); Proposition 16 and its
Corollaries 1 (p. 72), 2 and 3 (Corollaries 2 and 3 are the four and five lemmas, in Mathlib as
`Abelian.mono_of_epi_of_mono_of_mono` and `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`);
Proposition 17 (pp. 74–76, a nine-lemma-like statement) and Proposition 17 bis (pp. 76–77).

The proofs are general and live in `Bourbaki/Upstream/SemiCartesianSquare.lean`, in the namespace
`CategoryTheory.CommSq` (`CommSq.IsSemiCartesian`, `CommSq.exact_shortComplex_iff` for
`exact_iff`, and the other names unchanged); `IsPushout.isSemiCartesian` and
`IsPullback.isSemiCartesian` are declared there. The names below are aliases kept for the articles
that cite them.
-/

namespace Bourbaki.Redaction461

open CategoryTheory

/-- The map `μ` from the pushout of `(α₁, α₂)` to `b` induced by a commutative square. -/
alias fromPushout := CommSq.fromPushout

/-- The map `ν` from `a` to the pullback of `(β₁, β₂)` induced by a commutative square. -/
alias toPullback := CommSq.toPullback

/-- **Definition 3, rédaction n° 461, p. 66.** A commutative square is semi-cartesian when the
map from the pushout to `b` is a monomorphism and the map from `a` to the pullback is an
epimorphism (each condition implies the other, `mono_fromPushout_iff_epi_toPullback`). -/
alias IsSemiCartesian := CommSq.IsSemiCartesian

/-- The exactness of `a ⟶ a₁ ⊞ a₂ ⟶ b` in terms of morphisms: whenever
`x₁ ≫ β₁ + x₂ ≫ β₂ = 0`, the pair `(x₁, x₂)` comes, after an epimorphism `π`, from some
`y : T' ⟶ a` as `(y ≫ α₁, -(y ≫ α₂))`. -/
alias exact_iff := CommSq.exact_shortComplex_iff

/-- **Proposition 13, rédaction n° 461, p. 65 (first half).** The map from the pushout to `b`
is a monomorphism if and only if `a ⟶ a₁ ⊞ a₂ ⟶ b` is exact. -/
alias mono_fromPushout_iff_exact := CommSq.mono_fromPushout_iff_exact

/-- **Proposition 13, rédaction n° 461, p. 65 (second half).** The map from `a` to the pullback
is an epimorphism if and only if `a ⟶ a₁ ⊞ a₂ ⟶ b` is exact. -/
alias epi_toPullback_iff_exact := CommSq.epi_toPullback_iff_exact

/-- **Proposition 13, rédaction n° 461, p. 65.** The map from the pushout to `b` is a
monomorphism if and only if the map from `a` to the pullback is an epimorphism. -/
alias mono_fromPushout_iff_epi_toPullback := CommSq.mono_fromPushout_iff_epi_toPullback

/-- A square is semi-cartesian if and only if `a ⟶ a₁ ⊞ a₂ ⟶ b` is exact. -/
alias isSemiCartesian_iff_exact := CommSq.isSemiCartesian_iff_exact

/-- A square is semi-cartesian if and only if the map from the pushout to `b` is mono. -/
alias isSemiCartesian_iff_mono := CommSq.isSemiCartesian_iff_mono

/-- A square is semi-cartesian if and only if the map from `a` to the pullback is epi. -/
alias isSemiCartesian_iff_epi := CommSq.isSemiCartesian_iff_epi

/-- A semi-cartesian square, read as a pair of morphisms. -/
alias IsSemiCartesian.exists_lift := CommSq.IsSemiCartesian.exists_lift

/-- A semi-cartesian square from the condition on pairs of morphisms. -/
alias IsSemiCartesian.of_lift := CommSq.IsSemiCartesian.of_lift

/-- The symmetric square (exchanging `a₁` and `a₂`) of a semi-cartesian square is
semi-cartesian (rédaction n° 461, p. 67). -/
alias IsSemiCartesian.flip := CommSq.IsSemiCartesian.flip

/-- **Proposition 14, rédaction n° 461, pp. 66–67 (first assertion).** A semi-cartesian square
in which `α₁` is a monomorphism is cartesian, and `β₂` is then a monomorphism. -/
alias IsSemiCartesian.isPullback_of_mono := CommSq.IsSemiCartesian.isPullback_of_mono

/-- **Proposition 14, rédaction n° 461, p. 67 (second assertion).** A semi-cartesian square in
which `β₂` is an epimorphism is cocartesian, and `α₁` is then an epimorphism. -/
alias IsSemiCartesian.isPushout_of_epi := CommSq.IsSemiCartesian.isPushout_of_epi

/-- **Proposition 15, rédaction n° 461, p. 67 (first assertion).** A cocartesian square followed
by a cartesian square is semi-cartesian: if the square factors as a pushout square
`(α₁, u₀, u₁, α')` followed by a pullback square `(α', v₀, v₁, β₂)`, with `α₂ = u₀ ≫ v₀` and
`β₁ = u₁ ≫ v₁`, it is semi-cartesian. -/
alias isSemiCartesian_of_isPushout_of_isPullback :=
  CommSq.isSemiCartesian_of_isPushout_of_isPullback

/-- **Proposition 15, rédaction n° 461, p. 67 (second assertion).** If the square factors as
`(α₁, u₀, u₁, α')` followed by `(α', v₀, v₁, β₂)` and is semi-cartesian, and if `v₀` is a
monomorphism, then the first square is semi-cartesian. (The rédaction assumes the second square
mono in the arrow category, that is `v₀` and `v₁` mono; `v₀` suffices.) -/
alias IsSemiCartesian.left_of_comp := CommSq.IsSemiCartesian.left_of_comp

/-- **Proposition 15, rédaction n° 461, p. 67 (third assertion).** If the square factors as
`(α₁, u₀, u₁, α')` followed by `(α', v₀, v₁, β₂)` and is semi-cartesian, and if `u₁` is an
epimorphism, then the second square is semi-cartesian. (The rédaction assumes the first square
epi in the arrow category, that is `u₀` and `u₁` epi; `u₁` suffices.) -/
alias IsSemiCartesian.right_of_comp := CommSq.IsSemiCartesian.right_of_comp

/-- **Corollary 1 of Proposition 15, rédaction n° 461, p. 69.** If a semi-cartesian square
factors as `(α₁, u₀, u₁, α')` followed by `(α', v₀, v₁, β₂)` with `u₁` epi and `v₀` mono, the
first square is cocartesian and the second cartesian. (The rédaction assumes the first square
epi and the second mono in the arrow category.) -/
alias IsSemiCartesian.isPushout_isPullback_of_comp :=
  CommSq.IsSemiCartesian.isPushout_isPullback_of_comp

/-- **Corollary 2 of Proposition 15, rédaction n° 461, p. 70.** A commutative square is
semi-cartesian if and only if it factors, in the arrow category, as a pushout square
`(α₁, u₀, u₁, α')` followed by a pullback square `(α', v₀, v₁, β₂)`, with `α₂ = u₀ ≫ v₀` and
`β₁ = u₁ ≫ v₁`. For the necessity, the pushout square of `(α₁, α₂)` followed by the square
`(pushout.inr, 𝟙, μ, β₂)` will do. -/
alias isSemiCartesian_iff_exists_factorisation := CommSq.isSemiCartesian_iff_exists_factorisation

/-- `α₁ ≫ β₁ ≫ cokernel.π β₂ = 0` for a commutative square. -/
alias comp_cokernel_π_eq_zero := CommSq.comp_cokernel_π_eq_zero

/-- `kernel.ι α₁ ≫ α₂ ≫ β₂ = 0` for a commutative square. -/
alias kernel_ι_comp_eq_zero := CommSq.kernel_ι_comp_eq_zero

/-- **Corollary 4 of Proposition 16, rédaction n° 461, pp. 73–74.** A commutative square is
semi-cartesian if and only if the sequences `ker α₁ ⟶ a₂ ⟶ b` (maps `kernel.ι α₁ ≫ α₂` and
`β₂`) and `a ⟶ a₁ ⟶ coker β₂` (maps `α₁` and `β₁ ≫ cokernel.π β₂`) are exact. -/
alias isSemiCartesian_iff_exact_kernel_cokernel := CommSq.isSemiCartesian_iff_exact_kernel_cokernel

end Bourbaki.Redaction461
