import Bourbaki.Upstream.AbelianCommSqExact

/-!
# Bourbaki, rédaction n° 321 (1959), « Pull-backs »: pullbacks and pushouts in abelian categories

Rédaction 321 fixes a commutative square in an abelian category,
```
P --U--> B
|        |
V        v
v        v
A --u--> Q
```
and compares the pullback and pushout properties with the exactness of the sequence
`P → A ⊕ B → Q` built from `(V, U)` and `u - v` (p. 4, Prop. 2). In Mathlib's naming this is
`IsPullback V U u v` and `IsPushout V U u v`; the pullback sequence is `CommSq.shortComplex'`
(maps `biprod.lift V U` and `biprod.desc u (-v)`), the pushout sequence is `CommSq.shortComplex`
(maps `biprod.lift V (-U)` and `biprod.desc u v`). The two differ by the sign automorphism of
`A ⊞ B`, which preserves exactness (`shortComplexIso`); the rédaction uses one sign convention for
both.

**What is proved.**
* `isPullback_of_exact`, `isPullback_iff_exact`: **Prop. 2, pullback half** (rédaction n° 321,
  p. 4). The square is a pullback iff `0 → P → A ⊕ B → Q` is exact. Mathlib had the direct
  implication (`IsPullback.exact_shortComplex'` and `IsPullback.mono_shortComplex'_f`).
* `isPushout_of_exact`, `isPushout_iff_exact`: **Prop. 2, pushout half.** The square is a pushout
  iff `P → A ⊕ B → Q → 0` is exact.
* `shortComplexIso`: the two short complexes of a commutative square are isomorphic.
* `isPushout_of_isPullback_of_epi_right`, `isPushout_of_isPullback_of_epi_bottom`: **Prop. 4**
  (p. 4; Stacks 08N4). A pullback square in which `v` (or `u`) is an epimorphism is a pushout.
* `isPullback_of_isPushout_of_mono_top`, `isPullback_of_isPushout_of_mono_left`: **the dual of
  Prop. 4.** A pushout square in which `U` (or `V`) is a monomorphism is a pullback.
* `not_isPullback_of_isPushout_of_mono_bottom`: the dual as typed on p. 4 asks that the arrow
  written `u` be a monomorphism; read as the bottom arrow `u : A → Q`, the statement fails. For
  any nonzero `X`, the square `X → 0`, `X → 0`, `𝟙 0`, `𝟙 0` is a pushout with `u` an isomorphism,
  but not a pullback. The intended arrow is the top arrow `U`, the one dual to `v`.
* `epi_fst_of_isPullback`, `epi_snd_of_isPullback`: **Prop. 5, epimorphism half** (p. 5). In a
  pullback square of an abelian category, the base change of an epimorphism is an epimorphism.
  The monomorphism half holds in any category and is Mathlib's `IsPullback.mono_fst_of_mono`.
* `mono_inl_of_isPushout`, `mono_inr_of_isPushout`: the dual of Prop. 5 for pushouts.

**Not formalised.** Prop. 1 (existence of pullbacks and pushouts) is crossed out in the
typescript and is Mathlib's `HasPullbacks`/`HasPushouts` instance for abelian categories; Prop. 3
(also crossed out) is `IsPullback.hom_ext`; Prop. 6 (pasting) is Mathlib's `IsPullback.paste_horiz`.

The general statements live in `Bourbaki/Upstream/AbelianCommSqExact.lean`, under Mathlib's
names for the arrows of `IsPullback t l r b` (here `t = V`, `l = U`, `r = u`, `b = v`):
`CommSq.isPullback_of_exact`, `CommSq.isPullback_iff_exact`, `CommSq.isPushout_of_exact`,
`CommSq.isPushout_iff_exact`, `CommSq.shortComplex'IsoShortComplex`,
`IsPullback.isPushout_of_epi_bottom`, `IsPullback.isPushout_of_epi_right`,
`IsPushout.isPullback_of_mono_left`, `IsPushout.isPullback_of_mono_top`,
`IsPullback.epi_fst_of_epi`, `IsPullback.epi_snd_of_epi`, `IsPushout.mono_inl_of_mono`,
`IsPushout.mono_inr_of_mono`. The names below are kept for the articles that cite them.
-/

namespace Bourbaki.Redaction321

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {P A B Q : C} {V : P ⟶ A} {U : P ⟶ B} {u : A ⟶ Q} {v : B ⟶ Q}

/-- The automorphism of `A ⊞ B` that is the identity on `A` and `-1` on `B`. -/
noncomputable abbrev biprodNegIso (A B : C) : A ⊞ B ≅ A ⊞ B := biprod.negRightIso A B

/-- The two short complexes attached to a commutative square, the pullback one
`P → A ⊞ B → Q` with maps `(V, U)` and `u - v` and the pushout one with maps `(V, -U)` and
`u + v`, are isomorphic through the sign automorphism of `A ⊞ B`. -/
noncomputable abbrev shortComplexIso (sq : CommSq V U u v) :
    sq.shortComplex' ≅ sq.shortComplex :=
  sq.shortComplex'IsoShortComplex

/-- **Prop. 2, pullback half, converse** (rédaction n° 321, p. 4). A commutative square whose
sequence `0 → P → A ⊞ B → Q` is exact is a pullback square. -/
theorem isPullback_of_exact (sq : CommSq V U u v) (h : sq.shortComplex'.Exact)
    [Mono sq.shortComplex'.f] : IsPullback V U u v :=
  sq.isPullback_of_exact h

/-- **Prop. 2, pullback half** (rédaction n° 321, p. 4). A commutative square is a pullback iff
the sequence `0 → P → A ⊞ B → Q`, with maps `(V, U)` and `u - v`, is exact. -/
theorem isPullback_iff_exact (sq : CommSq V U u v) :
    IsPullback V U u v ↔ sq.shortComplex'.Exact ∧ Mono sq.shortComplex'.f :=
  sq.isPullback_iff_exact

/-- **Prop. 2, pushout half, converse** (rédaction n° 321, p. 4). A commutative square whose
sequence `P → A ⊞ B → Q → 0` is exact is a pushout square. -/
theorem isPushout_of_exact (sq : CommSq V U u v) (h : sq.shortComplex.Exact)
    [Epi sq.shortComplex.g] : IsPushout V U u v :=
  sq.isPushout_of_exact h

/-- **Prop. 2, pushout half** (rédaction n° 321, p. 4). A commutative square is a pushout iff
the sequence `P → A ⊞ B → Q → 0`, with maps `(V, -U)` and `u + v`, is exact. -/
theorem isPushout_iff_exact (sq : CommSq V U u v) :
    IsPushout V U u v ↔ sq.shortComplex.Exact ∧ Epi sq.shortComplex.g :=
  sq.isPushout_iff_exact

/-- **Prop. 4** (rédaction n° 321, p. 4; Stacks 08N4). A pullback square in which `v` is an
epimorphism is also a pushout square. -/
theorem isPushout_of_isPullback_of_epi_right (h : IsPullback V U u v) [Epi v] :
    IsPushout V U u v :=
  h.isPushout_of_epi_bottom

/-- **Prop. 4**, the symmetric case: a pullback square in which `u` is an epimorphism is also a
pushout square. -/
theorem isPushout_of_isPullback_of_epi_bottom (h : IsPullback V U u v) [Epi u] :
    IsPushout V U u v :=
  h.isPushout_of_epi_right

/-- **The dual of Prop. 4** (rédaction n° 321, p. 4). A pushout square in which `U` is a
monomorphism is also a pullback square. -/
theorem isPullback_of_isPushout_of_mono_top (h : IsPushout V U u v) [Mono U] :
    IsPullback V U u v :=
  h.isPullback_of_mono_left

/-- The dual of Prop. 4, the symmetric case: a pushout square in which `V` is a monomorphism is
also a pullback square. -/
theorem isPullback_of_isPushout_of_mono_left (h : IsPushout V U u v) [Mono V] :
    IsPullback V U u v :=
  h.isPullback_of_mono_top

open ZeroObject in
/-- The dual of Prop. 4 fails when the monomorphism is the bottom arrow `u : A → Q` rather than
the top arrow `U : P → B`. For a nonzero `X`, the square with `P = X` and `A = B = Q = 0` is a
pushout, its bottom arrow `𝟙 0` is a monomorphism, and it is not a pullback. -/
theorem not_isPullback_of_isPushout_of_mono_bottom {X : C} (hX : ¬ IsZero X) :
    IsPushout (0 : X ⟶ 0) (0 : X ⟶ 0) (𝟙 0) (𝟙 0) ∧ Mono (𝟙 (0 : C)) ∧
      ¬ IsPullback (0 : X ⟶ 0) (0 : X ⟶ 0) (𝟙 0) (𝟙 0) := by
  have hepi : Epi (0 : X ⟶ 0) := ⟨fun _ _ _ => (isZero_zero C).eq_of_src _ _⟩
  refine ⟨IsPushout.of_vert_isIso_epi ⟨by simp⟩, inferInstance, fun h => hX ?_⟩
  have := h.mono_fst_of_mono
  exact IsZero.of_mono_zero X 0

/-- **Prop. 5, epimorphism half** (rédaction n° 321, p. 5). In a pullback square of an abelian
category, if `v` is an epimorphism, so is `V`. -/
theorem epi_fst_of_isPullback (h : IsPullback V U u v) [Epi v] : Epi V :=
  h.epi_fst_of_epi

/-- **Prop. 5, epimorphism half**, the symmetric case: if `u` is an epimorphism, so is `U`. -/
theorem epi_snd_of_isPullback (h : IsPullback V U u v) [Epi u] : Epi U :=
  h.epi_snd_of_epi

/-- The dual of Prop. 5 for pushouts: if `U` is a monomorphism, so is `u`. -/
theorem mono_inl_of_isPushout (h : IsPushout V U u v) [Mono U] : Mono u :=
  h.mono_inl_of_mono

/-- The dual of Prop. 5 for pushouts, the symmetric case: if `V` is a monomorphism, so is `v`. -/
theorem mono_inr_of_isPushout (h : IsPushout V U u v) [Mono V] : Mono v :=
  h.mono_inr_of_mono

end Bourbaki.Redaction321
