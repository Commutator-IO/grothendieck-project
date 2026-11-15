import Buffalo.AG.Part01c
import StacksFrontier.RingTheory.Koszul.Regular
import StacksFrontier.RingTheory.RegularRing.Defs
import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing.PowerSeriesSurjection

/-!
# Buffalo, algebraic geometry, parts 05–06: regular rings, Koszul complexes and completions

Entries of `docs/buffalo-ag/index.tex` that `Part05c.lean` and `Part06b.lean` left partial or
unformalised because Mathlib (at `715a03a`) lacked the material, completed here with files of
AxiomMath/Stacks vendored under `lean/Stacks/` (Apache-2.0, see `lean/Stacks/NOTICE.md`).

* `Oqhr-Gt66es-7990` (Koszul complexes): `prop_7990_koszul`. The Koszul complex `K_•(x)` of a
  finite sequence and its homology are the Stacks definitions (`Koszul.IsKoszulRegularOn x M`
  says `H_i(K_•(x) ⊗ M) = 0` for `i ≠ 0`, tag 062E); acyclicity for an `M`-regular sequence is
  tag 062F (`Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular`).
* `Oqhr-Gt66es-8055` (`𝔾_m` and `GL_n` are regular): `prop_8055_Gm`, `prop_8055_GL`, from the
  regularity of localizations of a regular ring (`isRegularRing_of_isLocalization`, the lemma
  after tag 00OD in `StacksFrontier/RingTheory/RegularRing/Defs.lean`).
* `Oqhr-Gt66es-2525` (completions of noetherian rings are noetherian): `prop_2525_completion`,
  from tag 0316 (`AdicCompletion.isNoetherianRing`).
* `Oqhr-Gt66es-8250` (a noetherian local ring is regular iff its completion is):
  `prop_8250`. The completion has the same Krull dimension (`ringKrullDim_completion`, the
  statement of tag 07NV) and the same minimal number of generators of the maximal ideal
  (Mathlib's `AdicCompletion.spanFinrank_maximalIdeal_eq`). The two lemmas are proved here,
  following the argument of AxiomMath's `StacksFrontier/RingTheory/AdicCompletion/
  PermanenceOfProperties.lean` (tags 07NV, 07NY), whose own import closure (230 files) is too
  large to vendor: only the noetherianity of the completion (tag 0316, two files) is imported.
-/

open IsLocalRing

universe u

noncomputable section

namespace Buffalo.AG.Part06

/-- Oqhr-Gt66es-7990 (2:13:10) [prop] For an `M`-regular sequence `x₁, …, x_r` of `A`, the
Koszul complex `K_•(x) ⊗ M` is acyclic: `H_i(K_•(x) ⊗_A M) = 0` for `i ≠ 0`; in particular a
regular sequence of `A` has acyclic Koszul complex `K_•(x)`. The same holds for weakly regular
sequences (no condition `M ≠ (x)M`). Stacks tag 062F. -/
theorem prop_7990_koszul {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M] {r : ℕ}
    (x : Fin r → A) :
    (RingTheory.Sequence.IsWeaklyRegular M (List.ofFn x) → Koszul.IsKoszulRegularOn x M) ∧
    (RingTheory.Sequence.IsRegular M (List.ofFn x) → Koszul.IsKoszulRegularOn x M) ∧
    (RingTheory.Sequence.IsRegular A (List.ofFn x) → Koszul.IsKoszulRegular x) :=
  Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular

/-- Oqhr-Gt66es-8055 (2:14:15) [prop] (the case of `𝔾_m`) The ring `k[t, t⁻¹]` of the
multiplicative group, a localization of the regular ring `k[t]`, is regular. -/
theorem prop_8055_Gm (k : Type u) [Field k] :
    IsRegularRing (Localization.Away (Polynomial.X : Polynomial k)) :=
  isRegularRing_of_isLocalization (Submonoid.powers (Polynomial.X : Polynomial k))

/-- Oqhr-Gt66es-8055 (2:14:15) [prop] (the case of `GL_n`) The ring `k[T_ij][1/det]` of the
general linear group, a localization of the regular ring `k[T_ij]`, is regular. -/
theorem prop_8055_GL (k : Type u) [Field k] (n : Type u) [Fintype n] [DecidableEq n] :
    IsRegularRing (Buffalo.AG.Part01.OGL k n) :=
  isRegularRing_of_isLocalization (Submonoid.powers (Buffalo.AG.Part01.detP k n))

/-- Oqhr-Gt66es-8055 (2:14:15) [prop] A field is regular; if `A` is regular, so are `A[t]` and
every localization of `A`; hence `k[t₁, …, tₙ]`, `𝔾_{m,k}` and `GL_{n,k}` are regular. -/
theorem prop_8055_full (k : Type u) [Field k] (A : Type u) [CommRing A] [IsRegularRing A]
    (S : Submonoid A) (n : ℕ) (m : Type u) [Fintype m] [DecidableEq m] :
    IsRegularLocalRing k ∧ IsRegularRing (Polynomial A) ∧ IsRegularRing (Localization S) ∧
      IsRegularRing (MvPolynomial (Fin n) k) ∧
      IsRegularRing (Localization.Away (Polynomial.X : Polynomial k)) ∧
      IsRegularRing (Buffalo.AG.Part01.OGL k m) :=
  ⟨inferInstance, inferInstance, isRegularRing_of_isLocalization S, inferInstance,
    prop_8055_Gm k, prop_8055_GL k m⟩

/-- A noetherian local ring and its completion have the same Krull dimension (the statement of
Stacks tag 07NV). The completion is noetherian (tag 0316) and flat, hence has going down, and its
maximal ideal is `𝔪Â`, so the dimension formula for flat local maps has a zero-dimensional fibre
term. -/
theorem ringKrullDim_completion (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    ringKrullDim A = ringKrullDim (AdicCompletion (maximalIdeal A) A) := by
  let B := AdicCompletion (maximalIdeal A) A
  have : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(maximalIdeal_comap (algebraMap A B)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal A) (maximalIdeal B)
  have hm : maximalIdeal B = (maximalIdeal A).map (algebraMap A B) :=
    AdicCompletion.maximalIdeal_eq_map
  have : Nontrivial (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Ideal.Quotient.nontrivial_iff.mpr (hm ▸ (maximalIdeal.isMaximal B).ne_top)
  have hf : (maximalIdeal B).map
      (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) = ⊥ := by
    rw [hm]
    exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by simp)
  have hdim : (maximalIdeal B).height = (maximalIdeal A).height := by
    rw [hf] at h
    simpa using h
  rw [← maximalIdeal_height_eq_ringKrullDim (R := A),
    ← maximalIdeal_height_eq_ringKrullDim (R := B)]
  exact_mod_cast hdim.symm

/-- Oqhr-Gt66es-8250 (2:17:30) [prop] A noetherian local ring `A` is regular if and only if its
completion `Â` is: both conditions say that the maximal ideal is generated by `dim` elements,
and `A` and `Â` have the same dimension (`ringKrullDim_completion`) and the same minimal number
of generators of the maximal ideal. Stacks tag 07NY. -/
theorem prop_8250 (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsRegularLocalRing A ↔ IsRegularLocalRing (AdicCompletion (maximalIdeal A) A) := by
  rw [isRegularLocalRing_iff, isRegularLocalRing_iff, AdicCompletion.spanFinrank_maximalIdeal_eq,
    ← ringKrullDim_completion]

end Buffalo.AG.Part06

namespace Buffalo.AG.Part05

/-- Oqhr-Gt66es-2525 (0:42:05) [prop] (the two noetherian halves) A localization of a noetherian
ring is noetherian, and so is the completion `lim A/Iⁿ` of a noetherian ring with respect to the
powers of any ideal `I` (Stacks tag 0316); in particular the completion of a noetherian local
ring. -/
theorem prop_2525_completion (A : Type u) [CommRing A] [IsNoetherianRing A] (S : Submonoid A)
    (I : Ideal A) :
    IsNoetherianRing (Localization S) ∧ IsNoetherianRing (AdicCompletion I A) :=
  ⟨IsLocalization.isNoetherianRing S _ ‹_›, inferInstance⟩

end Buffalo.AG.Part05

end
