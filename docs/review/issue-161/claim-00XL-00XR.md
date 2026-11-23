# Draft review claim on AxiomMath/Stacks: 00XL, 00XR, 00XX, cocontinuous functors

Draft for Michel (issue #161, move 3, rank 2 of `targets.md`). It is not posted. The fields
follow the `claim.yml` form of AxiomMath/Stacks. Everything was read at Stacks commit `f56a316`,
against Mathlib `56a0058` (v4.35.0, the Stacks pin) and Mathlib `master` of 23 Nov 2026. The Stacks
statements were read on the Stacks Project site and are paraphrased, not copied.

Suggested title: `[claim] 00XL, 00XR, 00XX: Sheaf pullback along a cocontinuous functor (StacksFrontier → StacksCore)`

---

**Task, tag or exercise.** 00XL, 00XR, 00XX

**Target tier.** Moving StacksFrontier code into StacksCore

**Statement.**

- *00XL (Sites and Sheaves, Lemma 7.20.3).* For a cocontinuous functor `u : C → D` between sites,
  the functor `Sh(D) → Sh(C)`, `G ↦ (u^p G)^#`, is left adjoint to `{}_s u` and is exact.
- *00XR (Lemma 7.21.5).* If `u` is moreover continuous, and `g : Sh(C) → Sh(D)` is the morphism
  of topoi of `u`, then: (1) no sheafification is needed, `g^{-1}(G)(U) = G(u(U))`; (2) `g^{-1}`
  has a left adjoint `g_! = (u_p ·)^#`; (3) `g^{-1}` commutes with all limits and colimits.
- *00XX (Lemma 7.22.1).* If `u` is cocontinuous with a right adjoint `v : D → C`, then
  `(g_* F)(V) = F(v(V))`, that is `g_* F = v^p F`, and `g^{-1} G = (v_p G)^#`.

**Proposed Lean statement.** Paste as is; the form renders this field as Lean.

```lean
-- No new statement: the claim moves StacksFrontier/CategoryTheory/Sites/CoverLifting.lean
-- to StacksCore, with its current signatures. Coefficients are in any category `A`
-- (Stacks: sheaves of sets).

noncomputable def Functor.sheafPullbackCocontinuous [HasWeakSheafify J A] :
    Sheaf K A ⥤ Sheaf J A  -- G ↦ (u^p G)^#

-- 00XL, under [u.IsCocontinuous J K] [HasWeakSheafify J A]
--   [∀ F : Cᵒᵖ ⥤ A, u.op.HasPointwiseRightKanExtension F]
@[stacks 00XL] noncomputable def Functor.sheafAdjunctionPullbackCocontinuous :
    u.sheafPullbackCocontinuous A J K ⊣ u.sheafPushforwardCocontinuous A J K
@[stacks 00XL] instance Functor.preservesFiniteColimits_sheafPullbackCocontinuous :
    PreservesFiniteColimits (u.sheafPullbackCocontinuous A J K)
@[stacks 00XL] instance Functor.preservesFiniteLimits_sheafPullbackCocontinuous
    [HasFiniteLimits A] [HasSheafify J A] :
    PreservesFiniteLimits (u.sheafPullbackCocontinuous A J K)

-- 00XR, with u also continuous
@[stacks 00XR "(1)"] noncomputable def Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous :
    u.sheafPullbackCocontinuous A J K ≅ u.sheafPushforwardContinuous A J K
@[stacks 00XR "(1)"] noncomputable def Functor.sheafPullbackCocontinuousObjObjIso (G : Sheaf K A) (U : C) :
    ((u.sheafPullbackCocontinuous A J K).obj G).obj.obj (op U) ≅ G.obj.obj (op (u.obj U))
@[stacks 00XR "(2)"] noncomputable def Functor.sheafAdjunctionLowerShriek :
    sheafPullbackConstruction.sheafPullback u A J K ⊣ u.sheafPushforwardContinuous A J K
@[stacks 00XR "(3)"] instance Functor.preservesLimits_sheafPushforwardContinuous :
    PreservesLimits (u.sheafPushforwardContinuous A J K)
@[stacks 00XR "(3)"] instance Functor.preservesColimits_sheafPushforwardContinuous :
    PreservesColimits (u.sheafPushforwardContinuous A J K)

-- 00XX, for adj : u ⊣ v with u cocontinuous
@[stacks 00XX "(1)"] noncomputable def Functor.sheafPushforwardCocontinuousIsoRestriction :
    u.sheafPushforwardCocontinuous A J K ⋙ sheafToPresheaf K A ≅
      sheafToPresheaf J A ⋙ (whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj v.op
@[stacks 00XX "(2)"] noncomputable def Functor.sheafPullbackCocontinuousIsoLan :
    u.sheafPullbackCocontinuous A J K ≅ sheafToPresheaf K A ⋙ v.op.lan ⋙ presheafToSheaf J A
```

**Existing work.**

- The file to move: `StacksFrontier/CategoryTheory/Sites/CoverLifting.lean` (288 lines). It
  imports only Mathlib and `StacksCore.Tactic.StacksAttribute`, so the move needs nothing else from
  Frontier. 55 Frontier files import it directly; the move changes their import path and nothing else.
- It does not use `MorphismOfTopoi` and is independent of #25 (00XA, 00XC).
- Mathlib: `Functor.sheafPushforwardCocontinuous`, `Functor.sheafAdjunctionCocontinuous`,
  `sheafPullbackConstruction.sheafAdjunctionContinuous`, `Functor.ranAdjunction`,
  `sheafificationAdjunction`, in `Mathlib/CategoryTheory/Sites/CoverLifting.lean` and
  `Mathlib/CategoryTheory/Sites/Pullback.lean`.
- Cocontinuity is Mathlib's `Functor.IsCocontinuous`, already registered for 00XJ in
  `StacksCore/CategoryTheory/Sites/Cocontinuous/CocontinuousDefs.lean`.

**Proof outline.** No proof changes. 00XL restricts the composite of the adjunctions
`u.op.ranAdjunction` and `sheafificationAdjunction` to sheaves. Exactness comes from the left
adjoint on one side and, on the other, from the left exactness of sheafification (00WJ, the
`HasSheafify` hypothesis). 00XR (1) and 00XX are uniqueness of adjoints. 00XR (2) and the colimit
half of (3) are Mathlib's adjunctions.

Points the review should settle before the move:

1. **The file fills two TODOs of Mathlib.** `Mathlib/CategoryTheory/Sites/CoverLifting.lean`
   names `G.sheafPullbackCocontinuous A J K` and its comparison with
   `sheafPushforwardContinuous` as TODOs. They are still open at the Stacks pin and on Mathlib
   `master` (23 Nov 2026). The conventions say a tag Mathlib covers is registered with
   `add_to_stacks`. The maintainers may prefer to upstream these declarations to Mathlib first and
   register them, rather than keep them in Core.
2. **Two declarations wrap Mathlib's names.** `sheafAdjunctionLowerShriek` (00XR (2)) is
   definitionally `sheafPullbackConstruction.sheafAdjunctionContinuous`, and
   `preservesColimits_sheafPushforwardContinuous` (00XR (3)) is the left-adjoint half of Mathlib's
   `sheafAdjunctionCocontinuous`. For these parts `add_to_stacks` on the Mathlib names would do.
3. **A parallel copy of 00XL.** `StacksFrontier/CategoryTheory/Sites/Cocontinuous/CocontinuousAdjunction.lean`
   defines `gInv`, which is `sheafPullbackCocontinuous` for `A = Type u`, together with `gStar`,
   `main_adjunction00XO` (the same proof term as `sheafAdjunctionPullbackCocontinuous`) and
   `main_left_exact`. It tags them 00XO, but they prove the statement of 00XL. The convention
   « reuse existing definitions » asks that Core keep one and that the other be retagged or
   removed. The names `main_adjunction00XO` and `main_left_exact` are not in Mathlib style.
4. **00XO is not formalized in its generality.** 00XO (Lemma 7.21.1) says that `{}_s u` and
   `(u^p ·)^#` form a morphism of topoi for every cocontinuous `u`. The Frontier declarations
   tagged 00XO are either unbundled (point 3) or assume `u` continuous as well:
   `Functor.morphismOfTopoiOfCocontinuous` (`Sites/Cohomology/FibredCategory/RingedToposOfAMorphism.lean`)
   and `morphismOfTopoi_of_isCocontinuous` (`Sites/MorphismOfSites/CocontinuousSmallModel.lean`).
   Once `MorphismOfTopoi` is in Core (#25), 00XO follows from 00XL in a few lines. It is left out
   of this claim and can be a follow-up claim.
5. **Generality.** The file works with coefficients in any category `A` and arbitrary universes,
   under `HasWeakSheafify`/`HasSheafify` and pointwise right Kan extensions along `u.op`. Stacks
   works with sheaves of sets. The statements are at least as general as the source.
6. **SGA 4 references.** Checked against the numbering of KokunoYumeto's English translation
   (`KokunoYumeto/sga-en`), which keeps the original numbering; not yet against a scan of the
   1972 edition.
   - On `sheafAdjunctionPullbackCocontinuous`:
     - `sga "4 IV 4.7" "partial"` and `sga "4 III 5.3" "more general"` are correct. 4.7 builds the
       morphism of topoi of a cocontinuous functor from III 2.3, and III 5.3 is the case of a
       localization `j_X`.
     - `sga "4 IV 4.6.1" "partial"`: 4.6.1 is the presheaf case, so "special case" would describe
       it better.
     - The primary source, III 2.3 3) (the right adjoint `u_*`), is missing.
   - On the exactness instances: `sga "4 III 2.3" "clause 1"` on the finite-colimit instance is
     correct. III 2.3 1) also gives exactness, but the finite-limit instance carries no `sga`
     attribute.
   - On `sheafPullbackCocontinuousIsoSheafPushforwardContinuous`, `sga "4 III 2.7" "more general"`
     is doubtful. III 2.7 is an example (an open subspace), and the identification it records is
     with the pushforward along a right adjoint, closer to 00XX than to 00XR (1). The proof of
     III 2.6 uses 00XR (1) implicitly.
   - On `sheafAdjunctionLowerShriek`, all six attributes check out:
     - `sga "4 III 1.3" "1)"`, `"4 IV 4.9.1"`, `"4 IV 4.7"` and `"4 III 5.3"` are correct.
     - `"4 IV 4.7.4"` is correct for the sufficiency direction.
     - `"4 IV 4.6.1"` is the presheaf case.
   - On the two `(3)` instances:
     - `sga "4 III 2.6"` is correct for both, and `sga "4 III 2.3"` for colimits.
     - `sga "4 IV 3.1.2" "special case"` is loose: the proof uses that a right adjoint preserves
       limits (I 2.11), not 3.1.2.
   - On `restrictionIsoLanOfAdjunction`, `sga "4 I 5.5"` and `"4 I 5.5.2"` are correct, with the
     roles of `u` and `v` exchanged with respect to SGA 4. The other isomorphism of I 5.5,
     `ranIsoRestrictionOfAdjunction`, has no attribute.
7. **Untagged declarations.** `sheafPullbackAdjunctionOfAdjunction`,
   `isRightAdjoint_sheafPullback_of_continuous_leftAdjoint`,
   `whiskeringLeftAdjunctionOfAdjunction`, `ranIsoRestrictionOfAdjunction` and
   `restrictionIsoLanOfAdjunction` formalize no tag. They are auxiliary to 00XX and would move
   with the file.

**References.** Stacks Project, Tags 00XJ, 00XL, 00XO, 00XR, 00XX, 00WJ. SGA 4, Exposé I 5.5;
Exposé III 1.3, 2.3, 2.6, 2.7, 5.3; Exposé IV 4.6.1, 4.7, 4.9.1 (numbering checked in the English
translation `KokunoYumeto/sga-en`). Mathlib, `Mathlib/CategoryTheory/Sites/CoverLifting.lean`
(the two TODOs).

**Before submitting.** Michel ticks the two checkboxes after checking the open claims (#8 and #25
on 23 Nov).

---

## Why this one second

- One file, no dependency on #25, the same chapter as #25.
- It serves GrothendieckTopoi 2.4 (`GeometricMorphism.exists_of_isCocontinuous`) at the same
  generality.
- Point 1 can also lead to a Mathlib pull request, through the `contribute-to-mathlib` skill, if
  the maintainers prefer that route.
