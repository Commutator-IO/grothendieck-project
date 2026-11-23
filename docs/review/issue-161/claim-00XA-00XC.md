# Draft review claim on AxiomMath/Stacks: 00XA and 00XC, morphisms of topoi

Draft for Michel (issue #161, move 3). It is not posted. The fields follow the
`claim.yml` issue form of AxiomMath/Stacks. Everything below was read at Stacks commit `f56a316`
(18 Nov 2026, the pin of the fork `mycaule/Stacks`). Statements are paraphrased: no Stacks Project
prose is copied.

---

**Task, tag or exercise.** 00XA, 00XC

**Target tier.** Moving StacksFrontier code into StacksCore

**Statement.**

- *00XA (Sites and Sheaves, definition of a morphism of topoi).* For sites `C` and `D`, a morphism
  of topoi `Sh(D) → Sh(C)` is a pair of functors `f_* : Sh(D) → Sh(C)` and `f⁻¹ : Sh(C) → Sh(D)`,
  with an adjunction `f⁻¹ ⊣ f_*`, such that `f⁻¹` commutes with finite limits (1). Morphisms
  compose by composing the direct images and, in the opposite order, the inverse images (2).
- *00XC (Sites and Sheaves, lemma).* A morphism of sites `f : D → C` given by `u : C → D`
  induces a morphism of topoi `Sh(D) → Sh(C)`, with `f⁻¹ = u_s` and `f_* = u^s`.

**Proposed Lean statement.** No new statement. The claim moves these declarations, with their
current signatures:

```lean
-- StacksFrontier/CategoryTheory/Sites/Topos/MorphismOfTopoi.lean
structure MorphismOfTopoi (E : Type u) [Category.{v} E] (F : Type u') [Category.{v'} F] where
  pushforward : E ⥤ F
  inverseImage : F ⥤ E
  adj : inverseImage ⊣ pushforward
  preservesFiniteLimits : PreservesFiniteLimits inverseImage

@[stacks 00XC]
noncomputable def CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi
    {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {u : C ⥤ D}
    (h : u.IsMorphismOfSites J K) :
    MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w))

-- StacksFrontier/CategoryTheory/Sites/Topos/ToposDefs.lean
@[stacks 00XA "(1); …"]
abbrev SheafToposMorphism (J : GrothendieckTopology C) (K : GrothendieckTopology D) :=
  MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w))

@[stacks 00XA "(2)"]
abbrev SheafToposMorphism.comp (f : SheafToposMorphism J K) (g : SheafToposMorphism K L) :
    SheafToposMorphism J L
```

There is one addition: a bridge lemma, so that 00XC is stated for the morphisms of sites of 00X1.

```lean
theorem Stacks.Sites.Site.IsMorphismOfSites.toFunctor
    {SC : Site C} {SD : Site D} {u : C ⥤ D} (h : Site.IsMorphismOfSites SC SD u) :
    u.IsMorphismOfSites SC.topology SD.topology
```

**Existing work.**

- The three files to move: `StacksFrontier/CategoryTheory/Sites/MorphismOfSites.lean` (for
  `Functor.IsMorphismOfSites`), `…/Sites/Topos/MorphismOfTopoi.lean` and `…/Sites/Topos/ToposDefs.lean`.
  Their closure inside the library is these three files. They import only Mathlib and
  `StacksCore.Tactic.*`, so the move needs nothing else from Frontier.
- `MorphismOfTopoi` is used by 716 Frontier files, and `IsMorphismOfSites.morphismOfTopoi` by 19.
  Moving it to Core changes their imports and nothing else.
- `Stacks.Sites.Site.IsMorphismOfSites` (00X1) and `Stacks.Sites.Site.IsContinuous` (00WV), in
  `StacksFrontier/CategoryTheory/Sites/FamilySite.lean`, for the bridge lemma.
- Mathlib: `Functor.sheafPullback`, `Functor.sheafPushforwardContinuous`,
  `Functor.sheafAdjunctionContinuous`, `Functor.IsContinuous`.

**Proof outline.** No proof changes for 00XA, which is definitional, or for 00XC, which assembles
Mathlib's adjunction. The bridge lemma uses 00WW: a functor continuous in the sense of 00WV
satisfies Mathlib's `Functor.IsContinuous`. The two exactness fields then carry over, after
identifying `Functor.sheafPullbackConstruction.sheafPullback` with Mathlib's `Functor.sheafPullback`
(both are left adjoints of the same pushforward). 00WW is in Frontier only:
`isContinuous_toGrothendieck_of_preservesLimit_cospan`, in
`StacksFrontier/CategoryTheory/Sites/Continuous/SheafRestriction.lean`, stated for pretopologies.
Since `FamilySite.lean` is Frontier too, the bridge lemma stays in Frontier, which may import Core.
Moving it to Core would pull in 00WV, 00WW and 00X1 and enlarge the claim.

Points the review should settle before the move (the reason for this claim):

1. **00XC is proved in greater generality than stated.** `Functor.IsMorphismOfSites` asks for
   Mathlib's continuity, which is the conclusion of 00WW and weaker than continuity in the sense of
   00WV. The file's own docstring says so. That is allowed, since the result is more general, but
   then the tagged declaration is not about the 00X1 notion until the bridge lemma above exists.
2. **Parallel definitions.** Frontier has four notions named `IsMorphismOfSites`:
   - `Functor.IsMorphismOfSites` (`Sites/MorphismOfSites.lean`, `@[sga "4 IV 4.9.1"]`);
   - `Stacks.Sites.Site.IsMorphismOfSites` (`Sites/FamilySite.lean`, `@[stacks 00X1]`);
   - the class `IsMorphismOfSites` (`Sites/MorphismOfSites/MorphismDefs.lean`, also
     `@[sga "4 IV 4.9.1"]`, defined as the existence of a left exact left adjoint of the
     pushforward);
   - a ringed version in `Sites/Modules/LocallyRingedSites/MorphismsGeneral.lean`, with its own
     `morphismOfTopoi`.

   The convention « reuse existing definitions rather than introducing parallel ones » asks which
   one Core keeps. The two definitions both tagged `sga "4 IV 4.9.1"` are different, so at most one
   of them is SGA 4's.
3. **`LeftAdjointsPreserveFiniteLimits`** (`ToposDefs.lean`) formalises no tag, and its own
   docstring calls it false in general. On the one-point site, `X × -` is left adjoint to `X ⟹ -`
   but does not preserve the terminal object unless `X` is a singleton. It should stay behind or be
   removed rather than move to Core.
4. **SGA references to check against SGA 4.** `MorphismOfTopoi.id` and `MorphismOfTopoi.comp`
   carry `@[sga "4 IV 3.3.1"]`, and `Functor.IsMorphismOfSites` carries `@[sga "4 IV 4.9.1"]` and
   `@[sga "4 IV 4.9" "morphism of sites def"]`. These are not checked yet.
5. **Argument order.** `SheafToposMorphism.comp f g` is `f ∘ g` (`f : Sh(D) → Sh(C)`,
   `g : Sh(E) → Sh(D)`), whereas `MorphismOfTopoi.comp g f` takes the second morphism first.
   Mathlib naming would want a single convention.
6. **Universes.** `SheafToposMorphism` allows sites in any universes, with sheaves in `Type w`.
   `morphismOfTopoi` asks for `SmallCategory C`, `SmallCategory D` in `Type w`. That matches the
   Stacks Project's set-theoretic conventions for 00XC. A large-sections variant exists
   (`IsMorphismOfSites.morphismOfTopoiLargeSections`, `Sites/MorphismOfSitesLargeSections.lean`)
   and stays in Frontier.

**References.** Stacks Project, Tags 00XA, 00XC, 00X1, 00WV, 00WW. SGA 4, Exposé IV, 3.1–3.3 and
4.9.

**Before submitting.** Michel ticks the two checkboxes after checking the open claims (#8 was the
only one on 21 Nov).

---

## Why this one first

- The overlap survey found the largest overlap in GrothendieckTopoi Layer 1–2 (`targets.md`).
- `MorphismOfTopoi` is the definition under most of `Sites/Topos`, `Subtopos`, `SliceTopos` and
  `Point` (716 files), so the later review claims below build on it.
- The closure is three files, so the claim is small enough to show how long a review takes.

## Next review claims, once this one is approved

The order follows the roadmap targets they serve (`targets.md`).

1. 00XL, 00XR: a cocontinuous functor gives a morphism of topoi (`Sites/CoverLifting.lean`).
   Serves GrothendieckTopoi 2.4.
2. 04GZ, 04IP: slices `Sh(C)/F ≌ Sh(C/F)` and the localization morphism
   (`Sites/ToposLocalizationSheaf.lean`, `Sites/SliceTopos/`). Serves 3.1–3.2.
3. 00Y4, 00Y5, 00YA, 00YC: points of sites and of topoi (`Sites/Point/`). Serves 6.1.
4. 00YQ: Deligne's criterion (`Sites/Point/CriterionForExistenceOfPoints/DeligneCriterion.lean`).
   Serves 6.4.
5. 08LU, 08LV, 08LY, 08LZ: subtopoi, embeddings, open and closed subtopoi (`Sites/Subtopos/`).
   Definitions under 4.1, 4.3 and 9.2.
