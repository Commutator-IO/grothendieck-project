# What AxiomMath's Stacks library can fill in the edition's Lean files (2026-11-15)

## Scope and method

This review asks which Lean results of the edition were left unproved, or proved only in part,
because Mathlib lacked a notion or a theorem, and whether the Lean formalization of the Stacks
Project published by AxiomMath (<https://github.com/AxiomMath/Stacks>, Apache-2.0) now supplies
the missing piece.

The edition's side was read from three places: the `lean` field of the entries of
`src/content/findings.ts` (49 entries whose text says « Partly », « not proved », or names a
Mathlib gap), the docstrings of `lean/Grothendieck/*.lean` that state what Mathlib does not have,
and the « not formalised » paragraphs of `docs/lean/sections/*.tex`. The 383 findings without a
`lean` field were screened by keyword for algebraic geometry (schemes, sheaves, étale, flat,
descent, cohomology, EGA/SGA): 197 match, of which 128 are neither matched nor refuted. Those
are research-level statements about moduli, abelian schemes, étale cohomology or topoi, and none
of them is within reach of a single Stacks declaration; they are summarised at the end rather
than ranked.

The Stacks side is a copy of the upstream default branch taken on 2026-11-15 (64,215 Lean files,
StacksCore human-reviewed, StacksFrontier AI-written, no `sorry`). Declarations were located by
their `@[stacks TAG]`, `@[ega …]` and `@[sga …]` attributes, by file and declaration names, and
by reading statements. For each candidate file the column « closure » counts the Stacks files it
pulls in transitively through its `import StacksCore.…`/`import StacksFrontier.…` lines, the file
itself included. Mathlib imports are not counted: our Mathlib (`715a03a`) is already built, and
every Mathlib module imported by the closures used below exists at our pin.

Feasibility is graded as: **done** (proved in this round), **high** (closure small, statement
fills the gap directly), **medium** (closure small, but real glue work or a partial fill),
**low** (closure above about 40 files, or the Stacks result covers only part of the gap), and
**none** (nothing relevant found).

## Ranked table

| # | Item (cote, finding or file) | Missing piece | Stacks declaration(s), file, tier | Closure | Feasibility |
|---|---|---|---|---|---|
| 1 | 22, `22-power-series-discrete-obstruction` (`Folder22.lean`) | the `t`-adic half: `k[[t]]` formally smooth over `k` for the `t`-adic topology; Mathlib has no formal smoothness of topological rings | `RingHom.FormallySmoothNAdic` (tag 07NI), `StacksFrontier/RingTheory/FormallySmooth/Topological.lean`; `powerSeries_hom_ext`, `StacksFrontier/RingTheory/MvPowerSeries/HomExt.lean`; Frontier | 3 | **done** (`Folder22Adic.lean`) |
| 2 | FG_IL_5_SGA6_2_3, `FG_IL_5_SGA6_2_3-K0-triangulated-basics`, section `ihes-sga6-2-3` | `K(A) ≅ K(D^b(A))` for an abelian `A` (n° 2); Mathlib has no `K₀` of an abelian category | `DerivedCategory.Bounded.exists_addEquiv_K0` (tag 0FCP), `StacksFrontier/Algebra/Homology/DerivedCategory/KGroup.lean`; `KZero` (02MU); `Pretriangulated.K0` (0FCN); Frontier, two Core files in the closure | 7 | **done** (`IhesSGA6_2_3Db.lean`) |
| 3 | 94, `94-generic-tor-regular-sequences` (`Folder94.lean`) | the Koszul step: from `R_𝔭`-regularity of `t` to vanishing of the higher homology; Mathlib has no Koszul complex of a sequence | `Koszul.IsKoszulRegularOn`, `Koszul.IsKoszulRegular` (062E), `isKoszulRegularOn_and_isKoszulRegular_of_regular` (062F), `StacksFrontier/RingTheory/Koszul/Regular.lean`; Frontier | 9 | **done**, in Koszul-homology form (`Folder94Koszul.lean`); the identification with Mathlib's `Tor` is not made |
| 4 | 94, same finding, Lemme 16 | generic flatness for `X` of finite type over `S` | `Module.exists_ne_zero_free_localizedModule_away` (051R; EGA IV 6.9.2), `StacksFrontier/Algebra/Category/Ring/Epi/GenericFlatness/Noetherian.lean`; `…/GenericFlatness/FinitePresentation.lean` (051S); Frontier | 5 (6 for 051S) | **high**: the file elaborates unchanged against our Mathlib (checked). Remaining work: pass from a domain to the reduced ring `A/J` through its finitely many minimal primes, and give the `J`-adic layers of a finite `B`-module their `B/JB`-module structure |
| 5 | FG_IL_5_SGA6_2_3, section `ihes-sga6-2-3` | the Euler formula `Σ(−1)ⁱχ(Xⁱ) = Σ(−1)ⁱχ(Hⁱ)` for any additive function on an abelian category (proved only for dimensions) | `KZero.lift`, `KZero.universal` (02MU), `StacksFrontier/CategoryTheory/Abelian/GrothendieckGroup.lean`; Euler characteristic `eulerChar` in `…/DerivedCategory/KGroup.lean`; Frontier | 2 (7) | **high**: `KZero` is the universal additive function, so the formula reduces to one identity in `KZero A`, by the usual two short exact sequences per degree |
| 6 | 55, `55-lemma-b-identity-principle` (`Folder55.lean`) | coherent sheaves on a ringed space, to show that the identity principle (v) gives the uniformity used in Lemme B | `SheafOfModules.IsCoherent` (01BV, EGA 0 5.3.7), `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`; Frontier | 5 | **medium**: the definition and finite-type closure properties are there; supports of `O/J`, stalks and primary decomposition at stalks still have to be written |
| 7 | 128, `128-nilpotent-conductor-flat-descent` (`Folder128.lean`) | Cor. 2 and 3 (preschemes, flat base change); faithfully flat descent of modules beyond comonadicity | faithfully flat effective descent of modules (023N), `StacksFrontier/AlgebraicGeometry/Descent/Modules/FaithfullyFlatEffectiveDescent.lean`; effective descent (08XA), `…/Descent/Modules/EffectiveDescent.lean`; Milnor patching (0D2F), `StacksFrontier/RingTheory/MilnorPatching/ModuleCategory.lean`; Frontier | 23; 21; 4 | **medium** for the affine statements (our file already proves flat descent directly); **low** for the prescheme corollaries, which need gluing along schemes |
| 8 | 100, `100-baire-dimension-one-points` (`Folder100.lean`) | the page's own route through Cohen's structure theorem (the statement itself is already proved another way) | Cohen structure theorem (0323, 032A), `StacksFrontier/RingTheory/CompleteLocalRing/CohenStructureTheorem/CoefficientRing.lean`; complete regular local rings (0C0S), `…/CompleteLocalRing/Regular.lean`; Frontier | 96; 101 | **low**: closure too large, and the finding is already settled |
| 9 | 101, `101-sheaf-duality-dim-one` (`Folder101.lean`) | Ext and local cohomology of `O_X`-modules on `Spec A`; the identification of `Ext¹_A(K, A)` with a cokernel | local cohomology (0952, 0A6R), `StacksFrontier/RingTheory/LocalCohomology/CechModel.lean`, `StacksFrontier/RingTheory/Dualizing/LocalCohomology/RightAdjoint.lean`; Frontier | 102 | **low**; the `Ext¹` identification is better done with Mathlib's own `Ext` long exact sequence |
| 10 | 22, docstring of `Folder22.lean` | Cohen algebras, formal smoothness and geometric regularity (3.2, 3.6–3.13) | formally smooth ⇔ geometrically regular (07NQ), `StacksFrontier/RingTheory/GeometricallyRegular/FormalSmoothness.lean`; regular local rings (07EI), `StacksFrontier/RingTheory/FormallySmooth/RegularLocal.lean`; the multivariable power-series transfer (EGA 0 19.3.4), `StacksFrontier/RingTheory/FormallySmooth/CompleteLocalTransfer.lean`; Frontier | 397; 227; 628 | **low** (closures) |
| 11 | 29, `29-inertia-matrix-determinant` (`Folder29.lean`) | tame inertia of regular schemes, the Kummer computation of the inertia map | Abhyankar's lemma (0BRM), `StacksFrontier/RingTheory/DiscreteValuationRing/Abhyankar/AbhyankarLemma.lean`; tame covers along a regular divisor (0EYG), `StacksFrontier/AlgebraicGeometry/FundamentalGroup/Abhyankar/RegularDivisorUnconditional.lean`; Frontier | 279; 4,384 | **low** |
| 12 | 2, `2-trivial-total-chern-class` (`Folder2.lean`) | the K-group of coherent sheaves and Chern classes, to see that `i_!(O_Y)` is nonzero | Grothendieck groups of coherent and perfect complexes, `StacksFrontier/AlgebraicGeometry/Perfect/GrothendieckGroupCoherentNonzero.lean`; first Chern class of divisors, `StacksFrontier/AlgebraicGeometry/Divisors/WeilDivisorClass/FirstChernClassInjective.lean`; Frontier | 254; 991 | **low**; no total Chern class on `K` was found |
| 13 | 29, `29-degree-n-as-primitive` | universal effective descent morphisms in general, and for finite sets | descent along coverings of a site, `StacksFrontier/CategoryTheory/Sites/Stack/EffectiveDescent*.lean`; Frontier | not counted | **none** for the categorical statement needed (effective descent for an abstract class of morphisms in a category, and its identification in `FintypeCat`) |
| 14 | FG_IL_5_SGA6_2_4, `FG_IL_5_SGA6_2_4-ext-effaceability-criterion` | effaceability of positive-degree `Ext` classes in an arbitrary abelian category | `StacksCore/CategoryTheory/Abelian/DeltaFunctor/Effaceable.lean` (universality of effaceable δ-functors); Core | 4 | **none**: it is the converse direction (effaceable ⇒ universal); the effaceability of Yoneda classes is not there |
| 15 | 145, `145-unit-exponent-exercise` | free profinite groups, `ℤ̂`-powers | profinite integers only (`StacksFrontier/NumberTheory/TraceFormula/ProfiniteIntegersProcyclic.lean`) | — | **none** |
| 16 | 115, `115-isbell-duality-derived-from-kernels` | Isbell duality | — | — | **none** |
| 17 | 161-3, three findings | a 2-category of topoi | ringed topoi and their morphisms appear in many files, but not a 2-category of topoi with localic products | — | **none** for the statement needed |
| 18 | 113, `Folder113.lean` | projective generators of a functor category | only for derived categories of schemes (`StacksFrontier/AlgebraicGeometry/Perfect/ProjectiveGenerator*.lean`) | — | **none** |
| 19 | 46, `46-semilocal-hilbert90-inertia` | Lang's theorem over a finite residue field; completion and Artin–Rees descent in the wild case | nothing found by name for Lang's theorem | — | **none** |
| 20 | 13, 1, 150, 152, 154, 88 and the other non-geometric gaps (Lindemann, Schatten classes, stratified spaces, maps on surfaces, oriented matroids) | outside algebraic geometry | — | — | **none**: out of the library's scope |

## Notes on the three proofs written

**Folder 22, the `t`-adic half** (`lean/Grothendieck/Folder22Adic.lean`). For every commutative
ring `k`, `C : k → k[[t]]` satisfies `RingHom.FormallySmoothNAdic` for the ideal `(t)`
(`formallySmoothNAdic_C_X`), for every ideal containing `t` (`formallySmoothNAdic_C_of_X_mem`),
and over a field for the maximal ideal (`formallySmoothNAdic_C_maximalIdeal`); `adic_not_discrete`
puts the two halves of pages 22 and 24 side by side for `k = ℚ(x_i : i ∈ I)`, `I` infinite. The
argument lifts the image of `t` to a nilpotent element, evaluates power series there with
Mathlib's `PowerSeries.eval₂Hom`, and checks the lift with the Stacks uniqueness lemma
`powerSeries_hom_ext`. It is the one-variable case of a Stacks theorem whose file has too large a
closure to vendor, rewritten for `PowerSeries`.

**SGA 6 2/3, `K(A) ≅ K(D^b(A))`** (`lean/Grothendieck/IhesSGA6_2_3Db.lean`). The edition's
`K₀` of a pretriangulated category is definitionally the Stacks `Pretriangulated.K0`
(`K₀_eq_K0`, by `rfl`), so tag 0FCP applies as stated: `exists_addEquiv` gives the isomorphism
with `[X] ↦ cl(X[0])`, `addEquiv_unique` its uniqueness, and `exists_cl_eq` the corollary that
every element of `K(A)` corresponds to the class of one object of `D^b(A)`.

**Folder 94, the Koszul step of Lemme 6** (`lean/Grothendieck/Folder94Koszul.lean`).
`exists_isOpen_dense_isKoszulRegularOn`: on the dense open of the existing
`exists_isOpen_dense_isWeaklyRegular'`, every `A_𝔭`-weakly regular sequence `t` has acyclic
Koszul complex `K_•(t)` and `H_i(K_•(t) ⊗ R_𝔭) = 0` for `i > 0`. The first vanishing makes
`K_•(t)` a free resolution of `A_𝔭/(t)`, so the second is the vanishing of
`Tor_i(R_𝔭, A_𝔭/(t))`; the comparison with Mathlib's derived-functor `Tor` is not formalised.

All three files elaborate under `lake build` (with the project's `warningAsError = true`), and
`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for every theorem.

## Vendoring

Sixteen Stacks files (472 KB of source) are copied to `lean/Stacks/`, at their upstream module
paths, with the upstream `LICENSE` and a `NOTICE.md`. Two library entries in
`lean/lakefile.toml` (`StacksCore`, `StacksFrontier`, `srcDir = "Stacks"`, globs on the module
prefix, warnings not errors) make the imports resolve. Every copied file elaborates unchanged
against Mathlib `715a03a`: no API drift had to be fixed, and the attribute files
(`StacksCore/Tactic/StacksAttribute.lean`, `EgaSgaAttribute.lean`) are vendored as they are, so
no attribute was stripped. The generic-freeness files of row 4 were also copied and built
without change, then removed again since no proof uses them yet; they can be re-vendored as they
are.

## Findings without a Lean entry

Of the 128 unsettled algebraic-geometry findings with no `lean` field, the statements concern
moduli of abelian varieties and curves (6, 9, 59, 64, 123, 147), ℓ-adic and tame monodromy (12,
34, 36, 60), topoi and stacks (103, 134-1, 161-2), representability and descent of functors (94,
102, 126, 127, 131), and group schemes (27, 45, 57, 129, 133). The library offers the
infrastructure several of them start from (fpqc descent, Artin's axioms, Picard schemes, étale
fundamental groups, local cohomology), but each claim is a new statement whose proof would be a
project of its own, and none can be closed by citing a declaration. The nearest is
`23-finite-normalisation-quotient-of-regular` (finiteness of normalisation for quotients of
regular rings), for which the library's Nagata and excellence material would be the place to
look first.
