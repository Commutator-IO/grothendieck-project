# Open findings in an area of Stacks: literature re-check (23 November 2026)

A `/find-novelty` re-check of the 71 open rows that the Findings chart counts as « Open, beyond mathlib, in an area of Stacks » (`reach: 'beyond'`, `theory` matching `inStacks` in `src/components/FindingsChart.tsx`). It follows the Lean-reach sweep of 16 November (`stacks-findings-sweep-2026-11-16.md`). Only `literature`, `status` and `settle` change, never `lean`. A row is marked `matched` only when its statement was read in the cited source. Sources that were located but not read are recorded as such in the row. No row claims priority.

| Before → after | Rows |
|---|---|
| unsearched → matched | 5 |
| candidate → matched | 1 |
| unsearched → candidate | 32 |
| unsearched → unsearched | 1 (`41-irreducible-components-etale-criterion`: rests on illegible words) |
| candidate → candidate | 32 |

## Row by row

The `matched` rows come first, then the rest by `onPage` (proved, partial, stated).

| Row | onPage | Before | After | Reference |
|---|---|---|---|---|
| `100-neron-extension-p-divisible` | partial | unsearched | **matched** | SGA 7 I, exp. IX, Cor. 5.9 and Rem. 5.9.1 (Raynaud; any Néron model, S not henselian), statement without proof. |
| `130-neron-symbol-component-correction` | partial | unsearched | **matched** | Bosch–Lorenzini, Invent. Math. 148 (2002), §4 p. 377 and Thm 4.4, recalling Néron 1965 ch. III / Lang ch. 11 Thm 5.1. |
| `36-griffiths-conditional-l-adic` | partial | unsearched | **matched** | Katz, SGA 7 II Exp. XX « Le théorème de Griffiths », Th. 4.1 and Cor. 5.1 (hypotheses (B) and (4.1.2)) |
| `47-chow-fourier-todd-over-base` | partial | unsearched | **matched** | Deninger–Murre, Crelle 422 (1991), Prop. 2.2, Cor. 2.22; Hasan–…–Moonen, arXiv:2407.06184, Prop. 4.7(1), Rem. 4.6, Thm. 5.5(2). |
| `51-albanese-good-reduction-codim-two` | partial | unsearched | **matched** | Chung, « Semi-abelian reduction of Albanese varieties », arXiv:2608.14417 (2026), Thm 1.1 (geometrically R_1 special fibre ⇒ good reduction of Alb and Pic^0_red). |
| `FG_IL_2_GIRAUD69-total-obstruction-relative-classifying-topos` | stated | candidate | **matched** | Illusie, « Cotangent complex and deformations of torsors and group schemes », LNM 274 (1972), Thm 3.4 (H³(BG/S, ℓ^∨⊗I)) and Thm 5.3 (Ext²) |
| `43-local-cohomology-concentration` | proved | unsearched | candidate | Partial: Toën, arXiv:2308.01670 (2023), Prop. 1.2 and Def. 3.5 (fppf lower vanishing; J_x pro-represents H^d_x); Zariski concentration not found. |
| `100-formal-abelian-curve-criterion` | partial | unsearched | candidate | none found; algebraisation of formal abelian schemes via curves |
| `100-full-faithfulness-connected-components` | partial | unsearched | candidate | none found; web search for non-normal full-faithfulness, only normal-base results surfaced |
| `100-proper-epimorphism-hom-descent` | partial | unsearched | candidate | partial: Rydh, Bull. SMF 138 (2010), Prop. 7.2 (injectivity) and Th. 7.4 (exactness, weakly normal p) |
| `12-immersion-level-bound` | partial | candidate | candidate | none found; links' Hodge numbers (Durfee 1983, Durfee–Saito 1990) searched |
| `123-grothendieck-springer-pic-twisted-torus` | partial | unsearched | candidate | none found; web search on Pic of Grothendieck–Springer space, non-split torus; Sansuc 1981 not read |
| `123-steinberg-no-resolution-picard` | partial | unsearched | candidate | none found for Picard route; statement classical (Brieskorn 1970, Slodowy LNM 815, monodromy), not read |
| `126-generic-descent` | partial | candidate | candidate | none found; nearest Weil 1956 Th. 6–7 (via Milne AG Th. 16.36), field case, effective |
| `127-closure-flatness-artinian-or-trait` | partial | unsearched | candidate | none found; EGA IV 11.8.1 (reduced base, DVRs), 11.10.9–10 (fibrewise density) |
| `127-hironaka-reduced-base-openness` | partial | candidate | candidate | none found; nearest Kollár, Families of varieties of general type (2023) Th. 10.72 (normal excellent base) |
| `130-quasi-function-sheaf` | partial | unsearched | candidate | Substance in Vojta, CIME LNM 2009 (2011), Thm. 8.7 (after Lang 1983 ch. 10); sheaf form QF_X not found. |
| `131-locally-quasi-finite-representability` | partial | candidate | candidate | none found; Murre exp. 294 (unramified case, LQF announced), Artin 1969 not reachable |
| `133-affine-quotient-not-constructible` | partial | candidate | candidate | none found; SGA 3 VI_B §12, Brion 2009/2017 closest |
| `134-1-picard-sign-sequence` | partial | unsearched | candidate | partial: SGA 4 XVIII 1.4.15/1.4.17 (strict Picard stacks ≃ D^[−1,0], the Ext² term); full sequence not found |
| `136-automorphism-group-scheme` | partial | candidate | candidate | none found; polynomial-forms literature (A_PL) defines object, never computes Aut |
| `14-albanese-equivalence-ring` | partial | unsearched | candidate | Partial: Samuel, ICM 1958, Props. 9–11, 15–16 (square ⊂ folder's relation ⊂ abelian equivalence); the relation itself not found. |
| `142-teichmuller-galois-category-etale` | partial | unsearched | candidate | none found; Teichmüller-tower/operad literature (Basualdo Bonatto et al. 2026, Boggi, Lochak 2019) abstracts only |
| `147-m11-stratified-class-over-z` | partial | unsearched | candidate | none found for the invariant; Bergh 2016 Prop. 7.3 ({M_{1,1}} = L, different invariant); value checked by own computation |
| `149-cusp-specialisation-index` | partial | unsearched | candidate | none found; Stix 2012 (cuspidal sections), Porowski 2025 read |
| `15-brandt-picard-category` | partial | candidate | candidate | none found; closest Voight, Quaternion Algebras, Thm 18.3.4(a) (IJ = JI, group level); Fröhlich 1973 located, not read |
| `161-2-definite-characteristic-join-of-subtopoi` | partial | candidate | candidate | none found; searched classifying topos of rings/characteristic subtoposes; Elephant A4.5 not read |
| `162-5-formal-categories-flat-conormal-de-rham` | partial | unsearched | candidate | none found; Kapranov 2007 Prop. A.5.10/Thm A.6.4 integrates only finite-rank filtered case |
| `18-archimedean-lattice-cocycle` | partial | unsearched | candidate | none found; conjugate-varieties literature (Serre 1964, Charles, Shimada) abstracts only |
| `27-semicontinuity-proof` | partial | candidate | candidate | none found; closest Gille–Guralnick arXiv:2211.09876 Thm 4.1 (other rank functions) |
| `29-ramification-domain-axioms` | partial | candidate | candidate | none found; Lieblich–Olsson 2010 App. A closest; Grothendieck–Murre LNM 208 located, not read |
| `32-pullback-kernel-index` | partial | candidate | candidate | none found; restriction–corestriction over a field and Brauer-group analogues searched |
| `34-lci-local-1-asphericity` | partial | candidate | candidate | Partial: SGA 7 I Exp. I Th. 4.5/Var. 4.8 (char 0 trait, abelian local acyclicity only) |
| `34-multiparameter-tame-monodromy` | partial | candidate | candidate | closest: Hoshi–Mochizuki 2011 Def. 2.10 (log point, rel. dim 1); Kisin 2000 Cor. 1.16 (trait) |
| `36-h1-invariant-cycle-defect` | partial | candidate | candidate | partial: Raynaud 1970 Prop. 6.3.5/Cor. 6.3.6 (kernel part); Esnault–Wittenberg Rem. 2.3 (defect named) |
| `36-orthogonality-regular-adic-base` | partial | unsearched | candidate | Close: SGA 7 IX 7.4.8 (complete adic base, semi-abelian special fibre, biextension) and Rem. 2.6 a) (weight argument sketched) |
| `4-vanishing-unit-root-bound` | partial | unsearched | candidate | none found; Illusie 1990 located not read |
| `45-bands-tsen-field` | partial | unsearched | candidate | partial: Springer 1966 Thm 3.5 / Flicker–Scheiderer–Sujatha 1998 Thm 3.1 (perfect k, cd ≤ 1, smooth groups); non-smooth/imperfect case not found |
| `45-h1-surjectivity-dim-one` | partial | unsearched | candidate | Smooth case: Lourdeaux–Zidani, arXiv:2604.05148, Cor. 7.2 (scd(K) ≤ 1, any smooth G → G′); non-smooth case not found. |
| `47-dual-polarisation-divisibility` | partial | candidate | candidate | none found; Küronya–Mustopa Lemma 2.6 + Mukai 1981 Prop. 3.11 give it as a two-line corollary, not stated |
| `57-generic-hyperplane-h1-injective` | partial | unsearched | candidate | none found; SGA 6 XIII not accessible; Lauritzen–Rao 1997 (very ample, but only H^{penultimate}) checked |
| `57-rigid-subgroups-one-fibre` | partial | unsearched | candidate | none found; rigidity under prime-to-p torsion density |
| `59-determinant-canonical-section` | partial | candidate | candidate | none found; Mukai/Birkenhake–Lange, Moret-Bailly cover only X = A |
| `59-surface-even-chi-torsor` | partial | candidate | candidate | Field case (char ≠ 2): Poonen–Rains arXiv:1104.2105 Prop. 3.6(f) plus a rank-≤4 step; relative case not found. |
| `6-formal-group-not-in-abelian-variety` | partial | unsearched | candidate | none found; Oort AV over finite fields 9.5, Chai–Oort 3.18 use same mechanism |
| `6-ordinary-moduli-complete-intersection` | partial | unsearched | candidate | none found; Norman–Oort 1980 located not read; Chai–Oort 2007 (1.13) only reduced étale statement |
| `6-same-formal-group-not-isogenous` | partial | unsearched | candidate | none found explicitly; follows from Oort JAMS 2004 central leaves + countable isogeny classes |
| `60-inertia-average-duality` | partial | unsearched | candidate | none found; Tate 1979 §4 and Deligne LNM 349 located, not read |
| `77-arf-cover-stein-factorisation` | partial | candidate | candidate | Partial: Auel–Bernardara–Bolognesi, arXiv:1109.6938, Prop. B.2 (Stein factor = discriminant cover, regular base, via Clifford algebras). |
| `8-dim-one-A-module-homs` | partial | unsearched | candidate | none found; web search on formal A-modules (Hazewinkel CWI reports, snippets) |
| `8-lubin-tate-via-hodge-filtration` | partial | candidate | candidate | none found; Faltings 2002 §7 (O-DP lifting theory) closest; Messing, Fontaine searched |
| `9-det-etale-tate-iso` | partial | unsearched | candidate | none found; Chai 2003 Prop. 2.7–2.8 (duality of étale/multiplicative parts) closest |
| `9-symmetric-positive-det-sqrt-degree` | partial | candidate | candidate | none found; Deligne 1969 §3 + Debarre 1992 Thm 2.1 combine to it, not printed |
| `91-centraliser-condition-R` | partial | candidate | candidate | partial: SGA 3 VI_B 6.9 d)+6.2.4 e) (connected fibres), Romagny arXiv:2205.11114 Cor. A.8; (R) itself not found |
| `91-weil-restriction-finite-etale-criterion` | partial | candidate | candidate | none found; Romagny π₀ (reduced fibres), Bertapelle–González-Avilés Th. 1.2 (field case), Overkamp Prop. 2.3 (ν ≡ 1) |
| `94-representability-criterion` | partial | candidate | candidate | none found; Hall arXiv:1206.4179 Ex. 3.7–3.13 (needs products), Jaffe 1994 (algebras), Hartshorne 1998 not read |
| `102-open-immersion-criterion` | stated | candidate | candidate | none found as stated; nearest Hall–Rydh arXiv:1306.4599 Th. 10.3 (Artin 1973 VII.7.2), excellent base |
| `103-gr-stacks-relative-cohomology-BG` | stated | unsearched | candidate | partial: Breen, Astérisque 225 (1994) §7.6 (gr-stack ↦ 2-gerbe on Bπ₀, class in H³(Bπ₀,π₁)); relative τ≤2 statement not found |
| `119-foliation-quotient-topos-equivalence` | stated | candidate | candidate | none found; closest Kock–Moerdijk JPAA 82 (1992) §6 with Lemma 5.1; Moerdijk 1993 not read |
| `127-non-flat-descent-artinian-epimorphism` | stated | unsearched | candidate | none found; Stacks 08XA/08XD (universally injective maps only) |
| `129-ext2-vanishing-p-odd` | stated | candidate | candidate | Partial: Breen, Ann. ÉNS 8 (1975), main theorem (smooth H, p-groups); full NB not found. |
| `134-1-sign-realisation-universal-argument` | stated | candidate | candidate | none found; Grothendieck withdrew it (1ILL21, 1975); Baues 1996 Rem. 1.5.5 supports doubt only indirectly |
| `162-5-de-rham-hochschild-flat-formal-category` | stated | unsearched | candidate | none found; one web search, Kapranov 2007 not relevant |
| `29-domram-morphisms-fully-faithful` | stated | unsearched | candidate | none found; searched Grothendieck–Murre/Galois-category 2-categories; Tonini not read |
| `29-h1-five-classes-infinite-group` | stated | unsearched | candidate | Partial: Bhatt–Scholze, arXiv:1309.1198, Lemmas 7.3.8, 7.4.6, 7.4.10 (étale analogues); fppf-class comparisons not found. |
| `2ILL5-p8-full-faithfulness-conjecture` | stated | candidate | candidate | partial: Ogus LNM 900 Hope 4.11.3 (number field, cycles; via Tang arXiv 1510.01357 Conj. 2.1.4); relative form not found |
| `31-local-ring-cd-lower-bound` | stated | candidate | candidate | Partial only: SGA 4 X 2.4 (ℓ invertible, cruder ℓ=2 exception); Gabber volume Intro Cor. 8 (henselian quasi-excellent equality); ℓ=2 refinements not found |
| `41-irreducible-components-etale-criterion` | stated | unsearched | unsearched | none found; Romagny 2011 read previously (flat, reduced-fibres case only) |
| `64-legendre-pinning-moduli` | stated | candidate | candidate | none found; Antieau–Meier arXiv 1608.00851 §4 (no strict 𝔖₃ lift); Katz–Mazur not read |
| `91-res-representable-by-scheme` | stated | candidate | candidate | none found; read Nitsure Th. 6.6 (projective case), Martin Th. 2.1 (Matsumura–Oort over a field), Stacks 0D1C (space) |
| `FG_IL_5_SGA7_4-depth-local-acyclicity` | stated | candidate | candidate | Partial: SGA 7 I Exp. I Th. 4.5, Var. 4.8, Prop. 4.10 (trait of char 0, acyclicity half) |

## Caveats

- **`130-neron-symbol-component-correction`** is matched through Bosch–Lorenzini's statement of Néron's decomposition (Invent. 148, §4 and Th. 4.4). I did not read Néron 1965, ch. III, or Lang, ch. 11 myself. I did not check either that *j* is characterised by exactly the folder's four axioms, boundedness included. Medium confidence.
- **`47-chow-fourier-todd-over-base`**: Deninger–Murre, Cor. 2.22(1), implies that the correction factor pulled back from *S* is 1 in CH(*S*)_ℚ. So the page's single factor Todd(*t_A*) is not the right correction, and `settle` says so. The claim, which says only « a factor pulled back from *S* », remains true. Medium confidence.
- **`51-albanese-good-reduction-codim-two`**: Chung, arXiv:2608.14417, is a 2026 preprint, not yet refereed. Its hypotheses are weaker than the folder's. Geometric normality of *X_K*, deduced from the hypotheses by Serre's criterion, is a step of this pass.
- **`100-neron-extension-p-divisible`**: the general statement is in SGA 7 IX, Rem. 5.9.1, credited to Raynaud, without proof: the remark refers to an unpublished property of the construction of Néron models. What the folder may add is a proof, and `settle` says so.
- **`59-surface-even-chi-torsor`** stays `candidate`. Over a field of characteristic ≠ 2, the claim follows from Poonen–Rains, Prop. 3.6(f), plus a step of this pass on the rank of δ(A[2]). The relative case and characteristic 2 remain open.
