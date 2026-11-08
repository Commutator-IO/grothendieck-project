# Do mathlib4's closed pull requests cover the formalisation roadmaps? (8 November 2026)

A quantified study of every closed pull request of `leanprover-community/mathlib4`, all authors,
read through its title, labels and the first 600 characters of its description, against the
lists the community keeps of what is still missing. The question: do merged PRs cover the
roadmaps, do abandoned PRs account for part of them, or do the roadmaps stay untouched?

Short answer: they stay mostly untouched. Between 7 % and 14 % of the roadmap items have at
least one merged PR that addresses them (after hand-checking). About 1.5 % have only abandoned
attempts and about 1 % only open PRs. The other 84–90 % have no PR whose title or description
names them. Most merged work goes to algebra, category theory, topology, order theory and
infrastructure. Those areas are big in mathlib and small or absent in the roadmaps. The roadmaps
weigh heavily on number theory, algebraic geometry and differential geometry.

## 1. Method

**PR corpus.** I fetched every closed PR through the REST list endpoint
(`pulls?state=closed`, 424 pages of 100, 8 November 2026). It has no 1,000-result cap, so I did
not need to cut the search API into month-long slices. I also fetched the 2,763 open PRs, so that
"open only" can be told apart from "untouched". mathlib merges through bors: a merged PR is
*closed* on GitHub with the title prefix `[Merged by Bors] -`, and `merged_at` is set on only 369
of them. So merged here means `merged_at` set, or that title prefix.

**Roadmaps.**
- `docs/undergrad.yaml`: an item counts as missing when its value is a URL instead of a Lean
  declaration (the file no longer uses `~`). That gives 37 missing out of 436 leaves. The 399
  present leaves serve as a control.
- `docs/overview.yaml`: 510 leaves, none missing, so it is not used.
- `docs/100.yaml`: 22 of 100 entries have no `decl`/`decls`.
- `docs/1000.yaml`: 982 of 1,199 entries have no `decl`/`decls`. Of those, 32 carry a URL or
  authors for a formalisation elsewhere.
- TauCeti roadmaps (`TauCetiProject/TauCetiRoadmap`): 172 roadmap directories, 142 active and
  30 under `Completed/`, 171 distinct names (IntegralLattices is in both). I read every
  `README.md` and `metadata.toml` (arXiv area). I cut each README into its leaf "Layer / Stage /
  numbered" headings, which gives 2,962 sections. 44 READMEs have no such headings; each of them
  counts as one item, its title.
- Tracking issues in mathlib4: searches for roadmap, tracking, project, todo and missing in issue
  titles gave 45 issues. Most are about tactics, linters or performance. Seven are mathematical:
  #21749, #26771, #20747, #18696, #12035, #18161 and #42600.
- The project's own gaps (§ 5) were searched with hand-written regular expressions and checked
  one PR at a time.

**Matching.** Text is normalised: accents dropped, CamelCase split, light stemming. Then:
- Undergrad items: every content word of the item, plus its parent heading when the item's
  words are generic, must appear in a PR title. Or the whole phrase must appear in the
  description.
- Named theorems (100, 1000): the full name ("Kneser theorem") in the title or description, or
  all its name words together in the title.
- TauCeti sections: the heading is cut at commas, "and", "with", "via" and so on. A piece matches
  if all its content words are in a title, or the phrase is in the description.
- Single generic words are dropped, and so is any piece matching more than 60 PRs (120 for the
  YAML lists). PRs that only edit the 100/1000 lists are excluded.

An item is then:
- **merged** if at least one merged PR matches it;
- **abandoned-only** if only closed-unmerged PRs match;
- **open-only** if only open PRs match;
- **untouched** if nothing matches.

**Checks by hand.**
- Precision: I judged 96 matched items against their PR titles.
- Recall: I used the 399 undergrad items already in mathlib, and re-searched 20 untouched items
  with GitHub's own search.
- Every undergrad and 100 missing item (59 in all) was checked by hand.

**Closure reasons.** I drew a random sample of 111 closed-unmerged PRs, stratified by closing
year. For each I read the last five comments, the closing event (who closed it) and the cross
references, all through GraphQL. I classified them automatically, then corrected the result by
hand.

Rate limits: about 470 REST calls, 8 GraphQL calls, 25 search calls. Nothing was posted on
GitHub. mathlib4 was not cloned.

## 2. Data scope

| | count |
|---|---|
| Closed PRs (#1 to #45790) | 42,360 |
| merged | 36,359 (85.8 %) |
| closed unmerged | 6,001 (14.2 %) |
| Open PRs (snapshot) | 2,763 |
| Merged PRs with a `t-*` area label | 23,387 (64 %) |

Merged / closed-unmerged PRs per quarter of closing (monthly counts are in the scratch file
`monthly_counts.csv`):

| quarter | merged / unmerged | quarter | merged / unmerged |
|---|---|---|---|
| 2021 (all) | 137 / 8 | 2024-Q3 | 2,448 / 370 |
| 2022 Q1–Q3 | 241 / 13 | 2024-Q4 | 2,705 / 260 |
| 2022-Q4 | 683 / 55 | 2025-Q1 | 2,616 / 309 |
| 2023-Q1 | 1,734 / 58 | 2025-Q2 | 2,153 / 603 |
| 2023-Q2 | 2,242 / 107 | 2025-Q3 | 2,701 / 489 |
| 2023-Q3 | 1,490 / 117 | 2025-Q4 | 2,902 / 447 |
| 2023-Q4 | 1,536 / 177 | 2026-Q1 | 3,097 / 509 |
| 2024-Q1 | 1,916 / 200 | 2026-Q2 | 2,731 / 561 |
| 2024-Q2 | 1,952 / 291 | 2026-Q3 | 2,138 / 588 |
| | | 2026-Q4 (to 8 Nov.) | 937 / 839 |

The jump in 2026-Q4 comes from one day: on 24 October 2026, 543 unmerged PRs were closed when
mathlib stopped taking PRs from branches of the main repository and required PRs from forks
(§ 4).

Merged PRs per area label (one PR can carry several labels; 12,972 merged PRs have none, mostly
from 2023, when labels were not yet added automatically):

| label | merged | unmerged | | label | merged | unmerged |
|---|---|---|---|---|---|---|
| t-algebra | 6,534 | 1,037 | | t-combinatorics | 703 | 177 |
| t-category-theory | 2,765 | 338 | | t-algebraic-geometry | 542 | 73 |
| t-analysis | 2,403 | 382 | | t-set-theory | 405 | 92 |
| t-topology | 2,072 | 278 | | t-logic | 376 | 91 |
| t-order | 1,573 | 161 | | t-differential-geometry | 371 | 71 |
| t-measure-probability | 1,570 | 214 | | t-group-theory | 293 | 57 |
| t-data | 1,510 | 272 | | t-linter | 277 | 128 |
| t-meta | 1,484 | 320 | | t-algebraic-topology | 184 | 20 |
| t-ring-theory | 1,071 | 165 | | t-euclidean-geometry | 180 | 16 |
| t-number-theory | 900 | 167 | | t-computability | 89 | 54 |

Some labels named in the brief do not exist in mathlib4: t-linear-algebra, t-differential-topology
and t-probability. Linear algebra is under t-algebra, probability under t-measure-probability.

## 3. Matching results

### 3.1 Raw automatic classification

| roadmap list | items | merged | abandoned-only | open-only | untouched |
|---|---|---|---|---|---|
| undergrad.yaml, missing | 37 | 11 (30 %) | 3 (8 %) | 2 (5 %) | 21 (57 %) |
| undergrad.yaml, present (control) | 399 | 226 (57 %) | 6 (2 %) | 8 (2 %) | 159 (40 %) |
| 100.yaml, missing | 22 | 5 (23 %) | 3 (14 %) | 3 (14 %) | 11 (50 %) |
| 1000.yaml, missing | 982 | 126 (13 %) | 37 (4 %) | 34 (3 %) | 785 (80 %) |
| TauCeti, active sections | 2,676 | 724 (27 %) | 63 (2 %) | 47 (2 %) | 1,842 (69 %) |
| TauCeti, completed sections | 286 | 82 (29 %) | 8 (3 %) | 7 (2 %) | 189 (66 %) |
| **all missing items + TauCeti sections** | **4,003** | **948 (24 %)** | **114 (3 %)** | **93 (2 %)** | **2,848 (71 %)** |

### 3.2 Precision and recall

- **Precision of a "merged" match** (does a matched merged PR really address the item?):
  - TauCeti sections: 8 of 30 (27 %). Section headings are descriptive ("The ring structure",
    "Reflection"), so pieces of them hit unrelated PRs.
  - Named theorems in 1000.yaml: 15 of 30 (50 %). Name clashes are frequent: "Green's theorem"
    hits the CI branch `nightly-testing-green`, "Pick's theorem" hits `pick_goal`, "Bell's
    theorem" hits Bell numbers.
  - Undergrad and 100 missing items: 9 of 16 (56 %).
- **Precision of "abandoned-only"**: 10 of 20 (50 %).
- **Recall**:
  - The matcher finds a merged PR for 57 % of the undergrad items that are already in mathlib.
    This is a lower bound, since many came in through 2023 port PRs titled only by file name.
  - Among 20 untouched items re-searched with GitHub search, 2 had probably been missed:
    Doob's martingale convergence theorem, which mathlib has, and the weak topology on p-adic
    measures, close to #37984 and #42832. That is about 10 %.

### 3.3 Corrected estimate

The 59 undergrad and 100 items were classified by hand. For 1000.yaml and TauCeti the
correction is: merged ≈ raw merged × precision + about 10 % of the raw untouched.

| list | merged (addresses the item) | abandoned-only | open-only | untouched |
|---|---|---|---|---|
| undergrad missing (37, by hand) | 4 (11 %) | 2 (5 %) | 2 (5 %) | 29 (78 %) |
| 100 missing (22, by hand) | 3 (14 %) | 3 (14 %) | 3 (14 %) | 13 (59 %) |
| 1000 missing (982, corrected) | 7–13 % | ≈ 2 % | ≈ 2 % | ≈ 83–89 % |
| TauCeti sections (2,962, corrected) | 7–14 % | ≈ 1 % | ≈ 1 % | ≈ 84–91 % |
| **all 4,003 items** | **≈ 7–14 %** | **≈ 1.5 %** | **≈ 1 %** | **≈ 84–90 %** |

"Merged" almost never means that the item is finished. The matched PR is usually groundwork: the
Gödel β-function (#8887) for incompleteness, asymptotics lemmas from the PrimeNumberTheoremAnd
project for PNT, FLT for n = 3 (#10698), uniqueness of partial fractions (#35702).

Details from the hand check:
- **Undergrad, merged**: elementary row operations (#38596), improper integrals (2023 ports
  #4864 and #4928), partial fraction decomposition over ℝ(X) and ℂ(X) (#35702, uniqueness only).
- **Undergrad, abandoned-only**: polar decompositions in GL(n, ℝ) and GL(n, ℂ) (#33642, #42449).
- **Undergrad, open-only**: triangularisation (Schur triangulation, #39139); simultaneous
  diagonalisation of two quadratic forms (#42931).
- **100, abandoned-only**: Euler's polyhedron formula (#29639); Ramsey's theorem, hypergraph
  version (#12167, #12773, #27217); Desargues (#37456).
- **100, open-only**: Pascal (#44986), Feuerbach (#44236), Brouwer (#36770).
- **The "missing" lists lag behind mathlib.** Several 1000.yaml items marked missing have merged
  PRs that prove them: Hilbert 90 (#33124 and earlier), Krylov–Bogolyubov (#42947),
  Kraft–McMillan (#34108), Erdős–Stone in its minimum-degree form (#28685), the von Neumann–Sion
  minimax theorem (#31560), and Doob's convergence theorem. In undergrad.yaml, elementary row
  operations and improper integrals are present but still listed with URLs.

### 3.4 Per area

The table compares each area's share of labelled merged PRs (23,387) with its share of TauCeti
sections (2,962). TauCeti areas come from the arXiv tags, grouped.

| area | merged PRs | share of labelled merged | TauCeti roadmaps | share of TauCeti sections | undergrad missing |
|---|---|---|---|---|---|
| Algebra (t-algebra, group, ring) | 7,622 | 32.6 % | 29 | 12.9 % | 21 |
| Infrastructure (t-data, t-meta, t-linter) | 3,247 | 13.9 % | 0 | 0 | 0 |
| Category theory | 2,765 | 11.8 % | 2 | 0.9 % | 0 |
| Analysis (incl. functional) | 2,403 | 10.3 % | 26 | 10.0 % | 13 |
| General topology | 2,072 | 8.9 % | 0 | 0 | 0 |
| Order theory | 1,573 | 6.7 % | 0 | 0 | 0 |
| Measure theory & probability | 1,570 | 6.7 % | 5 | 5.7 % | 0 |
| Number theory | 900 | 3.8 % | 34 | 37.7 % | 0 |
| Logic, set theory, computability | 865 | 3.7 % | 5 | 1.9 % | 0 |
| Combinatorics | 703 | 3.0 % | 5 | 3.7 % | 0 |
| Algebraic geometry | 542 | 2.3 % | 29 | 15.9 % | 0 |
| Differential geometry | 371 | 1.6 % | 20 | 7.9 % | 0 |
| Euclidean & convex geometry | 245 | 1.0 % | 2 | 0.1 % | 3 |
| Algebraic topology (incl. condensed) | 243 | 1.0 % | 14 | 3.3 % | 0 |
| Dynamics | 74 | 0.3 % | 0 | 0 | 0 |

Raw per-area TauCeti coverage, by sections with a merged match:
- math.FA 61 %, math.AP 54 %, math.DG 52 %, math.CT 50 %, math.GR 48 %, math.SG 47 %, math.AG 46 %;
- math.PR 36 %, math.NT 36 %, math.CO 35 %, math.AC 25 %.

The order is not informative once the 27 % precision is applied. By roadmap, the median raw
share of sections with a merged match is 25 %. 36 of the 172 roadmaps have no section matched by
any merged PR (list in § 3.6).

### 3.5 High PR activity that no roadmap lists

- **General topology** (2,072 merged), **order theory** (1,573) and **dynamics** (74): no
  TauCeti roadmap, nothing missing in undergrad.yaml.
- **Category theory** (2,765 merged, the second-largest mathematical label): 2 TauCeti
  roadmaps out of 172 (DiagrammaticCoherence and PivotalSpherical, 0.9 % of sections). Much of
  this activity is homological algebra, sites and sheaves, presentable categories and
  localisation, all driven from inside mathlib (a few long series on presentable categories,
  derived categories and descent data account for a large share).
- **Infrastructure** (data, meta, linters: 3,247 merged) is by nature on no roadmap. So are the
  2023 port (about 7,000 merged PRs), golfing, deprecations and renames. Only 3,027 of the 6,001
  unmerged PRs have a `feat` title.
- **Labelled downstream projects** feed mathlib without a roadmap file in mathlib: FLT, carleson,
  sphere-packing, infinity-cosmos, brownian and toric.

The reverse also holds. Number theory has 38 % of the TauCeti sections and 3.8 % of the merged
PRs; algebraic geometry 16 % against 2.3 %; differential geometry 8 % against 1.6 %. TauCeti is
a library downstream of mathlib, so its roadmaps are written to be built there, not in mathlib.
Low mathlib coverage of them is partly by design.

### 3.6 Roadmap topics with no PR at all

- **Undergrad** (no PR names them):
  - linear algebra: rank of a system of linear equations, elementary column operations,
    row-reduced matrices, kernels lemma, Jordan normal form, diagonalisation of normal
    endomorphisms;
  - representations of finite groups: dual groups, Fourier transform on finite abelian groups,
    class functions, orthonormal basis of irreducible characters, representations of abelian
    groups (one open PR only, off topic);
  - affine geometry: affine property, group generated by homotheties and translations,
    transformations fixing a basis of directions;
  - analysis: summation of comparison relations, products of series, Taylor with little-o
    remainder, Taylor series expansions, absolute vs conditional convergence of improper
    integrals, comparison test for improper integrals, normal convergence.
- **100 theorems**: trisecting the angle and doubling the cube, the parallel postulate,
  independence of CH, the four colour theorem, Puiseux, the isoperimetric theorem, Platonic
  solids, π and e transcendental, Hermite–Lindemann, Morley. Several of these are formalised in
  other libraries.
- **1000 theorems**: about 85 % untouched. A random sample of the untouched ones:
  Hirzebruch–Riemann–Roch, Frucht, Nielsen realisation, Kaplansky density, Karhunen–Loève,
  Hille–Yosida, Bochner's tube theorem, Immerman–Szelepcsényi, Hopf–Rinow, fixed-point theorems
  in infinite-dimensional spaces.
- **TauCeti roadmaps with no merged match in any section**: FormalLaurentPuiseux,
  AdicSpacesPartIV, AlgebraicVectorBundles, ComplexCurveModuli, ComplexTori,
  RealAnalyticGeometry, SchubertGeometry, HodgeStructures, CharacteristicClasses,
  EllipticIntegrals, TauberianBoundaryConvergence, Hyperfunctions, ConformalMapping,
  GeometricCurrents, Orbifolds, SeibergWittenTheory, SpinGeometry, Yamabe, ChevalleyGroups,
  CombinatorialHeegaardFloer, KhovanovHomology, TopologicalKTheory, CountableModelCounting,
  GeometricMeasureTheory, Isoperimetry, Rank24LatticeConstructions, OperatorAlgebraDynamics,
  QuantumGroups, FinancialMathematics, TypeAHeckeAlgebras, GeometricRepresentationCategories,
  NilpotentOrbits, RepresentationTheory, HamiltonianFloerOperations, SymplecticGeometry,
  TaubesGromov. Many of these have no layer headings, so they count as one item, their title.
- **mathlib tracking issues**:
  - simplicial objects by generators and relations (#21749): 4 merged PRs (#21741–#21743,
    #30586); the comparison functor #25740 is open.
  - tilting equivalence of perfectoid fields (#18696): groundwork merged (#21563, #26384, #26388,
    #32248); perfectoid fields themselves are open (#26389) after an abandoned #19972. The
    equivalence is not there.
  - digraphs (#26771): 4 merged, 10 open.
  - dimension theory (#20747), L-series (#12035) and combinatorial games (#18161, closed): many
    merged PRs.
  - Sheppard's formula (#42600): nothing.

## 4. Why closed-unmerged PRs are closed

Sample of 111, stratified by closing year (random seed 20261108), from comments, closing actor
and cross references:

| reason | n | share |
|---|---|---|
| stale, or withdrawn by its author with no stated reason (often after merge conflicts) | 33 | 30 % |
| infrastructure: benchmarks, CI tests, toolchain adaptations, experiments, file splits | 28 | 25 % |
| superseded, duplicate or redesigned (another PR merged, or a new design) | 23 | 21 % |
| closed administratively in the move to fork-based PRs (2025-06, 2026-10-24) | 15 | 14 % |
| rejected by reviewers (wrong direction, AI policy, LLM-generated label) | 8 | 7 % |
| moved to another project or venue (separate repo, Mathlib Phrasebook) | 4 | 4 % |

"Split into smaller PRs" almost never appears as such. Dependent series show up as superseded,
or as `blocked-by-other-PR`. Corpus-wide signals:

- Label counts among the 6,001 unmerged PRs: `merge-conflict` 2,274; `WIP` 1,035; `awaiting-author`
  1,001; `will-close-soon` 550; `LLM-generated` 380; `migrated-to-fork` 243; `please-adopt` 63.
- Mass closures: 543 PRs on 2026-10-24 and 89 on 2025-06-12, both in the fork migration.

Some of these closures hit roadmap topics: topos-theory basics (#21269), power objects
(#22302), pure submodules (#22909) and descent of sheaves (#8661) were all closed on 24 October
2026. They were closed for administrative reasons, not on their mathematics, and can be reopened
from a fork.

## 5. The gaps this project ran into

I searched these by regular expression over all titles and descriptions, then checked each hit by
hand.

| gap | merged | closed unmerged | open | verdict |
|---|---|---|---|---|
| Subtopoi, essential geometric morphisms | 0 on the topic. Related: subobject classifier (#21281, #22881, #26556, #35867, #35895), adjoint quadruples (#27720) | topos basics #21269 and power objects #22302 (fork closure, 2026-10-24); Heyting algebra of subobjects in an elementary topos #39618 | elementary topos #26757 | **untouched.** Nothing on subtopoi, Lawvere–Tierney topologies, local operators or essential geometric morphisms; even the elementary topos is open only. |
| Pure morphisms, descent of modules | pure morphisms in presentable categories (#41200, #41420, #44044); universally injective morphisms of schemes (#18845, #39910); descent along faithfully flat ring maps (#22565, #37982); extension of scalars comonadic for a faithfully flat algebra (#32326); descent data and stacks on sites (#30189, #30190, #33195, #35396, #35452); fpqc descent for open immersions (#32957) | pure submodules #22909 (fork closure); descent data for ModuleCat #14203 | descent data by presieves #29638 | **partly covered.** Categorical purity and faithfully flat descent are merged. Purity of ring maps and modules, and descent along pure (non-flat) morphisms, are not. |
| Schur–Weyl duality | 0 (only "triple centraliser = centraliser" #13492, marginal) | double commutant theorem for von Neumann algebras #35538 | – | **untouched.** |
| Schatten ideals | 0 | – | Schatten operators #44525, Hilbert–Schmidt #41477, nuclear operators #42197, trace / abs / polar of operators on Hilbert spaces #44994, #44997, #45001, #45002 | **open only.** A series under review since October 2026. |
| Quasi-coherent sheaves on schemes | 16, from #13464 (July 2024) to #40988 (June 2026): tilde, pushforward between affines, restriction, presentations on affine covers, quasi-coherent algebras | affine cohomology vanishing #36344 (successor #36345 open) | pullback is quasi-coherent #39989 | **covered for the basic theory.** Pullback, cohomology and descent of quasi-coherent sheaves not merged. |
| Algebraic theories relative to a class of limits | 0 (the keyword hits are "limit theorem", "monadic" in other senses) | 0 | 0 | **untouched.** No Lawvere theories, sketches or essentially algebraic theories. |
| Locally presentable categories | 34 since January 2025 (#19937 … #45545): accessible functors, κ-presentable objects, locally presentable categories (#28178), presheaves and Type locally presentable, the uniformisation theorem (#31018), the orthogonal-reflection construction | 3 (#20263, superseded by #28178; #36758; #41193) | representation theorem #30847, κ-continuous presheaves #30817 | **covered and active.** The best-served of the seven. |

## 6. Conclusions

1. **Coverage is low.** Roughly 7–14 % of the roadmap items (missing undergrad entries, missing
   100 and 1000 theorems, TauCeti sections) have a merged PR that addresses them, usually in
   part. About 1.5 % have only abandoned attempts and about 1 % only open PRs. About 84–90 % have
   no PR at all, judged by titles and descriptions.
2. **Merged work goes elsewhere.** Mathlib's activity is driven by the library itself:
   generality, refactors, ports, infrastructure, and big foundational series in category
   theory, topology, order and algebra. These areas are big in mathlib and almost absent from
   the roadmaps.
3. **The main uncovered areas** are those the TauCeti roadmaps put first:
   - arithmetic: class field theory, modular forms and curves, L-functions beyond Dirichlet,
     local fields, Iwasawa theory;
   - algebraic geometry beyond the foundations: curves, vector bundles, Hodge structures,
     Schubert and flag varieties, adic and rigid spaces;
   - differential, symplectic and low-dimensional topology: spin geometry, Floer theories,
     Khovanov homology, Seiberg–Witten;
   - representation theory: character theory of finite groups, Schur–Weyl, quantum groups,
     Hecke algebras;
   - operator theory: Schatten ideals, von Neumann algebras.

   The undergrad list still misses Jordan normal form, character theory and Taylor series.
4. **Abandonment is mostly not about the mathematics.**
   - About 30 % of closed-unmerged PRs go stale or are withdrawn without a stated reason.
   - About 25 % are infrastructure.
   - About 21 % are superseded by another PR.
   - About 14 % were closed administratively in the move to fork-based PRs.
   - Only about 7 % are rejected, now often under the AI policy.

   The fork-migration closure of 24 October 2026 swept up roadmap-relevant PRs (topos theory,
   pure submodules, descent of sheaves).
5. **Of this project's seven gaps:**
   - covered: locally presentable categories and the basics of quasi-coherent sheaves on schemes;
   - partly covered: pure morphisms and descent (categorical purity and faithfully flat descent
     are merged; purity of modules and pure descent are not);
   - open only: Schatten ideals (a PR series under review);
   - untouched: subtopoi and essential geometric morphisms, Schur–Weyl duality, and algebraic
     theories relative to a class of limits.

## 7. Limits

- **Text only.** PRs are judged by title, labels and the first 600 characters of the
  description, never by their diff. A PR can prove a theorem without naming it, or name it
  without proving it. The 2023 port PRs name files, not theorems.
- **Precision is low.**
  - TauCeti section headings are descriptive and match loosely (27 % precision on a sample of
    30).
  - Named theorems clash with ordinary words (50 %).
  - The corrected figures in § 3.3 come from samples of 16 to 30 items per class, so their
    error bars are wide, about ±10 points on the precision.
- **Recall is uncertain.** On items known to be in mathlib, recall is at least 57 %. On
  untouched items, about 10 % were misses (2 of 20).
- **Items are not comparable.**
  - "Covered" means at least one PR addresses the item, not that it is formalised.
  - The units differ: a TauCeti section such as "0.17 Depth, Cohen–Macaulay modules and Serre's
    conditions" weighs the same as "Kneser's theorem".
  - One roadmap, ClassicalArithmeticCompletion, has 569 of the 2,962 sections.
  - 44 TauCeti READMEs could not be cut into layers and count as one item.
- **The lists lag behind mathlib.** undergrad.yaml and 1000.yaml are not always updated when a
  result lands, so some "missing" items are in fact done.
- **Downstream libraries are invisible.** TauCeti is built to live downstream of mathlib, and so
  are FLT, PrimeNumberTheoremAnd and Carleson. Work done there is not counted.
- **Labels came late.** Area labels are systematic only from 2024: 36 % of merged PRs, mostly
  from 2023, have none. That makes the per-area counts underestimates for 2023.
- **Closure reasons** come from a sample of 111, classified from the last five comments. A
  silent closure counts as stale even when the work was continued elsewhere without a cross
  reference.

Raw data, scripts and intermediate files are kept outside the repository and are not versioned:
the PR JSON lines, the roadmap copies, `matches.json`, the hand-check sheets and the closure
sample.
