# mathlib4: the rejected pull requests (second pass, 8 November 2026)

Second pass on the study in `mathlib-pr-roadmap-study-2026-11-08.md`, restricted to the
**rejected** PRs: closed unmerged because a maintainer or reviewer turned them down (not suitable
for mathlib, wrong design, the AI policy, out of scope, "won't merge"). PRs that went stale, were
superseded or duplicated, were infrastructure, were closed in the fork migrations, or moved to
another project are left out.

Short answer: **421 rejected PRs** found among the 6,001 closed-unmerged ones (7 %), 297 of them
in 2026. Almost half (191) were closed under the AI policy, nearly all since March 2026. About
316 carry mathematical content. Of the 60 most substantial ones whose code I read, about 41 build
cleanly (green CI, no `sorry`, no `axiom`) and state a result that the project's pinned Mathlib
(12 October 2026) still lacks, wholly or in its main theorem; about 25 of them could be revived at
reasonable cost. So there is interesting code in the rejected PRs, but little of it bears on this
project's gaps, and most of it was closed under the AI policy: reviving it means rewriting it by
hand, not reopening it.

## 1. Method

**Data.** For each of the 6,001 closed-unmerged PRs I fetched, through GraphQL (301 queries of 20
PRs, about 300 points of the hourly 5,000), the author, the actor of the closing event, the labels,
the size, the last four comments (first 1,200 characters each) and the last six reviews.

**Pre-filter.** I dropped:
- the mass closures of 2025-06-12 and 2026-10-24 and the `migrated-to-fork` label (875 PRs);
- infrastructure titles: CI, bench, toolchain bumps, `lean-pr-testing`, adaptations, dependency
  updates;
- the `closed-due-to-inactivity` label;
- PRs whose last two comments point to a successor: "in favour of", "superseded", "duplicate",
  "already in mathlib", "split into", "reopened as", and so on.

Among the remaining 1,937 PRs that had a comment or review by someone other than the author, I
kept 773 candidates with at least one cheap signal:
- a closer who is not the author (592);
- a rejection phrase in a non-author comment or review (197): "not suitable", "we don't want",
  "not convinced", "out of scope", "AI-generated", "LLM", "policy", "wrong approach", "won't
  merge", "too specialized", and so on;
- the `LLM-generated` label (283);
- a `CHANGES_REQUESTED` review.

**Reading.** I read the last two comments of each of the 773 candidates and classified them by
hand: 395 rejected, 378 not (stale, superseded, moved, or the author's own decision with no
objection). A second sweep over 132 PRs closed by their author just after acknowledging a
reviewer ("fair enough", "you're right", "I see your point", "makes sense") added 26.

**Recall.** The first pass had found 8 rejected PRs in its random sample of 111. This pass
recovers 7 of them. The one it misses is an author-closed golf PR with no stated objection, which
I count as withdrawn. Recall is therefore about 85–90 % on the sample; the true total is probably
between 420 and 480.

**Code.** I fetched the diff of 60 PRs with `gh pr diff` (2.7 MB, kept outside the repository).
For each I recorded:
- the files, the added lines, `sorry`, `axiom` and `native_decide` counts, the main statements;
- the CI state of the last commit;
- whether the pinned Mathlib (`715a03a`, 12 October 2026) has the result, by a text search of its
  sources for the declaration names and the concepts, then reading the hits.

I did not recompile any PR against current Mathlib.

## 2. Counts

| | PRs |
|---|---|
| closed unmerged | 6,001 |
| after the pre-filter, with a non-author comment | 1,937 |
| candidates read | 773 + 132 |
| **rejected** | **421** (7.0 %) |
| with mathematical content (feat/refactor, not a golf, rename, lint, style or doc) | 316 |
| of those, 100 added lines or more | 171 |
| of those, 300 added lines or more | 100 |
| code read | 60 |
| of those, green CI, no `sorry` or `axiom` | 46 |
| of those, result absent from Mathlib, wholly or in its main theorem | about 41 |
| salvageable at reasonable cost (objection fixable, under about 2 weeks of work) | about 25 |

By year of closure: 2022: 4, 2023: 5, 2024: 21, 2025: 94, 2026: 297.

## 3. Split by reason

| reason | all | with mathematics |
|---|---|---|
| AI policy: LLM-generated code, undisclosed AI use, AI-written replies | 191 | 183 |
| scope: not wanted in mathlib, too specialised, trivial corollary, no use case, belongs downstream | 114 | 59 |
| design or API: wrong generality, wrong approach, a better existing API, notation, instances, performance | 91 | 50 |
| other process reasons: size and authorship (one series of 20 PRs), licence (1) | 21 | 21 |
| mathematical error: the statement is not what is claimed, or the proof rests on axioms | 4 | 3 |

- **The AI policy dominates since spring 2026.** Before March 2026 there are 6 such closures. Then
  18 in March, 30 in April, 24 in May, 22 in September and 62 in October.
  - 136 of these PRs were closed by the triage account with a standard message: the code does not
    meet the community standards for the use of AI, and reviewer time goes first to people who
    can learn and contribute back.
  - Since spring 2026 the rule is that new contributors may not open AI-generated PRs. Several
    closures say so explicitly.
  - 104 distinct authors are concerned. A few opened 10 to 20 PRs in a day, which drew a warning
    against spamming.
  - **37 of the 421 rejected PRs are this project's own** (opened in October 2026), 36 of them
    closed under the AI policy (§ 5).
- **Scope** objections are usually one of three:
  - the lemma is a one-line corollary to be inlined;
  - the subject is too specialised (unitary perfect numbers #33838) or belongs downstream
    (CSLib, the Archive, the Mathlib Phrasebook);
  - mathlib's set theory is not meant to rebuild ℕ, ℤ, ℚ inside `ZFSet` (#25484–#25488, about
    6,800 lines).
- **Design** objections often ask for more generality:
  - total variation and Pinsker for all measures, not finite distributions (#35826, #36637);
  - Kolmogorov's inequality as a special case of Doob's (#36545, #36602);
  - polar decomposition in C⋆-algebras, not matrices (#33642, #42449);
  - π₁ of the circle through a general covering-space theory (#36119; mathlib now has it).
- **Mathematical errors** are rare:
  - a "Ville's inequality" with no statement about the supremum (#36641);
  - a "P ≠ NP" resting on axioms (#34509);
  - a polynomial "l'Hôpital rule" whose statement reduces to the Leibniz rule (#22348);
  - a fix to a definition that was already correct (#32402).

## 4. The code of the 60 most substantial rejected PRs with mathematics

I chose the 60 as follows:
- by size;
- the 20-PR Hadamard series counted as one item;
- PRs whose content is not mathematics as mathlib means it left out ("entropy axiomatics",
  "uncertainty chain", "grey theory", the P = NP PRs, the 12-PR "path coherence" series, 158
  unrelated lemmas from an automated learner);
- every rejected PR touching the project's gaps added, whatever its size.

The other 256 rejected PRs with mathematics were read by title only. "CI" is the state of the PR's
last commit. "Mathlib" means the pinned Mathlib of 12 October 2026.

| PR | content | + lines | CI | Mathlib has it? | objection | fixable? / cost |
|---|---|---|---|---|---|---|
| [#34333](https://github.com/leanprover-community/mathlib4/pull/34333) and 19 siblings (#34320–#34340) | Weierstrass factors, canonical products, Borel–Carathéodory, Cartan bounds, Hadamard factorisation, Binet's formula | ≈ 55,000 | fail, 1 `sorry` | no (only Borel–Carathéodory) | 20 PRs in a few hours; authorship of the code disputed; asked for a few small PRs at a time | fixable, high: weeks |
| [#39251](https://github.com/leanprover-community/mathlib4/pull/39251) | Sylvester–Schur theorem | 5,220 | green | no | AI policy; asked to split | rewrite, high |
| [#38485](https://github.com/leanprover-community/mathlib4/pull/38485) | Schröder polynomials, Hankel determinants | 3,751 | fail, 36 `sorry`, 2 `axiom` | no | AI policy | no |
| [#34481](https://github.com/leanprover-community/mathlib4/pull/34481) | Ore's theorem (Hamiltonian cycles) | 3,372 | green | no (only `IsHamiltonian`) | AI policy | rewrite, medium: the proof is far too long |
| [#43803](https://github.com/leanprover-community/mathlib4/pull/43803) | Fejér kernel, uniform convergence of Fejér means | 2,202 | green | no | AI policy | rewrite, medium |
| [#39532](https://github.com/leanprover-community/mathlib4/pull/39532) | Mertens' first and third theorems | 2,102 | green | no | AI policy | rewrite, medium |
| [#25488](https://github.com/leanprover-community/mathlib4/pull/25488) (+#25484–#25486) | ℕ, ℤ, ℚ, Boolean algebras inside ZFC | ≈ 6,800 | green | no | scope: not wanted | no, fundamental |
| [#38446](https://github.com/leanprover-community/mathlib4/pull/38446) | abstract Sperner parity theorem | 1,748 | green | no | AI policy | rewrite, medium |
| [#42558](https://github.com/leanprover-community/mathlib4/pull/42558) (+#42559) | Sturm's theorem, counting roots in an interval | 1,065 | green | no: Mathlib has `sturmSeq`, not the root count | AI policy | rewrite on `sturmSeq`, medium |
| [#39090](https://github.com/leanprover-community/mathlib4/pull/39090) (+#39384) | Stokes on boxes and on the half-space | 1,246 | green | no (divergence theorem on boxes only) | AI policy | rewrite, medium–high |
| [#35732](https://github.com/leanprover-community/mathlib4/pull/35732) | reproducing kernels | 1,191 | green | partly: Mathlib has an `RKHS` class of another design | proofs long and unidiomatic, design | no, superseded |
| [#39349](https://github.com/leanprover-community/mathlib4/pull/39349) (+#45115) | Doob's Lᵖ maximal inequality | 1,119 | green | no (weak form `maximal_ineq` only) | AI policy | rewrite, low–medium |
| [#37879](https://github.com/leanprover-community/mathlib4/pull/37879) | absolutely monotone functions, Bernstein | 1,072 | green | partly: the definition and closure lemmas, not Bernstein's theorem | AI policy | rewrite, low |
| [#43779](https://github.com/leanprover-community/mathlib4/pull/43779) | shuffles of words | 986 | green | no | licence: derived from GPL code | clean-room only |
| [#37705](https://github.com/leanprover-community/mathlib4/pull/37705) | Johnson–Lindenstrauss lemma | 965 | green | no | AI policy | rewrite, medium |
| [#42468](https://github.com/leanprover-community/mathlib4/pull/42468) | Adams operations and λ-rings (plethystic form) | 898 | green | no | AI policy | rewrite, medium–high, depends on symmetric functions |
| [#42040](https://github.com/leanprover-community/mathlib4/pull/42040) | Størmer's theorem | 861 | green | no | AI policy | rewrite, medium |
| [#31821](https://github.com/leanprover-community/mathlib4/pull/31821) | SVD of matrices | 803 | the file has no `.lean` extension, so it was never compiled | partly: singular values exist | AI policy | no |
| [#44746](https://github.com/leanprover-community/mathlib4/pull/44746) | complex Stirling formula with remainder | 754 | fail | no | AI policy | rewrite, medium |
| [#37706](https://github.com/leanprover-community/mathlib4/pull/37706) | Church–Rosser theorem | 735 | fail | no | AI policy; belongs in CSLib | elsewhere |
| [#40824](https://github.com/leanprover-community/mathlib4/pull/40824) | 1-D Poincaré inequality | 678 | green | no | proofs not idiomatic; the statements were judged satisfactory | rewrite, low–medium |
| [#40037](https://github.com/leanprover-community/mathlib4/pull/40037) | three-gap theorem | 625 | green | no | AI policy | rewrite, medium |
| [#42461](https://github.com/leanprover-community/mathlib4/pull/42461) | lower quantile function | 603 | green | no | AI policy | rewrite, low |
| [#43488](https://github.com/leanprover-community/mathlib4/pull/43488) | Ramsey for graphs with the Erdős–Szekeres bound | 586 | green | no | AI policy | rewrite, low–medium |
| [#40741](https://github.com/leanprover-community/mathlib4/pull/40741) | Dilworth's and Mirsky's theorems | 568 | green | no | AI policy | rewrite, low–medium |
| [#33838](https://github.com/leanprover-community/mathlib4/pull/33838) | unitary divisors, unitary perfect numbers | 554 | green | no | scope: too specialised | no |
| [#34442](https://github.com/leanprover-community/mathlib4/pull/34442) | basis of 𝔰𝔩(n) | 507 | green | no | AI disclosure; a shorter version was given on Zulip | low |
| [#36637](https://github.com/leanprover-community/mathlib4/pull/36637) | Pinsker's inequality, finite case | 507 | green | no | design: should be for all measures | rewrite, medium |
| [#36104](https://github.com/leanprover-community/mathlib4/pull/36104) | Adámek's initial-algebra theorem | 469 | green | no (Lambek's lemma only) | AI policy | rewrite, low |
| [#38295](https://github.com/leanprover-community/mathlib4/pull/38295) (+#38296) | L∞ ≅ (L¹)* isometrically | 465 | green | no | AI policy | rewrite, medium |
| [#35826](https://github.com/leanprover-community/mathlib4/pull/35826) | total variation distance on PMFs | 459 | green | no | design: should be for measures | rewrite, medium |
| [#43906](https://github.com/leanprover-community/mathlib4/pull/43906) | Riesz–Schauder: 1 + compact is Fredholm of index 0; compact perturbations keep the index | 430 | green | no (Mathlib has `Fredholm/Basic`, `Open`) | AI policy | rewrite, low–medium |
| [#42881](https://github.com/leanprover-community/mathlib4/pull/42881) | Mittag-Leffler expansion of Beta | 425 | green | no | AI policy | rewrite, low |
| [#45439](https://github.com/leanprover-community/mathlib4/pull/45439) | n-torsion is (ℤ/n)^r | 389 | green | no | AI policy | low |
| [#25338](https://github.com/leanprover-community/mathlib4/pull/25338) | divisible completion of a monoid | 372 | – | yes, `DivisibleHull` | design | superseded |
| [#36917](https://github.com/leanprover-community/mathlib4/pull/36917) | bivectors of a Clifford algebra form a Lie subalgebra | 338 | green | no | AI policy | rewrite, low |
| [#44728](https://github.com/leanprover-community/mathlib4/pull/44728) | Ky Fan's inequality for singular values | 329 | green | no | AI policy | rewrite, low |
| [#38496](https://github.com/leanprover-community/mathlib4/pull/38496) | Favard's theorem | 313 | fail | no | AI policy | rewrite, medium |
| [#44790](https://github.com/leanprover-community/mathlib4/pull/44790) | Pringsheim–Vivanti theorem | 279 | green | no | AI policy | rewrite, low |
| [#38845](https://github.com/leanprover-community/mathlib4/pull/38845) | Morera, triangle version | 269 | fail | no (rectangle version only) | AI policy | low |
| [#44723](https://github.com/leanprover-community/mathlib4/pull/44723) | fixed points of an adjunction, idempotent adjunctions | 257 | green | partly (idempotent monads, reflective subcategories) | AI policy | low |
| [#39618](https://github.com/leanprover-community/mathlib4/pull/39618) | Heyting algebra on `Subobject X` in an elementary topos | 247 | green | no | AI policy (new contributor) | rewrite, low |
| [#36119](https://github.com/leanprover-community/mathlib4/pull/36119) | π₁(S¹) ≅ ℤ | 236 | green | yes, now (`windingNumberIso`) | design: wanted the general theory | superseded |
| [#44539](https://github.com/leanprover-community/mathlib4/pull/44539) | Jordan's criteria (strong form) | 235 | green | partly (multiple primitivity) | AI policy | low |
| [#40572](https://github.com/leanprover-community/mathlib4/pull/40572) | first-order Euler–Maclaurin | 226 | green | no | AI policy | low |
| [#39701](https://github.com/leanprover-community/mathlib4/pull/39701) | solid condensed modules | 195 | green, but 2 `axiom` | `Condensed/Solid` exists | axioms, AI policy | no |
| [#39546](https://github.com/leanprover-community/mathlib4/pull/39546) | F fully faithful iff Lan_F fully faithful | 191 | fail | no | AI policy | low |
| [#36758](https://github.com/leanprover-community/mathlib4/pull/36758) | `ModuleCat R` is locally finitely presentable | 163 | green | no | AI policy | rewrite, low |
| [#42047](https://github.com/leanprover-community/mathlib4/pull/42047) | locally nilpotent derivations | 167 | green | no | AI policy | low |
| [#36620](https://github.com/leanprover-community/mathlib4/pull/36620) | existence of covariant derivatives | 164 | fail | no | AI policy; asked to rewrite by hand | low–medium |
| [#19977](https://github.com/leanprover-community/mathlib4/pull/19977) | chosen finite products of affine schemes | 99 | – | no | design choice | no |
| [#44731](https://github.com/leanprover-community/mathlib4/pull/44731) | direct categories ⇔ well-founded | 80 | green | no | needs much work for a good API | medium |
| [#41781](https://github.com/leanprover-community/mathlib4/pull/41781) | permutation action on `TensorPower` | 22 | green | no (only `PiTensorProduct.reindex`) | one-liners; does not build the tensor-power action | as a first step only |
| [#44727](https://github.com/leanprover-community/mathlib4/pull/44727) | Beck (co)monadicity as an iff | 73 | green | no | AI policy | low |
| [#44726](https://github.com/leanprover-community/mathlib4/pull/44726) | additive functors on the Karoubi envelope | 67 | green | no | AI policy | low |
| [#44715](https://github.com/leanprover-community/mathlib4/pull/44715) | M f.p. ⇒ M ⊗ Πᵢ Pᵢ ≅ Πᵢ (M ⊗ Pᵢ) | 78 | green | no | AI policy | low |
| [#44970](https://github.com/leanprover-community/mathlib4/pull/44970) | first fundamental sequence split for formally smooth | 25 | green | no | AI policy | low |
| [#44722](https://github.com/leanprover-community/mathlib4/pull/44722) | integer-valued polynomials, Pólya basis | 184 | green | no | AI policy | low |

These were also read and not kept for salvage:
- #38035 Sophie Germain: fails CI;
- #35128 (`anti_pascal`): judged of dubious value;
- #43950 and the other "coherence" PRs;
- #39684–#39702 graph-catalogue Archive PRs: native_decide brute force, up to 8,800 lines.

**What "correct" means here.**
- A green CI on a PR's last commit means it compiled against the Mathlib of that day with
  warnings as errors, so with no `sorry`.
- The statements I read are the standard ones (Doob, Dilworth, Fredholm index, Ky Fan,
  Johnson–Lindenstrauss, Pinsker, Ramsey, three-gap), with no vacuous hypothesis, except where the
  table says otherwise.
- Completeness beyond that, and whether the code still builds on current Mathlib, are not checked.
  Most of these PRs are 1 to 8 months old, so all of them will need adapting.

## 5. Relevance to this project

| gap | rejected PRs touching it | verdict |
|---|---|---|
| subtopoi, essential geometric morphisms | Heyting algebra of subobjects in an elementary topos #39618 (AI policy) | none on subtopoi or essential morphisms; #39618 is a useful brick, small and green |
| pure morphisms, descent of modules | M f.p. ⇒ ⊗ commutes with products #44715 (Lenzing, a step toward Mittag-Leffler and purity criteria); products of flat modules #44714; Noetherian rings via f.p. modules #44716 (all this project's, AI policy) | no descent; only these three small lemmas |
| Schur–Weyl duality | permutation action on `TensorPower` #41781 (closed: one-liners, the action not built); 𝔰𝔩(n) basis #34442; Clifford bivectors #36917 | nothing on the double centraliser |
| Schatten ideals | Ky Fan's inequality #44728 (this project's): subadditivity of the sums of the n largest singular values, the key step toward the triangle inequality for Schatten and Ky Fan norms; SVD #31821 (never compiled); Fredholm perturbation #43906 | #44728 is the one rejected PR that serves the gap directly |
| quasi-coherent sheaves | none (only #19977, products of affine schemes, design) | none |
| algebraic theories relative to a class of limits | Adámek's initial-algebra theorem #36104; idempotent adjunctions #44723; Beck monadicity as an iff #44727; Karoubi envelope #44726 | bricks only, no Lawvere theories or sketches |
| locally presentable categories | `ModuleCat R` locally finitely presentable #36758; `preorder_of_cofiltered` #44534; countable (co)limits #44538 | #36758 fills an obvious hole in an active area |
| algebraic geometry, topos, K-theory, cyclic homology | Adams operations and λ-rings #42468; Kähler differentials #44970; semilocal rings have stable range one #44734 (K-theory); integer-valued polynomials #44722; solid modules #39701 (axioms); direct (Reedy) categories #44731 | λ-rings is the largest piece; nothing on cyclic homology |

**This project's own PRs.** 37 rejected PRs come from this project's account, all opened in
October 2026; 36 were closed by the triage account under the AI policy.
- They are mostly small, green, and absent from Mathlib: the Lucas lemmas #44735 and #45006;
  Hasse derivatives #44736 and #44755; Cauchy–Binet #44757; Ky Fan #44728; monadicity #44727; the
  Karoubi envelope #44726; Kähler differentials #44970; semilocal stable range #44734; and others.
- The only one closed on design grounds is #44731 (direct categories); #44732 was taken to the
  TauCeti roadmap instead.
- Under the current policy they can only come back as code written by hand, after a Zulip
  discussion, a few at a time (see `.claude/skills/contribute-to-mathlib`).

## 6. Answer

**Is there much interesting code in the rejected PRs? Some, though not much of it is relevant
here.**
- 421 PRs were rejected.
- 316 of them carry mathematics, 100 with 300 lines or more.
- Of the 60 read, about 41 build and state a result Mathlib still lacks; about 25 could be revived
  at reasonable cost.
- Almost all of those 25 were closed under the AI policy, not on their mathematics. Reviving one
  means a human writing it again, with the PR as a blueprint and its review comments as a guide.
  Reopening it unchanged would be closed again.

**Worth reviving**, in order of value for cost:

1. [#43906](https://github.com/leanprover-community/mathlib4/pull/43906): Riesz–Schauder and the
   invariance of the Fredholm index under compact perturbation. Standard, absent, 430 lines, green.
2. [#39349](https://github.com/leanprover-community/mathlib4/pull/39349) (or #45115): Doob's Lᵖ
   maximal inequality. Mathlib has only the weak form.
3. [#40741](https://github.com/leanprover-community/mathlib4/pull/40741): Dilworth and Mirsky.
   Both are on the 1000-theorems list and absent.
4. [#44728](https://github.com/leanprover-community/mathlib4/pull/44728): Ky Fan's inequality.
   It builds on the existing `singularValues`, and it is the first step toward Schatten norms.
5. [#42558](https://github.com/leanprover-community/mathlib4/pull/42558): Sturm's theorem. It
   could be rebased on the `sturmSeq` now in Mathlib, which stops short of the root count.
6. [#36758](https://github.com/leanprover-community/mathlib4/pull/36758): `ModuleCat R` locally
   finitely presentable. Small, and an obvious instance missing from an active area.
7. [#39618](https://github.com/leanprover-community/mathlib4/pull/39618): the Heyting algebra of
   subobjects in an elementary topos. Small, and a brick for the topos gap.
8. [#36104](https://github.com/leanprover-community/mathlib4/pull/36104): Adámek's
   initial-algebra theorem. Small, absent, close to the algebraic-theories gap.
9. [#44715](https://github.com/leanprover-community/mathlib4/pull/44715): tensoring with a
   finitely presented module commutes with products (Lenzing's easy half). Useful for purity.
10. [#38295](https://github.com/leanprover-community/mathlib4/pull/38295): L∞ ≅ (L¹)* as an
    isometry. Absent, medium size.
11. [#44746](https://github.com/leanprover-community/mathlib4/pull/44746): the complex Stirling
    formula with remainder. Absent; another rejected PR (#42881) notes its absence. CI failed.
12. [#43803](https://github.com/leanprover-community/mathlib4/pull/43803): Fejér's theorem on
    `AddCircle`. Absent; 2,200 lines to condense.
13. [#42468](https://github.com/leanprover-community/mathlib4/pull/42468): Adams operations and
    λ-rings. The one K-theoretic piece; depends on a symmetric-functions API.
14. [#34320](https://github.com/leanprover-community/mathlib4/pull/34320) and its series:
    Weierstrass and Hadamard factorisation. The largest body of absent mathematics, but it is
    55,000 lines with an authorship dispute, so it is high-cost and can only be split by its
    authors.
15. [#43488](https://github.com/leanprover-community/mathlib4/pull/43488) and
    [#37705](https://github.com/leanprover-community/mathlib4/pull/37705): Ramsey with the
    Erdős–Szekeres bound, and Johnson–Lindenstrauss. Both standard and absent.

## 7. Limits

- **Classification.**
  - One reader, from the last two to four comments (truncated), so a reason stated earlier in a
    long thread or on Zulip can be missed.
  - "Scope" and "design" overlap.
  - Some author-closed PRs sit on the line between "withdrawn" and "rejected"; I counted them as
    rejected only when the author was answering an objection.
  - About 10–15 % of rejected PRs are probably missed (§ 1). They are mostly author-closed with
    no explicit phrase.
- **Mathematical content** is judged from the title (feat/refactor, not golf, rename, lint, style
  or doc) or size; the 316 is approximate.
- **Code.**
  - Only 60 diffs were read, and those through their statements, docstrings, CI state and the
    `sorry`/`axiom` counts. No proof was checked line by line, and nothing was recompiled against
    current Mathlib.
  - "Absent from Mathlib" is a text search of the pinned Mathlib of 12 October 2026. A result may
    exist under another name, may have landed since, or may be in an open PR; I did not check the
    2,763 open PRs for overlap.
  - Costs are rough guesses: low means days, medium one to two weeks, high more.
- **The AI-policy count is a 2026 phenomenon.** It reflects both the rise in AI-generated
  submissions and a change of policy for new contributors, so it says little about how often
  mathlib turned PRs down before 2026 (30 of the 421 rejections are from 2022–2024).

Raw data, outside the repository and not versioned:
- the per-PR comment dump (`rejected/all_raw.jsonl`);
- the candidate sheets and labels (`cands.txt`, `labelled.json`, `extra.json`,
  `rejected_final.json`);
- the 60 diffs and their summaries (`diffs/`, `diffsum.json`, `docstrings.txt`, `ci.json`);
- the scripts `rej_*.py`.
