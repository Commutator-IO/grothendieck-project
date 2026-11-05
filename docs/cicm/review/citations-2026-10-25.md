# CICM paper: citation verification, 2026-10-25

Paper: `docs/cicm/article.tex`, last changed at 99af018. Bibliography: `docs/cicm/references.bib`.
Repository HEAD when checked: e9b4ad6 (24 Oct 2026, 18:49). This is a read-only review: nothing in the paper or the bibliography was edited.

## Method

Done per `~/.claude/skills/citation-verification` (canonical metadata first, then claim-level checks).

- **DOIs**: Crossref `api.crossref.org/works/{doi}`, all 15 DOIs in the bib. Title, authors, venue, volume, pages and year compared field by field.
- **arXiv identifiers**: arXiv API (`export.arxiv.org/api/query?id_list=`), all 11 identifiers.
- **Entries with no identifier**: Crossref bibliographic search. Semantic Scholar was tried twice and answered HTTP 429 every time, so it contributed nothing.
- **URLs**: `curl -I -L` HEAD requests, 10 URLs.
- **Claims**: full texts fetched from arXiv only (Edidin–Hu, Gorchinskiy–Viviani, Mathew, Clausen–Mathew, Gabber–Orgogozo, Pernice, Arsie–Vistoli), read with `pdftotext`. Formal Conjectures was checked through its README, CONTRIBUTING.md and file tree, using `gh api`. Mathlib PRs were checked with `gh pr list/view` on leanprover-community/mathlib4, author `mycaule`.
- **Not reachable** through the allowed sources: Kleiman 1968 and 1994, Cisinski 2006, Maltsiniotis 2005, Mumford 1965, Williams 1969 and the SMF volumes. Their claims are marked *not verified here*. Where the repository records a reading of these works, that record is quoted, and it should not be read as a check.

## Summary

| | count |
|---|---|
| Bib entries | 39 |
| Cited in the text | 39 (no uncited entry, no missing key; 41 `\cite` commands) |
| Exist | 39 of 39 |
| Metadata complete and correct | 30 |
| Metadata to fix or complete | 9: clausenmathew2021 (accent, DOI), mathew2021 (pages, DOI), pernice2022 (pages, DOI), wu2022 (proceedings), best2023 (published version), cisinskimo2026 (wrong source type), edidinhu2025 (volume pending), cisinski2006 and maltsiniotis2005 (DOIs available). The bib header's « checked on 21 October » is also stale |
| Rendering defects in the PDF | 2: [9] « ’etale », [38] « neurIPS 2022 » |
| Could not be checked (no open source among the allowed ones) | 8: kleiman1968, kleiman1994, cisinski2006, maltsiniotis2005, mumford1965, williams1969, colmez2001, maltsiniotis2022 (existence is beyond doubt; the cited theorem numbers are unchecked) |
| Dead or unreachable links | 1: grothendieck.umontpellier.fr (no response; the known Oct 2026 outage, expected back ~1 Nov) |
| Fabricated entries | 0 |
| In-text claims checked (22, table in section 2) | 8 supported; 6 supported but stated more broadly or loosely than the source (C2, C3, C5, C7, C8, C21); 3 inaccurate (C13 Cisinski « personal communication », C14 Formal Conjectures « published source », C16 PR count); 4 not verifiable here (C11, C12, C19, C20); 1 uncited (C22) |
| Works used but not in the bibliography | 9 (see « Missing references ») |

## 1. Entry by entry

| Key | Identifier check | Result | Action |
|---|---|---|---|
| mathlib2020 | Crossref 10.1145/3372885.3373824 | matches (CPP 2020, 367–381) | none |
| lean4 | Crossref 10.1007/978-3-030-79876-5_37 | matches (CADE 28, LNCS 12699, 625–635) | none |
| scholze2022 | Crossref | matches; Crossref adds issue 2 | optional: `number = {2}` |
| castelvecchi2021 | Crossref | matches; issue 7865 | none |
| hales2017 | Crossref | matches, 22 authors | none |
| formalabstracts | HEAD 200 | live | none |
| fltproject | HEAD 200 | live | none |
| best2023 | arXiv 2305.08955 | matches (4 authors, v2). A published version exists with a different title and six authors: « A complete formalization of Fermat's Last Theorem for regular primes in Lean », Annals of Formalized Mathematics 1 (2025), doi:10.46298/afm.14586 | cite the published version, or keep the arXiv and add a note |
| formalconjectures | HEAD 200 | live | see claim C14 |
| szegedy2020 | Crossref | matches (CICM 2020, LNCS 12236, 3–20) | none |
| wu2022 | arXiv 2205.12615 | matches; 7 authors (Jamnik, Szegedy omitted under « others ») | cite the proceedings: Advances in Neural Information Processing Systems 35 (2022), pp. 32353–32368 (Crossref 10.52202/068431-2344); write the note as `{NeurIPS} 2022`, because splncs04 lowercases it to « neurIPS » |
| azerbayev2023 | arXiv 2302.12433 | matches (Avigad among « others ») | none |
| xin2024 | arXiv 2405.14333 | matches | none |
| mathlibai | HEAD 200, section « Use of AI » present | live; the text supports what is cited (LLM-generated label, reviewers' pedagogical concern, summary closing) | none |
| kleiman1968 | no DOI; Crossref has no record | metadata standard (Adv. Stud. Pure Math. 3, 359–386, North-Holland 1968); not verified here | none |
| kleiman1994 | Crossref 10.1090/pspum/055.1/1265519 | matches (PSPUM 55.1, 3–20) | none |
| katz1970 | Crossref 10.1007/BF02684688 | matches | none |
| katz1972 | Crossref 10.1007/BF01389714 | matches | none |
| bost2001 | Crossref 10.1007/s10240-001-8191-3 | matches | none |
| williams1969 | not on Crossref (Numdam) | standard (Compositio 21, 1–3); not verified here | optional: Numdam URL |
| cisinski2006 | Crossref finds doi:10.24033/ast.715 | exists | add the DOI |
| cisinskimo2026 | — | **wrong type**. The repository (`lean/Grothendieck/Folder118.lean`, finding `118-groupoid-products-not-totally-aspherical`) records a **public MathOverflow answer** of 21 Oct 2026 (question 516223), CC BY-SA, not a private communication | replace it with a `@misc` for MathOverflow question 516223, answer by D.-C. Cisinski, 21 October 2026, with the URL; reword l. 80 « Asked directly » to match |
| maltsiniotis2005 | Crossref finds doi:10.24033/ast.689 | exists | add the DOI |
| colmez2001 | no DOI | standard; not verified here | none |
| maltsiniotis2022 | no DOI | standard; not verified here | also cite it for « Pursuing Stacks (1983) » in Table 1 |
| kmm | HEAD 200 | live | none |
| montpellier | **HEAD: no response** (000) | known outage (AHP/Montpellier down until ~1 Nov 2026) | recheck before submission |
| huajtei | HEAD 200 | live; a self-citation of an unpublished draft | fine for CICM; say « submitted » or « preprint » |
| hualean | HEAD 200 | live | page count in the text is stale (l. 60), see the peer review |
| repo | HEAD 200 | live | give a commit hash or tag in the entry |
| gorchinskiyviviani2008 | Crossref + arXiv math/0609705 | matches (Math. Z. 258(2), 319–331; online 2007, print 2008) | none |
| arsievistoli2004 | Crossref + arXiv math/0301008 | matches | none |
| gabberorgogozo2008 | Crossref + arXiv 0706.0671 | matches | none |
| edidinhu2025 | Crossref 10.1307/mmj/20236479 + arXiv 2208.00556 | matches; online-first (Crossref volume « -1 », pp. 1–23) | add the volume when it is assigned |
| mumford1965 | no DOI | standard; not verified here | none |
| pernice2022 | arXiv 2005.01513; Crossref finds doi:10.1093/imrn/rnab072 | exists; **no pages, no DOI** in the bib | add `pages = {11539--11574}`, `doi = {10.1093/imrn/rnab072}` |
| fultonolsson2010 | Crossref 10.2140/ant.2010.4.87 | matches | none |
| mathew2021 | arXiv 2005.08744; Crossref finds doi:10.1112/S0010437X21007144 | exists; **no number, pages or DOI**. splncs04 drops `eprint`, so the printed entry [29] carries no identifier at all | add `number = {5}`, `pages = {1079--1119}`, the DOI |
| clausenmathew2021 | arXiv 1905.06611; Crossref finds doi:10.1007/s00222-021-01043-3 | exists; **title accent broken** (`'etale` prints as « ’etale », [9]); no DOI, no issue | `title = {Hyperdescent and {\'e}tale {K}-theory}`, `number = {3}`, add the DOI |

The bib header (l. 1–4) says that every entry was checked on 21 October 2026. Six entries were added on 24 October (edidinhu2025, mumford1965, pernice2022, fultonolsson2010, mathew2021, clausenmathew2021). Update the header, or check those six the same way and date them.

## 2. Claims checked against the sources

| # | Line | Claim in the paper | Source checked | Verdict |
|---|---|---|---|---|
| C1 | 82 | Pic of [M_{0,n}/𝔖_n] is ℤ/2(n−1) for n even, by Gorchinskiy–Viviani Th. 3.6 | arXiv math/0609705, Th. 3.6: Pic(D_{2g+2}) = ℤ/(4g+2) if char k ∤ 2g+2; D_{2g+2} = [B_sm(2,2g+2)/PGL₂] | **Supported**. The source has a characteristic hypothesis, char ∤ n, that the paper omits. « Stack of smooth binary forms » should read « of *projective classes* of smooth binary forms modulo PGL₂ »: the affine stack of forms is a different stack, with a different Pic. |
| C2 | 82 | « the method of Arsie and Vistoli gives the rest » | arXiv math/0301008 (Th. 5.1: Pic of stacks of smooth forms / cyclic covers) | **Vague**. No statement for odd n is quoted, and the repository finding says the odd case was « recomputed by this pass ». Say « can be computed by the method of [1] », or give the computation. |
| C3 | 82 | Edidin–Hu compute A*([M_{0,2g+2}/𝔖_{2g+1}]) = ℤ[l]/(2g(2g+1) l) for g ≥ 2 | arXiv 2208.00556, **Theorem 1.3** (and Prop. in §3); conventions: g ≥ 2, k algebraically closed, char ∤ 2g+2 | **Supported** as to the group. **Overstated** as to « the order of L_i is also in print »: the paper gives a generator l = −l₁ + (g+1)l₂, not the class of L_i. That L_i has the maximal order is the edition's inference (Lean lower bound plus the group order). Say so. |
| C4 | 82 | Pernice's presentation by a Borel subgroup | Edidin–Hu §3 cites Pernice Prop. 1.3 and 1.5 | **Supported** |
| C5 | 82 | n = 4 follows from Pic(ℳ_{1,1}) = ℤ/12 [Mumford, Fulton–Olsson] | Fulton–Olsson (title and DOI checked); Mumford not reachable | **Inference not in the sources**. Going from ℤ/12 on ℳ_{1,1} to order 6 for L_i on [M_{0,4}/𝔖_3] passes through the hyperelliptic μ₂-gerbe. Give the one-line argument or say « can be deduced from ». |
| C6 | 106 | Gabber–Orgogozo: the local form, on an open of a henselian local domain, holds in a sharper form | arXiv 0706.0671, Th. 1.2: A *excellent* henselian local domain, dim_p(K) = dim A + dim_p(k); §6 extends it to affine opens of Spec A[1/p] | **Supported**. Add « excellent ». |
| C7 | 108 | Mathew proves a bound of the same shape for rings henselian along p | arXiv 2005.08744, **Prop. 4.5**: R an *excellent normal domain* henselian along I ∋ p, with dim R_𝔭 + log_p[κ:κ^p] ≤ d on V(I) ⇒ every residue field of R[1/p] has cd_p ≤ d+1 | **Supported, loosely**. It is a pointwise bound on residue fields, not on the cd of the scheme, and it carries the excellent-normal hypothesis. Name Prop. 4.5 and state it as pointwise. |
| C8 | 108 | For an arbitrary affine scheme only the cruder bound dim X + sup cd_p k(x) is known [Clausen–Mathew] | arXiv 1905.06611, **Cor. 3.29**: X qcqs of Krull dimension d, sup_x cd_x ≤ CohDim ≤ d + sup_x cd_x | **Supported** as to the bound. « only … is known » is a claim of absence. Write « the general bound we found is ». |
| C9 | 108 | the global bound with « +3 » was not found in print | — | a negative search claim; fine as worded |
| C10 | 106 | Katz proved the Gauss–Manin case [katz1972]; solvable case through Bost and others [bost2001] | metadata only | consistent with the standard attributions; theorem numbers not given or checked |
| C11 | 78 | Folder 16 claim = Kleiman 1968 **Th. 2.9**, same proof; 1994 **Th. 4-1** | not reachable. Repository record (finding `16-algebraic-iso-suffices`, read 2026-10-19): « Th. 2.9 — B(X) ⇔ C(X)+ν(X) ⇔ ν(X)+p(X) », p(X) rationality of characteristic polynomials | **Not verified here**. On the repository's own reading, Th. 2.9 uses p(X) where the folder uses D(X). Add a line saying D(X) ⇒ p(X) (or cite where Kleiman says so), so that « the same statement » is justified. |
| C12 | 80 | Cisinski Prop. 4.3.2, condition (g) | not reachable; the repository says it was read in the author's copy | **Not verified here**. The Lean model takes the groupoid characterisation of weak equivalences as a definition (`IsWeq`, `IsWeqOver`). Say « in a 1-truncated model where weak equivalences of groupoids are characterised by π₀ and π₁ ». |
| C13 | 80 | « Asked directly, Cisinski confirmed … [personal communication] » | repository: MathOverflow 516223, public answer, 21 Oct 2026 | **Inaccurate source type**: cite MathOverflow |
| C14 | 104, 108, 130 | Formal Conjectures « collects open conjectures stated in Lean with a published source »; « asks for a published source » | README, CONTRIBUTING.md (fetched 24 Oct) | **Overstated**. Sources accepted include Wikipedia, MathOverflow, OEIS and an `Other` folder; solved variants are also welcome (`@[category research solved]`). The repo has 964 Erdős-problem files, 251 OEIS, 182 Wikipedia, 10 Other. Reword as « with a cited source (literature, problem lists, Wikipedia, MathOverflow) ». « cannot enter … as they stand » should become « would need a citable source ». |
| C15 | 104 | none of the seven conjectures was in Formal Conjectures on 17 Oct | file tree on 24 Oct: no file name matches Grothendieck, standard conjecture, Hodge, p-curvature, section conjecture, homotopy hypothesis or Teichmüller (only `Wikipedia/HasseWeil.lean`, `EllipticCurve/GlobalPeriod.lean`) | **Consistent** (a file-name check only, not a full-text search) |
| C16 | 112–114 | 41 PRs between 10 and 20 Oct, 39 with the LLM-generated label, none merged, most closed by the triage account, two closed after J. Riou's comments, E. Wieser's review of the Pascal PR | `gh pr list --author mycaule`: **39 PRs in total, all 39 labelled LLM-generated**, created 10–20 Oct (#44702–#45064); 0 merged; 36 closed by `mathlib-triage[bot]`, 3 by the author (#44731 and #44732 among them, after Riou's comments); Wieser's review comment on #45008 matches | **Count wrong**: 39 of 39, not 39 of 41. « closed after » is right, but say « closed by the author after ». The comments are summarised fairly. |
| C17 | 114 | Mathlib's AI policy | contribute page, « Use of AI » | **Supported** |
| C18 | 130–132 | Related-work characterisations (Kepler, LTE, FLT, Formal Abstracts, Szegedy, Wu, ProofNet, DeepSeek-Prover) | abstracts/metadata | **Supported** |
| C19 | 84 | Williams: universes are V_κ under foundation | not reachable | **Not verified here**; this is the standard reading of Williams 1969 |
| C20 | 74 | Prop. 4 of p. 350 of *À la poursuite des champs* refuted by the category of cubes [Cisinski 2006, Maltsiniotis 2005] | not reachable | **Not verified here**; give section numbers |
| C21 | 54 | lean-action's axiom audit: fails if any declaration of the library depends on an axiom beyond the three | `leanprover/lean-action` action.yml: audits « declarations defined under the project's root namespace » | **Slightly overstated**: the 26 `Upstream/` files declare in Mathlib namespaces (`CategoryTheory`, `Polynomial`, …), so they are audited only through their uses (see the peer review) |
| C22 | 94–100 | Table 1 « published source » column: Grothendieck 1966, 1969; Bost–Charles 2016; *Pursuing Stacks*; *Esquisse*; letter to Faltings | — | **Uncited** (no bib entries); see below |

## 3. Missing references

These are used or named in the text, with no entry in the bibliography. Metadata was checked on Crossref where a DOI exists.

1. Grothendieck, « On the de Rham cohomology of algebraic varieties », Publ. Math. IHÉS 29 (1966) 95–103, doi:10.1007/BF02684807. Table 1, period conjecture.
2. Grothendieck, « Standard conjectures on algebraic cycles », in *Algebraic Geometry* (Bombay Colloquium 1968), Oxford Univ. Press, 1969, 193–199. No DOI. Table 1.
3. Grothendieck, « Hodge's general conjecture is false for trivial reasons », Topology 8 (1969) 299–303, doi:10.1016/0040-9383(69)90016-0. Table 1, generalised Hodge.
4. Bost, Charles, « Some remarks concerning the Grothendieck period conjecture », J. reine angew. Math. 714 (2016) 175–208, doi:10.1515/crelle-2014-0025. Table 1.
5. Grothendieck, « Esquisse d'un Programme », in Schneps, Lochak (eds.), *Geometric Galois Actions 1*, LMS Lecture Note Series 242, CUP 1997, 7–48, doi:10.1017/CBO9780511758874.003. Table 1.
6. Grothendieck, « Brief an G. Faltings », same volume, 49–58, doi:10.1017/CBO9780511758874.004. Table 1, section conjecture.
7. *Pursuing Stacks*: already in the bib as `maltsiniotis2022`. Cite it in Table 1.
8. MathOverflow question 516223, D.-C. Cisinski's answer, 21 Oct 2026. It replaces `cisinskimo2026`.
9. Archives Bourbaki (Archives Henri Poincaré), drafts no. 288, 307 and 457, named in l. 52 and l. 84 with no reference.

Optional: the Tau Ceti roadmap PR named in l. 116 (TauCetiProject/TauCetiRoadmap#1086). A source for Jacobson's formula (l. 106; Jacobson 1937, or Katz 1970 §5) is also optional.

## 4. Format (splncs04)

- `eprint`/`archivePrefix` are ignored by splncs04. For gorchinskiyviviani2008, arsievistoli2004 and gabberorgogozo2008 the DOI carries the identifier. For mathew2021 and clausenmathew2021 nothing is printed: add their DOIs.
- edidinhu2025 and pernice2022 put the arXiv in `note`, which is inconsistent with the `eprint` entries. Pick one convention.
- `@misc` with `howpublished = {arXiv:…}` (best2023, wu2022, azerbayev2023, xin2024) is acceptable in LNCS.
