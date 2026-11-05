# Peer-review working draft: CICM-HUA-2026-10-25

> A private working document: a mock CICM referee report written for the author before submission. Every number below was recomputed from the repository at HEAD e9b4ad6 (24 Oct 2026, 18:49). The paper itself was last changed at 99af018. Nothing in the paper was edited. The author has to verify and rewrite this before using any of it.

## Intake record

- Paper: « Formalising a Mathematician's Working Notes: 2,119 Lean Theorems from the Grothendieck Archive », `docs/cicm/article.tex`, LNCS (`llncs`), 13 pages: body to p. 11, references on pp. 11–13.
- Reviewer capacity: `author_requested_reader`, a pre-submission review requested by the author. The material is the author's own preprint, already public (`public/article/grothendieck-cicm.pdf`, public repository).
- Skill intake validator (`validate_review_intake.py`): **BLOCKED**, for two declared reasons. (1) The CICM 2027 review model is unknown: the call was not online when the README was written. (2) The assistant session is hosted, not local-only. Both are expected for a self-review of public material, and the author requested it. The review went ahead on that basis. The status is recorded here, not overridden.
- Peer-review model: `unknown`. Declared processing: `approved_ai_assistance` (Claude, at the author's request).
- Parts of the skill that were skipped as inapplicable: reporting-guideline selection (CONSORT, PRISMA and the like), the statistics audit, and the clinical, ethics and participant sections. The paper reports no statistical inference and no human-subject research.
- Competence limits: specialist review is advised for (a) the moduli-stack identifications of § 5 (folder 146: Picard groups of [M_{0,n}/𝔖_n], the gerbe step from ℳ_{1,1}) and (b) the set-theoretic claim on Bourbaki draft 307 (§ 5, « A refutation outside Lean »).

# Comments to authors

## Evidence-bounded summary

The paper reports a project. Statements are taken from LLM-produced « modernised readings » of Grothendieck's working notes (Montpellier fonds) and formalised in Lean 4 against a pinned Mathlib master. The paper describes the pipeline (Fig. 1), an attribution rule (« Grothendieck, page N » only if the page states it), a reachability triage of 203 open findings (16/39/147/1), and what the formalisation found: false glosses, errors on the page, statements already in print, a question of the notes (folder 146, p. 70) answered for every n in a model. It also places seven conjectures found in the notes beside Formal Conjectures, gives an account of 39–41 Mathlib PRs that were all closed, the limits of human checking, and costs. The central quantitative claims are 74 files, 40,667 lines and 2,119 top-level `theorem` declarations depending only on the three standard axioms, plus 69 proof cards with a verdict distribution.

## Strengths

- **A real, inspectable artefact.** Every claim points to a public file. I could recompute almost every number from `lean/`, `src/content/{proofs,findings}.ts`, `src/content/hand.json` and the GitHub issues. Few CICM project papers allow this.
- **The paper is honest about what Lean can and cannot check** (l. 42, l. 120–122): a proof certifies a reading's coherence, not its faithfulness to the page. Issue #69, where a reader of the hand cannot judge the mathematics, is a useful negative result.
- **The attribution rule is a good contribution** for formalisation of historical material. It is applied in the appendix: 183 boxed statements carry « Grothendieck, page N » and 11 are labelled « énoncé de l'édition » (count over `docs/lean/` at HEAD).
- **The Mathlib section reports the reception of AI-generated PRs plainly and accurately.** I checked it against the threads: 36 of 39 were closed by `mathlib-triage[bot]`, and J. Riou's and E. Wieser's comments are summarised fairly. The community needs this kind of report.
- **The axiom hygiene is real.** CI runs `lake build` with `warningAsError = true` and lean-action's `axiom-audit: true`. The last five runs of `lean.yml` passed. There is no `axiom`, `sorry` or `native_decide` in `lean/Grothendieck/` at HEAD.

## Recount against the repository (HEAD e9b4ad6)

| Line | Claim in the paper | Recomputed | Status |
|---|---|---|---|
| 24, 32, 52 | 74 files (72 folders and 2 Bourbaki), 40,667 lines, 2,119 `^theorem` | 74; 72 + 2; 40,667 (`wc -l` equivalent); 2,119 | **matches** |
| 52 | counting rule `grep -c '^theorem'` | It leaves out 285 top-level `lemma`s, 9 `private theorem`s and the 63 theorems in the 26 `Upstream/` files (3,448 lines). Indented `theorem`s: 2,143 | rule stated, but the title « 2,119 Lean theorems » is rule-dependent (M1) |
| 52 | first file committed 26 Sep 2026 | 48b7bfe, 26 Sep 22:03 | matches |
| 52 | « 185 commits have touched the directory since » | 201 commits touch `lean/` at HEAD (196 touch `lean/Grothendieck/`). 186 is the count up to 23 Oct, when the library had 69 files, 39,562 lines and 2,052 theorems | **mixed snapshot** (M2) |
| 126 | 186 commits from 26 Sep to 23 Oct | 186 up to 23 Oct | matches its own date, but not the file counts of l. 52 |
| 54 | toolchain v4.35.0-rc4, Mathlib master pin | `lean-toolchain` v4.35.0-rc4; Mathlib `715a03a90adf491de40fbec8b456c179a623435f` | matches; the hash is not in the paper (M7) |
| 50 | 463 findings from 155 folders: 216/165/73/8/1 | 463, 155 folders, 216/165/73/8/1 | **matches** (also unchanged at HEAD) |
| 60, 70 | 69 cards: holds 14, more generally 16, partly 33, dropped hypothesis 3, gloss false 1, false on the page 2 | **74 cards**: holds 13, more generally 16, partly 34, dropped 3, gloss false 2, false on the page 6. The same at 99af018, the commit that last changed the paper | **stale** (M2) |
| 60 | appendix 277 pages | 293 pages (`docs/lean/article.pdf` at HEAD; 295 in the working tree) | **stale** |
| 116 | 26 files in `Upstream/` | 26 | matches |
| 32, 40 | 164 folders, 638 passes, 9,414 pages | `hand.json`: 164 folders, 638 batches, 9,414 pages; 164 `*.modern.tex` | matches (README still says 9,415) |
| 38 | 178 folders, 16,074 pages, 20 edited by hand | consistent with the jTEI paper's Table 1 | consistent |
| 32 | « written between 1949 and 1991 » | the jTEI companion says « the inventory dates from 1953 to 1991 » | **inconsistent across the companion papers** (m1) |
| 66 | 203 open findings, 111 folders, tiers 16/39/147/1 | issue #54: identical | matches |
| 112 | 41 PRs (10–20 Oct), 39 labelled | `gh pr list --author mycaule`: **39 PRs, all 39 labelled**, #44702–#45064, 0 merged, 36 closed by the triage bot, 3 by the author | **wrong count** (M5) |
| 120 | 19 issues settled 173 items: 74 word readings (40 insertions), 57 dates | `review-answered.json`: 19 issues, 183 answered items, 167 applied/confirmed; insertions (supplied + add) 40 ✓; date items 45 settled (47 answered) | **73 / 57 / 173 not reproducible from the repository file** (m4) |
| 138 | 879 drawings (#73) | `hand.json` today: 902 drawings | stale (m5) |
| 76 | « Eight errors are on the page » | Seven are listed (19 ×2, 152, 93, 74, 86, 70). The cards marked *false on the page* are 19, 80, 90, 150, 156-4 and 160, so only folder 19 is in both lists. The folder 74 card says *the reading dropped a hypothesis*: the condition is in the margin, so it is not an error on the page | **count and list inconsistent** (M3) |
| 104 vs Table 1 | « Four of the seven cannot be stated in Mathlib today » | Table 1 has three « no » (standard conjectures, generalised Hodge, section conjecture) | **inconsistent** (m2) |
| 70, 97, 106 | p-curvature: easy direction « in rank one » | `Folder93.lean` also proves it in rank n on the trivial bundle (`curvMat_eq_zero_of_horizontal`), with rank-2 examples (Airy, unipotent) | **understated** (m3) |
| 126 | « `axioms.sh` re-runs the axiom check » | `axioms.sh` was deleted in f16d1d8 (24 Oct); CI's lean-action audit replaces it | **stale** (M7) |
| 138 | tooling « reused for two other archives » | the repository has `transcripts-bourbaki`, `-quillen`, `-illusie`, `-buffalo` | imprecise (m6) |
| Fig. 2 | 2,119 of 2,119 theorems in 28 parts; 4 empty parts; descent only folder 128 | `fig-themes.tex` drawn at HEAD: same; descent = 3 theorems | matches |

## Major comments

### Major comment M1: the headline number does not measure what the title says

- Location: title (l. 24), abstract (l. 32), § 2 (l. 52), Fig. 2.
- Observation: « 2,119 Lean Theorems from the Grothendieck Archive » counts every top-level `theorem` keyword in 74 files. That includes auxiliary lemmas written as `theorem`, the edition's own counterexamples and lemmas, and the two Bourbaki files, which are not in the Grothendieck archive. It leaves out 285 `lemma` declarations, the `private theorem`s and `Upstream/`. Nothing in the paper says how many *statements of the pages* are formalised, which is the quantity a CICM reader wants.
- Evidence or criterion: recount above. The appendix already labels 183 statements « Grothendieck, page N » and 11 « énoncé de l'édition ». The cards give the verdicts.
- Why it matters: the title is the paper's main quantitative claim. Under the paper's own attribution rule (l. 58), most of the 2,119 are not « from the archive », so the title contradicts the rule the paper proposes.
- Requested action: change the title (for example « Formalising a Mathematician's Working Notes: Lean Proofs from the Grothendieck Archive »). Report a small table: page statements formalised (fully or partly), edition statements, counterexamples, auxiliary declarations. Keep 2,119 as a size measure with its rule, and say that the Bourbaki files are included.

### Major comment M2: the numbers come from different snapshots

- Location: l. 52, 60, 70, 126; README « What remains to check ».
- Observation: the file, line and theorem counts are those of 24 Oct (HEAD). The commit counts (185/186) are those of 23 Oct. The cards (69, with their verdicts) and the appendix's page count (277) are older than the commit that last revised the paper (99af018 has 74 cards and the appendix is now 293 pages). The README still gives 2,052 theorems, 69 files and 39,722 lines.
- Evidence or criterion: recount table.
- Why it matters: a reader who checks one number, as invited (« at the commit described here »), finds that the others disagree. The verdict distribution is a result of the paper, and it changed: *false on the page* went from 2 to 6 and *gloss false* from 1 to 2.
- Requested action: name one commit hash in the paper (a footnote in § 2), regenerate every count at it by script (extend `figures.mjs` to emit the counts as macros), and use those macros in the text. Update l. 60, 70, 76 and the README.

### Major comment M3: « Errors on the page » does not match the repository's own classification

- Location: § 5, « Errors on the page » (l. 76); abstract (« errors on the page »).
- Observation: the paragraph says eight and lists seven. The cards marked *false on the page* are folders 19, 80, 90, 150, 156-4 and 160. Of these, only 19 appears in the paragraph. The paragraph's folder 74 is, by its card, a case where the page carries the condition in the margin (*the reading dropped a hypothesis*). Folders 152, 86 and 70 have the verdicts *partly proved* or *holds*, with slips noted in the text. The appendix's « Bilan » (`docs/lean/sections/reste.tex`) gives yet another grouping.
- Evidence or criterion: `src/content/proofs.ts` at HEAD; `reste.tex` ¶ 3.
- Why it matters: this is the paper's most quotable finding, about errors in Grothendieck's notes, and it concerns the attribution of errors to a named mathematician. The paper's own rule calls for precision here.
- Requested action: define « error on the page » (for example: a statement on the leaf, not in the reading, that Lean refutes or corrects). Derive the list from the cards, give the number, and separate refuted claims (80, 90, 156-4, 160, 19), slips of index or label (86, 152), and sign or characteristic slips (70, 93, 160). Remove 74, or explain why it is there.

### Major comment M4: folder 146 says more than Lean and the literature support

- Location: abstract (« answered one question of the notes for every n »), § 5 ¶ « A question of the notes settled » (l. 82), § 6 (l. 106).
- Observation: the paragraph claims more than is proved, in five places (below).
- Evidence or criterion: `lean/Grothendieck/Folder146.lean` (docstrings and the statements of `six_dvd`, `coboundary_*_iff`, `trivL_iff`, `trivLi_iff`); arXiv 2208.00556 Th. 1.3; arXiv math/0609705 Th. 3.6.
  1. `trivL_iff` and `trivLi_iff` hold **over a field with primitive roots of unity of orders n − 1 and n − 2**. The paper says « for every n » with no hypothesis on K.
  2. The functions F in `TrivL`/`TrivLi` are arbitrary functions on K-points, « not required to be regular ». The upper bounds are explicit regular functions, which is fine; the lower bounds hold for arbitrary F. The passage from line bundles to these weight functions is not formalised (the paper says so), so « answered » should read « answered modulo an unformalised dictionary ».
  3. For n = 4 the docstring says the reduction from 𝔖₄ to 𝔖₃, the formula sgn g · g′(λ) for L, and the identification of the equivariant Pic with H¹ are not formalised. The paper presents the n = 4 values of L and L_i as « Lean confirms ».
  4. Edidin–Hu Th. 1.3 gives the *group* A¹ = ℤ/2g(2g+1) with a generator l = −l₁ + (g+1)l₂. It does not give the class of L_i. « The order of L_i is also in print » is an inference (a cyclic group of order (n−1)(n−2), plus the Lean lower bound). Likewise « n = 4 follows from Pic(ℳ_{1,1}) = ℤ/12 » needs the μ₂-gerbe argument. And « the method of Arsie and Vistoli gives the rest » quotes no statement.
  5. Gorchinskiy–Viviani Th. 3.6 assumes char k ∤ n. The quotient is of *projective classes* of smooth binary forms modulo PGL₂. This is not the affine stack of forms, whose Pic differs.
- Why it matters: this paragraph and the abstract put forward « what the edition adds » (the odd case). That claim has to rest on exactly what is proved.
- Requested action: state the hypotheses (primitive roots; arbitrary rather than regular functions; the dictionary not formalised, including for n = 4). Rephrase the literature sentences as « the group is known (…); that L_i generates it follows from the Lean lower bound ». Give the gerbe step for n = 4, or drop it. Name the A–V statement, or say the odd-n group was recomputed. In the abstract, say that the even case was already in print.

### Major comment M5: Mathlib section: the count, and how the PRs are attributed

- Location: § 7 (l. 112–116).
- Observation: GitHub shows 39 PRs by `mycaule` in mathlib4 (#44702–#45064, 10–20 Oct), all 39 with the LLM-generated label. The paper says 41 and 39. Two of the three PRs the author closed (#44731, #44732) are described as « closed after Joël Riou wrote… », which is correct but leaves out who closed them. The paragraph names two reviewers and paraphrases their comments.
- Evidence or criterion: `gh pr list -R leanprover-community/mathlib4 --author mycaule --state all`; the issue close events (36 `mathlib-triage[bot]`, 3 `mycaule`); the threads of #44727, #44731, #44732, #45008 and #44702.
- Why it matters: the paper reports on a community's response. The numbers should be exact, and so should who did what.
- Requested action: correct the count to 39 of 39, or say where the other two PRs are. Write « closed by the author after ». Before submission, consider telling J. Riou and E. Wieser that the paper paraphrases their public comments. Say how many of the 39 come from this edition and how many from the separate Lean-learning exercise: issue #52 lets you count this.

### Major comment M6: AI-use declaration: incomplete list of models, and the wrong template

- Location: « Declaration on the Use of Generative AI » (l. 140–142).
- Observation: the declaration names Claude Opus 5 and Opus 5.5. The repository records first transcription passes by **Claude Fable 5** (5 batches) and **Claude Fable 5.1** (26 batches), modernised-reading headers naming both, and **Claude Sonnet 5.5** as co-author of one commit touching `lean/`/`docs/cicm`. The closing sentence (« After using these tools, the author reviewed and edited the content as needed and takes full responsibility… ») is the CEUR/Elsevier declaration template. Springer Nature's policy asks for LLM use to be documented in the Methods section, or a suitable alternative section. LNCS's current template also asks for a **Disclosure of Interests** statement (`credits` environment, `\discintname`), and the paper has none.
- Evidence or criterion: `transcripts/*/batch-*.tex` « % Pass: » headers (505 by Opus 5.5, 102 by Opus 5, 26 by Fable 5.1, 5 by Fable 5); git `Co-Authored-By` trailers; Springer Nature AI policy; the llncs `samplepaper.tex` credits block.
- Why it matters: an incomplete declaration is a compliance issue, whatever the quality of the work. The paper is about AI provenance, so its own provenance statement has to be exact.
- Requested action: list every model and version with its role (transcription first passes: Opus 5.5, Opus 5, Fable 5.1, Fable 5; readings; Lean; paper drafting). Keep the declaration, and add a sentence in § 2 (Methods) pointing to it. Add `\begin{credits}…\subsubsection{\discintname}…\end{credits}`, declaring any relationship or funding application involving the AI vendor, or stating that there are none. Remove or adapt the CEUR wording.

### Major comment M7: reproducibility statements are stale or imprecise

- Location: § 2 (l. 54), § 9 (l. 126).
- Evidence or criterion: commit f16d1d8; `leanprover/lean-action` `action.yml` (input `axiom-audit`); `namespace` lines of `lean/Grothendieck/Upstream/*.lean`; `lean/lakefile.toml`; `.github/workflows/lean.yml`.
- Observation: four statements are stale or imprecise.
  1. l. 126 says « `axioms.sh` re-runs the axiom check ». The script was removed in f16d1d8, the commit whose message says the CICM paper was updated.
  2. l. 54 says the lean-action audit fails if « any declaration of the library » uses a non-standard axiom. lean-action audits « declarations defined under the project's root namespace ». The 26 `Upstream/` files declare in Mathlib namespaces (`CategoryTheory.Adjunction`, `Polynomial`, `Matrix`, …), so they are audited only through the `Grothendieck.*` declarations that use them.
  3. Neither the Mathlib commit (715a03a9…) nor the repository commit is given. The build command needs `cd lean`.
  4. leanchecker (the independent kernel re-check) is disabled in CI because it stopped the runner (`lean.yml` comment). Say so.
- Why it matters: CICM reviewers will try the build. A dead script and an imprecise audit claim weaken the paper's strongest asset.
- Requested action: replace `axioms.sh` with the CI audit, or with a `#print axioms` recipe. Either word the audit as « declarations in the `Grothendieck` namespace, and transitively what they use », or set `axiom-audit-root` (or a second audit) to cover `Upstream/`. Give both hashes and a release tag. State that leanchecker is not run.

### Major comment M8: contribution, novelty and related work

- Location: § 1 contributions (l. 44), § 10 Related work (l. 128–134).
- Observation: the contributions are a pipeline, a triage, an account of findings, and a report on reception. That fits CICM's « project and survey » category better than a regular paper. Related work does not discuss: formalisation of historical texts and proofs (for example Beeson, Narboux, Wiedijk, « Proof-checking Euclid », Ann. Math. Artif. Intell. 85 (2019) 213–257, doi:10.1007/s10472-018-9606-x); mathematical knowledge management and semantic markup of mathematical documents, the CICM core (for example Kohlhase, « Using LaTeX as a semantic markup format », Math. Comput. Sci. 2 (2008), doi:10.1007/s11786-008-0055-5), which bears on the restricted-LaTeX apparatus; and recent research-level autoformalisation and agentic proving, as opposed to the 2022–2024 benchmark papers cited. The paper also never quantifies the autoformalisation step itself: how many attempted statements failed, were dropped, or were changed by Lean.
- Evidence or criterion: CICM's paper categories (regular, project and survey); § 10 as written; issues #54 and #72, which record estimates and drops.
- Why it matters: the novelty claim (« starts from statements scattered through drafts », l. 130) is credible, but it needs positioning against the MKM literature that CICM reviewers know.
- Requested action: submit as a project paper, or say why it is a regular paper. Add one paragraph each on historical formalisation and on MKM/semantic markup. If the history allows, report attrition: statements selected, attempted, proved, refuted, abandoned (#54/#72 give estimates and drops).

## Minor comments

### Minor comment m1: dates of the fonds
- Location: l. 32.
- Observation: « between 1949 and 1991 » here; « 1953 to 1991 » in the jTEI companion.
- Evidence or criterion: `docs/study/article.tex` l. 25.
- Why it matters: companion papers should agree.
- Requested action: use one range and say what it rests on (inventory, or the leaves).

### Minor comment m2: Table 1 against the text
- Location: l. 94–104.
- Observation: the text says four of the seven cannot be stated; the table shows three « no ». The table cites Grothendieck 1966 and 1969, Bost–Charles 2016, *Pursuing Stacks*, *Esquisse* and the letter to Faltings with no bibliography entries (the README already notes this). The dates and pages are not checked on the facsimile (README).
- Evidence or criterion: the table itself; `docs/cicm/README.md`.
- Why it matters: internal consistency; the dates bear on « earlier than the texts usually cited ».
- Requested action: reconcile the count, add the six references (verified metadata in the citation report), and say in the caption that the leaf dates are machine readings not checked on the facsimile.

### Minor comment m3: folder 93 is understated
- Location: l. 70, 97, 106.
- Observation: Lean proves the easy direction in rank n on the trivial bundle, with rank-2 examples. The paper says rank one.
- Evidence or criterion: `Folder93.lean` `curvMat_eq_zero_of_horizontal`, `curvMat_airy_three/five`.
- Why it matters: accuracy, and it changes Table 1's « rank one only ».
- Requested action: update the three places.

### Minor comment m4: review-page figures
- Location: l. 120.
- Observation: 173 / 74 / 57 cannot be reproduced from `src/content/review-answered.json` (183 answered via 19 issues, 167 applied/confirmed, 45 settled date items; the 40 insertions do match). « 135 readings in 54 folders » has no stated source.
- Evidence or criterion: recount table.
- Why it matters: the human-checking section is where the paper's limits are argued.
- Requested action: give the counting rule and source (issues as of 23 Oct, or the JSON), or switch to the JSON figures.

### Minor comment m5: drawings
- Location: l. 138.
- Observation: 879 (the #73 title); `hand.json` now has 902.
- Evidence or criterion: `hand.json` sum of `drawings`.
- Why it matters: a stale number.
- Requested action: recount at the chosen commit.

### Minor comment m6: other archives
- Location: l. 138.
- Observation: « reused for two other archives ». The repository has Bourbaki, Quillen, Illusie and Buffalo pipelines.
- Evidence or criterion: `transcripts-*` directories.
- Why it matters: precision.
- Requested action: say « other archives », or name the ones meant.

### Minor comment m7: Cisinski
- Location: l. 80; bib `cisinskimo2026`.
- Observation: the confirmation is a public MathOverflow answer (question 516223, 21 Oct 2026), cited as « personal communication ». « (g) is weaker than the others » should read « (g) does not imply (c) for A = BG ». The Lean model takes the groupoid criterion for weak equivalences as a definition.
- Evidence or criterion: `Folder118.lean` docstring; finding `118-groupoid-products-not-totally-aspherical`.
- Why it matters: correct sourcing, and an exact statement of what Lean checks.
- Requested action: cite MathOverflow; restate the claim; mention the modelling assumption.

### Minor comment m8: Formal Conjectures
- Location: l. 104, 108, 130.
- Observation: the repository accepts cited sources including Wikipedia, MathOverflow, OEIS and « Other », and solved variants as well. « Asks for a published source » overstates its rule.
- Evidence or criterion: its README and CONTRIBUTING.md.
- Why it matters: the paper uses this rule to explain why the folder 31 and 69 questions cannot enter the repository.
- Requested action: reword (see the citation report, C14). The note posted on Zulip cannot be verified from the repository; give a link.

### Minor comment m9: folder 31 literature
- Location: l. 108.
- Observation: Gabber–Orgogozo Th. 1.2 and § 6 assume A *excellent*. Mathew Prop. 4.5 bounds cd_p of the *residue fields* of R[1/p], for R excellent normal, henselian along I ∋ p. It does not bound the scheme. « Only the cruder bound … is known » is a claim of absence.
- Evidence or criterion: arXiv 0706.0671, 2005.08744 (Prop. 4.5), 1905.06611 (Cor. 3.29).
- Why it matters: exact comparison with the « +3 » conjecture.
- Requested action: add the hypotheses and theorem numbers; write « the best general bound we found ».

### Minor comment m10: Bourbaki draft 307
- Location: l. 84.
- Observation: the set-theoretic claim (the two definitions differ at every inaccessible that is a limit of inaccessibles; the question is undecided in ZFC) is argued only « in the edition's register ». The draft is not cited, and draft 457 (l. 52) is never discussed.
- Evidence or criterion: no bib entry for the Bourbaki archive.
- Why it matters: an unformalised refutation in a paper about formalisation needs at least a sketch and a source.
- Requested action: cite the AHP archive items, add a two-line argument or a pointer to the register, and give one sentence to what Bourbaki457.lean proves.

### Minor comment m11: Fig. 1 against the AI declaration
- Location: Fig. 1 (arrow « Modernised reading → Statement » labelled *model*) and l. 142 (« The author chose … the statements to formalise »).
- Observation: the two disagree on who chooses the statements.
- Evidence or criterion: `fig-pipeline.tex`.
- Why it matters: the paper is about who did what.
- Requested action: mark that arrow as a human choice, or as a model proposal with human selection.

### Minor comment m12: Kleiman match
- Location: l. 78.
- Observation: according to the repository's reading, Kleiman's Th. 2.9 is ν(X) + p(X) ⇒ B(X). The folder uses D(X).
- Evidence or criterion: finding `16-algebraic-iso-suffices`.
- Why it matters: « the same statement » should be literally true.
- Requested action: add « D(X) implies p(X) » with a reference, or state the match as « Kleiman's Th. 2.9, via D ⇒ p ».

### Minor comment m13: bibliography hygiene
- Location: references.
- Observation: rendering defects ([9] « ’etale », [38] « neurIPS »); missing DOIs and pages (Mathew, Clausen–Mathew, Pernice, Cisinski, Maltsiniotis); published versions available (Wu, Best et al.); the bib header's « checked on 21 October » predates six entries.
- Evidence or criterion: citation report.
- Why it matters: presentation.
- Requested action: apply the fixes listed in `citations-2026-10-25.md`.

### Minor comment m14: LNCS format
- Location: whole paper.
- Observation: 13 pages, within the 2026 call's limit of 15 pages plus references. The `\orcidID`, keywords and running heads are correct. Fig. 1 is `\resizebox`ed to `\textwidth`, which makes its 7 pt `\scriptsize` labels smaller still; check legibility in print. The pdfLaTeX branch (`T1`/`lmodern`) is what Springer will compile. Test it once, because the site copy is built with XeTeX. A Disclosure of Interests block is missing (M6). If the 2027 call turns out to be double-blind, the self-citations (`huajtei`, `hualean`, `repo`) and the ORCID will need an anonymous version.
- Evidence or criterion: llncs template; the CICM 2026 call (README).
- Why it matters: avoiding a desk check.
- Requested action: run `pdflatex` with `splncs04` once, and check Fig. 1 at 100 %.

## Folder paragraphs double-checked against the Lean files

| Folder | Paper | Lean at HEAD | Verdict |
|---|---|---|---|
| 146 | n = 4: six substitutions through 𝔖₃, cocycle g′(λ), sixth power = coboundary of λ⁴(1−λ)⁴, no smaller; L exponent 3. n = 5: L 4, L_i 12. n = 6: L 5, L_i 20; lower bounds at fixed points with a primitive 5th root and i. All n: L n−1, L_i (n−1)(n−2); lower bounds from {0} ∪ μ_{n−1} and {0,∞} ∪ μ_{n−2}; the dictionary not formalised | `mul_group`, `anh_mul`, `der_mul`, `der_pow_six`, `six_dvd` (needs 2, 3 ≠ 0 and a root of ζ² − ζ + 1), `derL_pow_three`, `coboundary_derL_iff`, `coboundary_cL_iff`, `coboundary_c5_iff`, `coboundary_cL6_iff` (ω primitive 5th root), `coboundary_c6_iff` (ι² = −1), `trivL_iff` / `trivLi_iff` (primitive (n−1)th and (n−2)th roots, n ≥ 2 / 3, F arbitrary, not regular) | **values correct**; hypotheses and the n = 4 modelling steps are missing from the text (M4) |
| 31 | the local form by Gabber–Orgogozo; Mathew for henselian along p; Clausen–Mathew crude global bound; « +3 » not found | no Lean file (none claimed) | **consistent**; literature statements need their hypotheses (m9) |
| 69 | the automorphisms preserving a triangle form a group of order 1152, by a stabiliser chain | `card_Wt`, `card_aut` (1152), `card_pointwise` (192), orbit sizes 3·2·8·4·3·2 checked by the kernel | **matches**; could add « 192 fixing it pointwise » |
| 93 | D^p a derivation; Jacobson's formula for D + μ_a; easy direction in rank one, trivial bundle; ad − bc = 1 false, s = 2t over 𝔽₅ | `pDerivation`, `jacobson`, `pCurvature_eq_zero` (rank one, a unit horizontal section), **plus** `curvMat_eq_zero_of_horizontal` (rank n), the Airy and unipotent rank-2 examples; `det_one_counterexample` in 𝔽₅[T]/(T⁵) | **matches**, but understated (m3) |
| 118 | (g) weaker than the others for A = BG, checked in a 1-truncated model | `condition_g_holds`, `not_condition_c`, `g_not_imp_c`; weak equivalences of groupoids *defined* by π₀/π₁ | matches, modulo the modelling assumption (m7) |
| 140-1 | H¹(U_{0,3}, 𝔖₃; 𝔾_m) = ℤ/6 | `H1_units` (ℤ/6 for 2 ≠ 0; ℤ/3 in char 2) in a model of the units; O(U)^* = Units3 and Hochschild–Serre not formalised | matches; « in a model of the units » is missing |

## Methods and reproducibility

- **Method**: the tiers are defined (l. 66) and match issue #54. The attribution rule is defined (l. 58) and applied in the appendix. Its application is not audited: there is no count of attributed versus edition statements, and no second reader.
- **Claims and evidence**: all quantitative claims are traceable. Six are stale or wrong (M2, M3, M5, m2, m4, m5).
- **Reproducibility**: toolchain and Mathlib are pinned; CI builds with warnings as errors and audits the axioms; the last five runs passed. Missing: the two commit hashes in the text, a tag, leanchecker, and audit coverage of `Upstream/` (M7). I did not rebuild the library: no `lake build` was run, by design.
- **Statistics**: none reported, so this part of the review is skipped.

## Limitations of this review

The moduli-stack statements (folder 146) and the set theory of draft 307 need a specialist. Kleiman 1968 and 1994, Cisinski 2006, Maltsiniotis 2005, Mumford 1965 and Williams 1969 could not be read through the permitted sources, so their theorem numbers are unchecked. The Lean library was not rebuilt; CI status was read from GitHub. The repository changes by the hour: these figures are for e9b4ad6.

## Recommendation

**Major revision.** Accept as a project paper once the following are done:
- M1–M3: one snapshot, a title and count that match the attribution rule, and a reconciled list of errors on the page.
- M4: folder 146 restated with its hypotheses and with the literature attributed precisely.
- M5 and M6: the PR count and the AI declaration corrected.

The artefact and the honesty about limits are strong. The required changes are textual, and need no new proofs.

# Confidential comments to editor

## Reviewer disclosures

- Conflicts and editor clearance: this is a self-review requested by the author, so not an independent review.
- Competence limits or specialist review needed: moduli stacks (folder 146); set theory (Bourbaki draft 307).
- Assistance or tools used and required disclosure: prepared with Claude (Anthropic) at the author's request. Crossref, arXiv, GitHub and HEAD requests were used for checks; Semantic Scholar was rate-limited.
- Confidentiality or retention issue: none. The material is public.

## Editorial-process or integrity concerns

None beyond the AI-declaration completeness issue (M6), which is raised with the authors above.
