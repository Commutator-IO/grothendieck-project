# Referee report: the Lean appendix (« Annexe. Énoncés des lectures modernisées démontrés »)

Working draft, 2026-10-24/25. The author asked for this read-only review. Michel Hua is the accountable human and should check every point before acting on it.

**Line numbers** refer to a snapshot of the working tree taken on 2026-10-24 at 18:40, while another agent was revising the prose. Search by the quoted phrase if a line has moved.

## 0. Intake and scope

- **Material.** `docs/lean/article.tex`, `recapitulatif.tex`, `annexe-nonverifies.tex` and `sections/**/*.tex` (295 pages compiled). The Lean sources are `lean/Grothendieck/*.lean` at HEAD (`ce1e06e`), at the tag `article-lean-2026-10` (`c0379d0`, 2026-10-24 11:16) and in the working tree.
- **Authorization.** The author requested the review; the material is public (GitHub repository, PDF on the site).
- **Peer-review skill intake validator.** It returns `EXTERNAL_SERVICE_NOT_SUPPORTED`. That is a truthful declaration: the session is hosted, and bibliographic metadata was sent to Crossref and arXiv. The gate exists to protect confidential manuscripts, which this is not.
- **Skipped parts of the peer-review skill.** Reporting-guideline selection (CONSORT and the like), statistics, clinical ethics and the statistical-reproducibility audit do not apply to a formalisation appendix.
- **Replacing them.** Formal reproducibility: links, tag, sorry/axiom hygiene. Claim–evidence: French statement against Lean statement.
- **Competence limits.** Theorem numbers in cited works were checked against arXiv versions only. The fidelity of the readings to the manuscript pages is out of scope; the article says so itself.
- **Skill lint.** `lint_review.py` flags the missing author/editor channel headings. They do not apply: there is no editor, and this report goes to the author only.
- **AI disclosure.** This review was drafted by Claude (Opus 5.5) with three sub-agents, so the reviewer and the author's proof-writing model are the same family. A human mathematician should spot-check the major issues.

## 1. What the appendix claims

For 72 shelfmarks of the Montpellier fonds and two Bourbaki rédactions, the appendix restates in French statements taken from the modernised readings. It proves them along a Lean 4/mathlib proof cited in a footnote. It also reports superfluous hypotheses, counterexamples, and corrections to the reading or to the page, and lists what remains unproved (144 `\nonverifie` marks in an annex).

Central claims to evaluate:
1. Each statement labelled as proved is a faithful French rendering of a Lean theorem with no hidden hypothesis.
2. The verdict table (`recapitulatif.tex`) summarises the sections correctly.
3. Attribution: « Grothendieck, page N » appears only where the page states the result.
4. The counts are right: 72 shelfmarks; 48/5/19 partition; 40 pistes proved in full, 50 in part; and the README's 2,119 theorems.
5. The links point to the code that was verified.

## 2. Overall assessment

**Assessment: the mathematics needs minor revision, the bookkeeping moderate revision.** There is no editor here, so this is advice to the author, not a decision.

**The formal core holds up.**
- In a sample of 20 sections, 156 claims were checked against the Lean files. All 156 match.
- Every named theorem exists, and no Lean statement carries a hypothesis absent from the French. Where the proof works in a model or an encoding, the prose says so.
- No sampled file contains `sorry`, `admit`, an extra axiom or `native_decide`.
- Across all 72 sections, 295 Lean names quoted in `\texttt{}` were checked for existence. Only three are missing at the ref their section links to (§3.1, M1).

**The problems are in the apparatus.**
- **Release drift.** The tag the article links to predates a third of the day's work.
- **Counts disagree.** The introduction, the summary table and the *Bilan* give incompatible figures.
- **Attribution.** About a dozen boxed statements carry Grothendieck's name although the edition supplied the form stated.
- **Bibliography.** Two metadata errors and one wrong pointer (see the citation report).

None of these affects a proof, but each would cost a careful reader trust.

## 3. Major issues

### M1. The tag `article-lean-2026-10` does not represent the article

**Links that fail at the tag.**
- `\leanblob` points to the tag (article.tex:46–47), but the tag was cut at 11:16 and the PDF compiled at 17:46.
- At the tag there are 67 Folder files, not 72. Folder43, 63, 80, 90 and 156_4 exist only on `main`. Their sections and summary-table rows correctly use `\verifie[\leanblobmain]`.
- Nine tag-linked files changed after the tag: Folder2, 21, 22, 46, 79, 93, 104, 113, 160.
- Two sections cite declarations that **do not exist at the tag** they link to:
  - 22.tex:125: `incl`, `proj`, `no_derivation_mv`. This is the « troisième piste de la cote 22 » the introduction counts.
  - 46.tex:62: `mul_smul_sum_twist`, `isCohomologous_of_map`, `injective`. This is the « seconde piste de la cote 46 », the injectivity.
- `Folder93.lean` has +241 uncommitted lines in the working tree, and `sections/93.tex` is also modified.

**Fix.** Before release, commit, cut a new tag at the commit the PDF is built from (for instance `article-lean-2026-10b`), point `\leanref` at it, and drop `\leanblobmain` (every file would then be at the tag). Otherwise, switch 22 and 46 to `\leanblobmain` now.

### M2. The introduction, the summary table and the *Bilan* contradict each other

**Pistes proved in full.**
- Introduction (article.tex:129): « Quarante pistes sont démontrées ». This checks out: the list sums to 40, and the partial list to 50.
- *Bilan* (reste.tex:9): « Les trente-quatre pistes démontrées ».

**Errors on the page.**
- *Bilan* (reste.tex:7): « Deux erreurs sont sur la page elle-même, toutes deux dans la cote 19 ».
- The summary table gives « faux sur la page » for 19, 80, 90, 150, 156-4, 160 and Bourbaki 457.
- The introduction (article.tex:117) names 63, 80, 90 and 156-4 as the counterexamples among the « dix-neuf dernières ». The table gives 63 as « glose fausse » and 150 as « faux sur la page ». So 63 and 150 are swapped between the two lists, and 160 is missing.
- The *Bilan* predates the additions of 63, 80, 90 and 156-4 (committed today).

**Pistes not treated.** *Bilan*, reste.tex:3: « Quinze autres parties … quatre-vingt-treize pistes ». The snapshot has 16 `autres/*.tex` files with 96 distinct `\piste` ids.

**The 48/5/19 partition (article.tex:117).**
- The partition says the 19 are shelfmarks whose proved statement is « un lemme de la lecture ou une correction ».
- Yet 39, 104 and 158 have pistes proved in full (article.tex:129), and 21, 22 and 153 have pistes proved in part.
- Thirteen sections outside the 48 carry a `\piste`: 21, 22, 39, 41, 42, 80, 90, 104, 125, 150, 153, 158, 161-1.
- The five « détachés » (16, 19, 106, 114, 161-2) also carry pistes proved in full: 16 ×2, 19 ×2, 106.

**Fix.**
- Regenerate the *Bilan* figures from the same source as the introduction: the `\piste` occurrences and the proofs.ts verdicts.
- Restate the partition as « the proved statement *includes* a piste » (which would make 54 + 5 + 13), or drop it in favour of the table.
- Make the counterexample list match the table (see M3).

### M3. Summary-table verdicts disagree with their sections

The verdicts are generated from `src/content/proofs.ts`, so the fixes belong there; then rerun `node docs/lean/recapitulatif.mjs`.

| Shelfmark | Table says | Section shows | Severity |
|---|---|---|---|
| 44 (recapitulatif.tex:33) | confirmé tel que lu | the reading's claim is false: the three axioms alone do not give integral Cartan numbers | moderate |
| 63 (:35) | correction de la lecture (glose fausse) | the page's own argument at p. 99 fails (63.tex:22); the introduction counts it as a counterexample | moderate |
| 118 (:96) | confirmé tel que lu | also refutes the page's « visiblement stable par sommes » (118.tex:62) | moderate |
| 153 (:53) | plus général | the piste box is `\nonverifie` (153.tex:203, nv:69); the introduction lists 153 as partial | moderate |
| 158 (:97) | glose fausse | also shows the p. 52 corollary false as stated (158.tex:75, :105) and refutes the struck uniqueness claim of p. 44 | moderate |
| 19 (:44) | faux sur la page | Th. 1.12 a), sufficiency in b), the matrix and the adjoint chains are confirmed; should read « partiel ; faux sur la page » | minor |
| 16 (:15) | partiel | also refutes the reading's Φ₀ ring over **Z** (16.tex:98) | minor |
| 156-4 (:110) | faux sur la page | p. 68 says only « Je présume »; « conjecture de la page réfutée » is more exact | minor |

### M4. Attribution: « Grothendieck, page N » on statements whose form is the edition's

The rule (memory `lean-article-attribution`; article.tex:131–133): the name goes only on what the page states. Each item below was checked against the box text, the section's own remarks and the Findings `ours` field.

| Location | Label | Why it breaks the rule | Suggested label |
|---|---|---|---|
| 73.tex:95 | « Grothendieck, pages 23 à 27, Proposition, **forme corrigée par l'édition** » | A corrected form is by definition the edition's | « D'après les pages 23 à 27 (Proposition), forme corrigée par l'édition » |
| 73.tex:72 | « Grothendieck, pages 15, 18 et 28, critère du cas spécial II » | `ours`: the « il faut et il suffit » is `\uncertain`, the « paire de directions » form is the edition's restatement, the proof is entirely the edition's | « D'après les pages 15, 18 et 28, sous la forme de l'édition » |
| 72.tex:50 | « Grothendieck, pages 96 à 100 et 102 » | `ours`: « the classification as stated is the reading's consequence … the page never puts the two together » | « D'après les pages 96 à 102 » |
| 85.tex:193 | « Grothendieck, pages 4 à 7, modules des représentations de G₂ » | `ours`: the moduli-space reformulation (representability by an open of 𝔸²_**Z**) is the edition's, and condition c) is the reading's interpretation | « D'après les pages 4 à 7, reformulation de l'édition » |
| 146.tex:107 | « Grothendieck, page 70, colonne n = 5, pour L_i, valeur suivie de « ? » » | The page only guesses (« 12 ? »). By article.tex:133 that is a conjecture of the page, proved by the edition (orders computed 2026-10-21 per `ours`) | « Conjecture de la page 70 (« 12 ? »), démontrée par l'édition » |
| 80.tex:39–40 | « Grothendieck, pages 24 et 26, cas latticiel » | Per `ours`, reading condition b) as « n'est pas l'arrangement simple II₄ » is the edition's; the footnote does not say so | « D'après les pages 24 et 26, b) lu par l'édition » |
| 90.tex:40 | « Grothendieck, pages 13 à 23 » (non vérifié) | `ours`: the formula F′, the « plus petit sous-module stable » reading and the hypotheses of 3) are the reading's; the page never proves 3) | Keep his name for 1)–2) only, or « D'après les pages 13 à 23, forme précisée par la lecture » |
| 120.tex:47 | « Grothendieck, pages 10 à 13 » | `ours`: the reading restored the conclusion of p. 13 and the proof is the edition's (the text after the box says so) | Add « conclusion restituée par la lecture » |
| 115.tex:5 | « … la dualité d'Isbell comme cas particulier » | The folder never names Isbell; the names 𝒪/Spec are the reading's | « la dualité (dite d'Isbell) » |
| 11.tex:54 | corollary under his name | The χ case (struck on the page) and the pointed blocks come from the reading. The working tree now reads « et la table de l'édition », which may already address this. | Check |
| 16.tex:21 | « Page 16, le commutateur » | The Lean docstring calls the formula the editor's computation from (6.7) | « Énoncé de l'édition, d'après (6.7) » |
| 161-2.tex:71 | « Grothendieck, pages 47 à 49 » (non vérifié) | The note under the box says the gluing criterion is a brouillon « mis en forme par l'édition » | « D'après les pages 47 à 49 » for the criterion |

**Borderline cases** (the under-box note already discloses the edition's share): autres/schemas-en-groupes…:19 (Grothendieck–Springer, H¹ condition from the margin) and :47 (condition (ii) restored), and 39.tex:55 (box hypotheses (I),(S),(R),(H), whereas the page claims (H) alone).

### M5. Pistes whose Findings status is no longer « candidate » or « unsearched »

**The definition.** article.tex:129 defines a piste as « candidate » or « unsearched ».

**What the Findings tab says.** Eight `\piste` anchors point to Findings entries whose status is `matched` (found in the literature) or `confirmed`:
- 16-algebraic-iso-suffices (16.tex:207)
- 77-odd-rank-half-discriminant (77.tex:7)
- 79-homothety-distance-three (79.tex:126, :153; Singerman–Strudwick Th. 9)
- 84-two-regular-triplet-classification (84.tex:9, :148)
- 84-product-quadratic-algebras-formula (84.tex:40)
- 31-phi-specialisation-criterion (vide/cohomologie-etale-et-l-adique.tex:10)
- 118-groupoid-products-not-totally-aspherical (118.tex:7, `confirmed`)

Some of these are counted among the 40 and 50 proved pistes.

**Fix.** Either drop the diamond on matched entries (or give them a different mark), or widen the definition and recount.

## 4. Minor issues

**Proof pointers**
1. **`\general` lines name Upstream files the proof does not import.**
   - 16.tex:219–227: `SubalgebraIsUnitOfIsIntegral`. `Folder16.inverse_mem_of_charpoly` inverts directly; the prose argues « par l'énoncé général ».
   - 19.tex:78–84: `MonadicityIff`. `beck_iff` is proved locally in Folder19.
   - The Folder21 version at the tag does not use the Upstream file its `\general` names.
2. **Small fidelity caveats; all verdicts still « matched ».**
   - **Bourbaki 457:** « entière et séparable » (filtered union of finite étale subalgebras) is deduced from a root-of-monic-separable-split-polynomial statement, through an equivalence that is not formalised.
   - **153:** the Pólya formula c_k = (Δ^k P)(0) is in Upstream `eq_sum_fwdDiff_iter_smul_choose`, not in the statement of `polya`.
   - **120.tex:35:** « X/Y est un espace modéré au sens strict » is not in Lean.
   - **156-4:** « treillis complet orthocomplémenté » is proved piece by piece, and `cosuppH` is not linked to `cosupp`.
   - **115.tex:24:** `isbellO_yoneda`, called « le lemme », is a `def`.

**Wording and pointers**

3. **Abstract (article.tex:106).** « Elle se clôt sur la liste des énoncés de ces cotes qui ne sont pas démontrés ». The annex lists the 144 `\nonverifie` marks. It does not list the conjectures or the « Ne sont pas démontrés ici » paragraphs. Say « des énoncés rapportés comme théorèmes et non vérifiés ».
4. **Page numbers.** The Folder16 docstrings disagree with the tex: Lean says p. 16 where the tex says p. 9 (16.tex:17) and p. 13 (16.tex:25).
5. **Indices.** 1.tex:190 writes ∏_{i≤n} while the rest of the section uses zero-indexed ∏_{i<n}. In section 11, k names both the base ring and the number of factors.
6. **The partial-piste list (article.tex:129).** « une quatrième de la cote~77 » sits between three items about cote 1 and reads as a fourth piste of cote 1. Reorder by shelfmark.
7. **Section 21.** The Lean proof of Prop. 2.15 goes through `Ideal.injective_of_primaryComponent_eq_top`, not the Artin–Rees route the text writes out. Add one sentence.

**Style**

8. **French style (memory `article-french-style`).** One « Ce que les pages visent, … » turn at 93.tex:288.
9. **Notation is mixed across the volume, sometimes within a paragraph.**
   - **Z**: `\mathbb Z` 97× against `\mathbf Z` 243× (article.tex:129 has both).
   - **G**: `\mathbb G` 22× against `\mathbf G` 11×.
   - **Q**: `\mathbb Q` 26× against `\mathbf Q` 77×.
   - **P**: `\mathbb P` 2× against `\mathbf P` 48×.
   - `\leqslant` 49× against `\leq` 299×.
   - Pick one per symbol.
10. **Small typos.**
    - Double spaces: 19.tex:142, 78.tex:80–82.
    - A space before `\footnote`: 146.tex:246, :255.
    - English abbreviations in French prose: « i.e. » at 2.tex:47 (inside a quotation of the page, which is acceptable), « etc. » at bourbaki-457.tex:56.

## 5. Claim–evidence matrix (20 sections sampled)

| Section | Claims checked | Matched | Notes |
|---|---|---|---|
| 1 | 12 | 12 | index style (minor 5) |
| 11 | 5 | 5 | attribution M4 |
| 16 | 12 | 12 | `\general` unused; table M3; attribution M4 |
| 19 | 12 | 12 | `\general` unused; table M3 |
| 21 | 4 | 4 | proof route (minor 7) |
| 37 | 5 | 5 | — |
| 44 | 3 | 3 | table M3 |
| 50 | 5 | 5 | — |
| 63 | 1 (three parts) | 1 | linked to main, correctly; table M3 |
| 80 | 2 | 2 | linked to main, correctly; attribution M4 |
| 90 | 1 | 1 | linked to main, correctly; attribution M4 |
| 101 | 3 | 3 | — |
| 115 | 6 | 6 | attribution M4; `def` called a lemma |
| 118 | 12 | 12 | table M3; MathOverflow vs « communication personnelle » |
| 120 | 6 | 6 | attribution M4; one clause not in Lean |
| 146 | 42 (7 statements + 35 names) | 42 | attribution M4; citation issues (Edidin–Hu, Arsie–Vistoli) |
| 153 | 16 | 16 | table M3 |
| 156-4 | 2 | 2 | linked to main, correctly; table M3 (minor) |
| 158 | 6 | 6 | table M3 |
| Bourbaki 457 | 1 | 1 | unformalised equivalence (minor 2) |
| **Total** | **156** | **156** | 0 unfaithful statements, 0 hidden hypotheses, 0 sorry/axiom |

**Outside the sample** (automated over all sections):
- All 295 quoted Lean names were checked.
- Three names are declared only after the tag their section links to (M1).
- The other non-hits are mathlib names (`IsCompact`, `Algebra.TensorProduct.lmul'`, …) or regex artefacts (names ending in a prime).
- All 231 distinct `\piste` ids exist in `src/content/findings.ts`.
- `\nonverifie` marks (144) equal the annex rows (144).
- The three `\lie` statements (four diamonds, in 19, 21 and 125) match « Trois énoncés le portent ».
- Four empty parts and two `\ailleurs` lines, as stated.

## 6. Counts and counting rules

| Claim | Where | Repository | Verdict |
|---|---|---|---|
| 72 shelfmarks | abstract, introduction, README:344, :399 | 72 `sections/<cote>.tex`; 72 `Folder*.lean` at HEAD; **67 at the tag** | true at HEAD, false at the linked tag (M1) |
| 48 + 5 + 19 = 72 | article.tex:117 | the lists sum correctly; the definitions clash with the pistes (M2) | inconsistent |
| 40 pistes in full, 50 in part | article.tex:129 | the lists sum to 40 and 50; the *Bilan* says 34 | inconsistent (M2) |
| « Quinze autres parties … 93 pistes » | reste.tex:3 | 16 `autres` files, 96 distinct pistes (8 in the empty parts) | stale |
| 2,119 theorems | README.md:400, rule `cat lean/Grothendieck/*.lean \| grep -c '^theorem'` | **2,119 at HEAD** (reproduces). Working tree: 2,134, because the untracked `Scratch46.lean`/`ScratchB.lean` match the glob. **2,052 at the tag.** | reproducible at HEAD only |

**What the rule counts.** The rule is non-recursive, so it excludes the 26 Upstream files (116 theorem/lemma declarations). It counts only lines beginning with `theorem`. It leaves out 285 column-0 `lemma`s, 9 `private`/`protected` declarations, and about 55 declarations with attributes or indentation. Counted with comments stripped, Folder and Bourbaki files have **2,468** `theorem`/`lemma` declarations at HEAD.

**Suggestions.**
- State the rule as « déclarations `theorem` en début de ligne » or switch to all theorem/lemma declarations.
- Count at the release tag.
- Keep `Scratch*.lean` out of `lean/Grothendieck/`, or the README rule will drift.

**Lines** (the article states no line count): 40,667 lines in the 74 Folder/Bourbaki files at HEAD (40,908 in the working tree, which includes the uncommitted Folder93 lines); 3,448 in Upstream; 39,562 + 3,448 at the tag.

## 7. Links

- All 96 distinct GitHub targets (`\verifie`, `\general`, table) return HTTP 200 at their linked ref.
- All main-linked files are absent from the tag. That is consistent: none is linked to main without need.
- The tag is pushed (`refs/tags/article-lean-2026-10` = `ab0f0f6`, an annotated tag on `c0379d0`).
- The site URLs return 200: `/timeline/`, `/findings/`, `/article/grothendieck-lean.pdf`. `\lot` anchors are hash routes, so HTTP status cannot validate them, and they were not validated beyond the base URL.

## 8. Clarity, pedagogy, consistency

**What works.**
- The sections that were read closely (146, 1, 19, 118) do what the memory `lean-article-pedagogical` asks. They give context from the leaf, conventions first, then the statement, a short proof in plain French, then what Lean contains and what it does not.
- The figure in 146 (fixed points of 𝔖₃ on M_{0,4}) is a good model of intuition before computation.
- Each section's paragraph saying what the Lean proof does and does not contain is the best part of the apparatus.

**What hinders.**
- The introduction is front-heavy. Paragraph article.tex:129 runs to about 1,000 words and lists all 50 partial pistes inline. Move that list into the summary table: add a « piste » column with full/partial and the restriction. Keep a two-sentence summary in the introduction.
- The *Bilan* (reste.tex) is a narrative that has fallen behind the sections (M2). It is better generated, or reduced to pointers into the table.
- Box labels have grown long: « Grothendieck, pages 26 et 28, noyau des différentielles, dans la spécialisation de la page 28 ». Put the restriction in the first sentence of the box and keep the label to source and page.
- Notation and typography are covered in minor 9–10.

## 9. Requested actions, in priority order

1. Re-tag at the release commit and repoint `\leanref`. At the least, switch 22 and 46 to main (M1).
2. Bring the introduction, the *Bilan* and the summary table to one set of numbers, generated from one source (M2, M3).
3. Relabel the attribution cases in M4.
4. Decide what the diamond means for matched or confirmed Findings entries (M5).
5. Bibliography fixes (citation report): `ega4-1` pages; `friedmanlaza` published; the Mackall pointer; the dropped hypotheses for Gabber–Orgogozo Th. 6.1, Mathew Prop. 4.5 and Topaz; Edidin–Hu's field hypothesis and generator; MathOverflow instead of « communication personnelle »; DOIs throughout or not at all; `riehlverity2022` uncited.
6. Minor items in §4.
