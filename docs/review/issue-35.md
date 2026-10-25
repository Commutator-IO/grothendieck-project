Everything below can be settled by someone who reads **French handwriting of 1950–1990 and knows how an archive is filed**, with the facsimile open beside the reading — no mathematics needed. It is the part of the human check that does not wait for a geometer. Each item says where to look; the reading opens beside Montpellier's facsimile at `https://grothendieck.commutator.io/#<folder>/<batch>`.

**How to record a check.** Correct the transcription at source (`transcripts/<folder>/batch-NN.fr.tex`), with a `\note{}` saying who checked what and when. A register entry (`src/content/letters.json`, `src/content/dated-leaves.json`) is corrected in place, and its `where` line kept. Declare a batch `checked` in `transcripts/status.json` only after the *whole* batch has been compared — ink and mathematics — which this issue does not do; a partial check is a note, not a status.

---

## 1. The unread words in his prose — 39,473 `\ill{}`

Of the 40,469 words the first passes left illegible, **39,473 are in running French**, outside any formula (996 are inside one). These are the ones a reader of the hand, not of the mathematics, can recover — and the `\uncertain{}` readings with them: **26,917 doubtful readings in prose**, 507 inside formulas. The page *The hand* ([/hand/](https://grothendieck.commutator.io/hand/)) sorts every folder by its share of unread words.

Densest batches, prose `\ill{}` only:

- [x] 1 batch 5 — 719 · batch 2 — 572 · batch 4 — 548 — reviewed 2026-10-04: heavy crossings-out and struck text are on the page; nothing to correct
- [x] 58 batch 1 — 689 · batch 2 — 570 — sampled on the facsimile by Michel Hua, 2026-10-20 (#61, 04126b3): batch 1 p. 4 « on partira d'une partie finie »; batch 2 p. 24 « utilisant » confirmed, p. 34 « $i = n-1, n$ » (#61: still illegible: batch 1 p. 8, two places, and p. 18); (#74, c1e339c): batch 2 p. 29 « des résultats » and « n'est plus supposé propre », p. 32 « pour tt voisinage ouvert » (#74: still illegible: batch 1 p. 14); (#77, 8e4d1e0): batch 2 p. 30 « développement systématiques de certains théorèmes du type de « Lefschetz » »
- [x] 154 batch 3 — 686 · batch 2 — 507 — sampled on the facsimile by Michel Hua, 2026-10-20 (#61, af4b11e): batch 3 p. 41 « tiré » confirmed, p. 44 « en termes », p. 45 « les systèmes affines correspondant »; batch 2 p. 37 « en modifiant un peu la définition » (#61: still illegible: batch 2 pp. 24, 30, 33); (#74, 8391fe7): batch 3 p. 49 « il faut et suffit … que les sommets s' antipodiques de s », batch 2 p. 22 « ainsi que deux autres qui se correspondent » (#74: still illegible: batch 3 p. 57)
- [x] 62 batch 1 — 532 — sampled on the facsimile by Michel Hua, 2026-10-20 (#61, 9c8a671): p. 3 « d'équations … », p. 6 the illegible word is struck out; (#70, 0387974): p. 12 « pour », p. 15 « et en supposant que $sx=-x$, » and « qui ici ne fait qu'exprimer que les solutions »
- [x] 161-2 batch 3 — 472 — sampled on the facsimile by Michel Hua, 2026-10-20 (#74, 1d21dd2): p. 45 « ce sont les éléments de » (the line runs on further) and « modulaire » confirmed, p. 48 « schémas ayant une car > 0 », p. 55 « famille génératrice ont … » (approximate) (#74: can't tell: p. 46 « comme »)
- [x] 10 batch 9 — 448 — sampled on the facsimile by Michel Hua, 2026-10-20 (#74, 46bd7d9): p. 161 « si » confirmed but probably struck, p. 167 « automorphisme » confirmed, p. 172 « … voisinage de … », p. 176 « d'un « groupe de représentation » » (#74: still illegible: p. 165)
- [x] 101 batch 2 — 427 — sampled on the facsimile by Michel Hua, 2026-10-20 (#70, 5434c20): p. 24 the doubtful « car » is not on the page; p. 28 no word, only a space; p. 35 « l'expression » (or « l'expansion »), still doubtful; p. 39 « donc (lemme) il est injectif » (#70: still illegible: p. 33)
- [x] 98 batch 2 — 410 — sampled on the facsimile by Michel Hua, 2026-10-20 (#63, 3163b7a): p. 23 « donc » confirmed (#63: still doubtful: p. 37 « sait »); (#70, 0ffb0b1): p. 28 « cohérents », p. 34 « [lemme] », p. 36 « choisit »

Rule: a word is filled in only where the ink supports it. `references/lexicon.md` narrows the candidates; it never settles one.

## 2. His insertions and the transcriber's — the `\add` / `\supplied` residue

The macro that used to carry both senses was split by a rule on the file, not by a reading (238f80a): **529** uses glued to the word they complete became `\supplied{}` (ours), **5,615** standing free stayed `\add{}` (his). Both errors of the rule are ink questions:

- [x] a free-standing `\add{}` that is in fact a supply — « = » expanded to « même », a parenthesis restored at a clipped edge, a word the page never had → make it `\supplied{}` — sampled on the facsimile by Michel Hua, 2026-10-20 (#63): seven free-standing insertions (7 p. 69, 34 p. 2, 74 p. 3, 84 p. 54, 145 p. 11, 156-1 p. 15, 161-2 p. 10) are all his; none is a supply; (#70, 79bcfbc): 125 batch 1 p. 3 « de » is not on the page, now `\supplied{}`; (#75, 48c0afb): 121 batch 2 p. 33 « des » is his
- [x] a glued `\supplied{}` that is in fact his — an inserted prefix such as `\add{quasi-}torseur` → make it `\add{}` — sampled 2026-10-20 (#63, a272a52): 6 batch 1 p. 1 « R- » before « préschémas » is his, now `\add{}`; (#70–71): 82 batch 3 p. 48 and 121 batch 1 p. 15 « sous- » are his, now `\add{}` (2aed13b, 0ba7bf3); 6 p. 8, 10 p. 60, 31 p. 15 are typed corrections, now plain text (57dd7f4, a9d6cc0, 0cd5a93); 55 p. 8 the « c » is not on the page (e942fae); 154 p. 87 confirmed a supply (#71: can't tell: 137 batch 2 p. 22); (#75): 5 p. 22, 76 p. 35, 89 p. 6, 123 p. 4, 148 p. 66, 161-2 p. 6 are his, now `\add{}` (f44a22b, 5662f2f, 2063bc6, e951704, 35ac131, 1d21dd2); 9 p. 11 is a typed correction, now plain text (861e99e); 29 p. 119 confirmed a supply; (#77): 6 p. 21 « bi- », 43 p. 26 « Y- », 81 p. 50 « R_1- », 121 p. 71 « C_*- » are his, now `\add{}` (a585685, 43347cb, a5d533c, ebed4f9); 161-2 p. 7 the page has « Δ-fonctions », the « Δ- » his, now `\add{}` (5254757)
- [x] on the sixteen typescript batches where `\add{}` marks **his ink on a typed page** by declared convention (headers of 10 batches 2–4, 27 batch 1, 29 batches 5–6, 31 batch 2, 36 batch 1, 103 batch 1, 111 batch 1, 162-5 batch 3, among others): confirm the ink is his and not a typist's correction — sampled 2026-10-04: **27** batch 1 pp. 2-6 is a typist's ink (now plain text, 629df20); **36** batch 1 p. 2 pencil is his (05cf860); **135** Sính typescript ink is his (1633dd7); **111/162-5** « Tapis de Quillen » ink is his (d7b8a92). The other typescript batches keep the declared convention.

## 3. Dates written on the leaves — 160 records

`src/content/dated-leaves.json` ([/timeline/](https://grothendieck.commutator.io/timeline/)): 59 dates in his hand, 33 typed, 47 machine stamps, the rest other or unknown. All were read by a model from the transcriptions, not from the pages. Worst first:

- [x] **page not settled** — 154 batch 6: the 9 and 18 August 1982 banners among pp. 101, 102, 111, and 16–17 August 1982 among pp. 109, 116, 120 (recorded as ranges); 148 batch 1: three circulars of 14, 18 and 20 October 1983 over pp. 5–15; 67 « 11-08-82 » (pp. 47–50); 154 p. 5 or p. 7 for the 16 August 1982 banner; 100 p. 37, « Harvard University, Oct. 27, 1963 » — settled on the facsimile by Michel Hua, 2026-10-20 (#75): the 18 October 1983 circular of 148 is on p. 9 (35ac131), and for « 11-08-82 » in 67 the reader can't tell; (#77): the 16 August 1982 banner of 154 is on p. 5 (3e765a9); for 100 p. 37 the reader can't tell
- [x] **ambiguous readings** — 105 « 06/09/82 » (day/month order); 107 « 06/04/82 » read as 4 June; 7 p. 20 « Nov. Déc. 196? » read 1966; 7 p. 35 « ?5.11.66 » read as the 15th; 16 p. 47 « 6.1.1966 » against p. 43 « 4.1.67 »; 67 p. 1 « (1978 ou 77 ?) » — checked on the facsimile by Michel Hua, 2026-10-20 (#77): all six as recorded — 105 6 September 1982, 107 4 June 1982, 7 p. 20 November–December 1966, 7 p. 35 the 15th, 16 p. 47 6 January 1966, 67 p. 1 1976
- [x] **years taken from a neighbouring leaf** (12 records) — the day-only dates of 154 (24.12, 25.12), 67 (12.1, 13.1, from 11.1.84), and 156-1, 156-2, 156-3, 156-5 (June 1986) — checked on the facsimile by Michel Hua, 2026-10-20 (#77–78): no year on the leaves themselves; 154 inferred from the run dated « 23.12.83 » (p. 11); 67 from « 11.1.84 » on p. 53 (p. 54 of Montpellier's PDF); 156-1, 156-2, 156-3, 156-5 from the chapter heading on each folder's p. 1 (p. 2 of the PDF: « (Juin 86) », « (Juin 86) », « (8 Juin 86) », « (14.6.86) »)
- [x] **dates the transcriber paraphrased rather than quoted** — 12 p. 116; 29 p. 149; 71 pp. 3, 14; 108 p. 3 verso; 116 p. 10; 122 p. 17; 141 pp. 2, 4, 6; 148 pp. 21, 29; 151 pp. 3, 5, 7; 154 batches 5–9; 158 pp. 38, 40 — checked on the facsimile by Michel Hua, 2026-10-20 (#75–76): 12, 29, 71, 108, 116, 122, 151, 154 p. 99, 158 as recorded; 141 « Montpellier, le 12 Novembre 1980 »; 148 p. 21 « 10.32.40 AM 09 JUN 82 »; 154 p. 136 « 08/19/82-15:20:31 », p. 160 « 16 Aug 82 »
- [x] **labels, not datings?** — 101 « Notes antiques 1958 »; 29 « Compléments SGA / 1960 »; 118 « 1976 » with « Poèmes »; 120 pencil « 1978 »; 162-5 cover « (1968) », perhaps not his hand; 75 « 1977-78 » — all six labels or titles, not dates of writing (#76; 75: the title of the course given in 1977-78): now kind « label » in dated-leaves.json, left out of the Timeline; 101's proposed dating now rests on his later attribution (ecf02ca)
- [ ] **his hand or not** — every record's `hand` field: « his », « typed », « machine », « other »

## 4. The letters — 44 records, 42 letters

`src/content/letters.json` ([/letters/](https://grothendieck.commutator.io/letters/)). For each: the date as written, the direction (from him, to him), the form (typed, handwritten, carbon, draft), the language, and whether the writer is a public figure — which decides whether they are named.

- [x] **109 pp. 9–10** — an English blurb for *Pursuing Stacks* from an unnamed writer, filed as a letter — entry confirmed on the facsimile (#63)
- [x] **12 p. 116** — a typed administrative note of 27 March 1968; the date is the transcriber's paraphrase — entry confirmed on the facsimile (#63)
- [x] **23 pp. 52–53** — a carbon postscript in his voice, addressee unnamed — entry confirmed on the facsimile (#63)
- [x] **27 p. 30, 29 p. 149, 80 pp. 21–29, 97 p. 16** — writer or addressee unidentified; 80 is photocopies of an autobiographical letter in German — checked on the facsimile (#63): 27, 80 and 97 confirmed; 29 p. 149 is a letter to Grothendieck (a79e65d)
- [x] **100 p. 39** — a letter to Dieudonné whose writer is not stated — entry confirmed on the facsimile (#63)
- [x] **121 pp. 29–36** — a draft to A'Campo, perhaps the inventory's « lettre (1974) », undated — not a letter: working notes (#64, 1676595); taken out of the register
- [x] **121 p. 66** — the cancelled opening of a draft to Fujii Guruji — entry confirmed on the facsimile (#64)
- [x] **45** — the correspondent is « A. Delzant » as the page has it; first name unconfirmed — entry confirmed on the facsimile (#64)
- [x] **75** — a letter to the Minister of Education, the minister not named — entry confirmed on the facsimile (#64)
- [x] the inventory lists letters the transcriptions did not find: **1** « lettre (1953) », **73** « lettre (s.d.) », **121** « lettre (1974) » — none of the three found on the facsimile by Michel Hua, 2026-10-20 (#64; cd6cf6a, b6e1c11, 1676595)
- [x] ten records leave the correspondent unnamed as a private person — confirm that none of them is in fact a public figure, and that no named one is private

## 5. What was left out — 1,187 pages

The 130 folders begun count 6,142 pages in the inventory; **4,955** were transcribed. The other 1,187 were skipped by rule as carrying no mathematics: administrative versos, blank sheets, other people's paper.

- [ ] spot-check the skips: a page skipped as « no mathematics » that carries a calculation, a verso that continues its recto, a page skipped as illegible that is only upside down
- [x] the two batches declared `skipped` in `transcripts/status.json`, **31 #6** and **131 #3** — confirm they hold nothing to transcribe — confirmed 2026-10-04: both are the back of another duplicated typescript, upside down (0696dd7)
- [ ] others' typescripts and mémoires are summarised, his marks on them given in full — check that no mark of his was taken for the typist's, and none of theirs for his

## 6. The pages the articles quote

- [x] **19 batch 1, p. 8** — quoted whole in the jTEI article (#33), §4.5 and Appendix A. Read against the facsimile by Michel Hua on 2026-10-03 (two corrections) and 2026-10-15 (two more: « λ_i est » struck; « deux des indices i, j, k consécutifs ») — ea86e67. Still doubtful: the verb « ne montrent que » and the word after « l'identité, ». The article's « needed two corrections » (Appendix A) is to be updated at revision.
- [ ] the quotations of the Revue d'histoire des mathématiques article, once drafted (#34)

---

Not in this issue: whether a formula, an index or an arrow is right. That needs a reader of the mathematics as well as of the hand, and is the rest of the human check.


## Documents read against another transcription, then the facsimile (October 2026)

Ten documents of the fonds also exist in a transcription made elsewhere. Each difference between the two was settled on the facsimile by Michel Hua, and only those decisions were applied, recorded in the file's `% Revised` line. The other transcription served only to find the differences.

- [x] **103 pp. 16–17**: letter to Deligne, Giraud and Verdier, 23.6.1974. 11 differences, 2 changes (c9f53db)
- [x] **44 pp. 7–8**: letter to Serre, 12.8.1964. 5 differences, 2 changes (959dd23)
- [x] **5 pp. 49–52**: letter to Deligne, 10.12.1965. 13 differences, 1 change (cfc6367)
- [x] **16 pp. 43–46**: letter to Coates, 4.1.1967. 7 differences, no change
- [x] **16 pp. 47–49**: letter to Coates, 6.1.1966. 5 differences, 3 changes (301d80a)
- [x] **91 pp. 30–31**: letter to Anantharaman, 11.9.1967. 7 differences, 2 changes (2392385)
- [x] **66 pp. 1–4**: Travaux de thèses, 1964. 11 differences, 9 changes (24c42f9)
- [x] **75 pp. 30–32**: the two course announcements of 1977/78. 4 differences, no change
- [x] **69 p. 83**: announcement of the 1976 DEUG course on regular polyhedra — transcribed in full; the three letters 𝔖 are his hand, added in the blanks of the typing (Michel Hua on the facsimile, 2026-10-15; d09f4a4)
- [ ] **12**: Motifs. The other text cannot be extracted as text, so it has to be read as images (24 pages against 9 batches)






---

# Moved from #48 (2026-10-18)


### 1. Folder 12 (*Motifs*) against a transcription made elsewhere

Eight of the ten documents that also exist in an independent transcription have been settled on the facsimile (#35): 23 readings corrected and 4 illegible passages resolved. Folder 12 is left. The other transcription runs to 24 pages, and its PDF has no usable text layer, so it can only be read as images. It is to be compared with our 9 batches.

- [ ] Read the 24 pages of the other transcription against `transcripts/12/batch-0{1..9}.fr.tex`, listing the differences and the `\ill{}` it resolves.
- [ ] Settle each difference on the facsimile, then apply the decisions with a `% Revised` line, as for the other documents. The other transcription is not cited or named.

### 2. Agents' own arguments and references in the eight new modernised readings

The readings of 43, 103, 105, 107, 109, 111, 118 and 150 (3 October) footnote departures from the pages. Some footnotes carry arguments of the edition's own and references given from memory. Each is marked as such, but none has been checked.

**Arguments of the edition's own, to check:**
- [x] **107, p. 24:** the answer to « Ask Ronnie Brown! » is no in general, the obstruction being Milnor's lim¹. The counterexample is circles under degree-d maps with Y = K(ℤ,2).
- [ ] **107, p. 13:** the Proposition is corrected with π₀ exponents; it holds for connected L′, M′.
- [ ] **107, p. 20:** a path-fibration counterexample over S¹.
- [ ] **109, p. 14:** groupoids do not form a topos (via the subobjects of ℤ/3). Also (Ord) is a modelizer.
- [ ] **118, pp. 32–35:** the lemma on total asphericity is restated as what its proof gives.
- [ ] **118, p. 22:** the counterexample needs a group with non-zero abelianisation, not only π₁ ≠ 1.
- [ ] **103, p. 5:** the Picard envelope is strict when 2 = 0 in A. On p. 13, the cone is functorial with functorial injective resolutions.
- [ ] **105, p. 26:** a counterexample to the saturation question. Also the converses of W7 bis / W8 bis fail for W∞.
- [ ] **111, pp. 3, 4, 8, 16:** counterexamples K(ℤ/p,2), acyclic groups, loop functor not faithful, ℝP¹ in ℝP².
- [ ] **43:** about twenty corrections of the page (p. 3 units, p. 41 H²(π,ℤ) = ℚ/ℤ, p. 79 the pro-generalised Jacobian…). They are listed in the agent's report and in the file's header.
- [ ] **150, p. 19:** the equivalence holds only under strict compatibility. On p. 68, the dimension argument needs manifold-like Σ_i.

**References cited from memory, to confirm:**
- [x] Saavedra (LNM 265), SGA 4 XVIII, Deligne 1987, Breen (Astérisque 225), Illusie (LNM 283), Laplaza 1972 (103) — checked against zbMATH/Crossref and, where a place is cited, the text (bibliographic check, Opus 5.5, 2026-10-21).
- [x] Cisinski 2006, Quillen–Illusie, Thomason (109, 105, 118) — checked against zbMATH/Crossref and, where a place is cited, the text (bibliographic check, Opus 5.5, 2026-10-21).
- [x] Rezk 1998, Street 1974, Dwyer 1980, Brown 1973 (118) — checked against zbMATH/Crossref and, where a place is cited, the text (bibliographic check, Opus 5.5, 2026-10-21).
- [x] Siebenmann 1972, Quinn 1988, Mather 1970, Verona, Brasselet–Hector–Saralegi, Ayala–Francis–Tanaka (150) — checked against zbMATH/Crossref and, where a place is cited, the text (bibliographic check, Opus 5.5, 2026-10-21); Verona, Brasselet–Hector–Saralegi and Ayala–Francis–Tanaka are not cited in the reading.
- [x] Gabriel–Ulmer, Joyal–Tierney, Bousfield–Friedlander, Smith/Beke (105)

**Consistency between readings:**
- [x] **103 / 135:** same Sính typescript. 103 corrects « isomorphisme de catégories » to an equivalence and adds the groupoid hypothesis for K⁰/K¹; 135 does not. Revise 135. — transcriptions aligned 2026-10-04: the ink on the typescript is his in both (1633dd7). The modernised reading of 135 still to revise on the « équivalence » and groupoid points.
- [x] **111 / 162-5:** same « Tapis de Quillen ». 111 attributes the handwritten additions to him on the transcription's sampled check, 162-5 does not. Align them. — settled 2026-10-04 on the facsimile: his hand; both files now say so (d7b8a92).

None of these makes a batch `checked`. They are checks of the modernised readings, which the transcription governs.







# Hypotheses behind « shown false as stated » (#90, 2026-10-25)

### Is the refuted statement on the page as read?

Three findings say a statement of his is false as stated, by a counterexample of the edition's own, and a fourth (57) rests on a hypothesis read into an illegible word because without it a counterexample applies. Before these verdicts stand, the hypotheses have to be read on the facsimile: a missed or misread hypothesis would make the counterexample beside the point.

- [ ] **114, pp. 3–5:** Proposition 4 as read: for a basic localizer W satisfying Loc 4), totally W∞-aspherical ⟺ totally W-aspherical ⟺ non-empty with a × b 0-connected. Check that no further hypothesis on A or W is written (a test category, connections, W ⊆ W₀, a word before « namely »), since the category of cubes □ satisfies the last condition without being totally W∞-aspherical.
- [ ] **18, pp. 35, 37:** the boxed chain of p. 35 as read: f_∞ = 1 ⟺ all periods real ⟺ « M est engendré par ℚ(−2n) » ⟺ G ≃ G_m or {e}; and the Remarque of p. 37: f_∞ = id_M forces M to be a sum of tensor powers of ℚ(2). Check whether the margin of p. 35 (« engendré par ℚ tordu et par ℚ(2) ») names the sign-twisted Tate motive ℚ(−1) ⊗ ε, which would mean the page saw the correction, and whether « directe » on p. 37 is right.
- [ ] **42, pp. 1–2, 6:** the theorem of p. 2 as read: p : S_{0/S} → R_{/S} fully faithful on all S-preschemes locally of finite type over a locally noetherian S, and Corollaire 3 of p. 6. Check that neither the statement nor the definitions of p. 1 restrict Y (separated, quasi-compact, « de type fini » rather than « localement de type fini »), since the counterexample uses a non-quasi-compact, non-separated Y.
- [ ] **57, pp. 45–46:** the Théorème de rigidité of p. 45 as read: « G un schéma en groupes \add{\ill{}} de type fini sur S », the added word taken as « comm. » (commutative), as in Corollaire 1 of p. 46 (« G, H deux schémas en groupes comm. »). Check the added word: without « commutatif » the theorem fails, since the diagonal torus of GL₂ over 𝔸¹ and its conjugate by (1 t ; 0 1) are rigid, equal at t = 0 and different elsewhere.
