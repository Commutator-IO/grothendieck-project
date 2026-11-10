# Issue 66 — spot checks of the skipped pages (machine pre-check)

Status: complete — 61 sampled pages looked at on the facsimile (51 no, 6 yes, 4 cannot tell, 0 not done). Sections: 1 population, 2 sampling method, 3 table, 4 review lines (sections 2–4 follow the population table).

## 1. Population

How it was built (script: computations/issue-66-skipped/pop.py, output computations/issue-66-skipped/pop.json). The skill records a skip by absence: « a gap in the page numbers is the record ». So for every transcripts/<cote>/batch-NN.fr.tex the page range was read from the header (« pages A-B »), and every page of that range with no \page{N} marker in the body is counted as not transcribed. The reason is taken from the header comment sentence that names the page (alone, in a list or in a range) and sorted into a class by keyword; the class is a machine sorting of free prose and is wrong in places (a clause naming several pages with different reasons, a cover whose words were in fact carried as a heading). « gap only » means that no header sentence names the page. Covers inscribed in his hand are in the population because they take no \page marker, although their words are normally carried as a \section heading.

Total: **1928 pages without a \page marker**, in 140 folders, 465 batch files (of 639 batch files read).

| reason class | pages |
|---|---|
| others' typescript | 689 |
| blank | 623 |
| cover/wrapper | 190 |
| gap only (no header mention) | 162 |
| printed/published | 90 |
| skipped, reason not classifiable | 60 |
| administrative | 53 |
| unrelated | 18 |
| duplicate | 18 |
| illegible | 13 |
| verso (unspecified) | 12 |

### Full population

| cote | page | reason class | header wording | file:line |
|---|---|---|---|---|
| 1 | 1 | blank | Page 1 is blank and absent. | transcripts/1/batch-01.fr.tex:10 |
| 1 | 36 | blank | Page 36 is blank and absent. | transcripts/1/batch-02.fr.tex:9 |
| 1 | 42 | blank | Pages 42 and 46 are blank and absent. | transcripts/1/batch-03.fr.tex:9 |
| 1 | 46 | blank | Pages 42 and 46 are blank and absent. | transcripts/1/batch-03.fr.tex:9 |
| 1 | 105 | blank | page 105 is blank. \page{} numbers the position in the folder, as batches 1 to 5 did: the archivists' pencil numbers run two ahead, so page … | transcripts/1/batch-06.fr.tex:9 |
| 1 | 122 | blank | pages 122 and 140 are blank. | transcripts/1/batch-07.fr.tex:9 |
| 1 | 140 | blank | pages 122 and 140 are blank. | transcripts/1/batch-07.fr.tex:9 |
| 2 | 1 | gap only (no header mention) |  | transcripts/2/batch-01.fr.tex:1 |
| 2 | 5 | blank | page 5 (blank) | transcripts/2/batch-01.fr.tex:34 |
| 2 | 8 | gap only (no header mention) |  | transcripts/2/batch-01.fr.tex:1 |
| 2 | 10 | others' typescript | pages 10, 12 and 14 (a typescript that is not his | transcripts/2/batch-01.fr.tex:34 |
| 2 | 12 | others' typescript | pages 10, 12 and 14 (a typescript that is not his | transcripts/2/batch-01.fr.tex:34 |
| 2 | 14 | others' typescript | pages 10, 12 and 14 (a typescript that is not his | transcripts/2/batch-01.fr.tex:34 |
| 2 | 19 | gap only (no header mention) |  | transcripts/2/batch-01.fr.tex:1 |
| 2 | 23 | others' typescript | pages 23, 25, 33, 35 and 38 (typescripts that are not his and do not carry mathematics in his hand — 33 and 35 carry only line-by-line corre… | transcripts/2/batch-02.fr.tex:59 |
| 2 | 25 | others' typescript | pages 23, 25, 33, 35 and 38 (typescripts that are not his and do not carry mathematics in his hand — 33 and 35 carry only line-by-line corre… | transcripts/2/batch-02.fr.tex:59 |
| 2 | 26 | blank | pages 26 and 30 (blank leaves). | transcripts/2/batch-02.fr.tex:59 |
| 2 | 30 | blank | pages 26 and 30 (blank leaves). | transcripts/2/batch-02.fr.tex:59 |
| 2 | 31 | blank | Pages 31 and 39 are otherwise blank sheets inscribed in his hand naming the runs that follow: they get no \page, and their words are the sec… | transcripts/2/batch-02.fr.tex:62 |
| 2 | 33 | others' typescript | pages 23, 25, 33, 35 and 38 (typescripts that are not his and do not carry mathematics in his hand — 33 and 35 carry only line-by-line corre… | transcripts/2/batch-02.fr.tex:59 |
| 2 | 35 | others' typescript | pages 23, 25, 33, 35 and 38 (typescripts that are not his and do not carry mathematics in his hand — 33 and 35 carry only line-by-line corre… | transcripts/2/batch-02.fr.tex:59 |
| 2 | 38 | others' typescript | pages 23, 25, 33, 35 and 38 (typescripts that are not his and do not carry mathematics in his hand — 33 and 35 carry only line-by-line corre… | transcripts/2/batch-02.fr.tex:59 |
| 2 | 39 | blank | Pages 31 and 39 are otherwise blank sheets inscribed in his hand naming the runs that follow: they get no \page, and their words are the sec… | transcripts/2/batch-02.fr.tex:62 |
| 5 | 1 | blank | Page 1 is a blank tan wrapper (only the show-through of page 2) and gets no \page. | transcripts/5/batch-01.fr.tex:13 |
| 5 | 3 | others' typescript | page 3 (typescript, not his) | transcripts/5/batch-01.fr.tex:36 |
| 5 | 9 | others' typescript | page 9 (typescript, not his) | transcripts/5/batch-01.fr.tex:36 |
| 5 | 11 | others' typescript | page 11 (typescript, not his) | transcripts/5/batch-01.fr.tex:36 |
| 5 | 13 | others' typescript | page 13 (a list of page-and-line corrections to a typescript, in his hand, but not mathematics in hand). | transcripts/5/batch-01.fr.tex:36 |
| 5 | 14 | cover/wrapper | Page 14 is a tan cover in his hand, "Frobenius", for the run that follows | transcripts/5/batch-01.fr.tex:26 |
| 5 | 20 | cover/wrapper | Page 20 is a second tan cover in his hand naming the run that begins in batch 2 | transcripts/5/batch-01.fr.tex:31 |
| 5 | 33 | unrelated | Pages 33, 35, 37 and 39 carry no mathematics of his and are absent. | transcripts/5/batch-02.fr.tex:29 |
| 5 | 35 | unrelated | Pages 33, 35, 37 and 39 carry no mathematics of his and are absent. | transcripts/5/batch-02.fr.tex:29 |
| 5 | 37 | unrelated | Pages 33, 35, 37 and 39 carry no mathematics of his and are absent. | transcripts/5/batch-02.fr.tex:29 |
| 5 | 39 | unrelated | Pages 33, 35, 37 and 39 carry no mathematics of his and are absent. | transcripts/5/batch-02.fr.tex:29 |
| 5 | 41 | others' typescript | page 41, a typescript (a course announcement and a seminar programme) scanned upside down, nothing in his hand | transcripts/5/batch-03.fr.tex:49 |
| 5 | 43 | others' typescript | page 43, a typescript on Banach categories and Spin(p,q), nothing in his hand. | transcripts/5/batch-03.fr.tex:49 |
| 5 | 48 | blank | Page 48 is an otherwise blank leaf carrying, in his hand, « lettre à Deligne / sur coh. p-adique »: the cover of the letter that follows, an… | transcripts/5/batch-03.fr.tex:34 |
| 6 | 2 | blank | Pages skipped: 2, the blank verso of the first leaf (only the printed letterhead of the Istituto Matematico of Pisa and show-through | transcripts/6/batch-01.fr.tex:20 |
| 6 | 32 | cover/wrapper | Pages skipped (no \page): 32, 37, 39 — covers, whose words are carried as section headings. | transcripts/6/batch-02.fr.tex:49 |
| 6 | 37 | cover/wrapper | Pages skipped (no \page): 32, 37, 39 — covers, whose words are carried as section headings. | transcripts/6/batch-02.fr.tex:49 |
| 6 | 39 | cover/wrapper | Pages skipped (no \page): 32, 37, 39 — covers, whose words are carried as section headings. | transcripts/6/batch-02.fr.tex:49 |
| 6 | 41 | others' typescript | Pages skipped (no \page): 41, 43, 45 (foreign typescript, unrelated) | transcripts/6/batch-03.fr.tex:69 |
| 6 | 43 | others' typescript | Pages skipped (no \page): 41, 43, 45 (foreign typescript, unrelated) | transcripts/6/batch-03.fr.tex:69 |
| 6 | 45 | others' typescript | Pages skipped (no \page): 41, 43, 45 (foreign typescript, unrelated) | transcripts/6/batch-03.fr.tex:69 |
| 6 | 46 | cover/wrapper | 46 and 51 (covers, carried as headings) | transcripts/6/batch-03.fr.tex:69 |
| 6 | 51 | cover/wrapper | 46 and 51 (covers, carried as headings) | transcripts/6/batch-03.fr.tex:69 |
| 6 | 57 | blank | - Page 57: blank. | transcripts/6/batch-03.fr.tex:57 |
| 6 | 63 | illegible | Pages skipped (no \page): 63, a leaf with nothing of his — only the show-through of p. 64 (no ink of its own, checked at raised contrast) | transcripts/6/batch-04.fr.tex:33 |
| 6 | 66 | blank | 66, a blank sheet (printed letterhead only, nothing written). | transcripts/6/batch-04.fr.tex:35 |
| 7 | 1 | blank | Pages skipped: 1 and 19, blank cream sheets carrying nothing but show-through from the neighbouring leaves (no word of his on either). | transcripts/7/batch-01.fr.tex:18 |
| 7 | 19 | blank | Pages skipped: 1 and 19, blank cream sheets carrying nothing but show-through from the neighbouring leaves (no word of his on either). | transcripts/7/batch-01.fr.tex:18 |
| 8 | 2 | others' typescript | Pages skipped: 2, an upside-down typed leaf in English (p. 132, « §24. | transcripts/8/batch-01.fr.tex:17 |
| 8 | 18 | others' typescript | 18, a Bourbaki « Tribu n° 66 » (« Décisions sur l'intégration »), nothing in his hand | transcripts/8/batch-01.fr.tex:18 |
| 8 | 20 | others' typescript | 20, a faded typed leaf « - 65 - » on holomorphic functions (Schwarz's lemma), nothing in his hand. | transcripts/8/batch-01.fr.tex:18 |
| 8 | 22 | others' typescript | Pages skipped: 22, an upside-down typed leaf « - 53 - » on the variation of the amplitude of z along a path (complex analysis), nothing in h… | transcripts/8/batch-02.fr.tex:17 |
| 8 | 23 | blank | 23, 27 and 32, blank cream sheets carrying only show-through from the neighbouring leaves | transcripts/8/batch-02.fr.tex:19 |
| 8 | 27 | blank | 23, 27 and 32, blank cream sheets carrying only show-through from the neighbouring leaves | transcripts/8/batch-02.fr.tex:19 |
| 8 | 32 | blank | 23, 27 and 32, blank cream sheets carrying only show-through from the neighbouring leaves | transcripts/8/batch-02.fr.tex:19 |
| 8 | 34 | others' typescript | 34, 36, 38 and 40, upside-down typed leaves « n° 382 » (pp. 81-84, jets and fibrations of C^r manifolds, §7.1-7.2), nothing in his hand (the… | transcripts/8/batch-02.fr.tex:19 |
| 8 | 36 | others' typescript | 34, 36, 38 and 40, upside-down typed leaves « n° 382 » (pp. 81-84, jets and fibrations of C^r manifolds, §7.1-7.2), nothing in his hand (the… | transcripts/8/batch-02.fr.tex:19 |
| 8 | 38 | others' typescript | 34, 36, 38 and 40, upside-down typed leaves « n° 382 » (pp. 81-84, jets and fibrations of C^r manifolds, §7.1-7.2), nothing in his hand (the… | transcripts/8/batch-02.fr.tex:19 |
| 8 | 40 | others' typescript | 34, 36, 38 and 40, upside-down typed leaves « n° 382 » (pp. 81-84, jets and fibrations of C^r manifolds, §7.1-7.2), nothing in his hand (the… | transcripts/8/batch-02.fr.tex:19 |
| 8 | 42 | others' typescript | Pages skipped: 42, 44, 46, 48, 50, 52, 54 and 56, typed leaves « n° 382 » (pp. 79, 78, 77, 76, 73, 43, 42, 40 of a stencilled text on C^r ma… | transcripts/8/batch-03.fr.tex:17 |
| 8 | 44 | others' typescript | Pages skipped: 42, 44, 46, 48, 50, 52, 54 and 56, typed leaves « n° 382 » (pp. 79, 78, 77, 76, 73, 43, 42, 40 of a stencilled text on C^r ma… | transcripts/8/batch-03.fr.tex:17 |
| 8 | 46 | others' typescript | Pages skipped: 42, 44, 46, 48, 50, 52, 54 and 56, typed leaves « n° 382 » (pp. 79, 78, 77, 76, 73, 43, 42, 40 of a stencilled text on C^r ma… | transcripts/8/batch-03.fr.tex:17 |
| 8 | 48 | others' typescript | Pages skipped: 42, 44, 46, 48, 50, 52, 54 and 56, typed leaves « n° 382 » (pp. 79, 78, 77, 76, 73, 43, 42, 40 of a stencilled text on C^r ma… | transcripts/8/batch-03.fr.tex:17 |
| 8 | 50 | others' typescript | Pages skipped: 42, 44, 46, 48, 50, 52, 54 and 56, typed leaves « n° 382 » (pp. 79, 78, 77, 76, 73, 43, 42, 40 of a stencilled text on C^r ma… | transcripts/8/batch-03.fr.tex:17 |
| 8 | 52 | others' typescript | Pages skipped: 42, 44, 46, 48, 50, 52, 54 and 56, typed leaves « n° 382 » (pp. 79, 78, 77, 76, 73, 43, 42, 40 of a stencilled text on C^r ma… | transcripts/8/batch-03.fr.tex:17 |
| 8 | 54 | others' typescript | Pages skipped: 42, 44, 46, 48, 50, 52, 54 and 56, typed leaves « n° 382 » (pp. 79, 78, 77, 76, 73, 43, 42, 40 of a stencilled text on C^r ma… | transcripts/8/batch-03.fr.tex:17 |
| 8 | 56 | others' typescript | Pages skipped: 42, 44, 46, 48, 50, 52, 54 and 56, typed leaves « n° 382 » (pp. 79, 78, 77, 76, 73, 43, 42, 40 of a stencilled text on C^r ma… | transcripts/8/batch-03.fr.tex:17 |
| 8 | 63 | others' typescript | Pages given as typescript, one French \note each with the hand-made interventions in full, the typed text not re-set: 61, 63, 65, 67, 69, 73… | transcripts/8/batch-04.fr.tex:24 |
| 8 | 71 | others' typescript | Pages skipped: 71 and 75, stencilled leaves « n° 397 » (pp. - 35 - and - 33 - of a text on measures, convolution and L^p spaces, Hölder's in… | transcripts/8/batch-04.fr.tex:17 |
| 8 | 75 | others' typescript | Pages skipped: 71 and 75, stencilled leaves « n° 397 » (pp. - 35 - and - 33 - of a text on measures, convolution and L^p spaces, Hölder's in… | transcripts/8/batch-04.fr.tex:17 |
| 8 | 76 | blank | 76, blank. | transcripts/8/batch-04.fr.tex:17 |
| 9 | 1 | cover/wrapper | page 1 (buff card), « Dualité des modules de Dieudonné de gpes de B.T. duals l'un de l'autre ..... | transcripts/9/batch-01.fr.tex:26 |
| 9 | 3 | administrative | Pages skipped: 3, a sheet of Pisa letterhead (Università di Pisa, Istituto Matematico « Leonida Tonelli ») carrying nothing but show-through | transcripts/9/batch-01.fr.tex:20 |
| 9 | 5 | administrative | 5, a leaf of the same letterhead with a list of Italian phrases and a street sketch, no mathematics. | transcripts/9/batch-01.fr.tex:20 |
| 9 | 9 | gap only (no header mention) |  | transcripts/9/batch-01.fr.tex:1 |
| 9 | 14 | others' typescript | 2026-10-20 — readings checked on the facsimile by Michel Hua (#74–76): p. 11, « sous- » before « groupe d'inertie » is on the page, a correc… | transcripts/9/batch-01.fr.tex:14 |
| 10 | 1 | cover/wrapper | Pages 1-16 are one continuous draft in blue ink, opened by a cover sheet inscribed « Polarisations sur les ⊗-catégories graduées » (page 1, … | transcripts/10/batch-01.fr.tex:9 |
| 10 | 2 | blank | Page 2 is the back of the cover, page 17 a blank leaf, page 19 a blank leaf with one struck line upside down at its foot — all three absent. | transcripts/10/batch-01.fr.tex:40 |
| 10 | 17 | blank | Page 2 is the back of the cover, page 17 a blank leaf, page 19 a blank leaf with one struck line upside down at its foot — all three absent. | transcripts/10/batch-01.fr.tex:40 |
| 10 | 19 | blank | Page 2 is the back of the cover, page 17 a blank leaf, page 19 a blank leaf with one struck line upside down at its foot — all three absent. | transcripts/10/batch-01.fr.tex:40 |
| 10 | 21 | blank | Page 21 is a near-blank leaf with one struck line at its head, page 31 a blank leaf — both absent. | transcripts/10/batch-02.fr.tex:61 |
| 10 | 31 | blank | Page 21 is a near-blank leaf with one struck line at its head, page 31 a blank leaf — both absent. | transcripts/10/batch-02.fr.tex:61 |
| 10 | 58 | blank | Page 58, the blank verso of page 59 where only its frappe shows through, is absent. | transcripts/10/batch-03.fr.tex:75 |
| 10 | 84 | blank | Pages 84, 91, 93 and 100 are blank and are absent. | transcripts/10/batch-05.fr.tex:116 |
| 10 | 87 | cover/wrapper | Pages 88-98, « Filtration des foncteurs fibres » (his cover, page 87), his own hand throughout, paginated 1 to ... in his own numbering (88 … | transcripts/10/batch-05.fr.tex:60 |
| 10 | 91 | blank | Pages 84, 91, 93 and 100 are blank and are absent. | transcripts/10/batch-05.fr.tex:116 |
| 10 | 93 | blank | Pages 84, 91, 93 and 100 are blank and are absent. | transcripts/10/batch-05.fr.tex:116 |
| 10 | 99 | cover/wrapper | Page 99 is a cover sheet in his hand, « Notes Saavedra », naming a run that begins after this batch | transcripts/10/batch-05.fr.tex:113 |
| 10 | 100 | blank | Pages 84, 91, 93 and 100 are blank and are absent. | transcripts/10/batch-05.fr.tex:116 |
| 10 | 109 | skipped, reason not classifiable | Pages 109 and 113 carry nothing: they are absent from what follows. | transcripts/10/batch-06.fr.tex:94 |
| 10 | 113 | skipped, reason not classifiable | Pages 109 and 113 carry nothing: they are absent from what follows. | transcripts/10/batch-06.fr.tex:94 |
| 10 | 137 | blank | Page 137 is the blank verso of 136. | transcripts/10/batch-07.fr.tex:13 |
| 10 | 140 | cover/wrapper | Page 140 is a brown folder cover inscribed by him, naming the run that begins after this batch. | transcripts/10/batch-07.fr.tex:15 |
| 10 | 141 | blank | Page 141 is blank. | transcripts/10/batch-08.fr.tex:11 |
| 10 | 155 | blank | Page 155 is blank. | transcripts/10/batch-08.fr.tex:16 |
| 11 | 1 | blank | Ten leaves in his hand (the even pages 2-20), written on the backs of a typescript in English on geometric invariant theory: the nine odd pa… | transcripts/11/batch-01.fr.tex:14 |
| 11 | 3 | blank | Ten leaves in his hand (the even pages 2-20), written on the backs of a typescript in English on geometric invariant theory: the nine odd pa… | transcripts/11/batch-01.fr.tex:14 |
| 11 | 5 | blank | Ten leaves in his hand (the even pages 2-20), written on the backs of a typescript in English on geometric invariant theory: the nine odd pa… | transcripts/11/batch-01.fr.tex:14 |
| 11 | 7 | blank | Ten leaves in his hand (the even pages 2-20), written on the backs of a typescript in English on geometric invariant theory: the nine odd pa… | transcripts/11/batch-01.fr.tex:14 |
| 11 | 9 | blank | Ten leaves in his hand (the even pages 2-20), written on the backs of a typescript in English on geometric invariant theory: the nine odd pa… | transcripts/11/batch-01.fr.tex:14 |
| 11 | 11 | blank | Ten leaves in his hand (the even pages 2-20), written on the backs of a typescript in English on geometric invariant theory: the nine odd pa… | transcripts/11/batch-01.fr.tex:14 |
| 11 | 13 | blank | Ten leaves in his hand (the even pages 2-20), written on the backs of a typescript in English on geometric invariant theory: the nine odd pa… | transcripts/11/batch-01.fr.tex:14 |
| 11 | 15 | blank | Ten leaves in his hand (the even pages 2-20), written on the backs of a typescript in English on geometric invariant theory: the nine odd pa… | transcripts/11/batch-01.fr.tex:14 |
| 11 | 17 | blank | Ten leaves in his hand (the even pages 2-20), written on the backs of a typescript in English on geometric invariant theory: the nine odd pa… | transcripts/11/batch-01.fr.tex:14 |
| 11 | 19 | blank | Ten leaves in his hand (the even pages 2-20), written on the backs of a typescript in English on geometric invariant theory: the nine odd pa… | transcripts/11/batch-01.fr.tex:14 |
| 11 | 21 | blank | Pages 21, 23, 25, 27, 29, 31, 34, 36, 38 and 40 are pages of an unrelated English typescript (several scanned upside down) and page 32 is a … | transcripts/11/batch-02.fr.tex:15 |
| 11 | 23 | blank | Pages 21, 23, 25, 27, 29, 31, 34, 36, 38 and 40 are pages of an unrelated English typescript (several scanned upside down) and page 32 is a … | transcripts/11/batch-02.fr.tex:15 |
| 11 | 25 | blank | Pages 21, 23, 25, 27, 29, 31, 34, 36, 38 and 40 are pages of an unrelated English typescript (several scanned upside down) and page 32 is a … | transcripts/11/batch-02.fr.tex:15 |
| 11 | 27 | blank | Pages 21, 23, 25, 27, 29, 31, 34, 36, 38 and 40 are pages of an unrelated English typescript (several scanned upside down) and page 32 is a … | transcripts/11/batch-02.fr.tex:15 |
| 11 | 29 | blank | Pages 21, 23, 25, 27, 29, 31, 34, 36, 38 and 40 are pages of an unrelated English typescript (several scanned upside down) and page 32 is a … | transcripts/11/batch-02.fr.tex:15 |
| 11 | 31 | blank | Pages 21, 23, 25, 27, 29, 31, 34, 36, 38 and 40 are pages of an unrelated English typescript (several scanned upside down) and page 32 is a … | transcripts/11/batch-02.fr.tex:15 |
| 11 | 32 | blank | Pages 21, 23, 25, 27, 29, 31, 34, 36, 38 and 40 are pages of an unrelated English typescript (several scanned upside down) and page 32 is a … | transcripts/11/batch-02.fr.tex:15 |
| 11 | 34 | blank | Pages 21, 23, 25, 27, 29, 31, 34, 36, 38 and 40 are pages of an unrelated English typescript (several scanned upside down) and page 32 is a … | transcripts/11/batch-02.fr.tex:15 |
| 11 | 36 | blank | Pages 21, 23, 25, 27, 29, 31, 34, 36, 38 and 40 are pages of an unrelated English typescript (several scanned upside down) and page 32 is a … | transcripts/11/batch-02.fr.tex:15 |
| 11 | 38 | blank | Pages 21, 23, 25, 27, 29, 31, 34, 36, 38 and 40 are pages of an unrelated English typescript (several scanned upside down) and page 32 is a … | transcripts/11/batch-02.fr.tex:15 |
| 11 | 40 | blank | Pages 21, 23, 25, 27, 29, 31, 34, 36, 38 and 40 are pages of an unrelated English typescript (several scanned upside down) and page 32 is a … | transcripts/11/batch-02.fr.tex:15 |
| 11 | 42 | others' typescript | The others are skipped: 42, 44, 46, 48, 51, 53, 55 and 57 are the backs of an English typescript that has nothing to do with these notes, an… | transcripts/11/batch-03.fr.tex:21 |
| 11 | 44 | others' typescript | The others are skipped: 42, 44, 46, 48, 51, 53, 55 and 57 are the backs of an English typescript that has nothing to do with these notes, an… | transcripts/11/batch-03.fr.tex:21 |
| 11 | 46 | others' typescript | The others are skipped: 42, 44, 46, 48, 51, 53, 55 and 57 are the backs of an English typescript that has nothing to do with these notes, an… | transcripts/11/batch-03.fr.tex:21 |
| 11 | 48 | others' typescript | The others are skipped: 42, 44, 46, 48, 51, 53, 55 and 57 are the backs of an English typescript that has nothing to do with these notes, an… | transcripts/11/batch-03.fr.tex:21 |
| 11 | 49 | others' typescript | The others are skipped: 42, 44, 46, 48, 51, 53, 55 and 57 are the backs of an English typescript that has nothing to do with these notes, an… | transcripts/11/batch-03.fr.tex:21 |
| 11 | 51 | others' typescript | The others are skipped: 42, 44, 46, 48, 51, 53, 55 and 57 are the backs of an English typescript that has nothing to do with these notes, an… | transcripts/11/batch-03.fr.tex:21 |
| 11 | 53 | others' typescript | The others are skipped: 42, 44, 46, 48, 51, 53, 55 and 57 are the backs of an English typescript that has nothing to do with these notes, an… | transcripts/11/batch-03.fr.tex:21 |
| 11 | 55 | others' typescript | The others are skipped: 42, 44, 46, 48, 51, 53, 55 and 57 are the backs of an English typescript that has nothing to do with these notes, an… | transcripts/11/batch-03.fr.tex:21 |
| 11 | 57 | others' typescript | The others are skipped: 42, 44, 46, 48, 51, 53, 55 and 57 are the backs of an English typescript that has nothing to do with these notes, an… | transcripts/11/batch-03.fr.tex:21 |
| 12 | 10 | blank | page 10 is a blank letterhead sheet (absent) | transcripts/12/batch-01.fr.tex:13 |
| 12 | 19 | blank | Page 19 is blank (absent). | transcripts/12/batch-01.fr.tex:14 |
| 12 | 21 | others' typescript | Page 21 is a leaf of an unrelated typescript (a carbon on generic flatness, Ass F, « prop. 3 a) (ii) », struck through by one long stroke, n… | transcripts/12/batch-02.fr.tex:12 |
| 12 | 60 | others' typescript | Page 60 is the upside-down verso of an unrelated typescript (a few lines on a base change, cancelled by strokes, nothing in his hand) and is… | transcripts/12/batch-03.fr.tex:11 |
| 12 | 65 | others' typescript | Skipped: 65, 67, 69, 71, 80 — typescript of EGA (IV, § 7.5 on excellent rings and the conditions (i)-(viii), § 11.9, and a run of Propositio… | transcripts/12/batch-04.fr.tex:12 |
| 12 | 67 | others' typescript | Skipped: 65, 67, 69, 71, 80 — typescript of EGA (IV, § 7.5 on excellent rings and the conditions (i)-(viii), § 11.9, and a run of Propositio… | transcripts/12/batch-04.fr.tex:12 |
| 12 | 69 | others' typescript | Skipped: 65, 67, 69, 71, 80 — typescript of EGA (IV, § 7.5 on excellent rings and the conditions (i)-(viii), § 11.9, and a run of Propositio… | transcripts/12/batch-04.fr.tex:12 |
| 12 | 71 | others' typescript | Skipped: 65, 67, 69, 71, 80 — typescript of EGA (IV, § 7.5 on excellent rings and the conditions (i)-(viii), § 11.9, and a run of Propositio… | transcripts/12/batch-04.fr.tex:12 |
| 12 | 80 | others' typescript | Skipped: 65, 67, 69, 71, 80 — typescript of EGA (IV, § 7.5 on excellent rings and the conditions (i)-(viii), § 11.9, and a run of Propositio… | transcripts/12/batch-04.fr.tex:12 |
| 12 | 82 | skipped, reason not classifiable | 82, 84  Skipped. | transcripts/12/batch-05.fr.tex:19 |
| 12 | 84 | skipped, reason not classifiable | 82, 84  Skipped. | transcripts/12/batch-05.fr.tex:19 |
| 12 | 95 | cover/wrapper | 95      Cover in his hand, « Poids et niveaux d'espaces de cohomologie l-adiques (base var. quelconque) ». | transcripts/12/batch-05.fr.tex:47 |
| 12 | 102 | blank | 102, 109 Blank. | transcripts/12/batch-06.fr.tex:18 |
| 12 | 109 | blank | 102, 109 Blank. | transcripts/12/batch-06.fr.tex:18 |
| 12 | 116 | verso (unspecified) | The two skipped versos (116, 118) both carry March 1968 dates | transcripts/12/batch-06.fr.tex:59 |
| 12 | 118 | verso (unspecified) | The two skipped versos (116, 118) both carry March 1968 dates | transcripts/12/batch-06.fr.tex:59 |
| 12 | 123 | blank | 123      Blank. | transcripts/12/batch-07.fr.tex:50 |
| 12 | 125 | others' typescript | These are the rectos of leaves whose other sides are the odd pages 125-137 — a Bourbaki typescript (n° 383, groups generated by reflections)… | transcripts/12/batch-07.fr.tex:47 |
| 12 | 127 | others' typescript | These are the rectos of leaves whose other sides are the odd pages 125-137 — a Bourbaki typescript (n° 383, groups generated by reflections)… | transcripts/12/batch-07.fr.tex:47 |
| 12 | 129 | others' typescript | These are the rectos of leaves whose other sides are the odd pages 125-137 — a Bourbaki typescript (n° 383, groups generated by reflections)… | transcripts/12/batch-07.fr.tex:47 |
| 12 | 131 | others' typescript | These are the rectos of leaves whose other sides are the odd pages 125-137 — a Bourbaki typescript (n° 383, groups generated by reflections)… | transcripts/12/batch-07.fr.tex:47 |
| 12 | 133 | others' typescript | These are the rectos of leaves whose other sides are the odd pages 125-137 — a Bourbaki typescript (n° 383, groups generated by reflections)… | transcripts/12/batch-07.fr.tex:47 |
| 12 | 135 | others' typescript | These are the rectos of leaves whose other sides are the odd pages 125-137 — a Bourbaki typescript (n° 383, groups generated by reflections)… | transcripts/12/batch-07.fr.tex:47 |
| 12 | 137 | others' typescript | These are the rectos of leaves whose other sides are the odd pages 125-137 — a Bourbaki typescript (n° 383, groups generated by reflections)… | transcripts/12/batch-07.fr.tex:47 |
| 12 | 138 | printed/published | The batch file carries no cover sheet: PDF page N is page 120+N, as the Montpellier footer printed on each PDF page confirms, and the archiv… | transcripts/12/batch-07.fr.tex:4 |
| 12 | 142 | blank | 142     A cover: otherwise blank, bearing his title « Enveloppes pseudo-abéliennes de catégories multiplicatives (Constructions abstraites d… | transcripts/12/batch-08.fr.tex:18 |
| 12 | 159 | printed/published | The batch file carries no cover sheet: PDF page N is page 140+N, as the Montpellier footer printed on each PDF page confirms, and the archiv… | transcripts/12/batch-08.fr.tex:4 |
| 12 | 161 | printed/published | The batch file carries no cover sheet: PDF page N is page 160+N, as the Montpellier footer printed on each PDF page confirms, and the archiv… | transcripts/12/batch-09.fr.tex:4 |
| 12 | 163 | printed/published | The batch file carries no cover sheet: PDF page N is page 160+N, as the Montpellier footer printed on each PDF page confirms, and the archiv… | transcripts/12/batch-09.fr.tex:4 |
| 12 | 165 | printed/published | The batch file carries no cover sheet: PDF page N is page 160+N, as the Montpellier footer printed on each PDF page confirms, and the archiv… | transcripts/12/batch-09.fr.tex:4 |
| 12 | 167 | printed/published | The batch file carries no cover sheet: PDF page N is page 160+N, as the Montpellier footer printed on each PDF page confirms, and the archiv… | transcripts/12/batch-09.fr.tex:4 |
| 13 | 1 | blank | Page 1 is an otherwise blank leaf carrying, in his hand and underlined, « Groupe de Hodge » and « lettre à Mumford »: it is the wrapper for … | transcripts/13/batch-01.fr.tex:11 |
| 13 | 2 | blank | Page 2 is blank apart from the show-through of page 3 and gets no \page. | transcripts/13/batch-01.fr.tex:20 |
| 13 | 12 | blank | Page 12 is blank. | transcripts/13/batch-01.fr.tex:16 |
| 13 | 20 | cover/wrapper | Page 20 is a second cover in his hand, « Descriptions transcendantes de motifs en car. 0 … », naming the run that begins in batch 2 | transcripts/13/batch-01.fr.tex:21 |
| 13 | 21 | blank | Pages 21, 25, 32 and 35 are blank apart from show-through and get no \page{} | transcripts/13/batch-02.fr.tex:14 |
| 13 | 25 | blank | Pages 21, 25, 32 and 35 are blank apart from show-through and get no \page{} | transcripts/13/batch-02.fr.tex:14 |
| 13 | 32 | blank | Pages 21, 25, 32 and 35 are blank apart from show-through and get no \page{} | transcripts/13/batch-02.fr.tex:14 |
| 13 | 35 | blank | Pages 21, 25, 32 and 35 are blank apart from show-through and get no \page{} | transcripts/13/batch-02.fr.tex:14 |
| 13 | 44 | blank | Eleven leaves in his hand, of which ten carry mathematics (page 44 is blank and gets no \page{}). | transcripts/13/batch-03.fr.tex:12 |
| 14 | 1 | cover/wrapper | the pencilled numbers bottom-left ("1", "2", "4" ... "18", "20") read at the PDF page of the same number. | transcripts/14/batch-01.fr.tex:4 |
| 14 | 3 | others' typescript | Two short runs in his hand, each opened by a cover sheet he inscribed, written on the rectos of leaves whose versos are typescripts unrelate… | transcripts/14/batch-01.fr.tex:10 |
| 14 | 5 | others' typescript | Two short runs in his hand, each opened by a cover sheet he inscribed, written on the rectos of leaves whose versos are typescripts unrelate… | transcripts/14/batch-01.fr.tex:10 |
| 14 | 7 | others' typescript | Two short runs in his hand, each opened by a cover sheet he inscribed, written on the rectos of leaves whose versos are typescripts unrelate… | transcripts/14/batch-01.fr.tex:10 |
| 14 | 9 | others' typescript | Two short runs in his hand, each opened by a cover sheet he inscribed, written on the rectos of leaves whose versos are typescripts unrelate… | transcripts/14/batch-01.fr.tex:10 |
| 14 | 11 | others' typescript | Two short runs in his hand, each opened by a cover sheet he inscribed, written on the rectos of leaves whose versos are typescripts unrelate… | transcripts/14/batch-01.fr.tex:10 |
| 14 | 13 | others' typescript | Two short runs in his hand, each opened by a cover sheet he inscribed, written on the rectos of leaves whose versos are typescripts unrelate… | transcripts/14/batch-01.fr.tex:10 |
| 14 | 15 | others' typescript | Two short runs in his hand, each opened by a cover sheet he inscribed, written on the rectos of leaves whose versos are typescripts unrelate… | transcripts/14/batch-01.fr.tex:10 |
| 14 | 16 | cover/wrapper | p. 16   cover: « Équivalence d'Albanese et de Picard des cycles algébriques ». | transcripts/14/batch-01.fr.tex:41 |
| 14 | 17 | blank | Those versos carry no hand and are absent, as is the blank p. 17. | transcripts/14/batch-01.fr.tex:14 |
| 14 | 19 | others' typescript | a French typescript in blue, p. 19). | transcripts/14/batch-01.fr.tex:14 |
| 14 | 21 | others' typescript | page 21, a leaf of an unrelated typescript (a Bourbaki draft, « n° 391 », p. 14, on affine pseudo-reflections and Proposition 9 on orthogona… | transcripts/14/batch-02.fr.tex:11 |
| 14 | 22 | blank | page 22, blank | transcripts/14/batch-02.fr.tex:11 |
| 14 | 39 | blank | page 39, an otherwise blank sheet inscribed in his hand « Astuce de Tate sur les cycles décomposables » — a cover, whose words become the \s… | transcripts/14/batch-02.fr.tex:11 |
| 14 | 42 | others' typescript | Page 42 is a faint duplicate (carbon or show-through copy) of the letter's first leaf, page 43, with nothing in his hand: absent. | transcripts/14/batch-03.fr.tex:11 |
| 14 | 47 | cover/wrapper | Page 47 is a cover in his hand, « Sorites sur VA, Picard, Albanese ..... »: no \page, its words head the section that follows (hand.md, sect… | transcripts/14/batch-03.fr.tex:13 |
| 14 | 71 | blank | Skipped: 71 (blank | transcripts/14/batch-04.fr.tex:10 |
| 14 | 74 | others' typescript | 74 (an English typescript on Hopf algebra / coalgebra structures on K[t], page « 7 », scanned upside down) | transcripts/14/batch-04.fr.tex:10 |
| 14 | 76 | others' typescript | 76 and 78 (a French typescript on topos cohomology, pages « -20- » and « -25- », Corollaire 2.6 and Définition 3.5 on flasque sheaves | transcripts/14/batch-04.fr.tex:10 |
| 14 | 78 | others' typescript | 76 and 78 (a French typescript on topos cohomology, pages « -20- » and « -25- », Corollaire 2.6 and Définition 3.5 on flasque sheaves | transcripts/14/batch-04.fr.tex:10 |
| 14 | 81 | skipped, reason not classifiable | 81, 83, 85, 87, 89 Skipped. | transcripts/14/batch-05.fr.tex:15 |
| 14 | 83 | skipped, reason not classifiable | 81, 83, 85, 87, 89 Skipped. | transcripts/14/batch-05.fr.tex:15 |
| 14 | 85 | skipped, reason not classifiable | 81, 83, 85, 87, 89 Skipped. | transcripts/14/batch-05.fr.tex:15 |
| 14 | 87 | skipped, reason not classifiable | 81, 83, 85, 87, 89 Skipped. | transcripts/14/batch-05.fr.tex:15 |
| 14 | 89 | skipped, reason not classifiable | 81, 83, 85, 87, 89 Skipped. | transcripts/14/batch-05.fr.tex:15 |
| 14 | 90 | cover/wrapper | 90      Cover in his hand, « Tableau des classes de cycles ... ». | transcripts/14/batch-05.fr.tex:39 |
| 14 | 92 | cover/wrapper | 92      Cover in his hand, « Mumford-Nakai / Cycles algébriques amples ..... ». | transcripts/14/batch-05.fr.tex:49 |
| 14 | 96 | skipped, reason not classifiable | 96, 98, 100 Skipped. | transcripts/14/batch-05.fr.tex:66 |
| 14 | 98 | skipped, reason not classifiable | 96, 98, 100 Skipped. | transcripts/14/batch-05.fr.tex:66 |
| 14 | 100 | skipped, reason not classifiable | 96, 98, 100 Skipped. | transcripts/14/batch-05.fr.tex:66 |
| 14 | 101 | cover/wrapper | Skipped: 101      A cover sheet in his hand (« Conjectures de Lefschetz pour cycles algébriques : Extension aux Jac. inter. / Conjectures lo… | transcripts/14/batch-06.fr.tex:12 |
| 14 | 103 | printed/published | The batch file carries no cover sheet: PDF page N is page 100+N, as the Montpellier footer printed on each PDF page confirms, and the archiv… | transcripts/14/batch-06.fr.tex:4 |
| 14 | 104 | blank | 104, 109, 118  Blank. | transcripts/14/batch-06.fr.tex:24 |
| 14 | 109 | blank | 104, 109, 118  Blank. | transcripts/14/batch-06.fr.tex:24 |
| 14 | 118 | blank | 104, 109, 118  Blank. | transcripts/14/batch-06.fr.tex:24 |
| 14 | 121 | others' typescript | Skipped: 121, 123, 126, 128  leaves of SGA 3 typescripts used as paper — typed pages 3 and 2 of an exposé on stabilisers (M_v(S'), the diagr… | transcripts/14/batch-07.fr.tex:11 |
| 14 | 123 | others' typescript | Skipped: 121, 123, 126, 128  leaves of SGA 3 typescripts used as paper — typed pages 3 and 2 of an exposé on stabilisers (M_v(S'), the diagr… | transcripts/14/batch-07.fr.tex:11 |
| 14 | 124 | blank | 124, 129 blank leaves through which 125 and 128 show. | transcripts/14/batch-07.fr.tex:20 |
| 14 | 126 | others' typescript | Skipped: 121, 123, 126, 128  leaves of SGA 3 typescripts used as paper — typed pages 3 and 2 of an exposé on stabilisers (M_v(S'), the diagr… | transcripts/14/batch-07.fr.tex:11 |
| 14 | 128 | others' typescript | Skipped: 121, 123, 126, 128  leaves of SGA 3 typescripts used as paper — typed pages 3 and 2 of an exposé on stabilisers (M_v(S'), the diagr… | transcripts/14/batch-07.fr.tex:11 |
| 14 | 129 | blank | 124, 129 blank leaves through which 125 and 128 show. | transcripts/14/batch-07.fr.tex:20 |
| 15 | 1 | blank | page 1, an otherwise blank sheet of brown paper inscribed in his hand « Groupe de Galois motivique commutatif. | transcripts/15/batch-01.fr.tex:11 |
| 15 | 3 | others' typescript | pages 3, 5, 7, 9, 11, five leaves of an unrelated English typescript on two-dimensional rational singularities (Theorem 25.1, Remarks 25.2-2… | transcripts/15/batch-01.fr.tex:13 |
| 15 | 5 | cover/wrapper | Cas d'un corps de base fini » — a cover, whose words become the \section heading before page 2 (references/hand.md §5) | transcripts/15/batch-01.fr.tex:13 |
| 15 | 7 | others' typescript | pages 3, 5, 7, 9, 11, five leaves of an unrelated English typescript on two-dimensional rational singularities (Theorem 25.1, Remarks 25.2-2… | transcripts/15/batch-01.fr.tex:13 |
| 15 | 9 | others' typescript | pages 3, 5, 7, 9, 11, five leaves of an unrelated English typescript on two-dimensional rational singularities (Theorem 25.1, Remarks 25.2-2… | transcripts/15/batch-01.fr.tex:13 |
| 15 | 11 | others' typescript | pages 3, 5, 7, 9, 11, five leaves of an unrelated English typescript on two-dimensional rational singularities (Theorem 25.1, Remarks 25.2-2… | transcripts/15/batch-01.fr.tex:13 |
| 15 | 14 | blank | page 14, blank. | transcripts/15/batch-01.fr.tex:13 |
| 15 | 24 | blank | page 24, blank | transcripts/15/batch-02.fr.tex:11 |
| 15 | 26 | others' typescript | pages 26, 28, 30, 32, 34, 36, 38 and 40, the typed versos of pages 25-39 — leaves of an unrelated typescript on holomorphic functions of one… | transcripts/15/batch-02.fr.tex:11 |
| 15 | 28 | others' typescript | pages 26, 28, 30, 32, 34, 36, 38 and 40, the typed versos of pages 25-39 — leaves of an unrelated typescript on holomorphic functions of one… | transcripts/15/batch-02.fr.tex:11 |
| 15 | 30 | others' typescript | pages 26, 28, 30, 32, 34, 36, 38 and 40, the typed versos of pages 25-39 — leaves of an unrelated typescript on holomorphic functions of one… | transcripts/15/batch-02.fr.tex:11 |
| 15 | 32 | others' typescript | pages 26, 28, 30, 32, 34, 36, 38 and 40, the typed versos of pages 25-39 — leaves of an unrelated typescript on holomorphic functions of one… | transcripts/15/batch-02.fr.tex:11 |
| 15 | 34 | others' typescript | pages 26, 28, 30, 32, 34, 36, 38 and 40, the typed versos of pages 25-39 — leaves of an unrelated typescript on holomorphic functions of one… | transcripts/15/batch-02.fr.tex:11 |
| 15 | 36 | others' typescript | pages 26, 28, 30, 32, 34, 36, 38 and 40, the typed versos of pages 25-39 — leaves of an unrelated typescript on holomorphic functions of one… | transcripts/15/batch-02.fr.tex:11 |
| 15 | 38 | others' typescript | pages 26, 28, 30, 32, 34, 36, 38 and 40, the typed versos of pages 25-39 — leaves of an unrelated typescript on holomorphic functions of one… | transcripts/15/batch-02.fr.tex:11 |
| 15 | 40 | others' typescript | pages 26, 28, 30, 32, 34, 36, 38 and 40, the typed versos of pages 25-39 — leaves of an unrelated typescript on holomorphic functions of one… | transcripts/15/batch-02.fr.tex:11 |
| 15 | 42 | others' typescript | pages 42, 44, 46, 48, 50, 52, 54 and 56, the versos of pages 41-55 — leaves of the unrelated typescript on holomorphic functions of several … | transcripts/15/batch-03.fr.tex:14 |
| 15 | 44 | others' typescript | pages 42, 44, 46, 48, 50, 52, 54 and 56, the versos of pages 41-55 — leaves of the unrelated typescript on holomorphic functions of several … | transcripts/15/batch-03.fr.tex:14 |
| 15 | 46 | others' typescript | pages 42, 44, 46, 48, 50, 52, 54 and 56, the versos of pages 41-55 — leaves of the unrelated typescript on holomorphic functions of several … | transcripts/15/batch-03.fr.tex:14 |
| 15 | 48 | others' typescript | pages 42, 44, 46, 48, 50, 52, 54 and 56, the versos of pages 41-55 — leaves of the unrelated typescript on holomorphic functions of several … | transcripts/15/batch-03.fr.tex:14 |
| 15 | 50 | others' typescript | pages 42, 44, 46, 48, 50, 52, 54 and 56, the versos of pages 41-55 — leaves of the unrelated typescript on holomorphic functions of several … | transcripts/15/batch-03.fr.tex:14 |
| 15 | 52 | others' typescript | pages 42, 44, 46, 48, 50, 52, 54 and 56, the versos of pages 41-55 — leaves of the unrelated typescript on holomorphic functions of several … | transcripts/15/batch-03.fr.tex:14 |
| 15 | 54 | others' typescript | pages 42, 44, 46, 48, 50, 52, 54 and 56, the versos of pages 41-55 — leaves of the unrelated typescript on holomorphic functions of several … | transcripts/15/batch-03.fr.tex:14 |
| 15 | 56 | others' typescript | pages 42, 44, 46, 48, 50, 52, 54 and 56, the versos of pages 41-55 — leaves of the unrelated typescript on holomorphic functions of several … | transcripts/15/batch-03.fr.tex:14 |
| 15 | 57 | blank | page 57, blank. | transcripts/15/batch-03.fr.tex:18 |
| 15 | 61 | others' typescript | pages 61, 63, 66, 68, 70, 72, 74, 78 — leaves of an unrelated typescript (a course on analytic functions of several variables: « Domaines d'… | transcripts/15/batch-04.fr.tex:11 |
| 15 | 63 | others' typescript | pages 61, 63, 66, 68, 70, 72, 74, 78 — leaves of an unrelated typescript (a course on analytic functions of several variables: « Domaines d'… | transcripts/15/batch-04.fr.tex:11 |
| 15 | 64 | blank | Pages 64 and 79, blank. | transcripts/15/batch-04.fr.tex:16 |
| 15 | 66 | others' typescript | pages 61, 63, 66, 68, 70, 72, 74, 78 — leaves of an unrelated typescript (a course on analytic functions of several variables: « Domaines d'… | transcripts/15/batch-04.fr.tex:11 |
| 15 | 68 | others' typescript | pages 61, 63, 66, 68, 70, 72, 74, 78 — leaves of an unrelated typescript (a course on analytic functions of several variables: « Domaines d'… | transcripts/15/batch-04.fr.tex:11 |
| 15 | 70 | others' typescript | pages 61, 63, 66, 68, 70, 72, 74, 78 — leaves of an unrelated typescript (a course on analytic functions of several variables: « Domaines d'… | transcripts/15/batch-04.fr.tex:11 |
| 15 | 72 | others' typescript | pages 61, 63, 66, 68, 70, 72, 74, 78 — leaves of an unrelated typescript (a course on analytic functions of several variables: « Domaines d'… | transcripts/15/batch-04.fr.tex:11 |
| 15 | 74 | others' typescript | pages 61, 63, 66, 68, 70, 72, 74, 78 — leaves of an unrelated typescript (a course on analytic functions of several variables: « Domaines d'… | transcripts/15/batch-04.fr.tex:11 |
| 15 | 78 | others' typescript | pages 61, 63, 66, 68, 70, 72, 74, 78 — leaves of an unrelated typescript (a course on analytic functions of several variables: « Domaines d'… | transcripts/15/batch-04.fr.tex:11 |
| 15 | 79 | blank | Pages 64 and 79, blank. | transcripts/15/batch-04.fr.tex:16 |
| 15 | 82 | blank | page 82, blank | transcripts/15/batch-05.fr.tex:12 |
| 15 | 84 | others' typescript | the even pages 84 to 100, all versos of unrelated typescripts — 84, 88, 90, 92 leaves of a French typescript on étale cohomology and descent… | transcripts/15/batch-05.fr.tex:12 |
| 15 | 86 | others' typescript | the even pages 84 to 100, all versos of unrelated typescripts — 84, 88, 90, 92 leaves of a French typescript on étale cohomology and descent… | transcripts/15/batch-05.fr.tex:12 |
| 15 | 88 | others' typescript | the even pages 84 to 100, all versos of unrelated typescripts — 84, 88, 90, 92 leaves of a French typescript on étale cohomology and descent… | transcripts/15/batch-05.fr.tex:12 |
| 15 | 90 | others' typescript | the even pages 84 to 100, all versos of unrelated typescripts — 84, 88, 90, 92 leaves of a French typescript on étale cohomology and descent… | transcripts/15/batch-05.fr.tex:12 |
| 15 | 92 | others' typescript | the even pages 84 to 100, all versos of unrelated typescripts — 84, 88, 90, 92 leaves of a French typescript on étale cohomology and descent… | transcripts/15/batch-05.fr.tex:12 |
| 15 | 94 | others' typescript | the even pages 84 to 100, all versos of unrelated typescripts — 84, 88, 90, 92 leaves of a French typescript on étale cohomology and descent… | transcripts/15/batch-05.fr.tex:12 |
| 15 | 96 | others' typescript | the even pages 84 to 100, all versos of unrelated typescripts — 84, 88, 90, 92 leaves of a French typescript on étale cohomology and descent… | transcripts/15/batch-05.fr.tex:12 |
| 15 | 98 | others' typescript | the even pages 84 to 100, all versos of unrelated typescripts — 84, 88, 90, 92 leaves of a French typescript on étale cohomology and descent… | transcripts/15/batch-05.fr.tex:12 |
| 15 | 100 | others' typescript | the even pages 84 to 100, all versos of unrelated typescripts — 84, 88, 90, 92 leaves of a French typescript on étale cohomology and descent… | transcripts/15/batch-05.fr.tex:12 |
| 15 | 102 | others' typescript | the others are versos of unrelated typescripts, nothing of his mathematics on them — 102, an English typescript « IV.8 » on ringed spaces an… | transcripts/15/batch-06.fr.tex:12 |
| 15 | 104 | others' typescript | 104, 106, 110, 112, 114, 119, the English translation typed in violet already met in batch 5 (typed pp. 94, 92, 86, 84, 85, 78: sections of … | transcripts/15/batch-06.fr.tex:12 |
| 15 | 106 | others' typescript | 104, 106, 110, 112, 114, 119, the English translation typed in violet already met in batch 5 (typed pp. 94, 92, 86, 84, 85, 78: sections of … | transcripts/15/batch-06.fr.tex:12 |
| 15 | 108 | others' typescript | 108, a typescript on maximal tori and unipotent elements (« 2.9 Corollary », « 2.10 Remark »), upside down | transcripts/15/batch-06.fr.tex:18 |
| 15 | 110 | others' typescript | 104, 106, 110, 112, 114, 119, the English translation typed in violet already met in batch 5 (typed pp. 94, 92, 86, 84, 85, 78: sections of … | transcripts/15/batch-06.fr.tex:12 |
| 15 | 112 | others' typescript | 104, 106, 110, 112, 114, 119, the English translation typed in violet already met in batch 5 (typed pp. 94, 92, 86, 84, 85, 78: sections of … | transcripts/15/batch-06.fr.tex:12 |
| 15 | 114 | others' typescript | 104, 106, 110, 112, 114, 119, the English translation typed in violet already met in batch 5 (typed pp. 94, 92, 86, 84, 85, 78: sections of … | transcripts/15/batch-06.fr.tex:12 |
| 15 | 115 | blank | page 115, blank | transcripts/15/batch-06.fr.tex:12 |
| 15 | 117 | others' typescript | 117, typed errata to an exposé on groups of multiplicative type (« Page 33. | transcripts/15/batch-06.fr.tex:18 |
| 15 | 119 | others' typescript | 104, 106, 110, 112, 114, 119, the English translation typed in violet already met in batch 5 (typed pp. 94, 92, 86, 84, 85, 78: sections of … | transcripts/15/batch-06.fr.tex:12 |
| 15 | 121 | others' typescript | pages 121, 123, 125, three leaves of an unrelated English typescript (a translated paper on regular maps in the Zariski topology, its own pa… | transcripts/15/batch-07.fr.tex:12 |
| 15 | 123 | others' typescript | pages 121, 123, 125, three leaves of an unrelated English typescript (a translated paper on regular maps in the Zariski topology, its own pa… | transcripts/15/batch-07.fr.tex:12 |
| 15 | 125 | others' typescript | pages 121, 123, 125, three leaves of an unrelated English typescript (a translated paper on regular maps in the Zariski topology, its own pa… | transcripts/15/batch-07.fr.tex:12 |
| 15 | 126 | blank | pages 126 and 133, blank | transcripts/15/batch-07.fr.tex:16 |
| 15 | 133 | blank | pages 126 and 133, blank | transcripts/15/batch-07.fr.tex:16 |
| 15 | 135 | others' typescript | page 135, an administrative typed sheet (« DIVERS — CANDIDATS », dated 1.4.68 — the only date in the batch, on a verso, so no evidence for t… | transcripts/15/batch-07.fr.tex:16 |
| 15 | 137 | others' typescript | page 137, a typed errata list of some other text, scanned upside down | transcripts/15/batch-07.fr.tex:16 |
| 15 | 139 | cover/wrapper | page 139, an orange cover inscribed in his hand « Motifs essentiellement abéliens et théorie du corps de classes », whose words become the \… | transcripts/15/batch-07.fr.tex:16 |
| 15 | 145 | blank | pages 145, 152, 155 and 157, blank (145, 152, 155 show only the ink of the recto through the paper) | transcripts/15/batch-08.fr.tex:12 |
| 15 | 152 | blank | pages 145, 152, 155 and 157, blank (145, 152, 155 show only the ink of the recto through the paper) | transcripts/15/batch-08.fr.tex:12 |
| 15 | 155 | blank | pages 145, 152, 155 and 157, blank (145, 152, 155 show only the ink of the recto through the paper) | transcripts/15/batch-08.fr.tex:12 |
| 15 | 156 | cover/wrapper | page 156, a brown cover inscribed in his hand « Corps de classes commutatif = Motifs à groupe fondamental motivique [connexe] commutatif (= … | transcripts/15/batch-08.fr.tex:12 |
| 15 | 157 | blank | pages 145, 152, 155 and 157, blank (145, 152, 155 show only the ink of the recto through the paper) | transcripts/15/batch-08.fr.tex:12 |
| 15 | 159 | others' typescript | page 159, a leaf of an unrelated typescript (Bourbaki « n° 413 », p. 1-41, on differential operators on a Lie group, scanned upside down, no… | transcripts/15/batch-08.fr.tex:12 |
| 15 | 161 | others' typescript | pages 161, 163, 165, leaves of an unrelated typescript (a Bourbaki draft, « n° 413 », pp. 1-38, 1-37, 1-36, on point distributions and their… | transcripts/15/batch-09.fr.tex:13 |
| 15 | 163 | others' typescript | pages 161, 163, 165, leaves of an unrelated typescript (a Bourbaki draft, « n° 413 », pp. 1-38, 1-37, 1-36, on point distributions and their… | transcripts/15/batch-09.fr.tex:13 |
| 15 | 165 | others' typescript | pages 161, 163, 165, leaves of an unrelated typescript (a Bourbaki draft, « n° 413 », pp. 1-38, 1-37, 1-36, on point distributions and their… | transcripts/15/batch-09.fr.tex:13 |
| 15 | 166 | blank | pages 166 and 168, blank | transcripts/15/batch-09.fr.tex:13 |
| 15 | 168 | blank | pages 166 and 168, blank | transcripts/15/batch-09.fr.tex:13 |
| 15 | 170 | others' typescript | page 170, a leaf of another typescript (« Systèmes de racines (20) », Tribu n° 59, exercises on W(E7) and Sp(3,F2)), nothing in his hand | transcripts/15/batch-09.fr.tex:17 |
| 15 | 171 | blank | page 171, an otherwise blank buff sheet inscribed top right in his hand « Calculs de cohomologie absolue des Motifs de Tate Z(n). » — a cove… | transcripts/15/batch-09.fr.tex:17 |
| 15 | 179 | blank | page 179, an otherwise blank sheet carrying in pencil, centred, « Calculs de cohomologie absolue des motifs de Tate Z(n) » again — a second … | transcripts/15/batch-09.fr.tex:17 |
| 15 | 180 | printed/published | page 180, a computer listing of names and numbers, scanned upside down | transcripts/15/batch-09.fr.tex:17 |
| 15 | 181 | blank | page 181, an otherwise blank sheet inscribed top right in his hand « Généralités fonctorielles-catégoriques sur la distribution des Frobeniu… | transcripts/15/batch-10.fr.tex:13 |
| 15 | 183 | others' typescript | pages 183, 185, 187, leaves of an unrelated English typescript (pp. 73, 72, 70 of a text on the cohomology H^i(V, O_V(nE)) of a variety, equ… | transcripts/15/batch-10.fr.tex:13 |
| 15 | 185 | others' typescript | pages 183, 185, 187, leaves of an unrelated English typescript (pp. 73, 72, 70 of a text on the cohomology H^i(V, O_V(nE)) of a variety, equ… | transcripts/15/batch-10.fr.tex:13 |
| 15 | 187 | others' typescript | pages 183, 185, 187, leaves of an unrelated English typescript (pp. 73, 72, 70 of a text on the cohomology H^i(V, O_V(nE)) of a variety, equ… | transcripts/15/batch-10.fr.tex:13 |
| 15 | 188 | cover/wrapper | page 188, a buff card in pencil, « Théorie de Galois des Motifs » (underlined) over « Généralités » (underlined), and page 189, a sheet insc… | transcripts/15/batch-10.fr.tex:13 |
| 15 | 189 | cover/wrapper | page 188, a buff card in pencil, « Théorie de Galois des Motifs » (underlined) over « Généralités » (underlined), and page 189, a sheet insc… | transcripts/15/batch-10.fr.tex:13 |
| 15 | 191 | others' typescript | pages 191, 193, 195, 197, 199, leaves of a Bourbaki typescript (« Tribu n° 99 », « Algèbres de Lie semi-simples (5)-(9) », scanned upside do… | transcripts/15/batch-10.fr.tex:13 |
| 15 | 193 | others' typescript | pages 191, 193, 195, 197, 199, leaves of a Bourbaki typescript (« Tribu n° 99 », « Algèbres de Lie semi-simples (5)-(9) », scanned upside do… | transcripts/15/batch-10.fr.tex:13 |
| 15 | 195 | others' typescript | pages 191, 193, 195, 197, 199, leaves of a Bourbaki typescript (« Tribu n° 99 », « Algèbres de Lie semi-simples (5)-(9) », scanned upside do… | transcripts/15/batch-10.fr.tex:13 |
| 15 | 197 | others' typescript | pages 191, 193, 195, 197, 199, leaves of a Bourbaki typescript (« Tribu n° 99 », « Algèbres de Lie semi-simples (5)-(9) », scanned upside do… | transcripts/15/batch-10.fr.tex:13 |
| 15 | 199 | others' typescript | pages 191, 193, 195, 197, 199, leaves of a Bourbaki typescript (« Tribu n° 99 », « Algèbres de Lie semi-simples (5)-(9) », scanned upside do… | transcripts/15/batch-10.fr.tex:13 |
| 15 | 201 | others' typescript | Absent: the odd pages 201-219, leaves of unrelated typescripts — Bourbaki drafts (« Tribu n° 59 »: « Algèbres de Lie semi-simples (3), (4) »… | transcripts/15/batch-11.fr.tex:11 |
| 15 | 203 | others' typescript | Absent: the odd pages 201-219, leaves of unrelated typescripts — Bourbaki drafts (« Tribu n° 59 »: « Algèbres de Lie semi-simples (3), (4) »… | transcripts/15/batch-11.fr.tex:11 |
| 15 | 205 | others' typescript | Absent: the odd pages 201-219, leaves of unrelated typescripts — Bourbaki drafts (« Tribu n° 59 »: « Algèbres de Lie semi-simples (3), (4) »… | transcripts/15/batch-11.fr.tex:11 |
| 15 | 207 | others' typescript | Absent: the odd pages 201-219, leaves of unrelated typescripts — Bourbaki drafts (« Tribu n° 59 »: « Algèbres de Lie semi-simples (3), (4) »… | transcripts/15/batch-11.fr.tex:11 |
| 15 | 209 | others' typescript | Absent: the odd pages 201-219, leaves of unrelated typescripts — Bourbaki drafts (« Tribu n° 59 »: « Algèbres de Lie semi-simples (3), (4) »… | transcripts/15/batch-11.fr.tex:11 |
| 15 | 211 | others' typescript | Absent: the odd pages 201-219, leaves of unrelated typescripts — Bourbaki drafts (« Tribu n° 59 »: « Algèbres de Lie semi-simples (3), (4) »… | transcripts/15/batch-11.fr.tex:11 |
| 15 | 213 | others' typescript | Absent: the odd pages 201-219, leaves of unrelated typescripts — Bourbaki drafts (« Tribu n° 59 »: « Algèbres de Lie semi-simples (3), (4) »… | transcripts/15/batch-11.fr.tex:11 |
| 15 | 215 | others' typescript | Absent: the odd pages 201-219, leaves of unrelated typescripts — Bourbaki drafts (« Tribu n° 59 »: « Algèbres de Lie semi-simples (3), (4) »… | transcripts/15/batch-11.fr.tex:11 |
| 15 | 217 | others' typescript | Absent: the odd pages 201-219, leaves of unrelated typescripts — Bourbaki drafts (« Tribu n° 59 »: « Algèbres de Lie semi-simples (3), (4) »… | transcripts/15/batch-11.fr.tex:11 |
| 15 | 219 | others' typescript | Absent: the odd pages 201-219, leaves of unrelated typescripts — Bourbaki drafts (« Tribu n° 59 »: « Algèbres de Lie semi-simples (3), (4) »… | transcripts/15/batch-11.fr.tex:11 |
| 15 | 221 | others' typescript | pages 221, 223, 225 and 227, leaves of an unrelated typescript — a Bourbaki draft marked « n°370 » (Haar measure: relatively invariant measu… | transcripts/15/batch-12.fr.tex:12 |
| 15 | 223 | others' typescript | pages 221, 223, 225 and 227, leaves of an unrelated typescript — a Bourbaki draft marked « n°370 » (Haar measure: relatively invariant measu… | transcripts/15/batch-12.fr.tex:12 |
| 15 | 225 | others' typescript | pages 221, 223, 225 and 227, leaves of an unrelated typescript — a Bourbaki draft marked « n°370 » (Haar measure: relatively invariant measu… | transcripts/15/batch-12.fr.tex:12 |
| 15 | 227 | others' typescript | pages 221, 223, 225 and 227, leaves of an unrelated typescript — a Bourbaki draft marked « n°370 » (Haar measure: relatively invariant measu… | transcripts/15/batch-12.fr.tex:12 |
| 16 | 1 | blank | Page 1 is blank apart from show-through and gets no \page{}. | transcripts/16/batch-01.fr.tex:17 |
| 16 | 22 | blank | the rest are unrelated typescripts used as paper (pages 22, 25, 27, 29, 34, 36, 38, 40 — the Brauer group, corrections to SGAD, a bibliograp… | transcripts/16/batch-02.fr.tex:10 |
| 16 | 23 | blank | the rest are unrelated typescripts used as paper (pages 22, 25, 27, 29, 34, 36, 38, 40 — the Brauer group, corrections to SGAD, a bibliograp… | transcripts/16/batch-02.fr.tex:10 |
| 16 | 25 | blank | the rest are unrelated typescripts used as paper (pages 22, 25, 27, 29, 34, 36, 38, 40 — the Brauer group, corrections to SGAD, a bibliograp… | transcripts/16/batch-02.fr.tex:10 |
| 16 | 27 | blank | the rest are unrelated typescripts used as paper (pages 22, 25, 27, 29, 34, 36, 38, 40 — the Brauer group, corrections to SGAD, a bibliograp… | transcripts/16/batch-02.fr.tex:10 |
| 16 | 29 | blank | the rest are unrelated typescripts used as paper (pages 22, 25, 27, 29, 34, 36, 38, 40 — the Brauer group, corrections to SGAD, a bibliograp… | transcripts/16/batch-02.fr.tex:10 |
| 16 | 30 | blank | 24-28   « Algèbres de Hodge » — the title is his, taken from the otherwise blank leaf page 30 (that leaf gets no page number of its own). | transcripts/16/batch-02.fr.tex:25 |
| 16 | 31 | blank | 32-39   « Formulaire de L, Λ » — his title again, from the blank leaf page 31 and from the typescript's own heading. | transcripts/16/batch-02.fr.tex:34 |
| 16 | 34 | blank | the rest are unrelated typescripts used as paper (pages 22, 25, 27, 29, 34, 36, 38, 40 — the Brauer group, corrections to SGAD, a bibliograp… | transcripts/16/batch-02.fr.tex:10 |
| 16 | 36 | blank | the rest are unrelated typescripts used as paper (pages 22, 25, 27, 29, 34, 36, 38, 40 — the Brauer group, corrections to SGAD, a bibliograp… | transcripts/16/batch-02.fr.tex:10 |
| 16 | 38 | blank | the rest are unrelated typescripts used as paper (pages 22, 25, 27, 29, 34, 36, 38, 40 — the Brauer group, corrections to SGAD, a bibliograp… | transcripts/16/batch-02.fr.tex:10 |
| 16 | 40 | blank | the rest are unrelated typescripts used as paper (pages 22, 25, 27, 29, 34, 36, 38, 40 — the Brauer group, corrections to SGAD, a bibliograp… | transcripts/16/batch-02.fr.tex:10 |
| 16 | 42 | printed/published | The other four are skipped: 42 is a galley of EGA IV (§ 18.11, unramified homomorphisms), unrelated to this folder's subject although it car… | transcripts/16/batch-03.fr.tex:17 |
| 16 | 51 | printed/published | 51, 53 and 55 are a Bourbaki « Tribu » n° 65 on étale algebras and the different, and carry nothing of his. | transcripts/16/batch-03.fr.tex:17 |
| 16 | 53 | printed/published | 51, 53 and 55 are a Bourbaki « Tribu » n° 65 on étale algebras and the different, and carry nothing of his. | transcripts/16/batch-03.fr.tex:17 |
| 16 | 55 | printed/published | 51, 53 and 55 are a Bourbaki « Tribu » n° 65 on étale algebras and the different, and carry nothing of his. | transcripts/16/batch-03.fr.tex:17 |
| 18 | 1 | skipped, reason not classifiable | Page 1 is the same NSF proposal, but he has written across the head of it « Papiers donnés à Saav[edra] » — provenance rather than mathemati… | transcripts/18/batch-01.fr.tex:18 |
| 18 | 2 | others' typescript | The remaining leaves — 2, 7, 15, 17, 19, 21 — are unrelated typescript (an NSF grant proposal in English, a French typescript on formal kern… | transcripts/18/batch-01.fr.tex:14 |
| 18 | 3 | others' typescript | Nine leaves in his hand (pages 4, 5, 8, 10, 11, 12, 14, 16, 18, 20), three of them preceded by a cover inscribed with the title of the run t… | transcripts/18/batch-01.fr.tex:11 |
| 18 | 7 | others' typescript | The remaining leaves — 2, 7, 15, 17, 19, 21 — are unrelated typescript (an NSF grant proposal in English, a French typescript on formal kern… | transcripts/18/batch-01.fr.tex:14 |
| 18 | 9 | others' typescript | Nine leaves in his hand (pages 4, 5, 8, 10, 11, 12, 14, 16, 18, 20), three of them preceded by a cover inscribed with the title of the run t… | transcripts/18/batch-01.fr.tex:11 |
| 18 | 13 | others' typescript | Nine leaves in his hand (pages 4, 5, 8, 10, 11, 12, 14, 16, 18, 20), three of them preceded by a cover inscribed with the title of the run t… | transcripts/18/batch-01.fr.tex:11 |
| 18 | 15 | others' typescript | The remaining leaves — 2, 7, 15, 17, 19, 21 — are unrelated typescript (an NSF grant proposal in English, a French typescript on formal kern… | transcripts/18/batch-01.fr.tex:14 |
| 18 | 17 | others' typescript | The remaining leaves — 2, 7, 15, 17, 19, 21 — are unrelated typescript (an NSF grant proposal in English, a French typescript on formal kern… | transcripts/18/batch-01.fr.tex:14 |
| 18 | 19 | others' typescript | The remaining leaves — 2, 7, 15, 17, 19, 21 — are unrelated typescript (an NSF grant proposal in English, a French typescript on formal kern… | transcripts/18/batch-01.fr.tex:14 |
| 18 | 21 | cover/wrapper | The batch file carries no cover sheet: its PDF page 1 is archivists' page 21. | transcripts/18/batch-02.fr.tex:4 |
| 18 | 23 | others' typescript | The five odd leaves 21, 23, 25, 27, 29 are the backs of typescripts foreign to these notes — a French typescript on formal kernels on 21, a … | transcripts/18/batch-02.fr.tex:13 |
| 18 | 25 | others' typescript | The five odd leaves 21, 23, 25, 27, 29 are the backs of typescripts foreign to these notes — a French typescript on formal kernels on 21, a … | transcripts/18/batch-02.fr.tex:13 |
| 18 | 27 | others' typescript | The five odd leaves 21, 23, 25, 27, 29 are the backs of typescripts foreign to these notes — a French typescript on formal kernels on 21, a … | transcripts/18/batch-02.fr.tex:13 |
| 18 | 29 | others' typescript | The five odd leaves 21, 23, 25, 27, 29 are the backs of typescripts foreign to these notes — a French typescript on formal kernels on 21, a … | transcripts/18/batch-02.fr.tex:13 |
| 18 | 30 | cover/wrapper | Fourteen leaves carry his hand: 22, 24, 26, 28, then 30 (a cover) and 31-40 unbroken. | transcripts/18/batch-02.fr.tex:12 |
| 18 | 41 | blank | Page 41 is otherwise blank and carries only the two lines that name the run | transcripts/18/batch-03.fr.tex:14 |
| 18 | 43 | others' typescript | The odd ones, 43 45 47 49 51 53 55 57 59, are the backs of typescripts foreign to these notes (an English mathematical typescript, Bourbaki … | transcripts/18/batch-03.fr.tex:11 |
| 18 | 45 | others' typescript | The odd ones, 43 45 47 49 51 53 55 57 59, are the backs of typescripts foreign to these notes (an English mathematical typescript, Bourbaki … | transcripts/18/batch-03.fr.tex:11 |
| 18 | 47 | others' typescript | The odd ones, 43 45 47 49 51 53 55 57 59, are the backs of typescripts foreign to these notes (an English mathematical typescript, Bourbaki … | transcripts/18/batch-03.fr.tex:11 |
| 18 | 49 | others' typescript | The odd ones, 43 45 47 49 51 53 55 57 59, are the backs of typescripts foreign to these notes (an English mathematical typescript, Bourbaki … | transcripts/18/batch-03.fr.tex:11 |
| 18 | 51 | others' typescript | The odd ones, 43 45 47 49 51 53 55 57 59, are the backs of typescripts foreign to these notes (an English mathematical typescript, Bourbaki … | transcripts/18/batch-03.fr.tex:11 |
| 18 | 53 | others' typescript | The odd ones, 43 45 47 49 51 53 55 57 59, are the backs of typescripts foreign to these notes (an English mathematical typescript, Bourbaki … | transcripts/18/batch-03.fr.tex:11 |
| 18 | 55 | others' typescript | The odd ones, 43 45 47 49 51 53 55 57 59, are the backs of typescripts foreign to these notes (an English mathematical typescript, Bourbaki … | transcripts/18/batch-03.fr.tex:11 |
| 18 | 57 | others' typescript | The odd ones, 43 45 47 49 51 53 55 57 59, are the backs of typescripts foreign to these notes (an English mathematical typescript, Bourbaki … | transcripts/18/batch-03.fr.tex:11 |
| 18 | 59 | others' typescript | The odd ones, 43 45 47 49 51 53 55 57 59, are the backs of typescripts foreign to these notes (an English mathematical typescript, Bourbaki … | transcripts/18/batch-03.fr.tex:11 |
| 19 | 2 | blank | Pages 2 and 12 are blank versos — absent. | transcripts/19/batch-01.fr.tex:6 |
| 19 | 12 | blank | Pages 2 and 12 are blank versos — absent. | transcripts/19/batch-01.fr.tex:6 |
| 19 | 29 | blank | Pages 29 and 34 are blank versos — absent. | transcripts/19/batch-02.fr.tex:6 |
| 19 | 34 | blank | Pages 29 and 34 are blank versos — absent. | transcripts/19/batch-02.fr.tex:6 |
| 19 | 49 | blank | Pages 49, 51 and 55 are blank sheets — absent. | transcripts/19/batch-03.fr.tex:6 |
| 19 | 51 | blank | Pages 49, 51 and 55 are blank sheets — absent. | transcripts/19/batch-03.fr.tex:6 |
| 19 | 55 | blank | Pages 49, 51 and 55 are blank sheets — absent. | transcripts/19/batch-03.fr.tex:6 |
| 19 | 69 | blank | Page 69 is a blank sheet — absent. | transcripts/19/batch-04.fr.tex:6 |
| 19 | 85 | blank | Pages 85 and 93 are blank versos — absent. | transcripts/19/batch-05.fr.tex:9 |
| 19 | 93 | blank | Pages 85 and 93 are blank versos — absent. | transcripts/19/batch-05.fr.tex:9 |
| 21 | 1 | blank | Pages skipped, and why — the gap in the numbering is the record: 1   kraft wrapper, blank but for « Notes pour Dieud. §9 » in his hand, top … | transcripts/21/batch-01.fr.tex:32 |
| 21 | 2 | blank | 14  second kraft wrapper, blank but for six lines in his hand, struck through with three long diagonals: « Foncteurs \uncertain{élémentaires… | transcripts/21/batch-01.fr.tex:38 |
| 21 | 12 | others' typescript | Pages 3 to 13 are eleven leaves of a carbon typescript of his own, headed « 2. | transcripts/21/batch-01.fr.tex:13 |
| 21 | 14 | blank | 14  second kraft wrapper, blank but for six lines in his hand, struck through with three long diagonals: « Foncteurs \uncertain{élémentaires… | transcripts/21/batch-01.fr.tex:38 |
| 22 | 4 | blank | Jouanolou's two Comptes rendus notes of 1963 — « Étude différentielle des anneaux locaux réguliers : applications » (t. 257, pp. 2948-2950, … | transcripts/22/batch-01.fr.tex:16 |
| 22 | 6 | blank | Jouanolou's two Comptes rendus notes of 1963 — « Étude différentielle des anneaux locaux réguliers : applications » (t. 257, pp. 2948-2950, … | transcripts/22/batch-01.fr.tex:16 |
| 22 | 7 | blank | Jouanolou's two Comptes rendus notes of 1963 — « Étude différentielle des anneaux locaux réguliers : applications » (t. 257, pp. 2948-2950, … | transcripts/22/batch-01.fr.tex:16 |
| 22 | 8 | blank | Checked against the pencilled numbers bottom-left — "1" through "8" on the eight offprint leaves, then "9" … "17" on the typescript, "18" on… | transcripts/22/batch-01.fr.tex:5 |
| 22 | 18 | blank | Checked against the pencilled numbers bottom-left — "1" through "8" on the eight offprint leaves, then "9" … "17" on the typescript, "18" on… | transcripts/22/batch-01.fr.tex:5 |
| 22 | 25 | blank | 25     an otherwise blank cream sheet carrying only « Différentielles » in his hand, top right, underlined. | transcripts/22/batch-02.fr.tex:31 |
| 22 | 27 | others' typescript | - Pages 27 and 29 are printed matter — a reproduced typescript, in a type that is not his and in a hand that is nobody's, on the topology of… | transcripts/22/batch-02.fr.tex:16 |
| 22 | 29 | others' typescript | - Pages 27 and 29 are printed matter — a reproduced typescript, in a type that is not his and in a hand that is nobody's, on the topology of… | transcripts/22/batch-02.fr.tex:16 |
| 23 | 1 | cover/wrapper | 1      Cover of the whole shelfmark: « EGA IV, Calcul diff. | transcripts/23/batch-01.fr.tex:17 |
| 23 | 2 | cover/wrapper | 2      Cover « Discriminant etc ». | transcripts/23/batch-01.fr.tex:19 |
| 23 | 6 | blank | 6      Blank. | transcripts/23/batch-01.fr.tex:27 |
| 23 | 7 | cover/wrapper | 7      Cover « Exponentielle ». | transcripts/23/batch-01.fr.tex:28 |
| 23 | 17 | cover/wrapper | 17     Cover « Fibrés des germes d'ordre n de sections, etc. | transcripts/23/batch-01.fr.tex:47 |
| 23 | 33 | blank | 33     An otherwise blank leaf inscribed « Exemples, cas particuliers » in his hand, top right: the cover of the run that follows. | transcripts/23/batch-02.fr.tex:60 |
| 23 | 37 | others' typescript | 37     A typescript leaf, not in his hand: a Bourbaki-style rédaction « n° 215 », its own page « -9 7- », on groupes de trivialité and espèc… | transcripts/23/batch-02.fr.tex:74 |
| 23 | 38 | blank | 38     An otherwise blank leaf inscribed « Foncteurs différentiels d'ordre n » in his hand, top right. | transcripts/23/batch-02.fr.tex:78 |
| 23 | 41 | blank | 41-42  Two blank leaves (a blue separator sheet, then a cream one). | transcripts/23/batch-03.fr.tex:14 |
| 23 | 42 | blank | 41-42  Two blank leaves (a blue separator sheet, then a cream one). | transcripts/23/batch-03.fr.tex:14 |
| 23 | 47 | blank | 47     Blank cream leaf. | transcripts/23/batch-03.fr.tex:22 |
| 23 | 49 | blank | 49     An otherwise blank leaf inscribed « Suites régulières / Th. 11.2.9 de Raynaud » in his hand, top right: the cover of the run that fol… | transcripts/23/batch-03.fr.tex:31 |
| 23 | 54 | blank | 54     An otherwise blank leaf inscribed « Lettres Deligne » in his hand, top right: cover of the last block. | transcripts/23/batch-03.fr.tex:45 |
| 23 | 65 | blank | 65     An otherwise blank kraft sheet inscribed « Divers …. » in his hand, top right: the cover of the run that follows. | transcripts/23/batch-04.fr.tex:29 |
| 23 | 68 | blank | Pages 68 and 71 are blank versos (68 shows page 67 through the paper) and are absent. | transcripts/23/batch-04.fr.tex:37 |
| 23 | 71 | blank | Pages 68 and 71 are blank versos (68 shows page 67 through the paper) and are absent. | transcripts/23/batch-04.fr.tex:37 |
| 23 | 81 | cover/wrapper | The batch file carries no cover sheet and opens at page 81: PDF page N is archivists' page 80+N. | transcripts/23/batch-05.fr.tex:4 |
| 23 | 85 | blank | 85      Blank (bleed-through of 84 only). | transcripts/23/batch-05.fr.tex:27 |
| 23 | 90 | cover/wrapper | 90      Orange cover, « IV 12 », then in pencil « Fibres des morphismes plats de présentation finie ». | transcripts/23/batch-05.fr.tex:40 |
| 23 | 94 | blank | 94      Blank (bleed-through of 93). | transcripts/23/batch-05.fr.tex:49 |
| 25 | 121 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 122 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 123 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 124 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 125 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 126 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 127 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 128 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 129 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 130 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 131 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 132 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 133 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 136 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 137 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 138 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 139 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 25 | 140 | others' typescript | The other pages of the batch (pp. 121-133 and 136-140: typescript of §§ IV 19-21 and the contents of « IV 21 », with his ink) are left out, … | transcripts/25/batch-07.fr.tex:8 |
| 26 | 1 | cover/wrapper | Pages 1 and 9 are brown wrappers carrying, in his hand in the top right corner, "V / Plan / Notations" and "Problèmes ouverts" respectively,… | transcripts/26/batch-01.fr.tex:6 |
| 26 | 9 | cover/wrapper | Pages 1 and 9 are brown wrappers carrying, in his hand in the top right corner, "V / Plan / Notations" and "Problèmes ouverts" respectively,… | transcripts/26/batch-01.fr.tex:6 |
| 27 | 1 | cover/wrapper | Page 1 is a tan cover inscribed in pencil, top right, « Divers [pour] XII à XIV » (the numerals underlined) | transcripts/27/batch-01.fr.tex:12 |
| 27 | 7 | blank | Pages skipped: 7 and 16, blank cream sheets (only show-through) | transcripts/27/batch-01.fr.tex:7 |
| 27 | 16 | blank | Pages skipped: 7 and 16, blank cream sheets (only show-through) | transcripts/27/batch-01.fr.tex:7 |
| 27 | 20 | blank | 20, the upside-down lower half of a typed leaf on Nil(a), nilpotent subalgebras and subalgebras equal to their own normaliser, with the blan… | transcripts/27/batch-01.fr.tex:7 |
| 27 | 27 | cover/wrapper | Page 27 is a tan cover sheet inscribed in ink, top right and underlined, « Théorème de 1/2 continuité » (the 1/2 written as a small fraction… | transcripts/27/batch-02.fr.tex:10 |
| 27 | 30 | skipped, reason not classifiable | Pages skipped: 30 (below). | transcripts/27/batch-02.fr.tex:10 |
| 29 | 6 | blank | Page 6 is the blank back of the carbon of page 7 — absent. | transcripts/29/batch-01.fr.tex:6 |
| 29 | 48 | others' typescript | Pages 48, 50, 52, 54, 56 and 58 are six consecutive sheets of an unrelated violet typescript — "n° 385", pages 10, 11, 12, 13, 22 and 23, on… | transcripts/29/batch-03.fr.tex:6 |
| 29 | 50 | others' typescript | Pages 48, 50, 52, 54, 56 and 58 are six consecutive sheets of an unrelated violet typescript — "n° 385", pages 10, 11, 12, 13, 22 and 23, on… | transcripts/29/batch-03.fr.tex:6 |
| 29 | 52 | others' typescript | Pages 48, 50, 52, 54, 56 and 58 are six consecutive sheets of an unrelated violet typescript — "n° 385", pages 10, 11, 12, 13, 22 and 23, on… | transcripts/29/batch-03.fr.tex:6 |
| 29 | 54 | others' typescript | Pages 48, 50, 52, 54, 56 and 58 are six consecutive sheets of an unrelated violet typescript — "n° 385", pages 10, 11, 12, 13, 22 and 23, on… | transcripts/29/batch-03.fr.tex:6 |
| 29 | 56 | others' typescript | Pages 48, 50, 52, 54, 56 and 58 are six consecutive sheets of an unrelated violet typescript — "n° 385", pages 10, 11, 12, 13, 22 and 23, on… | transcripts/29/batch-03.fr.tex:6 |
| 29 | 58 | others' typescript | Pages 48, 50, 52, 54, 56 and 58 are six consecutive sheets of an unrelated violet typescript — "n° 385", pages 10, 11, 12, 13, 22 and 23, on… | transcripts/29/batch-03.fr.tex:6 |
| 29 | 88 | others' typescript | Pages 88, 90, 92, 94, 96 and 98 are six consecutive sheets of one unrelated typescript — SGA 3, on diagonalisable group schemes, "Définition… | transcripts/29/batch-05.fr.tex:6 |
| 29 | 90 | others' typescript | Pages 88, 90, 92, 94, 96 and 98 are six consecutive sheets of one unrelated typescript — SGA 3, on diagonalisable group schemes, "Définition… | transcripts/29/batch-05.fr.tex:6 |
| 29 | 92 | others' typescript | Pages 88, 90, 92, 94, 96 and 98 are six consecutive sheets of one unrelated typescript — SGA 3, on diagonalisable group schemes, "Définition… | transcripts/29/batch-05.fr.tex:6 |
| 29 | 94 | others' typescript | Pages 88, 90, 92, 94, 96 and 98 are six consecutive sheets of one unrelated typescript — SGA 3, on diagonalisable group schemes, "Définition… | transcripts/29/batch-05.fr.tex:6 |
| 29 | 96 | others' typescript | Pages 88, 90, 92, 94, 96 and 98 are six consecutive sheets of one unrelated typescript — SGA 3, on diagonalisable group schemes, "Définition… | transcripts/29/batch-05.fr.tex:6 |
| 29 | 98 | others' typescript | Pages 88, 90, 92, 94, 96 and 98 are six consecutive sheets of one unrelated typescript — SGA 3, on diagonalisable group schemes, "Définition… | transcripts/29/batch-05.fr.tex:6 |
| 29 | 111 | blank | - page 111, an empty orange folder cover inscribed, in his hand, "Notes pour SGA 7". | transcripts/29/batch-06.fr.tex:11 |
| 29 | 117 | blank | - page 117, the blank verso of page 116, showing only that page's bleed-through and one struck fragment — a formula number (2.1.14.6) and fo… | transcripts/29/batch-06.fr.tex:14 |
| 29 | 123 | blank | - page 123, an empty folder cover inscribed, in his hand, « "Vrai" groupe fondamental [feuilles anciennes] ». | transcripts/29/batch-07.fr.tex:11 |
| 29 | 131 | others' typescript | - pages 131, 133 and 135, three sheets of an English typescript on k-structures on vector spaces (fields of definition, Proposition 1 on k(W… | transcripts/29/batch-07.fr.tex:15 |
| 29 | 133 | others' typescript | - pages 131, 133 and 135, three sheets of an English typescript on k-structures on vector spaces (fields of definition, Proposition 1 on k(W… | transcripts/29/batch-07.fr.tex:15 |
| 29 | 135 | others' typescript | - pages 131, 133 and 135, three sheets of an English typescript on k-structures on vector spaces (fields of definition, Proposition 1 on k(W… | transcripts/29/batch-07.fr.tex:15 |
| 29 | 143 | blank | - page 143, an otherwise blank sheet inscribed, in his hand, top right, « Compléments SGA / 1960 » (a label, not the date the page was writt… | transcripts/29/batch-08.fr.tex:13 |
| 29 | 145 | others' typescript | - pages 145 and 147, two sheets of a French typescript (a corollary attributed to Hilbert on Jacobson rings, paginated "- 156 -" | transcripts/29/batch-08.fr.tex:19 |
| 29 | 147 | others' typescript | - pages 145 and 147, two sheets of a French typescript (a corollary attributed to Hilbert on Jacobson rings, paginated "- 156 -" | transcripts/29/batch-08.fr.tex:19 |
| 29 | 163 | blank | - page 163, an otherwise blank sheet inscribed top right, in his hand, « <struck>Le Groupe</struck> / Progroupe fondamental / pour les revêt… | transcripts/29/batch-09.fr.tex:11 |
| 29 | 172 | gap only (no header mention) |  | transcripts/29/batch-09.fr.tex:1 |
| 29 | 174 | gap only (no header mention) |  | transcripts/29/batch-09.fr.tex:1 |
| 29 | 177 | gap only (no header mention) |  | transcripts/29/batch-09.fr.tex:1 |
| 29 | 188 | gap only (no header mention) |  | transcripts/29/batch-10.fr.tex:1 |
| 29 | 189 | blank | - page 189, an otherwise blank leaf. | transcripts/29/batch-10.fr.tex:13 |
| 29 | 207 | blank | Page 207 is a blank leaf and gets no \page{}. | transcripts/29/batch-11.fr.tex:10 |
| 31 | 1 | others' typescript | The batch holds three runs and four leaves of corrected typescript, each run opened by a cover sheet inscribed in his hand (pages 1, 9, 18),… | transcripts/31/batch-01.fr.tex:10 |
| 31 | 3 | others' typescript | Pages 3, 5 and 7 are typescript versos (an exposé on multiplicative groups, Théorème 5.1 and its corollaries) carrying nothing in his hand —… | transcripts/31/batch-01.fr.tex:45 |
| 31 | 5 | others' typescript | Pages 3, 5 and 7 are typescript versos (an exposé on multiplicative groups, Théorème 5.1 and its corollaries) carrying nothing in his hand —… | transcripts/31/batch-01.fr.tex:45 |
| 31 | 7 | others' typescript | Pages 3, 5 and 7 are typescript versos (an exposé on multiplicative groups, Théorème 5.1 and its corollaries) carrying nothing in his hand —… | transcripts/31/batch-01.fr.tex:45 |
| 31 | 9 | others' typescript | The batch holds three runs and four leaves of corrected typescript, each run opened by a cover sheet inscribed in his hand (pages 1, 9, 18),… | transcripts/31/batch-01.fr.tex:10 |
| 31 | 18 | others' typescript | 2026-10-20 — readings checked on the facsimile by Michel Hua (#70–71): p. 15, « réunion de sous- » after the struck « somme de » is on the p… | transcripts/31/batch-01.fr.tex:8 |
| 31 | 20 | blank | Page 20 is a blank leaf with a three-word scrap upside down at its foot — absent. | transcripts/31/batch-01.fr.tex:47 |
| 31 | 23 | cover/wrapper | The batch closes the run begun on page 19 (batch 1), then holds two runs opened by cover sheets inscribed in his hand (pages 23, 32), which … | transcripts/31/batch-02.fr.tex:9 |
| 31 | 29 | others' typescript | Pages 29 and 31 are typescript leaves of the same text (Corollaire 2.2, Lemme 2.3, Corollaire 2.4) carrying nothing in his hand — absent. | transcripts/31/batch-02.fr.tex:61 |
| 31 | 31 | others' typescript | Pages 29 and 31 are typescript leaves of the same text (Corollaire 2.2, Lemme 2.3, Corollaire 2.4) carrying nothing in his hand — absent. | transcripts/31/batch-02.fr.tex:61 |
| 31 | 32 | cover/wrapper | The batch closes the run begun on page 19 (batch 1), then holds two runs opened by cover sheets inscribed in his hand (pages 23, 32), which … | transcripts/31/batch-02.fr.tex:9 |
| 31 | 33 | blank | Pages 33, 37, 39 and 40 are blank — absent. | transcripts/31/batch-02.fr.tex:62 |
| 31 | 37 | blank | Pages 33, 37, 39 and 40 are blank — absent. | transcripts/31/batch-02.fr.tex:62 |
| 31 | 39 | blank | Pages 33, 37, 39 and 40 are blank — absent. | transcripts/31/batch-02.fr.tex:62 |
| 31 | 40 | blank | Pages 33, 37, 39 and 40 are blank — absent. | transcripts/31/batch-02.fr.tex:62 |
| 31 | 45 | blank | Page 45 is blank and page 52 an empty folder cover | transcripts/31/batch-03.fr.tex:61 |
| 31 | 52 | blank | Page 45 is blank and page 52 an empty folder cover | transcripts/31/batch-03.fr.tex:61 |
| 31 | 53 | cover/wrapper | The third is opened by a cover sheet inscribed in his hand (page 53), which becomes the section heading and carries no \page{} | transcripts/31/batch-03.fr.tex:9 |
| 31 | 62 | blank | Page 62 — an otherwise blank sheet inscribed « cd des affines » in his hand | transcripts/31/batch-04.fr.tex:14 |
| 31 | 63 | blank | Pages 63 and 72 (blank) are absent. | transcripts/31/batch-04.fr.tex:41 |
| 31 | 72 | blank | Pages 63 and 72 (blank) are absent. | transcripts/31/batch-04.fr.tex:41 |
| 31 | 88 | blank | Page 88 (blank) is absent. | transcripts/31/batch-05.fr.tex:45 |
| 31 | 91 | blank | Page 91 — an otherwise blank sheet inscribed « Théorème de Spécialisation : Corollaire » in his hand | transcripts/31/batch-05.fr.tex:32 |
| 31 | 99 | others' typescript | Page 99 carries a leaf of an unrelated typescript (Bourbaki, Algèbre commutative, chap. | transcripts/31/batch-05.fr.tex:45 |
| 32 | 1 | blank | Pages 1 (blank folder cover) | transcripts/32/batch-01.fr.tex:36 |
| 32 | 3 | blank | Page 2 — ink, top left of a blank leaf: « SGA 4 IX », a list of page and line numbers to correct (pp. 2, 3, 60, 61, 63, 80, 91), no text. | transcripts/32/batch-01.fr.tex:11 |
| 32 | 5 | cover/wrapper | 3 and 5 (covers, which become the section headings) are absent. | transcripts/32/batch-01.fr.tex:36 |
| 33 | 4 | others' typescript | The even pages 4, 6, 8, 10, 12, 14, 16, 18 and page 20 are typed versos (a Bourbaki-style draft on root systems and Dynkin diagrams, pages n… | transcripts/33/batch-01.fr.tex:9 |
| 33 | 6 | others' typescript | The even pages 4, 6, 8, 10, 12, 14, 16, 18 and page 20 are typed versos (a Bourbaki-style draft on root systems and Dynkin diagrams, pages n… | transcripts/33/batch-01.fr.tex:9 |
| 33 | 8 | others' typescript | The even pages 4, 6, 8, 10, 12, 14, 16, 18 and page 20 are typed versos (a Bourbaki-style draft on root systems and Dynkin diagrams, pages n… | transcripts/33/batch-01.fr.tex:9 |
| 33 | 10 | others' typescript | The even pages 4, 6, 8, 10, 12, 14, 16, 18 and page 20 are typed versos (a Bourbaki-style draft on root systems and Dynkin diagrams, pages n… | transcripts/33/batch-01.fr.tex:9 |
| 33 | 12 | others' typescript | The even pages 4, 6, 8, 10, 12, 14, 16, 18 and page 20 are typed versos (a Bourbaki-style draft on root systems and Dynkin diagrams, pages n… | transcripts/33/batch-01.fr.tex:9 |
| 33 | 14 | others' typescript | The even pages 4, 6, 8, 10, 12, 14, 16, 18 and page 20 are typed versos (a Bourbaki-style draft on root systems and Dynkin diagrams, pages n… | transcripts/33/batch-01.fr.tex:9 |
| 33 | 16 | others' typescript | The even pages 4, 6, 8, 10, 12, 14, 16, 18 and page 20 are typed versos (a Bourbaki-style draft on root systems and Dynkin diagrams, pages n… | transcripts/33/batch-01.fr.tex:9 |
| 33 | 18 | others' typescript | The even pages 4, 6, 8, 10, 12, 14, 16, 18 and page 20 are typed versos (a Bourbaki-style draft on root systems and Dynkin diagrams, pages n… | transcripts/33/batch-01.fr.tex:9 |
| 33 | 20 | others' typescript | The even pages 4, 6, 8, 10, 12, 14, 16, 18 and page 20 are typed versos (a Bourbaki-style draft on root systems and Dynkin diagrams, pages n… | transcripts/33/batch-01.fr.tex:9 |
| 33 | 22 | gap only (no header mention) |  | transcripts/33/batch-02.fr.tex:1 |
| 33 | 24 | gap only (no header mention) |  | transcripts/33/batch-02.fr.tex:1 |
| 33 | 26 | gap only (no header mention) |  | transcripts/33/batch-02.fr.tex:1 |
| 33 | 28 | gap only (no header mention) |  | transcripts/33/batch-02.fr.tex:1 |
| 33 | 30 | gap only (no header mention) |  | transcripts/33/batch-02.fr.tex:1 |
| 33 | 32 | gap only (no header mention) |  | transcripts/33/batch-02.fr.tex:1 |
| 33 | 34 | gap only (no header mention) |  | transcripts/33/batch-02.fr.tex:1 |
| 33 | 36 | gap only (no header mention) |  | transcripts/33/batch-02.fr.tex:1 |
| 33 | 38 | gap only (no header mention) |  | transcripts/33/batch-02.fr.tex:1 |
| 33 | 40 | gap only (no header mention) |  | transcripts/33/batch-02.fr.tex:1 |
| 33 | 42 | others' typescript | The even pages (42, 44, 46, 48, 50, 52, 54, 56, 58, 60) carry only typescript unrelated to the notes in hand (an English text on sheaves and… | transcripts/33/batch-03.fr.tex:4 |
| 33 | 44 | others' typescript | The even pages (42, 44, 46, 48, 50, 52, 54, 56, 58, 60) carry only typescript unrelated to the notes in hand (an English text on sheaves and… | transcripts/33/batch-03.fr.tex:4 |
| 33 | 46 | others' typescript | The even pages (42, 44, 46, 48, 50, 52, 54, 56, 58, 60) carry only typescript unrelated to the notes in hand (an English text on sheaves and… | transcripts/33/batch-03.fr.tex:4 |
| 33 | 48 | others' typescript | The even pages (42, 44, 46, 48, 50, 52, 54, 56, 58, 60) carry only typescript unrelated to the notes in hand (an English text on sheaves and… | transcripts/33/batch-03.fr.tex:4 |
| 33 | 50 | others' typescript | The even pages (42, 44, 46, 48, 50, 52, 54, 56, 58, 60) carry only typescript unrelated to the notes in hand (an English text on sheaves and… | transcripts/33/batch-03.fr.tex:4 |
| 33 | 52 | others' typescript | The even pages (42, 44, 46, 48, 50, 52, 54, 56, 58, 60) carry only typescript unrelated to the notes in hand (an English text on sheaves and… | transcripts/33/batch-03.fr.tex:4 |
| 33 | 54 | others' typescript | The even pages (42, 44, 46, 48, 50, 52, 54, 56, 58, 60) carry only typescript unrelated to the notes in hand (an English text on sheaves and… | transcripts/33/batch-03.fr.tex:4 |
| 33 | 56 | others' typescript | The even pages (42, 44, 46, 48, 50, 52, 54, 56, 58, 60) carry only typescript unrelated to the notes in hand (an English text on sheaves and… | transcripts/33/batch-03.fr.tex:4 |
| 33 | 58 | others' typescript | The even pages (42, 44, 46, 48, 50, 52, 54, 56, 58, 60) carry only typescript unrelated to the notes in hand (an English text on sheaves and… | transcripts/33/batch-03.fr.tex:4 |
| 33 | 60 | others' typescript | The even pages (42, 44, 46, 48, 50, 52, 54, 56, 58, 60) carry only typescript unrelated to the notes in hand (an English text on sheaves and… | transcripts/33/batch-03.fr.tex:4 |
| 33 | 62 | others' typescript | The even pages 62–80 are those typescripts' own faces, unrelated, carrying nothing in his hand: skipped. | transcripts/33/batch-04.fr.tex:6 |
| 33 | 64 | others' typescript | The even pages 62–80 are those typescripts' own faces, unrelated, carrying nothing in his hand: skipped. | transcripts/33/batch-04.fr.tex:6 |
| 33 | 66 | others' typescript | The even pages 62–80 are those typescripts' own faces, unrelated, carrying nothing in his hand: skipped. | transcripts/33/batch-04.fr.tex:6 |
| 33 | 68 | others' typescript | The even pages 62–80 are those typescripts' own faces, unrelated, carrying nothing in his hand: skipped. | transcripts/33/batch-04.fr.tex:6 |
| 33 | 70 | others' typescript | The even pages 62–80 are those typescripts' own faces, unrelated, carrying nothing in his hand: skipped. | transcripts/33/batch-04.fr.tex:6 |
| 33 | 72 | others' typescript | The even pages 62–80 are those typescripts' own faces, unrelated, carrying nothing in his hand: skipped. | transcripts/33/batch-04.fr.tex:6 |
| 33 | 74 | others' typescript | The even pages 62–80 are those typescripts' own faces, unrelated, carrying nothing in his hand: skipped. | transcripts/33/batch-04.fr.tex:6 |
| 33 | 76 | others' typescript | The even pages 62–80 are those typescripts' own faces, unrelated, carrying nothing in his hand: skipped. | transcripts/33/batch-04.fr.tex:6 |
| 33 | 78 | others' typescript | The even pages 62–80 are those typescripts' own faces, unrelated, carrying nothing in his hand: skipped. | transcripts/33/batch-04.fr.tex:6 |
| 33 | 80 | others' typescript | The even pages 62–80 are those typescripts' own faces, unrelated, carrying nothing in his hand: skipped. | transcripts/33/batch-04.fr.tex:6 |
| 33 | 82 | gap only (no header mention) |  | transcripts/33/batch-05.fr.tex:1 |
| 33 | 84 | gap only (no header mention) |  | transcripts/33/batch-05.fr.tex:1 |
| 33 | 86 | gap only (no header mention) |  | transcripts/33/batch-05.fr.tex:1 |
| 33 | 88 | gap only (no header mention) |  | transcripts/33/batch-05.fr.tex:1 |
| 33 | 90 | gap only (no header mention) |  | transcripts/33/batch-05.fr.tex:1 |
| 33 | 92 | gap only (no header mention) |  | transcripts/33/batch-05.fr.tex:1 |
| 33 | 94 | gap only (no header mention) |  | transcripts/33/batch-05.fr.tex:1 |
| 33 | 96 | gap only (no header mention) |  | transcripts/33/batch-05.fr.tex:1 |
| 33 | 98 | gap only (no header mention) |  | transcripts/33/batch-05.fr.tex:1 |
| 33 | 100 | gap only (no header mention) |  | transcripts/33/batch-05.fr.tex:1 |
| 33 | 102 | others' typescript | The even pages 102-120 are that typescript alone, with nothing in his hand, and are absent. | transcripts/33/batch-06.fr.tex:9 |
| 33 | 104 | others' typescript | The even pages 102-120 are that typescript alone, with nothing in his hand, and are absent. | transcripts/33/batch-06.fr.tex:9 |
| 33 | 106 | others' typescript | The even pages 102-120 are that typescript alone, with nothing in his hand, and are absent. | transcripts/33/batch-06.fr.tex:9 |
| 33 | 108 | others' typescript | The even pages 102-120 are that typescript alone, with nothing in his hand, and are absent. | transcripts/33/batch-06.fr.tex:9 |
| 33 | 110 | others' typescript | The even pages 102-120 are that typescript alone, with nothing in his hand, and are absent. | transcripts/33/batch-06.fr.tex:9 |
| 33 | 112 | others' typescript | The even pages 102-120 are that typescript alone, with nothing in his hand, and are absent. | transcripts/33/batch-06.fr.tex:9 |
| 33 | 114 | others' typescript | The even pages 102-120 are that typescript alone, with nothing in his hand, and are absent. | transcripts/33/batch-06.fr.tex:9 |
| 33 | 116 | others' typescript | The even pages 102-120 are that typescript alone, with nothing in his hand, and are absent. | transcripts/33/batch-06.fr.tex:9 |
| 33 | 118 | others' typescript | The even pages 102-120 are that typescript alone, with nothing in his hand, and are absent. | transcripts/33/batch-06.fr.tex:9 |
| 33 | 120 | others' typescript | The even pages 102-120 are that typescript alone, with nothing in his hand, and are absent. | transcripts/33/batch-06.fr.tex:9 |
| 33 | 122 | others' typescript | Even pages 122–140 are versos carrying typescripts unrelated to the notes (an upside-down French typescript on relative divisors, then pages… | transcripts/33/batch-07.fr.tex:4 |
| 33 | 124 | others' typescript | Even pages 122–140 are versos carrying typescripts unrelated to the notes (an upside-down French typescript on relative divisors, then pages… | transcripts/33/batch-07.fr.tex:4 |
| 33 | 126 | others' typescript | Even pages 122–140 are versos carrying typescripts unrelated to the notes (an upside-down French typescript on relative divisors, then pages… | transcripts/33/batch-07.fr.tex:4 |
| 33 | 128 | others' typescript | Even pages 122–140 are versos carrying typescripts unrelated to the notes (an upside-down French typescript on relative divisors, then pages… | transcripts/33/batch-07.fr.tex:4 |
| 33 | 130 | others' typescript | Even pages 122–140 are versos carrying typescripts unrelated to the notes (an upside-down French typescript on relative divisors, then pages… | transcripts/33/batch-07.fr.tex:4 |
| 33 | 132 | others' typescript | Even pages 122–140 are versos carrying typescripts unrelated to the notes (an upside-down French typescript on relative divisors, then pages… | transcripts/33/batch-07.fr.tex:4 |
| 33 | 134 | others' typescript | Even pages 122–140 are versos carrying typescripts unrelated to the notes (an upside-down French typescript on relative divisors, then pages… | transcripts/33/batch-07.fr.tex:4 |
| 33 | 136 | others' typescript | Even pages 122–140 are versos carrying typescripts unrelated to the notes (an upside-down French typescript on relative divisors, then pages… | transcripts/33/batch-07.fr.tex:4 |
| 33 | 138 | others' typescript | Even pages 122–140 are versos carrying typescripts unrelated to the notes (an upside-down French typescript on relative divisors, then pages… | transcripts/33/batch-07.fr.tex:4 |
| 33 | 140 | others' typescript | Even pages 122–140 are versos carrying typescripts unrelated to the notes (an upside-down French typescript on relative divisors, then pages… | transcripts/33/batch-07.fr.tex:4 |
| 33 | 142 | gap only (no header mention) |  | transcripts/33/batch-08.fr.tex:1 |
| 33 | 144 | gap only (no header mention) |  | transcripts/33/batch-08.fr.tex:1 |
| 33 | 146 | gap only (no header mention) |  | transcripts/33/batch-08.fr.tex:1 |
| 33 | 148 | gap only (no header mention) |  | transcripts/33/batch-08.fr.tex:1 |
| 33 | 150 | gap only (no header mention) |  | transcripts/33/batch-08.fr.tex:1 |
| 33 | 152 | gap only (no header mention) |  | transcripts/33/batch-08.fr.tex:1 |
| 33 | 154 | gap only (no header mention) |  | transcripts/33/batch-08.fr.tex:1 |
| 33 | 156 | gap only (no header mention) |  | transcripts/33/batch-08.fr.tex:1 |
| 33 | 158 | gap only (no header mention) |  | transcripts/33/batch-08.fr.tex:1 |
| 33 | 160 | gap only (no header mention) |  | transcripts/33/batch-08.fr.tex:1 |
| 33 | 162 | others' typescript | Pages 162, 167, 170, 172, 174, 176, 178 and 180 are unrelated typescripts (Bourbaki « tribu », papers in English) | transcripts/33/batch-09.fr.tex:3 |
| 33 | 163 | blank | page 168 is blank, page 163 is a cover whose words become the section heading — all absent. | transcripts/33/batch-09.fr.tex:3 |
| 33 | 167 | others' typescript | Pages 162, 167, 170, 172, 174, 176, 178 and 180 are unrelated typescripts (Bourbaki « tribu », papers in English) | transcripts/33/batch-09.fr.tex:3 |
| 33 | 168 | blank | page 168 is blank, page 163 is a cover whose words become the section heading — all absent. | transcripts/33/batch-09.fr.tex:3 |
| 33 | 170 | others' typescript | Pages 162, 167, 170, 172, 174, 176, 178 and 180 are unrelated typescripts (Bourbaki « tribu », papers in English) | transcripts/33/batch-09.fr.tex:3 |
| 33 | 172 | others' typescript | Pages 162, 167, 170, 172, 174, 176, 178 and 180 are unrelated typescripts (Bourbaki « tribu », papers in English) | transcripts/33/batch-09.fr.tex:3 |
| 33 | 174 | others' typescript | Pages 162, 167, 170, 172, 174, 176, 178 and 180 are unrelated typescripts (Bourbaki « tribu », papers in English) | transcripts/33/batch-09.fr.tex:3 |
| 33 | 176 | others' typescript | Pages 162, 167, 170, 172, 174, 176, 178 and 180 are unrelated typescripts (Bourbaki « tribu », papers in English) | transcripts/33/batch-09.fr.tex:3 |
| 33 | 178 | others' typescript | Pages 162, 167, 170, 172, 174, 176, 178 and 180 are unrelated typescripts (Bourbaki « tribu », papers in English) | transcripts/33/batch-09.fr.tex:3 |
| 33 | 180 | others' typescript | Pages 162, 167, 170, 172, 174, 176, 178 and 180 are unrelated typescripts (Bourbaki « tribu », papers in English) | transcripts/33/batch-09.fr.tex:3 |
| 34 | 1 | blank | Page 1 is a blank cover sheet carrying only the archivists' number and is skipped. | transcripts/34/batch-01.fr.tex:8 |
| 34 | 51 | blank | Page 51 is blank and carries no \page{} | transcripts/34/batch-03.fr.tex:4 |
| 34 | 82 | blank | Page 82 is a blank sheet and carries no \page{} | transcripts/34/batch-05.fr.tex:4 |
| 34 | 128 | blank | Page 128 is blank and skipped. | transcripts/34/batch-07.fr.tex:10 |
| 34 | 162 | blank | Page 162 is blank and page 168 an unrelated typed verso | transcripts/34/batch-09.fr.tex:11 |
| 34 | 168 | blank | Page 162 is blank and page 168 an unrelated typed verso | transcripts/34/batch-09.fr.tex:11 |
| 34 | 181 | blank | Page 181 is blank and absent. | transcripts/34/batch-10.fr.tex:4 |
| 34 | 199 | gap only (no header mention) |  | transcripts/34/batch-10.fr.tex:1 |
| 36 | 1 | blank | Pages skipped: 1 (a blank cream sheet carrying only show-through of the squared leaf behind it) and 8 (blank). | transcripts/36/batch-01.fr.tex:10 |
| 36 | 8 | blank | Pages skipped: 1 (a blank cream sheet carrying only show-through of the squared leaf behind it) and 8 (blank). | transcripts/36/batch-01.fr.tex:10 |
| 36 | 34 | blank | Page 34 is a blank sheet carrying only his title « Picard et dualité » (underlined): a cover, no \page marker, his words become the section … | transcripts/36/batch-02.fr.tex:11 |
| 36 | 37 | others' typescript | Pages skipped: 37 (upside-down typed verso of an unrelated Bourbaki draft on algebras, nothing in his hand). | transcripts/36/batch-02.fr.tex:10 |
| 36 | 46 | cover/wrapper | Pages 46 and 59 are covers (a tan sheet with only his title): no \page marker, his words become the section heading, with a \note. | transcripts/36/batch-03.fr.tex:18 |
| 36 | 52 | others' typescript | Pages skipped: 52, 54 and 58, leaves of an English typescript on invariant theory (typed pagination « -1.5- », « -1.6- », « -0.26 bis- »: De… | transcripts/36/batch-03.fr.tex:10 |
| 36 | 54 | others' typescript | Pages skipped: 52, 54 and 58, leaves of an English typescript on invariant theory (typed pagination « -1.5- », « -1.6- », « -0.26 bis- »: De… | transcripts/36/batch-03.fr.tex:10 |
| 36 | 58 | others' typescript | Pages skipped: 52, 54 and 58, leaves of an English typescript on invariant theory (typed pagination « -1.5- », « -1.6- », « -0.26 bis- »: De… | transcripts/36/batch-03.fr.tex:10 |
| 36 | 59 | cover/wrapper | Pages 46 and 59 are covers (a tan sheet with only his title): no \page marker, his words become the section heading, with a \note. | transcripts/36/batch-03.fr.tex:18 |
| 36 | 65 | others' typescript | Pages skipped: 65, 67, 69, 71 (typed versos of an unrelated Bourbaki draft, « n° 384 », typed pp. 10, 9, 7, 3 (pp. 65, 67, 69, 71 in that or… | transcripts/36/batch-04.fr.tex:10 |
| 36 | 67 | others' typescript | Pages skipped: 65, 67, 69, 71 (typed versos of an unrelated Bourbaki draft, « n° 384 », typed pp. 10, 9, 7, 3 (pp. 65, 67, 69, 71 in that or… | transcripts/36/batch-04.fr.tex:10 |
| 36 | 69 | others' typescript | Pages skipped: 65, 67, 69, 71 (typed versos of an unrelated Bourbaki draft, « n° 384 », typed pp. 10, 9, 7, 3 (pp. 65, 67, 69, 71 in that or… | transcripts/36/batch-04.fr.tex:10 |
| 36 | 71 | others' typescript | Pages skipped: 65, 67, 69, 71 (typed versos of an unrelated Bourbaki draft, « n° 384 », typed pp. 10, 9, 7, 3 (pp. 65, 67, 69, 71 in that or… | transcripts/36/batch-04.fr.tex:10 |
| 36 | 72 | cover/wrapper | Page 72 is a cover (a sheet bearing only his title): no \page marker, his words become the section heading, with a \note. | transcripts/36/batch-04.fr.tex:13 |
| 36 | 77 | blank | nothing of SGA 7 on them) and 77 (a blank sheet of IHES letterhead). | transcripts/36/batch-04.fr.tex:10 |
| 36 | 81 | cover/wrapper | Page 81 is a tan cover inscribed in ink, top right: a struck-through title (« Extensions et biextensions de groupes algébriques ... », the r… | transcripts/36/batch-05.fr.tex:11 |
| 36 | 84 | blank | Pages skipped: 84, a blank sheet of IHES letterhead with nothing in his hand. | transcripts/36/batch-05.fr.tex:10 |
| 37 | 1 | blank | Pages skipped: 1 (a blank cream sheet). | transcripts/37/batch-01.fr.tex:10 |
| 37 | 5 | cover/wrapper | Pages 5 and 7 are tan covers inscribed in pencil, top right, « SGA 1 » and « SGA 4 »: no \page marker, their words become section headings w… | transcripts/37/batch-01.fr.tex:10 |
| 37 | 7 | cover/wrapper | Pages 5 and 7 are tan covers inscribed in pencil, top right, « SGA 1 » and « SGA 4 »: no \page marker, their words become section headings w… | transcripts/37/batch-01.fr.tex:10 |
| 37 | 28 | blank | Pages skipped: 28 and 31 (blank cream sheets) | transcripts/37/batch-02.fr.tex:10 |
| 37 | 31 | blank | Pages skipped: 28 and 31 (blank cream sheets) | transcripts/37/batch-02.fr.tex:10 |
| 37 | 36 | blank | 36 (a blank IHES letterhead leaf, upside down, nothing written on it). | transcripts/37/batch-02.fr.tex:10 |
| 37 | 45 | blank | Pages skipped: 45 (a blank cream sheet). | transcripts/37/batch-03.fr.tex:10 |
| 37 | 50 | cover/wrapper | Pages 50 and 55 are tan covers inscribed in pencil, top right, « SGA 5 » and « SGA 6 »: no \page marker, their words become section headings… | transcripts/37/batch-03.fr.tex:10 |
| 37 | 55 | cover/wrapper | Pages 50 and 55 are tan covers inscribed in pencil, top right, « SGA 5 » and « SGA 6 »: no \page marker, their words become section headings… | transcripts/37/batch-03.fr.tex:10 |
| 37 | 64 | blank | Pages skipped: 64 (a blank cream sheet). | transcripts/37/batch-04.fr.tex:10 |
| 37 | 72 | cover/wrapper | Page 72 is a tan cover inscribed in pencil, top right, « SGA 7 »: no \page marker, its words become a section heading with a \note (hand.md … | transcripts/37/batch-04.fr.tex:10 |
| 37 | 83 | cover/wrapper | Pages 83 and 98 are tan covers inscribed top right, « Réédition EGA I » (ink, underlined, a scribbled-out word below it) and « EGA II » (pen… | transcripts/37/batch-05.fr.tex:11 |
| 37 | 98 | cover/wrapper | Pages 83 and 98 are tan covers inscribed top right, « Réédition EGA I » (ink, underlined, a scribbled-out word below it) and « EGA II » (pen… | transcripts/37/batch-05.fr.tex:11 |
| 39 | 1 | blank | Pages 1, 8 and 17 are blank cream separator sheets carrying nothing in his hand | transcripts/39/batch-01.fr.tex:7 |
| 39 | 8 | blank | Pages 1, 8 and 17 are blank cream separator sheets carrying nothing in his hand | transcripts/39/batch-01.fr.tex:7 |
| 39 | 17 | blank | Pages 1, 8 and 17 are blank cream separator sheets carrying nothing in his hand | transcripts/39/batch-01.fr.tex:7 |
| 41 | 2 | skipped, reason not classifiable | Page 2 is the reverse of that leaf and carries nothing | transcripts/41/batch-01.fr.tex:11 |
| 43 | 1 | duplicate | tiles in archives/tiles/43/p1-p20. | transcripts/43/batch-01.fr.tex:2 |
| 43 | 2 | cover/wrapper | Pages 1 and 2 are covers inscribed in his hand and take no \page marker | transcripts/43/batch-01.fr.tex:23 |
| 43 | 13 | blank | Pages skipped: 13, a blank sheet. | transcripts/43/batch-01.fr.tex:23 |
| 43 | 23 | cover/wrapper | covers 23 and 35 are chamois card. | transcripts/43/batch-02.fr.tex:19 |
| 43 | 35 | cover/wrapper | covers 23 and 35 are chamois card. | transcripts/43/batch-02.fr.tex:19 |
| 43 | 38 | blank | Pages skipped: 38, a blank cream sheet. | transcripts/43/batch-02.fr.tex:23 |
| 43 | 43 | blank | Pages skipped: 43, a blank cream sheet. | transcripts/43/batch-03.fr.tex:24 |
| 43 | 69 | duplicate | Page 69 is a cover inscribed in his hand at the top right, « Jacobiennes locales »: it takes no \page marker and its words become the sectio… | transcripts/43/batch-04.fr.tex:25 |
| 43 | 82 | blank | Pages skipped: 82, 87, 98 (blank cream sheets) | transcripts/43/batch-05.fr.tex:31 |
| 43 | 84 | others' typescript | 84 and 86 (two leaves of a typed bibliography, typed pages 131 and 132, [1]-[17] — Cartier, Lang, Lang-Néron, Néron, Northcott, Samuel, Serr… | transcripts/43/batch-05.fr.tex:31 |
| 43 | 86 | others' typescript | 84 and 86 (two leaves of a typed bibliography, typed pages 131 and 132, [1]-[17] — Cartier, Lang, Lang-Néron, Néron, Northcott, Samuel, Serr… | transcripts/43/batch-05.fr.tex:31 |
| 43 | 87 | blank | Pages skipped: 82, 87, 98 (blank cream sheets) | transcripts/43/batch-05.fr.tex:31 |
| 43 | 90 | cover/wrapper | Page 90 is a cover (kraft folder) inscribed in his hand at the top right, « Corps de classe local géométrique et dualité »: it takes no \pag… | transcripts/43/batch-05.fr.tex:39 |
| 43 | 98 | blank | Pages skipped: 82, 87, 98 (blank cream sheets) | transcripts/43/batch-05.fr.tex:31 |
| 43 | 100 | others' typescript | 100 (an upside-down typed page, « 22. », of an English paper on Thom complexes, Stiefel manifolds and James's « intrinsic join », Pembroke C… | transcripts/43/batch-05.fr.tex:31 |
| 43 | 102 | others' typescript | Pages skipped: 102 and 104, two typed leaves of an English paper on Stiefel manifolds and « intrinsic join » (typed p. 21 and the REFERENCES… | transcripts/43/batch-06.fr.tex:29 |
| 43 | 104 | others' typescript | Pages skipped: 102 and 104, two typed leaves of an English paper on Stiefel manifolds and « intrinsic join » (typed p. 21 and the REFERENCES… | transcripts/43/batch-06.fr.tex:29 |
| 43 | 110 | blank | 110, a blank sheet. | transcripts/43/batch-06.fr.tex:29 |
| 43 | 121 | duplicate | tiles in archives/tiles/43/p121-p140. | transcripts/43/batch-07.fr.tex:2 |
| 43 | 123 | others' typescript | Pages skipped: 123, 125, 138, 140 — typed leaves (upside down for 123 and 125) of a French typescript on sheaves, headed « n° 239 », typed p… | transcripts/43/batch-07.fr.tex:26 |
| 43 | 125 | others' typescript | Pages skipped: 123, 125, 138, 140 — typed leaves (upside down for 123 and 125) of a French typescript on sheaves, headed « n° 239 », typed p… | transcripts/43/batch-07.fr.tex:26 |
| 43 | 126 | blank | Page 126: a blank sheet. | transcripts/43/batch-07.fr.tex:31 |
| 43 | 138 | others' typescript | Pages skipped: 123, 125, 138, 140 — typed leaves (upside down for 123 and 125) of a French typescript on sheaves, headed « n° 239 », typed p… | transcripts/43/batch-07.fr.tex:26 |
| 43 | 140 | others' typescript | Pages skipped: 123, 125, 138, 140 — typed leaves (upside down for 123 and 125) of a French typescript on sheaves, headed « n° 239 », typed p… | transcripts/43/batch-07.fr.tex:26 |
| 43 | 141 | duplicate | tiles in archives/tiles/43/p141-p160. | transcripts/43/batch-08.fr.tex:2 |
| 43 | 146 | cover/wrapper | the covers 141, 146, 159 are originals. | transcripts/43/batch-08.fr.tex:26 |
| 43 | 156 | blank | Pages skipped: 156 and 158, blank sheets (158 carries only a stray pencil mark). | transcripts/43/batch-08.fr.tex:32 |
| 43 | 158 | blank | Pages skipped: 156 and 158, blank sheets (158 carries only a stray pencil mark). | transcripts/43/batch-08.fr.tex:32 |
| 43 | 159 | cover/wrapper | the covers 141, 146, 159 are originals. | transcripts/43/batch-08.fr.tex:26 |
| 43 | 170 | cover/wrapper | page 170 is an orange cover sheet. | transcripts/43/batch-09.fr.tex:26 |
| 43 | 193 | blank | Pages skipped: 193, a blank cream sheet | transcripts/43/batch-10.fr.tex:27 |
| 43 | 197 | blank | 197, the blank side of a letterhead sheet carrying only the printed heading. | transcripts/43/batch-10.fr.tex:27 |
| 43 | 202 | cover/wrapper | Page 202 is a cover (an orange sheet inscribed in his hand at the top right, « Accouplements de [one sign] Tate -- Lang ») and takes no \pag… | transcripts/43/batch-11.fr.tex:17 |
| 44 | 6 | others' typescript | page 2 is a cancelled sheet of his own on the completion of a graded ring, page 4 a cancelled sheet of his own on the axioms of a root datum… | transcripts/44/batch-01.fr.tex:9 |
| 45 | 1 | cover/wrapper | page 1, the tan folder cover, inscribed in brown ink top right « Groupes semi-simples » | transcripts/45/batch-01.fr.tex:16 |
| 45 | 2 | blank | page 2, a sheet blank but for « Application des s.-alg. de Cartan aux corps de dim. 1 » top right, in his hand | transcripts/45/batch-01.fr.tex:16 |
| 45 | 15 | blank | page 15, a sheet blank but for a struck line and « Cas non ½simple : Question de rationalité du radical, définition de la "variété des drape… | transcripts/45/batch-01.fr.tex:16 |
| 45 | 27 | blank | page 27, a grey sheet blank but for « Groupes [diagonalisables struck] radiciels et Hyperalgèbres des groupes diagonalisables » top right | transcripts/45/batch-02.fr.tex:12 |
| 45 | 30 | skipped, reason not classifiable | Pages skipped, without description: 30, 32, 38, 40. | transcripts/45/batch-02.fr.tex:18 |
| 45 | 32 | skipped, reason not classifiable | Pages skipped, without description: 30, 32, 38, 40. | transcripts/45/batch-02.fr.tex:18 |
| 45 | 36 | blank | page 36, a tan sheet blank but for « Cohomologie de l'algèbre de Lie et cohom. des groupes ... » top right. | transcripts/45/batch-02.fr.tex:12 |
| 45 | 38 | skipped, reason not classifiable | Pages skipped, without description: 30, 32, 38, 40. | transcripts/45/batch-02.fr.tex:18 |
| 45 | 40 | skipped, reason not classifiable | Pages skipped, without description: 30, 32, 38, 40. | transcripts/45/batch-02.fr.tex:18 |
| 45 | 42 | skipped, reason not classifiable | Pages skipped, without description: 42, 45, 47, 49, 51, 53, 55, 57, 59. | transcripts/45/batch-03.fr.tex:18 |
| 45 | 43 | blank | page 43, a tan sheet blank but for « H^1 » top right | transcripts/45/batch-03.fr.tex:12 |
| 45 | 45 | skipped, reason not classifiable | Pages skipped, without description: 42, 45, 47, 49, 51, 53, 55, 57, 59. | transcripts/45/batch-03.fr.tex:18 |
| 45 | 47 | skipped, reason not classifiable | Pages skipped, without description: 42, 45, 47, 49, 51, 53, 55, 57, 59. | transcripts/45/batch-03.fr.tex:18 |
| 45 | 49 | skipped, reason not classifiable | Pages skipped, without description: 42, 45, 47, 49, 51, 53, 55, 57, 59. | transcripts/45/batch-03.fr.tex:18 |
| 45 | 51 | skipped, reason not classifiable | Pages skipped, without description: 42, 45, 47, 49, 51, 53, 55, 57, 59. | transcripts/45/batch-03.fr.tex:18 |
| 45 | 53 | skipped, reason not classifiable | Pages skipped, without description: 42, 45, 47, 49, 51, 53, 55, 57, 59. | transcripts/45/batch-03.fr.tex:18 |
| 45 | 55 | skipped, reason not classifiable | Pages skipped, without description: 42, 45, 47, 49, 51, 53, 55, 57, 59. | transcripts/45/batch-03.fr.tex:18 |
| 45 | 57 | skipped, reason not classifiable | Pages skipped, without description: 42, 45, 47, 49, 51, 53, 55, 57, 59. | transcripts/45/batch-03.fr.tex:18 |
| 45 | 59 | skipped, reason not classifiable | Pages skipped, without description: 42, 45, 47, 49, 51, 53, 55, 57, 59. | transcripts/45/batch-03.fr.tex:18 |
| 45 | 60 | blank | page 60, a tan sheet blank but for three lines top right, read « Formes quadratiques / bilinéaires symétriques / etc » (first two words doub… | transcripts/45/batch-03.fr.tex:12 |
| 45 | 62 | skipped, reason not classifiable | Pages skipped, without description: 62, 64, 66, 68, 70, 79. | transcripts/45/batch-04.fr.tex:12 |
| 45 | 64 | skipped, reason not classifiable | Pages skipped, without description: 62, 64, 66, 68, 70, 79. | transcripts/45/batch-04.fr.tex:12 |
| 45 | 66 | skipped, reason not classifiable | Pages skipped, without description: 62, 64, 66, 68, 70, 79. | transcripts/45/batch-04.fr.tex:12 |
| 45 | 68 | skipped, reason not classifiable | Pages skipped, without description: 62, 64, 66, 68, 70, 79. | transcripts/45/batch-04.fr.tex:12 |
| 45 | 70 | skipped, reason not classifiable | Pages skipped, without description: 62, 64, 66, 68, 70, 79. | transcripts/45/batch-04.fr.tex:12 |
| 45 | 79 | skipped, reason not classifiable | Pages skipped, without description: 62, 64, 66, 68, 70, 79. | transcripts/45/batch-04.fr.tex:12 |
| 46 | 1 | cover/wrapper | page 1 (tan folder, « Schémas en groupes et fibrés principaux (Divers) ») | transcripts/46/batch-01.fr.tex:11 |
| 46 | 3 | cover/wrapper | page 3 (« p-structures sur fibrés vectoriels et sur torseurs ») | transcripts/46/batch-01.fr.tex:11 |
| 46 | 9 | cover/wrapper | page 9 (« Frobenius »). | transcripts/46/batch-01.fr.tex:11 |
| 46 | 22 | others' typescript | Pages skipped, and why: - 22: a stencilled (blue) typescript, « CHAPITRE II. | transcripts/46/batch-02.fr.tex:10 |
| 46 | 27 | cover/wrapper | Covers, no \page marker, words as headings with a \note: 27 (« Frobeniuseries pour faisceaux étales ») | transcripts/46/batch-02.fr.tex:24 |
| 46 | 34 | blank | - 34 and 36: two typed leaves (the second numbered « 11 ») on the restriction maps H^n(X,F) -> H^n(Y,h(F)) for torsion sheaves, with their a… | transcripts/46/batch-02.fr.tex:14 |
| 46 | 36 | blank | - 34 and 36: two typed leaves (the second numbered « 11 ») on the restriction maps H^n(X,F) -> H^n(Y,h(F)) for torsion sheaves, with their a… | transcripts/46/batch-02.fr.tex:14 |
| 46 | 37 | verso (unspecified) | - 38: back of a folder (the tan sheet of page 37) | transcripts/46/batch-02.fr.tex:21 |
| 46 | 38 | verso (unspecified) | - 38: back of a folder (the tan sheet of page 37) | transcripts/46/batch-02.fr.tex:21 |
| 46 | 39 | cover/wrapper | 39 (« Brauer-Severi. | transcripts/46/batch-02.fr.tex:24 |
| 46 | 41 | others' typescript | Pages skipped, and why: - 41, 43, 45: three stencilled typed leaves, « -VI-6- », « -VI-5- », « -VI-4- », each headed « n°383 », scanned upsi… | transcripts/46/batch-03.fr.tex:10 |
| 46 | 43 | others' typescript | Pages skipped, and why: - 41, 43, 45: three stencilled typed leaves, « -VI-6- », « -VI-5- », « -VI-4- », each headed « n°383 », scanned upsi… | transcripts/46/batch-03.fr.tex:10 |
| 46 | 45 | others' typescript | Pages skipped, and why: - 41, 43, 45: three stencilled typed leaves, « -VI-6- », « -VI-5- », « -VI-4- », each headed « n°383 », scanned upsi… | transcripts/46/batch-03.fr.tex:10 |
| 46 | 47 | others' typescript | - 47 (« - 3 - », « n° 399 », a corollary on divisible modules over a principal ring) and 49 (« - 59 - », « n°357 », the normalised Haar meas… | transcripts/46/batch-03.fr.tex:18 |
| 46 | 49 | others' typescript | - 47 (« - 3 - », « n° 399 », a corollary on divisible modules over a principal ring) and 49 (« - 59 - », « n°357 », the normalised Haar meas… | transcripts/46/batch-03.fr.tex:18 |
| 46 | 50 | cover/wrapper | - 54: back of the cover of page 50 | transcripts/46/batch-03.fr.tex:22 |
| 46 | 54 | cover/wrapper | - 54: back of the cover of page 50 | transcripts/46/batch-03.fr.tex:22 |
| 46 | 55 | others' typescript | no further leaf of that typescript occurs in pages 41-60. | transcripts/46/batch-03.fr.tex:24 |
| 46 | 67 | cover/wrapper | Covers, no \page marker, words as headings with a \note: 67 (tan folder, « "Restriction des scalaires" dans les groupes algébriques et leurs… | transcripts/46/batch-04.fr.tex:12 |
| 46 | 71 | cover/wrapper | 71 (grey folder, « Petits fourbis cohomologiques », the word « fourbis » flagged as doubtful in the note). | transcripts/46/batch-04.fr.tex:12 |
| 46 | 93 | cover/wrapper | Page 93 is a cover (grey folder, inscribed top right « Contre-exemples à passage au quotient », the last two words doubtful) | transcripts/46/batch-05.fr.tex:12 |
| 47 | 1 | cover/wrapper | Page 1 is a cover sheet carrying, in his hand, the title the inventory reproduces — "Produit de convolution sur les VA et transformation de … | transcripts/47/batch-01.fr.tex:6 |
| 49 | 1 | cover/wrapper | page 1 is a cover bearing only the title "Picard des schémas abéliens", so it carries no \page{} and its words open the file as the section … | transcripts/49/batch-01.fr.tex:5 |
| 50 | 1 | cover/wrapper | Page 1 is a grey wrapper carrying, in pencil in the top right corner, the four words "Sur bouquin Lang" and nothing else: it takes no \page{… | transcripts/50/batch-01.fr.tex:6 |
| 50 | 3 | others' typescript | Pages 3 and 5 are two leaves of a Bourbaki typescript on valuations (rédaction n° 280, see below), in another hand and unrelated to the note… | transcripts/50/batch-01.fr.tex:8 |
| 50 | 5 | others' typescript | Pages 3 and 5 are two leaves of a Bourbaki typescript on valuations (rédaction n° 280, see below), in another hand and unrelated to the note… | transcripts/50/batch-01.fr.tex:8 |
| 51 | 1 | blank | page 1, a sheet of buff card otherwise blank, inscribed top right in his hand « "Bonne réduction" (Shimura, Koizumi) » — a cover, whose word… | transcripts/51/batch-01.fr.tex:11 |
| 52 | 1 | cover/wrapper | Page 1 is a tan cover sheet carrying two words of his in the top right corner and nothing else, "Th. de Torelli" | transcripts/52/batch-01.fr.tex:5 |
| 53 | 1 | duplicate | Page 1 is a tan folder cover inscribed in pencil « Groupes algébriques. », repeated on its tab | transcripts/53/batch-01.fr.tex:30 |
| 53 | 16 | skipped, reason not classifiable | Pages skipped: 16-20. | transcripts/53/batch-01.fr.tex:12 |
| 53 | 17 | skipped, reason not classifiable | Pages skipped: 16-20. | transcripts/53/batch-01.fr.tex:12 |
| 53 | 18 | skipped, reason not classifiable | Pages skipped: 16-20. | transcripts/53/batch-01.fr.tex:12 |
| 53 | 19 | skipped, reason not classifiable | Pages skipped: 16-20. | transcripts/53/batch-01.fr.tex:12 |
| 53 | 20 | skipped, reason not classifiable | Pages skipped: 16-20. | transcripts/53/batch-01.fr.tex:12 |
| 54 | 1 | cover/wrapper | Page 1 is a cover in his hand, naming the run | transcripts/54/batch-01.fr.tex:5 |
| 54 | 7 | others' typescript | Page 7 is a Bourbaki typescript on chambers and walls — the recto of the leaf carrying page 6 — unrelated and untouched by him: it does not … | transcripts/54/batch-01.fr.tex:14 |
| 55 | 15 | skipped, reason not classifiable | page 15 carries nothing and is skipped, the gap in the page numbers being the record. | transcripts/55/batch-01.fr.tex:5 |
| 56 | 1 | illegible | Page 1 reads « Situation des "vanishing cycles" : [one illegible word] Cas des quadriques », with a pencilled « 3 p » that is not obviously … | transcripts/56/batch-01.fr.tex:10 |
| 56 | 8 | illegible | page 8 reads « Calculs de cohomologie des quadriques, des cônes projetants », with a pencilled « 12 p », likewise left out. | transcripts/56/batch-01.fr.tex:10 |
| 56 | 9 | blank | Pages skipped: 9 and 18, blank cream sheets with nothing on them. | transcripts/56/batch-01.fr.tex:7 |
| 56 | 18 | blank | Pages skipped: 9 and 18, blank cream sheets with nothing on them. | transcripts/56/batch-01.fr.tex:7 |
| 56 | 33 | blank | Pages skipped: 33, a blank cream sheet | transcripts/56/batch-02.fr.tex:10 |
| 56 | 38 | printed/published | 38, the back cover of the offprint, which carries only its printed colophon (« Extrait des Comptes rendus des séances de l'Académie des Scie… | transcripts/56/batch-02.fr.tex:10 |
| 57 | 1 | blank | Page 1 is blank and absent | transcripts/57/batch-01.fr.tex:11 |
| 57 | 13 | cover/wrapper | page 13 is a cover sheet in his hand (« Carré, cube, rigidité… »), which becomes the heading of the run that follows and gets no \page{}. | transcripts/57/batch-01.fr.tex:12 |
| 57 | 23 | cover/wrapper | Page 23 is a cover sheet in his hand (« Rigidité », « Groupes V »), which becomes the section heading and gets no \page{}. | transcripts/57/batch-02.fr.tex:7 |
| 57 | 35 | others' typescript | Pages 35, 37 and 39 are unrelated typed versos (a stationery price list) and are absent. | transcripts/57/batch-02.fr.tex:9 |
| 57 | 37 | others' typescript | Pages 35, 37 and 39 are unrelated typed versos (a stationery price list) and are absent. | transcripts/57/batch-02.fr.tex:9 |
| 57 | 39 | others' typescript | Pages 35, 37 and 39 are unrelated typed versos (a stationery price list) and are absent. | transcripts/57/batch-02.fr.tex:9 |
| 57 | 41 | gap only (no header mention) |  | transcripts/57/batch-03.fr.tex:1 |
| 57 | 58 | gap only (no header mention) |  | transcripts/57/batch-03.fr.tex:1 |
| 57 | 64 | cover/wrapper | Pages 64, 66 and 79 are covers inscribed in his hand | transcripts/57/batch-04.fr.tex:4 |
| 57 | 66 | cover/wrapper | Pages 64, 66 and 79 are covers inscribed in his hand | transcripts/57/batch-04.fr.tex:4 |
| 57 | 79 | cover/wrapper | Pages 64, 66 and 79 are covers inscribed in his hand | transcripts/57/batch-04.fr.tex:4 |
| 57 | 81 | blank | Absent: pp. 81, 83, 92 (typed letter openings, struck out, no mathematics), pp. 89, 94 (unrelated English typescript on theta functions, sca… | transcripts/57/batch-05.fr.tex:7 |
| 57 | 83 | blank | Absent: pp. 81, 83, 92 (typed letter openings, struck out, no mathematics), pp. 89, 94 (unrelated English typescript on theta functions, sca… | transcripts/57/batch-05.fr.tex:7 |
| 57 | 89 | blank | Absent: pp. 81, 83, 92 (typed letter openings, struck out, no mathematics), pp. 89, 94 (unrelated English typescript on theta functions, sca… | transcripts/57/batch-05.fr.tex:7 |
| 57 | 92 | blank | Absent: pp. 81, 83, 92 (typed letter openings, struck out, no mathematics), pp. 89, 94 (unrelated English typescript on theta functions, sca… | transcripts/57/batch-05.fr.tex:7 |
| 57 | 94 | blank | Absent: pp. 81, 83, 92 (typed letter openings, struck out, no mathematics), pp. 89, 94 (unrelated English typescript on theta functions, sca… | transcripts/57/batch-05.fr.tex:7 |
| 57 | 95 | cover/wrapper | Page 95 is a cover in his hand (« Critères d'équivalence »), which becomes the section heading and gets no \page{}. | transcripts/57/batch-05.fr.tex:9 |
| 57 | 97 | blank | Absent: pp. 81, 83, 92 (typed letter openings, struck out, no mathematics), pp. 89, 94 (unrelated English typescript on theta functions, sca… | transcripts/57/batch-05.fr.tex:7 |
| 57 | 103 | cover/wrapper | 103 and 114 are covers in his hand, used as section headings | transcripts/57/batch-06.fr.tex:4 |
| 57 | 114 | cover/wrapper | 103 and 114 are covers in his hand, used as section headings | transcripts/57/batch-06.fr.tex:4 |
| 57 | 116 | others' typescript | Skipped: 116 and 118 (typed versos, upside down, pages "20" and "19" of a typescript on descent, unrelated to the notes in hand, no ink of h… | transcripts/57/batch-06.fr.tex:4 |
| 57 | 118 | others' typescript | Skipped: 116 and 118 (typed versos, upside down, pages "20" and "19" of a typescript on descent, unrelated to the notes in hand, no ink of h… | transcripts/57/batch-06.fr.tex:4 |
| 57 | 124 | blank | 136 (blank). 124 and 140 are covers in his hand: their words are the section headings, without \page. | transcripts/57/batch-07.fr.tex:4 |
| 57 | 129 | others' typescript | Skipped: 129, 131, 135 (typescript versos, cohomology drafts, nothing in his hand) | transcripts/57/batch-07.fr.tex:4 |
| 57 | 131 | others' typescript | Skipped: 129, 131, 135 (typescript versos, cohomology drafts, nothing in his hand) | transcripts/57/batch-07.fr.tex:4 |
| 57 | 135 | others' typescript | Skipped: 129, 131, 135 (typescript versos, cohomology drafts, nothing in his hand) | transcripts/57/batch-07.fr.tex:4 |
| 57 | 136 | blank | 136 (blank). 124 and 140 are covers in his hand: their words are the section headings, without \page. | transcripts/57/batch-07.fr.tex:4 |
| 57 | 140 | blank | 136 (blank). 124 and 140 are covers in his hand: their words are the section headings, without \page. | transcripts/57/batch-07.fr.tex:4 |
| 57 | 142 | blank | Absent: p. 142 (typed IHES letter to a third party, no hand of his), p. 145 (blank), pp. 147, 149, 151, 155 (English typescript on analytic … | transcripts/57/batch-08.fr.tex:7 |
| 57 | 145 | blank | Absent: p. 142 (typed IHES letter to a third party, no hand of his), p. 145 (blank), pp. 147, 149, 151, 155 (English typescript on analytic … | transcripts/57/batch-08.fr.tex:7 |
| 57 | 147 | blank | Absent: p. 142 (typed IHES letter to a third party, no hand of his), p. 145 (blank), pp. 147, 149, 151, 155 (English typescript on analytic … | transcripts/57/batch-08.fr.tex:7 |
| 57 | 149 | blank | Absent: p. 142 (typed IHES letter to a third party, no hand of his), p. 145 (blank), pp. 147, 149, 151, 155 (English typescript on analytic … | transcripts/57/batch-08.fr.tex:7 |
| 57 | 151 | blank | Absent: p. 142 (typed IHES letter to a third party, no hand of his), p. 145 (blank), pp. 147, 149, 151, 155 (English typescript on analytic … | transcripts/57/batch-08.fr.tex:7 |
| 57 | 155 | blank | Absent: p. 142 (typed IHES letter to a third party, no hand of his), p. 145 (blank), pp. 147, 149, 151, 155 (English typescript on analytic … | transcripts/57/batch-08.fr.tex:7 |
| 57 | 156 | cover/wrapper | Page 156 is a cover in his hand (« Foncteurs de Picard, Diviseurs… »): it becomes the section heading and gets no \page{}. | transcripts/57/batch-08.fr.tex:10 |
| 57 | 162 | printed/published | Skipped: 162 (printed chapter opening, "Le langage des schémas") | transcripts/57/batch-09.fr.tex:3 |
| 57 | 164 | others' typescript | 164 (typescript page "- 34 -", n° 297, on topological modules) | transcripts/57/batch-09.fr.tex:3 |
| 57 | 167 | blank | 167 and 171 (blank). | transcripts/57/batch-09.fr.tex:3 |
| 57 | 171 | blank | 167 and 171 (blank). | transcripts/57/batch-09.fr.tex:3 |
| 57 | 183 | cover/wrapper | Skipped: 183 and 194 (cover sheets in his hand: their words are the section headings below) | transcripts/57/batch-10.fr.tex:4 |
| 57 | 194 | cover/wrapper | Skipped: 183 and 194 (cover sheets in his hand: their words are the section headings below) | transcripts/57/batch-10.fr.tex:4 |
| 57 | 196 | others' typescript | 196 and 198 (typed pages on dimension and the chain condition, carrying no ink of his) | transcripts/57/batch-10.fr.tex:4 |
| 57 | 198 | others' typescript | 196 and 198 (typed pages on dimension and the chain condition, carrying no ink of his) | transcripts/57/batch-10.fr.tex:4 |
| 57 | 199 | others' typescript | 199 (no writing of its own). | transcripts/57/batch-10.fr.tex:4 |
| 57 | 206 | blank | Absent: 206 (blank but for show-through) | transcripts/57/batch-11.fr.tex:7 |
| 57 | 212 | blank | 212 (blank). | transcripts/57/batch-11.fr.tex:7 |
| 57 | 222 | others' typescript | Absent: 222, 224 (typescript versos of a Bourbaki draft, n° 215, upside down) | transcripts/57/batch-12.fr.tex:9 |
| 57 | 224 | others' typescript | Absent: 222, 224 (typescript versos of a Bourbaki draft, n° 215, upside down) | transcripts/57/batch-12.fr.tex:9 |
| 57 | 225 | cover/wrapper | page 225 (a cover in his hand) gives the section heading and has no \page. | transcripts/57/batch-12.fr.tex:7 |
| 57 | 231 | blank | 231 (blank) | transcripts/57/batch-12.fr.tex:9 |
| 57 | 233 | others' typescript | 233, 235, 237, 239 (typescript versos of a Bourbaki draft « Algèbre commutative », n° 227 and n° 338). | transcripts/57/batch-12.fr.tex:9 |
| 57 | 235 | others' typescript | 233, 235, 237, 239 (typescript versos of a Bourbaki draft « Algèbre commutative », n° 227 and n° 338). | transcripts/57/batch-12.fr.tex:9 |
| 57 | 237 | others' typescript | 233, 235, 237, 239 (typescript versos of a Bourbaki draft « Algèbre commutative », n° 227 and n° 338). | transcripts/57/batch-12.fr.tex:9 |
| 57 | 239 | others' typescript | 233, 235, 237, 239 (typescript versos of a Bourbaki draft « Algèbre commutative », n° 227 and n° 338). | transcripts/57/batch-12.fr.tex:9 |
| 57 | 241 | others' typescript | Skipped: 241, 243 (Bourbaki typescript n° 227, "L'application rationnelle définie par un système linéaire") | transcripts/57/batch-13.fr.tex:3 |
| 57 | 243 | others' typescript | Skipped: 241, 243 (Bourbaki typescript n° 227, "L'application rationnelle définie par un système linéaire") | transcripts/57/batch-13.fr.tex:3 |
| 57 | 246 | blank | 246 (blank) | transcripts/57/batch-13.fr.tex:3 |
| 57 | 248 | others' typescript | 248, 250, 252, 260 (typescript pages of a Bourbaki draft on commutative algebra, versos) | transcripts/57/batch-13.fr.tex:3 |
| 57 | 250 | others' typescript | 248, 250, 252, 260 (typescript pages of a Bourbaki draft on commutative algebra, versos) | transcripts/57/batch-13.fr.tex:3 |
| 57 | 252 | others' typescript | 248, 250, 252, 260 (typescript pages of a Bourbaki draft on commutative algebra, versos) | transcripts/57/batch-13.fr.tex:3 |
| 57 | 254 | administrative | 254 (four-line private letter draft, no mathematics) | transcripts/57/batch-13.fr.tex:3 |
| 57 | 256 | others' typescript | 256, 258 (typescript "Bourbaki's Diktät", programme of a Bourbaki congress). | transcripts/57/batch-13.fr.tex:3 |
| 57 | 258 | others' typescript | 256, 258 (typescript "Bourbaki's Diktät", programme of a Bourbaki congress). | transcripts/57/batch-13.fr.tex:3 |
| 57 | 260 | others' typescript | 248, 250, 252, 260 (typescript pages of a Bourbaki draft on commutative algebra, versos) | transcripts/57/batch-13.fr.tex:3 |
| 57 | 262 | others' typescript | Skipped: 262, 264, 266, 268, 270, 272 (typed pages of a Bourbaki draft n° 227 on divisors and linear systems, pp. 8-12 and 44, no hand of hi… | transcripts/57/batch-14.fr.tex:3 |
| 57 | 264 | others' typescript | Skipped: 262, 264, 266, 268, 270, 272 (typed pages of a Bourbaki draft n° 227 on divisors and linear systems, pp. 8-12 and 44, no hand of hi… | transcripts/57/batch-14.fr.tex:3 |
| 57 | 266 | others' typescript | Skipped: 262, 264, 266, 268, 270, 272 (typed pages of a Bourbaki draft n° 227 on divisors and linear systems, pp. 8-12 and 44, no hand of hi… | transcripts/57/batch-14.fr.tex:3 |
| 57 | 268 | others' typescript | Skipped: 262, 264, 266, 268, 270, 272 (typed pages of a Bourbaki draft n° 227 on divisors and linear systems, pp. 8-12 and 44, no hand of hi… | transcripts/57/batch-14.fr.tex:3 |
| 57 | 270 | others' typescript | Skipped: 262, 264, 266, 268, 270, 272 (typed pages of a Bourbaki draft n° 227 on divisors and linear systems, pp. 8-12 and 44, no hand of hi… | transcripts/57/batch-14.fr.tex:3 |
| 57 | 272 | others' typescript | Skipped: 262, 264, 266, 268, 270, 272 (typed pages of a Bourbaki draft n° 227 on divisors and linear systems, pp. 8-12 and 44, no hand of hi… | transcripts/57/batch-14.fr.tex:3 |
| 57 | 273 | cover/wrapper | 273 is a cover sheet carrying only his title | transcripts/57/batch-14.fr.tex:5 |
| 57 | 277 | blank | 277 (blank). | transcripts/57/batch-14.fr.tex:3 |
| 57 | 281 | cover/wrapper | Absent: 281 (cover sheet in his hand, its words used as the first heading) | transcripts/57/batch-15.fr.tex:7 |
| 57 | 292 | blank | 292 (blank) | transcripts/57/batch-15.fr.tex:7 |
| 57 | 294 | others' typescript | 294, 295, 298, 300 (unrelated typescripts: a Bourbaki-type text, a third-party typescript on lim^(p), two pages of a "Tribu" report). | transcripts/57/batch-15.fr.tex:7 |
| 57 | 295 | others' typescript | 294, 295, 298, 300 (unrelated typescripts: a Bourbaki-type text, a third-party typescript on lim^(p), two pages of a "Tribu" report). | transcripts/57/batch-15.fr.tex:7 |
| 57 | 298 | others' typescript | 294, 295, 298, 300 (unrelated typescripts: a Bourbaki-type text, a third-party typescript on lim^(p), two pages of a "Tribu" report). | transcripts/57/batch-15.fr.tex:7 |
| 57 | 300 | others' typescript | 294, 295, 298, 300 (unrelated typescripts: a Bourbaki-type text, a third-party typescript on lim^(p), two pages of a "Tribu" report). | transcripts/57/batch-15.fr.tex:7 |
| 57 | 302 | others' typescript | Absent: 302, 306, 311 (typescripts with nothing of his hand on them: a Bourbaki "Tribu" report, an upside-down typed page on group prescheme… | transcripts/57/batch-16.fr.tex:7 |
| 57 | 304 | cover/wrapper | 304 and 307 (covers in his hand, whose words become section headings). | transcripts/57/batch-16.fr.tex:7 |
| 57 | 306 | others' typescript | Absent: 302, 306, 311 (typescripts with nothing of his hand on them: a Bourbaki "Tribu" report, an upside-down typed page on group prescheme… | transcripts/57/batch-16.fr.tex:7 |
| 57 | 307 | cover/wrapper | 304 and 307 (covers in his hand, whose words become section headings). | transcripts/57/batch-16.fr.tex:7 |
| 57 | 311 | others' typescript | Absent: 302, 306, 311 (typescripts with nothing of his hand on them: a Bourbaki "Tribu" report, an upside-down typed page on group prescheme… | transcripts/57/batch-16.fr.tex:7 |
| 58 | 1 | duplicate | tiles in archives/tiles/58/p1-p20. | transcripts/58/batch-01.fr.tex:2 |
| 58 | 3 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17 and 19 — the versos, which are leaves of a typescript (mostly scanned upside down: graded modules,… | transcripts/58/batch-01.fr.tex:14 |
| 58 | 5 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17 and 19 — the versos, which are leaves of a typescript (mostly scanned upside down: graded modules,… | transcripts/58/batch-01.fr.tex:14 |
| 58 | 7 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17 and 19 — the versos, which are leaves of a typescript (mostly scanned upside down: graded modules,… | transcripts/58/batch-01.fr.tex:14 |
| 58 | 9 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17 and 19 — the versos, which are leaves of a typescript (mostly scanned upside down: graded modules,… | transcripts/58/batch-01.fr.tex:14 |
| 58 | 11 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17 and 19 — the versos, which are leaves of a typescript (mostly scanned upside down: graded modules,… | transcripts/58/batch-01.fr.tex:14 |
| 58 | 13 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17 and 19 — the versos, which are leaves of a typescript (mostly scanned upside down: graded modules,… | transcripts/58/batch-01.fr.tex:14 |
| 58 | 15 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17 and 19 — the versos, which are leaves of a typescript (mostly scanned upside down: graded modules,… | transcripts/58/batch-01.fr.tex:14 |
| 58 | 17 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17 and 19 — the versos, which are leaves of a typescript (mostly scanned upside down: graded modules,… | transcripts/58/batch-01.fr.tex:14 |
| 58 | 19 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17 and 19 — the versos, which are leaves of a typescript (mostly scanned upside down: graded modules,… | transcripts/58/batch-01.fr.tex:14 |
| 58 | 21 | others' typescript | Pages skipped: 21, 23, 25 — typed leaves of a Bourbaki draft (« Algèbre commutative, Rédaction n° 355, Chapitre IV — Décomposition primaire … | transcripts/58/batch-02.fr.tex:17 |
| 58 | 23 | others' typescript | Pages skipped: 21, 23, 25 — typed leaves of a Bourbaki draft (« Algèbre commutative, Rédaction n° 355, Chapitre IV — Décomposition primaire … | transcripts/58/batch-02.fr.tex:17 |
| 58 | 25 | others' typescript | Pages skipped: 21, 23, 25 — typed leaves of a Bourbaki draft (« Algèbre commutative, Rédaction n° 355, Chapitre IV — Décomposition primaire … | transcripts/58/batch-02.fr.tex:17 |
| 58 | 27 | cover/wrapper | Page 27 is a grey cover inscribed top right « [struck word] couple de Lefschetz-Grauert (X, Y) » | transcripts/58/batch-02.fr.tex:21 |
| 58 | 28 | blank | skipped by the settled rule for typed versos. 28 — a blank cream sheet. | transcripts/58/batch-02.fr.tex:20 |
| 58 | 44 | blank | Pages skipped: 44 and 54 — blank cream sheets. 46, 48 — typed leaves of a Bourbaki draft (« II - 11 -, II - 10 -, n° 338 »: projective modul… | transcripts/58/batch-03.fr.tex:15 |
| 58 | 46 | blank | Pages skipped: 44 and 54 — blank cream sheets. 46, 48 — typed leaves of a Bourbaki draft (« II - 11 -, II - 10 -, n° 338 »: projective modul… | transcripts/58/batch-03.fr.tex:15 |
| 58 | 48 | blank | Pages skipped: 44 and 54 — blank cream sheets. 46, 48 — typed leaves of a Bourbaki draft (« II - 11 -, II - 10 -, n° 338 »: projective modul… | transcripts/58/batch-03.fr.tex:15 |
| 58 | 50 | blank | Pages skipped: 44 and 54 — blank cream sheets. 46, 48 — typed leaves of a Bourbaki draft (« II - 11 -, II - 10 -, n° 338 »: projective modul… | transcripts/58/batch-03.fr.tex:15 |
| 58 | 52 | blank | Pages skipped: 44 and 54 — blank cream sheets. 46, 48 — typed leaves of a Bourbaki draft (« II - 11 -, II - 10 -, n° 338 »: projective modul… | transcripts/58/batch-03.fr.tex:15 |
| 58 | 53 | cover/wrapper | Page 53 is a tan cover inscribed top right « Applications aux morphismes [struck word] projectifs et aux morphismes propres » | transcripts/58/batch-03.fr.tex:19 |
| 58 | 54 | blank | Pages skipped: 44 and 54 — blank cream sheets. 46, 48 — typed leaves of a Bourbaki draft (« II - 11 -, II - 10 -, n° 338 »: projective modul… | transcripts/58/batch-03.fr.tex:15 |
| 58 | 62 | others' typescript | Pages skipped: 62 — an upside-down typed leaf (page « - 7 - » of a paper on characters of finite groups: condition (B_q), Proposition 2 afte… | transcripts/58/batch-04.fr.tex:15 |
| 58 | 63 | others' typescript | skipped by the settled rule for typed versos. 63 — a cream sheet carrying only the offset of page 60 (typescript and pencil figures transfer… | transcripts/58/batch-04.fr.tex:17 |
| 59 | 21 | blank | Pages skipped: 21, a blank cream sheet carrying nothing but the faint show-through of the next leaf — no mathematics of his, skipped without… | transcripts/59/batch-02.fr.tex:13 |
| 60 | 1 | blank | Page 1 is the folder's cover, otherwise blank, inscribed top right in his hand « Notes sur l'équation fonctionnelle » (underlined) | transcripts/60/batch-01.fr.tex:17 |
| 60 | 3 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17, 19 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-01.fr.tex:13 |
| 60 | 5 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17, 19 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-01.fr.tex:13 |
| 60 | 7 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17, 19 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-01.fr.tex:13 |
| 60 | 9 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17, 19 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-01.fr.tex:13 |
| 60 | 11 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17, 19 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-01.fr.tex:13 |
| 60 | 13 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17, 19 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-01.fr.tex:13 |
| 60 | 15 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17, 19 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-01.fr.tex:13 |
| 60 | 17 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17, 19 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-01.fr.tex:13 |
| 60 | 19 | others' typescript | Pages skipped: 3, 5, 7, 9, 11, 13, 15, 17, 19 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-01.fr.tex:13 |
| 60 | 21 | others' typescript | Pages skipped: 21, 23, 25, 27, 29, 31, 33, 35, 37, 39 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-02.fr.tex:14 |
| 60 | 23 | others' typescript | Pages skipped: 21, 23, 25, 27, 29, 31, 33, 35, 37, 39 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-02.fr.tex:14 |
| 60 | 25 | others' typescript | Pages skipped: 21, 23, 25, 27, 29, 31, 33, 35, 37, 39 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-02.fr.tex:14 |
| 60 | 27 | others' typescript | Pages skipped: 21, 23, 25, 27, 29, 31, 33, 35, 37, 39 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-02.fr.tex:14 |
| 60 | 29 | others' typescript | Pages skipped: 21, 23, 25, 27, 29, 31, 33, 35, 37, 39 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-02.fr.tex:14 |
| 60 | 31 | others' typescript | Pages skipped: 21, 23, 25, 27, 29, 31, 33, 35, 37, 39 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-02.fr.tex:14 |
| 60 | 33 | others' typescript | Pages skipped: 21, 23, 25, 27, 29, 31, 33, 35, 37, 39 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-02.fr.tex:14 |
| 60 | 35 | others' typescript | Pages skipped: 21, 23, 25, 27, 29, 31, 33, 35, 37, 39 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-02.fr.tex:14 |
| 60 | 37 | others' typescript | Pages skipped: 21, 23, 25, 27, 29, 31, 33, 35, 37, 39 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-02.fr.tex:14 |
| 60 | 39 | others' typescript | Pages skipped: 21, 23, 25, 27, 29, 31, 33, 35, 37, 39 — the typed versos of the sheets (Bourbaki material | transcripts/60/batch-02.fr.tex:14 |
| 60 | 41 | others' typescript | Pages skipped: 41, 43, 45, 47, 49, 51, 53, 55, 57, 59 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 4-34 to 4-42 and 6-… | transcripts/60/batch-03.fr.tex:13 |
| 60 | 43 | others' typescript | Pages skipped: 41, 43, 45, 47, 49, 51, 53, 55, 57, 59 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 4-34 to 4-42 and 6-… | transcripts/60/batch-03.fr.tex:13 |
| 60 | 45 | others' typescript | Pages skipped: 41, 43, 45, 47, 49, 51, 53, 55, 57, 59 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 4-34 to 4-42 and 6-… | transcripts/60/batch-03.fr.tex:13 |
| 60 | 47 | others' typescript | Pages skipped: 41, 43, 45, 47, 49, 51, 53, 55, 57, 59 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 4-34 to 4-42 and 6-… | transcripts/60/batch-03.fr.tex:13 |
| 60 | 49 | others' typescript | Pages skipped: 41, 43, 45, 47, 49, 51, 53, 55, 57, 59 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 4-34 to 4-42 and 6-… | transcripts/60/batch-03.fr.tex:13 |
| 60 | 51 | others' typescript | Pages skipped: 41, 43, 45, 47, 49, 51, 53, 55, 57, 59 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 4-34 to 4-42 and 6-… | transcripts/60/batch-03.fr.tex:13 |
| 60 | 53 | others' typescript | Pages skipped: 41, 43, 45, 47, 49, 51, 53, 55, 57, 59 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 4-34 to 4-42 and 6-… | transcripts/60/batch-03.fr.tex:13 |
| 60 | 55 | others' typescript | Pages skipped: 41, 43, 45, 47, 49, 51, 53, 55, 57, 59 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 4-34 to 4-42 and 6-… | transcripts/60/batch-03.fr.tex:13 |
| 60 | 57 | others' typescript | Pages skipped: 41, 43, 45, 47, 49, 51, 53, 55, 57, 59 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 4-34 to 4-42 and 6-… | transcripts/60/batch-03.fr.tex:13 |
| 60 | 59 | others' typescript | Pages skipped: 41, 43, 45, 47, 49, 51, 53, 55, 57, 59 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 4-34 to 4-42 and 6-… | transcripts/60/batch-03.fr.tex:13 |
| 60 | 61 | others' typescript | Pages skipped: 61, 63, 65, 67, 69 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 6-45, 6-35, 6-34, 6-33, 6-32: exercises… | transcripts/60/batch-04.fr.tex:13 |
| 60 | 63 | others' typescript | Pages skipped: 61, 63, 65, 67, 69 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 6-45, 6-35, 6-34, 6-33, 6-32: exercises… | transcripts/60/batch-04.fr.tex:13 |
| 60 | 65 | others' typescript | Pages skipped: 61, 63, 65, 67, 69 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 6-45, 6-35, 6-34, 6-33, 6-32: exercises… | transcripts/60/batch-04.fr.tex:13 |
| 60 | 67 | others' typescript | Pages skipped: 61, 63, 65, 67, 69 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 6-45, 6-35, 6-34, 6-33, 6-32: exercises… | transcripts/60/batch-04.fr.tex:13 |
| 60 | 69 | others' typescript | Pages skipped: 61, 63, 65, 67, 69 — the typed versos of the sheets (Bourbaki rédaction n° 392, pages 6-45, 6-35, 6-34, 6-33, 6-32: exercises… | transcripts/60/batch-04.fr.tex:13 |
| 62 | 1 | cover/wrapper | Page 1 is a tan cover inscribed top right « Courbes elliptiques » | transcripts/62/batch-01.fr.tex:14 |
| 62 | 2 | blank | Pages skipped: 2 and 17, blank cream sheets (show-through only) | transcripts/62/batch-01.fr.tex:11 |
| 62 | 17 | blank | Pages skipped: 2 and 17, blank cream sheets (show-through only) | transcripts/62/batch-01.fr.tex:11 |
| 62 | 19 | others' typescript | 19, the upside-down leaf of a typescript (« - 20 - », « n° 276 », §2 « Anneaux m-adiques noethériens », Artin-Rees) with nothing in his hand… | transcripts/62/batch-01.fr.tex:11 |
| 62 | 25 | others' typescript | Pages skipped: 25, 28, 30, 32, 34, 36, 38 and 40, typed leaves (the other sides of the sheets he wrote on) with nothing of his mathematics | transcripts/62/batch-02.fr.tex:9 |
| 62 | 26 | blank | Page 26 is a blank sheet. | transcripts/62/batch-02.fr.tex:13 |
| 62 | 28 | others' typescript | Pages skipped: 25, 28, 30, 32, 34, 36, 38 and 40, typed leaves (the other sides of the sheets he wrote on) with nothing of his mathematics | transcripts/62/batch-02.fr.tex:9 |
| 62 | 30 | others' typescript | Pages skipped: 25, 28, 30, 32, 34, 36, 38 and 40, typed leaves (the other sides of the sheets he wrote on) with nothing of his mathematics | transcripts/62/batch-02.fr.tex:9 |
| 62 | 32 | others' typescript | Pages skipped: 25, 28, 30, 32, 34, 36, 38 and 40, typed leaves (the other sides of the sheets he wrote on) with nothing of his mathematics | transcripts/62/batch-02.fr.tex:9 |
| 62 | 34 | others' typescript | Pages skipped: 25, 28, 30, 32, 34, 36, 38 and 40, typed leaves (the other sides of the sheets he wrote on) with nothing of his mathematics | transcripts/62/batch-02.fr.tex:9 |
| 62 | 36 | others' typescript | Pages skipped: 25, 28, 30, 32, 34, 36, 38 and 40, typed leaves (the other sides of the sheets he wrote on) with nothing of his mathematics | transcripts/62/batch-02.fr.tex:9 |
| 62 | 38 | others' typescript | Pages skipped: 25, 28, 30, 32, 34, 36, 38 and 40, typed leaves (the other sides of the sheets he wrote on) with nothing of his mathematics | transcripts/62/batch-02.fr.tex:9 |
| 62 | 40 | others' typescript | Pages skipped: 25, 28, 30, 32, 34, 36, 38 and 40, typed leaves (the other sides of the sheets he wrote on) with nothing of his mathematics | transcripts/62/batch-02.fr.tex:9 |
| 62 | 44 | others' typescript | Pages skipped: 44, 48, 50, 52, 54 — leaves of the same unrelated typescript as batch 1's page 19 and batch 2's pp. 21-40 (« n° 276 », typed … | transcripts/62/batch-03.fr.tex:12 |
| 62 | 48 | others' typescript | Pages skipped: 44, 48, 50, 52, 54 — leaves of the same unrelated typescript as batch 1's page 19 and batch 2's pp. 21-40 (« n° 276 », typed … | transcripts/62/batch-03.fr.tex:12 |
| 62 | 50 | others' typescript | Pages skipped: 44, 48, 50, 52, 54 — leaves of the same unrelated typescript as batch 1's page 19 and batch 2's pp. 21-40 (« n° 276 », typed … | transcripts/62/batch-03.fr.tex:12 |
| 62 | 52 | others' typescript | Pages skipped: 44, 48, 50, 52, 54 — leaves of the same unrelated typescript as batch 1's page 19 and batch 2's pp. 21-40 (« n° 276 », typed … | transcripts/62/batch-03.fr.tex:12 |
| 62 | 54 | others' typescript | Pages skipped: 44, 48, 50, 52, 54 — leaves of the same unrelated typescript as batch 1's page 19 and batch 2's pp. 21-40 (« n° 276 », typed … | transcripts/62/batch-03.fr.tex:12 |
| 62 | 55 | blank | 55, a blank sheet. | transcripts/62/batch-03.fr.tex:12 |
| 62 | 58 | cover/wrapper | Page 58 is a tan cover sheet inscribed in pencil top right « Théorie transcendante (Généralités classiques) »: no \page marker, its words be… | transcripts/62/batch-03.fr.tex:23 |
| 63 | 1 | blank | Pages skipped: 1 and 14, blank cream sheets (nothing written on them). | transcripts/63/batch-01.fr.tex:10 |
| 63 | 14 | blank | Pages skipped: 1 and 14, blank cream sheets (nothing written on them). | transcripts/63/batch-01.fr.tex:10 |
| 63 | 34 | blank | Pages skipped: 34, a blank sheet. | transcripts/63/batch-02.fr.tex:12 |
| 63 | 55 | blank | Pages skipped: 55, a blank cream sheet. | transcripts/63/batch-03.fr.tex:12 |
| 63 | 64 | blank | Pages skipped: - 64 and 78, blank cream sheets. | transcripts/63/batch-04.fr.tex:12 |
| 63 | 67 | others' typescript | - 67, 69, 71: typed versos of the yellowed sheets carrying pp. 66, 68, 70 (Bourbaki drafts, « n° 357 » p. 19 on integration of representatio… | transcripts/63/batch-04.fr.tex:14 |
| 63 | 69 | others' typescript | - 67, 69, 71: typed versos of the yellowed sheets carrying pp. 66, 68, 70 (Bourbaki drafts, « n° 357 » p. 19 on integration of representatio… | transcripts/63/batch-04.fr.tex:14 |
| 63 | 71 | others' typescript | - 67, 69, 71: typed versos of the yellowed sheets carrying pp. 66, 68, 70 (Bourbaki drafts, « n° 357 » p. 19 on integration of representatio… | transcripts/63/batch-04.fr.tex:14 |
| 63 | 73 | others' typescript | - 73 and 77: typed leaves of a draft of the SGA 4 Avant-propos (the bibliography page ending « GT », and typed p. 1 « AVANT-PROPOS »), on th… | transcripts/63/batch-04.fr.tex:18 |
| 63 | 77 | others' typescript | - 73 and 77: typed leaves of a draft of the SGA 4 Avant-propos (the bibliography page ending « GT », and typed p. 1 « AVANT-PROPOS »), on th… | transcripts/63/batch-04.fr.tex:18 |
| 63 | 78 | blank | Pages skipped: - 64 and 78, blank cream sheets. | transcripts/63/batch-04.fr.tex:12 |
| 63 | 81 | blank | Pages skipped: 81, 85 and 94, blank cream separator sheets | transcripts/63/batch-05.fr.tex:10 |
| 63 | 85 | blank | Pages skipped: 81, 85 and 94, blank cream separator sheets | transcripts/63/batch-05.fr.tex:10 |
| 63 | 94 | blank | Pages skipped: 81, 85 and 94, blank cream separator sheets | transcripts/63/batch-05.fr.tex:10 |
| 63 | 96 | administrative | 96, a handwritten letter to him (signed Carlos Ruiz, dated « Wattignies 9/III/68 »), not mathematics — its date is recorded in one \note on … | transcripts/63/batch-05.fr.tex:10 |
| 63 | 100 | others' typescript | 100, a single typed page on the specialisation of cycles ((7.10.1), (7.11.1), (7.11.2), A^.(X_t) -> A^.(X_s)), cancelled by one long diagona… | transcripts/63/batch-05.fr.tex:10 |
| 64 | 1 | cover/wrapper | Page 1 is a cover in his hand (large roman « I », title « Fourbis combinatoires (ens. à 4 éléments, cubes, octaèdres, modules libres de rang… | transcripts/64/batch-01.fr.tex:12 |
| 64 | 40 | others' typescript | Pages skipped: 40 (an unrelated typed administrative letter, no mathematics). | transcripts/64/batch-02.fr.tex:8 |
| 64 | 43 | cover/wrapper | Pages skipped: 43 (a cover sheet in his hand, « (25 p.) II Structures octaédrales dans P1 » | transcripts/64/batch-03.fr.tex:8 |
| 64 | 69 | skipped, reason not classifiable | Pages skipped: 69 (a coloured sheet bearing only his title « III. | transcripts/64/batch-04.fr.tex:8 |
| 64 | 100 | blank | Page 100 is a blank sheet carrying only a heading in his hand ("IV Descriptions explicites par fonctions P de Weierstrass") | transcripts/64/batch-05.fr.tex:8 |
| 64 | 121 | blank | Pages skipped: 121 (blank, show-through of 122) | transcripts/64/batch-07.fr.tex:8 |
| 64 | 123 | others' typescript | 123 (typed USTL thesis-defence notice) | transcripts/64/batch-07.fr.tex:8 |
| 64 | 126 | others' typescript | 126 (typed USTL seminar announcement) | transcripts/64/batch-07.fr.tex:8 |
| 64 | 127 | cover/wrapper | Pages 127 and 128 are covers in his hand | transcripts/64/batch-07.fr.tex:9 |
| 64 | 128 | cover/wrapper | Pages 127 and 128 are covers in his hand | transcripts/64/batch-07.fr.tex:9 |
| 64 | 129 | blank | 129 (blank). | transcripts/64/batch-07.fr.tex:8 |
| 64 | 141 | blank | Pages skipped: 141 (blank sheet) | transcripts/64/batch-08.fr.tex:8 |
| 64 | 152 | blank | 152 (blank sheet). | transcripts/64/batch-08.fr.tex:8 |
| 67 | 1 | administrative | primitive class in π_1 | transcripts/67/batch-01.fr.tex:31 |
| 67 | 7 | others' typescript | 7      Unrelated typed verso (a list of plots of land). | transcripts/67/batch-01.fr.tex:30 |
| 67 | 11 | administrative | 8-13   Scratch on envelopes: three successive drafts (8, 10, 12) of one list of six equivalent data — elliptic curve with oriented closed ge… | transcripts/67/batch-01.fr.tex:31 |
| 67 | 14 | blank | 14     Blank. | transcripts/67/batch-01.fr.tex:40 |
| 67 | 22 | blank | 22     Blank. | transcripts/67/batch-02.fr.tex:24 |
| 67 | 23 | printed/published | 23     Cover in his hand, top right, on the back of a computer listing: « Métriques canoniques sur les surfaces conformes ». | transcripts/67/batch-02.fr.tex:25 |
| 67 | 46 | blank | Pages 46 and 51 are blank leaves and are absent. \page{} numbers the position in the folder, as batches 1 and 4 do: the archivists' pencil n… | transcripts/67/batch-03.fr.tex:18 |
| 67 | 51 | blank | Pages 46 and 51 are blank leaves and are absent. \page{} numbers the position in the folder, as batches 1 and 4 do: the archivists' pencil n… | transcripts/67/batch-03.fr.tex:18 |
| 67 | 82 | blank | 82, 89  Blank. | transcripts/67/batch-05.fr.tex:21 |
| 67 | 89 | blank | 82, 89  Blank. | transcripts/67/batch-05.fr.tex:21 |
| 68 | 17 | others' typescript | Page 17 is a typed administrative table (promotions list) and is skipped. | transcripts/68/batch-01.fr.tex:34 |
| 68 | 22 | blank | 22     Blank. | transcripts/68/batch-02.fr.tex:24 |
| 68 | 34 | blank | 34     Blank. | transcripts/68/batch-02.fr.tex:36 |
| 68 | 46 | blank | 46, 48 Blank. | transcripts/68/batch-03.fr.tex:23 |
| 68 | 48 | blank | 46, 48 Blank. | transcripts/68/batch-03.fr.tex:23 |
| 68 | 50 | others' typescript | 50, 52, 54  Three copies of a typescript page headed « XVIII Les épousailles (2) » (paired words: lumière et ombre, …), with handwritten cor… | transcripts/68/batch-03.fr.tex:35 |
| 68 | 52 | others' typescript | 50, 52, 54  Three copies of a typescript page headed « XVIII Les épousailles (2) » (paired words: lumière et ombre, …), with handwritten cor… | transcripts/68/batch-03.fr.tex:35 |
| 68 | 54 | others' typescript | 50, 52, 54  Three copies of a typescript page headed « XVIII Les épousailles (2) » (paired words: lumière et ombre, …), with handwritten cor… | transcripts/68/batch-03.fr.tex:35 |
| 69 | 1 | cover/wrapper | Pages skipped: 1, a tan cover sheet bearing only a pencilled « (34p) » top right (a page count, not a heading, and not certainly his), so it… | transcripts/69/batch-01.fr.tex:13 |
| 69 | 40 | skipped, reason not classifiable | Pages skipped: 40, a pink separator sheet (only a pencilled « (23 p) » top right, a page count, not certainly his). | transcripts/69/batch-02.fr.tex:13 |
| 69 | 64 | illegible | page 64, a pink separator sheet | transcripts/69/batch-04.fr.tex:13 |
| 69 | 65 | illegible | pages 65, 72 and 76, cream separator sheets bearing only show-through of the neighbouring leaves. | transcripts/69/batch-04.fr.tex:13 |
| 69 | 72 | illegible | pages 65, 72 and 76, cream separator sheets bearing only show-through of the neighbouring leaves. | transcripts/69/batch-04.fr.tex:13 |
| 69 | 76 | illegible | pages 65, 72 and 76, cream separator sheets bearing only show-through of the neighbouring leaves. | transcripts/69/batch-04.fr.tex:13 |
| 69 | 88 | blank | Pages skipped: 88, 93, 94 and 99, blank cream separator sheets (only show-through). | transcripts/69/batch-05.fr.tex:19 |
| 69 | 93 | blank | Pages skipped: 88, 93, 94 and 99, blank cream separator sheets (only show-through). | transcripts/69/batch-05.fr.tex:19 |
| 69 | 94 | blank | Pages skipped: 88, 93, 94 and 99, blank cream separator sheets (only show-through). | transcripts/69/batch-05.fr.tex:19 |
| 69 | 99 | blank | Pages skipped: 88, 93, 94 and 99, blank cream separator sheets (only show-through). | transcripts/69/batch-05.fr.tex:19 |
| 69 | 104 | blank | Pages skipped: 104 and 106, blank cream separator sheets. | transcripts/69/batch-06.fr.tex:19 |
| 69 | 106 | blank | Pages skipped: 104 and 106, blank cream separator sheets. | transcripts/69/batch-06.fr.tex:19 |
| 70 | 1 | cover/wrapper | Pages 1 and 2 are covers inscribed in pencil | transcripts/70/batch-01.fr.tex:7 |
| 70 | 2 | cover/wrapper | Pages 1 and 2 are covers inscribed in pencil | transcripts/70/batch-01.fr.tex:7 |
| 70 | 26 | unrelated | Pages 26, 27 and 37 carry no mathematics and are absent. | transcripts/70/batch-02.fr.tex:4 |
| 70 | 27 | unrelated | Pages 26, 27 and 37 carry no mathematics and are absent. | transcripts/70/batch-02.fr.tex:4 |
| 70 | 28 | cover/wrapper | Pages 28 and 38 are covers in his hand: no \page{}, their words become section headings. | transcripts/70/batch-02.fr.tex:4 |
| 70 | 37 | unrelated | Pages 26, 27 and 37 carry no mathematics and are absent. | transcripts/70/batch-02.fr.tex:4 |
| 70 | 38 | cover/wrapper | Pages 28 and 38 are covers in his hand: no \page{}, their words become section headings. | transcripts/70/batch-02.fr.tex:4 |
| 70 | 48 | blank | Pages skipped: 48 (blank) | transcripts/70/batch-03.fr.tex:21 |
| 70 | 49 | cover/wrapper | p. 41 opens mid-argument and p. 47 breaks off mid-sentence. pp. 49 and 50 are his covers (« 2 – Polyèdres réguliers. | transcripts/70/batch-03.fr.tex:14 |
| 70 | 50 | cover/wrapper | p. 41 opens mid-argument and p. 47 breaks off mid-sentence. pp. 49 and 50 are his covers (« 2 – Polyèdres réguliers. | transcripts/70/batch-03.fr.tex:14 |
| 70 | 57 | administrative | 57 (a draft letter in his hand, cancelled by two diagonals — not mathematics) | transcripts/70/batch-03.fr.tex:21 |
| 70 | 60 | blank | 60 (blank but for faint offset of another sheet's text). | transcripts/70/batch-03.fr.tex:21 |
| 70 | 63 | blank | Skipped as carrying no mathematics: 63 (a blank verso showing the ink of p. 62 through the paper) | transcripts/70/batch-04.fr.tex:4 |
| 70 | 72 | blank | 72 (blank coloured separator sheet) | transcripts/70/batch-04.fr.tex:4 |
| 70 | 73 | cover/wrapper | Page 73 is a cover inscribed in his hand | transcripts/70/batch-04.fr.tex:6 |
| 70 | 77 | others' typescript | 77 and 79 (typed administrative versos). | transcripts/70/batch-04.fr.tex:4 |
| 70 | 79 | others' typescript | 77 and 79 (typed administrative versos). | transcripts/70/batch-04.fr.tex:4 |
| 70 | 81 | gap only (no header mention) |  | transcripts/70/batch-05.fr.tex:1 |
| 70 | 112 | blank | Page 112 is a blank pink sheet and is absent. | transcripts/70/batch-06.fr.tex:11 |
| 70 | 113 | cover/wrapper | Page 113 is a pink cover inscribed in his hand « Position du pb des 2-polyèdres réguliers / vieille rédaction » and « (10 p) » | transcripts/70/batch-06.fr.tex:12 |
| 70 | 124 | blank | Page 124 is an unrelated typed verso (a USTL letter stamped 17 JUN 1976 — consistent with the inventory's "[à partir de 1976]") and page 125… | transcripts/70/batch-07.fr.tex:16 |
| 70 | 125 | blank | Page 124 is an unrelated typed verso (a USTL letter stamped 17 JUN 1976 — consistent with the inventory's "[à partir de 1976]") and page 125… | transcripts/70/batch-07.fr.tex:16 |
| 71 | 1 | blank | pages 1, 4, 15, 17 and 19, blank cream sheets (separators, bearing only the pencilled number) | transcripts/71/batch-01.fr.tex:11 |
| 71 | 3 | others' typescript | 2026-10-20 — dates checked on the facsimile by Michel Hua (#74–76): pp. 3 and 14, the typed notices are dated « Montpellier, 19 avril 1977 »… | transcripts/71/batch-01.fr.tex:9 |
| 71 | 4 | blank | pages 1, 4, 15, 17 and 19, blank cream sheets (separators, bearing only the pencilled number) | transcripts/71/batch-01.fr.tex:11 |
| 71 | 8 | printed/published | page 8, a printed Crédit Lyonnais leaflet dated « Janvier 1978 », upside down, with nothing in his hand. | transcripts/71/batch-01.fr.tex:13 |
| 71 | 14 | others' typescript | 2026-10-20 — dates checked on the facsimile by Michel Hua (#74–76): pp. 3 and 14, the typed notices are dated « Montpellier, 19 avril 1977 »… | transcripts/71/batch-01.fr.tex:9 |
| 71 | 15 | blank | pages 1, 4, 15, 17 and 19, blank cream sheets (separators, bearing only the pencilled number) | transcripts/71/batch-01.fr.tex:11 |
| 71 | 17 | blank | pages 1, 4, 15, 17 and 19, blank cream sheets (separators, bearing only the pencilled number) | transcripts/71/batch-01.fr.tex:11 |
| 71 | 19 | blank | pages 1, 4, 15, 17 and 19, blank cream sheets (separators, bearing only the pencilled number) | transcripts/71/batch-01.fr.tex:11 |
| 71 | 25 | blank | Absent (no \page): 25, 34 and 40, versos of the mémoire blank but for an abandoned start in its author's hand, upside down at the foot. | transcripts/71/batch-02.fr.tex:32 |
| 71 | 34 | blank | Absent (no \page): 25, 34 and 40, versos of the mémoire blank but for an abandoned start in its author's hand, upside down at the foot. | transcripts/71/batch-02.fr.tex:32 |
| 71 | 40 | blank | Absent (no \page): 25, 34 and 40, versos of the mémoire blank but for an abandoned start in its author's hand, upside down at the foot. | transcripts/71/batch-02.fr.tex:32 |
| 71 | 45 | verso (unspecified) | page 45, the verso of the leaf of page 44 — two pencil drawings of non-convex polygons (vertices s', s, s'') and, upside down at its foot, a… | transcripts/71/batch-03.fr.tex:25 |
| 72 | 1 | cover/wrapper | The raw scan's cover sheet was removed from the batch PDF: PDF page k is archivists' page k, and the pencilled numbers bottom-left (« 1 » ..… | transcripts/72/batch-01.fr.tex:8 |
| 72 | 21 | blank | Pages skipped: 21, a blank tan wrapper sheet with nothing of his. | transcripts/72/batch-02.fr.tex:12 |
| 72 | 26 | gap only (no header mention) |  | transcripts/72/batch-02.fr.tex:1 |
| 72 | 30 | gap only (no header mention) |  | transcripts/72/batch-02.fr.tex:1 |
| 72 | 31 | gap only (no header mention) |  | transcripts/72/batch-02.fr.tex:1 |
| 72 | 36 | gap only (no header mention) |  | transcripts/72/batch-02.fr.tex:1 |
| 72 | 43 | cover/wrapper | page 43, a wrapper sheet inscribed top right in his hand « Calculs de discriminants etc. », and page 55, a pink wrapper sheet inscribed top … | transcripts/72/batch-03.fr.tex:13 |
| 72 | 55 | cover/wrapper | page 43, a wrapper sheet inscribed top right in his hand « Calculs de discriminants etc. », and page 55, a pink wrapper sheet inscribed top … | transcripts/72/batch-03.fr.tex:13 |
| 72 | 59 | others' typescript | Page 59, a typed USTL « avis de soutenance » (thèse de 3e cycle in biochemistry) dated Montpellier, 26 juin 1978, upside down, with nothing … | transcripts/72/batch-03.fr.tex:17 |
| 72 | 61 | others' typescript | pages 61, 63, 65, 67 and 69, typed USTL documents (avis de soutenance dated 1er and 3 juillet and 28 juin 1978, a « Recueil n° 16 » of Conse… | transcripts/72/batch-04.fr.tex:11 |
| 72 | 63 | others' typescript | pages 61, 63, 65, 67 and 69, typed USTL documents (avis de soutenance dated 1er and 3 juillet and 28 juin 1978, a « Recueil n° 16 » of Conse… | transcripts/72/batch-04.fr.tex:11 |
| 72 | 65 | others' typescript | pages 61, 63, 65, 67 and 69, typed USTL documents (avis de soutenance dated 1er and 3 juillet and 28 juin 1978, a « Recueil n° 16 » of Conse… | transcripts/72/batch-04.fr.tex:11 |
| 72 | 67 | others' typescript | pages 61, 63, 65, 67 and 69, typed USTL documents (avis de soutenance dated 1er and 3 juillet and 28 juin 1978, a « Recueil n° 16 » of Conse… | transcripts/72/batch-04.fr.tex:11 |
| 72 | 69 | others' typescript | pages 61, 63, 65, 67 and 69, typed USTL documents (avis de soutenance dated 1er and 3 juillet and 28 juin 1978, a « Recueil n° 16 » of Conse… | transcripts/72/batch-04.fr.tex:11 |
| 72 | 71 | gap only (no header mention) |  | transcripts/72/batch-04.fr.tex:1 |
| 72 | 78 | gap only (no header mention) |  | transcripts/72/batch-04.fr.tex:1 |
| 72 | 83 | cover/wrapper | Pages 84-90 (after the cover of page 83): a regular combinatorial n-carte C with automorphism group G, its repères R a G-torsor, generators … | transcripts/72/batch-05.fr.tex:51 |
| 72 | 95 | cover/wrapper | Pages 96-100 (after the cover of page 95): Théorème, for pseudo-reflections tau_i of a k-module E and s_0 ∈ E, with s_i, E_i, lambda_i: cond… | transcripts/72/batch-05.fr.tex:63 |
| 72 | 106 | gap only (no header mention) |  | transcripts/72/batch-06.fr.tex:1 |
| 73 | 2 | illegible | Pages skipped: 2, 7, 11 and 13, cream sheets carrying nothing but the show-through of the neighbouring leaf. | transcripts/73/batch-01.fr.tex:26 |
| 73 | 7 | illegible | Pages skipped: 2, 7, 11 and 13, cream sheets carrying nothing but the show-through of the neighbouring leaf. | transcripts/73/batch-01.fr.tex:26 |
| 73 | 11 | illegible | Pages skipped: 2, 7, 11 and 13, cream sheets carrying nothing but the show-through of the neighbouring leaf. | transcripts/73/batch-01.fr.tex:26 |
| 73 | 13 | illegible | Pages skipped: 2, 7, 11 and 13, cream sheets carrying nothing but the show-through of the neighbouring leaf. | transcripts/73/batch-01.fr.tex:26 |
| 74 | 2 | blank | Pages absent: 2, 4, 7, 9, 11, 17, 19 (blank, or no mathematics). | transcripts/74/batch-01.fr.tex:6 |
| 74 | 4 | blank | Pages absent: 2, 4, 7, 9, 11, 17, 19 (blank, or no mathematics). | transcripts/74/batch-01.fr.tex:6 |
| 74 | 7 | blank | Pages absent: 2, 4, 7, 9, 11, 17, 19 (blank, or no mathematics). | transcripts/74/batch-01.fr.tex:6 |
| 74 | 9 | blank | Pages absent: 2, 4, 7, 9, 11, 17, 19 (blank, or no mathematics). | transcripts/74/batch-01.fr.tex:6 |
| 74 | 11 | blank | Pages absent: 2, 4, 7, 9, 11, 17, 19 (blank, or no mathematics). | transcripts/74/batch-01.fr.tex:6 |
| 74 | 17 | blank | Pages absent: 2, 4, 7, 9, 11, 17, 19 (blank, or no mathematics). | transcripts/74/batch-01.fr.tex:6 |
| 74 | 19 | blank | Pages absent: 2, 4, 7, 9, 11, 17, 19 (blank, or no mathematics). | transcripts/74/batch-01.fr.tex:6 |
| 74 | 24 | gap only (no header mention) |  | transcripts/74/batch-02.fr.tex:1 |
| 74 | 31 | gap only (no header mention) |  | transcripts/74/batch-02.fr.tex:1 |
| 74 | 34 | gap only (no header mention) |  | transcripts/74/batch-02.fr.tex:1 |
| 74 | 36 | gap only (no header mention) |  | transcripts/74/batch-02.fr.tex:1 |
| 74 | 40 | gap only (no header mention) |  | transcripts/74/batch-02.fr.tex:1 |
| 74 | 42 | blank | Skipped: p. 42 and p. 45 (blank covers carrying only a pencilled number) | transcripts/74/batch-03.fr.tex:5 |
| 74 | 45 | blank | Skipped: p. 42 and p. 45 (blank covers carrying only a pencilled number) | transcripts/74/batch-03.fr.tex:5 |
| 74 | 67 | blank | Pages 67 (typed Bourbaki seminar programme, no hand) and 71 (blank coloured separator sheet) carry no mathematics and are skipped. | transcripts/74/batch-04.fr.tex:4 |
| 74 | 71 | blank | Pages 67 (typed Bourbaki seminar programme, no hand) and 71 (blank coloured separator sheet) carry no mathematics and are skipped. | transcripts/74/batch-04.fr.tex:4 |
| 74 | 91 | gap only (no header mention) |  | transcripts/74/batch-05.fr.tex:1 |
| 74 | 126 | blank | Skipped: p. 126 (blank coloured sheet, only a pencilled "(9p)" not in his hand). | transcripts/74/batch-07.fr.tex:4 |
| 75 | 1 | cover/wrapper | Page 1 is the folder's cover, inscribed in pencil along the right edge « C4 DEA — Géométrie combinatoire », with « (24 p) » above | transcripts/75/batch-01.fr.tex:19 |
| 75 | 28 | others' typescript | Pages skipped: 28 and 29 — two copies (the first a faint carbon, the second a photocopy with a pencil scrawl across it) of a typed letter si… | transcripts/75/batch-02.fr.tex:13 |
| 75 | 29 | others' typescript | Pages skipped: 28 and 29 — two copies (the first a faint carbon, the second a photocopy with a pencil scrawl across it) of a typed letter si… | transcripts/75/batch-02.fr.tex:13 |
| 76 | 1 | blank | Pages skipped: 1, 10 and 14, blank sheets (1 and 14 cream, with only show-through | transcripts/76/batch-01.fr.tex:18 |
| 76 | 10 | blank | Pages skipped: 1, 10 and 14, blank sheets (1 and 14 cream, with only show-through | transcripts/76/batch-01.fr.tex:18 |
| 76 | 14 | blank | Pages skipped: 1, 10 and 14, blank sheets (1 and 14 cream, with only show-through | transcripts/76/batch-01.fr.tex:18 |
| 76 | 34 | blank | Pages skipped: 34, a blank cream sheet (it separates two runs). | transcripts/76/batch-02.fr.tex:19 |
| 76 | 43 | cover/wrapper | Page 43 is a cover in his hand (« 2-cartes cellulaires » struck, « cube combinatoire » above | transcripts/76/batch-03.fr.tex:19 |
| 76 | 44 | blank | Pages skipped: 44 and 48 (blank) | transcripts/76/batch-03.fr.tex:18 |
| 76 | 46 | blank | 46 (blank but for show-through of p. 47). | transcripts/76/batch-03.fr.tex:18 |
| 76 | 48 | blank | Pages skipped: 44 and 48 (blank) | transcripts/76/batch-03.fr.tex:18 |
| 77 | 1 | cover/wrapper | Pages 1, 6 and 20 are covers inscribed in his hand | transcripts/77/batch-01.fr.tex:4 |
| 77 | 6 | cover/wrapper | Pages 1, 6 and 20 are covers inscribed in his hand | transcripts/77/batch-01.fr.tex:4 |
| 77 | 20 | cover/wrapper | Pages 1, 6 and 20 are covers inscribed in his hand | transcripts/77/batch-01.fr.tex:4 |
| 77 | 64 | cover/wrapper | Page 64 is a cover sheet in his hand | transcripts/77/batch-04.fr.tex:5 |
| 77 | 70 | others' typescript | Pages 70, 72, 74, 76, 78 and 80 are unrelated typed versos and are not transcribed. | transcripts/77/batch-04.fr.tex:4 |
| 77 | 72 | others' typescript | Pages 70, 72, 74, 76, 78 and 80 are unrelated typed versos and are not transcribed. | transcripts/77/batch-04.fr.tex:4 |
| 77 | 74 | others' typescript | Pages 70, 72, 74, 76, 78 and 80 are unrelated typed versos and are not transcribed. | transcripts/77/batch-04.fr.tex:4 |
| 77 | 76 | others' typescript | Pages 70, 72, 74, 76, 78 and 80 are unrelated typed versos and are not transcribed. | transcripts/77/batch-04.fr.tex:4 |
| 77 | 78 | others' typescript | Pages 70, 72, 74, 76, 78 and 80 are unrelated typed versos and are not transcribed. | transcripts/77/batch-04.fr.tex:4 |
| 77 | 80 | others' typescript | Pages 70, 72, 74, 76, 78 and 80 are unrelated typed versos and are not transcribed. | transcripts/77/batch-04.fr.tex:4 |
| 77 | 82 | others' typescript | Page 82 is an unrelated typed verso (administrative notice) and is skipped. | transcripts/77/batch-05.fr.tex:4 |
| 77 | 126 | cover/wrapper | Page 126 is a cover sheet in his hand (no \page | transcripts/77/batch-07.fr.tex:4 |
| 78 | 49 | cover/wrapper | Page 49 is a cover in his hand (« Cours / Polygones réguliers / II »), which becomes the section heading | transcripts/78/batch-03.fr.tex:8 |
| 78 | 53 | blank | page 53 is a blank sheet of Institut de mathématiques letterhead. | transcripts/78/batch-03.fr.tex:8 |
| 78 | 93 | others' typescript | Page 93 is an unrelated typed letter (from Jean-Pierre Aubin, CEREMADE, Paris, 10 November 1977, the sender read on the facsimile by Michel … | transcripts/78/batch-05.fr.tex:9 |
| 78 | 108 | cover/wrapper | Page 108 is a pink folder cover inscribed « Polynômes cyclotomiques » | transcripts/78/batch-06.fr.tex:7 |
| 79 | 1 | cover/wrapper | Page 1 is a cover in his hand: its words become the opening section heading (no \page). | transcripts/79/batch-01.fr.tex:4 |
| 79 | 271 | blank | Pages 271 and 274 are blank and are absent. | transcripts/79/batch-14.fr.tex:6 |
| 79 | 274 | blank | Pages 271 and 274 are blank and are absent. | transcripts/79/batch-14.fr.tex:6 |
| 79 | 281 | blank | Skipped (no \page): 281 (blank sheet) | transcripts/79/batch-15.fr.tex:4 |
| 79 | 287 | others' typescript | 287, 289, 291, 296 (university administrative notices and seminar announcements, typed, with nothing in his hand). | transcripts/79/batch-15.fr.tex:4 |
| 79 | 289 | others' typescript | 287, 289, 291, 296 (university administrative notices and seminar announcements, typed, with nothing in his hand). | transcripts/79/batch-15.fr.tex:4 |
| 79 | 291 | others' typescript | 287, 289, 291, 296 (university administrative notices and seminar announcements, typed, with nothing in his hand). | transcripts/79/batch-15.fr.tex:4 |
| 79 | 296 | others' typescript | 287, 289, 291, 296 (university administrative notices and seminar announcements, typed, with nothing in his hand). | transcripts/79/batch-15.fr.tex:4 |
| 80 | 1 | blank | Pages skipped: 1, 8, 15 and 19, blank cream separator sheets with nothing on them. | transcripts/80/batch-01.fr.tex:18 |
| 80 | 8 | blank | Pages skipped: 1, 8, 15 and 19, blank cream separator sheets with nothing on them. | transcripts/80/batch-01.fr.tex:18 |
| 80 | 15 | blank | Pages skipped: 1, 8, 15 and 19, blank cream separator sheets with nothing on them. | transcripts/80/batch-01.fr.tex:18 |
| 80 | 19 | blank | Pages skipped: 1, 8, 15 and 19, blank cream separator sheets with nothing on them. | transcripts/80/batch-01.fr.tex:18 |
| 80 | 21 | administrative | Pages skipped: 21, 23, 25 and 29, photocopies of a handwritten letter in German, autobiographical and unrelated to the mathematics (two copi… | transcripts/80/batch-02.fr.tex:23 |
| 80 | 23 | administrative | Pages skipped: 21, 23, 25 and 29, photocopies of a handwritten letter in German, autobiographical and unrelated to the mathematics (two copi… | transcripts/80/batch-02.fr.tex:23 |
| 80 | 25 | administrative | Pages skipped: 21, 23, 25 and 29, photocopies of a handwritten letter in German, autobiographical and unrelated to the mathematics (two copi… | transcripts/80/batch-02.fr.tex:23 |
| 80 | 27 | others' typescript | Page 27 is a typed USTL notice dated « Montpellier, le 13 mai 1981 », which is consistent with the archivists' « [à partir de 1981] » | transcripts/80/batch-02.fr.tex:19 |
| 80 | 29 | administrative | Pages skipped: 21, 23, 25 and 29, photocopies of a handwritten letter in German, autobiographical and unrelated to the mathematics (two copi… | transcripts/80/batch-02.fr.tex:23 |
| 80 | 30 | blank | 30, a blank sheet. | transcripts/80/batch-02.fr.tex:23 |
| 80 | 55 | blank | Pages skipped: 55 and 59, blank cream separator sheets with nothing on them. | transcripts/80/batch-03.fr.tex:20 |
| 80 | 59 | blank | Pages skipped: 55 and 59, blank cream separator sheets with nothing on them. | transcripts/80/batch-03.fr.tex:20 |
| 80 | 71 | blank | Pages skipped: 71, a blank cream separator sheet (only show-through from the neighbouring leaf). | transcripts/80/batch-04.fr.tex:24 |
| 81 | 1 | blank | page 1, a sheet otherwise blank inscribed in pencil « 0 Cartes sphériques en général » — a cover, whose words head the first section | transcripts/81/batch-01.fr.tex:12 |
| 81 | 6 | unrelated | pages 6-7, an attempted proof of Fermat's last theorem (a^q + b^q = c^q, Newton's binomial expansion, with a boxed example q = 2, 3-4-5) in … | transcripts/81/batch-01.fr.tex:12 |
| 81 | 7 | unrelated | pages 6-7, an attempted proof of Fermat's last theorem (a^q + b^q = c^q, Newton's binomial expansion, with a boxed example q = 2, 3-4-5) in … | transcripts/81/batch-01.fr.tex:12 |
| 81 | 8 | blank | page 8, blank apart from a faint pencilled name and dates read through the paper | transcripts/81/batch-01.fr.tex:12 |
| 81 | 12 | blank | page 12, a table in his hand that is not mathematics, whose latest year, 1981, agrees with the archivists' « [à partir de 1981] » | transcripts/81/batch-01.fr.tex:12 |
| 81 | 13 | cover/wrapper | page 13, a pink cover inscribed « décompositions n-aires (et découpages) d'espaces topologiques », whose words head the second section. | transcripts/81/batch-01.fr.tex:12 |
| 81 | 30 | blank | page 30, a blank (pink) sheet | transcripts/81/batch-02.fr.tex:14 |
| 81 | 40 | blank | page 40, an otherwise blank sheet inscribed in pencil, top right, in his hand, « relations d'équi. non parallèles » — a cover for the run th… | transcripts/81/batch-02.fr.tex:14 |
| 82 | 1 | cover/wrapper | Page 1 is a pink cover inscribed in pencil, top right, « Algèbres de Lie de rang 3 associées aux formes bil. symétriques de rang 3 », with «… | transcripts/82/batch-01.fr.tex:17 |
| 82 | 32 | cover/wrapper | Page 32 is a pink cover with nothing on it but « (21 p) » in pencil top right (hand not certain) and no title | transcripts/82/batch-02.fr.tex:21 |
| 82 | 35 | blank | Pages skipped: 35, a blank sheet (only show-through). | transcripts/82/batch-02.fr.tex:21 |
| 82 | 45 | blank | Pages skipped: 45, a blank cream sheet (only show-through of p. 44). | transcripts/82/batch-03.fr.tex:17 |
| 82 | 56 | skipped, reason not classifiable | The folder is seventy-eight pages in four batches (1-20, 21-40, 41-60, 61-78), transcribed in parallel by four passes | transcripts/82/batch-03.fr.tex:6 |
| 83 | 1 | blank | Page 1 is blank. | transcripts/83/batch-01.fr.tex:5 |
| 83 | 4 | others' typescript | Pages 4, 6, 8, 10, 12, 14 and 16 are typescript leaves of his non-mathematical writing (Récoltes et Semailles « L » letter pages, and « PU »… | transcripts/83/batch-01.fr.tex:5 |
| 83 | 6 | others' typescript | Pages 4, 6, 8, 10, 12, 14 and 16 are typescript leaves of his non-mathematical writing (Récoltes et Semailles « L » letter pages, and « PU »… | transcripts/83/batch-01.fr.tex:5 |
| 83 | 8 | others' typescript | Pages 4, 6, 8, 10, 12, 14 and 16 are typescript leaves of his non-mathematical writing (Récoltes et Semailles « L » letter pages, and « PU »… | transcripts/83/batch-01.fr.tex:5 |
| 83 | 10 | others' typescript | Pages 4, 6, 8, 10, 12, 14 and 16 are typescript leaves of his non-mathematical writing (Récoltes et Semailles « L » letter pages, and « PU »… | transcripts/83/batch-01.fr.tex:5 |
| 83 | 12 | others' typescript | Pages 4, 6, 8, 10, 12, 14 and 16 are typescript leaves of his non-mathematical writing (Récoltes et Semailles « L » letter pages, and « PU »… | transcripts/83/batch-01.fr.tex:5 |
| 83 | 14 | others' typescript | Pages 4, 6, 8, 10, 12, 14 and 16 are typescript leaves of his non-mathematical writing (Récoltes et Semailles « L » letter pages, and « PU »… | transcripts/83/batch-01.fr.tex:5 |
| 83 | 16 | others' typescript | Pages 4, 6, 8, 10, 12, 14 and 16 are typescript leaves of his non-mathematical writing (Récoltes et Semailles « L » letter pages, and « PU »… | transcripts/83/batch-01.fr.tex:5 |
| 83 | 17 | cover/wrapper | Page 17 is an orange folder cover carrying only a pencil « sl(2, Λ) » | transcripts/83/batch-01.fr.tex:9 |
| 83 | 37 | cover/wrapper | Page 37 is a cover sheet inscribed in his hand ("Rapport anharmonique, avril 1986") | transcripts/83/batch-02.fr.tex:9 |
| 83 | 46 | blank | Page 46 is blank and page 51 is a cover sheet in his hand (its words head the section before page 52) | transcripts/83/batch-03.fr.tex:5 |
| 83 | 51 | blank | Page 46 is blank and page 51 is a cover sheet in his hand (its words head the section before page 52) | transcripts/83/batch-03.fr.tex:5 |
| 83 | 74 | gap only (no header mention) |  | transcripts/83/batch-04.fr.tex:1 |
| 83 | 76 | gap only (no header mention) |  | transcripts/83/batch-04.fr.tex:1 |
| 83 | 78 | gap only (no header mention) |  | transcripts/83/batch-04.fr.tex:1 |
| 83 | 79 | gap only (no header mention) |  | transcripts/83/batch-04.fr.tex:1 |
| 83 | 93 | others' typescript | Page 93 is a typescript leaf of his non-mathematical writing (« PU 65 », on abstraction and concepts), cancelled and annotated in his hand | transcripts/83/batch-05.fr.tex:5 |
| 83 | 100 | blank | Page 100 is a blank sheet | transcripts/83/batch-05.fr.tex:7 |
| 83 | 128 | gap only (no header mention) |  | transcripts/83/batch-07.fr.tex:1 |
| 83 | 148 | gap only (no header mention) |  | transcripts/83/batch-08.fr.tex:1 |
| 83 | 181 | blank | Page 181 is blank | transcripts/83/batch-10.fr.tex:5 |
| 83 | 195 | others' typescript | pages 195 and 197 are typescript pages (L 19, L 17) of a non-mathematical text by Grothendieck with no mathematics on them, skipped. | transcripts/83/batch-10.fr.tex:5 |
| 83 | 197 | others' typescript | pages 195 and 197 are typescript pages (L 19, L 17) of a non-mathematical text by Grothendieck with no mathematics on them, skipped. | transcripts/83/batch-10.fr.tex:5 |
| 83 | 201 | others' typescript | Pages 201, 203, 207, 209, 211, 213, 215, 217 and 219 are typescript pages of Récoltes et Semailles (with his blue-ink corrections), unrelate… | transcripts/83/batch-11.fr.tex:5 |
| 83 | 203 | others' typescript | Pages 201, 203, 207, 209, 211, 213, 215, 217 and 219 are typescript pages of Récoltes et Semailles (with his blue-ink corrections), unrelate… | transcripts/83/batch-11.fr.tex:5 |
| 83 | 205 | blank | page 205 is blank. | transcripts/83/batch-11.fr.tex:5 |
| 83 | 207 | others' typescript | Pages 201, 203, 207, 209, 211, 213, 215, 217 and 219 are typescript pages of Récoltes et Semailles (with his blue-ink corrections), unrelate… | transcripts/83/batch-11.fr.tex:5 |
| 83 | 209 | others' typescript | Pages 201, 203, 207, 209, 211, 213, 215, 217 and 219 are typescript pages of Récoltes et Semailles (with his blue-ink corrections), unrelate… | transcripts/83/batch-11.fr.tex:5 |
| 83 | 211 | others' typescript | Pages 201, 203, 207, 209, 211, 213, 215, 217 and 219 are typescript pages of Récoltes et Semailles (with his blue-ink corrections), unrelate… | transcripts/83/batch-11.fr.tex:5 |
| 83 | 213 | others' typescript | Pages 201, 203, 207, 209, 211, 213, 215, 217 and 219 are typescript pages of Récoltes et Semailles (with his blue-ink corrections), unrelate… | transcripts/83/batch-11.fr.tex:5 |
| 83 | 215 | others' typescript | Pages 201, 203, 207, 209, 211, 213, 215, 217 and 219 are typescript pages of Récoltes et Semailles (with his blue-ink corrections), unrelate… | transcripts/83/batch-11.fr.tex:5 |
| 83 | 217 | others' typescript | Pages 201, 203, 207, 209, 211, 213, 215, 217 and 219 are typescript pages of Récoltes et Semailles (with his blue-ink corrections), unrelate… | transcripts/83/batch-11.fr.tex:5 |
| 83 | 219 | others' typescript | Pages 201, 203, 207, 209, 211, 213, 215, 217 and 219 are typescript pages of Récoltes et Semailles (with his blue-ink corrections), unrelate… | transcripts/83/batch-11.fr.tex:5 |
| 83 | 222 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 223 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 224 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 225 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 226 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 227 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 228 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 229 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 230 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 231 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 232 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 233 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 234 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 235 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 236 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 237 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 238 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 239 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 83 | 240 | gap only (no header mention) |  | transcripts/83/batch-12.fr.tex:1 |
| 84 | 4 | others' typescript | Pages 4, 6 and 7 are unrelated versos (typescript pages, a computer listing) and are absent. | transcripts/84/batch-01.fr.tex:5 |
| 84 | 6 | others' typescript | Pages 4, 6 and 7 are unrelated versos (typescript pages, a computer listing) and are absent. | transcripts/84/batch-01.fr.tex:5 |
| 84 | 7 | others' typescript | Pages 4, 6 and 7 are unrelated versos (typescript pages, a computer listing) and are absent. | transcripts/84/batch-01.fr.tex:5 |
| 84 | 42 | cover/wrapper | Page 42 is a cover sheet in his hand on music paper: it carries no \page{}, and its words open the section heading, as hand.md prescribes. | transcripts/84/batch-03.fr.tex:12 |
| 84 | 44 | blank | page 44 (blank sheet, only show-through). | transcripts/84/batch-03.fr.tex:12 |
| 84 | 122 | blank | Even pages 122–140 are skipped: 122 is blank, 124–140 are typed pages (pp. 465–473) of a non-mathematical typescript used as scrap paper. | transcripts/84/batch-07.fr.tex:5 |
| 84 | 124 | blank | Even pages 122–140 are skipped: 122 is blank, 124–140 are typed pages (pp. 465–473) of a non-mathematical typescript used as scrap paper. | transcripts/84/batch-07.fr.tex:5 |
| 84 | 126 | blank | Even pages 122–140 are skipped: 122 is blank, 124–140 are typed pages (pp. 465–473) of a non-mathematical typescript used as scrap paper. | transcripts/84/batch-07.fr.tex:5 |
| 84 | 128 | blank | Even pages 122–140 are skipped: 122 is blank, 124–140 are typed pages (pp. 465–473) of a non-mathematical typescript used as scrap paper. | transcripts/84/batch-07.fr.tex:5 |
| 84 | 130 | blank | Even pages 122–140 are skipped: 122 is blank, 124–140 are typed pages (pp. 465–473) of a non-mathematical typescript used as scrap paper. | transcripts/84/batch-07.fr.tex:5 |
| 84 | 132 | blank | Even pages 122–140 are skipped: 122 is blank, 124–140 are typed pages (pp. 465–473) of a non-mathematical typescript used as scrap paper. | transcripts/84/batch-07.fr.tex:5 |
| 84 | 134 | blank | Even pages 122–140 are skipped: 122 is blank, 124–140 are typed pages (pp. 465–473) of a non-mathematical typescript used as scrap paper. | transcripts/84/batch-07.fr.tex:5 |
| 84 | 136 | blank | Even pages 122–140 are skipped: 122 is blank, 124–140 are typed pages (pp. 465–473) of a non-mathematical typescript used as scrap paper. | transcripts/84/batch-07.fr.tex:5 |
| 84 | 138 | blank | Even pages 122–140 are skipped: 122 is blank, 124–140 are typed pages (pp. 465–473) of a non-mathematical typescript used as scrap paper. | transcripts/84/batch-07.fr.tex:5 |
| 84 | 140 | blank | Even pages 122–140 are skipped: 122 is blank, 124–140 are typed pages (pp. 465–473) of a non-mathematical typescript used as scrap paper. | transcripts/84/batch-07.fr.tex:5 |
| 84 | 142 | others' typescript | The even pages 142-160 are typescript pages of Récoltes et Semailles (pp. 474-489 of that text: notes 108-111, « Yang enterre yin », the « r… | transcripts/84/batch-08.fr.tex:5 |
| 84 | 144 | others' typescript | The even pages 142-160 are typescript pages of Récoltes et Semailles (pp. 474-489 of that text: notes 108-111, « Yang enterre yin », the « r… | transcripts/84/batch-08.fr.tex:5 |
| 84 | 146 | others' typescript | The even pages 142-160 are typescript pages of Récoltes et Semailles (pp. 474-489 of that text: notes 108-111, « Yang enterre yin », the « r… | transcripts/84/batch-08.fr.tex:5 |
| 84 | 148 | others' typescript | The even pages 142-160 are typescript pages of Récoltes et Semailles (pp. 474-489 of that text: notes 108-111, « Yang enterre yin », the « r… | transcripts/84/batch-08.fr.tex:5 |
| 84 | 150 | others' typescript | The even pages 142-160 are typescript pages of Récoltes et Semailles (pp. 474-489 of that text: notes 108-111, « Yang enterre yin », the « r… | transcripts/84/batch-08.fr.tex:5 |
| 84 | 152 | others' typescript | The even pages 142-160 are typescript pages of Récoltes et Semailles (pp. 474-489 of that text: notes 108-111, « Yang enterre yin », the « r… | transcripts/84/batch-08.fr.tex:5 |
| 84 | 154 | others' typescript | The even pages 142-160 are typescript pages of Récoltes et Semailles (pp. 474-489 of that text: notes 108-111, « Yang enterre yin », the « r… | transcripts/84/batch-08.fr.tex:5 |
| 84 | 156 | others' typescript | The even pages 142-160 are typescript pages of Récoltes et Semailles (pp. 474-489 of that text: notes 108-111, « Yang enterre yin », the « r… | transcripts/84/batch-08.fr.tex:5 |
| 84 | 158 | others' typescript | The even pages 142-160 are typescript pages of Récoltes et Semailles (pp. 474-489 of that text: notes 108-111, « Yang enterre yin », the « r… | transcripts/84/batch-08.fr.tex:5 |
| 84 | 160 | others' typescript | The even pages 142-160 are typescript pages of Récoltes et Semailles (pp. 474-489 of that text: notes 108-111, « Yang enterre yin », the « r… | transcripts/84/batch-08.fr.tex:5 |
| 84 | 162 | blank | The even pages 162–180 are blank versos and are absent. | transcripts/84/batch-09.fr.tex:5 |
| 84 | 164 | blank | The even pages 162–180 are blank versos and are absent. | transcripts/84/batch-09.fr.tex:5 |
| 84 | 166 | blank | The even pages 162–180 are blank versos and are absent. | transcripts/84/batch-09.fr.tex:5 |
| 84 | 168 | blank | The even pages 162–180 are blank versos and are absent. | transcripts/84/batch-09.fr.tex:5 |
| 84 | 170 | blank | The even pages 162–180 are blank versos and are absent. | transcripts/84/batch-09.fr.tex:5 |
| 84 | 172 | blank | The even pages 162–180 are blank versos and are absent. | transcripts/84/batch-09.fr.tex:5 |
| 84 | 174 | blank | The even pages 162–180 are blank versos and are absent. | transcripts/84/batch-09.fr.tex:5 |
| 84 | 176 | blank | The even pages 162–180 are blank versos and are absent. | transcripts/84/batch-09.fr.tex:5 |
| 84 | 178 | blank | The even pages 162–180 are blank versos and are absent. | transcripts/84/batch-09.fr.tex:5 |
| 84 | 180 | blank | The even pages 162–180 are blank versos and are absent. | transcripts/84/batch-09.fr.tex:5 |
| 84 | 182 | others' typescript | Even pages 182, 184, 186, 188, 190, 192 are versos of a typescript of Grothendieck's own non-mathematical writing (typed pages 495-500, yin … | transcripts/84/batch-10.fr.tex:5 |
| 84 | 184 | others' typescript | Even pages 182, 184, 186, 188, 190, 192 are versos of a typescript of Grothendieck's own non-mathematical writing (typed pages 495-500, yin … | transcripts/84/batch-10.fr.tex:5 |
| 84 | 186 | others' typescript | Even pages 182, 184, 186, 188, 190, 192 are versos of a typescript of Grothendieck's own non-mathematical writing (typed pages 495-500, yin … | transcripts/84/batch-10.fr.tex:5 |
| 84 | 188 | others' typescript | Even pages 182, 184, 186, 188, 190, 192 are versos of a typescript of Grothendieck's own non-mathematical writing (typed pages 495-500, yin … | transcripts/84/batch-10.fr.tex:5 |
| 84 | 190 | others' typescript | Even pages 182, 184, 186, 188, 190, 192 are versos of a typescript of Grothendieck's own non-mathematical writing (typed pages 495-500, yin … | transcripts/84/batch-10.fr.tex:5 |
| 84 | 192 | others' typescript | Even pages 182, 184, 186, 188, 190, 192 are versos of a typescript of Grothendieck's own non-mathematical writing (typed pages 495-500, yin … | transcripts/84/batch-10.fr.tex:5 |
| 85 | 3 | cover/wrapper | Pages 3 and 11 are wrappers inscribed in his hand and nothing else | transcripts/85/batch-01.fr.tex:11 |
| 85 | 11 | cover/wrapper | Pages 3 and 11 are wrappers inscribed in his hand and nothing else | transcripts/85/batch-01.fr.tex:11 |
| 85 | 22 | gap only (no header mention) |  | transcripts/85/batch-02.fr.tex:1 |
| 85 | 32 | gap only (no header mention) |  | transcripts/85/batch-02.fr.tex:1 |
| 85 | 41 | cover/wrapper | Pages 41 and 57 are covers on pink card, each inscribed in ink at the top right and counted in pencil | transcripts/85/batch-03.fr.tex:10 |
| 85 | 57 | cover/wrapper | Pages 41 and 57 are covers on pink card, each inscribed in ink at the top right and counted in pencil | transcripts/85/batch-03.fr.tex:10 |
| 85 | 74 | cover/wrapper | Page 74 is a cover on pink card, inscribed in ink at the top right « 2-Polyèdres réguliers finis en car. 0 (classification) » and in pencil … | transcripts/85/batch-04.fr.tex:10 |
| 85 | 81 | cover/wrapper | Pages 81 and 94 are covers (cream, then yellow card), each inscribed in ink at the top right and counted in pencil at the top: p. 81 « Opéra… | transcripts/85/batch-05.fr.tex:10 |
| 85 | 94 | cover/wrapper | Pages 81 and 94 are covers (cream, then yellow card), each inscribed in ink at the top right and counted in pencil at the top: p. 81 « Opéra… | transcripts/85/batch-05.fr.tex:10 |
| 86 | 1 | cover/wrapper | Pages skipped: none apart from the three covers (1, 9, 17), which carry nothing but those inscriptions. | transcripts/86/batch-01.fr.tex:21 |
| 86 | 9 | cover/wrapper | Pages skipped: none apart from the three covers (1, 9, 17), which carry nothing but those inscriptions. | transcripts/86/batch-01.fr.tex:21 |
| 86 | 17 | cover/wrapper | Pages skipped: none apart from the three covers (1, 9, 17), which carry nothing but those inscriptions. | transcripts/86/batch-01.fr.tex:21 |
| 87 | 1 | blank | Page 1 is a tan wrapper sheet with nothing on it, and pages 16 and 20 are blank tan sheets of the same kind: all three are skipped, the gaps… | transcripts/87/batch-01.fr.tex:7 |
| 87 | 15 | cover/wrapper | Page 15 is a tan cover carrying, in ink in the top right corner, the single word « Cubes », and in pencil, circled, « (13 p.) » — the latter… | transcripts/87/batch-01.fr.tex:10 |
| 87 | 16 | blank | Page 1 is a tan wrapper sheet with nothing on it, and pages 16 and 20 are blank tan sheets of the same kind: all three are skipped, the gaps… | transcripts/87/batch-01.fr.tex:7 |
| 87 | 20 | blank | Page 1 is a tan wrapper sheet with nothing on it, and pages 16 and 20 are blank tan sheets of the same kind: all three are skipped, the gaps… | transcripts/87/batch-01.fr.tex:7 |
| 87 | 31 | skipped, reason not classifiable | Page 31 is skipped: it carries nothing in his hand (only page 32 showing through the sheet), and the gap in the page numbers is the record. | transcripts/87/batch-02.fr.tex:7 |
| 88 | 1 | cover/wrapper | Page 1 is a tan wrapper carrying, alone in the top right corner and in pencil, « Cartes associées aux syst. de Racines » followed by a « (7)… | transcripts/88/batch-01.fr.tex:8 |
| 88 | 9 | cover/wrapper | Page 9 is the other face of that wrapper: nothing of his hand is on it — what shows is page 10's ink read through the sheet — and it is skip… | transcripts/88/batch-01.fr.tex:12 |
| 89 | 1 | cover/wrapper | Page 1 is a cover carrying only « les ensembles 3-3 » in pencil | transcripts/89/batch-01.fr.tex:7 |
| 91 | 1 | cover/wrapper | Page 1 is a cover in his hand: its words become the section heading, with no \page. | transcripts/91/batch-01.fr.tex:5 |
| 91 | 3 | blank | Pages 3 and 14 are blank and are absent. | transcripts/91/batch-01.fr.tex:5 |
| 91 | 14 | blank | Pages 3 and 14 are blank and are absent. | transcripts/91/batch-01.fr.tex:5 |
| 91 | 29 | blank | Pages 29 and 32 are blank versos (ink show-through only) and are skipped. | transcripts/91/batch-02.fr.tex:6 |
| 91 | 32 | blank | Pages 29 and 32 are blank versos (ink show-through only) and are skipped. | transcripts/91/batch-02.fr.tex:6 |
| 91 | 59 | gap only (no header mention) |  | transcripts/91/batch-03.fr.tex:1 |
| 91 | 80 | cover/wrapper | Source: archives/batches/91/batch-04.pdf (cover sheet excluded), read from the 700-dpi tiles in archives/tiles/91/p61 … p80. | transcripts/91/batch-04.fr.tex:5 |
| 91 | 82 | gap only (no header mention) |  | transcripts/91/batch-05.fr.tex:1 |
| 91 | 84 | gap only (no header mention) |  | transcripts/91/batch-05.fr.tex:1 |
| 91 | 85 | gap only (no header mention) |  | transcripts/91/batch-05.fr.tex:1 |
| 91 | 87 | gap only (no header mention) |  | transcripts/91/batch-05.fr.tex:1 |
| 91 | 89 | gap only (no header mention) |  | transcripts/91/batch-05.fr.tex:1 |
| 91 | 91 | gap only (no header mention) |  | transcripts/91/batch-05.fr.tex:1 |
| 91 | 93 | gap only (no header mention) |  | transcripts/91/batch-05.fr.tex:1 |
| 91 | 95 | gap only (no header mention) |  | transcripts/91/batch-05.fr.tex:1 |
| 91 | 97 | gap only (no header mention) |  | transcripts/91/batch-05.fr.tex:1 |
| 91 | 99 | gap only (no header mention) |  | transcripts/91/batch-05.fr.tex:1 |
| 91 | 101 | blank | Skipped: 101, 118, 120 (typed Bourbaki pages with nothing of his on them) and 102, 111, 116 (blank). | transcripts/91/batch-06.fr.tex:6 |
| 91 | 102 | blank | Skipped: 101, 118, 120 (typed Bourbaki pages with nothing of his on them) and 102, 111, 116 (blank). | transcripts/91/batch-06.fr.tex:6 |
| 91 | 111 | blank | Skipped: 101, 118, 120 (typed Bourbaki pages with nothing of his on them) and 102, 111, 116 (blank). | transcripts/91/batch-06.fr.tex:6 |
| 91 | 116 | blank | Skipped: 101, 118, 120 (typed Bourbaki pages with nothing of his on them) and 102, 111, 116 (blank). | transcripts/91/batch-06.fr.tex:6 |
| 91 | 118 | blank | Skipped: 101, 118, 120 (typed Bourbaki pages with nothing of his on them) and 102, 111, 116 (blank). | transcripts/91/batch-06.fr.tex:6 |
| 91 | 120 | blank | Skipped: 101, 118, 120 (typed Bourbaki pages with nothing of his on them) and 102, 111, 116 (blank). | transcripts/91/batch-06.fr.tex:6 |
| 91 | 122 | others' typescript | Pages 122, 126, 128, 138 and 140 are typed versos unrelated to the notes | transcripts/91/batch-07.fr.tex:5 |
| 91 | 124 | blank | pages 124, 129, 132 and 136 are blank. | transcripts/91/batch-07.fr.tex:6 |
| 91 | 126 | others' typescript | Pages 122, 126, 128, 138 and 140 are typed versos unrelated to the notes | transcripts/91/batch-07.fr.tex:5 |
| 91 | 128 | others' typescript | Pages 122, 126, 128, 138 and 140 are typed versos unrelated to the notes | transcripts/91/batch-07.fr.tex:5 |
| 91 | 129 | blank | pages 124, 129, 132 and 136 are blank. | transcripts/91/batch-07.fr.tex:6 |
| 91 | 132 | blank | pages 124, 129, 132 and 136 are blank. | transcripts/91/batch-07.fr.tex:6 |
| 91 | 136 | blank | pages 124, 129, 132 and 136 are blank. | transcripts/91/batch-07.fr.tex:6 |
| 91 | 138 | others' typescript | Pages 122, 126, 128, 138 and 140 are typed versos unrelated to the notes | transcripts/91/batch-07.fr.tex:5 |
| 91 | 140 | others' typescript | Pages 122, 126, 128, 138 and 140 are typed versos unrelated to the notes | transcripts/91/batch-07.fr.tex:5 |
| 91 | 142 | others' typescript | Page 142 is an unrelated typed verso (a typescript of Lie-group exercises, scanned upside down) carrying nothing in his hand: skipped, per t… | transcripts/91/batch-08.fr.tex:5 |
| 93 | 1 | blank | Page 1 is blank and omitted. | transcripts/93/batch-01.fr.tex:10 |
| 93 | 25 | blank | Skipped without trace: p. 25 (blank), p. 26 (cover, used as heading), pp. 31 and 33 (unrelated English typescript versos), p. 34 (blank), p.… | transcripts/93/batch-02.fr.tex:10 |
| 93 | 26 | blank | Skipped without trace: p. 25 (blank), p. 26 (cover, used as heading), pp. 31 and 33 (unrelated English typescript versos), p. 34 (blank), p.… | transcripts/93/batch-02.fr.tex:10 |
| 93 | 31 | blank | Skipped without trace: p. 25 (blank), p. 26 (cover, used as heading), pp. 31 and 33 (unrelated English typescript versos), p. 34 (blank), p.… | transcripts/93/batch-02.fr.tex:10 |
| 93 | 33 | blank | Skipped without trace: p. 25 (blank), p. 26 (cover, used as heading), pp. 31 and 33 (unrelated English typescript versos), p. 34 (blank), p.… | transcripts/93/batch-02.fr.tex:10 |
| 93 | 34 | blank | Skipped without trace: p. 25 (blank), p. 26 (cover, used as heading), pp. 31 and 33 (unrelated English typescript versos), p. 34 (blank), p.… | transcripts/93/batch-02.fr.tex:10 |
| 93 | 36 | blank | Skipped without trace: p. 25 (blank), p. 26 (cover, used as heading), pp. 31 and 33 (unrelated English typescript versos), p. 34 (blank), p.… | transcripts/93/batch-02.fr.tex:10 |
| 93 | 49 | others' typescript | Skipped without trace: pp. 49 and 51 (Bourbaki draft n° 393 on Banach algebras, versos), p. 54 (cover, his words used as heading), pp. 56, 5… | transcripts/93/batch-03.fr.tex:10 |
| 93 | 51 | others' typescript | Skipped without trace: pp. 49 and 51 (Bourbaki draft n° 393 on Banach algebras, versos), p. 54 (cover, his words used as heading), pp. 56, 5… | transcripts/93/batch-03.fr.tex:10 |
| 93 | 54 | others' typescript | Skipped without trace: pp. 49 and 51 (Bourbaki draft n° 393 on Banach algebras, versos), p. 54 (cover, his words used as heading), pp. 56, 5… | transcripts/93/batch-03.fr.tex:10 |
| 93 | 56 | others' typescript | Skipped without trace: pp. 49 and 51 (Bourbaki draft n° 393 on Banach algebras, versos), p. 54 (cover, his words used as heading), pp. 56, 5… | transcripts/93/batch-03.fr.tex:10 |
| 93 | 58 | others' typescript | Skipped without trace: pp. 49 and 51 (Bourbaki draft n° 393 on Banach algebras, versos), p. 54 (cover, his words used as heading), pp. 56, 5… | transcripts/93/batch-03.fr.tex:10 |
| 93 | 60 | others' typescript | Skipped without trace: pp. 49 and 51 (Bourbaki draft n° 393 on Banach algebras, versos), p. 54 (cover, his words used as heading), pp. 56, 5… | transcripts/93/batch-03.fr.tex:10 |
| 93 | 62 | others' typescript | Pages 62, 64 and 66 are unrelated typescript versos (an administrative report on university research) | transcripts/93/batch-04.fr.tex:4 |
| 93 | 64 | others' typescript | Pages 62, 64 and 66 are unrelated typescript versos (an administrative report on university research) | transcripts/93/batch-04.fr.tex:4 |
| 93 | 66 | others' typescript | Pages 62, 64 and 66 are unrelated typescript versos (an administrative report on university research) | transcripts/93/batch-04.fr.tex:4 |
| 93 | 68 | blank | 68-69 a list of names and an address, 70 and 78 blank | transcripts/93/batch-04.fr.tex:4 |
| 93 | 69 | blank | 68-69 a list of names and an address, 70 and 78 blank | transcripts/93/batch-04.fr.tex:4 |
| 93 | 70 | blank | 68-69 a list of names and an address, 70 and 78 blank | transcripts/93/batch-04.fr.tex:4 |
| 93 | 78 | blank | 68-69 a list of names and an address, 70 and 78 blank | transcripts/93/batch-04.fr.tex:4 |
| 93 | 84 | blank | Page 84 is a blank sheet and is skipped. | transcripts/93/batch-05.fr.tex:4 |
| 93 | 124 | blank | Pages 124 and 140 are blank separator sheets and are not transcribed. | transcripts/93/batch-07.fr.tex:4 |
| 93 | 140 | blank | Pages 124 and 140 are blank separator sheets and are not transcribed. | transcripts/93/batch-07.fr.tex:4 |
| 93 | 154 | gap only (no header mention) |  | transcripts/93/batch-08.fr.tex:1 |
| 93 | 160 | gap only (no header mention) |  | transcripts/93/batch-08.fr.tex:1 |
| 93 | 167 | cover/wrapper | p. 167 is a cover sheet in his hand ("Opération de Cartier"), used as a heading and given no \page | transcripts/93/batch-09.fr.tex:5 |
| 93 | 187 | cover/wrapper | Page 187 is a cover sheet inscribed in his hand | transcripts/93/batch-10.fr.tex:5 |
| 93 | 204 | cover/wrapper | 204, 213 and 218 are covers in his hand (their words become section headings) | transcripts/93/batch-11.fr.tex:5 |
| 93 | 213 | cover/wrapper | 204, 213 and 218 are covers in his hand (their words become section headings) | transcripts/93/batch-11.fr.tex:5 |
| 93 | 218 | cover/wrapper | 204, 213 and 218 are covers in his hand (their words become section headings) | transcripts/93/batch-11.fr.tex:5 |
| 94 | 1 | cover/wrapper | Page 1 is a brown cover inscribed in ink, top right | transcripts/94/batch-01.fr.tex:14 |
| 94 | 11 | others' typescript | Pages skipped: 11 and 13, typed leaves unrelated to the notes and with nothing in his hand (a typescript chapter on valued fields, and a typ… | transcripts/94/batch-01.fr.tex:12 |
| 94 | 13 | others' typescript | Pages skipped: 11 and 13, typed leaves unrelated to the notes and with nothing in his hand (a typescript chapter on valued fields, and a typ… | transcripts/94/batch-01.fr.tex:12 |
| 97 | 2 | unrelated | page 2, a list of mathematicians' names in his hand with brackets and boxes (a distribution list, no mathematics) | transcripts/97/batch-01.fr.tex:9 |
| 97 | 3 | administrative | page 3, a sheet of IHES letterhead carrying only the abandoned opening of a letter to Atiyah | transcripts/97/batch-01.fr.tex:9 |
| 97 | 5 | blank | page 5, blank | transcripts/97/batch-01.fr.tex:9 |
| 97 | 14 | blank | page 14, the blank verso of page 13, showing only its bleed-through. | transcripts/97/batch-01.fr.tex:13 |
| 98 | 1 | blank | Absent: - page 1, a buff card cover blank but for his pencil « Formalisation des Normes » and « Cf aussi SGA 4 XVIII » | transcripts/98/batch-01.fr.tex:19 |
| 98 | 3 | others' typescript | - pages 3, 5, 7, 9, typed pages « - 39 - », « - 35 - », « - 37 - », « - 36 - » of a French typescript « n° 329 » on general topology (produc… | transcripts/98/batch-01.fr.tex:23 |
| 98 | 5 | blank | the words head the \section and are quoted in a \note (hand.md §5) | transcripts/98/batch-01.fr.tex:19 |
| 98 | 7 | others' typescript | - pages 3, 5, 7, 9, typed pages « - 39 - », « - 35 - », « - 37 - », « - 36 - » of a French typescript « n° 329 » on general topology (produc… | transcripts/98/batch-01.fr.tex:23 |
| 98 | 9 | others' typescript | - pages 3, 5, 7, 9, typed pages « - 39 - », « - 35 - », « - 37 - », « - 36 - » of a French typescript « n° 329 » on general topology (produc… | transcripts/98/batch-01.fr.tex:23 |
| 98 | 14 | others' typescript | - pages 14, 16, 20, typed pages « - 99 - » (n° 266), « - 96 - » and « - 89 - » (n° 268) of a French typescript on abelian varieties (theorem… | transcripts/98/batch-01.fr.tex:28 |
| 98 | 16 | others' typescript | - pages 14, 16, 20, typed pages « - 99 - » (n° 266), « - 96 - » and « - 89 - » (n° 268) of a French typescript on abelian varieties (theorem… | transcripts/98/batch-01.fr.tex:28 |
| 98 | 20 | others' typescript | - pages 14, 16, 20, typed pages « - 99 - » (n° 266), « - 96 - » and « - 89 - » (n° 268) of a French typescript on abelian varieties (theorem… | transcripts/98/batch-01.fr.tex:28 |
| 98 | 22 | others' typescript | Absent: - pages 22 and 24: typed leaves of someone else's typescript (French, scanned upside down, headed « n° 268 », paginated « -87- » and… | transcripts/98/batch-02.fr.tex:19 |
| 98 | 24 | others' typescript | Absent: - pages 22 and 24: typed leaves of someone else's typescript (French, scanned upside down, headed « n° 268 », paginated « -87- » and… | transcripts/98/batch-02.fr.tex:19 |
| 98 | 25 | blank | - page 25: an otherwise blank sheet carrying, in his hand, « Familles limitées » and « cf. SGA 6 XIII ». | transcripts/98/batch-02.fr.tex:25 |
| 100 | 1 | blank | Absent: - page 1, a sheet of buff card blank but for his words top right, « Bonne réduction et gpes p-divisibles » — a cover | transcripts/100/batch-01.fr.tex:17 |
| 100 | 11 | others' typescript | - pages 11, 13, 17 and 19, versos with nothing of his on them that bears on these notes: 11 is a typed English errata list for some other te… | transcripts/100/batch-01.fr.tex:21 |
| 100 | 13 | others' typescript | - pages 11, 13, 17 and 19, versos with nothing of his on them that bears on these notes: 11 is a typed English errata list for some other te… | transcripts/100/batch-01.fr.tex:21 |
| 100 | 17 | others' typescript | - pages 11, 13, 17 and 19, versos with nothing of his on them that bears on these notes: 11 is a typed English errata list for some other te… | transcripts/100/batch-01.fr.tex:21 |
| 100 | 19 | others' typescript | - pages 11, 13, 17 and 19, versos with nothing of his on them that bears on these notes: 11 is a typed English errata list for some other te… | transcripts/100/batch-01.fr.tex:21 |
| 100 | 23 | others' typescript | Absent: - pages 23, 25, 27, 31, 35, 37: leaves of the same typed English text on quotients of schemes by group actions that batch 1 met on p… | transcripts/100/batch-02.fr.tex:22 |
| 100 | 25 | others' typescript | Absent: - pages 23, 25, 27, 31, 35, 37: leaves of the same typed English text on quotients of schemes by group actions that batch 1 met on p… | transcripts/100/batch-02.fr.tex:22 |
| 100 | 27 | others' typescript | Absent: - pages 23, 25, 27, 31, 35, 37: leaves of the same typed English text on quotients of schemes by group actions that batch 1 met on p… | transcripts/100/batch-02.fr.tex:22 |
| 100 | 29 | others' typescript | The batch alternates: his manuscript on the even pages 22-40 (blue ink), typed leaves and letters on the odd pages 21-39. | transcripts/100/batch-02.fr.tex:19 |
| 100 | 31 | others' typescript | Absent: - pages 23, 25, 27, 31, 35, 37: leaves of the same typed English text on quotients of schemes by group actions that batch 1 met on p… | transcripts/100/batch-02.fr.tex:22 |
| 100 | 33 | others' typescript | The batch alternates: his manuscript on the even pages 22-40 (blue ink), typed leaves and letters on the odd pages 21-39. | transcripts/100/batch-02.fr.tex:19 |
| 100 | 35 | others' typescript | Absent: - pages 23, 25, 27, 31, 35, 37: leaves of the same typed English text on quotients of schemes by group actions that batch 1 met on p… | transcripts/100/batch-02.fr.tex:22 |
| 100 | 37 | others' typescript | Absent: - pages 23, 25, 27, 31, 35, 37: leaves of the same typed English text on quotients of schemes by group actions that batch 1 met on p… | transcripts/100/batch-02.fr.tex:22 |
| 100 | 39 | others' typescript | The batch alternates: his manuscript on the even pages 22-40 (blue ink), typed leaves and letters on the odd pages 21-39. | transcripts/100/batch-02.fr.tex:19 |
| 100 | 41 | others' typescript | Absent: - pages 41, 43 and 45, three leaves of a typed list « EGA IV 4e Errata et Compléments » (45 carries that heading | transcripts/100/batch-03.fr.tex:18 |
| 100 | 43 | others' typescript | Absent: - pages 41, 43 and 45, three leaves of a typed list « EGA IV 4e Errata et Compléments » (45 carries that heading | transcripts/100/batch-03.fr.tex:18 |
| 100 | 45 | others' typescript | Absent: - pages 41, 43 and 45, three leaves of a typed list « EGA IV 4e Errata et Compléments » (45 carries that heading | transcripts/100/batch-03.fr.tex:18 |
| 100 | 46 | blank | - page 46, a blank leaf. | transcripts/100/batch-03.fr.tex:28 |
| 101 | 1 | blank | Absent: - pages 1, 5 and 16, sheets of buff card blank but for his words top right — covers | transcripts/101/batch-01.fr.tex:18 |
| 101 | 5 | blank | Absent: - pages 1, 5 and 16, sheets of buff card blank but for his words top right — covers | transcripts/101/batch-01.fr.tex:18 |
| 101 | 9 | others' typescript | - pages 9 and 13, typed pages of some other French text (page « - 85 - », on « faisceaux fins », and page « II - 18 - », on modules of fract… | transcripts/101/batch-01.fr.tex:24 |
| 101 | 13 | cover/wrapper | 2026-10-20 — dates checked on the facsimile by Michel Hua (#74–76): p. 16, « Notes antiques 1958 » is a label or title on the cover, not the… | transcripts/101/batch-01.fr.tex:11 |
| 101 | 16 | blank | Absent: - pages 1, 5 and 16, sheets of buff card blank but for his words top right — covers | transcripts/101/batch-01.fr.tex:18 |
| 102 | 1 | cover/wrapper | Page 1 is an orange cover inscribed « Recollements » in his hand | transcripts/102/batch-01.fr.tex:7 |
| 102 | 7 | blank | Pages 7 (blank) and 9 (an unrelated printed verso, upside down, exercises on valuations with no hand on it) are skipped, the gap in the page… | transcripts/102/batch-01.fr.tex:5 |
| 102 | 9 | blank | Pages 7 (blank) and 9 (an unrelated printed verso, upside down, exercises on valuations with no hand on it) are skipped, the gap in the page… | transcripts/102/batch-01.fr.tex:5 |
| 103 | 7 | blank | Page 7 is blank and is skipped | transcripts/103/batch-01.fr.tex:29 |
| 105 | 3 | blank | page 3, a sheet of pink card carrying only a pencilled name struck through and a few ink spots, nothing mathematical | transcripts/105/batch-01.fr.tex:13 |
| 105 | 5 | printed/published | pages 5, 7, 10, 12, 14, 16, 18 and 20, sheets of computer listing (job logs, tables, a banner page) carrying nothing of his — page 18 has tw… | transcripts/105/batch-01.fr.tex:13 |
| 105 | 7 | printed/published | pages 5, 7, 10, 12, 14, 16, 18 and 20, sheets of computer listing (job logs, tables, a banner page) carrying nothing of his — page 18 has tw… | transcripts/105/batch-01.fr.tex:13 |
| 105 | 8 | blank | page 8, a blank sheet. | transcripts/105/batch-01.fr.tex:13 |
| 105 | 10 | printed/published | pages 5, 7, 10, 12, 14, 16, 18 and 20, sheets of computer listing (job logs, tables, a banner page) carrying nothing of his — page 18 has tw… | transcripts/105/batch-01.fr.tex:13 |
| 105 | 12 | printed/published | pages 5, 7, 10, 12, 14, 16, 18 and 20, sheets of computer listing (job logs, tables, a banner page) carrying nothing of his — page 18 has tw… | transcripts/105/batch-01.fr.tex:13 |
| 105 | 14 | printed/published | pages 5, 7, 10, 12, 14, 16, 18 and 20, sheets of computer listing (job logs, tables, a banner page) carrying nothing of his — page 18 has tw… | transcripts/105/batch-01.fr.tex:13 |
| 105 | 16 | printed/published | pages 5, 7, 10, 12, 14, 16, 18 and 20, sheets of computer listing (job logs, tables, a banner page) carrying nothing of his — page 18 has tw… | transcripts/105/batch-01.fr.tex:13 |
| 105 | 18 | printed/published | pages 5, 7, 10, 12, 14, 16, 18 and 20, sheets of computer listing (job logs, tables, a banner page) carrying nothing of his — page 18 has tw… | transcripts/105/batch-01.fr.tex:13 |
| 105 | 20 | printed/published | pages 5, 7, 10, 12, 14, 16, 18 and 20, sheets of computer listing (job logs, tables, a banner page) carrying nothing of his — page 18 has tw… | transcripts/105/batch-01.fr.tex:13 |
| 105 | 22 | printed/published | pages 22, 25, 30, 32, 34, 36, 38 and 40, sheets of computer listing (banner pages, job logs, tables) carrying nothing of his — page 36 has t… | transcripts/105/batch-02.fr.tex:13 |
| 105 | 23 | blank | pages 23 and 28, blank sheets. | transcripts/105/batch-02.fr.tex:13 |
| 105 | 25 | printed/published | pages 22, 25, 30, 32, 34, 36, 38 and 40, sheets of computer listing (banner pages, job logs, tables) carrying nothing of his — page 36 has t… | transcripts/105/batch-02.fr.tex:13 |
| 105 | 28 | blank | pages 23 and 28, blank sheets. | transcripts/105/batch-02.fr.tex:13 |
| 105 | 30 | printed/published | pages 22, 25, 30, 32, 34, 36, 38 and 40, sheets of computer listing (banner pages, job logs, tables) carrying nothing of his — page 36 has t… | transcripts/105/batch-02.fr.tex:13 |
| 105 | 32 | printed/published | pages 22, 25, 30, 32, 34, 36, 38 and 40, sheets of computer listing (banner pages, job logs, tables) carrying nothing of his — page 36 has t… | transcripts/105/batch-02.fr.tex:13 |
| 105 | 34 | printed/published | pages 22, 25, 30, 32, 34, 36, 38 and 40, sheets of computer listing (banner pages, job logs, tables) carrying nothing of his — page 36 has t… | transcripts/105/batch-02.fr.tex:13 |
| 105 | 36 | printed/published | pages 22, 25, 30, 32, 34, 36, 38 and 40, sheets of computer listing (banner pages, job logs, tables) carrying nothing of his — page 36 has t… | transcripts/105/batch-02.fr.tex:13 |
| 105 | 38 | printed/published | pages 22, 25, 30, 32, 34, 36, 38 and 40, sheets of computer listing (banner pages, job logs, tables) carrying nothing of his — page 36 has t… | transcripts/105/batch-02.fr.tex:13 |
| 105 | 40 | printed/published | pages 22, 25, 30, 32, 34, 36, 38 and 40, sheets of computer listing (banner pages, job logs, tables) carrying nothing of his — page 36 has t… | transcripts/105/batch-02.fr.tex:13 |
| 105 | 41 | blank | page 41, a blank leaf carrying nothing but a faint ghost of the text of page 42 | transcripts/105/batch-03.fr.tex:12 |
| 105 | 43 | others' typescript | page 43, a typed page (typist's number « 90 ») of prose unrelated to the mathematics, whose only marks by hand are typing corrections. | transcripts/105/batch-03.fr.tex:12 |
| 106 | 4 | skipped, reason not classifiable | Pages 4, 6, 8, 10 and 16 carry nothing of his and are skipped, the gaps in the page numbers being the record. | transcripts/106/batch-01.fr.tex:18 |
| 106 | 6 | skipped, reason not classifiable | Pages 4, 6, 8, 10 and 16 carry nothing of his and are skipped, the gaps in the page numbers being the record. | transcripts/106/batch-01.fr.tex:18 |
| 106 | 8 | skipped, reason not classifiable | Pages 4, 6, 8, 10 and 16 carry nothing of his and are skipped, the gaps in the page numbers being the record. | transcripts/106/batch-01.fr.tex:18 |
| 106 | 10 | skipped, reason not classifiable | Pages 4, 6, 8, 10 and 16 carry nothing of his and are skipped, the gaps in the page numbers being the record. | transcripts/106/batch-01.fr.tex:18 |
| 106 | 16 | skipped, reason not classifiable | Pages 4, 6, 8, 10 and 16 carry nothing of his and are skipped, the gaps in the page numbers being the record. | transcripts/106/batch-01.fr.tex:18 |
| 107 | 1 | cover/wrapper | page 1 (« Formalisme des X (x) M, X^M, Hom_A, Hom_B relatif : ... | transcripts/107/batch-01.fr.tex:30 |
| 107 | 4 | printed/published | Pages skipped: 4, 6, 8, 10, 12 and 19 — the printed sides of JCL and job-log listings, with no mathematics of his (the pencil marks on them … | transcripts/107/batch-01.fr.tex:24 |
| 107 | 6 | printed/published | Pages skipped: 4, 6, 8, 10, 12 and 19 — the printed sides of JCL and job-log listings, with no mathematics of his (the pencil marks on them … | transcripts/107/batch-01.fr.tex:24 |
| 107 | 8 | printed/published | Pages skipped: 4, 6, 8, 10, 12 and 19 — the printed sides of JCL and job-log listings, with no mathematics of his (the pencil marks on them … | transcripts/107/batch-01.fr.tex:24 |
| 107 | 10 | printed/published | Pages skipped: 4, 6, 8, 10, 12 and 19 — the printed sides of JCL and job-log listings, with no mathematics of his (the pencil marks on them … | transcripts/107/batch-01.fr.tex:24 |
| 107 | 12 | printed/published | Pages skipped: 4, 6, 8, 10, 12 and 19 — the printed sides of JCL and job-log listings, with no mathematics of his (the pencil marks on them … | transcripts/107/batch-01.fr.tex:24 |
| 107 | 17 | blank | produits », ink over the header of a listing) and page 17 (« Question des lim filtrantes dans Hot », alone on a blank sheet) are headings fo… | transcripts/107/batch-01.fr.tex:31 |
| 107 | 19 | printed/published | Pages skipped: 4, 6, 8, 10, 12 and 19 — the printed sides of JCL and job-log listings, with no mathematics of his (the pencil marks on them … | transcripts/107/batch-01.fr.tex:24 |
| 107 | 25 | printed/published | Pages skipped: 25, the second page of an assembler listing (« ASM 0201 15.27 06/04/82 ») with nothing of his mathematics on it. | transcripts/107/batch-02.fr.tex:14 |
| 109 | 11 | blank | Skipped pages: 11, 15 and 19, blank tan separator sheets. | transcripts/109/batch-01.fr.tex:10 |
| 109 | 15 | blank | Skipped pages: 11, 15 and 19, blank tan separator sheets. | transcripts/109/batch-01.fr.tex:10 |
| 109 | 19 | blank | Skipped pages: 11, 15 and 19, blank tan separator sheets. | transcripts/109/batch-01.fr.tex:10 |
| 113 | 1 | blank | Page 1 is an otherwise blank computer listing carrying two things in his hand: the single word « Abelianization » in the top right corner, a… | transcripts/113/batch-01.fr.tex:7 |
| 113 | 4 | printed/published | Pages 4, 6, 8 and 10 are listings of that run with nothing of his on them and are skipped | transcripts/113/batch-01.fr.tex:21 |
| 113 | 6 | printed/published | Pages 4, 6, 8 and 10 are listings of that run with nothing of his on them and are skipped | transcripts/113/batch-01.fr.tex:21 |
| 113 | 8 | printed/published | Pages 4, 6, 8 and 10 are listings of that run with nothing of his on them and are skipped | transcripts/113/batch-01.fr.tex:21 |
| 113 | 10 | printed/published | Pages 4, 6, 8 and 10 are listings of that run with nothing of his on them and are skipped | transcripts/113/batch-01.fr.tex:21 |
| 115 | 4 | printed/published | Pages 4, 6 and 12 are versos of unrelated computer listings (dated 02 JUN 82) — absent, as they should be. | transcripts/115/batch-01.fr.tex:4 |
| 115 | 6 | printed/published | Pages 4, 6 and 12 are versos of unrelated computer listings (dated 02 JUN 82) — absent, as they should be. | transcripts/115/batch-01.fr.tex:4 |
| 115 | 12 | printed/published | Pages 4, 6 and 12 are versos of unrelated computer listings (dated 02 JUN 82) — absent, as they should be. | transcripts/115/batch-01.fr.tex:4 |
| 116 | 1 | cover/wrapper | Page 1 is the kraft wrapper the notes were folded into | transcripts/116/batch-01.fr.tex:6 |
| 116 | 8 | blank | Page 8 is blank (only the show-through of page 9 is visible) and page 10 is an administrative notice of the Université des Sciences et Techn… | transcripts/116/batch-01.fr.tex:14 |
| 116 | 10 | blank | Page 8 is blank (only the show-through of page 9 is visible) and page 10 is an administrative notice of the Université des Sciences et Techn… | transcripts/116/batch-01.fr.tex:14 |
| 117 | 6 | administrative | pages 6, 8, 10, 12, 14, 16 and 18, the versos of the leaves carrying his pages 1-7 — ruled administrative tables in another hand (names, amo… | transcripts/117/batch-01.fr.tex:11 |
| 117 | 8 | administrative | pages 6, 8, 10, 12, 14, 16 and 18, the versos of the leaves carrying his pages 1-7 — ruled administrative tables in another hand (names, amo… | transcripts/117/batch-01.fr.tex:11 |
| 117 | 10 | administrative | pages 6, 8, 10, 12, 14, 16 and 18, the versos of the leaves carrying his pages 1-7 — ruled administrative tables in another hand (names, amo… | transcripts/117/batch-01.fr.tex:11 |
| 117 | 12 | administrative | pages 6, 8, 10, 12, 14, 16 and 18, the versos of the leaves carrying his pages 1-7 — ruled administrative tables in another hand (names, amo… | transcripts/117/batch-01.fr.tex:11 |
| 117 | 14 | administrative | pages 6, 8, 10, 12, 14, 16 and 18, the versos of the leaves carrying his pages 1-7 — ruled administrative tables in another hand (names, amo… | transcripts/117/batch-01.fr.tex:11 |
| 117 | 16 | administrative | pages 6, 8, 10, 12, 14, 16 and 18, the versos of the leaves carrying his pages 1-7 — ruled administrative tables in another hand (names, amo… | transcripts/117/batch-01.fr.tex:11 |
| 117 | 18 | administrative | pages 6, 8, 10, 12, 14, 16 and 18, the versos of the leaves carrying his pages 1-7 — ruled administrative tables in another hand (names, amo… | transcripts/117/batch-01.fr.tex:11 |
| 117 | 23 | others' typescript | pages 23 and 25, typed administrative documents (a D.E.A. notice of the USTL, a ministry circular with stamps) carrying nothing in his hand. | transcripts/117/batch-02.fr.tex:11 |
| 117 | 25 | others' typescript | pages 23 and 25, typed administrative documents (a D.E.A. notice of the USTL, a ministry circular with stamps) carrying nothing in his hand. | transcripts/117/batch-02.fr.tex:11 |
| 118 | 1 | cover/wrapper | Absent, with no \page and no note: 1      a pink cover in his hand, « Cohomology properties of maps in (Cat) : 1) Fibration-like properties … | transcripts/118/batch-01.fr.tex:13 |
| 118 | 3 | administrative | 3      an administrative accounts sheet (amounts, « Fonctionnement »), nothing of his | transcripts/118/batch-01.fr.tex:17 |
| 118 | 5 | administrative | 5, 6   ruled administrative tables (seminar names, amounts) in another hand, nothing of his (page 7's paper shows the same table through) | transcripts/118/batch-01.fr.tex:19 |
| 118 | 6 | administrative | 5, 6   ruled administrative tables (seminar names, amounts) in another hand, nothing of his (page 7's paper shows the same table through) | transcripts/118/batch-01.fr.tex:19 |
| 118 | 9 | administrative | 9      a kraft envelope, printed « DU LANGUEDOC », addressed in pencil to him — no mathematics | transcripts/118/batch-01.fr.tex:21 |
| 118 | 12 | unrelated | 12     a sheet inscribed « 1976 » and « Poèmes » in pencil, the first word overwritten — unrelated to the mathematics | transcripts/118/batch-01.fr.tex:23 |
| 118 | 17 | others' typescript | 17     a typed university notice of a doctoral defence, dated « Montpellier, le 29 avril 1985 » — the only dated leaf in the batch | transcripts/118/batch-01.fr.tex:25 |
| 118 | 37 | blank | page 37, a blank sheet (only the archivists' pencil number). | transcripts/118/batch-02.fr.tex:10 |
| 119 | 143 | unrelated | - p. 143: wrapper « Notes de math. oubliées par Jean Malgoire » (probably not his hand) | transcripts/119/batch-08.fr.tex:7 |
| 119 | 146 | blank | - p. 146: blank divider, no \page. | transcripts/119/batch-08.fr.tex:11 |
| 119 | 153 | blank | - p. 153: blank divider, no \page. | transcripts/119/batch-08.fr.tex:14 |
| 119 | 253 | blank | p. 253 — blank archivists' divider | transcripts/119/batch-13.fr.tex:25 |
| 119 | 271 | blank | - p. 271: blank archivists' divider — no \page{}. | transcripts/119/batch-14.fr.tex:10 |
| 119 | 274 | blank | - p. 274: blank archivists' divider — no \page{}. | transcripts/119/batch-14.fr.tex:16 |
| 119 | 276 | others' typescript | - pp. 275–280: « Rapport de la Commission relative au recrutement des enseignants » (Orsay | transcripts/119/batch-14.fr.tex:17 |
| 119 | 277 | others' typescript | - pp. 275–280: « Rapport de la Commission relative au recrutement des enseignants » (Orsay | transcripts/119/batch-14.fr.tex:17 |
| 119 | 278 | others' typescript | - pp. 275–280: « Rapport de la Commission relative au recrutement des enseignants » (Orsay | transcripts/119/batch-14.fr.tex:17 |
| 119 | 279 | others' typescript | - pp. 275–280: « Rapport de la Commission relative au recrutement des enseignants » (Orsay | transcripts/119/batch-14.fr.tex:17 |
| 119 | 280 | others' typescript | - pp. 275–280: « Rapport de la Commission relative au recrutement des enseignants » (Orsay | transcripts/119/batch-14.fr.tex:17 |
| 119 | 281 | blank | Contents of the batch (special rules for folder 119, issues #45 and #49): - pp. 281, 287: blank archivists' divider sheets. | transcripts/119/batch-15.fr.tex:4 |
| 119 | 287 | blank | Contents of the batch (special rules for folder 119, issues #45 and #49): - pp. 281, 287: blank archivists' divider sheets. | transcripts/119/batch-15.fr.tex:4 |
| 119 | 302 | blank | - pp. 302, 307, 309: blank archivists' divider sheets. | transcripts/119/batch-16.fr.tex:8 |
| 119 | 307 | blank | - pp. 302, 307, 309: blank archivists' divider sheets. | transcripts/119/batch-16.fr.tex:8 |
| 119 | 309 | blank | - pp. 302, 307, 309: blank archivists' divider sheets. | transcripts/119/batch-16.fr.tex:8 |
| 120 | 1 | illegible | 2026-10-20 — dates checked on the facsimile by Michel Hua (#74–76): p. 1, the faint pencil « 1978 » on the cover is a label or title, not th… | transcripts/120/batch-01.fr.tex:11 |
| 121 | 2 | blank | Pages skipped: 2, a blank cream sheet. | transcripts/121/batch-01.fr.tex:24 |
| 121 | 24 | blank | Pages skipped: 24, 28, 37 and 39, blank cream separator sheets (only show-through on 37). | transcripts/121/batch-02.fr.tex:18 |
| 121 | 28 | blank | Pages skipped: 24, 28, 37 and 39, blank cream separator sheets (only show-through on 37). | transcripts/121/batch-02.fr.tex:18 |
| 121 | 37 | blank | Pages skipped: 24, 28, 37 and 39, blank cream separator sheets (only show-through on 37). | transcripts/121/batch-02.fr.tex:18 |
| 121 | 39 | blank | Pages skipped: 24, 28, 37 and 39, blank cream separator sheets (only show-through on 37). | transcripts/121/batch-02.fr.tex:18 |
| 121 | 47 | administrative | No letter appears in this batch: the 1974 letter of the inventory is not among pages 41-60. | transcripts/121/batch-03.fr.tex:20 |
| 121 | 52 | blank | Pages skipped: 52, a blank cream sheet. | transcripts/121/batch-03.fr.tex:20 |
| 121 | 63 | blank | Pages skipped: 63 and 68, blank cream separator sheets. | transcripts/121/batch-04.fr.tex:32 |
| 121 | 68 | blank | Pages skipped: 63 and 68, blank cream separator sheets. | transcripts/121/batch-04.fr.tex:32 |
| 122 | 1 | blank | Pages skipped: 1 and 18, blank cream sheets | transcripts/122/batch-01.fr.tex:12 |
| 122 | 3 | others' typescript | 3, 5, 7, 9, 11, 13, 15, typed leaves of a Bourbaki draft (« n° 387 », pp. -42- to -48-, exercises on valuations, linearly compact modules an… | transcripts/122/batch-01.fr.tex:12 |
| 122 | 5 | others' typescript | 3, 5, 7, 9, 11, 13, 15, typed leaves of a Bourbaki draft (« n° 387 », pp. -42- to -48-, exercises on valuations, linearly compact modules an… | transcripts/122/batch-01.fr.tex:12 |
| 122 | 7 | others' typescript | 3, 5, 7, 9, 11, 13, 15, typed leaves of a Bourbaki draft (« n° 387 », pp. -42- to -48-, exercises on valuations, linearly compact modules an… | transcripts/122/batch-01.fr.tex:12 |
| 122 | 9 | others' typescript | 3, 5, 7, 9, 11, 13, 15, typed leaves of a Bourbaki draft (« n° 387 », pp. -42- to -48-, exercises on valuations, linearly compact modules an… | transcripts/122/batch-01.fr.tex:12 |
| 122 | 11 | others' typescript | 3, 5, 7, 9, 11, 13, 15, typed leaves of a Bourbaki draft (« n° 387 », pp. -42- to -48-, exercises on valuations, linearly compact modules an… | transcripts/122/batch-01.fr.tex:12 |
| 122 | 13 | others' typescript | 3, 5, 7, 9, 11, 13, 15, typed leaves of a Bourbaki draft (« n° 387 », pp. -42- to -48-, exercises on valuations, linearly compact modules an… | transcripts/122/batch-01.fr.tex:12 |
| 122 | 15 | others' typescript | 3, 5, 7, 9, 11, 13, 15, typed leaves of a Bourbaki draft (« n° 387 », pp. -42- to -48-, exercises on valuations, linearly compact modules an… | transcripts/122/batch-01.fr.tex:12 |
| 122 | 17 | others' typescript | 17, a typed announcement from the Institut Henri Poincaré (lectures by N. | transcripts/122/batch-01.fr.tex:12 |
| 122 | 18 | blank | Pages skipped: 1 and 18, blank cream sheets | transcripts/122/batch-01.fr.tex:12 |
| 122 | 20 | others' typescript | 20, a leaf (-4.15-) of the English typescript on geometric quotients whose other leaves are the versos of batch 2. | transcripts/122/batch-01.fr.tex:16 |
| 122 | 22 | verso (unspecified) | Pages skipped: 22, 24, 26, 28, 30, 32 — the versos. | transcripts/122/batch-02.fr.tex:12 |
| 122 | 24 | verso (unspecified) | Pages skipped: 22, 24, 26, 28, 30, 32 — the versos. | transcripts/122/batch-02.fr.tex:12 |
| 122 | 26 | verso (unspecified) | Pages skipped: 22, 24, 26, 28, 30, 32 — the versos. | transcripts/122/batch-02.fr.tex:12 |
| 122 | 28 | verso (unspecified) | Pages skipped: 22, 24, 26, 28, 30, 32 — the versos. | transcripts/122/batch-02.fr.tex:12 |
| 122 | 30 | verso (unspecified) | Pages skipped: 22, 24, 26, 28, 30, 32 — the versos. | transcripts/122/batch-02.fr.tex:12 |
| 122 | 32 | verso (unspecified) | Pages skipped: 22, 24, 26, 28, 30, 32 — the versos. | transcripts/122/batch-02.fr.tex:12 |
| 123 | 3 | cover/wrapper | Absent: - pages 3, 7 and 14, covers bearing only a title in his hand | transcripts/123/batch-01.fr.tex:14 |
| 123 | 7 | cover/wrapper | Absent: - pages 3, 7 and 14, covers bearing only a title in his hand | transcripts/123/batch-01.fr.tex:14 |
| 123 | 14 | cover/wrapper | Absent: - pages 3, 7 and 14, covers bearing only a title in his hand | transcripts/123/batch-01.fr.tex:14 |
| 123 | 20 | blank | - page 20, a blank buff sheet. | transcripts/123/batch-01.fr.tex:20 |
| 123 | 23 | cover/wrapper | Absent: - 23 and 36, covers bearing only a title in his hand (buff paper) | transcripts/123/batch-02.fr.tex:12 |
| 123 | 24 | blank | - 24 and 32, blank buff sheets. | transcripts/123/batch-02.fr.tex:18 |
| 123 | 32 | blank | - 24 and 32, blank buff sheets. | transcripts/123/batch-02.fr.tex:18 |
| 123 | 36 | cover/wrapper | Absent: - 23 and 36, covers bearing only a title in his hand (buff paper) | transcripts/123/batch-02.fr.tex:12 |
| 123 | 42 | blank | - page 42 is a cover: an otherwise blank sheet inscribed top right « Résumé de quelques résultats de Kostant ». | transcripts/123/batch-03.fr.tex:18 |
| 125 | 1 | cover/wrapper | The cover (page 1) reads "Dualité locale et dualité projective", with one word blotted out between "dualité" and "projective". | transcripts/125/batch-01.fr.tex:6 |
| 126 | 15 | cover/wrapper | Page 15 is a tan cover inscribed in ink, top right and underlined, « Descente fidèlement plate » | transcripts/126/batch-01.fr.tex:14 |
| 126 | 16 | blank | Pages skipped: 16, a blank white sheet. | transcripts/126/batch-01.fr.tex:14 |
| 126 | 24 | blank | Pages skipped: 24, a blank sheet of the typist's letterhead (M. | transcripts/126/batch-02.fr.tex:12 |
| 126 | 25 | blank | 25 and 30, blank sheets (only show-through). | transcripts/126/batch-02.fr.tex:12 |
| 126 | 30 | blank | 25 and 30, blank sheets (only show-through). | transcripts/126/batch-02.fr.tex:12 |
| 127 | 1 | cover/wrapper | Page 1 is a tan cover inscribed in ink, top right, underlined: « Application de la descente non plate : platitude d'une adhérence schématiqu… | transcripts/127/batch-01.fr.tex:19 |
| 127 | 21 | blank | Page 21 is a tan sheet, otherwise blank, inscribed top right in brown ink « foncteurs non / [struck: Morphismes non] / ramifiés, / étales ..… | transcripts/127/batch-02.fr.tex:20 |
| 128 | 30 | blank | Pages skipped: 30, a blank tan sheet (presumably the back cover of the run), nothing in anyone's hand. | transcripts/128/batch-02.fr.tex:16 |
| 129 | 14 | blank | Pages skipped: 14, a blank cream sheet. | transcripts/129/batch-01.fr.tex:15 |
| 129 | 78 | blank | Pages skipped: 78, a blank cream sheet. | transcripts/129/batch-04.fr.tex:16 |
| 129 | 88 | blank | Pages skipped, without description: 88 (a blank cream sheet) | transcripts/129/batch-05.fr.tex:25 |
| 129 | 96 | blank | - 96 is a cover: an otherwise blank sheet inscribed in ink top right « Sorites sur Groupes p-divisibles et groupes de B.T. » | transcripts/129/batch-05.fr.tex:36 |
| 129 | 98 | others' typescript | 98 and 100 (typed duplicator pages of an unrelated text, « n° 380 », pp. 48 and 51, on spectra of algebras of bounded functions -- the front… | transcripts/129/batch-05.fr.tex:25 |
| 129 | 100 | others' typescript | 98 and 100 (typed duplicator pages of an unrelated text, « n° 380 », pp. 48 and 51, on spectra of algebras of bounded functions -- the front… | transcripts/129/batch-05.fr.tex:25 |
| 129 | 102 | others' typescript | Pages skipped, without description: 102, 104, 108, 110 (typed pages of an unrelated text, versos of his sheets, blue duplicator copies numbe… | transcripts/129/batch-06.fr.tex:25 |
| 129 | 104 | others' typescript | Pages skipped, without description: 102, 104, 108, 110 (typed pages of an unrelated text, versos of his sheets, blue duplicator copies numbe… | transcripts/129/batch-06.fr.tex:25 |
| 129 | 108 | others' typescript | Pages skipped, without description: 102, 104, 108, 110 (typed pages of an unrelated text, versos of his sheets, blue duplicator copies numbe… | transcripts/129/batch-06.fr.tex:25 |
| 129 | 110 | others' typescript | Pages skipped, without description: 102, 104, 108, 110 (typed pages of an unrelated text, versos of his sheets, blue duplicator copies numbe… | transcripts/129/batch-06.fr.tex:25 |
| 129 | 111 | blank | one handwritten word inserted on 102, hand undetermined, part of that text's own correction), and 111 (a blank cream sheet). | transcripts/129/batch-06.fr.tex:25 |
| 130 | 1 | blank | page 1, an otherwise blank sheet inscribed in his hand, top right, « Formules de Néron » — a cover, whose words become the first \section he… | transcripts/130/batch-01.fr.tex:16 |
| 130 | 2 | blank | pages 2, 8, 15 and 20, blank | transcripts/130/batch-01.fr.tex:16 |
| 130 | 8 | blank | pages 2, 8, 15 and 20, blank | transcripts/130/batch-01.fr.tex:16 |
| 130 | 15 | blank | pages 2, 8, 15 and 20, blank | transcripts/130/batch-01.fr.tex:16 |
| 130 | 17 | others' typescript | pages 17 and 19, two leaves of a Bourbaki typescript (n° 383, « -VII-10- » and « -VII-9- », on Dynkin diagrams), printed (their text shows t… | transcripts/130/batch-01.fr.tex:16 |
| 130 | 19 | others' typescript | pages 17 and 19, two leaves of a Bourbaki typescript (n° 383, « -VII-10- » and « -VII-9- », on Dynkin diagrams), printed (their text shows t… | transcripts/130/batch-01.fr.tex:16 |
| 130 | 20 | blank | pages 2, 8, 15 and 20, blank | transcripts/130/batch-01.fr.tex:16 |
| 130 | 22 | others' typescript | pages 22, 24, 26, 28, 30, 32, typed pages of an unrelated duplicated typescript with nothing in his hand | transcripts/130/batch-02.fr.tex:11 |
| 130 | 24 | others' typescript | pages 22, 24, 26, 28, 30, 32, typed pages of an unrelated duplicated typescript with nothing in his hand | transcripts/130/batch-02.fr.tex:11 |
| 130 | 26 | others' typescript | pages 22, 24, 26, 28, 30, 32, typed pages of an unrelated duplicated typescript with nothing in his hand | transcripts/130/batch-02.fr.tex:11 |
| 130 | 28 | others' typescript | pages 22, 24, 26, 28, 30, 32, typed pages of an unrelated duplicated typescript with nothing in his hand | transcripts/130/batch-02.fr.tex:11 |
| 130 | 30 | others' typescript | pages 22, 24, 26, 28, 30, 32, typed pages of an unrelated duplicated typescript with nothing in his hand | transcripts/130/batch-02.fr.tex:11 |
| 130 | 32 | others' typescript | pages 22, 24, 26, 28, 30, 32, typed pages of an unrelated duplicated typescript with nothing in his hand | transcripts/130/batch-02.fr.tex:11 |
| 130 | 33 | blank | page 33, a blank leaf. | transcripts/130/batch-02.fr.tex:11 |
| 130 | 49 | others' typescript | page 49, a typed page of someone else's text (a draft on integration, « n°357 », « - 82 - ») crossed by two long strokes, with nothing of hi… | transcripts/130/batch-03.fr.tex:12 |
| 131 | 7 | others' typescript | pages 7, 9, 12 and 20, leaves of a typed text by someone else (headed « n° 392 », pages « 4-27 », « 4-26 », « 4-24 », and « n° 371 », page «… | transcripts/131/batch-01.fr.tex:17 |
| 131 | 9 | others' typescript | pages 7, 9, 12 and 20, leaves of a typed text by someone else (headed « n° 392 », pages « 4-27 », « 4-26 », « 4-24 », and « n° 371 », page «… | transcripts/131/batch-01.fr.tex:17 |
| 131 | 10 | blank | pages 10 and 18, blank | transcripts/131/batch-01.fr.tex:17 |
| 131 | 12 | others' typescript | pages 7, 9, 12 and 20, leaves of a typed text by someone else (headed « n° 392 », pages « 4-27 », « 4-26 », « 4-24 », and « n° 371 », page «… | transcripts/131/batch-01.fr.tex:17 |
| 131 | 18 | blank | pages 10 and 18, blank | transcripts/131/batch-01.fr.tex:17 |
| 131 | 20 | others' typescript | pages 7, 9, 12 and 20, leaves of a typed text by someone else (headed « n° 392 », pages « 4-27 », « 4-26 », « 4-24 », and « n° 371 », page «… | transcripts/131/batch-01.fr.tex:17 |
| 131 | 21 | blank | page 21, a blank leaf | transcripts/131/batch-02.fr.tex:12 |
| 131 | 23 | others' typescript | pages 23, 25, 27, 29, 31, 33, 35, 37, 39, typed pages of an unrelated duplicated typescript (a Bourbaki draft, « n° 371 », on tensor product… | transcripts/131/batch-02.fr.tex:12 |
| 131 | 25 | others' typescript | pages 23, 25, 27, 29, 31, 33, 35, 37, 39, typed pages of an unrelated duplicated typescript (a Bourbaki draft, « n° 371 », on tensor product… | transcripts/131/batch-02.fr.tex:12 |
| 131 | 27 | others' typescript | pages 23, 25, 27, 29, 31, 33, 35, 37, 39, typed pages of an unrelated duplicated typescript (a Bourbaki draft, « n° 371 », on tensor product… | transcripts/131/batch-02.fr.tex:12 |
| 131 | 29 | others' typescript | pages 23, 25, 27, 29, 31, 33, 35, 37, 39, typed pages of an unrelated duplicated typescript (a Bourbaki draft, « n° 371 », on tensor product… | transcripts/131/batch-02.fr.tex:12 |
| 131 | 31 | others' typescript | pages 23, 25, 27, 29, 31, 33, 35, 37, 39, typed pages of an unrelated duplicated typescript (a Bourbaki draft, « n° 371 », on tensor product… | transcripts/131/batch-02.fr.tex:12 |
| 131 | 33 | others' typescript | pages 23, 25, 27, 29, 31, 33, 35, 37, 39, typed pages of an unrelated duplicated typescript (a Bourbaki draft, « n° 371 », on tensor product… | transcripts/131/batch-02.fr.tex:12 |
| 131 | 35 | others' typescript | pages 23, 25, 27, 29, 31, 33, 35, 37, 39, typed pages of an unrelated duplicated typescript (a Bourbaki draft, « n° 371 », on tensor product… | transcripts/131/batch-02.fr.tex:12 |
| 131 | 37 | others' typescript | pages 23, 25, 27, 29, 31, 33, 35, 37, 39, typed pages of an unrelated duplicated typescript (a Bourbaki draft, « n° 371 », on tensor product… | transcripts/131/batch-02.fr.tex:12 |
| 131 | 39 | others' typescript | pages 23, 25, 27, 29, 31, 33, 35, 37, 39, typed pages of an unrelated duplicated typescript (a Bourbaki draft, « n° 371 », on tensor product… | transcripts/131/batch-02.fr.tex:12 |
| 131 | 41 | others' typescript | Page 41 is one more leaf of the unrelated duplicated typescript already met in batches 1 and 2 (« n° 371 », here its page « - 25 - »: a Bour… | transcripts/131/batch-03.fr.tex:10 |
| 132 | 4 | blank | Pages skipped: 4, 9 and 12, blank sheets (only show-through). | transcripts/132/batch-01.fr.tex:29 |
| 132 | 9 | blank | Pages skipped: 4, 9 and 12, blank sheets (only show-through). | transcripts/132/batch-01.fr.tex:29 |
| 132 | 12 | blank | Pages skipped: 4, 9 and 12, blank sheets (only show-through). | transcripts/132/batch-01.fr.tex:29 |
| 132 | 24 | blank | Page skipped: 24, a blank cream sheet. | transcripts/132/batch-02.fr.tex:22 |
| 133 | 1 | blank | page 1, an otherwise blank sheet of pink card inscribed in his hand « groupes Witt et formes quadratiques » — a cover, whose words become th… | transcripts/133/batch-01.fr.tex:15 |
| 133 | 4 | blank | pages 4 and 9, blank | transcripts/133/batch-01.fr.tex:15 |
| 133 | 9 | blank | pages 4 and 9, blank | transcripts/133/batch-01.fr.tex:15 |
| 133 | 10 | printed/published | pages 10-16, two offprints, printed, with nothing in his hand on any of the seven leaves (checked at 250 dpi and by an ink-colour count), he… | transcripts/133/batch-01.fr.tex:15 |
| 133 | 11 | printed/published | pages 10-16, two offprints, printed, with nothing in his hand on any of the seven leaves (checked at 250 dpi and by an ink-colour count), he… | transcripts/133/batch-01.fr.tex:15 |
| 133 | 12 | printed/published | pages 10-16, two offprints, printed, with nothing in his hand on any of the seven leaves (checked at 250 dpi and by an ink-colour count), he… | transcripts/133/batch-01.fr.tex:15 |
| 133 | 13 | printed/published | pages 10-16, two offprints, printed, with nothing in his hand on any of the seven leaves (checked at 250 dpi and by an ink-colour count), he… | transcripts/133/batch-01.fr.tex:15 |
| 133 | 14 | printed/published | pages 10-16, two offprints, printed, with nothing in his hand on any of the seven leaves (checked at 250 dpi and by an ink-colour count), he… | transcripts/133/batch-01.fr.tex:15 |
| 133 | 15 | printed/published | pages 10-16, two offprints, printed, with nothing in his hand on any of the seven leaves (checked at 250 dpi and by an ink-colour count), he… | transcripts/133/batch-01.fr.tex:15 |
| 133 | 16 | printed/published | pages 10-16, two offprints, printed, with nothing in his hand on any of the seven leaves (checked at 250 dpi and by an ink-colour count), he… | transcripts/133/batch-01.fr.tex:15 |
| 133 | 34 | blank | page 34, an otherwise blank leaf inscribed in his hand « Groupes formels » — a cover, whose words become the \section heading before page 35… | transcripts/133/batch-02.fr.tex:16 |
| 133 | 40 | blank | page 40, a blank leaf, nothing in his hand. | transcripts/133/batch-02.fr.tex:16 |
| 133 | 44 | blank | page 44, an otherwise blank leaf inscribed in his hand « Fourbis auxiliaires cohomologiques pour groupes formels » — a cover, whose words be… | transcripts/133/batch-03.fr.tex:20 |
| 133 | 47 | others' typescript | pages 47 and 49, typed notices of the USTL administration, nothing in his hand. | transcripts/133/batch-03.fr.tex:20 |
| 133 | 49 | others' typescript | pages 47 and 49, typed notices of the USTL administration, nothing in his hand. | transcripts/133/batch-03.fr.tex:20 |
| 134-1 | 1 | cover/wrapper | Page 1 is the folder's own pink cover, carrying only the title "Lettres Breen 75, 76" from which the inventory takes its own | transcripts/134-1/batch-01.fr.tex:7 |
| 134-1 | 2 | blank | page 2 is blank. | transcripts/134-1/batch-01.fr.tex:7 |
| 134-2 | 1 | skipped, reason not classifiable | Letters in this batch: pp. 14-20 — to Daniel Quillen, « Les Aumettes 19.2.1983 » (cont. 20.2), English, his own: skipped as Pursuing Stacks … | transcripts/134-2/batch-01.fr.tex:25 |
| 134-2 | 82 | blank | - p. 82: blank but for a pencilled « I » | transcripts/134-2/batch-05.fr.tex:14 |
| 134-2 | 90 | unrelated | - p. 90: an unrelated verso (Bourbaki seminar abstracts, not his, upside down) | transcripts/134-2/batch-05.fr.tex:36 |
| 134-2 | 91 | blank | absent. p. 91: blank | transcripts/134-2/batch-05.fr.tex:37 |
| 134-2 | 116 | blank | - p. 116 (pencilled 117): blank | transcripts/134-2/batch-06.fr.tex:31 |
| 134-2 | 121 | blank | Contents of the batch: - p. 121 (pencilled 122): blank | transcripts/134-2/batch-07.fr.tex:16 |
| 134-2 | 127 | printed/published | - p. 127 (pencilled 128): unrelated verso (computer listing) | transcripts/134-2/batch-07.fr.tex:26 |
| 134-2 | 144 | blank | - p. 144 (pencilled 145): blank | transcripts/134-2/batch-08.fr.tex:20 |
| 134-8 | 61 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 62 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 64 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 65 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 66 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 67 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 68 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 69 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 70 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 71 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 72 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 73 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 74 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 75 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 76 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 77 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 78 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 79 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 134-8 | 80 | gap only (no header mention) |  | transcripts/134-8/batch-04.fr.tex:1 |
| 135 | 1 | blank | Pages 1 and 6 are blank — absent. | transcripts/135/batch-01.fr.tex:4 |
| 135 | 3 | others' typescript | Pages 3 and 5 are two copies of the same English typescript, a song titled "Lonely Road" (the second copy struck through twice in ink) — reu… | transcripts/135/batch-01.fr.tex:4 |
| 135 | 5 | others' typescript | Pages 3 and 5 are two copies of the same English typescript, a song titled "Lonely Road" (the second copy struck through twice in ink) — reu… | transcripts/135/batch-01.fr.tex:4 |
| 135 | 6 | blank | Pages 1 and 6 are blank — absent. | transcripts/135/batch-01.fr.tex:4 |
| 135 | 24 | blank | Pages 24, 30, 34 and 38 are blank — absent. | transcripts/135/batch-02.fr.tex:4 |
| 135 | 30 | blank | Pages 24, 30, 34 and 38 are blank — absent. | transcripts/135/batch-02.fr.tex:4 |
| 135 | 33 | unrelated | Page 33 is a handwritten French poem titled "Rêve", struck through with long diagonal strokes — not the mathematics in hand, absent. | transcripts/135/batch-02.fr.tex:4 |
| 135 | 34 | blank | Pages 24, 30, 34 and 38 are blank — absent. | transcripts/135/batch-02.fr.tex:4 |
| 135 | 36 | gap only (no header mention) |  | transcripts/135/batch-02.fr.tex:1 |
| 135 | 38 | blank | Pages 24, 30, 34 and 38 are blank — absent. | transcripts/135/batch-02.fr.tex:4 |
| 135 | 45 | blank | Page 45 is blank — absent. | transcripts/135/batch-03.fr.tex:4 |
| 136 | 1 | cover/wrapper | Page 1 is an orange cover inscribed in his hand | transcripts/136/batch-01.fr.tex:4 |
| 136 | 18 | blank | Page 18 is a blank coloured sheet. | transcripts/136/batch-01.fr.tex:5 |
| 136 | 35 | others' typescript | Pages 35, 37 and 39 are skipped: two typescript pages (numbered 13.4.10 and "- 180 - IX") carrying no work of this batch, and an administrat… | transcripts/136/batch-02.fr.tex:4 |
| 136 | 37 | others' typescript | Pages 35, 37 and 39 are skipped: two typescript pages (numbered 13.4.10 and "- 180 - IX") carrying no work of this batch, and an administrat… | transcripts/136/batch-02.fr.tex:4 |
| 136 | 39 | others' typescript | Pages 35, 37 and 39 are skipped: two typescript pages (numbered 13.4.10 and "- 180 - IX") carrying no work of this batch, and an administrat… | transcripts/136/batch-02.fr.tex:4 |
| 136 | 41 | blank | Pages 41, 43, 45, 46, 48, 50, 52, 54, 56, 58 and 60 are not transcribed: typed versos by other hands (administrative minutes, typescripts) o… | transcripts/136/batch-03.fr.tex:4 |
| 136 | 43 | blank | Pages 41, 43, 45, 46, 48, 50, 52, 54, 56, 58 and 60 are not transcribed: typed versos by other hands (administrative minutes, typescripts) o… | transcripts/136/batch-03.fr.tex:4 |
| 136 | 45 | blank | Pages 41, 43, 45, 46, 48, 50, 52, 54, 56, 58 and 60 are not transcribed: typed versos by other hands (administrative minutes, typescripts) o… | transcripts/136/batch-03.fr.tex:4 |
| 136 | 46 | blank | Pages 41, 43, 45, 46, 48, 50, 52, 54, 56, 58 and 60 are not transcribed: typed versos by other hands (administrative minutes, typescripts) o… | transcripts/136/batch-03.fr.tex:4 |
| 136 | 48 | blank | Pages 41, 43, 45, 46, 48, 50, 52, 54, 56, 58 and 60 are not transcribed: typed versos by other hands (administrative minutes, typescripts) o… | transcripts/136/batch-03.fr.tex:4 |
| 136 | 50 | blank | Pages 41, 43, 45, 46, 48, 50, 52, 54, 56, 58 and 60 are not transcribed: typed versos by other hands (administrative minutes, typescripts) o… | transcripts/136/batch-03.fr.tex:4 |
| 136 | 52 | blank | Pages 41, 43, 45, 46, 48, 50, 52, 54, 56, 58 and 60 are not transcribed: typed versos by other hands (administrative minutes, typescripts) o… | transcripts/136/batch-03.fr.tex:4 |
| 136 | 54 | blank | Pages 41, 43, 45, 46, 48, 50, 52, 54, 56, 58 and 60 are not transcribed: typed versos by other hands (administrative minutes, typescripts) o… | transcripts/136/batch-03.fr.tex:4 |
| 136 | 56 | blank | Pages 41, 43, 45, 46, 48, 50, 52, 54, 56, 58 and 60 are not transcribed: typed versos by other hands (administrative minutes, typescripts) o… | transcripts/136/batch-03.fr.tex:4 |
| 136 | 58 | blank | Pages 41, 43, 45, 46, 48, 50, 52, 54, 56, 58 and 60 are not transcribed: typed versos by other hands (administrative minutes, typescripts) o… | transcripts/136/batch-03.fr.tex:4 |
| 136 | 60 | blank | Pages 41, 43, 45, 46, 48, 50, 52, 54, 56, 58 and 60 are not transcribed: typed versos by other hands (administrative minutes, typescripts) o… | transcripts/136/batch-03.fr.tex:4 |
| 136 | 62 | blank | Pages 62, 70 and 72 are typescript pages of an unrelated text (verso), and page 78 is a blank folder cover: none is transcribed. | transcripts/136/batch-04.fr.tex:4 |
| 136 | 70 | blank | Pages 62, 70 and 72 are typescript pages of an unrelated text (verso), and page 78 is a blank folder cover: none is transcribed. | transcripts/136/batch-04.fr.tex:4 |
| 136 | 72 | blank | Pages 62, 70 and 72 are typescript pages of an unrelated text (verso), and page 78 is a blank folder cover: none is transcribed. | transcripts/136/batch-04.fr.tex:4 |
| 136 | 78 | blank | Pages 62, 70 and 72 are typescript pages of an unrelated text (verso), and page 78 is a blank folder cover: none is transcribed. | transcripts/136/batch-04.fr.tex:4 |
| 136 | 83 | blank | Pages 83, 85, 87, 89, 91, 92, 94, 96, 98 and 100 carry no writing of his (typescripts by other hands, or blank) and are absent. | transcripts/136/batch-05.fr.tex:8 |
| 136 | 85 | blank | Pages 83, 85, 87, 89, 91, 92, 94, 96, 98 and 100 carry no writing of his (typescripts by other hands, or blank) and are absent. | transcripts/136/batch-05.fr.tex:8 |
| 136 | 87 | blank | Pages 83, 85, 87, 89, 91, 92, 94, 96, 98 and 100 carry no writing of his (typescripts by other hands, or blank) and are absent. | transcripts/136/batch-05.fr.tex:8 |
| 136 | 89 | blank | Pages 83, 85, 87, 89, 91, 92, 94, 96, 98 and 100 carry no writing of his (typescripts by other hands, or blank) and are absent. | transcripts/136/batch-05.fr.tex:8 |
| 136 | 91 | blank | Pages 83, 85, 87, 89, 91, 92, 94, 96, 98 and 100 carry no writing of his (typescripts by other hands, or blank) and are absent. | transcripts/136/batch-05.fr.tex:8 |
| 136 | 92 | blank | Pages 83, 85, 87, 89, 91, 92, 94, 96, 98 and 100 carry no writing of his (typescripts by other hands, or blank) and are absent. | transcripts/136/batch-05.fr.tex:8 |
| 136 | 94 | blank | Pages 83, 85, 87, 89, 91, 92, 94, 96, 98 and 100 carry no writing of his (typescripts by other hands, or blank) and are absent. | transcripts/136/batch-05.fr.tex:8 |
| 136 | 96 | blank | Pages 83, 85, 87, 89, 91, 92, 94, 96, 98 and 100 carry no writing of his (typescripts by other hands, or blank) and are absent. | transcripts/136/batch-05.fr.tex:8 |
| 136 | 98 | blank | Pages 83, 85, 87, 89, 91, 92, 94, 96, 98 and 100 carry no writing of his (typescripts by other hands, or blank) and are absent. | transcripts/136/batch-05.fr.tex:8 |
| 136 | 100 | blank | Pages 83, 85, 87, 89, 91, 92, 94, 96, 98 and 100 carry no writing of his (typescripts by other hands, or blank) and are absent. | transcripts/136/batch-05.fr.tex:8 |
| 136 | 102 | others' typescript | Skipped as unrelated: pp. 102, 106, 111, 113, 115 (typescript of a text on monodromy pairings and Néron models, used as scrap paper, no ink … | transcripts/136/batch-06.fr.tex:5 |
| 136 | 106 | others' typescript | Skipped as unrelated: pp. 102, 106, 111, 113, 115 (typescript of a text on monodromy pairings and Néron models, used as scrap paper, no ink … | transcripts/136/batch-06.fr.tex:5 |
| 136 | 108 | others' typescript | p. 108 (English typescript by another hand) | transcripts/136/batch-06.fr.tex:5 |
| 136 | 109 | blank | p. 109 (blank ruled sheet) | transcripts/136/batch-06.fr.tex:8 |
| 136 | 111 | others' typescript | Skipped as unrelated: pp. 102, 106, 111, 113, 115 (typescript of a text on monodromy pairings and Néron models, used as scrap paper, no ink … | transcripts/136/batch-06.fr.tex:5 |
| 136 | 113 | others' typescript | Skipped as unrelated: pp. 102, 106, 111, 113, 115 (typescript of a text on monodromy pairings and Néron models, used as scrap paper, no ink … | transcripts/136/batch-06.fr.tex:5 |
| 136 | 115 | others' typescript | Skipped as unrelated: pp. 102, 106, 111, 113, 115 (typescript of a text on monodromy pairings and Néron models, used as scrap paper, no ink … | transcripts/136/batch-06.fr.tex:5 |
| 136 | 117 | administrative | p. 117 (the opening of a personal letter, no mathematics) | transcripts/136/batch-06.fr.tex:8 |
| 136 | 119 | administrative | p. 119 (third-party letter, not circulated | transcripts/136/batch-06.fr.tex:8 |
| 136 | 121 | blank | Page 121 is a blank coloured sheet | transcripts/136/batch-07.fr.tex:5 |
| 136 | 123 | printed/published | the odd pages 123–139 are printed proofs of an unrelated SGA 7 exposé (versos), skipped without description. | transcripts/136/batch-07.fr.tex:6 |
| 136 | 125 | printed/published | the odd pages 123–139 are printed proofs of an unrelated SGA 7 exposé (versos), skipped without description. | transcripts/136/batch-07.fr.tex:6 |
| 136 | 127 | printed/published | the odd pages 123–139 are printed proofs of an unrelated SGA 7 exposé (versos), skipped without description. | transcripts/136/batch-07.fr.tex:6 |
| 136 | 129 | printed/published | the odd pages 123–139 are printed proofs of an unrelated SGA 7 exposé (versos), skipped without description. | transcripts/136/batch-07.fr.tex:6 |
| 136 | 131 | printed/published | the odd pages 123–139 are printed proofs of an unrelated SGA 7 exposé (versos), skipped without description. | transcripts/136/batch-07.fr.tex:6 |
| 136 | 133 | printed/published | the odd pages 123–139 are printed proofs of an unrelated SGA 7 exposé (versos), skipped without description. | transcripts/136/batch-07.fr.tex:6 |
| 136 | 135 | printed/published | the odd pages 123–139 are printed proofs of an unrelated SGA 7 exposé (versos), skipped without description. | transcripts/136/batch-07.fr.tex:6 |
| 136 | 137 | printed/published | the odd pages 123–139 are printed proofs of an unrelated SGA 7 exposé (versos), skipped without description. | transcripts/136/batch-07.fr.tex:6 |
| 136 | 139 | printed/published | the odd pages 123–139 are printed proofs of an unrelated SGA 7 exposé (versos), skipped without description. | transcripts/136/batch-07.fr.tex:6 |
| 136 | 141 | others' typescript | Skipped (no \page): 141, 153, 155, 157 (typed pages of an SGA 7 exposé IX typescript, nothing in his hand bearing on these notes) | transcripts/136/batch-08.fr.tex:4 |
| 136 | 142 | printed/published | 142 (computer listing) | transcripts/136/batch-08.fr.tex:4 |
| 136 | 153 | others' typescript | Skipped (no \page): 141, 153, 155, 157 (typed pages of an SGA 7 exposé IX typescript, nothing in his hand bearing on these notes) | transcripts/136/batch-08.fr.tex:4 |
| 136 | 155 | others' typescript | Skipped (no \page): 141, 153, 155, 157 (typed pages of an SGA 7 exposé IX typescript, nothing in his hand bearing on these notes) | transcripts/136/batch-08.fr.tex:4 |
| 136 | 157 | others' typescript | Skipped (no \page): 141, 153, 155, 157 (typed pages of an SGA 7 exposé IX typescript, nothing in his hand bearing on these notes) | transcripts/136/batch-08.fr.tex:4 |
| 136 | 160 | blank | 160 (blank). | transcripts/136/batch-08.fr.tex:4 |
| 136 | 164 | others' typescript | The other even pages (164–180) are typed pages of a SGA 7 exposé IX typescript, unrelated to the mathematics in hand, and are skipped. | transcripts/136/batch-09.fr.tex:4 |
| 136 | 166 | others' typescript | The other even pages (164–180) are typed pages of a SGA 7 exposé IX typescript, unrelated to the mathematics in hand, and are skipped. | transcripts/136/batch-09.fr.tex:4 |
| 136 | 168 | others' typescript | The other even pages (164–180) are typed pages of a SGA 7 exposé IX typescript, unrelated to the mathematics in hand, and are skipped. | transcripts/136/batch-09.fr.tex:4 |
| 136 | 170 | others' typescript | The other even pages (164–180) are typed pages of a SGA 7 exposé IX typescript, unrelated to the mathematics in hand, and are skipped. | transcripts/136/batch-09.fr.tex:4 |
| 136 | 172 | others' typescript | The other even pages (164–180) are typed pages of a SGA 7 exposé IX typescript, unrelated to the mathematics in hand, and are skipped. | transcripts/136/batch-09.fr.tex:4 |
| 136 | 174 | others' typescript | The other even pages (164–180) are typed pages of a SGA 7 exposé IX typescript, unrelated to the mathematics in hand, and are skipped. | transcripts/136/batch-09.fr.tex:4 |
| 136 | 176 | others' typescript | The other even pages (164–180) are typed pages of a SGA 7 exposé IX typescript, unrelated to the mathematics in hand, and are skipped. | transcripts/136/batch-09.fr.tex:4 |
| 136 | 178 | others' typescript | The other even pages (164–180) are typed pages of a SGA 7 exposé IX typescript, unrelated to the mathematics in hand, and are skipped. | transcripts/136/batch-09.fr.tex:4 |
| 136 | 180 | others' typescript | The other even pages (164–180) are typed pages of a SGA 7 exposé IX typescript, unrelated to the mathematics in hand, and are skipped. | transcripts/136/batch-09.fr.tex:4 |
| 136 | 182 | others' typescript | The even pages (182, 184, …, 200) are versos carrying a typescript unrelated to these notes | transcripts/136/batch-10.fr.tex:4 |
| 136 | 184 | others' typescript | The even pages (182, 184, …, 200) are versos carrying a typescript unrelated to these notes | transcripts/136/batch-10.fr.tex:4 |
| 136 | 186 | gap only (no header mention) |  | transcripts/136/batch-10.fr.tex:1 |
| 136 | 188 | gap only (no header mention) |  | transcripts/136/batch-10.fr.tex:1 |
| 136 | 190 | gap only (no header mention) |  | transcripts/136/batch-10.fr.tex:1 |
| 136 | 192 | gap only (no header mention) |  | transcripts/136/batch-10.fr.tex:1 |
| 136 | 194 | gap only (no header mention) |  | transcripts/136/batch-10.fr.tex:1 |
| 136 | 196 | gap only (no header mention) |  | transcripts/136/batch-10.fr.tex:1 |
| 136 | 198 | gap only (no header mention) |  | transcripts/136/batch-10.fr.tex:1 |
| 136 | 200 | others' typescript | The even pages (182, 184, …, 200) are versos carrying a typescript unrelated to these notes | transcripts/136/batch-10.fr.tex:4 |
| 136 | 202 | others' typescript | Pages 202–212 (even) are typed proofs of an unrelated exposé (versos) | transcripts/136/batch-11.fr.tex:5 |
| 136 | 204 | others' typescript | Pages 202–212 (even) are typed proofs of an unrelated exposé (versos) | transcripts/136/batch-11.fr.tex:5 |
| 136 | 206 | others' typescript | Pages 202–212 (even) are typed proofs of an unrelated exposé (versos) | transcripts/136/batch-11.fr.tex:5 |
| 136 | 208 | others' typescript | Pages 202–212 (even) are typed proofs of an unrelated exposé (versos) | transcripts/136/batch-11.fr.tex:5 |
| 136 | 210 | others' typescript | Pages 202–212 (even) are typed proofs of an unrelated exposé (versos) | transcripts/136/batch-11.fr.tex:5 |
| 136 | 212 | others' typescript | Pages 202–212 (even) are typed proofs of an unrelated exposé (versos) | transcripts/136/batch-11.fr.tex:5 |
| 136 | 213 | blank | page 213 is blank, pages 215 and 217 are a third-party typescript | transcripts/136/batch-11.fr.tex:5 |
| 136 | 215 | blank | page 213 is blank, pages 215 and 217 are a third-party typescript | transcripts/136/batch-11.fr.tex:5 |
| 136 | 217 | blank | page 213 is blank, pages 215 and 217 are a third-party typescript | transcripts/136/batch-11.fr.tex:5 |
| 136 | 223 | others' typescript | Pages 223, 227, 229, 231, 233, 235, 237 and 239 are unrelated versos (a computer listing and typed pages of another text, with nothing in hi… | transcripts/136/batch-12.fr.tex:4 |
| 136 | 227 | others' typescript | Pages 223, 227, 229, 231, 233, 235, 237 and 239 are unrelated versos (a computer listing and typed pages of another text, with nothing in hi… | transcripts/136/batch-12.fr.tex:4 |
| 136 | 229 | others' typescript | Pages 223, 227, 229, 231, 233, 235, 237 and 239 are unrelated versos (a computer listing and typed pages of another text, with nothing in hi… | transcripts/136/batch-12.fr.tex:4 |
| 136 | 231 | others' typescript | Pages 223, 227, 229, 231, 233, 235, 237 and 239 are unrelated versos (a computer listing and typed pages of another text, with nothing in hi… | transcripts/136/batch-12.fr.tex:4 |
| 136 | 233 | others' typescript | Pages 223, 227, 229, 231, 233, 235, 237 and 239 are unrelated versos (a computer listing and typed pages of another text, with nothing in hi… | transcripts/136/batch-12.fr.tex:4 |
| 136 | 235 | others' typescript | Pages 223, 227, 229, 231, 233, 235, 237 and 239 are unrelated versos (a computer listing and typed pages of another text, with nothing in hi… | transcripts/136/batch-12.fr.tex:4 |
| 136 | 237 | others' typescript | Pages 223, 227, 229, 231, 233, 235, 237 and 239 are unrelated versos (a computer listing and typed pages of another text, with nothing in hi… | transcripts/136/batch-12.fr.tex:4 |
| 136 | 239 | others' typescript | Pages 223, 227, 229, 231, 233, 235, 237 and 239 are unrelated versos (a computer listing and typed pages of another text, with nothing in hi… | transcripts/136/batch-12.fr.tex:4 |
| 136 | 241 | others' typescript | Skipped: 241 (typescript page « - 182 - », not in his hand and not the mathematics in hand) | transcripts/136/batch-13.fr.tex:5 |
| 136 | 242 | blank | 242 (blank) | transcripts/136/batch-13.fr.tex:5 |
| 136 | 244 | administrative | 244 (third-party letter, not circulated under RIGHTS.md | transcripts/136/batch-13.fr.tex:5 |
| 136 | 254 | others' typescript | 254 (typed seminar notice) | transcripts/136/batch-13.fr.tex:8 |
| 136 | 257 | administrative | 257 (thesis-defence notice) | transcripts/136/batch-13.fr.tex:8 |
| 136 | 259 | others' typescript | 259 (typescript page « - 99 - IX », no hand of his on it). | transcripts/136/batch-13.fr.tex:8 |
| 136 | 261 | others' typescript | Pages 261, 263, 265, 267, 269, 271, 273, 275, 277, 279 are typescript versos unrelated to the notes and are skipped. | transcripts/136/batch-14.fr.tex:4 |
| 136 | 263 | others' typescript | Pages 261, 263, 265, 267, 269, 271, 273, 275, 277, 279 are typescript versos unrelated to the notes and are skipped. | transcripts/136/batch-14.fr.tex:4 |
| 136 | 265 | others' typescript | Pages 261, 263, 265, 267, 269, 271, 273, 275, 277, 279 are typescript versos unrelated to the notes and are skipped. | transcripts/136/batch-14.fr.tex:4 |
| 136 | 267 | others' typescript | Pages 261, 263, 265, 267, 269, 271, 273, 275, 277, 279 are typescript versos unrelated to the notes and are skipped. | transcripts/136/batch-14.fr.tex:4 |
| 136 | 269 | others' typescript | Pages 261, 263, 265, 267, 269, 271, 273, 275, 277, 279 are typescript versos unrelated to the notes and are skipped. | transcripts/136/batch-14.fr.tex:4 |
| 136 | 271 | others' typescript | Pages 261, 263, 265, 267, 269, 271, 273, 275, 277, 279 are typescript versos unrelated to the notes and are skipped. | transcripts/136/batch-14.fr.tex:4 |
| 136 | 273 | others' typescript | Pages 261, 263, 265, 267, 269, 271, 273, 275, 277, 279 are typescript versos unrelated to the notes and are skipped. | transcripts/136/batch-14.fr.tex:4 |
| 136 | 275 | others' typescript | Pages 261, 263, 265, 267, 269, 271, 273, 275, 277, 279 are typescript versos unrelated to the notes and are skipped. | transcripts/136/batch-14.fr.tex:4 |
| 136 | 277 | others' typescript | Pages 261, 263, 265, 267, 269, 271, 273, 275, 277, 279 are typescript versos unrelated to the notes and are skipped. | transcripts/136/batch-14.fr.tex:4 |
| 136 | 279 | others' typescript | Pages 261, 263, 265, 267, 269, 271, 273, 275, 277, 279 are typescript versos unrelated to the notes and are skipped. | transcripts/136/batch-14.fr.tex:4 |
| 136 | 281 | others' typescript | Skipped as unrelated versos: 281, 283, 285, 287, 289, 291, 293, 295, 297, 299 (typescript pages and exercise sheets with no writing of his o… | transcripts/136/batch-15.fr.tex:7 |
| 136 | 283 | others' typescript | Skipped as unrelated versos: 281, 283, 285, 287, 289, 291, 293, 295, 297, 299 (typescript pages and exercise sheets with no writing of his o… | transcripts/136/batch-15.fr.tex:7 |
| 136 | 285 | others' typescript | Skipped as unrelated versos: 281, 283, 285, 287, 289, 291, 293, 295, 297, 299 (typescript pages and exercise sheets with no writing of his o… | transcripts/136/batch-15.fr.tex:7 |
| 136 | 287 | others' typescript | Skipped as unrelated versos: 281, 283, 285, 287, 289, 291, 293, 295, 297, 299 (typescript pages and exercise sheets with no writing of his o… | transcripts/136/batch-15.fr.tex:7 |
| 136 | 289 | others' typescript | Skipped as unrelated versos: 281, 283, 285, 287, 289, 291, 293, 295, 297, 299 (typescript pages and exercise sheets with no writing of his o… | transcripts/136/batch-15.fr.tex:7 |
| 136 | 291 | others' typescript | Skipped as unrelated versos: 281, 283, 285, 287, 289, 291, 293, 295, 297, 299 (typescript pages and exercise sheets with no writing of his o… | transcripts/136/batch-15.fr.tex:7 |
| 136 | 293 | others' typescript | Skipped as unrelated versos: 281, 283, 285, 287, 289, 291, 293, 295, 297, 299 (typescript pages and exercise sheets with no writing of his o… | transcripts/136/batch-15.fr.tex:7 |
| 136 | 295 | others' typescript | Skipped as unrelated versos: 281, 283, 285, 287, 289, 291, 293, 295, 297, 299 (typescript pages and exercise sheets with no writing of his o… | transcripts/136/batch-15.fr.tex:7 |
| 136 | 297 | others' typescript | Skipped as unrelated versos: 281, 283, 285, 287, 289, 291, 293, 295, 297, 299 (typescript pages and exercise sheets with no writing of his o… | transcripts/136/batch-15.fr.tex:7 |
| 136 | 299 | others' typescript | Skipped as unrelated versos: 281, 283, 285, 287, 289, 291, 293, 295, 297, 299 (typescript pages and exercise sheets with no writing of his o… | transcripts/136/batch-15.fr.tex:7 |
| 136 | 300 | cover/wrapper | Page 300 is a cover in his hand naming the next run. | transcripts/136/batch-15.fr.tex:9 |
| 136 | 318 | cover/wrapper | Page 318 is a blue cover in his hand (« Gribouillis vrac », « Au Fil des Jours… »): no \page, its words become the section heading before pa… | transcripts/136/batch-16.fr.tex:4 |
| 136 | 335 | cover/wrapper | Page 335 carries only the word « Gribouillis » in his hand: treated as a cover sheet (no \page), the word becomes the section heading before… | transcripts/136/batch-17.fr.tex:4 |
| 136 | 343 | blank | Skipped: 343, 346, 353, 355 (blank leaves) | transcripts/136/batch-18.fr.tex:7 |
| 136 | 346 | blank | Skipped: 343, 346, 353, 355 (blank leaves) | transcripts/136/batch-18.fr.tex:7 |
| 136 | 348 | others' typescript | 348, 350, 352 (typescript by another hand, not transcribed — RIGHTS.md). | transcripts/136/batch-18.fr.tex:7 |
| 136 | 350 | others' typescript | 348, 350, 352 (typescript by another hand, not transcribed — RIGHTS.md). | transcripts/136/batch-18.fr.tex:7 |
| 136 | 352 | others' typescript | 348, 350, 352 (typescript by another hand, not transcribed — RIGHTS.md). | transcripts/136/batch-18.fr.tex:7 |
| 136 | 353 | blank | Skipped: 343, 346, 353, 355 (blank leaves) | transcripts/136/batch-18.fr.tex:7 |
| 136 | 355 | blank | Skipped: 343, 346, 353, 355 (blank leaves) | transcripts/136/batch-18.fr.tex:7 |
| 136 | 368 | blank | Page 368 is a blank music-ruled sheet (only a few strokes on the edge of an underlying leaf show) and is absent. | transcripts/136/batch-19.fr.tex:7 |
| 137 | 2 | others' typescript | Pages skipped: 2 and 4, leaves of an English typescript on minimal models and de Rham forms (« Appendix H (Hirsch Method) », typed page « H2… | transcripts/137/batch-01.fr.tex:11 |
| 137 | 4 | others' typescript | Pages skipped: 2 and 4, leaves of an English typescript on minimal models and de Rham forms (« Appendix H (Hirsch Method) », typed page « H2… | transcripts/137/batch-01.fr.tex:11 |
| 137 | 5 | blank | 5, a blank cream sheet showing only the show-through of page 4. | transcripts/137/batch-01.fr.tex:12 |
| 137 | 47 | blank | Pages skipped: 47, a blank tan sheet carrying only a stray pencil figure (a « 2 »?) at the top — nothing of the mathematics. | transcripts/137/batch-03.fr.tex:12 |
| 138 | 1 | administrative | Pages 1-2 (printed leaflet and order form of the review « Topologie Structurale ») carry no mathematics and are absent. | transcripts/138/batch-01.fr.tex:8 |
| 138 | 2 | administrative | Pages 1-2 (printed leaflet and order form of the review « Topologie Structurale ») carry no mathematics and are absent. | transcripts/138/batch-01.fr.tex:8 |
| 138 | 3 | cover/wrapper | Page 3 is a cover in his hand | transcripts/138/batch-01.fr.tex:9 |
| 138 | 23 | illegible | Page 23 carries only show-through from its neighbour and is skipped. | transcripts/138/batch-02.fr.tex:4 |
| 138 | 42 | others' typescript | Pages 42, 44, 47, 49, 51 and 55 are unrelated administrative or typed versos with nothing in his hand | transcripts/138/batch-03.fr.tex:8 |
| 138 | 44 | others' typescript | Pages 42, 44, 47, 49, 51 and 55 are unrelated administrative or typed versos with nothing in his hand | transcripts/138/batch-03.fr.tex:8 |
| 138 | 47 | others' typescript | Pages 42, 44, 47, 49, 51 and 55 are unrelated administrative or typed versos with nothing in his hand | transcripts/138/batch-03.fr.tex:8 |
| 138 | 49 | others' typescript | Pages 42, 44, 47, 49, 51 and 55 are unrelated administrative or typed versos with nothing in his hand | transcripts/138/batch-03.fr.tex:8 |
| 138 | 51 | others' typescript | Pages 42, 44, 47, 49, 51 and 55 are unrelated administrative or typed versos with nothing in his hand | transcripts/138/batch-03.fr.tex:8 |
| 138 | 55 | others' typescript | Pages 42, 44, 47, 49, 51 and 55 are unrelated administrative or typed versos with nothing in his hand | transcripts/138/batch-03.fr.tex:8 |
| 138 | 56 | cover/wrapper | Page 56 is a cover sheet bearing only his words « autom. des groupoïdes », used as the heading of pages 57-60 and given no \page. | transcripts/138/batch-03.fr.tex:10 |
| 138 | 64 | cover/wrapper | Pp. 64 and 69 are cover sheets carrying only a title in his hand | transcripts/138/batch-04.fr.tex:9 |
| 138 | 66 | others' typescript | Skipped: pp. 66 and 68 (typed USTL notices of thesis defences, June 1978, nothing in his hand). | transcripts/138/batch-04.fr.tex:8 |
| 138 | 68 | others' typescript | Skipped: pp. 66 and 68 (typed USTL notices of thesis defences, June 1978, nothing in his hand). | transcripts/138/batch-04.fr.tex:8 |
| 138 | 69 | cover/wrapper | Pp. 64 and 69 are cover sheets carrying only a title in his hand | transcripts/138/batch-04.fr.tex:9 |
| 138 | 75 | cover/wrapper | p. 75 likewise. | transcripts/138/batch-04.fr.tex:9 |
| 138 | 78 | blank | P. 78 is blank. | transcripts/138/batch-04.fr.tex:10 |
| 138 | 87 | blank | Pages 87 and 91 are blank and do not appear. | transcripts/138/batch-05.fr.tex:4 |
| 138 | 91 | blank | Pages 87 and 91 are blank and do not appear. | transcripts/138/batch-05.fr.tex:4 |
| 138 | 96 | blank | Page 96 is an otherwise blank sheet carrying three lines in his hand: they become the heading of the run that follows (pp. 97-100) and the p… | transcripts/138/batch-05.fr.tex:4 |
| 138 | 112 | cover/wrapper | Pages 112 and 120 are cover sheets inscribed in his hand | transcripts/138/batch-06.fr.tex:6 |
| 138 | 120 | cover/wrapper | Pages 112 and 120 are cover sheets inscribed in his hand | transcripts/138/batch-06.fr.tex:6 |
| 138 | 132 | others' typescript | Page 132 is an unrelated typed sheet with nothing in his hand | transcripts/138/batch-07.fr.tex:8 |
| 140-1 | 2 | skipped, reason not classifiable | Pages skipped: 2, 4, 6, 8, 10, 12. | transcripts/140-1/batch-01.fr.tex:18 |
| 140-1 | 4 | skipped, reason not classifiable | Pages skipped: 2, 4, 6, 8, 10, 12. | transcripts/140-1/batch-01.fr.tex:18 |
| 140-1 | 6 | skipped, reason not classifiable | Pages skipped: 2, 4, 6, 8, 10, 12. | transcripts/140-1/batch-01.fr.tex:18 |
| 140-1 | 8 | skipped, reason not classifiable | Pages skipped: 2, 4, 6, 8, 10, 12. | transcripts/140-1/batch-01.fr.tex:18 |
| 140-1 | 10 | skipped, reason not classifiable | Pages skipped: 2, 4, 6, 8, 10, 12. | transcripts/140-1/batch-01.fr.tex:18 |
| 140-1 | 12 | skipped, reason not classifiable | Pages skipped: 2, 4, 6, 8, 10, 12. | transcripts/140-1/batch-01.fr.tex:18 |
| 140-1 | 21 | blank | Pages skipped: 21 (blank sheet) | transcripts/140-1/batch-02.fr.tex:12 |
| 140-1 | 23 | others' typescript | 23, 25, 27 and 36 (typed leaves with nothing in his hand). | transcripts/140-1/batch-02.fr.tex:12 |
| 140-1 | 25 | others' typescript | 23, 25, 27 and 36 (typed leaves with nothing in his hand). | transcripts/140-1/batch-02.fr.tex:12 |
| 140-1 | 27 | others' typescript | 23, 25, 27 and 36 (typed leaves with nothing in his hand). | transcripts/140-1/batch-02.fr.tex:12 |
| 140-1 | 36 | others' typescript | 23, 25, 27 and 36 (typed leaves with nothing in his hand). | transcripts/140-1/batch-02.fr.tex:12 |
| 141 | 2 | others' typescript | Pages 2, 4 and 6 are typed administrative notices (USTL thesis-defence announcements dated « Montpellier, le 12 Novembre 1980 », checked on … | transcripts/141/batch-01.fr.tex:7 |
| 141 | 4 | others' typescript | Pages 2, 4 and 6 are typed administrative notices (USTL thesis-defence announcements dated « Montpellier, le 12 Novembre 1980 », checked on … | transcripts/141/batch-01.fr.tex:7 |
| 141 | 6 | others' typescript | Pages 2, 4 and 6 are typed administrative notices (USTL thesis-defence announcements dated « Montpellier, le 12 Novembre 1980 », checked on … | transcripts/141/batch-01.fr.tex:7 |
| 142 | 1 | cover/wrapper | batch page 1 = archivists' page 1), per the skill transcribe-grothendieck. | transcripts/142/batch-01.fr.tex:2 |
| 142 | 21 | cover/wrapper | Page 21 is a cover in his hand | transcripts/142/batch-02.fr.tex:4 |
| 142 | 22 | skipped, reason not classifiable | Page 22 carries only a pencilled page count and is skipped. | transcripts/142/batch-02.fr.tex:4 |
| 142 | 42 | blank | page 42 is a blank sheet carrying only a pencil tally and is skipped. | transcripts/142/batch-03.fr.tex:5 |
| 142 | 64 | blank | Page 64 is blank. | transcripts/142/batch-04.fr.tex:5 |
| 142 | 65 | cover/wrapper | Page 65 is a cover in his hand | transcripts/142/batch-04.fr.tex:5 |
| 142 | 104 | gap only (no header mention) |  | transcripts/142/batch-06.fr.tex:1 |
| 142 | 106 | gap only (no header mention) |  | transcripts/142/batch-06.fr.tex:1 |
| 142 | 108 | gap only (no header mention) |  | transcripts/142/batch-06.fr.tex:1 |
| 142 | 122 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 123 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 124 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 125 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 126 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 127 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 128 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 129 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 130 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 131 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 132 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 133 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 134 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 135 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 136 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 137 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 138 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 139 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 142 | 140 | gap only (no header mention) |  | transcripts/142/batch-07.fr.tex:1 |
| 143 | 33 | printed/published | Pages skipped: 33, a computer listing (columns of decimal numbers, upside down) carrying only two short numerical sums in another context («… | transcripts/143/batch-02.fr.tex:13 |
| 144 | 1 | cover/wrapper | Page 1 is a cover sheet in his hand (its words are the section heading) | transcripts/144/batch-01.fr.tex:4 |
| 144 | 11 | blank | page 11 is blank | transcripts/144/batch-01.fr.tex:5 |
| 144 | 28 | cover/wrapper | Page 28 is a cover sheet in his hand (its words become the section heading) | transcripts/144/batch-02.fr.tex:5 |
| 144 | 40 | blank | page 40 is blank. | transcripts/144/batch-02.fr.tex:5 |
| 144 | 43 | administrative | Skipped: 43, 45, 47 (administrative forms and letters, no mathematics) | transcripts/144/batch-03.fr.tex:4 |
| 144 | 45 | administrative | Skipped: 43, 45, 47 (administrative forms and letters, no mathematics) | transcripts/144/batch-03.fr.tex:4 |
| 144 | 47 | administrative | Skipped: 43, 45, 47 (administrative forms and letters, no mathematics) | transcripts/144/batch-03.fr.tex:4 |
| 144 | 48 | cover/wrapper | 48 (a cover in his hand, « 2-cartes cellulaires », used as the section heading). | transcripts/144/batch-03.fr.tex:4 |
| 144 | 101 | blank | Skipped: 101 (blank) | transcripts/144/batch-06.fr.tex:10 |
| 144 | 103 | duplicate | 103, 113, 115 (a student's copy on the icosahedron, dated 16 June 1978, on the backs of his sheets) | transcripts/144/batch-06.fr.tex:10 |
| 144 | 105 | administrative | 105, 107, 109, 111 (USTL administrative notes, 105 with only show-through) | transcripts/144/batch-06.fr.tex:10 |
| 144 | 107 | administrative | 105, 107, 109, 111 (USTL administrative notes, 105 with only show-through) | transcripts/144/batch-06.fr.tex:10 |
| 144 | 109 | administrative | 105, 107, 109, 111 (USTL administrative notes, 105 with only show-through) | transcripts/144/batch-06.fr.tex:10 |
| 144 | 111 | administrative | 105, 107, 109, 111 (USTL administrative notes, 105 with only show-through) | transcripts/144/batch-06.fr.tex:10 |
| 144 | 113 | duplicate | 103, 113, 115 (a student's copy on the icosahedron, dated 16 June 1978, on the backs of his sheets) | transcripts/144/batch-06.fr.tex:10 |
| 144 | 115 | duplicate | 103, 113, 115 (a student's copy on the icosahedron, dated 16 June 1978, on the backs of his sheets) | transcripts/144/batch-06.fr.tex:10 |
| 144 | 116 | cover/wrapper | 116 (a cover: its inscription becomes the section heading). | transcripts/144/batch-06.fr.tex:10 |
| 144 | 124 | blank | Skipped (no mathematics): 124, 127, 132 (blank sheets) | transcripts/144/batch-07.fr.tex:7 |
| 144 | 126 | administrative | 126 (an envelope) | transcripts/144/batch-07.fr.tex:7 |
| 144 | 127 | blank | Skipped (no mathematics): 124, 127, 132 (blank sheets) | transcripts/144/batch-07.fr.tex:7 |
| 144 | 131 | others' typescript | 131, 134, 136, 138 (typed administrative notices, nothing in his hand). | transcripts/144/batch-07.fr.tex:7 |
| 144 | 132 | blank | Skipped (no mathematics): 124, 127, 132 (blank sheets) | transcripts/144/batch-07.fr.tex:7 |
| 144 | 134 | others' typescript | 131, 134, 136, 138 (typed administrative notices, nothing in his hand). | transcripts/144/batch-07.fr.tex:7 |
| 144 | 136 | others' typescript | 131, 134, 136, 138 (typed administrative notices, nothing in his hand). | transcripts/144/batch-07.fr.tex:7 |
| 144 | 138 | others' typescript | 131, 134, 136, 138 (typed administrative notices, nothing in his hand). | transcripts/144/batch-07.fr.tex:7 |
| 144 | 140 | gap only (no header mention) |  | transcripts/144/batch-07.fr.tex:1 |
| 144 | 150 | administrative | Skipped as unrelated versos (administrative documents, computer listings): 150, 151, 152, 154, 156, 158, 160. | transcripts/144/batch-08.fr.tex:4 |
| 144 | 151 | administrative | Skipped as unrelated versos (administrative documents, computer listings): 150, 151, 152, 154, 156, 158, 160. | transcripts/144/batch-08.fr.tex:4 |
| 144 | 152 | administrative | Skipped as unrelated versos (administrative documents, computer listings): 150, 151, 152, 154, 156, 158, 160. | transcripts/144/batch-08.fr.tex:4 |
| 144 | 154 | administrative | Skipped as unrelated versos (administrative documents, computer listings): 150, 151, 152, 154, 156, 158, 160. | transcripts/144/batch-08.fr.tex:4 |
| 144 | 156 | administrative | Skipped as unrelated versos (administrative documents, computer listings): 150, 151, 152, 154, 156, 158, 160. | transcripts/144/batch-08.fr.tex:4 |
| 144 | 158 | administrative | Skipped as unrelated versos (administrative documents, computer listings): 150, 151, 152, 154, 156, 158, 160. | transcripts/144/batch-08.fr.tex:4 |
| 144 | 160 | administrative | Skipped as unrelated versos (administrative documents, computer listings): 150, 151, 152, 154, 156, 158, 160. | transcripts/144/batch-08.fr.tex:4 |
| 144 | 162 | blank | Skipped, no hand on them: 162, 164, 166, 168, 170, 175, 177, 180 (typed university notices on the versos) and 171, 178 (blank separator shee… | transcripts/144/batch-09.fr.tex:4 |
| 144 | 164 | blank | Skipped, no hand on them: 162, 164, 166, 168, 170, 175, 177, 180 (typed university notices on the versos) and 171, 178 (blank separator shee… | transcripts/144/batch-09.fr.tex:4 |
| 144 | 166 | blank | Skipped, no hand on them: 162, 164, 166, 168, 170, 175, 177, 180 (typed university notices on the versos) and 171, 178 (blank separator shee… | transcripts/144/batch-09.fr.tex:4 |
| 144 | 168 | blank | Skipped, no hand on them: 162, 164, 166, 168, 170, 175, 177, 180 (typed university notices on the versos) and 171, 178 (blank separator shee… | transcripts/144/batch-09.fr.tex:4 |
| 144 | 170 | blank | Skipped, no hand on them: 162, 164, 166, 168, 170, 175, 177, 180 (typed university notices on the versos) and 171, 178 (blank separator shee… | transcripts/144/batch-09.fr.tex:4 |
| 144 | 171 | blank | Skipped, no hand on them: 162, 164, 166, 168, 170, 175, 177, 180 (typed university notices on the versos) and 171, 178 (blank separator shee… | transcripts/144/batch-09.fr.tex:4 |
| 144 | 175 | blank | Skipped, no hand on them: 162, 164, 166, 168, 170, 175, 177, 180 (typed university notices on the versos) and 171, 178 (blank separator shee… | transcripts/144/batch-09.fr.tex:4 |
| 144 | 177 | blank | Skipped, no hand on them: 162, 164, 166, 168, 170, 175, 177, 180 (typed university notices on the versos) and 171, 178 (blank separator shee… | transcripts/144/batch-09.fr.tex:4 |
| 144 | 178 | blank | Skipped, no hand on them: 162, 164, 166, 168, 170, 175, 177, 180 (typed university notices on the versos) and 171, 178 (blank separator shee… | transcripts/144/batch-09.fr.tex:4 |
| 144 | 180 | blank | Skipped, no hand on them: 162, 164, 166, 168, 170, 175, 177, 180 (typed university notices on the versos) and 171, 178 (blank separator shee… | transcripts/144/batch-09.fr.tex:4 |
| 144 | 183 | others' typescript | Page 183 of the batch is a typed examination paper (DEUG A, juin 1981) with nothing in his hand: skipped. | transcripts/144/batch-10.fr.tex:4 |
| 146 | 1 | gap only (no header mention) |  | transcripts/146/batch-01.fr.tex:1 |
| 146 | 18 | gap only (no header mention) |  | transcripts/146/batch-01.fr.tex:1 |
| 146 | 20 | gap only (no header mention) |  | transcripts/146/batch-01.fr.tex:1 |
| 146 | 22 | blank | The others (22, 24, 25, 27, 29, 31, 33, 34, 36, 38, 40) are blank versos or unrelated paper (USTL administrative letters and tables, budget … | transcripts/146/batch-02.fr.tex:8 |
| 146 | 24 | blank | The others (22, 24, 25, 27, 29, 31, 33, 34, 36, 38, 40) are blank versos or unrelated paper (USTL administrative letters and tables, budget … | transcripts/146/batch-02.fr.tex:8 |
| 146 | 25 | blank | The others (22, 24, 25, 27, 29, 31, 33, 34, 36, 38, 40) are blank versos or unrelated paper (USTL administrative letters and tables, budget … | transcripts/146/batch-02.fr.tex:8 |
| 146 | 27 | blank | The others (22, 24, 25, 27, 29, 31, 33, 34, 36, 38, 40) are blank versos or unrelated paper (USTL administrative letters and tables, budget … | transcripts/146/batch-02.fr.tex:8 |
| 146 | 29 | blank | The others (22, 24, 25, 27, 29, 31, 33, 34, 36, 38, 40) are blank versos or unrelated paper (USTL administrative letters and tables, budget … | transcripts/146/batch-02.fr.tex:8 |
| 146 | 31 | blank | The others (22, 24, 25, 27, 29, 31, 33, 34, 36, 38, 40) are blank versos or unrelated paper (USTL administrative letters and tables, budget … | transcripts/146/batch-02.fr.tex:8 |
| 146 | 33 | blank | The others (22, 24, 25, 27, 29, 31, 33, 34, 36, 38, 40) are blank versos or unrelated paper (USTL administrative letters and tables, budget … | transcripts/146/batch-02.fr.tex:8 |
| 146 | 34 | blank | The others (22, 24, 25, 27, 29, 31, 33, 34, 36, 38, 40) are blank versos or unrelated paper (USTL administrative letters and tables, budget … | transcripts/146/batch-02.fr.tex:8 |
| 146 | 36 | blank | The others (22, 24, 25, 27, 29, 31, 33, 34, 36, 38, 40) are blank versos or unrelated paper (USTL administrative letters and tables, budget … | transcripts/146/batch-02.fr.tex:8 |
| 146 | 38 | blank | The others (22, 24, 25, 27, 29, 31, 33, 34, 36, 38, 40) are blank versos or unrelated paper (USTL administrative letters and tables, budget … | transcripts/146/batch-02.fr.tex:8 |
| 146 | 40 | blank | The others (22, 24, 25, 27, 29, 31, 33, 34, 36, 38, 40) are blank versos or unrelated paper (USTL administrative letters and tables, budget … | transcripts/146/batch-02.fr.tex:8 |
| 146 | 56 | blank | Skipped: 56 (blank) | transcripts/146/batch-03.fr.tex:8 |
| 146 | 58 | others' typescript | 58 and 60 (USTL thesis-defence notices of 1979, typed, nothing in his hand). | transcripts/146/batch-03.fr.tex:8 |
| 146 | 60 | others' typescript | 58 and 60 (USTL thesis-defence notices of 1979, typed, nothing in his hand). | transcripts/146/batch-03.fr.tex:8 |
| 146 | 68 | others' typescript | Skipped: 68 (unrelated typed letter | transcripts/146/batch-04.fr.tex:4 |
| 146 | 69 | blank | 69, 75, 79 (blank or bleed-through only) | transcripts/146/batch-04.fr.tex:4 |
| 146 | 71 | others' typescript | 71 (typed exam subject, nothing in his hand). | transcripts/146/batch-04.fr.tex:4 |
| 146 | 75 | blank | 69, 75, 79 (blank or bleed-through only) | transcripts/146/batch-04.fr.tex:4 |
| 146 | 79 | blank | 69, 75, 79 (blank or bleed-through only) | transcripts/146/batch-04.fr.tex:4 |
| 146 | 87 | blank | page 87 is blank and absent. | transcripts/146/batch-05.fr.tex:8 |
| 146 | 101 | blank | Pages 101 and 104 are blank and are not transcribed. | transcripts/146/batch-06.fr.tex:4 |
| 146 | 104 | blank | Pages 101 and 104 are blank and are not transcribed. | transcripts/146/batch-06.fr.tex:4 |
| 146 | 125 | cover/wrapper | Page 125 is a cover sheet in his hand (« Graphes MD ») | transcripts/146/batch-07.fr.tex:5 |
| 146 | 131 | others' typescript | Pages 131 and 133 are unrelated typed versos (USTL thesis-defence notices, November 1981) carrying nothing in his hand, and are skipped. | transcripts/146/batch-07.fr.tex:4 |
| 146 | 133 | others' typescript | Pages 131 and 133 are unrelated typed versos (USTL thesis-defence notices, November 1981) carrying nothing in his hand, and are skipped. | transcripts/146/batch-07.fr.tex:4 |
| 147 | 1 | cover/wrapper | Page 1 is a pencil cover sheet (« Pages 1-90 + table des matières »), not in Grothendieck's hand as far as can be judged | transcripts/147/batch-01.fr.tex:4 |
| 148 | 5 | others' typescript | Pages skipped: 5, 7, 9, 11, 13, 15 — the versos of his leaves 4-14, typed USTL « avis de soutenance » circulars (dated 14, 18 and 20 October… | transcripts/148/batch-01.fr.tex:13 |
| 148 | 7 | others' typescript | Pages skipped: 5, 7, 9, 11, 13, 15 — the versos of his leaves 4-14, typed USTL « avis de soutenance » circulars (dated 14, 18 and 20 October… | transcripts/148/batch-01.fr.tex:13 |
| 148 | 9 | others' typescript | Pages skipped: 5, 7, 9, 11, 13, 15 — the versos of his leaves 4-14, typed USTL « avis de soutenance » circulars (dated 14, 18 and 20 October… | transcripts/148/batch-01.fr.tex:13 |
| 148 | 11 | others' typescript | Pages skipped: 5, 7, 9, 11, 13, 15 — the versos of his leaves 4-14, typed USTL « avis de soutenance » circulars (dated 14, 18 and 20 October… | transcripts/148/batch-01.fr.tex:13 |
| 148 | 13 | others' typescript | Pages skipped: 5, 7, 9, 11, 13, 15 — the versos of his leaves 4-14, typed USTL « avis de soutenance » circulars (dated 14, 18 and 20 October… | transcripts/148/batch-01.fr.tex:13 |
| 148 | 15 | others' typescript | Pages skipped: 5, 7, 9, 11, 13, 15 — the versos of his leaves 4-14, typed USTL « avis de soutenance » circulars (dated 14, 18 and 20 October… | transcripts/148/batch-01.fr.tex:13 |
| 148 | 16 | others' typescript | Pages skipped: 5, 7, 9, 11, 13, 15 — the versos of his leaves 4-14, typed USTL « avis de soutenance » circulars (dated 14, 18 and 20 October… | transcripts/148/batch-01.fr.tex:13 |
| 148 | 21 | printed/published | Pages skipped: 21 and 29 — computer listings (job banners, June 1982 | transcripts/148/batch-02.fr.tex:15 |
| 148 | 28 | blank | Pages 28 and 39 are covers: listing sheets otherwise blank, inscribed in his hand « M_{0,5} » (28) and « Catalogue des opérations élémentair… | transcripts/148/batch-02.fr.tex:19 |
| 148 | 29 | printed/published | Pages skipped: 21 and 29 — computer listings (job banners, June 1982 | transcripts/148/batch-02.fr.tex:15 |
| 148 | 39 | blank | Pages 28 and 39 are covers: listing sheets otherwise blank, inscribed in his hand « M_{0,5} » (28) and « Catalogue des opérations élémentair… | transcripts/148/batch-02.fr.tex:19 |
| 148 | 65 | blank | Pages skipped: 65 only, as a page: it is a cover (tan listing paper, blank but for three pencil lines of his at top right, « Découpage de ca… | transcripts/148/batch-04.fr.tex:14 |
| 149 | 1 | unrelated | Page 1 carries only a pencilled label ("Pages 1-67") and no mathematics | transcripts/149/batch-01.fr.tex:4 |
| 150 | 5 | blank | Pages skipped: 5 and 10, blank sheets | transcripts/150/batch-01.fr.tex:11 |
| 150 | 8 | others' typescript | 8, an unrelated typed administrative verso with nothing of his. | transcripts/150/batch-01.fr.tex:11 |
| 150 | 10 | blank | Pages skipped: 5 and 10, blank sheets | transcripts/150/batch-01.fr.tex:11 |
| 151 | 3 | administrative | Pages 3, 5 and 7 are three copies of one administrative letter (Inspection académique de Vaucluse, Avignon, 6 December 1990), scanned upside… | transcripts/151/batch-01.fr.tex:6 |
| 151 | 5 | administrative | Pages 3, 5 and 7 are three copies of one administrative letter (Inspection académique de Vaucluse, Avignon, 6 December 1990), scanned upside… | transcripts/151/batch-01.fr.tex:6 |
| 151 | 7 | administrative | Pages 3, 5 and 7 are three copies of one administrative letter (Inspection académique de Vaucluse, Avignon, 6 December 1990), scanned upside… | transcripts/151/batch-01.fr.tex:6 |
| 151 | 9 | blank | Pages 9 and 15 are blank — absent. | transcripts/151/batch-01.fr.tex:6 |
| 151 | 15 | blank | Pages 9 and 15 are blank — absent. | transcripts/151/batch-01.fr.tex:6 |
| 151 | 25 | blank | Page 25 is blank — absent. | transcripts/151/batch-02.fr.tex:6 |
| 152 | 5 | printed/published | Pages 5, 8 and 11 are listings of the same run (IBM JCL, the job named PREDONTA) with nothing of his on them, and are skipped | transcripts/152/batch-01.fr.tex:12 |
| 152 | 8 | printed/published | Pages 5, 8 and 11 are listings of the same run (IBM JCL, the job named PREDONTA) with nothing of his on them, and are skipped | transcripts/152/batch-01.fr.tex:12 |
| 152 | 11 | printed/published | Pages 5, 8 and 11 are listings of the same run (IBM JCL, the job named PREDONTA) with nothing of his on them, and are skipped | transcripts/152/batch-01.fr.tex:12 |
| 153 | 4 | printed/published | Pages 4, 6, 8 and 10 are listings of the same run with nothing of his on them, and are skipped — the gaps in the page numbers are the record… | transcripts/153/batch-01.fr.tex:11 |
| 153 | 6 | printed/published | Pages 4, 6, 8 and 10 are listings of the same run with nothing of his on them, and are skipped — the gaps in the page numbers are the record… | transcripts/153/batch-01.fr.tex:11 |
| 153 | 8 | printed/published | Pages 4, 6, 8 and 10 are listings of the same run with nothing of his on them, and are skipped — the gaps in the page numbers are the record… | transcripts/153/batch-01.fr.tex:11 |
| 153 | 10 | printed/published | Pages 4, 6, 8 and 10 are listings of the same run with nothing of his on them, and are skipped — the gaps in the page numbers are the record… | transcripts/153/batch-01.fr.tex:11 |
| 154 | 5 | printed/published | Pages skipped: 5 and 7, computer listings (on p. 5 a job banner of 16 August 1982, placed on the facsimile by Michel Hua, 2026-10-20, #77 | transcripts/154/batch-01.fr.tex:24 |
| 154 | 7 | printed/published | Pages skipped: 5 and 7, computer listings (on p. 5 a job banner of 16 August 1982, placed on the facsimile by Michel Hua, 2026-10-20, #77 | transcripts/154/batch-01.fr.tex:24 |
| 154 | 10 | printed/published | Pages skipped: 5 and 7, computer listings (on p. 5 a job banner of 16 August 1982, placed on the facsimile by Michel Hua, 2026-10-20, #77 | transcripts/154/batch-01.fr.tex:24 |
| 154 | 98 | blank | Pages skipped: 98, a blank cream separator sheet. | transcripts/154/batch-05.fr.tex:25 |
| 155 | 2 | gap only (no header mention) |  | transcripts/155/batch-01.fr.tex:1 |
| 155 | 4 | gap only (no header mention) |  | transcripts/155/batch-01.fr.tex:1 |
| 155 | 6 | gap only (no header mention) |  | transcripts/155/batch-01.fr.tex:1 |
| 155 | 8 | gap only (no header mention) |  | transcripts/155/batch-01.fr.tex:1 |
| 155 | 10 | gap only (no header mention) |  | transcripts/155/batch-01.fr.tex:1 |
| 156-8 | 1 | cover/wrapper | Page 1 is the folder's cover, inscribed in his hand | transcripts/156-8/batch-01.fr.tex:5 |
| 156-8 | 4 | others' typescript | Pages 4 and 6 are unrelated typed versos (typescript pages of another text, scanned upside down) and are not transcribed. | transcripts/156-8/batch-01.fr.tex:4 |
| 156-8 | 6 | others' typescript | Pages 4 and 6 are unrelated typed versos (typescript pages of another text, scanned upside down) and are not transcribed. | transcripts/156-8/batch-01.fr.tex:4 |
| 156-9 | 109 | others' typescript | Pages 109, 111 and 113 are typed versos (notes of another text) carrying no mathematics of this run | transcripts/156-9/batch-06.fr.tex:4 |
| 156-9 | 111 | others' typescript | Pages 109, 111 and 113 are typed versos (notes of another text) carrying no mathematics of this run | transcripts/156-9/batch-06.fr.tex:4 |
| 156-9 | 113 | others' typescript | Pages 109, 111 and 113 are typed versos (notes of another text) carrying no mathematics of this run | transcripts/156-9/batch-06.fr.tex:4 |
| 156-9 | 128 | blank | Page 128 is a blank coloured sheet and is not transcribed. | transcripts/156-9/batch-07.fr.tex:4 |
| 158 | 5 | skipped, reason not classifiable | Pages 5 and 16 carry nothing but the archivists' pencilled number — absent. | transcripts/158/batch-01.fr.tex:10 |
| 158 | 16 | skipped, reason not classifiable | Pages 5 and 16 carry nothing but the archivists' pencilled number — absent. | transcripts/158/batch-01.fr.tex:10 |
| 158 | 34 | blank | Pages 34, 38 and 40 are unrelated versos (a blank Inspection Académique letterhead, then twice a circular from the same office) and are abse… | transcripts/158/batch-02.fr.tex:11 |
| 158 | 38 | blank | Pages 34, 38 and 40 are unrelated versos (a blank Inspection Académique letterhead, then twice a circular from the same office) and are abse… | transcripts/158/batch-02.fr.tex:11 |
| 158 | 40 | blank | Pages 34, 38 and 40 are unrelated versos (a blank Inspection Académique letterhead, then twice a circular from the same office) and are abse… | transcripts/158/batch-02.fr.tex:11 |
| 158 | 42 | administrative | Page 42 is an unrelated administrative verso, scanned upside down — absent. | transcripts/158/batch-03.fr.tex:8 |
| 158 | 43 | blank | Pages 43, 54 and 59 are blank and carry nothing but the archivists' number. | transcripts/158/batch-03.fr.tex:7 |
| 158 | 54 | blank | Pages 43, 54 and 59 are blank and carry nothing but the archivists' number. | transcripts/158/batch-03.fr.tex:7 |
| 158 | 59 | blank | Pages 43, 54 and 59 are blank and carry nothing but the archivists' number. | transcripts/158/batch-03.fr.tex:7 |
| 158 | 63 | administrative | Pages 63, 64 and 65 are one administrative circular, page 80 a printed seminar announcement: no mathematics — absent. | transcripts/158/batch-04.fr.tex:7 |
| 158 | 64 | administrative | Pages 63, 64 and 65 are one administrative circular, page 80 a printed seminar announcement: no mathematics — absent. | transcripts/158/batch-04.fr.tex:7 |
| 158 | 65 | administrative | Pages 63, 64 and 65 are one administrative circular, page 80 a printed seminar announcement: no mathematics — absent. | transcripts/158/batch-04.fr.tex:7 |
| 158 | 80 | administrative | Pages 63, 64 and 65 are one administrative circular, page 80 a printed seminar announcement: no mathematics — absent. | transcripts/158/batch-04.fr.tex:7 |
| 158 | 82 | unrelated | Pages 82, 84 and 85 carry no mathematics — absent. | transcripts/158/batch-05.fr.tex:7 |
| 158 | 84 | unrelated | Pages 82, 84 and 85 carry no mathematics — absent. | transcripts/158/batch-05.fr.tex:7 |
| 158 | 85 | unrelated | Pages 82, 84 and 85 carry no mathematics — absent. | transcripts/158/batch-05.fr.tex:7 |
| 159 | 13 | skipped, reason not classifiable | Page 13 carries nothing but the archivists' number — absent. | transcripts/159/batch-01.fr.tex:6 |
| 159 | 23 | blank | Page 23 is a blank leaf and is absent | transcripts/159/batch-02.fr.tex:9 |
| 160 | 17 | blank | Page 17 is blank and carries no mathematics — absent. | transcripts/160/batch-01.fr.tex:6 |
| 161-1 | 2 | blank | Pages 2, 8 and 14 are blank versos — absent. | transcripts/161-1/batch-01.fr.tex:4 |
| 161-1 | 8 | blank | Pages 2, 8 and 14 are blank versos — absent. | transcripts/161-1/batch-01.fr.tex:4 |
| 161-1 | 14 | blank | Pages 2, 8 and 14 are blank versos — absent. | transcripts/161-1/batch-01.fr.tex:4 |
| 161-1 | 16 | verso (unspecified) | Page 16 is a reused verso, pencil notes upside down on an entirely different subject (p-adic periods) — absent, as it should be. | transcripts/161-1/batch-01.fr.tex:5 |
| 161-1 | 18 | blank | Page 18 is a blank verso carrying three scribbled arrows with no labels — absent. | transcripts/161-1/batch-01.fr.tex:6 |
| 161-2 | 1 | cover/wrapper | Page 1 is the folder's cover, whose tab supplies the opening heading | transcripts/161-2/batch-01.fr.tex:4 |
| 161-2 | 2 | blank | pages 2 and 16 are blank — all three absent. | transcripts/161-2/batch-01.fr.tex:4 |
| 161-2 | 16 | blank | pages 2 and 16 are blank — all three absent. | transcripts/161-2/batch-01.fr.tex:4 |
| 161-2 | 25 | blank | Pages 25, 32 and 35 are blank — absent. | transcripts/161-2/batch-02.fr.tex:4 |
| 161-2 | 32 | blank | Pages 25, 32 and 35 are blank — absent. | transcripts/161-2/batch-02.fr.tex:4 |
| 161-2 | 35 | blank | Pages 25, 32 and 35 are blank — absent. | transcripts/161-2/batch-02.fr.tex:4 |
| 161-2 | 53 | blank | Page 53 is blank and page 57 carries a single scrawl with no mathematics — both absent. | transcripts/161-2/batch-03.fr.tex:4 |
| 161-2 | 57 | blank | Page 53 is blank and page 57 carries a single scrawl with no mathematics — both absent. | transcripts/161-2/batch-03.fr.tex:4 |
| 161-2 | 79 | blank | Page 79 is blank and absent | transcripts/161-2/batch-04.fr.tex:4 |
| 161-2 | 88 | blank | Pages 88 and 96 are blank and absent. | transcripts/161-2/batch-05.fr.tex:4 |
| 161-2 | 96 | blank | Pages 88 and 96 are blank and absent. | transcripts/161-2/batch-05.fr.tex:4 |
| 161-2 | 107 | blank | Pages 107 and 110 are blank and absent. | transcripts/161-2/batch-06.fr.tex:4 |
| 161-2 | 110 | blank | Pages 107 and 110 are blank and absent. | transcripts/161-2/batch-06.fr.tex:4 |
| 161-3 | 2 | blank | Pages 2, 13 and 16 are blank — absent. | transcripts/161-3/batch-01.fr.tex:4 |
| 161-3 | 13 | blank | Pages 2, 13 and 16 are blank — absent. | transcripts/161-3/batch-01.fr.tex:4 |
| 161-3 | 16 | blank | Pages 2, 13 and 16 are blank — absent. | transcripts/161-3/batch-01.fr.tex:4 |
| 161-3 | 22 | blank | Pages 22, 27, 29 and 33 are blank — absent. | transcripts/161-3/batch-02.fr.tex:4 |
| 161-3 | 27 | blank | Pages 22, 27, 29 and 33 are blank — absent. | transcripts/161-3/batch-02.fr.tex:4 |
| 161-3 | 29 | blank | Pages 22, 27, 29 and 33 are blank — absent. | transcripts/161-3/batch-02.fr.tex:4 |
| 161-3 | 33 | blank | Pages 22, 27, 29 and 33 are blank — absent. | transcripts/161-3/batch-02.fr.tex:4 |
| 161-4 | 1 | gap only (no header mention) |  | transcripts/161-4/batch-01.fr.tex:1 |
| 161-4 | 13 | blank | 13, 18 Blank: absent. | transcripts/161-4/batch-01.fr.tex:33 |
| 161-4 | 18 | blank | 13, 18 Blank: absent. | transcripts/161-4/batch-01.fr.tex:33 |
| 161-5 | 1 | printed/published | For the modernised reading: the printed footnote 1 (page 3) says that the idea of replacing p-adic Lie algebras by the corresponding algebra… | transcripts/161-5/batch-01.fr.tex:25 |
| 161-5 | 2 | printed/published | pages 2-8 and 10-14 carry nothing in any hand and are absent. | transcripts/161-5/batch-01.fr.tex:22 |
| 161-5 | 3 | printed/published | pages 2-8 and 10-14 carry nothing in any hand and are absent. | transcripts/161-5/batch-01.fr.tex:22 |
| 161-5 | 4 | printed/published | pages 2-8 and 10-14 carry nothing in any hand and are absent. | transcripts/161-5/batch-01.fr.tex:22 |
| 161-5 | 5 | printed/published | pages 2-8 and 10-14 carry nothing in any hand and are absent. | transcripts/161-5/batch-01.fr.tex:22 |
| 161-5 | 6 | printed/published | pages 2-8 and 10-14 carry nothing in any hand and are absent. | transcripts/161-5/batch-01.fr.tex:22 |
| 161-5 | 7 | printed/published | pages 2-8 and 10-14 carry nothing in any hand and are absent. | transcripts/161-5/batch-01.fr.tex:22 |
| 161-5 | 8 | printed/published | pages 2-8 and 10-14 carry nothing in any hand and are absent. | transcripts/161-5/batch-01.fr.tex:22 |
| 161-5 | 10 | printed/published | pages 2-8 and 10-14 carry nothing in any hand and are absent. | transcripts/161-5/batch-01.fr.tex:22 |
| 161-5 | 11 | printed/published | pages 2-8 and 10-14 carry nothing in any hand and are absent. | transcripts/161-5/batch-01.fr.tex:22 |
| 161-5 | 12 | printed/published | pages 2-8 and 10-14 carry nothing in any hand and are absent. | transcripts/161-5/batch-01.fr.tex:22 |
| 161-5 | 13 | printed/published | pages 2-8 and 10-14 carry nothing in any hand and are absent. | transcripts/161-5/batch-01.fr.tex:22 |
| 161-5 | 14 | printed/published | pages 2-8 and 10-14 carry nothing in any hand and are absent. | transcripts/161-5/batch-01.fr.tex:22 |
| 161-5 | 17 | gap only (no header mention) |  | transcripts/161-5/batch-01.fr.tex:1 |
| 161-5 | 18 | gap only (no header mention) |  | transcripts/161-5/batch-01.fr.tex:1 |
| 161-5 | 21 | cover/wrapper | The batch file carries no cover sheet: PDF page N is archivists' page N+20, as the pencilled numbers bottom-left ("21" ... "28") confirm. | transcripts/161-5/batch-02.fr.tex:4 |
| 161-6 | 1 | cover/wrapper | chemise p. 1 re-read on the facsimile (259 ppi scan) — the name stays \uncertain, the note now gives Laborde as an equally possible reading | transcripts/161-6/batch-01.fr.tex:8 |
| 161-6 | 2 | blank | 2, 11, 20  Blank: absent. | transcripts/161-6/batch-01.fr.tex:23 |
| 161-6 | 11 | blank | 2, 11, 20  Blank: absent. | transcripts/161-6/batch-01.fr.tex:23 |
| 161-6 | 20 | blank | 2, 11, 20  Blank: absent. | transcripts/161-6/batch-01.fr.tex:23 |
| 161-6 | 23 | blank | 23     Blank: absent. | transcripts/161-6/batch-02.fr.tex:28 |
| 161-6 | 31 | blank | 31     Blank: absent. | transcripts/161-6/batch-02.fr.tex:41 |
| 162-5 | 1 | others' typescript | 19     A typed list, « Publications of Daniel Quillen », items 1-11 (1966 to "to appear"), with nothing in his hand: absent, like any page t… | transcripts/162-5/batch-01.fr.tex:23 |
| 162-5 | 18 | blank | 18, 20 Blank separator sheets: absent. | transcripts/162-5/batch-01.fr.tex:22 |
| 162-5 | 19 | others' typescript | 19     A typed list, « Publications of Daniel Quillen », items 1-11 (1966 to "to appear"), with nothing in his hand: absent, like any page t… | transcripts/162-5/batch-01.fr.tex:23 |
| 162-5 | 20 | blank | 18, 20 Blank separator sheets: absent. | transcripts/162-5/batch-01.fr.tex:22 |
| 162-5 | 31 | blank | 31     Blank separator sheet: absent. | transcripts/162-5/batch-02.fr.tex:28 |
| 162-5 | 42 | blank | 42, 49, 56 Blank. | transcripts/162-5/batch-03.fr.tex:21 |
| 162-5 | 49 | blank | 42, 49, 56 Blank. | transcripts/162-5/batch-03.fr.tex:21 |
| 162-5 | 50 | gap only (no header mention) |  | transcripts/162-5/batch-03.fr.tex:1 |
| 162-5 | 51 | gap only (no header mention) |  | transcripts/162-5/batch-03.fr.tex:1 |
| 162-5 | 52 | gap only (no header mention) |  | transcripts/162-5/batch-03.fr.tex:1 |
| 162-5 | 53 | gap only (no header mention) |  | transcripts/162-5/batch-03.fr.tex:1 |
| 162-5 | 54 | gap only (no header mention) |  | transcripts/162-5/batch-03.fr.tex:1 |
| 162-5 | 55 | gap only (no header mention) |  | transcripts/162-5/batch-03.fr.tex:1 |
| 162-5 | 56 | blank | 42, 49, 56 Blank. | transcripts/162-5/batch-03.fr.tex:21 |
| 162-5 | 57 | duplicate | 57, 59, 60 carry nothing of the kind and are absent. | transcripts/162-5/batch-03.fr.tex:29 |
| 162-5 | 59 | duplicate | 57, 59, 60 carry nothing of the kind and are absent. | transcripts/162-5/batch-03.fr.tex:29 |
| 162-5 | 60 | duplicate | 57, 59, 60 carry nothing of the kind and are absent. | transcripts/162-5/batch-03.fr.tex:29 |
| 162-5 | 62 | duplicate | Pages absent: 62, 63, 64, 66, 67, 68 — duplication only. | transcripts/162-5/batch-04.fr.tex:37 |
| 162-5 | 63 | duplicate | Pages absent: 62, 63, 64, 66, 67, 68 — duplication only. | transcripts/162-5/batch-04.fr.tex:37 |
| 162-5 | 64 | duplicate | Pages absent: 62, 63, 64, 66, 67, 68 — duplication only. | transcripts/162-5/batch-04.fr.tex:37 |
| 162-5 | 66 | duplicate | Pages absent: 62, 63, 64, 66, 67, 68 — duplication only. | transcripts/162-5/batch-04.fr.tex:37 |
| 162-5 | 67 | duplicate | Pages absent: 62, 63, 64, 66, 67, 68 — duplication only. | transcripts/162-5/batch-04.fr.tex:37 |
| 162-5 | 68 | duplicate | Pages absent: 62, 63, 64, 66, 67, 68 — duplication only. | transcripts/162-5/batch-04.fr.tex:37 |

