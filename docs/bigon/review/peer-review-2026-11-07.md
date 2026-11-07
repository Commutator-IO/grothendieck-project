# Pre-submission report: "A bigon-free dichotomy for pseudoline arrangements, after a note of Grothendieck"

Working draft, 7 November 2026. Simulated referee report requested by the author (Michel Hua) on his own manuscript `docs/bigon/article.tex`, before submission to Hexagon. Local processing only; the manuscript text was not sent to any external service (only bibliographic metadata of the cited works was looked up). Intake validated with the peer-review skill's `validate_review_intake.py` (status READY_FOR_LOCAL_REVIEW; capacity: author-requested reader; no conflicts).

Competence limits: this is an automated, simulated report. It re-derives every proof step and checks the computations it could run, but it is not an independent expert referee report and does not replace one.

Materials used: the manuscript; the Lean source `lean/Grothendieck/Folder80Maps2.lean`; `computations/bigon/` (README, `results.txt`); the transcription of folder 80 (`transcripts/80/batch-01.fr.tex`, `batch-02.fr.tex`, `batch-03.fr.tex`) for the pages cited; the problems paper `docs/problems/article.tex`; the published text of Kelly–Rottenberg (PJM 40, 1972) and the arXiv text of Bokowski–Pokora.

## Summary of the submission

The note proves that a pseudoline arrangement in which every pseudoline carries at least three vertices either is four pseudolines in general position (II_4) or contains II_5, II'_{3,2} or the complete quadrangle III_6. Grothendieck states this, boxed, on pages 20 and 24 of folder 80. The note also proves a strengthened form of the ordering lemma of page 28, shows that for n ≥ 6 the near-pencils are the only arrangements avoiding the three configurations, refutes the auxiliary theorem of page 24 as written with six real lines, and reports an exhaustive enumeration (n ≤ 9, simple n = 10) and a Lean formalisation for generalised maps of Euler characteristic 1.

## Overall assessment

The mathematics is correct. Every proof was re-derived step by step (details below) and no error was found in the main line of argument. The result is elementary, which the note says plainly. The issues are one factual error in the computational section, one hypothesis in the cited theorem that was stated more weakly than the source, two short gaps in otherwise correct proofs, one unexplained step in Section 5, and some figure defects. All were fixed in the manuscript.

## Verification of the claims

| Claim | Check | Result |
|---|---|---|
| Intro: a pseudoline carries exactly one vertex only in a pencil | If ℓ has one vertex v, every other pseudoline meets ℓ at v | correct |
| Def. of II'_{3,2}, III_6 | III_6: 4 triple points and 3 simple diagonal points (two diagonal points coincide only if two sides through a common P_i meet twice) | correct |
| Theorem 1 (Kelly–Rottenberg Th. 3.6) | Read in the published paper: Th. 3.6 gives λ ≥ 3n/7 simple points, for every arrangement not all through one point | correct citation; statement was weaker than the source, see M1 |
| Lemma 2 | Re-derived: simple crossing p = a∩b, k ≥ 2 further vertices on a, the case analysis on c∩b, d∩b | correct; one gap, see M2 |
| Lemma 3 | Two non-opposite vertices share a side; opposite pairs form a perfect matching on the six vertices, so three vertices always include a non-opposite pair; the II_5 and II'_{3,2} cases | correct |
| At most three diagonals | Two diagonals through one pair meet twice | correct |
| Theorem 4 | The three cases (no / one / two diagonals); check that x, y, z, w, δ_1, δ_2 pass through exactly the six pairs | correct |
| Sharpness paragraph | Vertex counts of II_4, II_5, II'_{3,2}, III_6; deleting a side of III_6 leaves two triple points | correct; wording "sharp" replaced, see m1 |
| Corollary 5 | Immediate from Theorem 4 | correct |
| Theorem 6 | Monotonicity of vertex sets under adding pseudolines; a point lies on at most three sides of III_6, only the P_i on three; at most one diagonal when no III_6 | correct; the "at most three sides" step was compressed, see M3 |
| Corollary 7 | Both directions re-derived, including the case split on (s, t) with s + t ≥ 5 | correct |
| Small cases n = 4, 5 | Hand classification; matches `results.txt` (avoid mode: 2 classes at n = 4 and 5) | correct |
| Example 8 | All 20 determinants recomputed (exact integer arithmetic): exactly the three stated triples vanish; no two vertices cover the six lines; every 5-subset contains a concurrent triple; 9 vertices, 3 of them triple | correct |
| "IV_7 contains a II'_{3,2}" | Computed on a real IV_7: x, y and the three diagonals have exactly one concurrent triple | correct, but unexplained in the text, see M4 |
| "Theorem of p. 24 becomes true once II' excluded" | Re-derived: its hypothesis implies bigon-free; the proof of Theorem 4 gives Q plus diagonals; 0 or 1 diagonal violate the hypothesis, 3 give IV_7 which contains II' | correct, but the argument was missing, see M4 |
| Enumeration counts | `results.txt`: 1, 2, 4, 17, 143, 4890, 461053 and simple 4382, 312356; bigon-free per n: 0, 1, 2, 15, 140, 4887, 461049 | error, see M5 |
| "at n = 9 all but four are bigon-free" | 461053 − 461049 = 4 (I_9, I_{6,2}, I_{5,3}, I_{4,4}) | correct |
| Melchior inequality | 2E ≥ 3F, χ = 1, E = Σν(v) give Σ(3 − ν(v)) ≥ 3, hence some ν(v) = 2 | correct |
| Description of the Lean model | Compared with `GMap` and `PseudolineMap`: `two` says at least two pseudolines per vertex | wording error, see M6 |
| Attributions | p. 20 (statement with the three configurations drawn), p. 22 (« cas cruciaux »), p. 24 (boxed statement, I'_{3,2}, the theorem with III_6 / IV_7), p. 27 (notice of 13 May 1981), p. 28 (Lemme and sketch), p. 60 (definition by maps) all confirmed in the transcription | correct; inventory date phrased more exactly, see m2 |

## Major comments (all fixed)

**M1. Theorem 1 understated the source.**
Location: Theorem 1 and the first sentence of the proof of Lemma 2.
Observation: The theorem read "an arrangement that is not a near-pencil has a simple crossing". Kelly–Rottenberg's Theorem 3.6 gives at least 3n/7 simple crossings for every arrangement, near-pencils included. A near-pencil has n − 1 simple crossings, so the exclusion is unnecessary, and a reader may think it is needed.
Why it matters: A reader may conclude that the Sylvester–Gallai property fails for near-pencils.
Action taken: Theorem 1 now states the bound of Th. 3.6 and its consequence. The sentence proving that a bigon-free arrangement is not a near-pencil is removed from Lemma 2, where it is no longer needed. Bokowski–Pokora Th. 1.3 is Melchior's equality, not a Sylvester–Gallai statement, so it is now cited for that and moved next to the Melchior paragraph.

**M2. Lemma 2, the reduction to one point r.**
Location: third paragraph of the proof of Lemma 2.
Observation: The hypothesis compares pseudolines through different q_i, q_j. The text then concluded that all pseudolines through the q_i meet b at one point, which also requires comparing two pseudolines through the same q_i.
Action taken: One sentence added. Compare both with a pseudoline through some q_j, j ≠ i, which exists because k ≥ 2 and every vertex lies on at least two pseudolines.

**M3. Theorem 6, the count on the sides of III_6.**
Location: second paragraph of the proof of Theorem 6.
Observation: "The vertices of a III_6 lie on at most three of its sides" is true, but the argument needs it for every point of ℓ, and it needs the fact that only the P_i lie on three sides.
Action taken: Rewritten. Any three sides include two with a common P_i, which meet only there, so only the P_i lie on three sides. Two P_i share a side, so two points lie on at most five sides.

**M4. Section 5: the corrected form of the p. 24 theorem was asserted without argument.**
Location: last paragraph of Section 5.
Observation: The claims "IV_7 contains a II'_{3,2}" and "the theorem becomes true … this is what Theorem 4 gives" were stated without proof. Theorem 4 gives "contains", while the p. 24 theorem concludes "is".
Action taken: An explicit II'_{3,2} inside IV_7 is given: two sides and the three diagonals. The note adds that the diagonals are not concurrent because the Fano matroid is not orientable. The derivation is added: the hypothesis implies bigon-free, the proof of Theorem 4 gives Q plus diagonals, zero or one diagonal violates the hypothesis, and three give IV_7. The arrangement is therefore exactly a III_6.

**M5. Enumeration: wrong total.**
Location: Section 6, Enumeration.
Observation: "All 461049 bigon-free arrangements with n ≤ 9" uses the count for n = 9 alone. The total over 4 ≤ n ≤ 9 in `results.txt` is 1 + 2 + 15 + 140 + 4887 + 461049 = 466094.
Action taken: Corrected to "466094 … (461049 of them with n = 9)". The same wording occurs in `computations/bigon/README.md`, which is outside the scope of this pass and was not edited.

**M6. Formalisation: "every vertex lies on two pseudolines".**
Observation: The Lean field `two` says that every vertex lies on at least two pseudolines. "On two" would describe simple arrangements only.
Action taken: Changed to "at least two".

## Minor comments (all fixed unless stated)

- m1. "The four alternatives are sharp" is vague. Now: "None of the four alternatives can be omitted", followed by the existing argument.
- m2. The archival inventory dates the folder « [à partir de 1981] ». "Dates it from 1981" is now "from 1981 onwards".
- m3. In the definition of II'_{3,2}, "the pseudoline joining p to d∩e is absent" assumes a joining pseudoline exists. That is false for pseudolines in general. Now: "none of the five passes through both p and d∩e". The caption of Figure 1 was changed to match.
- m4. Figures (rendered at 110 dpi and checked at 250 to 300 dpi):
  - Figure 1. Labels P_1, P_2, P_3, q collided with lines. The II_5 drawing had crossings 1 mm apart, which looked like near-concurrency; it is redrawn as a pentagram. The II'_{3,2} panel sat higher than the others because of its subscript; the baselines are now aligned.
  - Figure 2. The pseudolines c and d were not labelled, and the source had an empty stray node. Labels q_i, r overlapped lines.
  - Figure 3. Labels collided with lines. It is replaced by a four-panel figure covering Lemma 3 (ℓ through no vertex or one vertex) and the three cases of Theorem 4.
  - Figure 4. The P and Q labels sat on lines. The five thin pseudolines are now labelled a to e, as in the proof.
  - Figure 5. The B and C labels overlapped lines. All six lines are now labelled.
  - Every figure was checked against the text: coordinates were recomputed, and incidences such as P_1 to P_4 on the right lines, r on all c_i, and the lines of Example 8 through A, B, C were verified numerically.
- m5. New Figure 6 shows the three involutions of a generalised map near an edge, for readers unfamiliar with G-maps.
- m6. An overfull line from the Lean theorem name in `\texttt` was fixed with `\allowbreak`.

## Points the author may still want to consider (not changed)

- The note says the statement may be known to specialists. A short search of the two surveys cited is reported. A sentence on what else was searched, or a question to an expert, would make the novelty claim easier to assess.
- The enumeration and the Lean proof are described but not available to referees except through the repository. Hexagon reviewers may want a pinned commit or tag for `computations/bigon` and the Lean file.
- The Felsner–Goodman chapter is cited without page numbers (no chapter DOI was found; see the citation report).

## Confidential comments to the editor

None. This is a self-review requested by the author; there is no editor channel.

## Process notes

- The skill's `lint_review.py` reports REVISION_REQUIRED only because this report does not use its fixed "comments to authors / confidential comments to editor" headings. It is a self-review with no editor, so the headings were not added.
- After the fixes, the prose had a light humanizer pass: the em dash in the header comment was removed, one sentence in §5 and the sentence on the enumeration were made plain and exact (456667 of the 461049 bigon-free classes at n = 9 contain a II'_{3,2}; the other 4382 are the simple ones), and no mathematics was changed.
- Final build: `tectonic -X compile article.tex`, 7 pages. No errors, no undefined references, no overfull boxes. Two underfull lines remain in the AI statement paragraph; they were there before.
