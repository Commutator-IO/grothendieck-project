# Peer review (working draft): docs/problem-three/article.tex, 8 November 2026

Local self-review of the author's own manuscript, done at the author's request. Intake validated with the skill's `validate_review_intake.py` (status READY_FOR_LOCAL_REVIEW, local only, no external service received manuscript text). This is a working draft for Michel Hua, who remains accountable for the text. The Kassis et al. citation proposed by the skill was not added.

## Scope

A mathematics article (category theory). No data, statistics or reporting guideline applies, so the review is about correctness, attribution, exposition and claim-evidence alignment. Limits: no specialist in 2-categorical algebra checked the arguments, and Adámek–Rosický's book could not be opened.

## Map of the claims

| ID | Claim | Evidence in the text |
|---|---|---|
| C1 | basic ⇒ (G), every D (Thm 3.2) | Lemma 3.1 and a transfinite induction over the steps of (H) |
| C2 | basic ⇔ (G) + algebraic (Thm 4.2) | Lemma 4.1 (closure), a pushout and a transfinite construction of an isomorphism |
| C3 | small D: basic ⇔ (G), base fixed (Thm 5.1) | two proofs: via C2, and directly |
| C4 | topoi: basic ⇔ (G) (Thm 6.3) | Lemma 6.2 (closure is a topos) and C1, C2 |
| C5 | two statements of the course on topoi are false (Prop 6.1) | explicit examples in Set × Set |
| C6 | Set: (G) in exactly two steps; Set not algebraic (Cor 7.2, Thm 7.5) | Props 7.1, 7.3, 7.4; Lean for 7.1–7.3 |
| C7 | algebraic ⇒ bounded steps; AR 6.38 gives unbounded steps and a second counterexample (Prop 7.7, Cor 7.8) | Prop 7.4; AR Example 6.38 as described on MathOverflow |

Each central claim has a proof in the text. C6 is partly machine-checked; C7 rests on a cited example that we did not read in the source.

## Major comments

**M1. Hypothesis (H) for topoi was used silently.** *Location:* §6 and Thm 6.3. *Observation:* Thm 6.3 has no "(H)" in its statement, but its proof uses the free constructions, including 2-pushouts and 2-colimits of chains, which are limits of topoi read the other way. *Why it matters:* without them the reduction theorem does not apply. *Action taken:* §6 now says that these constructions are pullbacks and limits of chains of topoi, used from standard topos theory without proof. "What is not done" lists this.

**M2. The example of Adámek and Rosický is cited second-hand.** *Location:* §7.3, Cor 7.8. *Observation:* the book was not opened. The example is known to us through Rosický's MathOverflow answer and Campion's exposition, which also notes that the book's example has a slightly different aim. *Why it matters:* Cor 7.8 and the answer to the question on bounds depend on it. *Action taken:* the text credits Rosický's answer and Campion's exposition, and "What is not done" says that the book was not accessible. *Remaining for the author:* read AR Example 6.38 in a library copy before submission.

**M3. Speculation in the open questions.** *Location:* §8, after Question 8.1. *Observation:* the earlier draft said that "finite limits may add objects that are not presentable", which nothing in the paper supports. *Action taken:* replaced by the precise reason that Prop 7.4 does not apply: its proof uses sketches for colimits only.

## Minor comments

- m1. *Kelly page reference.* The Buffalo article cited "§5.7, p. 100" for the remark on Cat₀ and {2}. In the TAC reprint the remark is at the end of §5.9 (between the running heads p. 101 and p. 103). The new article cites "end of §5.9". The Buffalo article's citation should be corrected when Appendix B is removed.
- m2. *Codensity versus density.* Remark 2.5 first compared (G) with density (left adequate), but for limits the right comparison is codensity (right adequate). Corrected: codensity gives (G) for limits in one step, and {2} ⊂ Set satisfies (G) without being codense.
- m3. *Three-element argument (Cor 7.2).* The phrase "say inside a product" was unclear. Rewritten to say that a limit of copies of 2 is a subset of a product closed under the coordinatewise ternary operation.
- m4. *"Every topos is algebraic"* was only a citation of the lecture. A short argument was added (envelope of Ob C, arrows and relations, then the subtopos of flat J-continuous diagrams).
- m5. *Enlarging the sketch (Prop 7.4).* The step was phrased obscurely. It now says why the closure D₀ contains the given objects: each is a small colimit of objects of K(A).
- m6. *Paré's theorem* is cited for the monadicity of the power-set functor. The paper could not be opened (AMS returns 403). Only its bibliographic data were checked (Crossref, zbMATH). Since Prop 7.1 has a complete proof, the citation only gives credit.

## Strengths

The reduction (Thm 4.2) turns the question into one about algebraicity alone. The negative results come with proofs, partly in Lean, and the text separates what is in print (Kelly §3.5, Thm 5.35, ch. 6; Gabriel–Ulmer; AR 6.38) from what is new.

## Not checked

The 2-categorical coherence in Thm 4.2 step (2) is argued at the level of universal properties, not written out. A specialist should look at it.
