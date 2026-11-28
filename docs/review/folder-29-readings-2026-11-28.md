# Readings of folder 29 to check on the facsimile (2026-11-28)

Folder 29, pp. 190, 191, 197 (batch 10) and 214 (batch 11): the questions that the machine revision pass of 28 November 2026 for #145 left to a reader.
That pass read the pages again on the facsimile and was not checked by a reader; its record is `docs/review/revision-145/29.md` (fourth sitting; its pages 171, 192 and 193 leave no question).
Each bullet is one place where the transcription now has one reading and the facsimile decides between it and another; nothing here has been checked by a person.
Same format as `folder-149-readings-2026-11-11.md`; `scripts/review-queue.mjs` reads every file named
`folder-<cote>-readings-<date>.md`, one item per open box, with the id `reading-29-<batch>-<line>`.

`- [ ] <cote> p<pages> batch-<NN>:<line> | reading | <where> | <our reading> | <alternative reading> | P<n>`

`<line>` is the line of `transcripts/29/batch-<NN>.fr.tex` on 28 November 2026 (a letter after the number tells apart two questions on one line).
Tick a box when its answer is applied; the transcription then gains a `% Revised` line naming the issue that carried the answer.

## 1. P. 190, axiom R2 and Prop. 1

- [ ] 29 p190 batch-10:447 | reading | R2, the word written over the struck « sous-objets », before « directs X′ de X » | « sommandes » (flagged) | « sous-objets », written again | P3
- [ ] 29 p190 batch-10:468 | reading | Prop. 1, the circled insertion under « Alors ce sont », tied to the mark after « sur R_S′ » | « (moins fine que la canon. » (flagged) | « (plus fine que la canon. » | P1

## 2. P. 191, the remark on R3 and the Corollaire

- [ ] 29 p191 batch-10:517 | reading | « R3 signifie que la topologie est … fine que la canonique » : the overwritten word before « fine » | « moins » (flagged, the word the mathematics wants) | « plus » | P2
- [ ] 29 p191 batch-10:524 | reading | Corollaire, the word in quotation marks after the R_S′ that has no tilde | « sera » (flagged) : R_S′ is the subcategory of locally constant finite objects of its topos | « sur » (first pass) : a stack in toposes over that subcategory | P1

## 3. P. 197, Prop. 6 and its second corollary

- [ ] 29 p197 batch-10:731 | reading | the bracket after Prop. 6, its first words | « En effet, P′, α étant donnés, on a une équivalence » (flagged) | « Si (P′, α) sont deux termes, on a une équivalence » (first pass) | P2
- [ ] 29 p197 batch-10:743 | reading | second Cor., the note written lengthwise in the left margin, tied to « ses opérations sur Z′, » : the bracketed word after « loc. » | « P′ constant par morceaux loc. (ét.) sur S » (the bracket flagged) | « loc. (cst.) sur S » | P1

## 4. P. 214, the induction and the last statement

- [ ] 29 p214 batch-11:622 | reading | third line under the square, the degree of X′ → Y′ | « n », a letter gone over in ink, followed by a short struck word (flagged) | « n − 1 » added over a struck « n » (first pass) | P2
- [ ] 29 p214 batch-11:637 | reading | Explicitation, « qu'un f morphisme » : the state of the f | struck | only retraced, not struck | P4
- [ ] 29 p214 batch-11:653 | reading | the underlined heading of the last paragraph | « Corollaire » | « Conclusion » (first pass, and the name the finding and the Lean section used) | P3
