# Readings of folder 153 to check on the facsimile (2026-11-27)

Folder 153, pp. 3, 7 and 9 (batch 01): the questions that the machine revision pass of 27 November 2026 for #145 left to a reader.
That pass read the pages again on the facsimile and was not checked by a reader; its record is `docs/review/revision-145/153.md`.
Where the record offers a rival that the pass did not see on the page (the word that opens the lemma; « ens. » on p. 7), the alternative is left open.
Each bullet is one place where the transcription now has one reading and the facsimile decides between it and another; nothing here has been checked by a person.
Same format as `folder-149-readings-2026-11-11.md`; `scripts/review-queue.mjs` reads every file named
`folder-<cote>-readings-<date>.md`, one item per open box, with the id `reading-153-<batch>-<line>`.

`- [ ] <cote> p<pages> batch-<NN>:<line> | reading | <where> | <our reading> | <alternative reading>`

`<line>` is the line of `transcripts/153/batch-<NN>.fr.tex` on 27 November 2026 (a letter after the number tells apart two questions on one line).
Tick a box when its answer is applied; the transcription then gains a `% Revised` line naming the issue that carried the answer.

## 1. P. 3, the lemma

- [ ] 153 p3 batch-01:252 | reading | the underlined word that opens the lemma, before « si M est un k_0-module libre » | « Lemme » | another word (say which)
- [ ] 153 p3 batch-01:253 | reading | lemma, third line, « Ω_M ⊂ K_0[T] ⊗ … » | « K_0[T] ⊗_{K_0} M_{K_0} » | « K_0[T] ⊗_{k_0} M »
- [ ] 153 p3 batch-01:285 | reading | « En effet, dans K_0[X,Y] = K_0[X] ⊗ K_0[Y] » : the index of the tensor sign (inked over) | « K_0 » | « k_0 »

## 2. P. 7

- [ ] 153 p7 batch-01:431 | reading | Ex 1, « et en tant que (A,A), A … , il a une structure de composition » | « ens. » | another word (say which)
- [ ] 153 p7 batch-01:482 | reading | last sentence, « On est content … Ω → Ω_{Ω_0} … injectif ! » | « quand … est injectif » | « que … soit injectif »

## 3. P. 9

- [ ] 153 p9 batch-01:494 | reading | « Le cas le plus intéressant est celui … (Z ⊂ Q » | « du couple » | « des corps »
