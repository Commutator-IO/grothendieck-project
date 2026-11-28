# Readings of folder 53 to check on the facsimile (2026-11-28)

Folder 53, pp. 9 (batch 01), 21 and 30 (batch 02): the questions that the machine revision pass of 28 November 2026 for #145 left to a reader.
That pass read the pages again on the facsimile and was not checked by a reader; its record is `docs/review/revision-145/53.md`.
Each bullet is one place where the transcription now has one reading and the facsimile decides between it and another; nothing here has been checked by a person.
Same format as `folder-149-readings-2026-11-11.md`; `scripts/review-queue.mjs` reads every file named
`folder-<cote>-readings-<date>.md`, one item per open box, with the id `reading-53-<batch>-<line>`.

`- [ ] <cote> p<pages> batch-<NN>:<line> | reading | <where> | <our reading> | <alternative reading> | P<n>`

`<line>` is the line of `transcripts/53/batch-<NN>.fr.tex` on 28 November 2026 (a letter after the number tells apart two questions on one line).
Tick a box when its answer is applied; the transcription then gains a `% Revised` line naming the issue that carried the answer.

## 1. P. 9, Rectificatif sur le critère d'irréductibilité géométrique

- [ ] 53 p9 batch-01:475 | reading | b), the interline word before « géom. régulier » | « voire » (flagged) | « univ. » (the earlier reading) | P3
- [ ] 53 p9 batch-01:482 | reading | Dém., the words written under X'_i and attached after « contenant f'(Z') » | unread | « (qui est irréd.) » | P3
- [ ] 53 p9 batch-01:485 | reading | Dém., the bracket after « p(X'_i) = X » | « [platitude … p + p fermé] » (flagged) | « [p ouvert + p fermé] » (the earlier reading) | P2

## 2. P. 21, Rectification

- [ ] 53 p21 batch-02:90 | reading | end of the Rectification, « alors G est un objet … » | « groupe » (flagged) | « gr.-pr. » (the earlier reading) | P1
- [ ] 53 p21 batch-02:128 | reading | « la structure … » before D → D ⊠ D | « supplémentaire » (flagged) | « co-algébrique » (the earlier reading) | P3

## 3. P. 30, last line of the Dém.

- [ ] 53 p30 batch-02:494 | reading | the last line, after « donc » | « l'anneau affine de End_k(M) et a fortiori celui de GL(n) s'envoie sur A » (flagged) | « … et [les] fonctions coordonnées de GL(n) s'envoient sur A » (the earlier reading) | P2
