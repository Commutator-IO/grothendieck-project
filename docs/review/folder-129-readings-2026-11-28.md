# An argument of folder 129 to check (2026-11-28)

Folder 129, p. 95 (batch 05): the NB « Ext²_ℤ(G, M) = 0 si 2 inv., pour tt G fini loc. libre » (finding 129-ext2-vanishing-p-odd, issue 247, section 2).
On 28 November 2026 a machine pass argued that the NB holds as read, over any base on which 2 is invertible; the argument is written in the finding (`ours`, `settle`) and was not checked by a person.
`scripts/review-queue.mjs` reads every file named `folder-<cote>-readings-<date>.md`; the type « argument » puts the question to mathematicians.

`- [ ] <cote> p<pages> batch-<NN>:<line> | argument | <the step> | <what the edition uses> | <what would replace it> | P<n>`

## 1. The partial resolution

- [ ] 129 p95 batch-05:588 | argument | the step that writes Ext²_T(G_T, W(M)) as H² of a finite complex D ⊗ M commuting with base change: it needs a functorial partial resolution L₃ → L₂ → L₁ → L₀ → G, exact at L₁ and at L₂, with terms finite sums of ℤ[G^j]. SGA 7 I, VII 3.5 (read 2026-11-28) gives only L₂ → L₁ → L₀ with H₁ = 0 and H₀ = G, and Remark 3.5.4 says it gives information on Ext¹ only; its correcteur's note says L. Breen built a full resolution | SGA 7 VII 3.5 as cited (insufficient: no exactness at L₂) | Breen's functorial resolution (to locate and check: L. Breen, « Extensions du groupe additif », Publ. Math. IHÉS 48, 1978, presumed) or MacLane's cubical construction for G of odd order | P0
