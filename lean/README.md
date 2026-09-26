# The readings, proved

Lean 4 proofs, against mathlib, of statements the modernised readings make
(issue [#26](https://github.com/Commutator-IO/grothendieck-project/issues/26)).
A proof here says that what a reading states **holds together**, not that it is
what the page says: a perfectly formalised statement can be a perfectly
formalised misreading.

```bash
cd lean && lake exe cache get && lake build   # fails on any warning, so on any sorry
```

| Folder | Reading | Lean | What the proof found |
|---|---|---|---|
| 42 | Lemme 2 (1) and (2), pp. 4–5 of `transcripts/42/42.modern.tex` | `Grothendieck/Folder42.lean` | Both hold as stated. Part (2) needs no Noetherian hypothesis; part (1) uses it only to make the kernel of `A → A_𝔭` finitely generated, the kernel being — as the reading's footnote corrects the page — what *some* element outside `𝔭` kills. |
