# The readings, proved

Lean 4 proofs, against mathlib, of statements the modernised readings make
(issue [#26](https://github.com/Commutator-IO/grothendieck-project/issues/26)).
A proof here says that what a reading states **holds together**, not that it is
what the page says: a perfectly formalised statement can be a perfectly
formalised misreading.

```bash
cd lean && lake exe cache get && lake build   # fails on any warning, so on any sorry
```

Eighteen folders (issue #26: tier 1, and the five rows of tier 2). Each statement, its written-out proof and
what the verification found are in the appendix
[`docs/lean/article.pdf`](../docs/lean/article.pdf), served at
<https://grothendieck.commutator.io/article/grothendieck-lean.pdf>, and on the
site's Findings page. `./axioms.sh`, run after `lake build`, lists the axioms
of every theorem and fails on any beyond Lean's three standard ones.

| Folder | File | Scope | Found |
|---|---|---|---|
| 42 | `Folder42.lean` | Lemme 2 | (2) needs no Noetherian hypothesis |
| 158 | `Folder158.lean` | Proposition 1 | the reading's gloss was false (Rees kernel not a point); corrected |
| 153 | `Folder153.lean` | Lemme | `k₀ ⊂ K₀` not needed |
| 152 | `Folder152.lean` | dictionary, partial | the page's head line contradicts its table |
| 88 | `Folder88.lean` | order 2ν, (6), partial | most hypotheses unused |
| 113 | `Folder113.lean` | Karoubi, Morita (additive), partial | smallness, abelianness unused |
| 104 | `Folder104.lean` | categories of models, partial | nothing wrong |
| 125 | `Folder125.lean` | étages, III-18, partial | prose slip `q < r − m` → `q ⩽ r − m` |
| 161-1 | `Folder161_1.lean` | condition (1), idempotency | nothing wrong |
| 22 | `Folder22.lean` | 3.3–3.5, partial | « par exemple noethérien » is equivalent, not an example |
| 41 | `Folder41.lean` | Proposition 1 | finiteness needed only for (iii bis) ⇒ (ii) |
| 21 | `Folder21.lean` | 2.15, 2.16, partial | nothing false |
| 39 | `Folder39.lean` | adic preparation, partial | nothing wrong |
| 19 | `Folder19.lean` | Théorème 1.12, Gabriel–Popescu | **the « only if » of 1.12 b) is false on the page**; condition C is not Beck's |
| 161-2 | `Folder161_2.lean` | monadicity, descent, Gabriel–Ulmer, Ind(Σ), partial | descent needs no topos |
| 16 | `Folder16.lean` | sl₂ against (6.7), algebra only | confirms the reading's correction of p. 16 |
| 106 | `Folder106.lean` | cofibration categories, Brown, W₀⁻¹C ≅ W⁻¹C | several axioms and hypotheses unused |
| 114 | `Folder114.lean` | Proposition 4, minimal localiser, partial | the reading dropped « satisfying Loc 4) »; without it W ⊆ W₀ fails |
