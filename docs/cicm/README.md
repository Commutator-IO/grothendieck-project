# Formalising a mathematician's working notes

The paper prepared for CICM, the Conference on Intelligent Computer
Mathematics (Springer LNCS/LNAI). It is the complement of the jTEI article
([`docs/study/`](../study/README.md)): that one covers the transcription, its
encoding and the checking of the readings; this one covers the formalisation
of the statements in Lean (`lean/`), with the appendix
([`docs/lean/`](../lean/article.tex)) as its long form.

- `article.tex` — the paper, in `llncs` (tectonic fetches the class and
  `splncs04.bst` from CTAN; nothing is vendored); `references.bib` its
  bibliography, every entry checked on 21 October 2026 (DOIs on Crossref,
  arXiv identifiers on the arXiv API, two items on zbMATH Open, URLs by
  request).
- `fig-pipeline.tex` — the pipeline from page to theorem, drawn by hand,
  because it states decisions and not data.
- `figures.mjs` — draws `fig-themes.tex`, the theorems per part of the Lean
  appendix, from the Lean files **as committed at HEAD** (not the working
  tree) and the `\part`s of `docs/lean/article.tex`.
- `article.pdf` — built and committed; the deploy copies it to
  `public/article/grothendieck-cicm.pdf` (`npm run article-tei`), linked from
  the Method page, `public/llms.txt` and the repository README.

```bash
node docs/cicm/figures.mjs && (cd docs/cicm && tectonic -X compile article.tex)
```

## Venue and limit

CICM 2027 is announced for 19–23 July 2027 in Erlangen; its call for papers
was not yet online on 21 October 2026 (the 2027 page still showed the 2026
call). The 2026 call allowed regular papers and project and survey papers of
**up to 15 pages plus bibliography** in LNCS style, submitted on EasyChair;
the 2026 deadlines were in April. This draft is 12 pages, the body ending on
page 11, references included, so there are about four pages to spare.
Check the 2027 call when it appears (limit, category, deadlines, whether the
review is double-blind: if it is, an anonymous version is needed).

## What remains to check

- Every figure is read from the repository at commit time (1,985 theorems,
  67 files, 38,325 lines, 463 findings, 67 proof cards and their verdicts,
  the triage of #54, the review figures of 21 October, 41 pull requests).
  They move: rerun `figures.mjs` and recount before submission.
- Folder 146, column n = 5: in progress and uncommitted when this was
  written; the paper says so. Update Section 5 and the conjectures section
  if it lands.
- The Mathlib section reports the record of the pull requests on 21 October
  2026 only; recheck the states before submission, and keep to what the
  threads say.
- The conjectures table is taken from `docs/conjectures/article.tex`, whose
  readings are machine transcriptions; its dates and pages are not checked
  on the facsimile.
- Bost–Charles 2016 and Grothendieck 1966/1969 are cited in the table by
  name only, without bibliography entries: add them, verified, if the table
  stays.
- Co-authors, acknowledgements, and the AI declaration's final wording are
  the author's to decide.

## Licence

The paper and these sources are © 2026 Michel Hua, licensed
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
