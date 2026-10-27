# Formalising a mathematician's working notes

The paper prepared for CICM, the Conference on Intelligent Computer
Mathematics (Springer LNCS/LNAI). It is the complement of the jTEI article
([`docs/study/`](../study/README.md)): that one covers the transcription, its
encoding and the checking of the readings; this one covers the formalisation
of the statements in Lean (`lean/`), with the appendix
([`docs/lean/`](../lean/article.tex)) as its long form.

- `article.tex` — the paper, in `llncs` (tectonic fetches the class and
  `splncs04.bst` from CTAN; nothing is vendored); `references.bib` its
  bibliography, every entry checked on 21 October 2026 and those added since
  on 25 October (DOIs on Crossref, arXiv identifiers on the arXiv API, two
  items on zbMATH Open, URLs by request).
- `fig-pipeline.tex` — the pipeline from page to theorem, drawn by hand,
  because it states decisions and not data.
- `figures.mjs` — reads the repository **at one commit** (`SNAPSHOT`, now
  81dcfaf; never the working tree) and writes `fig-themes.tex`, the theorems
  per part of the Lean appendix, and `fig-counts.tex`, every count the text
  cites as a `\cnt…` macro: Lean files, lines and declarations, proof cards
  and verdicts, the appendix's labels and pages, commits, findings,
  transcription totals, review answers. Moving `SNAPSHOT` is deliberate:
  rerun, then reread the prose around the numbers (the errors on the page,
  folder 146).
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
the 2026 deadlines were in April. This draft is 17 pages, the body ending on
page 14 and the references after it, so there is about one page to spare.
It fits the « project and survey » category best. Springer compiles with
pdfLaTeX; the site copy is built with XeTeX (tectonic), and the pdfLaTeX
branch of the preamble has not been run here.
Check the 2027 call when it appears (limit, category, deadlines, whether the
review is double-blind: if it is, an anonymous version is needed).

## What remains to check

- The counts are frozen at 81dcfaf (24 October 2026). Before submission,
  move `SNAPSHOT`, rerun `figures.mjs` and reread the paragraphs that comment
  on the numbers.
- The pull requests (39, all closed, 36 by the triage account) were counted
  on 25 October 2026; recheck before submission. J. Riou's and E. Wieser's
  public comments are paraphrased: consider telling them.
- The conjectures table is taken from `docs/conjectures/article.tex`, whose
  readings are machine transcriptions; its dates and pages are not checked
  on the facsimile (the caption says so).
- Folder 146: the odd-n Picard groups were recomputed by the edition and are
  not checked; the paper says so.
- Kleiman 1968 and 1994, Cisinski 2006, Maltsiniotis 2005, Williams 1969:
  theorem numbers taken from the repository's readings, not rechecked.
- Co-authors and acknowledgements are the author's to decide.

## Licence

The paper and these sources are © 2026 Michel Hua, licensed
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
