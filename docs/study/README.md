# A machine reads Grothendieck's working notes

The article prepared for the *Journal of the Text Encoding Initiative*, and the
scripts that draw its figures and encode it. It is the second report of the
method first described for the Hopper ledgers
([hopper-project/docs/study](https://github.com/Commutator-IO/hopper-project/tree/main/docs/study)),
and follows that article's structure, build and submission checklist.

- `article.tex` — the article; `fig-*.tex` its four figures. `article.pdf` is
  built from it and committed, because the deploy serves it.
- `figures.mjs` — draws `fig-pace.tex` (from git's history), `fig-hand.tex`
  (from `src/content/hand.json`) and `fig-dating.tex` (from the inventory and
  `src/content/dated-leaves.json`). `fig-pipeline.tex` is drawn by hand,
  because it states decisions and not data.
- `tei.mjs` — the submission: the article encoded in TEI against the journal's
  own schema, `tei_jtei`, and validated against it in both halves (RELAX NG
  with jing, Schematron with SchXslt on Saxon). `npm run article-tei` compiles
  each figure on its own, rasterises it to PNG at 300 dpi, writes
  `submission/article.xml` beside the PNGs and the sources, copies the XML and
  the PDF to `public/article/`, and fails on any error the journal's validator
  would report. `submission/` and `public/article/` are not committed.

```bash
node docs/study/figures.mjs && (cd docs/study && tectonic -X compile article.tex)
npm run article-tei
```

The fonts are Charter and Menlo, as installed on macOS; the figures compiled
alone for the TEI use XCharter, which is in TeX Live.

## Before submission

The journal's guidelines, as read for the Hopper article (hopper-project #30,
#31): abstract 150–250 words (this one: 227), at most seven keywords and not
« TEI » (seven), a biography of at most 100 words, a body of 5,000–10,000
words (about 6,500), Chicago author-date, the AI declaration under its
prescribed heading, figures as PNG with a rights line (supplied by `tei.mjs`).

## Licence

The article and these sources are © 2026 Michel Hua, licensed
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The words of
Alexandre Grothendieck quoted in it are quoted for criticism and study; the
fonds is the University of Montpellier's, and no image of it is reproduced.
