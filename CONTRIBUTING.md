# Contributing

**The full guide, with installable skills and copy-paste commands, is at
[grothendieck.commutator.io/contribute](https://grothendieck.commutator.io/contribute/).**
This file is the short version, for people who arrive through GitHub.

Everything on the site is first-pass machine work and says so. Corrections are
the point of publishing it.

## Three ways in, cheapest first

**1. Report a reading — one click.** Every batch on the site has a *Report a
reading* button that opens an issue with the shelfmark, batch and page already
filled in. You need no LaTeX, no clone, and no theory about what the word
should be. This is the most valuable thing anyone can do here: a reader who
spots a misread symbol is, at that moment, the only person who knows.

**2. Correct a reading — a pull request.** The `.tex` under `transcripts/` is
the source of record. Edit it, and the diff shows exactly what changed about
the reading.

**3. Transcribe a folder.** Install the skills, mirror a folder nobody has
taken, run the two passes.

```bash
npm run archive -- 19          # mirror it, cut into 20-page batches
claude                         # then, in order:
  /transcribe-grothendieck 19, batch 1
  /modernize-grothendieck 19, batch 1
npm run render && npm run pdf && npm run manifest
```

Check the archive page first: folders with a **green** rule already have a
scholarly edition, which is better than anything produced here. Folders with a
**blue** wash have been transcribed here already.

## The editions are written in French

Whoever runs the pass. The pages are French, the notions were thought in
French, and an English note in the middle of a French transcription is a seam
in the one document that must not have one. The only English inside an edition
is the `\keywords{}` line, which is a set of search keys.

Everything *around* the editions — this file, the code, commit messages,
issues — is English.

If that rules a folder out for you, routes 1 and 2 need no French at all.

## Rules of the road

- **Never fill a gap with a plausible word.** Illegible stays `\ill{}`,
  doubtful stays `\uncertain{}`. An invented word that reads like the others is
  the worst possible outcome, because nothing distinguishes it from a sure
  reading.
- **Never correct Grothendieck.** A wrong calculation on the page is wrong in
  the transcription, with a `\note{}`. The modernised reading is the one place
  that states what is true instead — and footnotes what the page has.
- **Never tick `checked`.** Unless you personally compared the batch with the
  facsimile, page by page. It is a declaration in `transcripts/status.json`,
  and the one claim here no file can prove.
- **Change only the source.** `public/transcripts/`, `public/manifest.json` and
  every PDF are derived and git-ignored. Never commit them.
- **Take both editions up together.** A correction to a reading is usually a
  correction to the modernised reading too, or they drift.
- **Stay inside the LaTeX subset.** `scripts/render.mjs` accepts a restricted
  subset deliberately and fails loudly on anything else — a diagram rendered
  with an arrow silently dropped asserts a commutation nobody wrote. Extending
  the subset means extending the renderer in the same commit.

## Before you open the pull request

```bash
npm run lint && npm run render && npm run pdf
```

CI runs the same on your branch. Nothing deploys from a pull request; only
`main` does.

## Licence

CC0 1.0 — the work goes into the public domain, which is the only licence that
makes sense for readings of a fonds nobody owns. By contributing you agree to
release your contribution under it.
