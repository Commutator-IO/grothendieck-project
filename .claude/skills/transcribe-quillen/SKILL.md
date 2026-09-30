---
name: transcribe-quillen
description: Transcribes a batch of twenty pages of one of Daniel Quillen's research notebooks (Clay Mathematics Institute, 1968–2003) into clean, mathematics-focused LaTeX with the same critical apparatus as the Grothendieck fonds — what was read, what was guessed, what is illegible. Use whenever someone asks to transcribe, read or put into LaTeX pages of Quillen's notebooks, or names one (1968-13, 1971-5, a lecture-notes file). The transcriptions stay local and are never committed or pushed — the notebooks are in copyright and the repository is public (#36).
---

# Transcribing a batch of Quillen's notebooks

**Nothing this skill produces leaves the machine.** Quillen died in 2011; the
notebooks are his family's in copyright and the scans are the Clay's. The
repository is public, so a transcription committed here would be published.
Until the Clay and the family have agreed (issue #36), every file is written
under `transcripts-quillen/`, which `.gitignore` excludes except for its
preamble. Never `git add -f` one, never paste one into an issue, a PR, a
commit message or the site. The site's Quillen tab would show transcriptions
only if built with `RENDER_QUILLEN=true`, and that switch is the user's, not
this skill's.

Since 2026-09-30 the user's instruction is to transcribe nothing yet. Run this
skill only when they ask for a specific notebook in so many words.

**Runs on Opus 5.5 or Opus 5, and on nothing else** — the same rule as
`/transcribe-grothendieck`, for the same reason: this is a sustained visual
attention task, and the file's header must say which model read the pages.
Opus 5.5 (`claude-opus-5-5`) by default; Opus 5 (`claude-opus-5`) permitted;
anything else, stop and say which model the session is on.

## What this produces

For **one batch of twenty PDF pages** of one notebook:

| File | Contents |
|---|---|
| `transcripts-quillen/<label>/batch-NN.en.tex` | The transcription — the mathematics, page by page, in English |

`<label>` is the notebook's label in `src/content/quillen.json` (`1971-5`,
`1983-Lecture Notes 5 Quillen`), with spaces turned into `_`. One batch per
pass and one pass per conversation, as for the fonds: past twenty pages the
reading weakens without warning.

There is no modernised edition, no TEI, no render step and no manifest entry:
`npm run render`, `npm run pdf` and `npm run tei` read `transcripts/` only,
and that is deliberate. The one check is that the file compiles (below).

## Before anything: what these pages are

### A diary of research, in English

Quillen kept the notebooks as a dated journal: an entry opens on its date
(« April 1 », « Dec 24 »), runs a page or ten, and the next day's picks up or
drops it. The date headings are the notebook's own structure; transcribe each
as `\subsection*{…}` with the date **exactly as written** (his abbreviations,
no year added). Where an entry takes up an earlier one (« cont. », « see Mar
30 »), keep the words as they stand.

He writes in English, and so does the edition: the transcription, and also
`\note{}` and `\drawing{}`, are English. Only the header comment addresses the
maintainers, and it is English too.

### Luke's index says what a notebook holds, not what a page says

Glenys Luke's index, published by the Clay, gives each notebook its dates and
subjects. `src/content/quillen.json` carries the entry as `index`. Read it
before the pages: it tells you which dates to expect and what the vocabulary
will be. **It never settles a reading.** Where the page and the index differ, as
on a date or a spelling, the page wins, and the difference goes into a `\note{}`
only if it matters to the mathematics.

### Pages are the PDF's pages

The Clay's files have no cover sheet and no archivists' numbering: page N is
PDF page N. `\page{N}` takes that number. Where Quillen paginated the notebook
himself, record his number once, on the page where it shows:
`\page{7}\note{notebook p.~12}`. A PDF page may show two facing pages. If it
does, say so in the header comment, and use `\pagerange{}` only if the batch
consistently puts two pages on one sheet.

### Not everything is his

Among the notebooks are typed papers, lecture notes by others, and preprints
filed with them (« Notes on a talk by May »). Handle them as the fonds handles others' typescripts
(folder 71): a text by someone else is summarised in a
`\note{}` per page, and his marks on it are transcribed in full. Lecture
notes in his hand are his, and are transcribed.

## The sequence

### 1. Get the pages

```bash
node scripts/quillen-mirror.mjs <group>     # e.g. 1971 — fills archives/quillen/<group>/
npm run tiles -- quillen/<label> <batch> --pdf archives/quillen/<group>/<label>.pdf
```

The mirror is private (it is under `archives/`, ignored) and is never served.
The tiles go to `archives/tiles/quillen/<label>/p<page>/`: the sheet whole,
six overlapping tiles at 700 dpi, and `tiles.json` for re-cropping a doubtful
word.

Read `references/hand.md` with the pages. It starts almost empty: it collects
what passes learn about his hand, and each pass adds to it what the next one
should not have to rediscover.

### 2. Read the twenty pages through, producing nothing

Note which pages carry mathematics, which entries the batch holds, the notation
fixed for the batch, and the internal cross-references. It is easier to see
what the batch is about now than after hours inside its notation.

### 3. Transcribe

Everything `/transcribe-grothendieck` says under « Transcribe the mathematics »
holds here, word for word — read that section; it is not repeated. In
particular:

- the mathematics first, and `tikz-cd` for every commutative diagram;
- his prose about the mathematics stays;
- uncertainty is marked, never resolved: `\ill{}` for what cannot be read,
  `\uncertain{}` for a reading offered;
- what he struck out stays: `\struck{}`;
- `\add{}` is his ink, `\supplied{}` is ours;
- no correction of his mathematics — flag it, do not repair it;
- the same permitted LaTeX subset, so that the file could be rendered one day
  without being rewritten.

The file opens like this:

```latex
% Transcription — Daniel Quillen, research notebook <label>, batch N (pages a-b).
% From the facsimile https://www.claymath.org/library/Quillen/… (Clay
% Mathematics Institute), read on the private mirror archives/quillen/….
% Luke's index entry consulted: yes.
% Not for distribution: the notebooks are in copyright (#36).
% Pass: Opus 5.5 (claude-opus-5-5), <date> — first pass, unchecked against the pages by a human.
\documentclass[11pt,a4paper]{article}
\input{../preamble/quillen}

\notebook{<label>}
\batch{N}
\pages{a}{b}
\dating{<the group the Clay files it under, verbatim: 1971, lectures, misc>}
\watermark{Demonstration edition}
```

`\dating{}` is the Clay's filing, not a date inferred here. His own dates are
in the entry headings. `references/specimen.tex` shows every macro in a
complete file.

### 4. Check

```bash
cd transcripts-quillen/<label> && tectonic batch-NN.en.tex
```

It must compile without errors, and no line may run past the right margin. Then
read the PDF beside the facsimile page by page. Leave the compiled PDF where it
is (ignored).

Close by telling the user the model, the pages read, what the batch is about,
the doubtful readings, and anything worth adding to `references/hand.md`. Add
that last item yourself.

## What not to do

- **Commit, push, upload or quote a transcription anywhere.** Not in an issue,
  not in the site, not in an article.
- **Fill a gap from Luke's index.** The index describes the notebook; it is not
  a second witness to the page.
- **Add a year to his dates, or a date he did not write.**
- **Transcribe the Clay's own sheets** (a cover or contents sheet, if a file
  has one). They are not his.
- **Extend the LaTeX subset.** It is shared with the fonds, and
  `scripts/render.mjs` defines it.
