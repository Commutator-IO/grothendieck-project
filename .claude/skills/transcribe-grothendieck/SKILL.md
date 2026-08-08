---
name: transcribe-grothendieck
description: Transcribes a batch of twenty handwritten leaves from the Alexandre Grothendieck fonds (University of Montpellier) into clean, mathematics-focused LaTeX with a critical apparatus — what was read, what was guessed, what is illegible. Use whenever someone asks to transcribe, decipher, read or put into LaTeX any pages of Grothendieck's manuscripts, or names a folder, a batch, or one of the notebooks (topos, motifs, Longue Marche, cahiers tardifs). Transcription only — the modernised reading has its own skill, /modernize-grothendieck, which runs on the transcription this one produces. Also covers revisions: correcting a reading, filling a skipped leaf.
model: claude-fable-5
---

# Transcribing a batch from the Grothendieck fonds


**Runs on Fable 5.** The frontmatter pins it, so invoking this skill switches
the model for the turn whatever the session was set to.

Reading seventy-year-old handwriting off fourteen page images at once is
the task this whole project turns on, and it is a sustained-visual-attention
task before it is a mathematical one. The pass is pinned to Fable 5 so that a
transcription's provenance is a fact about the file rather than a fact about
whichever model happened to be selected — every batch header records the model,
and they should all record the same one.

## What this produces

For **one batch of twenty leaves**, three LaTeX files:

| File | Contents |
|---|---|
| `transcripts/<folder>/batch-NN.fr.tex` | The transcription — the mathematics, leaf by leaf, in French |

One further edition derives from it, with its own skill, run afterwards:

| Skill | Produces |
|---|---|
| `/modernize-grothendieck` | `batch-NN.modern.tex` — a summary, then the mathematics in current notation; French |

`npm run render` turns each into the reading view the site's left pane shows;
`npm run pdf` compiles the PDFs the download buttons offer. The site has a tab
and a download row per edition — that is the full set of outputs, and there is
nothing else to produce.

**Two things govern everything below.**

**The LaTeX is clean and about the mathematics.** Not a diplomatic edition. The
archive's own material apparatus — which verso carried which administrative
letter, where a separator sheet fell, which page was scanned upside down — is
*not* the subject. It is noise in a document meant to be read as mathematics,
and it goes. What stays is what Grothendieck was actually working on.

**The editions stay separate, and this skill produces exactly one.** The
transcription is the mathematics and nothing else. No summary opens it, no
modernisation creeps into it: someone reading the transcription wants the
leaves. The derived editions are other skills' work, done afterwards, from
this file and never from the manuscript.

**One batch per pass, never two.** Past twenty handwritten leaves the quality of
reading degrades towards the end of the pass with nothing to signal it, and a
transcription whose weakening point is unknown cannot be used.

**Run under Fable 5, one batch per conversation.** The pass lives or dies on
sustained visual attention to fourteen-plus page images at once; a fresh
context per batch is what keeps leaf 18 read as carefully as leaf 2. Note the
model and the date in the file's header comment — a disputed reading years
later needs to know what produced it.

## Before anything: what these leaves are

Everything downstream follows from this, and a transcription made without
knowing it will be wrong in a way that is hard to repair afterwards.

### They are working notes, not texts

Grothendieck wrote for himself, day by day. He takes the same chapter up four
times over — the four *moutures* of *Analysis situs*, June 1986, sit in one
folder and read in sequence. He abandons a proof mid-way, picks it up thirty
pages later, refers to a leaf by its number. **Do not smooth this out.** A
restart is not a repetition to be deleted; it is the object itself.

### The versos carry other people's paper

He wrote on the back of whatever was to hand: letters from the USTL
administration, offprints, Bourbaki seminar notes, typescripts his secretary
had returned. The digitisation kept them **deliberately**, and the archive says
so plainly: "the reverse pages of the documents are often unrelated to the
mathematical notes."

For a mathematics-focused transcription this means, without exception:

- **A leaf whose content is not the mathematics in hand is not transcribed and
  not described.** No inventory of what the administrative letter said. Skip it
  — the leaf number simply does not appear.
- **A page that looks illegible may be upside down.** Unrelated versos were
  scanned in whatever orientation preserved the physical object. Turn it before
  calling it illegible.
- **A verso that *is* related** — a calculation continued on the back — is
  transcribed like any other leaf.

### Three numbering systems overlap

1. **Grothendieck's own**, where he paginated — the Long March runs 1 to 787
   across four boxes.
2. **The archivists'**, pencilled bottom-left on every leaf. This is what the
   inventory counts ("Cote n° 26, 10 pages") and what this project calls a
   *leaf*.
3. **The PDF's**, one ahead, because of the cover sheet Montpellier generates.

`\leaf{N}` always takes **the archivists' numbering**. Where Grothendieck's own
pagination is visible and useful for following a cross-reference, record it once:
`\leaf{47}\note{author's p. 213}`.

### Almost nothing is dated

Outside correspondence the inventory's dates are inferred — from a dated verso,
a numbered Bourbaki talk, an institute letterhead. **Never invent a date.** If a
leaf carries one, transcribe it; otherwise say nothing.

The late notebooks are the exception, and why they are worth starting with:
*Vers une géométrie des formes* dates nearly every chapter to the day.

### Bracketed titles are not his

In the inventory a `[bracketed]` title was supplied by the archivists because
the folder bore none. Reusing it unmarked attributes to Grothendieck a phrase
he never wrote.

## The sequence

### 1. Read the twenty leaves through, before writing a line

Open the facsimile with the file-reading tool — the pages render visually.
Either source works: the batch file if the folder has been mirrored
(`npm run archive -- <folder> --batches N`), or the folder's own PDF, in which
case remember the cover sheet offset.

Make one complete pass producing nothing, and note:

- **Which leaves are mathematics and which are not.** The second group will not
  appear in the output at all.
- **The notation of this batch.** Grothendieck's habits change over the years:
  a `\mathcal{C}` of 1962 is not drawn like one of 1986, he abbreviates, he
  writes $\widetilde{X}$ for a topos of sheaves, he spells out "fppf" then
  reduces it to initials. Fix the choices **once for the batch** and hold to
  them.
- **The internal cross-references** — "cf. p. 12", "voir plus haut" — which
  become `\ref{leaf:12}`.
- **What the batch is actually about.** You will need this for the summary, and
  it is much easier to see now, with all twenty leaves in view, than after
  three hours inside the notation.

### 2. Transcribe the mathematics

`\leaf{N}` at the start of each transcribed leaf, in order. Leaves that carry
no mathematics are simply absent — no placeholder, no note. A gap in the leaf
numbers *is* the record that something was skipped, and it is quiet enough not
to interrupt the reading.

In priority order:

1. **The mathematics is the document.** Where a leaf is too crowded to render
   whole — a diagram crammed into a margin, a formula overwritten three times —
   transcribe the mathematics and compress the surrounding prose, marking the
   compression with `\note{}`. The reverse is easy to produce and worthless.
2. **Commutative diagrams go into `tikz-cd`**, never into prose. That is the
   language of this fonds.
3. **His own prose stays, when it is about the mathematics.** "Focus on the
   mathematics" excludes the archive's material apparatus, not Grothendieck's
   words. Where he stops to say why a definition is the right one, or how the
   notion came to him, that is the content — often the best of it — and it is
   transcribed like everything else.
4. **Uncertainty is marked, not resolved.** An invented word that reads like the
   others is the worst possible outcome: nothing on the page distinguishes it
   from a sure reading. `\ill{}` and `\uncertain{}` exist so that never happens.
5. **The language stays his — and so does yours.** He writes in French, with
   his turns of phrase, his punctuation, his long sentences. Do not modernise,
   do not correct spelling, do not break up his sentences. An obvious slip
   stays and is flagged: `\uncertain{catégorei}\note{sic}`.

   **The transcriber's own prose is French too**, not only his: `\note{}` and
   `\marginal{}` are part of the edition a French reader reads straight
   through, and an English note in the middle of a French transcription is a
   seam in the one document that must not have one. This holds whatever
   language the pass is being run in or discussed in. The whole file is
   French; only the file's header comment, which is addressed to whoever
   maintains the repository, is English.
6. **What he struck out stays**, as `\struck{}`. A deletion often shows where
   the thought changed direction.

#### The apparatus, kept to what earns its place

| Macro | Use |
|---|---|
| `\leaf{47}` | leaf 47 begins (archivists' numbering) — this is what turns the facsimile as you scroll |
| `\ill{}` | illegible — **never guessed** |
| `\uncertain{word}` | a reading offered, and flagged as doubtful |
| `\add{s}` | an editorial addition: a missing letter, an implied word |
| `\struck{word}` | struck out by Grothendieck |
| `\note{…}` | the transcriber's note — **about the mathematics**, not about the paper |
| `\marginal{…}` | a marginal note **of his**, distinct from the body |

`\note{}` and `\marginal{}` are not interchangeable: the first is ours, the
second is his.

`\note{}` has become the easiest macro to overuse. It is for something a reader
of the mathematics needs — "the next step is missing", "author's p. 213", "the
diagram here is redrawn from a sketch". It is **not** for "stain on the paper",
"scanned upside down", "verso is a letter". Those observations belong to the
archive, and the archive already has them.

#### The permitted LaTeX subset

`scripts/render.mjs` understands a subset, **deliberately**: a converter that
accepted everything would silently mangle what it did not understand. Stepping
outside makes rendering fail loudly, which is the wanted behaviour.

Allowed: `\section` `\subsection` · paragraphs separated by a blank line ·
`\emph` `\textbf` `\textit` `\texttt` · `itemize` `enumerate` `quote` ·
`summary` · `tikzcd` (arrow syntax below) · `$…$` `\(…\)` `\[…\]` `equation`
`align` `gather` `cases` `array` and the matrix environments · the seven macros
above.

Apparatus macros may contain mathematics — `\note{the $\varphi_{*}$ here is
struck}` is the common case, not the exotic one, and the renderer matches
braces to allow it.

Mathematics is **not** converted: the delimiters pass through and KaTeX sets
them in the browser, so screen and PDF come from one source.

**Commutative diagrams are rendered in both.** In the PDF, by `tikz-cd`. In the
reading view, by a renderer that lays the nodes out in a CSS grid, typesets
each with KaTeX, and draws the arrows in SVG from the measured cell positions —
so the mathematics stays selectable text rather than becoming a picture. The
LaTeX source stays available under a fold beneath each diagram.

That renderer covers exactly the arrow syntax below, and **raises on anything
else** rather than dropping it — a diagram rendered with an arrow missing
asserts a commutation nobody wrote:

- directions built from `u` `d` `l` `r`, repeatable: `\arrow[d]`, `\arrow[rr]`,
  `\arrow[dl]`;
- an optional quoted label, with a trailing `'` to put it on the other side:
  `\arrow[d, "\approx"]`, `\arrow[d, "f_{!}"']` — or ` description` after the
  quotes to set it on the shaft itself, background knocking the line out:
  `\arrow[uu, no head, "\wedge\wedge" description]`;
- the styles `hook`, `hook'` (inclusions) and `Rightarrow`;
- `no head`, for a line that is scaffolding rather than a functor — an axis,
  a radius. A head the leaf does not have asserts a morphism nobody wrote;
- `bend left=N` / `bend right=N`, for arcs. Eight rim arcs at matching bends
  are what lets a wheel of functor categories close into the circle the
  manuscript draws instead of an octagon of chords.

Extending the subset means extending `scripts/render.mjs` in the same commit.

Two layout rules, both learned on a real batch:

- **A `tikzcd` sits in its own paragraph** — blank line before and after.
  Inline after a colon it inherits the paragraph's baseline and walks off the
  right margin.
- **Wide diagrams take `[column sep=small, row sep=small,
  nodes={font=\scriptsize}]`.** A wheel of eleven functor categories does not
  fit an A4 measure at text size, and an overfull box in a transcription is
  not a cosmetic defect: it hides content. (Those options affect the PDF only;
  the reading view sizes itself.)

**Wheels — census before drawing.** Learned on folder 115, leaf 5, by getting
it wrong first: a circle of functor categories is almost never one ring of
arrows. Before writing any `\arrow`, work through the facsimile at high
resolution — `pdftoppm -png -r 400` on the folder's PDF, then crop quadrant
by quadrant with `-x -y -W -H` — and take a census:

- **count distinct labels**, and look for repeats: on 115 the two inner
  categories each appear twice, at the two ends of a diameter, and the
  margin's own tally (« 6 cas », « 4 cas ») confirmed the count;
- **separate the rings** — centre, inner ring, rim — and lay them out on a
  grid with odd dimensions so the centre has a cell (a 7×7 held centre,
  four inner nodes, eight rim nodes and four corner annotations);
- **note which strokes are headless** — axes and radii are scaffolding, not
  functors — and transcribe them `no head`, their variance marks as
  `description` labels riding the line;
- **check every arrowhead one by one.** On 115 the eight rim arcs all
  converge into the four mixed three-argument forms, and one diagonal runs
  inward (a restriction) while the other three run outward (extensions).
  The asymmetry is on the leaf, so it is in the transcription; deciding it
  is an oversight is the reader's job, not ours.

A first pass had reduced that wheel to eight radiating arrows and misread
the mid-rim labels' argument lists. Every difference between that and the
leaf was mathematical content.

`references/specimen.tex` shows every macro in a complete file.

### 3. Check

```bash
npm run render      # fails loudly if the subset was left
npm run pdf         # compiles the three PDFs
npm run manifest    # declares the files to the site
```

Then read the rendered view **beside the facsimile**, on the notebook page.
That is precisely the gesture the site exists to allow, and it is the only
check worth anything: scrolling the transcript turns the facsimile's pages.

Two mechanical checks before the human one, because each caught a real defect
on the first batch: the reading view must contain **zero `katex-error`
nodes** (a formula that failed to typeset renders as red source), and the PDF
must show **no line running past the right margin** — overfull boxes in a
transcription hide content. Reload the browser tab before counting: a cached
frame happily shows yesterday's rendering.

## What not to do

- **Fill a gap.** An illegible word stays `\ill{}`. Always.
- **Guess a date, a recipient, a reference.** If the leaf says "SGA 4 exposé 8"
  and no more, transcribe that and do not go and open SGA 4.
- **Correct a mathematical error.** If a calculation is wrong on the leaf, it is
  wrong in the transcription. Flag it with `\note{}`; do not repair it.
- **Catalogue the paper.** No verso descriptions, no separator sheets, no
  orientation notes. That is the archive's job and the archive has done it.
- **Merge two *moutures*** because they look alike. Their difference is the
  information.
- **Extend the LaTeX subset without extending `scripts/render.mjs`.**

## Revising a batch

Corrections go in the `.tex`, never in the HTML or the PDF, which are derived.
A correction to a reading is also a correction to the translation: take both
files up together, or they drift.

On the notebook page a batch's state changes with a click — `Drafted` once the
LaTeX exists, `Checked` only after leaf-by-leaf comparison. It is a
declaration, not an observation: the site verifies nothing. Only tick `Checked`
if it is true.
