---
name: transcribe-grothendieck
description: Transcribes a batch of twenty handwritten leaves from the Alexandre Grothendieck fonds (University of Montpellier) into clean, mathematics-focused LaTeX, opened by a plain-English summary written for an undergraduate maths student, plus an English translation. Use whenever someone asks to transcribe, decipher, read, clean up or put into LaTeX any pages of Grothendieck's manuscripts — "help me transcribe these pages to latex, these are maths notes from Alexander Grothendieck", "summarise them in simple English", "explain this to an undergraduate maths student" — or names a folder, a batch, or one of the notebooks (topos, motifs, Longue Marche, cahiers tardifs). Also covers revisions: correcting a reading, filling a skipped leaf, redoing a translation that came out too literal, rewriting a summary that assumes too much.
---

# Transcribing a batch from the Grothendieck fonds

## What this produces

For **one batch of twenty leaves**, three LaTeX files:

| File | Contents |
|---|---|
| `transcripts/<folder>/batch-NN.fr.tex` | Summary, then the French transcription — the mathematics, leaf by leaf |
| `transcripts/<folder>/batch-NN.en.tex` | Summary, then the English translation of that transcription |
| `transcripts/<folder>/batch-NN.summary.tex` | The summary alone, standing on its own |

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

**The summary comes first, at the top of the document.** Not an appendix, not a
separate thing one has to go and find. These are working notes: nobody walks
into them cold, not even a mathematician from another field. A reader landing
on page 213 of the Long March without knowing what is being attempted does not
read more slowly — they do not read at all.

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
5. **The language stays his.** He writes in French, with his turns of phrase,
   his punctuation, his long sentences. Do not modernise, do not correct
   spelling, do not break up his sentences. An obvious slip stays and is
   flagged: `\uncertain{catégorei}\note{sic}`.
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
  `\arrow[d, "\approx"]`, `\arrow[d, "f_{!}"']`;
- the styles `hook`, `hook'` (inclusions) and `Rightarrow`.

Extending the subset means extending `scripts/render.mjs` in the same commit.

Two layout rules, both learned on a real batch:

- **A `tikzcd` sits in its own paragraph** — blank line before and after.
  Inline after a colon it inherits the paragraph's baseline and walks off the
  right margin.
- **Wide diagrams take `[column sep=small, row sep=small,
  nodes={font=\scriptsize}]`.** A wheel of eight functor categories does not
  fit an A4 measure at text size, and an overfull box in a transcription is
  not a cosmetic defect: it hides content. (Those options affect the PDF only;
  the reading view sizes itself.)

`references/specimen.tex` shows every macro in a complete file.

### 3. Write the summary, and put it at the top

In English, plain, one to two pages, inside `\begin{summary}…\end{summary}` as
the **first thing after `\begin{document}`** — before the first `\leaf`.

The reader has finished an undergraduate degree. They know groups, rings, some
topology. They do **not** know schemes, topoi, or étale cohomology, and must
not be assumed to.

Four questions, in this order:

1. **What are these twenty leaves about**, in one sentence, without jargon?
2. **What problem** is Grothendieck trying to solve, and why does that problem
   arise at all?
3. **What idea** does he bring to it — by analogy where necessary, without
   pretending to rigour?
4. **Where does it lead** in his work, and where can the reader go next?

Keep out: proofs, the critical apparatus, uncertain readings. The summary is
not an abridged transcription but a text that stands by itself, and it carries
**no** `\leaf{}`.

One thing does belong there, and is often the most valuable: **his reflection on
his own practice.** These notebooks are full of remarks on how a notion arrives,
on what he called the attitude of listening, on what understanding actually is.
They need no background at all, and they are why someone who will never do
algebraic geometry might want to read these pages.

The same summary block opens `.fr.tex` and `.en.tex`, and is the whole of
`.summary.tex`. Write it once; do not let three versions drift apart. It stays
in English even at the head of the French transcription — it is not part of
Grothendieck's text and must not be mistakable for it.

### 4. Translate — from the transcription, never from the leaf

`batch-NN.en.tex` derives from `batch-NN.fr.tex`. **Do not re-read the
manuscript to translate.** Both English documents (`en`, `summary`) put
`\selectlanguage{english}` immediately after `\begin{document}`: the shared
preamble defaults to French typography, which puts spaces before colons —
correct for his text, a fault in yours. Two independent readings of the same handwriting
would diverge, and nothing would say which was right.

- The apparatus macros carry over unchanged, in the same places. A word
  illegible in French is illegible in English.
- Mathematical terminology takes its established English form: *faisceau* →
  *sheaf*, *champ* → *stack*, *revêtement* → *covering*, *lisse* → *smooth*,
  *plat* → *flat*, *topos annelé* → *ringed topos*. Where in doubt, keep the
  French in italics and flag it.
- Terms he coined that have no equivalent — *la Longue Marche*, *Récoltes et
  Semailles*, *dérivateur*, *mouture* — stay in French.
- The register stays his: first person, sometimes addressing himself,
  digressing. A translation that flattens that into impersonal mathematical
  prose has lost what makes these notebooks worth reading.

### 5. Check

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
- **Write a summary that needs the transcription to make sense.** If it cannot
  be read on its own, it is not a summary.
- **Translate from the manuscript** instead of from the transcription.
- **Extend the LaTeX subset without extending `scripts/render.mjs`.**

## Revising a batch

Corrections go in the `.tex`, never in the HTML or the PDF, which are derived.
A correction to a reading is also a correction to the translation: take both
files up together, or they drift.

On the notebook page a batch's state changes with a click — `Drafted` once the
LaTeX exists, `Checked` only after leaf-by-leaf comparison. It is a
declaration, not an observation: the site verifies nothing. Only tick `Checked`
if it is true.
