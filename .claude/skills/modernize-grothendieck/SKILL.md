---
name: modernize-grothendieck
description: Produces the modernised reading of an already-transcribed folder of the Grothendieck fonds — taken whole, all its batches in one pass — a summary (« Résumé ») that orients a reader new to the subject, then the mathematics in current notation and current names, in French, mathematically correct as it stands, with footnotes carrying everything the transcription's critical apparatus carried. Use when someone asks to modernise, clean up, reinterpret, restate, summarise or explain a transcribed folder ("modernize folder 115", "give the modern reading", "explain these pages"), or after /transcribe-grothendieck has transcribed a folder's batches. Also covers revisions - tightening a statement, correcting a variance, rewriting a summary that assumes too much.
model: claude-opus-5
---

# The modernised reading of a folder


**Runs on Opus 5.** The frontmatter pins it, so invoking this skill switches
the model for the turn whatever the session was set to.

The standard this edition is held to — correct as it stands, with the four
failure modes checked — is a reasoning standard, and folder 115's reading is
what it was calibrated against. That reading was made on Opus 5, and its
header says so. Pinning the same model keeps the calibration meaningful: a
reading produced under a different one is not comparable to the reference, and
the header would say so only after the fact.

## What this produces

**The unit is the folder, not the batch.** That is the one place this skill
parts company with `/transcribe-grothendieck`, and the reason is what each
edition is for. Transcription is cut to twenty pages because reading that much
handwriting is as far as one pass carries. This edition has no such ceiling —
it reads typed LaTeX — and it has the opposite need: its job is to make an
argument run continuously, and Grothendieck's arguments do not stop at page 20.
Folder 151's semi-simplicial formalism opens on page 44 and is still being
built on page 74, across three batches. Modernised batch by batch it would be
restated three times by three passes that never saw each other, each guessing
where the construction was going.

So the skill is invoked once per folder:

```
/modernize-grothendieck 151
```

and it writes, in that one pass, one file per batch — the layout the site
reads:

| File | Contents |
|---|---|
| `transcripts/<folder>/batch-NN.modern.tex` | for **every** batch NN of the folder: a summary, then the mathematics in today's notation and names — **in French**, like the pages |

One file per batch is not a leftover: the reading view puts each edition beside
the facsimile pages it covers, and a single folder-wide document could not be
put beside anything. What changes is not the output layout but what the writer
knew — the whole folder — when each file was written.

A batch range may be given (`/modernize-grothendieck 151 3-4`) when only part
of a folder is being revised. Even then, **read the folder's transcriptions
whole first**; only the writing is narrowed.

It is an **interpretation, not a transcription**: it reorganises by argument,
states what the manuscript leaves implicit, and reads continuously, the way a
survey would. Where it and the transcription disagree in substance, the
transcription is the record. Anyone citing Grothendieck cites
`batch-NN.fr.tex`; this edition is for reading.

**Precondition: the transcriptions exist.** This skill reads
`batch-NN.fr.tex`, never the facsimile. Two independent readings of one hand
diverge, and nothing would say which is right. If a batch has no transcription,
stop and say which — do not transcribe on the way through.

Where a folder is only partly transcribed, say so and offer the choice: modernise
the transcribed batches now, knowing the argument's end is not yet in view, or
wait for the folder to be finished. Do not decide it silently — a reading made
without the last batch can be wrong in ways it cannot detect, and its header
will not say so.

## The summary

**Every batch's file opens with one** — `\section*{Résumé}`, before any
mathematics — and it is the only part of the project written for someone who
has not met the subject. One page, perhaps two.

The folder being the unit changes what these summaries say to each other. The
**first batch's** résumé orients over the whole folder: what the folder is
about, where its argument is going, what it will have built by the last page.
Each **later batch's** résumé is shorter, and does one thing the batch-by-batch
version could not — it situates that batch inside the folder's argument: what
has been established, what this stretch adds, what is still open. It does not
re-narrate the folder from the start, and it does not pretend the reader
arrived here first.

A reader may open any batch directly, so no résumé may depend on having read
another. Situating is not the same as continuing: one sentence recalling what
the construction is costs nothing and is what makes the file stand alone.

Its job is orientation, and it answers four questions in order:

1. **De quoi ces feuillets parlent-ils**, en une phrase sans jargon ?
2. **Quel problème** est attaqué, et pourquoi se pose-t-il ?
3. **Quelle idée** arrive — par analogie s'il le faut, sans prétendre à la
   rigueur ?
4. **Où cela mène-t-il**, et quels noms modernes chercher ensuite ?

The analogy is the main instrument. Folder 115's summary carries the
whole of Isbell duality on two: shadows cast from the left and from the right,
and the reflexivity of $V \to V^{**}$ in linear algebra. An analogy does not
pretend to rigour, and should not be dressed as if it did.

Assume a first degree in mathematics and no more: groups, rings, some
topology — **not** schemes, not topoi, not étale cohomology. Every notion
beyond that is either explained by analogy or not used. But **do not say so**.
No sentence names the reader's level, no heading says « pour la licence » or
« for undergraduates ». Announcing who a text is for is how you lose everyone
else, and a reader who needs the orientation will take it without being told
they needed it.

One thing belongs here whenever the batch offers it, and it is often the most
valuable: **Grothendieck's reflection on his own practice** — how a notion
arrives, what he called the attitude of listening, what understanding is. It
needs no background at all, and it is why someone who will never do algebraic
geometry might read these pages.

No apparatus in the summary, and no footnotes: doubts at the level of
single words belong to the transcription, and anything large enough to matter
at this altitude goes in the prose (« la datation vient des versos »). The
summary carries no `\page{}` either.

## The keywords

The résumé closes with one line, before `\end{resume}`:

```latex
\keywords{profunctor, Isbell duality, Cauchy completion}
```

Three to six terms, **in English** — they are search keys, not prose, and
the literature they point into is English — naming the modern vocabulary
under which what that batch builds is known today. They are the natural
sharpening of the résumé's fourth question (*quels noms modernes chercher
ensuite*), so write them when the résumé is written, last.

Each batch carries its own line, and the folder being written in one pass is
what makes them worth having separately: they should partition the folder's
vocabulary rather than repeat it. A term already earned by batch 1 is not
re-listed by batch 3 unless batch 3 is where it is actually built.

This line is the single source of the folder's tags: `npm run manifest`
extracts every `\keywords{}` of the folder's modernised readings, unions
them, and the archive and notebook pages show them as the folder's tags.
There is no tags file to edit, deliberately — a tag with no modernised
reading behind it would be a claim about content nobody has read.

## The standard: correct as it stands

This is the one edition where fidelity to the page is not the highest duty.
It is held to being **mathematically correct as written**. Where the
manuscript is loose, elliptical or wrong, the modernised reading states what
is *true*, and a footnote says what the page has. Reproducing an error
faithfully, in an edition whose whole promise is that it can be read as
mathematics, launders the error through the appearance of a modern text.

Four failure modes, each hit on a real batch (folder 115); check for all four:

- **Variances.** These notes are about two-sided constructions, and variance
  is where a plausible-looking modernisation does the most damage. A kernel
  contravariant in both arguments induces a *dual* adjunction, not an
  adjunction, and is not a profunctor — calling it one is false, not loose.
  Check every functor's variance before naming what it is.
- **Implicit hypotheses.** If a universal property needs $M$ cocomplète and
  the page does not say so, say so — and footnote that it was supplied.
  A statement that is only true under a hypothesis the reader cannot see is
  not correct as it stands.
- **Containments upgraded to equalities.** The manuscript's shorthand often
  looks like an equation ($A = \widehat{A} \cap A^{\vee\circ}$) where only a
  containment, or an equivalence onto an image, actually holds. Assert what
  holds; footnote the rest. On folder 115 the reflexive objects can strictly
  exceed $\mathrm{Kar}(A)$ — the equality would have been wrong.
- **Modern names.** Name them — dualité d'Isbell, complétion de Cauchy, cofin
  — and footnote whether the manuscript could have known them. That footnote
  is often the most interesting sentence on the page, and it is also where
  priority questions live; do not imply he cited work he did not.

## The apparatus becomes footnotes

**No square brackets, no underlines, no `\ill{}` — no apparatus at all.**
Everything it carried moves into `\footnote{}`: an uncertain reading the
interpretation depends on, a notation he used differently, a passage that is
missing, a convention that had to be chosen. The reader must still be able to
tell what was on the page and what is ours; footnotes are simply a better
place to say it in a text meant to be read continuously.

**No `\page{}` markers — but `\pagerange{first}{last}` at each section.**
This edition groups by argument, not by sheet, so no single page of the
source lines up with one paragraph of it: a page-by-page anchor the way the
transcription has one would be false. What is true, and worth having, is
coarser — which facsimile pages a section as a whole is drawn from. Place
`\pagerange{first}{last}` as the very first thing in the same block as each
`\section*{}`/`\subsection*{}` that opens over new pages, no blank line
between, exactly where `\page{}` would sit in the transcription. It drives
the same scrolling: the facsimile jumps to the section's first page once,
when the section comes into view, and holds there until the next marker
does — not a claim that every sentence in between is on that page, only that
the section as a whole is. Ground every range in the transcription's own
`\page{}` markers and the section's actual content before writing it down;
guessing from a heading is how a reader ends up looking at the wrong page.

Where a section already states its range in prose in the title (« La partie
fixe d'une adjonction (pages 3 à 5) ») — keep doing that too, for a reader
without the facsimile pane open at all. `\pagerange{}` is the separate,
machine-readable anchor behind it, not a replacement for it.

## Language and form

**In French.** The pages are in French, the notions were thought in French,
and the modernised reading has no reason to change language. Today's *names*
are used in their French forms: dualité d'Isbell, complétion de Cauchy,
enveloppe de Karoubi, cofin, curryfier.

Each document takes the shared preamble (`\input{../preamble/grothendieck}`),
its own batch metadata (`\folder`, `\batch`, `\pages`, `\dating` — copied
unchanged from that batch's transcription, since it is Montpellier's claim and
not a reading — and `\foldertitle` ending
« — lecture modernisée »), and the pass header comment naming the model and
date. The header says `Opus 5 (claude-opus-5)` because the frontmatter pins it;
if the session is somehow on another model, stop rather than write a header
that is true only of the pin. Say in the header that the folder was read whole,
and which batches the pass covered — a later reader cannot otherwise tell a
file written with the folder in view from one written before that was the rule.

It also carries its own legal notice, stronger than the transcription's,
because this edition is doubly ours — an unauthorised working document *and*
one reader's reading:

```latex
\watermark{Édition de démonstration\\interprétation personnelle de l'œuvre}
```

The preamble prints it in the title block and diagonally across every PDF
page; the reading view shows it too. Never omit it, and never soften the
second line: whoever cites this file must know it interprets. Structure with `\section*` and `\subsection*` following the argument.
Stay inside the LaTeX subset of the transcribe skill — the renderer raises on
anything else — plus `\footnote{}`, which the reading view renders as
numbered notes with backlinks, and `\pagerange{}{}`, described above.

Diagrams follow the transcribe skill's tikz-cd rules, wheels included —
rings on a grid of odd dimensions, `no head` radii with `description`
variance marks, rim arcs at matching bends. One liberty is this edition's
alone: where the page mixes directions among arrows that are all
equivalences (115 draws one diagonal as a restriction, inward, and three as
extensions, outward), the modernised wheel may normalise them to one
convention — with a footnote saying what the page draws and why both are
legitimate. Check the structure against the transcription's, node for node:
a wheel is a census (115: eleven distinct categories, two of them drawn
twice), and dropping a ring or an arc changes what is being asserted.

## The sequence

**Read the folder before writing any of it.** Steps 1 and 2 run once, over
every batch; steps 3 to 5 run per batch, in order, and step 6 once at the end.

1. Read **every** `transcripts/<folder>/batch-NN.fr.tex`, in order, in full,
   twice: once for the mathematics, once listing every `\uncertain{}`,
   `\ill{}` and `\note{}` — that list is the skeleton of the footnotes. Read
   the transcriptions' header comments too: they record what the reader of the
   hand found hard, which is where this edition is most likely to go wrong.
2. Identify the **folder's spine** — the construction the folder as a whole is
   building — and only then decide where each batch sits on it. Write the plan
   down before writing prose: for each batch, what it contributes to the spine
   and what it may therefore assume. This is the step the batch-by-batch
   version could not do, and skipping it wastes the folder-wide read.
   A construction that outlives a batch boundary gets **one** name, one
   notation and one convention for the whole folder, fixed here; changing
   notation mid-folder is the failure this scope exists to prevent.
   Where the folder restarts on itself — the *moutures* of one chapter — say
   so on the spine and keep them distinct. A restart is not a repetition to be
   merged; that difference is content.
3. Write each batch's body, in batch order, holding to the standard above.
   Every departure from the page gets a footnote at the point of departure.
   Where a batch continues a construction begun earlier, cite the earlier
   batch's section rather than restating it — but recall in one sentence what
   the construction is, so the file still stands alone.
4. Write each batch's summary **last within that batch**, when you know what
   it turned out to be about. Written first it describes what you expected to
   find. Batch 1's orients over the folder; later ones situate. Close each with
   its `\keywords{}` line — the folder's tags come from nowhere else.
5. Before leaving a batch, check it against the plan from step 2: is the
   notation the folder's, are the promises batch 1's résumé made still ones
   this folder keeps? If a later batch forces a change, **go back and fix the
   earlier files** — that is the whole point of one pass over the folder, and
   the cost of not doing it is an edition that contradicts itself.
6. `npm run render && npm run pdf && npm run manifest` — each batch becomes
   `AI-reviewed` by itself, from the file's existence; nothing is ticked by
   hand. Then read **every** rendered view with zero `katex-error` nodes and
   every PDF with no overfull lines, beside its transcription — not beside the
   facsimile; the transcription is this edition's source. Report which batches
   the pass covered and, if the folder was only partly transcribed, which it
   could not.

## What not to do

- **Transcribe.** If the transcription is missing or wrong, that is the
  transcribe skill's work; fix it there first, then re-derive.
- **Preserve an error out of respect.** Footnote it and state the truth.
- **Guess what an `\ill{}` hid.** If the interpretation needs the missing
  word, say in a footnote that the page is illegible there and that the
  reconstruction is ours.
- **Silently choose a convention.** Where the manuscript's notation forces a
  choice (folder 115's projection indices), choose, and footnote the choice.
- **Write English.** The pages are French and so is this. The one exception
  is `\keywords{}`, which is English on purpose: search keys, not prose.
- **Name the reader's level.** Write for them; do not address them as a class.
- **Let the summary become an abstract.** It orients; it does not compress
  the body into a paragraph.
- **Write one batch without having read the folder.** The scope is the whole
  point: a reading of batch 3 made blind to batch 4 guesses where the
  construction was going, and guesses wrong often enough to matter.
- **Merge the folder into one file.** The unit of *reading* is the folder; the
  unit of *output* stays `batch-NN.modern.tex`, because the site puts each file
  beside the facsimile pages it covers.
- **Let batch 1's résumé swallow the folder.** It orients over the folder in a
  page; it does not become the folder's article, leaving the later résumés
  nothing to say.
