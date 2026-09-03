---
name: modernize-grothendieck
description: Produces the modernised reading of an already-transcribed folder of the Grothendieck fonds — taken whole, all its batches in one pass, as a single document for the shelfmark — a summary (« Résumé ») that orients a reader new to the subject, then the mathematics in current notation and current names, in French, mathematically correct as it stands, with footnotes carrying everything the transcription's critical apparatus carried. Use when someone asks to modernise, clean up, reinterpret, restate, summarise or explain a transcribed folder ("modernize folder 115", "give the modern reading", "explain these pages"), or after /transcribe-grothendieck has transcribed a folder's batches. Also covers revisions - tightening a statement, correcting a variance, rewriting a summary that assumes too much.
---

# The modernised reading of a folder


**Runs on Fable 5.1 or Opus 5, and on nothing else.** The frontmatter used to
pin Opus 5, which made the choice automatic; the pin is gone since 2026-09-03,
when Fable 5.1 was admitted, and what replaces it is a check you make yourself
before reading a line of the transcription:

- **Fable 5.1 (`claude-fable-5-1`)** — permitted, and the default for a
  session already running on it.
- **Opus 5 (`claude-opus-5`)** — permitted; what every reading in the
  repository before 2026-09-03 was produced with.
- **Anything else** — stop, say which model the session is on, and do not
  write. A reading on a model nobody chose has a provenance nobody can vouch
  for.

One thing the pin used to carry has to be said plainly now that it is gone.
The standard this edition is held to — correct as it stands, with the four
failure modes checked — is a reasoning standard, and folder 115's reading is
what it was calibrated against. That reading was made on Opus 5, and its
header says so. A reading made on Fable 5.1 is held to the same standard but
is **not measured against that reference**: the two models were never
compared on this task, and nothing in this repository says how they differ.
The header records which one ran, and that is the only claim the file makes
about it.

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

and it writes, in that one pass, **one file for the whole shelfmark**:

| File | Contents |
|---|---|
| `transcripts/<folder>/<folder>.modern.tex` | one summary, then the mathematics in today's notation and names — **in French**, like the pages |

One file, not one per batch, and the reason is the same reason the unit is the
folder. An argument that runs from page 24 to page 190 has to be *written* in
one place to be *read* in one place: split across eleven files, folder 29's
two best observations — that the question its 1967 typescript poses at page 24
is answered at page 190, and that the pair `(C, s)` it defines at page 12 comes
back at page 201 as a presentation of the object it approximated — had to be
asserted eleven times and could be read nowhere. Every other folder of this
project is a single file; 29 was merged into one after being written the other
way, and the merge is what made those two facts sayable once.

The site is built for this and not merely tolerant of it. `scripts/manifest.mjs`
keys folder-wide readings by folder rather than by batch, and says why in its
own comment: filed under `#1` — the only batch key a `batch-01.modern.tex`
could produce — a folder-wide reading made the archive page report 161-3 as
"1/3 modernised" when all 54 of its pages had been read, and left the
Modernised toggle dead on batches 2 and 3. Keyed by folder, the one file is
offered against *every* batch of the folder, which is what it actually covers.

**A batch range is not an output unit.** `/modernize-grothendieck 151 3-4` may
be given when only part of a folder is being revised; it narrows what gets
rewritten inside the one file, never what gets written. And even then, **read
the folder's transcriptions whole first**.

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

**The file opens with one** — `\section*{Résumé}`, before any mathematics —
and it is the only part of the project written for someone who has not met the
subject. One page, perhaps two. **One per folder**, not one per batch: there
is one document, so there is one summary, and it orients over the whole
shelfmark — what the folder is about, where its argument is going, what it
will have built by the last page.

For a folder of any size, follow the résumé with a short section that lays out
the **spine and the conventions** — the stations of the argument with their
page ranges, the notation fixed for the whole document, and what the folder
announces but never establishes. Folder 19 does this under « Conventions,
valables pour tout le dossier » and folder 29 under « Le fil du dossier, et
l'ordre des feuillets ». It is what replaces the orientation that per-batch
summaries used to repeat, and on a two-hundred-page folder it is the only
navigation a reader has.

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

One thing belongs here whenever the folder offers it, and it is often the most
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

**In English** — they are search keys, not prose, and the literature they
point into is English — naming the modern vocabulary under which what the
folder builds is known today. They are the natural sharpening of the résumé's
fourth question (*quels noms modernes chercher ensuite*), so write them when
the résumé is written, last.

**One line for the folder**, since there is one file. Three to six terms for a
small shelfmark; a two-hundred-page folder will carry many more — 29 carries
fifty-five — but the discipline is the same one that a per-batch list used to
enforce by construction: **partition the folder's vocabulary rather than repeat
it**. A term earned by the opening sections is not re-listed for a later one,
and no term goes in that some section does not actually build.

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

Four failure modes, each hit on a real folder (115); check for all four:

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

The document takes the shared preamble (`\input{../preamble/grothendieck}`)
and the folder's metadata:

- `\folder` — the shelfmark;
- `\pages{first}{last}` — the **whole** span, first page of the first batch to
  last of the last;
- `\dating` — copied unchanged from the transcriptions, since it is
  Montpellier's claim and not a reading;
- `\foldertitle` — the inventory's title, ending
  « — lecture modernisée du dossier entier »;
- **no `\batch`.** The preamble is built for this: with `\batch` absent it
  drops the « (lot N) » from the title block rather than printing a number
  that would be false. A `\batch` line in this edition is a bug, and it is
  also what makes the manifest file the reading under `#N` instead of under
  the folder.

Then the pass header comment, naming the model and date, in the form the
existing files use — `% Pass: Fable 5.1 (claude-fable-5-1), <date> — first
pass, unchecked against the pages by a human.` — with the model that actually
ran, never the one a reference reading was made on. If the session is on a
model the list above does not admit, stop rather than write a header for it.
Use the header for what a reader cannot get from the body: the
notation fixed for the folder, the substantive departures from the pages with
their page numbers, and anything the folder announces and never establishes.

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

**Read the folder before writing any of it.** Every step runs once, over the
whole shelfmark — there is one document, so there is one pass.

1. Read **every** `transcripts/<folder>/batch-NN.fr.tex`, in order, in full,
   twice: once for the mathematics, once listing every `\uncertain{}`,
   `\ill{}` and `\note{}` — that list is the skeleton of the footnotes. Read
   the transcriptions' header comments too: they record what the reader of the
   hand found hard, which is where this edition is most likely to go wrong.
2. Identify the **folder's spine** — the construction the folder as a whole is
   building — and only then decide where each stretch of pages sits on it.
   Write the plan down before writing prose: what each stretch contributes to
   the spine and what it may therefore assume. Skipping this wastes the
   folder-wide read, and it is what the spine section after the résumé is
   written from.
   A construction that outlives a batch boundary gets **one** name, one
   notation and one convention for the whole document, fixed here; changing
   notation mid-folder is the failure this scope exists to prevent. Where two
   objects of the folder share a name — folder 29 calls both its 1967
   auxiliary datum and its late champ a « donnée/domaine de ramification » —
   fix the distinction here and state it in the spine section, because a
   reader meeting the second will otherwise read it as the first.
   Where the folder restarts on itself — the *moutures* of one chapter — say
   so on the spine and keep them distinct. A restart is not a repetition to be
   merged; that difference is content.
3. Write the body, in page order, holding to the standard above. Every
   departure from the page gets a footnote at the point of departure. Where a
   construction begun earlier is continued, **cite the earlier section by its
   pages** — « la donnée kummérienne des pages 19 et 20 » — and recall in one
   sentence what it is. Never cite a batch: the batch is a unit of
   transcription and has no existence in this document.
4. Write the summary **last**, when you know what the folder turned out to be
   about. Written first it describes what you expected to find. Close it with
   the `\keywords{}` line — the folder's tags come from nowhere else.
5. Before finishing, re-read against the plan from step 2: is the notation the
   folder's throughout, are the promises the résumé makes ones the document
   keeps, does every section the spine names exist? A late section that forces
   a change means **going back and fixing the earlier ones** — cheap in one
   file, and the reason the scope is what it is.
6. `npm run render && npm run pdf && npm run manifest` — the folder becomes
   `AI-reviewed` from the file's existence; nothing is ticked by hand. Confirm
   the manifest keys the reading **by folder** and not under `#1`: the count
   of folders "read whole" should go up by one, and no batch entry should
   carry a `modern` edition. Then read the rendered view with zero
   `katex-error` nodes and the PDF with no overfull lines, beside the
   transcriptions — not beside the facsimile; the transcription is this
   edition's source.

   Two checks worth running on a long folder, both cheap and both of which
   caught something real on 29: every transcribed `\page{N}` should fall
   inside some `\pagerange{}`, and every named result of the transcriptions
   (Lemme, Proposition, Corollaire, Exemple, Remarque) should be reachable in
   the reading. The second is what surfaces a statement the folder announces
   and never makes — an absence this edition is supposed to record, not step
   over.

   Report what the pass covered and, if the folder was only partly
   transcribed, what it could not.

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
- **Start writing before having read the folder.** The scope is the whole
  point: a section written blind to the pages after it guesses where the
  construction was going, and guesses wrong often enough to matter. On folder
  29 the last thirty pages answer a question the first forty ask; written in
  page order without having read to the end, neither half can say so.
- **Split the folder across one file per batch.** The unit of reading and the
  unit of output are both the folder. The manifest keys folder-wide readings by
  folder and offers them against every batch, so nothing is lost beside the
  facsimile — and an argument that crosses a batch boundary can be written once
  instead of being asserted at each crossing.
- **Let the résumé swallow the folder.** It orients in a page, perhaps two; it
  does not become the folder's article. On a long shelfmark the temptation is
  real, because there is now only one summary and everything wants to go in it.
  What the résumé cannot hold goes in the spine section under it, or in the
  body where it belongs.
- **Write a section that cites a batch.** Batches are units of transcription.
  In this document a cross-reference is to pages — « le théorème des pages 87 à
  97 » — because that is what a reader of the facsimile can follow and what
  survives a re-batching of the transcription.
