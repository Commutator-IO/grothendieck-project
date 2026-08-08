---
name: summarize-grothendieck
description: Writes the licence-level summary of an already-transcribed batch of the Grothendieck fonds - one to two pages, in French, standing entirely on its own, explaining what the leaves are about, what problem is being attacked, what idea arrives, and where it leads. Use when someone asks to summarise or explain a transcribed batch ("summarize folder 115", "explain this batch to a student", "résume ce lot"), or after /transcribe-grothendieck has produced a batch-NN.fr.tex. Also covers revisions - a summary that assumes too much, or that cannot be read without the transcription.
---

# The summary of a batch, for a licence-level reader

## What this produces

For a batch already transcribed by `/transcribe-grothendieck`:

| File | Contents |
|---|---|
| `transcripts/<folder>/batch-NN.summary.tex` | One to two pages, **in French**, self-contained |

**Precondition: the transcription exists.** The summary derives from
`batch-NN.fr.tex` (and from `batch-NN.modern.tex` when it exists, which has
already done the work of naming things), never from the facsimile. If there
is no transcription, stop and say so.

## The reader

Someone who has finished a licence de mathématiques: groups, rings, some
topology. **Not** schemes, not topoi, not étale cohomology — and nothing may
assume them. Every notion beyond the licence is either explained by analogy
or not used.

The analogy is the main instrument. Folder 115's summary carries the whole of
Isbell duality on two: shadows cast from the left and from the right, and the
reflexivity of $V \to V^{**}$ in linear algebra. An analogy does not pretend
to rigour; it pretends to orientation, and says so.

## Four questions, in order

1. **De quoi ces feuillets parlent-ils**, en une phrase sans jargon ?
2. **Quel problème** Grothendieck attaque-t-il, et pourquoi ce problème se
   pose-t-il ?
3. **Quelle idée** apporte-t-il — par analogie s'il le faut, sans prétendre à
   la rigueur ?
4. **Où cela mène-t-il** dans son œuvre, et où le lecteur peut-il aller
   ensuite ? (Les noms modernes à chercher — profoncteur, dualité d'Isbell —
   rendent ce dernier point actionnable.)

One thing belongs here whenever the batch offers it, and it is often the most
valuable: **Grothendieck's reflection on his own practice.** These notebooks
are full of remarks on how a notion arrives, on what he called the attitude
of listening, on what understanding is. They need no mathematical background
at all, and they are why someone who will never do algebraic geometry might
read these pages. The summary is where they reach that reader.

## Form

- The body is a single `\begin{summary}…\end{summary}` — the whole document.
  No banner, no heading above it: the document *is* the summary, and the
  site's header already names it.
- **No apparatus, no leaf markers, no footnotes.** Uncertainty at the level
  of individual words is the transcription's business; if a doubt is large
  enough to matter at this altitude, say it in the prose (« la datation vient
  des versos »).
- **Self-contained.** If it cannot be read by itself, it is not a summary.
  The test: hand it to someone who will never open the transcription.
- Shared preamble, batch metadata, `\foldertitle` ending « — résumé pour la
  licence », pass header naming model and date.
- Concrete anchors stay: dates, the physical detail that dates the folder
  (listings IBM de juin 1982), leaf numbers in prose where they help.

## What not to do

- **Abridge the transcription.** A compressed transcription is not a summary;
  the summary answers the four questions and nothing else.
- **Assume the licence covers categories.** It does not; « catégorie » may be
  used, « topos » must be introduced as a name for something explained.
- **Inflate.** One to two pages. A summary that needs three is answering
  questions nobody at this level asked.
- **Write English.** The site's prose is English; the editions are French.
