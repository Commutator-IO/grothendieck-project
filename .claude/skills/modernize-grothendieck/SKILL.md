---
name: modernize-grothendieck
description: Produces the modernised reading of an already-transcribed batch of the Grothendieck fonds — a summary (« Résumé ») that orients a reader new to the subject, then the mathematics in current notation and current names, in French, mathematically correct as it stands, with footnotes carrying everything the transcription's critical apparatus carried. Use when someone asks to modernise, clean up, reinterpret, restate, summarise or explain a transcribed batch ("modernize folder 115", "give the modern reading", "explain this batch"), or after /transcribe-grothendieck has produced a batch-NN.fr.tex. Also covers revisions - tightening a statement, correcting a variance, rewriting a summary that assumes too much.
model: claude-fable-5
---

# The modernised reading of a batch


**Runs on Fable 5.** The frontmatter pins it, so invoking this skill switches
the model for the turn whatever the session was set to.

The standard this edition is held to — correct as it stands, with the four
failure modes checked — is a reasoning standard, and it was calibrated against
Fable 5 on folder 115. Pinning the model keeps that calibration meaningful: a
reading produced under a different model is not comparable to the ones already
in the repository, and the header would say so only after the fact.

## What this produces

For a batch already transcribed by `/transcribe-grothendieck`:

| File | Contents |
|---|---|
| `transcripts/<folder>/batch-NN.modern.tex` | A summary, then the mathematics in today's notation and names — **in French**, like the leaves |

It is an **interpretation, not a transcription**: it reorganises by argument,
states what the manuscript leaves implicit, and reads continuously, the way a
survey would. Where it and the transcription disagree in substance, the
transcription is the record. Anyone citing Grothendieck cites
`batch-NN.fr.tex`; this edition is for reading.

**Precondition: the transcription exists.** This skill reads
`batch-NN.fr.tex`, never the facsimile. Two independent readings of one hand
diverge, and nothing would say which is right. If there is no transcription,
stop and say so — do not transcribe on the way through.

## The summary

The document opens with one — `\section*{Résumé}`, before any mathematics —
and it is the only part of the project written for someone who has not met the
subject. One page, perhaps two. Its job is orientation, and it answers four
questions in order:

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
summary carries no `\leaf{}` either.

## The standard: correct as it stands

This is the one edition where fidelity to the leaf is not the highest duty.
It is held to being **mathematically correct as written**. Where the
manuscript is loose, elliptical or wrong, the modernised reading states what
is *true*, and a footnote says what the leaf has. Reproducing an error
faithfully, in an edition whose whole promise is that it can be read as
mathematics, launders the error through the appearance of a modern text.

Four failure modes, each hit on a real batch (folder 115); check for all four:

- **Variances.** These notes are about two-sided constructions, and variance
  is where a plausible-looking modernisation does the most damage. A kernel
  contravariant in both arguments induces a *dual* adjunction, not an
  adjunction, and is not a profunctor — calling it one is false, not loose.
  Check every functor's variance before naming what it is.
- **Implicit hypotheses.** If a universal property needs $M$ cocomplète and
  the leaf does not say so, say so — and footnote that it was supplied.
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
tell what was on the leaf and what is ours; footnotes are simply a better
place to say it in a text meant to be read continuously.

**No `\leaf{}` markers either.** This edition groups by argument, not by
sheet, so leaf anchors would be false — and the site deliberately keeps the
facsimile still while it is open. Refer to leaves in prose (« le feuillet 5
dispose… ») where it helps the reader find their place.

## Language and form

**In French.** The leaves are in French, the notions were thought in French,
and the modernised reading has no reason to change language. Today's *names*
are used in their French forms: dualité d'Isbell, complétion de Cauchy,
enveloppe de Karoubi, cofin, curryfier.

The document takes the shared preamble (`\input{../preamble/grothendieck}`),
the batch metadata (`\folder`, `\batch`, `\leaves`, `\foldertitle` ending
« — lecture modernisée »), and the pass header comment naming the model and
date. Structure with `\section*` and `\subsection*` following the argument.
Stay inside the LaTeX subset of the transcribe skill — the renderer raises on
anything else — plus `\footnote{}`, which the reading view renders as
numbered notes with backlinks.

Diagrams follow the transcribe skill's tikz-cd rules, with one addition
earned on folder 115: **compound directions exist** (`\arrow[ul]`,
`\arrow[dd]`), and a radial diagram — a wheel with a centre — is drawn by
putting every arrow on the centre cell, pointing outward. Check the
arrowheads against what the transcription records: a wheel transcribed as
radiating from its centre asserts different equivalences than a rim of
arrows, and the renderer will faithfully draw whichever you write.

## The sequence

1. Read `batch-NN.fr.tex` in full, twice: once for the mathematics, once
   listing every `\uncertain{}`, `\ill{}` and `\note{}` — that list is the
   skeleton of the footnotes.
2. Identify the spine — the construction the batch is actually building — and
   organise the sections around it, not around the leaf order.
3. Write the body, holding to the standard above. Every departure from the
   leaf gets a footnote at the point of departure.
4. Write the summary **last**, when you know what the batch turned out to be
   about. Written first it describes what you expected to find.
5. `npm run render && npm run pdf && npm run manifest` — the batch becomes
   `AI-reviewed` by itself, from the file's existence; nothing is ticked by
   hand. Then read the
   rendered view with zero `katex-error` nodes and the PDF with no overfull
   lines, beside the transcription — not beside the facsimile; the
   transcription is this edition's source.

## What not to do

- **Transcribe.** If the transcription is missing or wrong, that is the
  transcribe skill's work; fix it there first, then re-derive.
- **Preserve an error out of respect.** Footnote it and state the truth.
- **Guess what an `\ill{}` hid.** If the interpretation needs the missing
  word, say in a footnote that the leaf is illegible there and that the
  reconstruction is ours.
- **Silently choose a convention.** Where the manuscript's notation forces a
  choice (folder 115's projection indices), choose, and footnote the choice.
- **Write English.** The leaves are French and so is this.
- **Name the reader's level.** Write for them; do not address them as a class.
- **Let the summary become an abstract.** It orients; it does not compress
  the body into a paragraph.
