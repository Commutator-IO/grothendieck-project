# Rights

This repository holds two kinds of thing, and one licence cannot honestly
cover both. Read this before reusing anything from it.

**Nobody here is a lawyer, and this file is not legal advice.** It states what
this project believes its own position to be, so that anyone reusing the work
can see the ground they are standing on rather than assume it.

## The code — CC0 1.0

`LICENSE` is CC0 1.0, and it covers **the parts of this repository that are
ours to give**:

- `scripts/` — the mirroring, tiling, rendering, TEI, PDF and manifest tooling
- `src/`, `relay/`, `public/vendor/`, the build configuration — the site and
  the facsimile relay
- `src/content/catalogue.ts` and `src/content/books.json` as *arrangements* —
  the data is read from Montpellier's inventory and the facts in it are theirs

Take it, fork it, use it without asking. That was the point of choosing CC0
and it is unaffected by everything below.

## The transcriptions — not ours to license

**`transcripts/` is not covered by CC0, and this project could not place it
there even if it wanted to.**

Every file under `transcripts/` reproduces or restates the contents of
manuscripts by Alexandre Grothendieck. He died on 13 November 2014, so under
French law the economic rights in those manuscripts run until **the end of
2084**, and they are held by his heirs. The moral rights — in particular the
*droit de divulgation*, the right to decide whether an unpublished work is
disclosed at all, and the *droit au respect de l'œuvre* — are perpetual and
inalienable under French law.

That the LaTeX was typed here, and that the reading was made by a machine,
does not change what the file contains. A transcription is a reproduction.

So:

- **This project claims no rights over the contents of the manuscripts**, and
  grants none.
- **It does not purport to authorise anyone else to reproduce them.** If you
  want to republish material from `transcripts/`, the permission you need is
  not ours to give, and you should seek it from the rights holders and from
  the University of Montpellier.
- What this project does claim, and places under CC0 along with the code, is
  the **editorial apparatus as a method** — the conventions, the macros, the
  structure of the files. Not the text they carry.

An earlier version of this repository licensed everything under CC0 and
described the material as "readings of a fonds nobody owns". That was wrong,
it is withdrawn, and this file replaces it.

## The facsimiles — Montpellier's

No facsimile is redistributed here. `archives/` is git-ignored; the reading
pane streams each folder's PDF from the University of Montpellier as you read
it, so the image you see is served by them and not by us.

The fonds Alexandre Grothendieck was given to the University of Montpellier by
Jean Malgoire and catalogued in 2015–2016 by Hélène Rodriguez and Frédéric
Troilo under the direction of Sophie Dikoff. Of its ~28,000 pages, about
18,000 may be circulated; third-party correspondence may not, without
permission. Every shelfmark, page number and dating on this site is theirs.

## Status of this edition

Every transcription carries `\watermark{Édition de démonstration}`, printed in
the reading view and across every page of the PDF. None of it is a scholarly
edition; none of it has been checked against the leaves by a person unless the
batch says so. Where an established edition exists — Maltsiniotis' *Pursuing
Stacks* and *Dérivateurs*, among others — it is marked on the archive page and
should be used instead of anything here.

**If the University of Montpellier or the rights holders ask for this material
to be taken down, it will be taken down.** No argument, no delay. The contact
for the fonds is the Service des Archives,
[dcsph-archives@umontpellier.fr](mailto:dcsph-archives@umontpellier.fr).

## Open questions, and what was decided

**No part of `transcripts/` will be deposited on Zenodo or in any archive that
mints a permanent identifier.** The project stays on GitHub and on the site,
both of which can be taken down at any time; that is what the takedown
commitment above relies on, and a DOI would break it. Weights of any model
trained on these transcriptions fall under the same rule.

What the fonds' open-access designation permits, and who holds the right to
authorise derivative works from it, have not been settled with the
University. The question was put in writing to the Service des Archives and
has not been answered yet. Until it is, this project reads the open-access
designation as covering a watermarked, retractable demonstration edition,
and defers to any request for removal. The reasoning, and each question it
leaves open, is in
[issue #23](https://github.com/Commutator-IO/grothendieck-project/issues/23).
