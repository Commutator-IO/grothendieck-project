---
name: transcribe-bourbaki
description: Transcribes a document of the Bourbaki archive (Archives Henri Poincaré, archives-bourbaki.ahp-numerique.fr) — mostly typescripts: numbered rédactions, letters, congress reports — into clean LaTeX with the same critical apparatus as the Grothendieck fonds, keeping apart what the machine typed and what a hand added. Use whenever someone asks to transcribe, read or put into LaTeX a Bourbaki rédaction or document (« rédaction n° 433 », an archive item number, a congress report), or the documents ringed in red on the Bourbaki tab (#50). The transcriptions stay local in transcripts-bourbaki/ and are never committed until the AHP and the ACNB agree.
---

# Transcribing a document of the Bourbaki archive

**Nothing this skill produces leaves the machine.** The documents belong to the
Association des Collaborateurs de Nicolas Bourbaki and are published by the
Archives Henri Poincaré. Under the rule that governs the fonds (BnF,
2026-09-29), no transcription goes online without their authorisation (#50).
Every file is written under `transcripts-bourbaki/`, which `.gitignore`
excludes except for its preamble. Never `git add -f` one, never paste one into
an issue, a PR, a commit message or the site, never quote more than a few
words of one in chat.

**Runs on Opus 5.5 or Opus 5, and on nothing else**, the same rule as
`/transcribe-grothendieck`, and the header records which model read the pages.

## What these documents are

**Typescripts, mostly.** A rédaction is a stencilled or carbon copy of a
typed text, circulated to the members before a congress; the congress reports
(« La Tribu ») and circulars likewise. That changes the work in three ways
from the fonds:

1. **The reading is easier and the pass can be longer.** Typed text does not
   degrade attention as handwriting does. A batch is **up to 40 PDF pages** of
   clean typescript (20 if the copy is faint, heavily annotated, or dense with
   formulas typed in by hand). Still one batch per pass.
2. **The formulas are the hard part.** Typewriters had no mathematical signs:
   symbols were added by hand in the blanks (∈, ∪, Greek letters, arrows,
   exponents), or approximated (« -> », « |-> », underlined letters for
   bold or for named sets, a double-struck letter written as an underlined
   capital). Set what the mathematics means in TeX and keep the convention
   once in the header: underlined `P` for the power set is `\underline{P}`,
   underlined `Q`, `N`, `Z` stay `\underline{Q}`… as typed, never silently
   turned into `\mathbb`.
3. **Two layers, typed and handwritten, kept apart.** Everything typed —
   including typed interlinear insertions and x-ed-out corrections at the
   machine (not reproduced, unless the struck words read and matter) — is
   running text. Everything in ink or pencil is apparatus: `\add{}` for a
   handwritten insertion into the line, `\struck{}` for a typed word struck by
   hand, `\marginal{}` for a note in the margin. **Whose hand** must be said,
   in a `\note{}` the first time: a member's correction, a reader's query, the
   typist's own fix. Do not assume Grothendieck: the copies come from members'
   papers (Cartier, Delsarte, Cartan, Samuel…), and the hand is usually the
   owner's. Name a hand only on evidence (a signature, initials, a hand known
   from the same fonds); otherwise « une main non identifiée ».

**What is not transcribed:**

- the archive's cover sheet (cote, title, page and leaf counts);
- the archive's pencilled cote and page numbers, and the typist's running heads
  (« - 2 - », « n° 433 »): `\page{}` takes the PDF page, which the archive
  pencils top right; say once in the header how the two paginations relate;
- in a congress report, nothing is cut: the report is the document. But a
  **skim** (#50, priority 3) is not this skill: it records passages about
  Grothendieck in a few words and transcribes nothing.

**Letters.** A rédaction may be letters between members (n° 433: Samuel to
Grothendieck and back). Letters to and from him are transcribed in full;
private addresses are withheld, as in the fonds.

## The sequence

1. **Get the PDF.** The archive's item number (`items/show/<id>`) gives the
   file through the public API:
   ```bash
   curl -s "https://archives-bourbaki.ahp-numerique.fr/api/files?item=<id>" | python3 -c "import json,sys;print(json.load(sys.stdin)[0]['file_urls']['original'])"
   curl -s -o archives/bourbaki/<id>.pdf <that url>
   ```
   `archives/` is ignored and never served. The PDFs have no text layer; do
   not run OCR. Read page images: `pdftoppm -r 110 -gray -png`, and zoom to
   200–300 dpi on formulas and handwriting.
2. **Read the batch through once, producing nothing**: which pages are text,
   which hands are present, the typing conventions for symbols, the internal
   references (« rédaction 424, § 5 »), which are kept as typed.
3. **Transcribe**, by the rules of `/transcribe-grothendieck` « Transcribe the
   mathematics » and its permitted LaTeX subset (read that section), with the
   two-layer convention above. The file opens like this:

   ```latex
   % Transcription — Archives Bourbaki, rédaction n° <N>, « <title> », pages a-b.
   % From the facsimile https://archives-bourbaki.ahp-numerique.fr/items/show/<id>
   % (<fonds and cote as the archive gives them>), read on archives/bourbaki/<id>.pdf.
   % Not for distribution until the AHP / ACNB agree (#50).
   % Pass: Opus 5.5 (claude-opus-5-5), <date> — first pass, unchecked against the pages by a human.
   % <pagination, hands, symbol conventions>
   \documentclass[11pt,a4paper]{article}
   \input{../preamble/bourbaki}

   \redaction{<N>}
   \batch{1}
   \pages{a}{b}
   \foldertitle{<the archive's title, verbatim>}
   \dating{<the archive's date, verbatim>}
   \watermark{Édition de démonstration}
   ```

   The file goes to `transcripts-bourbaki/<N>/batch-NN.fr.tex` (`<N>` the
   rédaction number, or `item-<id>` for an unnumbered document). Mind the
   `Revised` rule: never write a macro name inside a `% Revised` line.
4. **Check**: `cd transcripts-bourbaki/<N> && tectonic batch-NN.fr.tex` — no
   error, no overfull line — then read the PDF beside the facsimile. Leave the
   PDF where it is (ignored).

Close by telling the user the model, the pages read, what the document is,
the hands found, and the doubtful readings. Add what the next pass should know
about the typing conventions to `references/conventions.md`.

## What not to do

- **Commit, push, upload or quote a transcription.**
- **Attribute a hand to Grothendieck without evidence.**
- **Normalise the typist's symbols silently** (an underlined Q is not `\mathbb{Q}`
  without a note saying the convention).
- **Transcribe the archive's own sheets** or its pencilled numbering.
- **Extend the LaTeX subset.** It is the fonds'; `scripts/render.mjs` defines it.

`transcripts-bourbaki/433/batch-01.fr.tex` is the reference pass: two typed
letters, 1965, every convention above in use.
