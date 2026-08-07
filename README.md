# The mathematics Grothendieck wrote and never published

**A reading and transcription workbench for the 178 openly accessible folders of
the Alexandre Grothendieck fonds at the University of Montpellier — sixteen
thousand manuscript leaves, 1949 to 1991.**

→ **[grothendieck.commutator.io](https://grothendieck.commutator.io)**

## The point

Montpellier's inventory is complete and rigorous, and unreadable for anyone who
wants to *read*: folders filed by accession number, each titled with whatever
Grothendieck had pencilled on the cover, each a single PDF of between 4 MB and
270 MB.

This site does two things the inventory cannot. It offers four ways in — four
notebooks, each saying plainly whether its grouping is the archive's or ours.
And it puts the LaTeX transcription of a leaf **beside the leaf itself**, so
that scrolling the transcript turns the facsimile's pages. Every reading can be
checked against the handwriting it came from, on one screen, without a second
window.

## The site

| Page | Contents |
|---|---|
| [`/`](https://grothendieck.commutator.io/) | What the fonds is, how Grothendieck wrote, and the four notebooks |
| [`/topos/`](https://grothendieck.commutator.io/topos/) | **Cahier de Topos** — folders 19, 161-3, the categorical footing, SGA 4, the late stratified topos *(our grouping)* |
| [`/motifs/`](https://grothendieck.commutator.io/motifs/) | **Cahier de Motifs** — the inventory's *Théorie des motifs*, folders 10–18, 946 leaves *(the archive's grouping)* |
| [`/longue-marche/`](https://grothendieck.commutator.io/longue-marche/) | **La Longue Marche** — 1,584 leaves through Galois theory, plus the Teichmüller notes around it *(the archive's grouping)* |
| [`/tardifs/`](https://grothendieck.commutator.io/tardifs/) | **Cahiers tardifs** — *Vers une géométrie des formes* (1986) and *Dérivateurs* (1990–91) *(our grouping)* |
| [`/archive/`](https://grothendieck.commutator.io/archive/) | All 178 folders, in Grothendieck's filing order, searchable |
| [`/method/`](https://grothendieck.commutator.io/method/) | How he took notes, how transcription proceeds, what this site does not claim |

Two of the four notebooks reproduce an inventory group exactly; two are ours.
Each says which at the head of its page, because citing "the Cahier de Topos"
does not commit you to the same thing as citing folder 19.

## Nothing of the fonds is stored, anywhere

Not one leaf, not in the repository and not on disk. The facsimile pane streams
Montpellier's **own file**, fetched as you read it, and `.gitignore` refuses
`*.pdf` outright.

It cannot point at their server directly, and not for want of trying. Three
things were measured:

- **`X-Frame-Options: SAMEORIGIN`** — no other origin may embed their files. A
  probe iframe receives no document at all. Decisive on its own, and the one
  that would outlive every other fix.
- **Certificate expired 10 December 2025** — the identity is genuine (University
  of Montpellier, issued by GEANT), but the date has passed, so the load fails
  TLS verification and the click-through warning does not render inside a frame.
- **No CORS headers** — so a cross-origin `fetch` is barred too.

All three are enforced by the *browser* against the remote origin, and none
applies to a request made server-side. So a relay on this origin asks for the
file and passes the bytes straight through, verified byte-identical to the
source. In development that is a Vite middleware; in production, a Cloudflare
Worker.

**Range requests are what make it usable rather than a curiosity.** Montpellier
honours them, and the relay forwards them: opening leaf 221 of the 204 MB
second volume of the Long March moves **256 KB in 0.2 s**, not the volume.

### The production relay

`worker/source-relay.js`. A Worker cannot skip TLS verification — there is no
`rejectUnauthorized` in the runtime, and plain HTTP just `301`s to HTTPS — but
Cloudflare's *proxy* does not validate origin certificates in SSL/TLS mode
**Full** (as opposed to Full strict). So the Worker fetches through a proxied
hostname of ours pointed at Montpellier, and strips `X-Frame-Options` on the
way back. Two dashboard steps this expects:

1. A **proxied** CNAME `montpellier.commutator.io` → `grothendieck.umontpellier.fr`.
2. A configuration rule setting SSL/TLS to **Full** (not Full strict) for that
   hostname.

Then route the Worker at `grothendieck.commutator.io/source/*`. Until that is
in place the deployed site cannot show facsimiles, and the pane says so plainly
rather than offering a new tab — reading side by side is the point of the view,
and a tab that steals the window is not a lesser version of it.

### Mirroring, which reading no longer needs

Still worth having for transcription: handing a transcriber a twenty-leaf file
beats handing it a 204 MB volume and a page range.

```bash
npm run archive -- motives          # a whole notebook
npm run archive -- 19 --batches 1-3 # a beginning
```

Files land in `archives/`, outside `public/` so a build can never carry them,
and git-ignored so a commit never can either.

## Transcription

The [`transcrire-grothendieck`](skill/transcrire-grothendieck/SKILL.md) skill
transcribes one batch per pass and produces three editions of it: the French
transcription, an English translation of that transcription, and a summary for
a reader at undergraduate level. The translation and the summary are derived
from the transcription and never from the handwriting directly — two
independent readings of the same hand would diverge, and nothing would say
which was right.

```bash
npm run render      # transcripts/*.tex → the reading views the left pane shows
npm run pdf         # → the PDFs the download buttons offer
npm run manifest    # tell the site which files now exist
```

The `.tex` under `transcripts/` is the source of record and the only thing
versioned. HTML and PDF are derived, and rebuilt.

### The critical apparatus is the point

`transcripts/preamble/grothendieck.sty` defines seven macros, and they carry
the whole honesty of the exercise:

| Macro | Meaning |
|---|---|
| `\leaf{47}` | leaf 47 begins here — this is what turns the facsimile as you scroll |
| `\ill{}` | illegible; **never guessed** |
| `\uncertain{…}` | a reading offered, and flagged as doubtful |
| `\add{…}` | an editorial addition |
| `\struck{…}` | struck out by Grothendieck — a deletion often shows where the thought turned |
| `\note{…}` | the transcriber's note on the state of the leaf |
| `\marginal{…}` | a marginal note **of his**, distinct from the body |

A transcription that smooths over a gap has destroyed the only thing it was
for: an invented word that reads like the others is the worst possible outcome,
because nothing on the page distinguishes it from a sure reading.

`scripts/render.mjs` accepts a **restricted subset** of LaTeX, deliberately.
Anything outside it fails loudly rather than being silently flattened.
Mathematics is not converted at all — the delimiters pass through and KaTeX
typesets them, so screen and PDF come from one source.

## The repository

| Path | Role |
|---|---|
| `src/content/catalogue.ts` | The inventory — 178 folders, 22 groups — generated, never hand-edited |
| `src/content/books.json` | The four notebooks, read by the site *and* by the mirroring script |
| `src/components/FacsimilePane.tsx` | The right pane: the streamed folder PDF, resizable, page-anchored |
| `src/components/TranscriptPane.tsx` | The left pane: the transcript in its own frame, reporting the leaf being read |
| `scripts/catalogue.mjs` | Re-reads Montpellier's inventory into typed data |
| `scripts/archive.mjs` | Downloads and cuts folders into batches — for transcription, not for reading |
| `scripts/render.mjs` | LaTeX subset → the reading view, in ar5iv's stylesheet |
| `worker/source-relay.js` | The production relay: same job as the dev middleware, on the edge |
| `vite.config.ts` | Also relays `/source/*.pdf` from Montpellier in dev, forwarding range requests |

### Why the transcript pane is an iframe

It wears [ar5iv](https://github.com/dginev/ar5iv-css)'s stylesheet — the one
LaTeXML produces for arXiv articles, shared verbatim with
[tipe.commutator.io](https://tipe.commutator.io) — which claims `:root`, `body`
and a hundred generic element selectors. Dropped into a Tailwind page it would
fight everything; scoped by hand it would no longer be the same stylesheet. A
same-origin frame keeps it verbatim, and still lets the parent watch it scroll.

### Why pdf-lib and not poppler

These PDFs are LaTeX wrappers around a pool of scanned JPEGs, and
`pdfseparate` cannot prune that pool: it warns about recursive dictionaries and
gives up, so every extracted page carries all of the folder's images. Measured
on folder 19, a twenty-page batch came to **42 MB — larger than the 35 MB
source**. pdf-lib walks the object graph properly and gives **7.1 MB** for the
same twenty leaves.

## Running it

```bash
npm install && npm run dev
```

`pdfinfo` is needed to mirror folders (`brew install poppler`); a LaTeX engine
is needed only to compile transcript PDFs (`brew install --cask
mactex-no-gui`). Neither is needed to browse the inventory.

## Credit and limits

The facsimiles are from the **fonds Alexandre Grothendieck**, University of
Montpellier — given by Jean Malgoire, catalogued in 2015–2016 by Hélène
Rodriguez and Frédéric Troilo under the direction of Sophie Dikoff. Of the
fonds' ~28,000 leaves, about 18,000 may be circulated; third-party
correspondence cannot be, without permission.

No transcription here is an edition. A machine pass over seventy-year-old
handwriting produces a reading, checkable against the facsimile on the same
screen. That is its whole value, and its whole claim.
