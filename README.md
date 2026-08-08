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

This site does two things the inventory cannot. It offers five ways in — five
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
| [`/notes-dispersees/`](https://grothendieck.commutator.io/notes-dispersees/) | **Notes techniques dispersées** — the 35 folders belonging to no work, 1953–1984 *(our grouping)* |
| [`/method/`](https://grothendieck.commutator.io/method/) | How he took notes, how transcription proceeds, what this site does not claim |

Two of the five notebooks reproduce an inventory group exactly; three are ours.
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
source. In development that is a Vite middleware; in production, a small Node
service — see below for why it cannot be a Cloudflare Worker.

**Range requests are what make it usable rather than a curiosity.** Montpellier
honours them, and the relay forwards them: opening leaf 221 of the 204 MB
second volume of the Long March moves **256 KB in 0.2 s**, not the volume.

### The production relay

[`relay/`](relay/README.md) — one file, no dependencies, nothing stored.

A Cloudflare Worker cannot do this job: there is no `rejectUnauthorized` in
that runtime, so its `fetch()` throws on the expired certificate. The usual way
round is Cloudflare's *proxy* in SSL/TLS mode Full, which tolerates a bad origin
certificate — but that needs the zone on Cloudflare, and `commutator.io` is on
Google Cloud DNS.

**And no DNS record can substitute, on any provider.** DNS points at addresses;
it does not terminate TLS. A CNAME to Montpellier would send the browser
straight there, to a certificate now both expired *and* issued for the wrong
hostname.

Node has `rejectUnauthorized`, so the relay needs no DNS arrangement at all:
deploy the container anywhere, take the hostname the platform gives you — it
already has a valid certificate — and set the repository variable `RELAY_URL`
to it. Cross-origin is fine; `frame-ancestors` is what governs framing, and the
relay sets it to this site alone.

Left unset, the deployed site has no facsimiles and every batch says so plainly
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

The [`transcribe-grothendieck`](.claude/skills/transcribe-grothendieck/SKILL.md) skill —
installed as a project skill, so `/transcribe-grothendieck` works in this
repository —
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
| `relay/server.mjs` | The production relay: same job as the dev middleware, deployable |
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
