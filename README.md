# The mathematics Grothendieck wrote and never published

**A reading and transcription workbench for the 178 openly accessible folders of
the Alexandre Grothendieck fonds at the University of Montpellier — sixteen
thousand manuscript pages, 1949 to 1991.**

→ **[grothendieck.commutator.io](https://grothendieck.commutator.io)**

## The point

Montpellier's inventory is complete and rigorous, and unreadable for anyone who
wants to *read*: folders filed by accession number, each titled with whatever
Grothendieck had pencilled on the cover, each a single PDF of between 4 MB and
270 MB.

This site does two things the inventory cannot. It offers five ways in — five
notebooks, each saying plainly whether its grouping is the archive's or ours.
And it puts the LaTeX transcription of a page **beside the page itself**, so
that scrolling the transcript turns the facsimile's pages. Every reading can be
checked against the handwriting it came from, on one screen, without a second
window.

## The site

| Page | Contents |
|---|---|
| [`/`](https://grothendieck.commutator.io/) | What the fonds is, how Grothendieck wrote, and the five notebooks |
| [`/topos/`](https://grothendieck.commutator.io/topos/) | **Cahier de Topos** — folders 19, 161-3, the categorical footing, SGA 4, the late stratified topos *(our grouping)* |
| [`/motifs/`](https://grothendieck.commutator.io/motifs/) | **Cahier de Motifs** — the inventory's *Théorie des motifs*, folders 10–18, 946 pages *(the archive's grouping)* |
| [`/longue-marche/`](https://grothendieck.commutator.io/longue-marche/) | **La Longue Marche** — 1,584 pages through Galois theory, plus the Teichmüller notes around it *(the archive's grouping)* |
| [`/tardifs/`](https://grothendieck.commutator.io/tardifs/) | **Cahiers tardifs** — *Vers une géométrie des formes* (1986) and *Dérivateurs* (1990–91) *(our grouping)* |
| [`/archive/`](https://grothendieck.commutator.io/archive/) | All 178 folders, in Grothendieck's filing order, searchable |
| [`/notes-dispersees/`](https://grothendieck.commutator.io/notes-dispersees/) | **Notes techniques dispersées** — the 35 folders belonging to no work, 1953–1984 *(our grouping)* |
| [`/method/`](https://grothendieck.commutator.io/method/) | How he took notes, how transcription proceeds, what this site does not claim |

Two of the five notebooks reproduce an inventory group exactly; three are ours.
Each says which at the head of its page, because citing "the Cahier de Topos"
does not commit you to the same thing as citing folder 19.

## Nothing of the fonds is stored, anywhere

Not one page, not in the repository and not on disk. The facsimile pane streams
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
service — see below for why it has to be Node.

**Range requests are what make it usable rather than a curiosity.** Montpellier
honours them, and the relay forwards them: opening page 221 of the 204 MB
second volume of the Long March moves **256 KB in 0.2 s**, not the volume.

### The production relay

[`relay/`](relay/README.md) — one file, no dependencies, nothing stored.

**It has to be a real Node process.** Skipping verification of the expired
certificate needs `rejectUnauthorized`, which exists in Node and in no
edge or serverless V8 runtime — their `fetch()` simply throws. That one
requirement rules out most of the cheap hosting options, and it is worth
knowing before reaching for one.

**And no DNS record can substitute, on any provider.** DNS points at addresses;
it does not terminate TLS. A CNAME to Montpellier would send the browser
straight there, to a certificate now both expired *and* issued for the wrong
hostname — and its `X-Frame-Options` would arrive untouched, so the pane would
stay blank either way.

Node has `rejectUnauthorized`, so the relay needs no DNS arrangement at all:
deploy the container anywhere, take the hostname the platform gives you — it
already has a valid certificate — and set the repository variable `RELAY_URL`
to it. Cross-origin is fine; `frame-ancestors` is what governs framing, and the
relay sets it to this site alone.

Left unset, the deployed site has no facsimiles and every batch says so plainly
rather than offering a new tab — reading side by side is the point of the view,
and a tab that steals the window is not a lesser version of it.

### Mirroring, which reading no longer needs

Still worth having for transcription: handing a transcriber a twenty-page file
beats handing it a 204 MB volume and a page range.

```bash
npm run archive -- motives          # a whole notebook
npm run archive -- 19 --batches 1-3 # a beginning
```

Files land in `archives/`, outside `public/` so a build can never carry them,
and git-ignored so a commit never can either.

## Transcription

Two editions, one skill each, run in order — plus a third skill for the
folder's tags. All installed under `.claude/skills/`. Modernisation and tagging
pin Fable 5 in their frontmatter; transcription no longer does, so that Opus 5
can be measured against it on a hard hand — it accepts those two models, refuses
any other, and records in each file's header the one that read the pages, so
that a batch's provenance stays a fact about the file rather than about whichever
model happened to be selected:

| Skill | Produces |
|---|---|
| [`/transcribe-grothendieck`](.claude/skills/transcribe-grothendieck/SKILL.md) | the transcription — the pages as written, with the critical apparatus |
| [`/modernize-grothendieck`](.claude/skills/modernize-grothendieck/SKILL.md) | the modernised reading — a résumé, then current notation and names, footnotes instead of apparatus |
| [`/tag-grothendieck`](.claude/skills/tag-grothendieck/SKILL.md) | the folder's tags — the `\keywords{}` line closing the résumé |

Both editions are in French — Grothendieck's language, and the language the
notions were thought in. The modernised reading works from the transcription,
never from the handwriting directly: two independent readings of the same hand
would diverge, and nothing would say which was right.

The modernised reading is the one allowed to depart from the page, and is held
to being **correct as it stands**: where the manuscript is loose it states what
is true and footnotes what the page has. It opens with a `Résumé` written for
someone who has not met the subject, and closes that résumé with three to six
English keywords — the modern vocabulary to search under. Those keywords are
the **single source** of the folder's tags: `npm run manifest` extracts them,
and the archive page's search matches on them. There is deliberately no tags
file, so no tag can describe content nobody has read.

Every batch also carries a **Report a reading** button, in the reading view and
on each transcribed folder's card, opening a prefilled GitHub issue with the
shelfmark, the batch and the page currently on screen. Everything here is
first-pass machine work; corrections are the point of publishing it.

```bash
npm run render      # transcripts/*.tex → the reading views the left pane shows
npm run pdf         # → the PDFs the download buttons offer
npm run manifest    # tell the site which files now exist
```

The `.tex` under `transcripts/` is the source of record and the only thing
versioned. HTML and PDF are derived, and rebuilt.

**Five batches are transcribed so far**, all under Fable 5: folder 115
(fourteen pages — functorial correspondences and the duality of topoi) and
folder 161-1 (nineteen pages — adjoint functors, the free symmetric monoidal
category, theories, and a half-page sketch of Giraud's theorem) on 8 August
2026, then the three batches of folder 135 (fifty-eight pages, the whole folder
— Gr-categories, their classification by a class in $H^3$, and the Picard
envelope; the last thirteen pages are a manuscript in English) on 9 and 15
August. Two of the five also have their modernised reading: 161-1 under Fable 5,
115 under Opus 5. None has been checked page by page by a person. `/method/`
prices the two steps separately, from the passes themselves: transcription
carries almost all the cost, because it reads page images; the modernised
reading works from text.

### The critical apparatus is the point

`transcripts/preamble/grothendieck.sty` defines seven macros for the
transcription, and they carry the whole honesty of the exercise:

| Macro | Meaning |
|---|---|
| `\page{47}` | page 47 begins here — this is what turns the facsimile as you scroll |
| `\ill{}` | illegible; **never guessed** |
| `\uncertain{…}` | a reading offered, and flagged as doubtful |
| `\add{…}` | an editorial addition |
| `\struck{…}` | struck out by Grothendieck — a deletion often shows where the thought turned |
| `\note{…}` | the transcriber's note on the state of the page |
| `\marginal{…}` | a marginal note **of his**, distinct from the body |

A transcription that smooths over a gap has destroyed the only thing it was
for: an invented word that reads like the others is the worst possible outcome,
because nothing on the page distinguishes it from a sure reading.

`scripts/render.mjs` accepts a **restricted subset** of LaTeX, deliberately.
Anything outside it fails loudly rather than being silently flattened.
Mathematics is not converted at all — the delimiters pass through and KaTeX
typesets them, so screen and PDF come from one source.

Commutative diagrams are rendered in both: by `tikz-cd` in the PDF, and on
screen by a renderer that lays the nodes out in a CSS grid, typesets each with
KaTeX, and draws the arrows in SVG from the measured cell positions — so the
mathematics stays selectable text rather than becoming a picture. It covers the
documented arrow subset and **raises on anything else**, because a diagram
rendered with an arrow missing asserts a commutation nobody wrote.

### Running a pass without a human

A batch is normally transcribed by a person sitting in front of Claude Code,
one batch per conversation. That is how the method was established — the skills
were written by watching passes fail — and it does not reach 884 batches.

```bash
npm install --no-save @anthropic-ai/claude-agent-sdk   # not a dependency; see below
npm run headless -- transcribe 115 1      # one batch
npm run headless -- modernize 115         # one folder
npm run usage                             # what the passes so far cost
npm run verify -- 115 1                   # the three gates, as code
```

The SDK is asked for by name rather than declared as a dependency: it ships a
per-platform Claude Code binary of 188 MB, and everything else here is a static
site that has no use for it.

`npm run headless` is **Claude Code as a library**, not a reimplementation of
it. The [Claude Agent SDK](https://code.claude.com/docs/en/agent-sdk) supplies
the harness — the loop, the file and shell tools — and discovers
`.claude/skills/` from the filesystem exactly as the CLI does, so
`/transcribe-grothendieck 115 1` dispatches the same `SKILL.md` a person
dispatches by typing the same thing. There is no second copy of the method to
keep in step with the first, which is the whole reason for doing it this way: a
headless edition produced from a paraphrase of the skill would not be the same
edition, and nothing in the file would say so.

What the script adds is what the missing person was doing. A `PreToolUse`
guard refuses the few commands nobody should reach for unattended — `git
commit` and `git push` among them, so that a failed check comes back into the
loop instead of going quietly into the history. `npm run verify` is then run
against what the pass wrote, and its report handed back into the same session
to be fixed. And every round's token usage is recorded under `archives/usage/`,
in the shape `npm run usage` reports for the interactive passes, so the two can
be compared.

### Trying it without an API bill

The SDK spawns Claude Code, which resolves credentials the way the CLI does. So
a pass can be paid for two ways, and they differ only in who is billed:

```bash
claude auth login                   # a Claude subscription — no API invoice
claude setup-token                  # the same, as a long-lived token for CI
export ANTHROPIC_API_KEY=...        # the API, which is what unattended runs want
npm run headless -- smoke           # one turn: does the chain work?
```

On a subscription the pass draws on the same quota an interactive pass draws
on, which is what every batch in this repository was produced under. (Anthropic's
SDK terms cover using your own subscription for your own work; they do not
permit shipping a *product* to other people on subscription auth.) For anything
unattended, use the key — a subscription login expires, and it expires mid-pass
rather than before it.

`npm run headless -- smoke` is one turn with no tools and nothing written, a
few hundred tokens, and it reports whether credentials were accepted and which
skills were discovered. Run it before a real pass: a transcription is 31.5M
input tokens over a hundred-odd turns, and finding out at turn 3 that the
working directory was wrong is expensive. The cheapest *real* pass is
`npm run headless -- tag 115`, which rewrites one `\keywords` line and so
exercises the same loop — skill dispatch, file write, gates, meter — in a
handful of turns.

### Somewhere other than a laptop

The runner is an ordinary Node script and does not care where it runs. Where it
runs, though, is a choice between two things that do not currently combine.

**Watching it happen** means one of Anthropic's two surfaces, and both refuse an
API key by documented design — [Claude Code on the
web](https://code.claude.com/docs/en/claude-code-on-the-web) shares an account's
rate limits and needs a claude.ai sign-in, and [Remote
Control](https://code.claude.com/docs/en/remote-control) says plainly that API
keys are not supported. What they give in exchange is exactly the right shape
for the experiment that has to happen first:

```bash
claude --cloud "/transcribe-grothendieck 115 1"
```

launched from a checkout, run on an Anthropic VM, watched from claude.ai/code or
the phone, and it clones the GitHub remote at the current branch — so push
before starting one. It picks up `.claude/skills/` the same way everything else
here does.

**Paying for it separately** means an API key, and therefore no Anthropic
progress view: a VM you control, `nohup` or `tmux`, progress from the log and
`archives/usage/*.json`, spend from the Console's usage dashboard and a
workspace spend limit. `--budget` stops one pass; only the workspace limit stops
a month of them.

The first of those settles the question the second one needs answered, which is
the order to do them in. **69% of an interactive pass's cost is cache
*writes*,** plausibly because a one-hour cache entry expires in the gaps where a
person is thinking. A loop does not stop. Whether that share collapses is the
difference between roughly $47,000 for the fonds and a good deal less, and one
metered pass says which.

**None of this says the reading is right.** The gates prove the file is
well-formed, never that a word matches the page — and a fluent wrong word is
the one failure this edition has no mechanical defence against. A headless
transcription is a draft nobody has read, and its header comment says so.

## The repository

| Path | Role |
|---|---|
| `src/content/catalogue.ts` | The inventory — 178 folders, 22 groups — generated, never hand-edited |
| `src/content/books.json` | The five notebooks, read by the site *and* by the mirroring script |
| `transcripts/status.json` | The three states no file can prove — `running`, `checked`, `skipped` — reviewable in a diff |
| `src/components/FacsimilePane.tsx` | The right pane: the streamed folder PDF, resizable, page-anchored |
| `src/components/TranscriptPane.tsx` | The left pane: the transcript in its own frame, reporting the page being read |
| `scripts/catalogue.mjs` | Re-reads Montpellier's inventory into typed data |
| `scripts/archive.mjs` | Downloads and cuts folders into batches — for transcription, not for reading |
| `scripts/render.mjs` | LaTeX subset → the reading view, in ar5iv's stylesheet |
| `scripts/verify.mjs` | The three gates as code: it renders, every formula typesets, no overfull box |
| `scripts/headless.mjs` | A pass with no human in front of it, running the same skills through the Agent SDK |
| `scripts/usage.mjs` | What a pass cost, read back off the sessions that produced the editions |
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
same twenty pages.

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
fonds' ~28,000 pages, about 18,000 may be circulated; third-party
correspondence cannot be, without permission.

No transcription here is an edition. A machine pass over seventy-year-old
handwriting produces a reading, checkable against the facsimile on the same
screen. That is its whole value, and its whole claim.
