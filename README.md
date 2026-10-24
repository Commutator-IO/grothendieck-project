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

This site puts the LaTeX transcription of a page **beside the page itself**, so
that scrolling the transcript turns the facsimile's pages. Every reading can be
checked against the handwriting it came from, on one screen, without a second
window. Around that reader it builds what only a reading of the whole fonds
can give: an index, a timeline, a register of letters, the diagrams and
formulas, measurements of the hand, maps, and findings that may not stand in
the literature.

The five notebook pages that used to be the ways in (*Cahier de Topos*,
*Cahier de Motifs*, *La Longue Marche*, the late notebooks, the scattered notes) were
removed on 19 October 2026. Their groupings survive as badges on the folders
of the front page and as progress figures on `/method/`, which also says that
three of the five are ours and two reproduce an inventory group — citing "the
Cahier de Topos" does not commit you to the same thing as citing folder 19.

## The site

The header has three collections — **Fonds**, **Quillen**, **Bourbaki** — and,
for the fonds, its tabs and then the pages about the project.

| Page | Contents |
|---|---|
| [`/`](https://grothendieck.commutator.io/) | **Whole fonds** — what the fonds is, where the work stands, all 178 folders in Grothendieck's filing order, searchable, and the reader: transcription on the left, Montpellier's facsimile on the right. Also the published editions that cover a folder. `/archive/` stays as a door to it, for links posted before 26 September |
| [`/index/`](https://grothendieck.commutator.io/index/) | The people, his works cited and the subjects, each to the folder and the batch where it occurs |
| [`/timeline/`](https://grothendieck.commutator.io/timeline/) | When the folders were written, and how anyone knows: the inventory's datings as ranges, deduced or read, and the dates written on the leaves |
| [`/letters/`](https://grothendieck.commutator.io/letters/) | A register of the letters found in the transcribed folders: when, with whom, where, and how the site gives them |
| [`/hand/`](https://grothendieck.commutator.io/hand/) | The hand, measured from the transcriptions: words unread and doubtful, strike-outs, margins, diagrams and languages, folder by folder |
| [`/diagrams/`](https://grothendieck.commutator.io/diagrams/) | The 2,000 commutative diagrams, the richest first, each linked to its transcription and to the facsimile page |
| [`/formulas/`](https://grothendieck.commutator.io/formulas/) | The 25,946 displayed formulas, the same way |
| [`/maps/`](https://grothendieck.commutator.io/maps/) | Five maps: folders and what is in print, the mathematical lineage, who is named together, the mathematics by subject, what the folders cite |
| [`/findings/`](https://grothendieck.commutator.io/findings/) | Leaves bound backwards, manuscripts interleaved, results that may not stand in the literature — each with what would settle it — and the statements proved in Lean |
| [`/method/`](https://grothendieck.commutator.io/method/) | How he took notes, how transcription proceeds, what it costs, and what this site does not claim |
| [`/contribute/`](https://grothendieck.commutator.io/contribute/) | How to install the skills, run a batch, check readings and open a pull request |
| [`/review/`](https://grothendieck.commutator.io/review/) | The open checks against the facsimile, one spot of a page at a time — linked from Contribute, not in the header |
| [`/quillen/`](https://grothendieck.commutator.io/quillen/) | Daniel Quillen's 630 research notebooks, 1968–2003, as the Clay Mathematics Institute publishes them, with the index the Clay publishes, searchable |
| [`/bourbaki/`](https://grothendieck.commutator.io/bourbaki/) | The Bourbaki archive's catalogue (Archives Henri Poincaré) — rédactions, congress reports, circulars — with the documents that meet the fonds ringed in red |

Quillen and Bourbaki open their documents in the same facsimile pane as the
fonds, framed straight from claymath.org and from the archive's own server,
which both allow it: nothing is copied and no relay is involved. The articles
are served under `/article/` (below), and
[`/llms.txt`](https://grothendieck.commutator.io/llms.txt) describes the site
for language models, one line per page.

**Any passage can be commented on.** Select text in a reading view, on
Findings, on the Timeline or on Letters, and a panel offers to keep the comment
as a note — in the browser's `localStorage`, nowhere else — or to open a
prefilled GitHub issue quoting the passage and naming where it sits
(`src/lib/notes.ts`). The site is static: nothing leaves the browser until the
reader submits GitHub's own form.

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

The same relay serves the published editions listed on the front page whose
host forbids framing — but only the exact files in
[`relay/allowed.json`](relay/allowed.json), generated from
`src/content/editions.json` by `npm run relay:allowlist` (the build fails if it
is stale), so that it can never become an open proxy for someone else's
server.

### Mirroring, which reading no longer needs

Still worth having for transcription: handing a transcriber a twenty-page file
beats handing it a 204 MB volume and a page range.

```bash
npm run archive -- motives          # a whole notebook
npm run archive -- 19 --batches 1-3 # a beginning
```

Files land in `archives/`, outside `public/` so a build can never carry them,
and git-ignored so a commit never can either.

## The rights switch

The rights in the manuscripts belong to Grothendieck's heirs (see
[`RIGHTS.md`](RIGHTS.md)), and whether transcriptions may be shown online is an
open question with the institutions involved. So the deploy has a switch,
`RENDER_TRANSCRIPTS`, a repository variable set by hand through the
« Transcriptions switch » workflow. Off, nothing turns `transcripts/*.tex`
into a reading view, a TEI file, a PDF or a gallery page, and the review page
quotes no reading: the deployed site carries none of their text, while the
facsimile pane, the inventory and the registers stay as they are. It deletes
nothing and rewrites no history — the `.tex` stay in the repository, and
switching back on restores the site at the next deploy.

Quillen and Bourbaki go further: their transcriptions are never committed at
all, and so never reach the deploy. `transcripts-quillen/` and
`transcripts-bourbaki/` are git-ignored except for their preambles, and so are
their reading views, `public/transcripts-quillen/` and
`public/transcripts-bourbaki/`, which only the machine that holds the sources
can render:

```sh
npm run render:local     # = npm run render -- --quillen, then -- --bourbaki
npm run dev              # the dev server serves them as it serves public/transcripts/
```

In the dev server, the Quillen and Bourbaki tabs then open the same reading
layout as a Montpellier folder — the transcription on the left, landing on the
page the fragment names, the holder's PDF in the facsimile pane at `#page=N`,
following the page being read: `/quillen/#1968/1968-13/1/p3` (notebook, batch,
page; `#1968/1968-13` still opens the notebook at batch 1) and
`/bourbaki/#doc/792/1/p3` (AHP record 792 = rédaction n° 457, transcribed in
`transcripts-bourbaki/457/`; `#doc/792` still works). A Bourbaki folder is
named by the rédaction number or `item-<id>`, and is matched to its AHP record
by the `items/show/<id>` its header cites. A document with no rendered batch
says « no transcription yet ».

In a build, each reader is compiled in only with its switch:
`VITE_RENDER_QUILLEN=true` (repository variable `RENDER_QUILLEN`) and
`VITE_RENDER_BOURBAKI=true` (repository variable `RENDER_BOURBAKI`, set from
the « Transcriptions switch » workflow, whose Bourbaki choice defaults to
« unchanged »). Both are off by default; off, the tab is the catalogue and the
facsimile pane as before, with no reader chunk in the build, and a local build
also drops its copy of `public/transcripts-{quillen,bourbaki}/` and their
manifest entries from `dist/`. Switched on in CI, the reader is there but has
nothing to read: the transcription directories do not exist on the runner, so
every document says « no transcription yet ». The facsimiles need no switch,
in any collection: they are always streamed from the holder's own server and
never stored.

The Illusie tab has a switch of its own, `RENDER_ILLUSIE`, off unless the
repository variable is exactly `true` (set it from the « Transcriptions
switch » workflow, whose Illusie choice defaults to « unchanged », or with
`gh variable set RENDER_ILLUSIE`). The IHÉS has not published the Fonds
Grothendieck–Illusie, so off — the default — the deployed tab is the inventory
alone, with no facsimile pane, no image address and no reading view. On, the
deploy runs `npm run render -- --illusie` over `transcripts-illusie/` (versioned,
like `transcripts/`) and builds with `VITE_RENDER_ILLUSIE=true`, and each item
opens the same reading layout as a Montpellier folder, at
`/illusie/#<item>/<batch>/p<page>`: the transcription on the left, the IHÉS's
jpg page views in the facsimile pane, loaded from its server and never copied.
The dev server always shows that view; `VITE_RENDER_ILLUSIE=true npm run build`
reproduces it in a build.

## Transcription

Every skill lives under `.claude/skills/` and, since 19 October 2026, runs on
Opus 5.5 and nothing else; earlier passes ran under Fable 5, Fable 5.1 and
Opus 5, which are no longer admitted. Each file's header records the model
that read its pages and the date, so that a batch's provenance stays a fact
about the file rather than about whichever model happened to be selected.

| Skill | Produces |
|---|---|
| [`/transcribe-grothendieck`](.claude/skills/transcribe-grothendieck/SKILL.md) | the transcription of a twenty-page batch — the pages as written, with the critical apparatus |
| [`/modernize-grothendieck`](.claude/skills/modernize-grothendieck/SKILL.md) | the modernised reading of a whole folder — a résumé, then current notation and names, footnotes instead of apparatus |
| [`/tag-grothendieck`](.claude/skills/tag-grothendieck/SKILL.md) | the folder's tags — the `\keywords{}` line closing the résumé |
| [`/find-novelty`](.claude/skills/find-novelty/SKILL.md) | candidate findings, written as claims about the literature and never about priority, into `src/content/findings.ts` |
| [`/contribute-to-mathlib`](.claude/skills/contribute-to-mathlib/SKILL.md) | a general lemma a Lean proof needed, proposed to mathlib as a draft pull request |
| [`/transcribe-quillen`](.claude/skills/transcribe-quillen/SKILL.md) | a batch of one of Quillen's notebooks, same apparatus — local only, in `transcripts-quillen/` |
| [`/transcribe-bourbaki`](.claude/skills/transcribe-bourbaki/SKILL.md) | a Bourbaki document, keeping apart what the machine typed and what a hand added — local only, in `transcripts-bourbaki/` |

**Batches can run in parallel.** Transcription is one batch per fresh context,
but the batches of a folder need not wait for each other: run them as Claude
Code background tasks, one subagent per batch. The parent session mirrors and
tiles every batch first (`npm run archive -- <folder> --batches 1-N`, then
`npm run tiles -- <folder> <batch>` for each, which can run concurrently),
then launches one background subagent per batch with
`/transcribe-grothendieck <folder> batch <N>`. Each subagent writes only its
own `batch-NN.fr.tex` and runs `npm run render` to check it. It does not run
`pdf`, `manifest` or `lexicon`, and does not commit. When all of them have
finished, the parent runs `npm run render && npm run pdf && npm run manifest &&
npm run lexicon`, checks the reading views, and commits once. Folder 11 was
transcribed this way: three batches of about twenty-five minutes each, done in
the time of one. The cost per batch and the twenty-page ceiling don't change.
What you give up is continuity: no batch can read the one before it, so each
fixes its notation on its own and notes any run that crosses a batch boundary.
Give each subagent its own scratch folder. The modernised reading always runs
afterwards, on the whole folder.

Both editions are in French — Grothendieck's language, and the language the
notions were thought in. The modernised reading works from the transcription,
never from the handwriting directly: two independent readings of the same hand
would diverge, and nothing would say which was right.

The modernised reading is the one allowed to depart from the page, and is held
to being **correct as it stands**: where the manuscript is loose it states what
is true and footnotes what the page has. It opens with a `Résumé` written for
someone who has not met the subject, and closes that résumé with a line of
English keywords — the modern vocabulary to search under, three to six terms
for a short folder and many more for a long one. Those keywords are
the **single source** of the folder's tags: `npm run manifest` extracts them,
and the front page's search matches on them. There is deliberately no tags
file, so no tag can describe content nobody has read.

### Reporting a reading, and checking one

Everything here is first-pass machine work; corrections are the point of
publishing it. There are three ways to send one:

- the **Report a reading** button, in each batch's download row, opens a
  prefilled GitHub issue with the shelfmark, the batch and the page on screen;
- the **comment** feature (above) quotes the exact passage selected;
- the **review page**, `/review/`, puts the open checks in front of a reader
  of French handwriting one at a time — an unread or doubtful word, a date on a
  leaf, a letter's writer, an insertion that may be his or ours — with the
  question on the left and the facsimile at that page on the right. The
  answers (« Reading is right », « I read something else », « Can't tell »)
  stay in the browser until they are sent, all at once, as one prefilled
  issue. No mathematics is needed.

The queue is built by `scripts/review-queue.mjs` from
[`docs/review/issue-35.md`](docs/review/issue-35.md), the archived checklist of
issue #35, into `src/content/review-queue.json` (and the few words of current
reading around each spot into `review-snippets.json`, which the rights switch
leaves out). An answer is applied at the source only once a person has checked
it on the facsimile: the `.tex` is corrected, or confirmed, and gains a
`% Revised` line saying what was checked and in which issue, which becomes a `<change>` in the
TEI. The item is then recorded in `src/content/review-answered.json` — applied,
confirmed as it stood, or still illegible — and leaves the queue.

```bash
npm run render      # transcripts/*.tex → the reading views the left pane shows
npm run tikz        # compile the transcriptions' tikzpictures to committed SVGs
npm run pdf         # → the PDFs the download buttons offer
npm run tei         # → a TEI P5 file per transcription, for archives and deposits
npm run manifest    # tell the site which files now exist
```

The `.tex` under `transcripts/` is the source of record and the only thing
versioned, with the SVGs of its pictures. HTML, PDF and TEI are derived, and
rebuilt.

### The TEI export

`npm run tei` writes `batch-NN.fr.xml` beside each transcription's HTML and
PDF, and the download row offers it as **TEI**. It is produced from the `.tex`
alone, mechanically, and re-reads no page: the nine apparatus macros map one
to one onto TEI's own elements — `\ill{}` to `<gap reason="illegible"/>`,
`\uncertain{}` to `<unclear>`, `\supplied{}` to `<supplied>`, `\add{}` to
`<add>`, `\struck{}` to `<del>`, `\note{}` to an editorial `<note>`,
`\drawing{}` to a `<note>` of type drawing, `\marginal{}` to an authorial one
in the margin, `\page{}` to `<pb>` with a `facs` link into Montpellier's PDF at
the right offset. Mathematics travels untouched as TeX inside `<formula>`;
commutative diagrams as `tikz-cd` inside `<figure>`, and his other figures,
redrawn in TikZ, as a `<figure>` holding the SVG and its source. The header
carries what the file's comment carries — the model that read the pages and the date, and
every revision since (each `% Revised` line becomes a `<change>` in
`<revisionDesc>`, pointing at the model that made it), the « Édition de
démonstration » status, the shelfmark and the inventory's dating — as
structured statements, so a file deposited in HAL or Nakala keeps its
provenance without this site. The export holds the transcription's line of
not being a diplomatic edition: it encodes what the macros encode and nothing
about the paper. A construct outside the subset — an unknown environment, a
control sequence that would be left as text, a `% Pass:` or `% Revised` line
it cannot read — fails the run, as it fails `npm run render`.

The export is written against a customisation of its own,
[`tei/grothendieck.odd`](tei/grothendieck.odd): the sixty-four elements it
emits and no others, with closed value lists for the attributes that carry
meaning (`@type` on `div`, `figure` and `note`, `@notation` on `formula`,
`@reason` on `gap`, `@rend`). Each file names the RELAX NG derived from it in
an `<?xml-model?>` and the ODD in `<schemaRef>`, both served under
[/tei/](https://grothendieck.commutator.io/tei/grothendieck.odd), so an XML
editor validates a downloaded file without being told how. The deploy runs

```bash
npm run tei:validate
```

which validates every file, with jing, against unmodified `tei_all` and
against the schema derived from the ODD (TEI Stylesheets on Saxon, every
input pinned by version and SHA-256), then checks the ODD against the export
in both directions — no element used and undeclared, none declared and
unused. Any failure fails the deploy; so does `npm run check-tei`, which
compares the TEI reading view with the `.tex` one page by page. Locally it
needs Java.

**As of 24 October 2026, 638 batches are transcribed — 164 folders, 9,414
pages.** Every folder no edition covers has a first pass, and six folders an
edition covers are partly transcribed as well. Every transcribed folder also
has its modernised reading, taken whole, in current notation. A second
transcription pass
([issue #51](https://github.com/Commutator-IO/grothendieck-project/issues/51)),
re-reading each page on 700 dpi tiles, has taken 61 batches of 15 folders so
far. Statements of 72 folders are proved in Lean (below).

None of it has been read through page by page by a person. What has been
checked on the facsimile, by the author, is spot readings: 125 in 54 folders,
with 31 entries of the letters register and 57 dates, the checks recorded in
the transcription files as `% Revised` lines. `/method/` prices the steps separately, from the
passes themselves: transcription carries almost all the cost, because it reads
page images; the modernised reading works from text.

### The critical apparatus is the point

`transcripts/preamble/grothendieck.sty` defines nine macros for the
transcription, and they carry the whole honesty of the exercise:

| Macro | Meaning |
|---|---|
| `\page{47}` | page 47 begins here — this is what turns the facsimile as you scroll |
| `\ill{}` | illegible; **never guessed** |
| `\uncertain{…}` | a reading offered, and flagged as doubtful |
| `\add{…}` | an insertion **of his** — above the line, over a struck word, his ink on a typescript; set in ⌜corners⌝ |
| `\supplied{…}` | what the transcriber supplies and the page does not carry — a missing letter, a clipped word-end; set in [brackets] |
| `\struck{…}` | struck out by Grothendieck — a deletion often shows where the thought turned |
| `\note{…}` | the transcriber's note on the state of the page |
| `\drawing{…}` | a drawing of his, described by the transcriber rather than redrawn |
| `\marginal{…}` | a marginal note **of his**, distinct from the body |

`\add{}` and `\supplied{}` were one macro, declared as the supply, until 26
September 2026, when most of its 6,144 uses turned out to be his insertions and
the TEI was crediting them to the transcriber. They were separated by a rule
checkable in the file, not by a fresh reading: a use glued to the word it
completes (a letter or digit immediately before or after it) became
`\supplied{}` (529), one standing free stayed `\add{}` (5,615). That residue is
the rule's guess — a free-standing supply, such as an expanded « = » for
« même », still reads as his — and only a person with the facsimiles will
settle it.

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

## The Lean appendix

[`lean/`](lean/README.md) proves in Lean 4, against mathlib, statements the
modernised readings make: 72 folders, one file each, and two Bourbaki
rédactions, **2,146 theorems** (`cat lean/Grothendieck/*.lean | grep -c
'^theorem'`). CI builds it with every warning an error, and lean-action's axiom audit fails
on any axiom beyond Lean's three standard ones (`sorry` and `native_decide`
included). A proof says that what a reading states **holds
together**, not that it is what the page says: a perfectly formalised
statement can be a perfectly formalised misreading. Several proofs found the
reading's gloss false, or the page itself wrong, and say so.

Each statement, its proof written out in French and what the verification
found are in the appendix [`docs/lean/article.tex`](docs/lean/article.tex),
served as [/article/grothendieck-lean.pdf](https://grothendieck.commutator.io/article/grothendieck-lean.pdf)
and linked from Findings and Method. General lemmas the proofs needed are
proposed upstream to mathlib as draft pull requests, through
`/contribute-to-mathlib` (issue
[#52](https://github.com/Commutator-IO/grothendieck-project/issues/52)).

## The articles

| Source | Article | Served at |
|---|---|---|
| [`docs/rhm/`](docs/rhm/README.md) | *Dater, reprendre, déplacer* — the working notes as a mathematical practice, in French, for the *Revue d'histoire des mathématiques* | [/article/grothendieck-rhm.pdf](https://grothendieck.commutator.io/article/grothendieck-rhm.pdf) |
| [`docs/study/`](docs/study/README.md) | *A Machine Reads Grothendieck's Working Notes* — the method and the encoding, for the *Journal of the TEI*, with its TEI submission | [/article/grothendieck-jtei.pdf](https://grothendieck.commutator.io/article/grothendieck-jtei.pdf) and `.xml` |
| [`docs/lean/`](docs/lean/article.tex) | The Lean appendix, in French | [/article/grothendieck-lean.pdf](https://grothendieck.commutator.io/article/grothendieck-lean.pdf) |
| [`docs/cicm/`](docs/cicm/README.md) | *Formalising a Mathematician's Working Notes* — the statements formalised in Lean, for CICM (LNCS) | [/article/grothendieck-cicm.pdf](https://grothendieck.commutator.io/article/grothendieck-cicm.pdf) |
| [`docs/conjectures/`](docs/conjectures/article.tex) | *Conjectures in Grothendieck's working notes* — dated first appearances, open questions, what can be formalised | not yet on the site |

Each PDF is compiled locally and committed, excepted by name from `*.pdf` in
`.gitignore`, since these are ours and not the fonds'. The deploy
copies the served ones into `public/article/` (`npm run article-tei`, which
also builds and validates the jTEI submission).

## The repository

| Path | Role |
|---|---|
| `src/content/catalogue.ts` | The inventory — 178 folders, 22 groups — generated, never hand-edited |
| `src/content/books.json` | The five notebook groupings, now only the front page's badges, Method's progress figures and the mirroring script's shorthands (`npm run archive -- motives`) |
| `src/content/findings.ts` | The candidate findings the Findings tab renders, written by `/find-novelty` |
| `src/content/dated-leaves.json`, `letters.json` | The dates written on the leaves and the register of letters, every record resting on a file and a line |
| `src/content/editions.json` | The published editions that cover a folder, and how their shelfmarks correspond |
| `src/content/review-queue.json`, `review-answered.json` | The review page's open checks, and the ones already answered, by issue |
| `transcripts/status.json` | The three states no file can prove — `running`, `checked`, `skipped` — reviewable in a diff |
| `transcripts-quillen/`, `transcripts-bourbaki/` | Local transcriptions of the other collections, git-ignored but for their preambles |
| `src/components/FacsimilePane.tsx` | The right pane: the streamed PDF, resizable, page-anchored — shared by the fonds, Quillen, Bourbaki and Review |
| `src/components/TranscriptPane.tsx` | The left pane: the transcript in its own frame, reporting the page being read |
| `src/lib/notes.ts` | Select a passage, keep a note or open a prefilled issue |
| `scripts/catalogue.mjs` | Re-reads Montpellier's inventory into typed data |
| `scripts/archive.mjs` | Downloads and cuts folders into batches — for transcription, not for reading |
| `scripts/render.mjs` | LaTeX subset → the reading view, in ar5iv's stylesheet |
| `scripts/review-queue.mjs` | Builds the review queue from `docs/review/issue-35.md` |
| `relay/server.mjs`, `relay/allowed.json` | The production relay, and the exact third-party files it may fetch |
| `vite.config.ts` | One HTML entry per tab; also relays `/source/*.pdf` from Montpellier in dev, forwarding range requests |
| `lean/` | The Lean proofs, against a pinned mathlib |
| `tei/grothendieck.odd` | The TEI customisation the export is validated against |

### Why the transcript pane is an iframe

It wears [ar5iv](https://github.com/dginev/ar5iv-css)'s stylesheet — the one
LaTeXML produces for arXiv articles — which claims `:root`, `body`
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

Browsing needs nothing else. The other tools are needed only for what uses
them:

- `pdfinfo` and `pdftoppm` to mirror folders and cut tiles (`brew install
  poppler`);
- [tectonic](https://tectonic-typesetting.github.io/) to compile transcript
  PDFs and the articles (`brew install tectonic`) — `npm run pdf` falls back
  on a local XeLaTeX, never pdfLaTeX, since the preamble uses fontspec;
- Java for `npm run tei:validate` and `npm run article-tei`, which fetch
  their own pinned jing, Saxon and TEI Stylesheets;
- [elan](https://github.com/leanprover/elan) for `lean/`: `cd lean && lake exe
  cache get && lake build`.

`npm run build` checks the relay allowlist, writes the manifest, type-checks
with `tsc -b` and builds; CI also runs `npm run lint` first.

## Credit and limits

The facsimiles are from the **fonds Alexandre Grothendieck**, University of
Montpellier — given by Jean Malgoire, catalogued in 2015–2016 by Hélène
Rodriguez and Frédéric Troilo under the direction of Sophie Dikoff. Of the
fonds' ~28,000 pages, about 18,000 may be circulated; third-party
correspondence cannot be, without permission.

No transcription here is an edition. A machine pass over seventy-year-old
handwriting produces a reading, checkable against the facsimile on the same
screen. That is its whole value, and its whole claim.

**Two licences, not one.** The code and the site are CC0 — take them. The
transcriptions are not and cannot be: they reproduce manuscripts whose rights
run until the end of 2084 and belong to Grothendieck's heirs, so this project
claims nothing over their contents and grants nothing. [`RIGHTS.md`](RIGHTS.md)
sets out both, and says what happens if the University or the rights holders
ask for this to come down.
