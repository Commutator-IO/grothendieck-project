---
name: vectorise-drawings
description: Extracts and vectorises the drawings of a transcribed folder of the Grothendieck fonds, using the method of issue 73. A figure whose picture fixes its structure (dessin d'enfant, cell decomposition, polyhedron, stable graph, configuration on a line) is encoded as checked JSON data and rendered from it; every other figure is redrawn in TikZ from the facsimile; pixel tracing is never published. Writes transcripts/<cote>/drawings/ (<batch>-<n>.tex, .json, drawings.json), and keeps a local contact sheet for review. Use when someone asks to vectorise, redraw, encode or put into TikZ the drawings of a folder, or the \drawing{…} marks of its transcription, or to continue or extend issue 73. It never edits the transcriptions.
---

# Vectorising the drawings of a folder

**Runs on Opus 5.5, and on nothing else**, like every skill of this project.
Reading a pencil sketch off a 300 dpi crop is a visual-attention task. Put
the model in the headers (`build.py --model`, default `claude-opus-5-5`) and
in the closing message. On any other model, stop and say which model the
session is on.

The transcription (`/transcribe-grothendieck`) records each figure as a
`\drawing{…}` mark: a description in words, written after the `\page{N}` it
sits on. This skill turns those marks into figures. It also checks them: an
encoded figure must reproduce the counts Grothendieck writes beside it, and
when the drawing and the transcription disagree, the disagreement goes in a
note.

## The three methods, and which to use

- **Method 3: encode as data, then render.** Use it only when the figure alone
  determines the structure: a dessin with a clear bicolouring, a sphere cut
  by named circles, a polyhedron whose faces you can list, a stable graph, or
  points and intervals on a line. The data go in `<id>.json` (schemas below),
  and every encoding is checked. Never invent structure to make a figure
  encodable. For example, folder 146 has a polyhedron where it is unclear
  which solid is meant, a net where it is unclear which edges are glued, and
  a figure captioned "9 = 3+3+1+2 sommets". Those are redrawn, not encoded.
  In the runs so far, about 40 % of the figures in combinatorial folders (146)
  qualified, and almost none in folders 74 and 144.
- **Method 2: redraw in TikZ.** Use it for everything else: spheres with
  marked points, surfaces, sketches of polyhedra, arrow diagrams and plane
  figures. Draw what is on the page, keep labels as LaTeX text, and say in
  the notes what was left out and what is a reading.
- **Method 1: pixel tracing.** It may serve as a local aid, but it is never
  committed or published. It copies the hand, and for this purpose it adds
  nothing to method 2.

## Setup

- `python3.12` with Pillow. The system `python3` may have a broken PIL; if
  so, use 3.12 or a venv in the scratchpad.
- `pdftoppm` (poppler) and `curl`. The PDFs come through the session's proxy,
  with TLS verification left on.
- **TeX may be missing.** It was missing in every run so far. Without it the
  SVG previews stand in, and the headers say "not compiled". When an engine
  is present, run `compile_tikz.py`, fix every failure, then rebuild with
  `build.py --compiled`.
- **One work dir** in the scratchpad: `W=<scratchpad>/vectorise`. Pass it to
  every script as `--work $W`. It holds the pages, the specs, the previews and
  the contact sheets, and none of it is committed. The scripts are in
  `scripts/`; `scripts/README.md` lists them in the order they run.

## Per folder, step by step

1. **Locate the marks.** Run `extract.py --work $W <cote>`. It gives each
   `\drawing{…}` the id `<batch>-<n>`, the archive page of the last `\page{N}`
   before it, its PDF page and its description. It skips `\drawing` inside
   `%` comments. **PDF page = archive page + 1**, because Montpellier adds a
   cover sheet. Check this on the first page: the archivists' number,
   pencilled at the bottom left, must be on the render
   (`views.py page <cote> <N>`). If the offset is different, pass `--offset`
   to both `extract.py` and `fetch.py`.
2. **Render only the pages with drawings.** Run `fetch.py --work $W <cote>`.
   It downloads `https://grothendieck.umontpellier.fr/<cote>.pdf` and renders
   the marked pages at 300 dpi in grey. Add `--color` when coloured pencils
   carry meaning; the `Or Ye Rd Bl …` styles then give the strokes their
   colour.
3. **Crop, with one bbox per figure.** Look at several pages in one image
   (`views.py pages`). Then read coordinates off tight gridded crops
   (`views.py crops`, where the crop is 100 units wide and y points down).
   Put several crops into one image read: it halves the image tokens. When
   one mark covers several separate figures, give each figure its own
   `figures: [{what, bbox}]` entry. The mark's own `bbox` is then the union.
4. **Encode or redraw.** Write `$W/specs/<cote>.py` with
   `from dsl import *` and `SPECS[id] = dict(bbox=…, kind=…, method=2|3,
   status=…, notes=…, items=flat(…), comb=…)`. Coordinates are in units of
   the crop. If you typed points in a wider view, `from_view(view, bbox, …)`
   converts them to the crop's units.
5. **Check.** `build.py` runs `comb.check` on every encoding. Fix every
   `CHECK FAILED` before going on.
   - Dessins: the cycles of σ0 must match the black vertices, the cycles of
     σ1 the white vertices, and the cycles of σ0σ1 the faces, each compared
     with the picture. The genus comes from Euler: 2 − 2g = B + W − n + F.
   - Spheres and polyhedra: χ = 2, and every edge lies on two faces (or the
     figure is declared a disc, χ = 1).
   - **The numbers he writes**, such as « 6 sommets, 4 faces », go in an
     `expected` block and are compared automatically.
   - Stable-graph tables: the count in each row must equal the number
     `comb.enumerate_stable` finds, and his number must equal 3g − 3 + ν.
6. **Look at the overlay.** Run `build.py --work $W <cote>`. It writes the
   repository files and a triptych for each figure: crop, redraw, and the
   redraw in red over the crop. All the triptychs go into
   `$W/contact-<cote>.pdf`. Open the contact sheet. Re-check the worst
   figures with `views.py overlays`, correct their coordinates, then rebuild
   (`build.py <cote> <id> …` rebuilds only those previews).
7. **Set the status.**
   - **ok**: every element the transcription names is there, in the right
     place, with the right labels.
   - **partial**: something is approximate or left out, and the notes say
     what.
   - **failed**: the figure was not done or could not be located. A mark
     with no spec is written as failed, "not yet done".
8. **Write down disagreements with the transcription**, in `notes`, or in
   `disagreement` for the ones worth fixing. Examples: five looped points
   where the transcription says four; a label read differently; a figure on
   the page that no mark covers. Never correct the `.fr.tex` yourself.
9. **Commit the folder** (see Git below). Append a short report to the
   scratchpad giving the counts by kind and method, ok/partial/failed, the
   disagreements, the tokens, and any page whose crop shows a private name.
   Then run `fetch.py <cote> --clean`.

## Output

```
transcripts/<cote>/drawings/<batch>-<n>.tex   every drawing: standalone TikZ, header comment
transcripts/<cote>/drawings/<batch>-<n>.json  method 3 only: {id, cote, archive_page, encodings: [...], schema_doc}
transcripts/<cote>/drawings/drawings.json     the index
```

`<batch>-<n>`: `n` counts the marks of batch `<batch>` from 1, in source
order. Example: `04-7` is the seventh `\drawing` of `batch-04.fr.tex`.

The TikZ is `\documentclass[tikz]{standalone}` with `x=1mm, y=1mm`, so one
crop unit is 1 mm. It uses only `patterns`, `arrows.meta` and amssymb, plus
these styles:

- `pencil`: his faint strokes;
- `struck`: crossed-out strokes, drawn grey;
- `pt`, `opt`, `mark`: full, open and ringed points;
- the colour styles, when a coloured pencil carries meaning.

The header comment gives the transcription's description, the kind, the
method, the status, the notes, the bbox, the model and the date. It also says
"not checked by a human" and "behind RENDER_TRANSCRIPTS".

`drawings.json` is `{cote, issue: 73, generated_by, date, conventions,
drawings: [...]}`. Each record has these fields:

| Field | Meaning |
|---|---|
| `id` | `<batch>-<n>` |
| `cote`, `batch` | folder and batch number |
| `pdf_page`, `archive_page` | where the figure is; pdf = archive + 1 |
| `bbox` | `[x0, y0, x1, y1]` as fractions of the rendered PDF page, white frame included; with the crop units, it lets the redraw be laid back over the facsimile |
| `description` | copied verbatim from the `\drawing{…}` |
| `kind` | short English name: "sphere with marked points", "stable graph (MD graph)"… |
| `method` | 2 (TikZ redraw) or 3 (encoded and rendered); `null` if not done |
| `status` | `ok`, `partial` or `failed` |
| `notes` | what is drawn, what is left out or a reading, disagreements |
| `files` | `["<id>.tex"]`, plus `"<id>.json"` for method 3 |
| `checks` | method 3: per encoding, `name`, `schema` and the derived numbers (black, white, faces, genus, vertices, edges, euler, type, stable, `expected_ok`, `expected_mismatch`) |
| `orientation` | optional: the crop was rotated (upside-down half of a sheet, turned sheet) |
| `figures` | optional: `[{what, bbox}]`, one per figure when a mark covers several |
| `disagreement` | optional: a disagreement with the transcription that is worth fixing there |

## JSON schemas

Each encoding names its `schema`. It may carry a `name`, an `expected` block
(numbers read on the page) and `labels`. `build.py` adds a `derived` block.

- **`dessin/1`**: darts (edges) 1..n, with σ0 and σ1 as lists of cycles.
  Within a cycle the darts are in counter-clockwise order on the page.
  σ0σ1 means σ1 applied first. Derived: black, white, faces, face degrees,
  passport, genus, connected.
  `{"schema":"dessin/1","n":2,"sigma0":[[1],[2]],"sigma1":[[1,2]],"expected":{"faces":1,"genus":0}}` (z ↦ z²)
- **`map/1`**: one kind of vertex, on half-edges 1..2m. σ gives the
  rotation at the vertices and α the edge pairs.
  `{"schema":"map/1","sigma":[[1,2]],"alpha":[[1,2]]}`
- **`cellular/1`**: named edges and faces as boundary walks. It allows loops
  and parallel edges, so it is the schema for spheres cut by circles.
  `dsl.sphere_cells(equator, chords)` builds it.
  `{"schema":"cellular/1","edges":{"a":["1","2"],"b":["2","1"]},"faces":[["a","b"],["a","b"]]}`
- **`polyhedron/1`**: faces as cycles of vertices, for a simple graph.
  `extra_edges` and `isolated_vertices` cover graphs that are not closed
  surfaces.
  `{"schema":"polyhedron/1","faces":[["1","2","3"],["1","2","4"],["1","3","4"],["2","3","4"]],"expected":{"vertices":4,"faces":4}}`
- **`stable-graph/1`**: genus at each vertex (a genus may be symbolic,
  such as `"g1"`), edges (u = v for a loop), and the legs at each vertex.
  Derived: type (g, ν), b1, stability, stratum dimension 3g − 3 + ν − E.
  `{"schema":"stable-graph/1","vertices":{"v1":0,"v2":0},"edges":[["v1","v2"]],"legs":{"v1":2,"v2":2}}`
- **`stable-graph-table/1`**: his tables, one row per type. Each row has
  `type`, `his_number`, `drawn`, `enumerated` and `graphs`, and is rendered
  canonically with `dsl.stable_graph_items`.
  `{"schema":"stable-graph-table/1","rows":[{"type":[0,4],"his_number":1,"drawn":"drawn 2","enumerated":2,"graphs":[…]}]}`
- **`segment-config/1`**: points and intervals on a line, left to right.
  The point kinds are full, open, paren, bracket, isolated and cross.
  `{"schema":"segment-config/1","items":[{"pt":"a","kind":"full"},{"seg":["a","b"]},{"pt":"b","kind":"open"}]}`

To check the committed files again: `python3.12 scripts/comb.py check
transcripts/<cote>/drawings/*-*.json`.

## Rules

- **Never touch `batch-*.fr.tex` or `*.modern.tex`.** Disagreements go in the
  notes.
- **Draw only what is on the page.** Do not complete a figure from the text,
  and do not tidy his doublings into something he did not draw. Struck
  strokes are drawn `struck` or left out, and the notes say which. A label
  you cannot read is left out and named in the notes.
- **Privacy and rights.** Some sheets carry other people's paper, such as
  typed notices or letters naming private persons (folder 146 p. 77,
  folder 138 pp. 105 and 109). The redraws leave out all typed text. The
  crops still show it, so **the contact sheets and crops stay local and are
  never committed**. Name such pages in the report.
- **Behind `RENDER_TRANSCRIPTS`.** The redraws reproduce part of the work.
  They live in `transcripts/` and follow the transcriptions' switch; never
  publish them on their own, elsewhere.
- **Disk.** Free space is shared. Fetch one folder's PDF at a time.
  `fetch.py` refuses to download below 1 GB free; check `df -h /`. Render
  only the marked pages, and run `--clean` as soon as the folder is
  committed.

## Git

Other agents push to `main` in parallel, and the working tree holds other
people's uncommitted files. Add only this folder's path:

```bash
git add transcripts/<cote>/drawings
git commit -m "Issue 73: drawings of folder <cote> vectorised (<n> drawings: <ok> ok, <partial> partial, <failed> failed)" \
  -m "Co-Authored-By: …" -m "Claude-Session: …"   # the attribution lines of the session
git pull --rebase --autostash origin main && git push origin main
```

If the push is refused, retry the pull and push up to 4 times, waiting 2, 4,
8 and 16 s. **Never force-push, never `git add -A`, never commit the work
dir.**

Three times already, a snapshot taken mid-run was committed by another
process (28f0ee0, 3e07262, 157a59c). The folder's own commit supersedes such
a snapshot: say so in the report and leave the snapshot alone.

## Known failure modes

- **Whole-page figures** cost 3 to 5 times as much as a single figure and
  usually come out partial. Treat them as work items of their own: do them
  last and budget for them.
- **Rotated sheets.** On an upside-down half of a page, crop with
  `rot180=True` (folder 146 p. 66, folder 69 p. 119). Redraw upright, with
  coordinates in the rotated crop. For a turned sheet, use
  `rotate=90|270`, and give labels `s=["rotate=90"]` where he wrote them
  along the sheet. The record gets an `orientation` field.
- **Large arrow diagrams** ("cubes de revêtements", inclusion diagrams):
  place the nodes, draw the principal arrows between node centres, keep
  labels as the transcription reads them, and mark the figure **partial**.
- **Overlay drift.** Coordinates read by eye are off by 1 to 2 units on a
  tight crop, by 4 on large pencil circles, and by **5 to 10 units when read
  off a wide view**. After the first build, open the contact sheet, re-read
  the drifting figures on tight crops, correct them, and rebuild. A canonical
  method-3 rendering, such as a table, does not overlay by design: its check
  is the enumeration.
- **Overinked or tiny labels.** Place them after the transcription and say
  so. Never guess a label the transcription marks illegible.
- **Locating a mark.** The transcription says which page a mark is on, not
  where on the page. If you cannot fix the region, say so. A figure on the
  page that no mark covers is a note, not a new mark.

## Cost

Measured on the pilot and five folder runs, it takes **about 2–4k fresh
tokens per drawing**: 1.8k for 138, 2.4k for 74, 3.2k for 69, 3.6k for 144
and 4k for the pilot. Marginal figures cost about 1.5–2.5k, single figures
3–4k, and whole pages or tables 8–15k. Cached context comes on top and is
the larger share of the bill. To keep it down:

- run one session per folder, never one long session;
- batch crops into one image read;
- render the location views once per folder.

The pace is about 50 drawings in 30 minutes to an hour. A human reviewer
needs about a minute per drawing from the contact sheet, and longer for the
partial ones.
