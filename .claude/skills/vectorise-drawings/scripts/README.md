# vectorise-drawings scripts

The toolkit of issue 73, merged from the pilot (folders 146, 156-8) and the folder
runs (74, 138, 69, 144, 154). Python 3.12 with Pillow; `pdftoppm` and `curl`
(poppler, standard). No absolute paths: every script takes `--work DIR` (default
`$VECTORISE_WORK`, else `<tmp>/vectorise-drawings`; point it into the scratchpad)
and, where it touches the repository, `--repo DIR` (default `$GROTHENDIECK_REPO`,
else the repository this skill lives in). Each script answers `--help`.

| Script | Does |
|---|---|
| `common.py` | paths, work-dir layout, fonts (imported by the others) |
| `extract.py` | lists the `\drawing{…}` marks of a folder into `<work>/marks.json` (ids `<batch>-<n>`, archive and PDF page, description); skips `%` comments |
| `fetch.py` | downloads `<cote>.pdf` from Montpellier, renders only the marked pages at 300 dpi; `--clean` deletes PDF and renders |
| `views.py` | gridded views: `page`, `pages` (several side by side), `crop`, `crops` (several crops in one image), `overlays` (re-check drift) |
| `dsl.py` | short constructors for a spec's items (`L`, `Cv`, `Ci`, `E`, `D`, `T`, `H`…), `shift`/`affine`, `from_view`, `sphere_cells`, `stable_graph_items` |
| `drawkit.py` | one drawing model, three outputs: TikZ (the deliverable), SVG preview, PNG for the overlay |
| `comb.py` | the JSON schemas and their checks; `comb.py check <json>…`, `comb.py enumerate g n` |
| `build.py` | from `<work>/specs/<cote>.py`: writes `transcripts/<cote>/drawings/*.tex`, `*.json`, `drawings.json`, and locally the triptychs and `contact-<cote>.pdf` |
| `compile_tikz.py` | compiles the `.tex` when a TeX engine exists (exit 2 when none), optionally to SVG |

## Order

```bash
cd .claude/skills/vectorise-drawings/scripts
W=<scratchpad>/vectorise            # one work dir for the session
python3.12 extract.py --work $W 146                  # 1. the marks
python3.12 fetch.py   --work $W 146                  # 2. PDF + renders of the marked pages
python3.12 views.py   --work $W pages 146 12 13 15   # 3. locate each figure (page fractions)
python3.12 views.py   --work $W crops 146 a.jpg 01-1:12:0.39,0.68,0.57,0.74 ...   # 4. read coordinates
$EDITOR $W/specs/146.py                              # 5. SPECS = {id: {...}}, `from dsl import *`
python3.12 build.py   --work $W 146                  # 6. repo files + triptychs + contact sheet
python3.12 views.py   --work $W overlays 146 ov.jpg 01-1 01-2   # 7. check drift, fix the spec, rebuild (6)
python3.12 comb.py check ../../../../transcripts/146/drawings/*-*.json   # 8. encodings
python3.12 compile_tikz.py ../../../../transcripts/146/drawings          # 9. only if TeX exists
python3.12 fetch.py   --work $W 146 --clean          # 10. free the disk
```

Smoke test without a PDF: `python3.12 comb.py check transcripts/146/drawings/04-7.json`
from the repository root.
