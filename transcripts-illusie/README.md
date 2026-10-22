# transcripts-illusie

Transcriptions of the Fonds Grothendieck–Illusie, held by the Institut des
Hautes Études Scientifiques (IHÉS). None yet.

The IHÉS has not published this fonds: its scans sit on a bare file server,
`repo-archives.ihes.fr/FONDS_GROTHENDIECK_ILLUSIE/`, outside its public
catalogue, and the private correspondence needs its permission
(archives@ihes.fr). Until it agrees, nothing transcribed here is shown on the
deployed site.

## Layout

One directory per item, named by the item's identifier in
`src/content/illusie.json` (`FG_IL_2_GIRAUD69`, `1ILL1`, …), one file per
twenty pages, as for the Montpellier folders:

    transcripts-illusie/FG_IL_2_GIRAUD69/batch-01.fr.tex

The files follow the conventions of `transcripts/` (header comments, preamble
macros, `\page{N}` marks numbering the item's page views from 1, critical
apparatus) and stay inside the subset `scripts/render.mjs` accepts. The
preamble is the fonds' own, reached from here as
`\input{../../transcripts/preamble/grothendieck}`.

## Rendering, and the switch

    npm run render -- --illusie

renders them, with the same renderer as `transcripts/`, into
`public/transcripts-illusie/` (git-ignored), and `npm run manifest` lists them
under `illusie` in `public/manifest.json`. The Illusie tab shows them beside
the IHÉS's page views — in the dev server always, in a deployed build only
when the repository variable `RENDER_ILLUSIE` is `true` (off by default; see
« The rights switch » in the README). Switched off, the deploy renders nothing
from this directory and the tab is the inventory alone.
