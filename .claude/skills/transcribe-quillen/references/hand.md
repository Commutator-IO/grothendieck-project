# Quillen's hand — what the passes have learned

Nothing yet: no notebook has been transcribed. Each pass adds here, under a
dated heading naming the notebook and batch, what the next pass should not have
to work out again:

- the layout of a page: one notebook page per PDF page or two; ruled or plain; margins used;
- how an entry's date is written, and where on the page;
- abbreviations and shorthand (the English of a working notebook: « iff », « s.t. », arrows for « implies »);
- letters and symbols that are easy to confuse in his hand;
- his notation, and when it changes over the years.

Like the fonds' `hand.md`, this narrows the candidates for a reading and never
settles one: where the page will not support what it suggests, the page wins
and `\ill{}` stands.

## 2026-10-23 — 1983-2, batch 1 (pages 1-20)

- 1983 notebooks: one page per PDF page, unruled, black ink; a contents leaf in
  his hand opens the file (PDF p. 1: page span « 547-647 », dates, topics with
  page numbers). His running pagination continues across notebooks (547 on
  PDF p. 2), top right; give it once per page in a \note.
- Entry dates are full and underlined, top left: « January 27, 1983 ».
- 120 dpi grayscale renders (pdftoppm -r 120 -gray) were enough for nearly all
  of it; the hand is a fluent, slanted cursive, denser than in 1968.
- Script letters: script a for the space of connections (\mathcal{A}), script G
  for the gauge group (\mathcal{G}), a curled script a for a coefficient ring
  (rendered \mathfrak{a}), fraktur-like g for Lie algebras. Underlined G
  (\underline{G}) for the fibre of G_d -> G.
- Struck words still blotted solid; struck formulas sometimes scribbled into a
  boxed block. « Tr_(reg) », « F.P. » (finite part), « fmla », « diff'l »,
  « repns. », « coh. », « isom. », « thru ».

## 2026-10-23 — 1983-2, batch 2 (pages 21-40)

- Later corrections in a lighter (grey/pencil) ink appear (p. 24: « NO should
  be A »): transcribe as \marginal with a \note on the ink.
- Struck paragraphs crossed with a diagonal lattice stay readable; transcribe
  them inside \struck{} whole.
- Underlined Ω (single or double) marks a sheaf: \underline{\Omega}.
- \add{} inside display math takes no inner $…$ (\add{{} = 0}); with $…$ it
  breaks the compile.

## 2026-10-23 — 1983-2, batch 3 (pages 41-60)

- A heading can carry a slip of the year (p. 50: « February 22, 1984 » between
  1983 entries): keep it as written, with a \note.
- A lecture number may stand beside the date (p. 59: « Lecture 5 »); the date is
  sometimes repeated small at the head of the next page (p. 53: « Feb. 23 »);
  neither opens a new entry.
- Short horizontal rules separate topics within an entry; \noindent\rule{…}
  keeps them.
- Proper names can be misspelt (« Keiper's thm » for Kuiper): keep and note.
- Tilde and bar over the same letter mark different bundles (\tilde{E} upstairs,
  \bar{E} after descent); the bar is faint at 120 dpi, check at 300.
- For zooms, crop a full-page 300 dpi pdftoppm render with magick; pdftoppm's own
  -x/-y crop returned blank images on this file.

## 2026-10-23 — 1983-2, batch 4 (pages 61-80)

- His « dot » for an infinitesimal variation is a small circle over the letter
  (D̊, N̊, g̊): \mathring{D}; after a bracket, ( )° as a superscript \circ.
- Roman-numeral subscripts I, II for the pieces of an exact sequence
  (E_I, E_II): \mathrm{I}, \mathrm{II}.
- Cancelling terms are marked by a stroke through the matching factors in each
  term, not by deleting the terms: \struck{} on those factors only (it compiles
  inside display math).
- Re-inked words (written over, heavier) recur for emphasis: note once, do not
  treat as underlining.
- His page numbers are sometimes corrected in place (« 611 » over « 610 »).
- Inclusions drawn as ∪ under a row of a diagram: tikz-cd phantom arrow with
  "\cup" description.

## 2026-10-23 — 1983-2, batch 5 (pages 81-100)

- Entries are not always in date order (p. 84: « March 5 » after March 6, then
  March 6 again); keep each heading as written, note the order once.
- His superscript 1 is a short stroke that reads as a prime (V', ψ'_D, θ');
  where it pairs with a superscript 0 (V°, ψ°_D) it is 1. Say so in the header.
- A heavy dot as superscript (V^•_λ) stands for both degrees.
- The Dirac slash: \not{D} renders it.
- Later in the notebook the Luke index dates can differ from the page (index
  « March 6, 9 », page « March 7 » then « March 9 »): the page wins.

## 2026-10-23 — 1983-2, making batches 1-5 renderable

- `node scripts/render.mjs --quillen` refuses tabular, center, alignat*, and
  tikz-cd `phantom` / `equal` arrows, and reports only the first per file. Write
  instead: a list of his with page numbers as itemize; a table as `array` with
  `\text{}` inside `\[…\]`; a boxed formula as `\[\boxed{…}\]` (aligned inside
  for several lines); alignat* as `\[\begin{aligned}…\end{aligned}\]`; a topic
  rule as `\[\rule{9em}{0.4pt}\]` (em units, KaTeX takes them; at most 15em);
  ∪, ≀ or = between two rows of a diagram as an extra row of `\cup`, `\wr`,
  `\Vert` nodes, the vertical arrows of the other columns lengthened to `dd`.
  No `\hfill`, `\fbox`, `\parbox`, `\noindent`.

## 2026-10-23 — 1983-2 batch 6 and 1983-3, batches 1-3 (pages 1-60)

- 1983-3 opens, like 1983-2, with his contents leaf (« 648-730 »), which warns
  « there is an extra 670-699 »: after 699 his numbering starts again at 670
  (PDF p. 53), and from 695 on a small letter (a, b, c, ...) beside or above
  the number marks the pages of that stretch. Quote the number as written, in
  quotation marks for the second run, with the letter. A number can also be
  missing (no 685 after 684, PDF p. 38-39): say so in the \note of the page.
- Places stand beside the date (« March 20, 1983. (In Marseille) »), and states
  (« (very dizzy) »): keep them in the heading.
- His tilde over the Dirac slash: \tilde{\not{D}} renders in both TeX and KaTeX.
  Calligraphic B for the space of (0,1)-forms (\mathcal{B}), plain B for its
  elements; his double-struck 1 for the trivial bundle has no amssymb glyph:
  \mathbf{1} and a \note.
- His underlined words in prose (« Thm », « Summary », « Setup ») are given
  plain: \underline is refused in prose by the renderer (it survives only in
  math). A matrix with blank entries: pmatrix with empty cells, which both
  engines take.
- A horizontal « = » between two objects of a diagram: tikz-cd with « = » as a
  node in a middle column, never a phantom arrow (refused by render.mjs).
- A long display followed by prose (« which integrates to 1 if ... ») runs past
  the margin inside \[…\]: end the display and put the words in the paragraph.
- Check KaTeX with your own script in a subfolder of the scratchpad: the
  scratchpad is shared with other passes running at the same time, and a file
  with a common name (kcheck.cjs) can be overwritten under you.

## 2026-10-23 — 1983-4 to 1983-6 (render subset, more refusals)

- render.mjs also refuses: tikz-cd `mapsto` arrows (use a plain arrow and say
  « ↦ in the notebook » in a \note), a nested itemize (flatten: `\item[]` for
  the indented lines), and a tikz-cd that shares its \[…\] with anything else
  (a label, \qquad, a second formula): give the diagram its own display and
  put the label in a \note or a following display.
- `\add{$…$}` inside display math breaks the compile; `\add{…}` with the math
  bare works in both engines. `\S` is not in the prose subset: write §.
- Notebook numbering can restart in an inserted run (« new 930 », « new 931 »
  in 1983-6 after 932) as well as the lettered run of 1983-3: quote the
  number as written.
- 1983-4 to 1983-6 open with a cover leaf (page span and dates only, or a
  contents leaf with page numbers): transcribe it as page 1, like 1983-2.

## 2026-10-24 — 1983-7, batch 1

- 1983-7 restarts his pagination at 1 (after 1983-6 ended at 1014): PDF p. 2
  = his p. 1. Say so in the header; do not continue the old count.
- In an `array` (or any `\\`-separated environment), a row beginning with `[`
  is read as the optional spacing argument of `\\` and breaks the compile
  (« Missing number »): start such a row with `{}`.

## 2026-10-24 — 1983-10 to 1983-15

- His pagination runs on from 1983-7 (restart at 1) through 1983-15 (351);
  1983-10 numbers p. 125 a second time, and 1983-14 has his own inserted
  pages « 305a », « 306a » after 306: quote them as written.
- 1983-15's Clay scan holds only five pages (cover leaf + his pp. 351-354
  of « 351-395 »): say so in the header rather than looking for the rest.
- More render/KaTeX refusals: `\multicolumn` in an array (drop it, put the
  spanning header in a \note), `\rotatebox` (use \cup or \cap plus a note),
  tikz-cd arrow options with `bend` or `near end` (keep plain labels),
  `phantom` nodes (use `{}` or a hook arrow and a note), `flushright` (plain
  paragraphs plus a note that the closing stands at the right), and a
  tikz-cd followed by text in the same display (« \qquad is cartesian »,
  « over »): close the display first. `\xmapsto` is not in KaTeX: use
  `\overset{…}{\longmapsto}`.
- A heredoc line `\end{document}` typed through `echo` without `-e`-safe
  quoting can arrive as ESC + « nd{document} » (invalid character at the
  last line): append it with printf '%s\n' or inside the heredoc.

## 2026-10-24 — 1983 unnumbered files (Ideas, notes, lecture notes 0-15)

- For a label with spaces (« 1983-Lecture Notes 5 Quillen ») the directory
  takes underscores but `\notebook{}` must keep the spaces: an underscore
  in `\notebook{}` breaks the compile (« Missing $ inserted »).
- The lecture-notes files mix his notes of others' talks with leaves of his
  own (graduate-class preparation in LN 6, a Kronecker-foliation
  calculation in LN 11, Hall-effect reflections in LN 14): say in the
  header which leaves are which. Several files end with blank leaves; give
  them a \page and a « blank leaf » note so the page count matches.
- « Contents template2.pdf » is a typeset contents list, not his hand:
  skipped.

## 2026-10-24 — 1984-5 (pages 1-50)

- 1984-5 opens with a cover leaf (« Feb 29, - Mar 12, 1984 », « 552-600 »);
  his running numbers continue from earlier 1984 notebooks (552 on PDF p. 2).
- His creation/annihilation operators a*, a and the slashed D recur; struck
  formulas are blotted into solid boxes, struck lines crossed by loops.
- A small blank-ish leaf can carry struck notes in a hurried hand (p. 23,
  « Stuff added Mar 12 to use up paper »?): zoom at 300 dpi with magick crop.

## 2026-10-24 — 1984-3 and 1984-4 (whole notebooks)

- Both open with a cover leaf in his hand (date span and his page span:
  « 455-501 », « 502-551 »); his pagination runs on across the 1984 files
  (1984-3 PDF p. 2 = his 455). The 1984-4 scans are taller than the leaf,
  with blank paper below it.
- His Planck constant is a plain h, not ℏ. « Kuiper » is spelt both
  « Keiper » and « Kuiper » within one entry (1984-3, p. 42).
- « Grothendieck » occurs in these files only as « Grothendieck group » and
  « the Grothendieck type formula » (RR for maps): no Pursuing Stacks echo,
  despite what one might expect from early 1984.
- Two-row diagrams with dotted or labelled verticals, and exact sequences
  with « ‖ » under the ends, render most safely as an `array` with `\Vert`
  rows rather than tikz-cd.

## 2026-10-24 — 1984-1 (pp. 1-41) and 1984-2 (pp. 1-62)

- His pagination runs on from 1983-15: 1984-1 is « 355 »-« 395 » (no cover
  leaf; the first date is written « 1983 » with the 4 over the 3), 1984-2
  opens with a cover leaf « Jan. 10, 1984 — Feb. 4, 1984 », « 396-454 ».
- 1984-2 has two leaves scanned in reverse order (PDF p. 49 = « 443 », PDF
  p. 50 = « 442 »; the text runs 441 → 442 → 443) and the number « 443 »
  occurs twice (PDF pp. 49 and 51). A « 413½ » also occurs (PDF p. 20).
  Follow the text, keep the PDF order, and say so in the header.
- Conversation notes (Connes, Atiyah « Michael », Katz-Gabber-Deligne,
  Roe) are in his hand and are his: transcribe in full. A list of topics
  goes well as itemize with `\item[]`.
- `\rightleftarrows`, `\rtimes`, `\not{D}`, `\substack` under an
  underbrace and `\begin{cases}` all pass both engines.

## 2026-10-24 — 1968-16, batches 1-3 (pages 1-22)

- A fair-copy prose draft, not a diary: one page per PDF page, his page numbers
  top right equal the PDF pages, no dates at all. Large letters, about ten words
  a line; 120 dpi is ample. Struck passages are often boxed and crossed with big
  loops or an X lattice, still partly legible; split them into several \struck
  paragraphs. Blank citations « [ ] » and « ( ) » stand for references to fill.
- « ? » is used as a placeholder variable (St(π_1?; A), [?, Z]_0): keep it.
- Self-corrections addressed to himself appear boxed at a page head (p. 12:
  « necessary to add … to get correct statement », with « OKAY »).

## 2026-10-24 — 1968-15, batches 1-7 (pages 1-64)

- A mixed file: pencil drafts on ruled paper (pp. 1-25, 53-64) and ink fair
  copies on unruled or ruled paper, each section renumbered from 1 at top right
  (pp. 26-52). Say in each header which numbering runs where.
- Fair copies underline whole statements (Propositions, Corollaries): \emph.
- Faint pencil remarks in a margin or at the head of a page may be in another
  hand (p. 36 « Druck μ », a printing note); p. 56 « Atlantic City ». Zoom at
  300 dpi before reading them.
- He reuses sheets: p. 25 carries a struck passage from another draft (a p-adic
  lemma) above unrelated K-theory.
