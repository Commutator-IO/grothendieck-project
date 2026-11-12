# Readings of the transcriptions found by the drawings pass of #128 (12 November 2026)

Issue #145, step « Apply the readings already found by the drawings pass of #128 ». Collected on
2026-11-12 from the reports of 12 November of the #128 passes (`*-report.md`: g148, g154, g1616,
g31, g67, gmid, gsmallA, gsmallB, o145, o67, omidA, omidB, osmall, r148, r154a–d, rmisc), from the
`disagreement` fields of the folders' `drawings/drawings.json`, and from the answers of the
triage files of the same day (`*-settled.md`) that say the transcription is to be corrected.
Each place was then looked at on the Montpellier facsimile (PDF page = archive page + 1, colour,
300–400 dpi crops) by Opus 5.5 (claude-opus-5-5); nothing here was checked by a reader.

One line per place: shelfmark · batch · page · current reading · proposed reading · source.
`[x]` = applied to the transcription (what was applied follows); `[ ]` = left open (why follows).

Two rules held throughout:

- **The `\drawing{…}` marks are not rewritten.** The text of a mark is the key by which
  `scripts/lib/drawing-map.mjs` attaches the redrawn figure (it must equal the record's
  `description` in `drawings/drawings.json`, which this pass may not touch). Where the page
  contradicts the words of a mark, a `\note{}` saying what the facsimile shows is set right after
  it; the mark and its record are to be changed together later, by the vectorising skill.
- **Class t** (an arrow diagram described in words) is set as `tikzcd` or `array` only where every
  label of the page was read; otherwise the item stays open.

## Places

- [ ] 1 · b. 6 · p. 111 · current: note « trois rayons … deux pointillés » · proposed: two solid radii each doubled by a dotted line, and a short axis with a point · source: gsmallA-report; drawings.json 06-1 — not yet looked at
- [ ] 5 · b. 1 · p. 17 · current: note « deux points x′, x avec deux flèches α, β » (class t) · proposed: `x' \arrow[r, bend left, "\alpha"] \arrow[r, bend right, "\beta"'] & x` as tikz-cd · source: gsmallA-report — not yet looked at
- [ ] 5 · b. 1 · p. 17 · current: framed marginal diagram (class t) · proposed: tikz-cd x′ → x′₁ (f), x′ → x (u), x′₁ → x (v) · source: gsmallA-report — not yet looked at
- [ ] 12 · b. 4 · p. 72 · current: note « deux intervalles superposés » · proposed: [-2i,-i] and [-2i+2,-i+1] on one line, four marks · source: gmid-report — not yet looked at
- [ ] 14 · b. 5 · p. 99 · current: label P_2^+ · proposed: kept P_2^+ (no change proposed) · source: gmid-report — not yet looked at
- [ ] 15 · b. 12 · p. 224 · current: marginal sketch of a field tower (class t) · proposed: tikz-cd X–X over ℚ–k₀?–k · source: gsmallA-report — not yet looked at
- [ ] 19 · b. 2 · p. 32 · current: tikz-cd of the second Leitfaden (4 under 3, no 4–7) · proposed: strokes 1–2, 2–5, 2–3, 2–6, 3–4, 4–7, 6–7; 4 not under 3 · source: gsmallA-report — not yet looked at
- [ ] 23 · b. 4 · p. 77 · current: « un mot illisible sous le trait » · proposed: the word stands above the line · source: gmid-report, gmid-settled (23 04-2) — not yet looked at
- [ ] 27 · b. 1 · p. 19 · current: note « esquisses de matrices » (class t) · proposed: two dotted matrices as pmatrix · source: gsmallA-report — not yet looked at
- [ ] 27 · b. 2 · p. 35 · current: « une flèche descendant vers S » · proposed: an arrow G → S (a letter G above it) · source: drawings.json 02-1 — not yet looked at
- [ ] 29 · b. 5 · p. 86 · current: note: cube « l'essentiel de ses étiquettes est illisible » (class t) · proposed: the cube read in full, tikz-cd proposed · source: gmid-report — not yet looked at
- [ ] 29 · b. 10 · p. 183 · current: path x →u_n · → … →u_1 a · proposed: each step a pair of opposite arrows (\rightleftarrows), three pairs · source: rmisc-report — not yet looked at
- [ ] 31 · b. 3 · p. 56 · current: « Y » beside the pencil arc · proposed: X · source: g31-report; drawings.json 03-3 — not yet looked at
- [ ] 31 · b. 4 · p. 67 · current: sketch « dans la marge droite » · proposed: at the lower left of the page · source: g31-report — not yet looked at
- [ ] 31 · b. 4 · p. 70 · current: labels on the q-axis · proposed: n−1, n, n+1 under the p-axis; nothing on the q-axis · source: g31-report — not yet looked at
- [ ] 31 · b. 5 · p. 93 · current: « un petit carré … côtés étiquetés A/tA » · proposed: a tilted frame round an oblique annotation, not a figure · source: g31-report — not yet looked at
- [ ] 33 · b. 1 · p. 2 · current: description of the pencil sheet · proposed: adds a vertical arrow across k → k′ and a short arrow after A · source: drawings.json 01-1 — not yet looked at
- [ ] 43 · b. 3 · p. 50 · current: marked point « au croisement » · proposed: on the heavy curve a little above the crossing · source: g148-report — not yet looked at
- [ ] 43 · b. 4 · p. 61 · current: note « trois croquis sans légende lisible » (class t) · proposed: items 2 and 3 are relations: array C ↓ Ens., and an overbrace chain x_0 → x_n · source: g148-report — not yet looked at
- [ ] 43 · b. 4 · p. 64 · current: two brackets « superposées » · proposed: they follow one another · source: g148-report — not yet looked at
- [ ] 43 · b. 4 · p. 67 · current: sketch (2) four arcs; (4) « éventail » · proposed: (2) five strokes above the segment; (4) a graph of 8 points with 9 weighted arrows · source: r148-report — not yet looked at
- [ ] 43 · b. 6 · p. 107 · current: sketches « à droite » · proposed: in the left half of the page · source: g148-report, g148-settled; drawings.json 06-1 — not yet looked at
- [ ] 43 · b. 9 · p. 177 · current: list of class names and groups · proposed: adds « multiplicatif séparable », « unipotent k-connexe », a second « multiplicatif k-connexe », more instances of groups · source: r148-report — not yet looked at
- [ ] 45 · b. 3 · p. 52 · current: « triviale » and the large curve ending at (iii) · proposed: « triviale » beside (iii′) ⇒ (iii); the curve runs to (i″) · source: gsmallA-report, gsmallA-settled — not yet looked at
- [ ] 46 · b. 2 · p. 30 · current: note on the Frobenius square (class t) · proposed: tikz-cd X ← U over X ← U with Fr_X, Fr_U · source: gsmallA-report — not yet looked at
- [ ] 53 · b. 2 · p. 31 · current: \marginal and note on A ⊗ A (class t) · proposed: tikz-cd A ← A ⊗ A ⇉ k, ε · source: gsmallA-report — not yet looked at
- [ ] 57 · b. 7 · p. 138 · current: « un troisième croquis du même triangle, isolé au bas de la page » · proposed: no such sketch in that part of the page · source: drawings.json 07-2 — not yet looked at
- [ ] 57 · b. 8 · p. 141 · current: asterisk on the first cross of the upper row · proposed: the heavy cross is the first of the lower row · source: drawings.json 08-1 — not yet looked at
- [ ] 57 · b. 14 · p. 267 · current: « quatre triangles adjacents » · proposed: two triangles sharing the vertex (Michel, #136) · source: drawings.json 14-1 — not yet looked at
- [ ] 58 · b. 3 · p. 60 · current: « diagonale » · proposed: an oblique line off the origin · source: gmid-report — not yet looked at
- [ ] 58 · b. 4 · p. 64 · current: vertical stroke through the circle · proposed: runs along its right edge · source: gmid-report — not yet looked at
- [ ] 62 · b. 2 · p. 24 · current: a dot between 0 and 1 · proposed: no dot (paper speck) · source: osmall-report — not yet looked at
- [ ] 62 · b. 3 · p. 56 · current: struck rectangle Δ², Δ³, y, x (class t) · proposed: optional \struck array · source: gsmallA-report — not yet looked at
- [ ] 64 · b. 1 · p. 13 · current: « une flèche courbe au-dessus de s » · proposed: two arrows: a straight one left above a, a curved one down right of s · source: gmid-report; drawings.json 01-5 — not yet looked at
- [ ] 64 · b. 2 · p. 39 · current: « une petite figure en croix portant les lettres x, X » · proposed: a column of letters and rotated writing, no figure · source: gmid-report — not yet looked at
- [ ] 64 · b. 3 · p. 41 · current: two pencilled matrices in the left margin · proposed: (0 1 / 1 0), (1 0 / 0 1), if not transcribed · source: gmid-report — not yet looked at
- [ ] 67 · b. 3 · p. 50 · current: « le pôle ∞ » of the third sphere · proposed: ∞ on the back of the equator; the pole unlabelled · source: g67-report — not yet looked at
- [ ] 67 · b. 3 · p. 56 · current: letter x by the first sketch · proposed: no letter x (a cross in the oval); four hatching strokes · source: g67-report, o67-report — not yet looked at
- [ ] 67 · b. 4 · p. 70 · current: branches ζ, ζ̄ from b · proposed: they do not start from b · source: o67-report — not yet looked at
- [ ] 69 · b. 1 · p. 11 · current: « w‴ » in the description of D₇ · proposed: not on the page as a further vertex; D₇ has seven vertices · source: gmid-report — not yet looked at
- [ ] 69 · b. 1 · p. 16 · current: « une étoile à trois branches dont chaque bout porte un petit triangle » · proposed: a central triangle whose vertices each carry two spikes (Michel, #135) · source: drawings.json 01-14 — not yet looked at
- [ ] 69 · b. 4 · p. 61 · current: « des arcs issus d'un sommet » · proposed: arcs join both the upper and the lower vertex to each of the five points · source: gmid-report — not yet looked at
- [ ] 69 · b. 5 · p. 96 · current: second diagonal matrix (λ₁, λ₁⁻¹, …) unmentioned · proposed: present on the page (Michel, #142) · source: drawings.json 05-12 — not yet looked at
- [ ] 70 · b. 4 · p. 70 · current: trihedron u, V, W · proposed: v lowercase (Michel, #131) · source: drawings.json 04-3 — not yet looked at
- [ ] 71 · b. 1 · p. 2 · current: « deux cercles sécants » · proposed: two lobes sharing a median arc, Γ′₁, Γ′₂, Γ′₃, lower point y · source: g67-report — not yet looked at
- [ ] 71 · b. 1 · p. 10 · current: « un croquis au crayon » (class t) · proposed: two tikz-cd diagrams and a formula (rmisc) · source: g67-report, rmisc-report — not yet looked at
- [ ] 71 · b. 2 · p. 21 · current: thin arcs 1, 2 joining x and y · proposed: each thin line goes from its point of the base to the opposite vertex; x, y ends of a short heavy stroke · source: g67-report, o67-report; drawings.json 02-1 — not yet looked at
- [ ] 71 · b. 2 · p. 23 · current: thin contour · proposed: inside along the left branch, outside at the bottom · source: g67-report — not yet looked at
- [ ] 71 · b. 2 · p. 29 · current: two sketches · proposed: about a dozen · source: g67-report — not yet looked at
- [ ] 71 · b. 2 · p. 31 · current: « à six côtés » · proposed: seven sides · source: g67-report; drawings.json 02-6 — not yet looked at
- [ ] 73 · b. 1 · p. 14 · current: labels of the vertex figure · proposed: also s_{i+1} · source: g67-report — not yet looked at
- [ ] 73 · b. 1 · p. 16 · current: foot sketch, one angle · proposed: two angles · source: g67-report — not yet looked at
- [ ] 73 · b. 1 · p. 18 · current: segments from s_0 to all vertices · proposed: only to s_2, s_4, s_7 · source: g67-report; drawings.json 01-17 — not yet looked at
- [ ] 73 · b. 1 · p. 20 · current: middle sketch « pentagone s_0 … s_4 » · proposed: carries s_{n−1}, s_0, s_1, s_2, s_3 · source: g67-report — not yet looked at
- [ ] 74 · b. 2 · p. 23 · current: α, β, γ by the second cone, square by the first · proposed: α, β, γ in the left cone, the 3 × 3 square by the right one · source: gsmallA-settled — NOT APPLIED (no misreading): the mark pairs α, β, γ with the cone whose top is s′ and the 3 × 3 square with the cone whose top is s, which is what the page shows; it only describes the right-hand cone first.
- [x] 74 · b. 2 · p. 27 · current: label « −r_456 » beside the first figure · proposed: not on the page · source: osmall-report — APPLIED: at 600 dpi the right side carries « r_456 = 3(r_1+r_2+r_3 … » with no minus, the left side no label; the list of sides and its note corrected.
- [x] 74 · b. 3 · p. 43 · current: « un hexagone aux côtés fléchés » · proposed: no arrowheads (Michel, #135) · source: drawings.json 03-1 — APPLIED: no arrowheads, only small hooks; \note after the mark.
- [ ] 74 · b. 3 · p. 44 · current: pairs in braces {1 2} …, {i, i+2} · proposed: pairs between bars ∣12∣ …, no braces (Michel, #135) · source: drawings.json 03-5 — OPEN: at 130 dpi each pair is preceded by one hooked sign (« ʃ12 ʃ34 ʃ15 ʃ23 ʃ45 », « ʃi,i+2 ʃj,j+2 »), a prefix rather than a pair of braces or of bars; it is the same glyph as the one read ξ on p. 27 (ξ_1 ξ_2 ξ_3). Neither the transcription's braces nor the bars of #135 are confirmed; to be decided at higher resolution or by a reader.
- [x] 74 · b. 3 · p. 47 · current: τ_1, τ_2, τ_3 and bars, dotted diagonals · proposed: τ, τ″, τ′ and τ̄, τ̄′, τ̄″; no dotted diagonals visible · source: drawings.json 03-7 — APPLIED: confirmed (τ, τ″, τ′, τ̄′, τ̄″, τ̄; no dotted diagonal); \note after the mark.
- [x] 74 · b. 4 · p. 77 · current: « une étoile formée de deux triangles », « petit hexagone » · proposed: two overlapping squares; small polygon with eight to ten corners · source: osmall-report — APPLIED: at 700 dpi two overlapping squares (eight points) and a polygon of eight to ten ticked corners; \note after the mark.
- [ ] 74 · b. 4 · p. 77 · current: small arrow diagram H_s … e, 𝔖₃ × 𝔖₂ (class t) · proposed: not in the transcription; not read · source: gsmallA-report — OPEN: a relation diagram of about ten nodes (H_s, H_r, H_{r′}, H_{s*}, H_d, H_{tr}, H_{tror}, H_ω, H_{t*}, e) at the foot of the right edge; too small and crowded to read every label at 250 dpi in this pass, so not set.
- [x] 74 · b. 6 · p. 112 · current: s and t above the triangle, one marked point · proposed: below it, each stroke to its own bold point (Michel, #135) · source: drawings.json 06-6 — APPLIED: confirmed; \note after the mark.
- [ ] 75 · b. 1 · p. 5 · current: pencil lens, ink pentagon · proposed: lens heavily inked, pentagon light · source: drawings.json 01-2 — not yet looked at
- [x] 76 · b. 1 · p. 9 · current: note « six petites figures … trois arêtes, l'une hachurée » · proposed: seven figures; last vertex four edges · source: g67-report; drawings.json 01-5 — APPLIED: note corrected to « sept petites figures » and « un sommet d'où partent quatre arêtes, deux épaisses entre lesquelles sont tracées des hachures ».
- [x] 76 · b. 1 · p. 11 · current: \drawing « la flèche D_02 → D_1 barrée d'une croix » · proposed: the crossed arrow is D_02 → D_2 · source: g67-report, g67-settled; drawings.json 01-1 — APPLIED: confirmed (the crossed stroke continues the right leg of the caret under D_02 and stops at D_2); a \note set after the mark. Changes the mathematics: see below.
- [x] 76 · b. 1 · p. 11 · current: note « une flèche vers D_3 » · proposed: a dash before D_3; five strokes under the arc · source: g67-report, o67-report — APPLIED: note corrected (five strokes under the arc, the last closing the tip; a dash, not an arrow, before D_3).
- [ ] 76 · b. 2 · p. 28 · current: \drawing « … « n » » · proposed: last letter H · source: o67-report — OPEN: an H is on the page, but it stands below the row, slanted like the oblique note under it, and may belong to that note; the review line of #128 (76 02-1) is still open.
- [x] 76 · b. 2 · p. 36 · current: note: the bottom struck · proposed: the loop is not struck · source: g67-report — APPLIED: note completed (« que les traits obliques ne touchent pas »).
- [x] 79 · b. 14 · p. 280 · current: schema s, t, u, v with small circles marking vertices · proposed: path s–u–v–t, the circles mark segments (the 0 of A_0) · source: drawings.json 14-2 — APPLIED: confirmed at 250 dpi; \note after the mark.
- [x] 79 · b. 14 · p. 280 · current: sides marked A and A_0 · proposed: A and a small circle; no written A_0 · source: drawings.json 14-3 — APPLIED: confirmed (A on the lower sides and the diagonal, small circles above); \note after the mark.
- [x] 79 · b. 15 · p. 284 · current: s_-, t_- · proposed: s′, t′ (page turned a quarter turn); far-right quadrilateral s, t, t′, λ⁻¹s · source: drawings.json 15-5 — APPLIED: confirmed at 600 dpi, crop turned a quarter turn (s, t, s′, t′; λ⁻¹s at the far right); \note after the mark.
- [ ] 79 · b. 15 · p. 285 · current: ρ⁻¹(s) · proposed: λ⁻¹(s) · source: drawings.json 15-8 — OPEN: at 600 dpi, crop turned 180°, the label under the line λ⁻¹(s) — t — s′ is a loop with a rising stroke, like a ∂; neither a clear λ (compare the λ of the line above it) nor a clear ρ. The mark keeps ρ⁻¹(s).
- [x] 79 · b. 15 · p. 286 · current: « une étoile de six triangles » · proposed: seven triangles (eight spokes, one sector open) · source: drawings.json 15-10 — APPLIED: seven triangles counted, the left sector open; \note after the mark.
- [x] 79 · b. 15 · p. 290 · current: « un pentagone dont tous les sommets sont joints » · proposed: a hexagon with two interlaced triangles · source: drawings.json 15-12 — APPLIED: six corners counted (a short top side); \note after the mark.
- [x] 80 · b. 1 · p. 12 · current: six pseudo-lines, regions 4_1 … 4_6 · proposed: five lines and a short stroke; no 4_4 · source: g31-report; drawings.json 01-5 — APPLIED: confirmed at 200 dpi (five lines and a short stroke; no 4_4); note corrected.
- [x] 80 · b. 1 · p. 13 · current: double primes at the upper corners of the left square · proposed: −1 and +1 · source: g31-report — APPLIED: at 600 dpi the corners carry digits (« −1 », written as if twice, and « 1 » with a stroke read +), not primes; note corrected, both flagged \uncertain.
- [x] 80 · b. 1 · p. 20 · current: six marked points in configuration (5) · proposed: seven · source: g31-report — APPLIED: seven dots counted; note corrected.
- [x] 80 · b. 2 · p. 22 · current: dashed line joining the two vertices · proposed: through the lower vertex only · source: g31-report; drawings.json 02-6 — APPLIED: confirmed; note corrected.
- [x] 80 · b. 2 · p. 24 · current: two ringed points · proposed: three (the diagonal points) · source: g31-report — APPLIED: three ringed points; note corrected.
- [x] 80 · b. 3 · p. 44 · current: « un heptagone » · proposed: a hexagon (Michel, #132) · source: drawings.json 03-1 — APPLIED: six sides and six corners counted; \note set after the mark.
- [x] 80 · b. 3 · p. 53 · current: « une sixième droite » · proposed: the six lines are three sides and three concurrent lines · source: g31-report — APPLIED: confirmed (triangle a, b, c and three lines through d); note corrected.
- [x] 80 · b. 3 · p. 57 · current: small triangle at the centre; four dots · proposed: a square cut by its two diagonals; five dots · source: g31-report; drawings.json 03-7 — APPLIED: confirmed (square cut by its two diagonals; five dots); note corrected.
- [ ] 81 · b. 1 · p. 11 · current: « deux axes fléchés », three disks OK · proposed: only the horizontal axis has a head; four disks marked OK/ok · source: drawings.json 01-2, t83-settled — not yet looked at
- [ ] 81 · b. 2 · p. 26 · current: first sign of the legend ⊃ · proposed: a hooked arrow (Michel, #143) · source: drawings.json 02-3 — not yet looked at
- [ ] 81 · b. 3 · p. 42 · current: « une vingtaine » of points · proposed: 21: 7 full, 14 open (Michel, #142) · source: drawings.json 03-2 — not yet looked at
- [ ] 81 · b. 3 · p. 47 · current: figure « à droite » · proposed: at the left, in the margin (Michel, #143) · source: drawings.json 03-4 — not yet looked at
- [ ] 81 · b. 3 · p. 53 · current: « une double flèche » · proposed: a pair of opposite arrows one above the other (Michel, #143) · source: drawings.json 03-7 — not yet looked at
- [ ] 83 · b. 1 · p. 15 · current: labels u, u_0; v_0 omitted · proposed: v_0 at the right vertex; an overinked u at the centre; no u_0 · source: drawings.json 01-6, t83-settled — not yet looked at
- [ ] 83 · b. 3 · p. 52 · current: « son étoile de diagonales intérieures » · proposed: short broken strokes and dots only · source: drawings.json 03-2 — not yet looked at
- [ ] 83 · b. 11 · p. 204 · current: diagonal i; f, f′ labels · proposed: no diagonal i (a letter); f, f′ are words of the text · source: drawings.json 11-4 — not yet looked at
- [ ] 83 · b. 11 · p. 212 · current: vertex C · proposed: C′ · source: drawings.json 11-6 — not yet looked at
- [ ] 85 · b. 1 · p. 5 · current: two lines and the arc ρ_i · proposed: a third ray from the crossing; ρ_i runs to it · source: g31-report — not yet looked at
- [ ] 85 · b. 2 · p. 33 · current: fork labels · proposed: four labels 1, 0, J′, J · source: g31-report — not yet looked at
- [ ] 85 · b. 2 · p. 35 · current: circle points · proposed: four points · source: g31-report — not yet looked at
- [ ] 85 · b. 3 · p. 49 · current: two closed triangles · proposed: a zigzag of four strokes with small arrows · source: g31-report — not yet looked at
- [ ] 85 · b. 5 · p. 91 · current: Z → Z³ → Z³ in a note · proposed: optional display formula · source: g31-report — not yet looked at
- [ ] 85 · b. 5 · p. 95 · current: E_2 at the foot of the diamond; vertex list; S̃_3 · proposed: F_2; a node A′_3; S̃_3 = S_3 × S′_2 · source: g31-report, g31-settled — not yet looked at
- [ ] 85 · b. 5 · p. 95 · current: lower perspective lattice only in a note · proposed: a figure no mark covers · source: drawings.json 05-2 — not yet looked at
- [ ] 85 · b. 5 · p. 97 · current: middle group of D_3 ↔ ? ↔ D_3 ↔ S_3 × S″_2 read S_3 · proposed: A_3 · source: g31-report, g31-settled — not yet looked at
- [ ] 86 · b. 1 · p. 6 · current: outer letter a″ · proposed: c′ · source: g67-report — not yet looked at
- [ ] 86 · b. 1 · p. 7 · current: pencil frame « un cube » · proposed: not legible as a cube · source: g67-report — not yet looked at
- [ ] 86 · b. 2 · p. 29 · current: margin sketch of the diagram of p. 31 (class t) · proposed: tikz-cd proposed, to check against p. 31 · source: g67-report — not yet looked at
- [ ] 86 · b. 2 · p. 30 · current: « le sommet du bas » · proposed: the lower left vertex · source: g67-report — not yet looked at
- [ ] 87 · b. 2 · p. 29 · current: « quatre segments » · proposed: five (two heavy, three thin) · source: gmid-report, gmid-settled; drawings.json 02-1 — not yet looked at
- [ ] 87 · b. 2 · p. 30 · current: « pentagone » · proposed: six corners · source: gmid-report — not yet looked at
- [ ] 87 · b. 2 · p. 40 · current: hatched fan and bar with heavy ends · proposed: not in the transcription · source: omidA-report — not yet looked at
- [ ] 104 · b. 1 · p. 1 · current: « deux, trois puis quatre marques » · proposed: 3, 4, 5 marks counting the ends · source: gmid-report — not yet looked at
- [ ] 104 · b. 1 · p. 3 · current: four figures · proposed: six (a segment and an open rectangle besides) · source: gmid-report — not yet looked at
- [ ] 105 · b. 2 · p. 26 · current: arrow diagrams in a note (class t) · proposed: tikz-cd for the upper two thirds · source: gsmallB-report, rmisc-report — not yet looked at
- [ ] 106 · b. 1 · p. 2 · current: « presque aucun n'est étiqueté » (class t) · proposed: most carry letters; tikz-cd for the centre and top left · source: gsmallB-report, rmisc-report — not yet looked at
- [ ] 106 · b. 1 · p. 7 · current: note (class t) · proposed: two tikz-cd · source: gsmallB-report — not yet looked at
- [ ] 106 · b. 1 · p. 15 · current: note (class t) · proposed: two tikz-cd · source: gsmallB-report — not yet looked at
- [ ] 107 · b. 1 · p. 14 · current: « trois traits parallèles joignant X_{n-2} à X_{n-1} » (class t) · proposed: a triple arrow · source: gsmallB-report — not yet looked at
- [ ] 117 · b. 1 · p. 2 · current: 2-cells x ⇉ y (class t) · proposed: tikz-cd with a 2-arrow · source: gsmallB-report — not yet looked at
- [ ] 118 · b. 1 · p. 18 · current: note (class t) · proposed: tikz-cd u, y, u′, y′ · source: gsmallB-report — not yet looked at
- [ ] 118 · b. 1 · p. 19 · current: base-change cube (class t) · proposed: tikz-cd with crossing over · source: gsmallB-report — not yet looked at
- [ ] 121 · b. 1 · p. 1 · current: cover diagrams (class t) · proposed: three tikz-cd · source: rmisc-report — not yet looked at
- [ ] 121 · b. 3 · p. 41 · current: right diagram (class t) · proposed: ∂V_1 = V_10 → V_0, ↓ V_1 · source: gsmallB-report — not yet looked at
- [ ] 121 · b. 3 · p. 42 · current: level-2 schemas (class t) · proposed: three tikz-cd; π_{2,1,2} and ∂π_{2,1,1} · source: rmisc-report — not yet looked at
- [ ] 121 · b. 3 · p. 46 · current: staircases (class t) · proposed: two tikz-cd, and the display ∂(∂_j V_i°) · source: rmisc-report — not yet looked at
- [ ] 127 · b. 1 · p. 4 · current: label G_n by the brace · proposed: G_{U_n}; X_n, Y_n hooked strokes · source: gsmallB-report — not yet looked at
- [ ] 127 · b. 1 · p. 11 · current: T′ → T above X′ → X · proposed: below it, no visible arrowhead · source: gsmallB-report; drawings.json 01-4 — not yet looked at
- [ ] 129 · b. 5 · p. 99 · current: two ladders (class t) · proposed: both the same filtration, braces; display proposed · source: gsmallB-report, rmisc-report — not yet looked at
- [ ] 129 · b. 6 · p. 107 · current: « un triangle C → C, u ↑, C → » (class t) · proposed: tikz-cd C –F→ C, u, V · source: gsmallB-report — not yet looked at
- [ ] 129 · b. 6 · p. 107 · current: pencil of rays · proposed: twelve rays and a separate tick · source: osmall-report — not yet looked at
- [ ] 135 · b. 1 · p. 4 · current: « F × Γ » and a « griffonnage » · proposed: Γ × Γ; a formula π_0 × π_0 → Γ × Γ →φ π_1 · source: gsmallB-report — not yet looked at
- [ ] 135 · b. 2 · p. 35 · current: trial squares out of reach (class t) · proposed: three staircases, square, conditions read; ΩB not ΩD; Γ_q → Γ_f; d) not [a)] · source: rmisc-report — not yet looked at
- [ ] 136 · b. 2 · p. 36 · current: box « g, g′, gh » · proposed: G, g_1, …, g_k · source: gsmallB-report, gsmallB-settled — not yet looked at
- [ ] 136 · b. 17 · p. 337 · current: « hexagone de flèches » · proposed: a diamond of four nodes and four arrows (17-2, 17-3) · source: drawings.json 17-2 — not yet looked at
- [ ] 137 · b. 2 · p. 39 · current: « une colonne de petits complexes » (class t) · proposed: five lines of running text along the margin · source: rmisc-report — not yet looked at
- [ ] 138 · b. 4 · p. 77 · current: j, j̄ (« signes douteux ») · proposed: −j, −j̄ · source: drawings.json 04-8 — not yet looked at
- [x] 140-1 · b. 1 · p. 18 · current: five curves · proposed: four · source: omidB-report — APPLIED: four curves counted at 400 dpi where they leave the common point; note corrected (the mark, which says cinq, is followed by the note's correction).
- [ ] 141 · b. 1 · p. 9 · current: « deux points marqués » · proposed: three · source: gmid-report; drawings.json 01-2 — not yet looked at
- [ ] 141 · b. 1 · p. 14 · current: labels of the back arc · proposed: 2, 1, 3 (review line kept) · source: gmid-report — not yet looked at
- [x] 142 · b. 3 · p. 51 · current: incisions from P_ε at the top · proposed: from the bottom pole P_ε′ · source: drawings.json 03-2 — APPLIED: confirmed (the heavy strokes rise from P_ε′ at the bottom to the holes); \note after the mark.
- [x] 142 · b. 3 · p. 52 · current: « le graphe d'un octaèdre » · proposed: a triangular bipyramid (five vertices) · source: drawings.json 03-3 — APPLIED: confirmed (P_ε, P_ε′, Q_i, Q_j, Q_k: five vertices); \note after the mark. Changes the mathematics: see below.
- [x] 142 · b. 6 · p. 107 · current: « β relevé » once · proposed: twice · source: drawings.json 06-7 — APPLIED: confirmed; \note after the mark.
- [x] 142 · b. 6 · p. 109 · current: (a_1^- a_1^+)^{-1} · proposed: (a_1^{--} a_1^{-+}) · source: drawings.json 06-9, t142-settled — APPLIED: confirmed at 450 dpi, crop turned 180° (a₁⁻⁻ a₁⁻⁺, no exponent −1); \note after the mark.
- [ ] 144 · b. 3 · p. 54 · current: « dix triangles-repères » · proposed: nine · source: drawings.json 03-4 — not yet looked at
- [ ] 144 · b. 7 · p. 125 · current: M^{!∘}, M^∘ plain · proposed: underlined · source: drawings.json 07-1 — not yet looked at
- [ ] 144 · b. 7 · p. 133 · current: list of the cube · proposed: adds Π′ in the second row · source: drawings.json 07-7 — not yet looked at
- [ ] 144 · b. 7 · p. 135 · current: list of the variant · proposed: adds S (overwritten middle node) · source: drawings.json 07-8 — not yet looked at
- [ ] 144 · b. 7 · p. 139 · current: middle line of the fair copy · proposed: adds a node M under Z^!_{0ρ} (Michel, #135) · source: drawings.json 07-11 — not yet looked at
- [x] 146 · b. 1 · p. 19 · current: « quatre petits cercles fléchés » · proposed: five · source: drawings.json 01-5 — APPLIED: five arrowed loops counted; \note after the mark.
- [x] 146 · b. 2 · p. 23 · current: Q_+ at the top, Q_- at the bottom · proposed: Q_- at the top, Q_+ at the bottom · source: drawings.json 02-2, t83-settled — APPLIED: at 600 dpi the top label is Q with a bare dash (no vertical stroke), the bottom one Q with a +; \note after the mark.
- [x] 146 · b. 4 · p. 65 · current: « un hexagone (deux triangles accolés …) » · proposed: a pentagon whose centre is joined to its five vertices (Michel, #142) · source: drawings.json 04-6 — APPLIED: confirmed (five vertices, centre joined to each); \note after the mark.
- [x] 146 · b. 4 · p. 66 · current: « segment épais de 0 à 0, 1 au milieu, ∞ au fond », « grande ellipse avec ∞ » · proposed: a thin line through ∞ (sideways), 0, 1?; no ellipse in this region · source: drawings.json 04-9, t83-settled — APPLIED in part: the thin line through ∞ (sideways), 0 and a small stroke is confirmed (\note after the mark). Not applied: « no ellipse with ∞ in this region » — at 150 dpi an ellipse with ∞ at its end stands at the right of the same region, so the mark's « grande ellipse avec ∞ » is kept.
- [x] 146 · b. 7 · p. 124 · current: triangle « a » at the top vertex · proposed: the right side bends at a vertex labelled a (Michel, #142) · source: drawings.json 07-2 — APPLIED: confirmed at 500 dpi (a labels the vertex where the right side bends; the top vertex is unlabelled); \note after the mark.
- [ ] 147 · b. 4 · p. 73 · current: schema struck · proposed: not struck · source: gsmallB-report — not yet looked at
- [ ] 147 · b. 5 · p. 97 · current: graph · proposed: a short free segment leaves the third vertex · source: drawings.json 05-3 — not yet looked at
- [ ] 148 · b. 1 · p. 4 · current: rhombus « étiqueté V_S » · proposed: no label on the sketch · source: g148-report; drawings.json 01-7 — not yet looked at
- [ ] 148 · b. 1 · p. 17 · current: barycentric subdivision in red · proposed: medial triangles and segments to opposite vertices · source: drawings.json 01-5 — not yet looked at
- [ ] 148 · b. 1 · p. 17 · current: arrow from « un grand tétraèdre tronqué » · proposed: from the middle, untruncated tetrahedron · source: g148-report; drawings.json 01-12 — not yet looked at
- [ ] 148 · b. 2 · p. 22 · current: rotation arrow round the marked vertex · proposed: heavy arrow round the right vertex; pencil arc over the top · source: g148-report; drawings.json 02-2 — not yet looked at
- [ ] 148 · b. 2 · p. 23 · current: two curled signs · proposed: three · source: r148-report — not yet looked at
- [ ] 148 · b. 2 · p. 25 · current: sign in the loop · proposed: ± · source: r148-report — not yet looked at
- [ ] 148 · b. 2 · p. 27 · current: numerals 1–6 inside the cap; triangle labels · proposed: 5, 6, 4, 2, 3 inside, 4′…3′ around, a 6 below; a, b_a, c_a, c_b, a′ · source: r148-report — not yet looked at
- [ ] 148 · b. 2 · p. 30 · current: II_1 labels · proposed: 1, ∞, u_5, u_4, u_3, u_0, u_1, u_2, 0, P · source: r148-report — not yet looked at
- [ ] 148 · b. 2 · p. 31 · current: three points on the equator · proposed: two on it and one above · source: g148-report — not yet looked at
- [ ] 148 · b. 2 · p. 32 · current: « about seven and six » rim marks · proposed: 8 dots, 6 stars, ~12 ticks · source: r148-report — not yet looked at
- [ ] 148 · b. 2 · p. 35 · current: central edge barred · proposed: the free edge of the middle vertex · source: g148-report; drawings.json 02-18 — not yet looked at
- [ ] 148 · b. 3 · p. 46 · current: vertex 0 under 2° with two free edges · proposed: three · source: drawings.json 03-1 — not yet looked at
- [ ] 148 · b. 4 · p. 66 · current: region A_{∞1} · proposed: not found · source: drawings.json 04-1 — not yet looked at
- [ ] 148 · b. 4 · p. 69 · current: « un décalque au crayon du dessin de la page 68 » · proposed: show-through of p. 68 · source: g148-report; drawings.json 04-6 — not yet looked at
- [ ] 148 · b. 4 · p. 70 · current: tracing of p. 71 · proposed: show-through of p. 71 · source: g148-report — not yet looked at
- [ ] 148 · b. 4 · p. 71 · current: nine ringed vertices, nine red curves · proposed: eleven and eight (Michel, #142) · source: drawings.json 04-2 — not yet looked at
- [ ] 150 · b. 4 · p. 72 · current: strokes from the centre · proposed: only the middle stroke starts at the centre · source: gsmallB-report — not yet looked at
- [ ] 151 · b. 3 · p. 53 · current: generators to a and b · proposed: the one to b is dashed; the one to a has a gap · source: omidB-report — NOT APPLIED (nothing to correct): the transcription only says the two generators oa and ob are marked, and does not say which is broken; at 400 dpi the course of the dashes is consistent with the report but the text needs no change.
- [x] 151 · b. 3 · p. 58 · current: labels X_i, X_i^*, R_ij et C_ij · proposed: C_ij not in the sketch · source: gmid-report — APPLIED: X_i, X_i^*, R_ij read in and around the sketch at 300 dpi, no C_ij; note corrected.
- [x] 152 · b. 1 · p. 1 · current: « sept rayons » · proposed: four inked rays · source: omidB-report — APPLIED: at 500 dpi four ink strokes leave the centre; the other lines are long pencil lines across the sheet; \note set before the mark (its record keeps « sept »).
- [x] 152 · b. 1 · p. 1 · current: « chacun des deux cadres est suivi d'un petit cercle … » · proposed: both small circles inside the first frame · source: rmisc-report — APPLIED: confirmed (both small circles inside the first frame, at the ends of its two lines; nothing after the second frame, a faint circle under it); note rewritten.
- [x] 152 · b. 1 · p. 3 · current: « deux disques reliés par une arête »; five discs · proposed: that pair is at the foot; five discs of the right half unmentioned; two vertices of the dual tree · source: gmid-report — APPLIED: confirmed at 80 dpi (the linked pair is at the foot; five smaller discs at the right; two heavy points with a stroke each inside the large disc); note rewritten.
- [x] 152 · b. 1 · p. 10 · current: « trois cordes » · proposed: eight · source: gmid-report; drawings.json 01-4 — APPLIED: eight chords counted; note corrected.
- [ ] 154 · b. 1 · p. 4 · current: figure « en haut à droite » · proposed: mid-height of the right half · source: drawings.json 01-4 — not yet looked at
- [ ] 154 · b. 1 · p. 11 · current: three points between r and t · proposed: four marked points: r, two unnamed, t · source: g154-report — not yet looked at
- [ ] 154 · b. 1 · p. 19 · current: points a and a′ · proposed: the lower marginal point is a′ · source: drawings.json 01-13, t154a-settled — not yet looked at
- [ ] 154 · b. 1 · p. 20 · current: D labelled · proposed: no label D · source: drawings.json 01-14 — not yet looked at
- [ ] 154 · b. 2 · p. 21 · current: six fans; « en haut à gauche » · proposed: seven crossings; top of the right half · source: drawings.json 02-1 — not yet looked at
- [ ] 154 · b. 2 · p. 23 · current: two orange strokes · proposed: three · source: g154-report — not yet looked at
- [ ] 154 · b. 2 · p. 26 · current: labels round the point of concurrence · proposed: p−1, q, p≥4, q≥3; p′−1, q′, p′≥1, q′≥3 (Michel, #142) · source: drawings.json 02-6 — not yet looked at
- [ ] 154 · b. 3 · p. 43 · current: orange; a), b), c) · proposed: red-orange; label of a) « -) »; order b), a), c) · source: drawings.json 03-2 — not yet looked at
- [ ] 154 · b. 3 · p. 46 · current: two green lines · proposed: one horizontal and two vertical · source: drawings.json 03-3 — not yet looked at
- [ ] 154 · b. 3 · p. 56 · current: pentagon and quadrilateral · proposed: hexagon and rectangle (Michel, #132) · source: drawings.json 03-8 — not yet looked at
- [ ] 154 · b. 4 · p. 72 · current: « n − 1 », « (n−1) − (N−1) − (N′−1) » · proposed: « n − ν », « (n−1) − (ν−1) − (ν′−1) » · source: g154-report; drawings.json 04-12 — not yet looked at
- [ ] 154 · b. 5 · p. 87 · current: crossings · proposed: all above D · source: g154-report — not yet looked at
- [ ] 154 · b. 5 · p. 91 · current: D labelled · proposed: no label D · source: drawings.json 05-3 — not yet looked at
- [ ] 154 · b. 6 · p. 113 · current: curves in the circle; pencil eight · proposed: two spindles; two spindles above, one curve below · source: r154c-report — not yet looked at
- [ ] 154 · b. 7 · p. 124 · current: two thick red arcs « sur le bord » · proposed: the ends of one chord inside the rim · source: t154c-settled — not yet looked at
- [ ] 154 · b. 7 · p. 128 · current: « étoile bleue à huit branches », « hexagone vert » · proposed: seven branches; a pentagon · source: g154-report, g154-settled — not yet looked at
- [ ] 154 · b. 7 · p. 130 · current: lower tangent disk · proposed: red strands do not close; three strands meet at a dotted point · source: r154c-report — not yet looked at
- [ ] 154 · b. 7 · p. 132 · current: small strokes near the axis ends · proposed: arrows · source: r154c-report — not yet looked at
- [ ] 154 · b. 7 · p. 134 · current: upper drawing · proposed: two orange strokes, small arrow ω, no arrowhead on the green · source: r154c-report — not yet looked at
- [ ] 154 · b. 7 · p. 140 · current: named points e_10, a_0 · proposed: e_10 struck; a_0 = blotted a_1; a_5, a_7, a_11, b_11, b_2, c_9, c_10 missing · source: r154a-report — not yet looked at
- [ ] 154 · b. 8 · p. 144 · current: arrow tree beside the table of words (class t) · proposed: third column of couples in the array · source: g154-report — not yet looked at
- [ ] 154 · b. 8 · p. 145 · current: brown path « flèches numérotées 1 à 19 » · proposed: the numbers are on the crossings; sweep words σ_i · source: r154a-report, o145-report — not yet looked at
- [ ] 154 · b. 8 · p. 146 · current: four disks · proposed: five · source: g154-report — not yet looked at
- [ ] 154 · b. 8 · p. 147 · current: circled groups · proposed: 1,2,3,4; 8,9; 12,13,14; 14,15–16; 14,15; 18,19 twice · source: r154a-report — not yet looked at
- [ ] 154 · b. 8 · p. 150 · current: ω_L · proposed: ϖ_L (Michel, #132) · source: drawings.json 08-6 — not yet looked at
- [ ] 154 · b. 8 · p. 151 · current: « huit rayons »; numbers of the first green disk · proposed: twelve rays; a seventh number 11 · source: g154-report, g154-settled, r154c-report — not yet looked at
- [ ] 154 · b. 8 · p. 154 · current: (I_n) vertices · proposed: seven, as « n = 7 » says · source: g154-report — not yet looked at
- [ ] 154 · b. 8 · p. 156 · current: pencilled legend under the source of ρ_f; pairs « ou » · proposed: a legend « prenons lien de triangles » (uncertain); a fourth pair at the top right · source: r154d-report — not yet looked at
- [ ] 154 · b. 8 · p. 159 · current: δ′ in F′; F with δ and s · proposed: δ; a t below s · source: t154d-settled — not yet looked at
- [ ] 154 · b. 9 · p. 163 · current: four light green curves · proposed: three · source: g154-review, t154d-settled — not yet looked at
- [ ] 154 · b. 9 · p. 165 · current: « un réseau de courbes » · proposed: six curves, twelve marked ends · source: r154b-report — not yet looked at
- [ ] 154 · b. 9 · p. 168 · current: dark green arc « entre α_2 et α_3 »; chain of circles · proposed: from the left corner to an end labelled α_2; six circles · source: r154b-report — not yet looked at
- [ ] 154 · b. 9 · p. 169 · current: « une moitié renforcée en vert foncé » · proposed: about a third · source: r154b-report — not yet looked at
- [ ] 154 · b. 9 · p. 172 · current: small triangles · proposed: four short pencil strokes (Michel, #143) · source: drawings.json 09-8 — not yet looked at
- [ ] 154 · b. 9 · p. 173 · current: « un cercle vert clair »; petals; corners · proposed: a ring of 8 bars and 8 lenses; sixteen petals; sixteen radial bars · source: r154b-report — not yet looked at
- [ ] 154 · b. 9 · p. 175 · current: grey dashed line · proposed: two dark green and one blue dashed lines · source: r154b-report — not yet looked at
- [ ] 156-1 · b. 2 · p. 25 · current: marginal figure x, t, y (class t) · proposed: tikz-cd x ⇄ y with t · source: gsmallB-report — not yet looked at
- [ ] 156-4 · b. 3 · p. 51 · current: third top node F̄′ · proposed: F⃗ (Michel, #142) · source: drawings.json 03-3, t83-settled — not yet looked at
- [ ] 156-4 · b. 4 · p. 72 · current: sign « surchargé et barré » · proposed: overwritten, not struck · source: drawings.json 04-1 — not yet looked at
- [ ] 156-6 · b. 5 · p. 88 · current: point « près d'un sommet » · proposed: on the left side, about its middle · source: drawings.json 05-3 — not yet looked at
- [ ] 156-7 · b. 1 · p. 8 · current: « diamètre vertical, avec de petites croix » · proposed: oblique diameter (the diagonal); two crosses · source: drawings.json 01-3 — not yet looked at
- [ ] 156-7 · b. 4 · p. 70 · current: first segment « subdivisé en deux » · proposed: two interior ticks (three pieces) · source: drawings.json 04-1 — not yet looked at
- [ ] 158 · b. 4 · p. 61 · current: bottom-left diagram B, C, ∘, β, γ (class t) · proposed: not in the transcription; tikz-cd proposed · source: gsmallB-report — not yet looked at
- [ ] 161-2 · b. 3 · p. 47 · current: mark below the ovals · proposed: may be the letter V (review line) · source: osmall-report — not yet looked at
- [ ] 161-2 · b. 3 · p. 49 · current: note (class t) · proposed: tikz-cd A × Π_n … · source: gsmallB-report — not yet looked at
- [ ] 161-2 · b. 3 · p. 51 · current: base-change sketches (class t) · proposed: two tikz-cd · source: rmisc-report — not yet looked at
- [ ] 161-2 · b. 3 · p. 52 · current: marginal sketch (class t) · proposed: tikz-cd M → N, A → B, f, g, Y ← X · source: rmisc-report — not yet looked at
- [ ] 161-6 · b. 1 · p. 12 · current: « cinq rayons » · proposed: six strokes · source: g1616-report — not yet looked at
- [ ] 161-6 · b. 1 · p. 16 · current: graph on six vertices; u_1, u_0 in the two innermost ovals · proposed: eight vertices (the cube); both in the innermost of three · source: g1616-report — not yet looked at
- [ ] 161-6 · b. 1 · p. 17 · current: vectors u, v from the centre · proposed: the heavy stroke runs from 0 to u, v starts at u · source: g1616-report — not yet looked at
- [ ] 161-6 · b. 1 · p. 18 · current: A_2 … A_3 in the cyclic order · proposed: A_3 at the bottom, A_2 at the left · source: g1616-report; drawings.json 01-5 — not yet looked at
- [ ] 161-6 · b. 1 · p. 19 · current: « trois vecteurs issus d'un point », « un décagone » · proposed: two ink figures of four strokes each; eight corners · source: g1616-report — not yet looked at
- [ ] 162-5 · b. 2 · p. 21 · current: \marginal (class t) · proposed: tikz-cd X_2 ⇛ X_1 ⇉ X_0 with curved arrows up · source: rmisc-report — not yet looked at

## Readings that change the mathematics: for /modernize-grothendieck and /find-novelty

- **76 p. 11** (batch 1): the arrow barred by a cross in the lattice of flags for n = 2 is D_02 → D_2, not D_02 → D_1. `76.modern.tex` (about l. 593) says « La flèche D_{02} → D_1 est barrée … : il n'y a pas de restriction de D_{0,2} vers D_{1} ». With D_02 → D_2 crossed, that gloss no longer holds, and by the page's own rule (D_I → D_J epi when J ⊂ I has the same top element) D_02 → D_2 is an epimorphism: the cross is more likely a cancellation of the stroke than a statement. To be rewritten by /modernize-grothendieck; no finding of `src/content/findings.ts` cites this arrow (checked by grep on 76).
- **80 pp. 12 and 57** (batches 1 and 3): five pseudo-lines (not six; regions 4_1, 4_2, 4_3, 4_5, 4_6, no 4_4) on p. 12; on p. 57 the six lines meet in a central square cut by its two diagonals, not a small triangle. `80.modern.tex` l. 698–699 and l. 1659 repeat the old readings (« six pseudo-droites … six régions 4_1, …, 4_6 », « un petit triangle entouré de triangles »); to be corrected by /modernize-grothendieck. p. 44: the cyclic figure of « u_0(i) = i+1 » is a hexagon, not a heptagon (check the modern reading if it draws a count from it).
- **142 p. 52** (batch 3): the graph along whose cycles the isomorphisms (30) compose is a triangular bipyramid (two poles P_ε, P_ε′, three Q_i on the equator; five vertices), not an octahedron. `142.modern.tex` l. 1065 says « le long des cycles du graphe de l'octaèdre (deux pôles, trois Q_i) »: the parenthesis is right, the name is not; to be corrected by /modernize-grothendieck (and any finding of `findings.ts` on folder 142 that names the octahedron should be checked by /find-novelty).
- **142 p. 109** (batch 6): the inscription in the loop above the circle of 1 is (a₁⁻⁻ a₁⁻⁺), not (a₁⁻ a₁⁺)⁻¹. Only the \drawing description carried it; the modern reading does not quote it (grep), nothing to rewrite unless it is drawn on later.

