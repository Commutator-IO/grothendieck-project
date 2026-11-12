# Doubtful drawings of issue #128 (2026-11-09)

These are the drawings redrawn for #128 that the redraw could not settle alone. For each one, the question is
put to the reader against the facsimile. `scripts/review-queue.mjs` reads this file, one item per bullet,
as kind `drawing`. The bullet's format is:

`- [ ] <cote> <id> | <type> | <question> | <current reading> | <alternative reading>`

The types are:

- `reading`: the redraw reads something the page leaves unclear;
- `disagreement`: the drawing and the transcription read the page differently;
- `strike`: what Grothendieck struck out, and so what the redraw left out.

The last field is empty when there is no alternative. Tick a box when its answer is applied. The answer
goes in the drawing's record in `transcripts/<cote>/drawings/drawings.json`, not in the transcription,
which only the transcription skill edits.

## En priorité : figures du livre « Vers une géométrie des formes » à marquer et redessiner

Ces figures sont décrites par une note de la transcription, sans marque `\drawing` : elles n'ont donc pas encore de dessin. Le livre de lecture les signale par un cadre « Figure à redessiner ». Pour chacune, dire si la description correspond à la page ; la figure sera ensuite marquée dans la transcription et redessinée (type `missing`, identifiant `p<page>`).

- [x] 156-2 p2 | missing | Is there a sketch above the line, linked to Ẇ_t (the tubular neighbourhood, its interior and its boundary)? | petit croquis au-dessus de la ligne, relié à Ẇ_t par un trait |
- [x] 156-2 p4 | missing | Is there a small circle marked with two points under the note? | un petit cercle marqué de deux points |
- [x] 156-5 p27 | missing | Is the « croquis » of the note anything other than the arrow diagram S ↪ 𝓛 ↩ S′ already set in the text? | No sketch: the note describes the tikz-cd diagram of the text; K appears only in the formula K = Im(S∩T → I×J) | A separate sketch of I × I′ with the corner K, to mark and redraw
- [x] 156-7 p77 | missing | Is there a small overwritten triangle linked to a circled (2) in the margin of the last line? | No sketch seen: the looped descender of the « f » of « fait » and faint grey traces | A pencil renvoi sign, as the note says
- [x] 156-6 p35 | missing | Is the small circle before « de ce type » a disk with a marked point? | un petit cercle contenant un signe, sans doute le disque à point marqué |
- [x] 156-6 p88 | missing | Is there a small triangle with a point marked near a vertex, and a small circle at the end of the parenthesis? | un petit triangle, un point marqué près d'un sommet ; un petit cercle |
- [x] 156-7 p8 | missing | Is the margin drawing a rhombus containing a circle cut by a vertical diameter, with small crosses around? | losange contenant un cercle coupé par un diamètre vertical, petites croix autour |
- [x] 156-7 p69 | missing | Are there three sketches on the left: for b) a segment X and a point Y at its end; for c) two segments X, Y apart, « ou » end to end? | trois petits croquis de segments et de points |
- [x] 156-7 p71 | missing | Does the sentence end on a subdivided segment with points a₁, a₂, …, aₙ? | un segment subdivisé, points a₁, …, aₙ |

## En priorité : pages citées par les preuves de l'article Lean

Toutes les questions de ce bloc ont reçu réponse (#131, #132) et sont appliquées. Les cases cochées restent ici pour garder les identifiants des questions ; les dessins à revoir après ces réponses sont en tête de « Folder 154 ».

- [x] 80 03-1 | disagreement | Is it a heptagon? | A hexagon with six arrowed sides; the seventh vertex only suggested by dots outside it | A heptagon, as in the transcription
- [x] 72 05-1 | reading | Is this the network meant (relocated: four rising and four descending lines, a centre node, a rounded frame)? | As redrawn; the index couples at the nodes left out | 
- [x] 154 01-12 | reading | How far does the faint pencil hatching of the top sector extend? | 7 strokes and a boundary arc | A whole hatched sector
- [x] 34 09-1 | disagreement | Is there an inclusion sign between X̄ and X̄|U? | Not visible, not drawn | ⊃, as in the transcription
- [x] 154 03-8 | disagreement | What are the upside-down annotations around the green circle? | Left 1/2 and γ, right 1/2 and 1 | « 1/2, 1/1, 1 », as in the transcription; the left sign may be λ
- [x] 154 03-8 | reading | Where does the hexagon's diagonal end? | Where it meets the right side | At the dot just left of the vertex 3, with the vertex there
- [x] 154 03-8 | reading | Is the curl at the hexagon's top vertex a label « 2 »? | A plain vertex, no label | A label « 2 »
- [x] 154 08-6 | disagreement | Is the orientation of L written ω_L or ϖ_L? | ϖ_L: a bar is visible | ω_L, as in the transcription
- [x] 154 08-8 | reading | Are the net lines orange in two families, with dark brown ink over parts of them, dots at the crossings and arrowheads? | The current file draws ten brown straight lines | Orange lines with dark-ink zigzag paths, dots and arrowheads, as on the facsimile
- [x] 154 08-8 | reading | Is the right-hand strand B7 one curved strand, or two meeting at the P6 crossing? | Not yet drawn | Possibly two


## Folder 70


## Folder 154

- [x] 154 02-2 | reading | Do the three orange lines meet at the apex of the dashed arc? | Yes, with a black point drawn there | 
- [x] 154 01-7 | reading | Does the snapped drawing still match the page? | As redrawn | 
- [x] 154 06-8 | reading | Does the snapped drawing still match the page? | As redrawn | 
- [x] 154 08-3 | reading | Does the snapped drawing still match the page? | As redrawn | 
- [x] 154 08-4 | reading | Does the snapped drawing still match the page? | As redrawn | 
- [x] 154 02-6 | reading | Does the snapped drawing still match the page? | As redrawn | 
- [x] 154 07-4 | reading | Should these nearby stroke ends meet at one corner? | Merged into one corner | Separate ends
- [x] 154 06-16 | reading | Should these nearby stroke ends meet at one corner? | Merged into one corner | Separate ends
- [x] 154 02-5 | reading | At the four antipodal blue marks, are the strands paired right? | The two near-vertical strands and the two near-horizontal ones meet only at the marks | 
- [x] 154 02-9 | reading | On the right, near the small yellow region, which strand continues which? | The upper-left strand goes on to the lower-right rim, the top strand to the dark green arc; one strand ends at that crossing | 
- [x] 154 02-9 | disagreement | How many small triangles are there near the rim? | Five orange wedges at the rim, plus five small regions inside | Six, as in the transcription
- [x] 154 02-14 | reading | In the lower isolated disk, are the strands paired right, and are the pencil ticks rightly left out? | As redrawn | 
- [x] 154 09-4 | reading | In the left disk, is the dashed path a closed loop along the strands, with three triple points? | Yes | 
- [x] 154 09-7 | disagreement | Which labels does the orange disk carry? | Also 4, 4′, 5′, 6, 7, 7′, 8, 9′ | Only 1, 2, 3, 1′, 2′, 3′, 5, 6′, 8′, 9, as in the transcription
- [x] 154 09-7 | disagreement | How many blue arcs has the pencil circle? | Three, plus a pencil arrowhead on the right | Four, as in the transcription
- [x] 154 09-7 | disagreement | In what order do the small disk's labels run, from the top? | 1, 0, 4, 5, …, 9, as in the sequence written above it | 9, 0, 1, 2, 3, 4, as in the transcription
- [x] 154 02-15 | reading | In disk A, does the short solid strand from the top rim end where D₁ crosses the dashed strand? | Yes | 
- [x] 154 02-15 | reading | In disk B, does a short solid stroke run from D₀ to the right-hand dashed strand, closing the hatched region? | Yes | 
- [x] 154 02-15 | reading | In disk D, does a solid strand start on the lower dashed strand, cross D₀ once and reach the bottom rim? | Yes | 
- [x] 154 08-8 | reading | Does the spindle redrawn from the crop (mango-shaped outline, pointed at both ends, the net as read) match the page now? | As redrawn on 9 November after #132 | 
- [x] 154 08-4 | reading | Does the sphere redrawn from the crop match the page? | As redrawn on 9 November after #134 | 
- [x] 154 02-6 | disagreement | What are the labels around the star? | Read upright: p−1, q, p≥1, q≥3 on one side, p′−1, q′, p′≥1, q′≥3 on the other | b, b−1, b+1, b±2, as in the transcription
- [x] 154 02-6 | disagreement | What are the two labels under the V on the green line? | 4 and 4, the same glyph as the 4s of the spindles | b, as in the transcription
- [x] 154 02-6 | reading | In the right group, does the third line of the pencil at Q pass through the crossing of the other two? | Drawn concurrent | Not concurrent, a gap of about 1 unit
- [x] 154 05-1 | reading | Are the grey pencil lines strands of the arrangements, or the underdrawing? | Not yet decided; the drawing is left as it was | 

## Folder 74

- [x] 74 03-1 | reading | Do the hexagon's sides end in arrowheads? | Yes, small hooks read as arrowheads | No arrowheads, as in the earlier redraw
- [x] 74 03-5 | disagreement | Is the glyph a ξ or a pair of braces? | ξ, the same glyph as elsewhere on the page | Braces {1 2} … {i, i+2}, as in the transcription
- [x] 74 03-4 | disagreement | Where are the labels ξ12, ξ25, … and x1…x6? | ξ on the upper hexagon's vertices, x1…x6 on the lower | Pairs beside two hexagons on x1…x6, as in the transcription
- [x] 74 03-4 | reading | Is the upper figure a graph on the six pairs, with edges between the labels and no hexagon? | Yes: on the page the strokes run between the six labels ζ_ij, with no hexagon and no dots, as the current drawing has it. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 74 03-4 | reading | In the lower figure, is x1 joined to x4 (and not to x2)? | Yes: x1 is joined to x4 by a long line and x2 to x6; only a short doubled stroke points from x1 towards x2, as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 74 03-4 | reading | p. 44, lower left figure: are the overwritten values after « x4 = » and « x3 = » the pairs ζ16 and ζ24 written cleanly just to their right? | Left out as unread (« = ζ » only) | x4 = ζ16, x3 = ζ24 (and x5, x6 unread)
- [x] 74 03-7 | disagreement | What are the labels? | τ, τ′, τ″ and their bars; no dotted diagonals visible | τ1, τ2, τ3 with dotted diagonals, as in the transcription
- [x] 74 04-3 | disagreement | Where is k, and which vertices is u joined to? | k at the bottom left; u joined to j, q, r | A rectangle i p q k, u joined to p, q, r
- [x] 74 06-6 | disagreement | Where are s and t? | Below the triangle, each joined to its own bold point | As in the transcription
- [x] 74 02-4 | disagreement | Which cone carries α, β, γ? | α, β, γ are written inside the left (first) double cone and the 3 × 3 square of points stands above the right one, as drawn; the transcription has them the other way round (for the transcription skill). [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 74 07-4 | strike | Is the first sketch struck out? | Left out as struck | An abandoned start of the same chain, to draw
- [x] 74 07-9 | reading | Which strokes of the cube are dashed? | As redrawn | 
- [x] 74 06-4 | reading | Are the vertex letters placed right? | As redrawn | 

## Folder 69

- [ ] 69 04-5 | reading | Does the whole-page redraw match the page, including the arrowed parallelogram kept from the earlier redraw? | As redrawn | 
- [ ] 69 04-8 | reading | Are the large polyhedron and the middle figure read right from the overdrawn strokes? | As redrawn | 
- [x] 69 06-12 | reading | Is the faint plane outline rightly left out? | Left out | To draw
- [ ] 69 01-10 | reading | Are D₆ and D₇ right, and where is w‴? | D₆, D₇ approximate; w‴ not located | 
- [ ] 69 05-2 | reading | What are the end labels of the c and b fans? | Illegible, left out | 
- [ ] 69 03-1 | disagreement | Where does the branch leave the bar, and are α, β written at its ends? | From the left end; α, β not visible | From the middle, with α, β, as in the transcription
- [x] 69 05-12 | disagreement | Is the second bracketed diagonal matrix (λ₁, λ₁⁻¹ … λ_r, λ_r⁻¹) a drawing to mark? | On the page, with no mark | 
- [x] 69 01-14 | disagreement | Is it a three-branch star? | A central triangle with two spikes at each vertex | A three-branch star, as in the transcription
- [ ] 69 05-3 | disagreement | How many points do the broken lines show? | About 4 and 3 | 3 and 2, as in the transcription
- [ ] 69 06-4 | disagreement | What are the small prism's two upper labels? | Like 6 and 4′, left out | Primes, as in the transcription

## Folder 142

- [x] 142 06-18 | reading | Do the three lines through the centre meet at one point on the page? | At 600 dpi the three lines cross at the central vertex 1 of the star, as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 142 06-12 | reading | Are the three bands and their label indices right? | The bands are three nested closed curves as drawn; the labels compared one by one at 600 dpi agree with the redraw, except the lower right corner of the R_2 quadrilateral, now set R_2^omega as the page reads. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 142 06-15 | reading | Are the schematic arrows acceptable? | The vertices, triangles and labels are those of the page; only the course of the arrows is schematic, which does not change the figure (it stays partial for the strokes left out). [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 142 03-3 | disagreement | Is it an octahedron? | Five vertices on the page (P_epsilon, P_epsilon', three Q), so a triangular bipyramid; an octahedron would have six; the labels Q_j (right) and Q_k (middle) were exchanged in the redraw and are corrected. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 142 03-2 | disagreement | Where do the incisions start? | The three thick incisions start from the bottom pole, labelled P_epsilon' on the page, as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 142 03-4 | disagreement | What does the label by the bottom hole read? | At 600 dpi the bottom hole reads R_{omega i} simeq R_0 (the loop l_0 runs to it) and the top hole R_{omega^2 i} simeq R_1: the transcription's identifications are right, the redraw had the two holes exchanged and is corrected. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 142 06-6 | disagreement | What are the circle labels? | At 600 dpi the labels read 1, i, -1, -i (the flag before the back right 1 and the dash before the back i are minus signs), the cyclic order on the equator, as in the transcription; redraw corrected. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 142 06-7 | disagreement | How many times is « β relevé » written? | « beta relevé » is written twice, above and below the circle round 1, as drawn; the transcription should say twice. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 142 06-9 | disagreement | What is the inscription in the loop? | At 600 dpi the loop reads (a_1^{--} a_1^{-+}) with no exponent -1, the two upper arcs of the circle round 1, as drawn; the transcription's reading is to be revised. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 142 06-17 | disagreement | Which indices do the labels carry, and how many copies of 0 and ∞ are there? | The third marked point of the triangle r, beside R^{0,1}_r and R^{1,infty}_r, can only be R^{infty,0}_r; with the frame widened the page shows two copies of each of 0, 1, infinity, as the transcription says; redraw completed. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |

## Folder 144

- [x] 144 03-8 | reading | In which sense do the small rotation arrows of the frames turn? | Not drawn: their senses are not legible | 
- [x] 144 07-9 | reading | In the crowded centre, which nodes do the short strokes join? | As redrawn | 
- [x] 144 07-10 | disagreement | What is the index on M′^! → M′? | 6 | σ
- [x] 144 07-11 | disagreement | Is there a node M under Z^!_{0ρ} = M(j̄)? | Yes, read M | Not in the transcription's list
- [x] 144 09-3 | reading | Is the stack of boxes read right from the overinked sketch? | A freehand stack of three boxes in perspective with axes x and y and no other label: which of the doubled strokes is kept does not change the figure. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 144 07-2 | reading | Page 128, pencil lattice: ũ and σ̃ (left vertical) and ρ̃ (under the lower horizontal) are now read at 600 dpi. Is the faint turned label on the top horizontal, between the top middle and top right points, a ṽ? | Set ρ̃; no ṽ drawn | ṽ
- [x] 144 03-4 | disagreement | How many triangles carry a frame label? | Nine triangles carry a frame label on the page, and the transcription's own list has nine entries; « dix » is a miscount. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 144 07-1 | disagreement | Which labels are underlined? | At 600 dpi M^!, M^{!o} and M^o all stand over an underline bar like those of M, M', M'', and the formula under the figure writes M and M^{!o} underlined; as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 144 07-7 | disagreement | Is there a label Π′ in the second row? | A label Pi' stands in the second row, right of M^!_S[0] and directly above the Pi of the third row; as drawn, missing from the transcription's list. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 144 07-8 | disagreement | What is the overwritten middle node? | The eight nodes are the vertices of the cube {S, M} x {!, no !} x {+, no +} and the seven legible ones leave S for the overwritten middle node, as drawn. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 144 04-5 | disagreement | Do the three equator dots carry labels 0, 1, ∞? | At 600 dpi the back dot carries a small infinity, the front left a 0 and the front right a 1, in agreement with Q_infty = 1/2 between 0 and 1; labels added. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |

## Folder 83

- [x] 83 01-6 | disagreement | How are the triangle's vertices labelled? | The labels read v₁ at the top, v₂ on the left, v₀ on the right, and the heavy mark at the centre is an overinked u (now drawn); there is no u₀ on the figure, so the transcription's list should drop u₀ and add v₀. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 83 04-1 | reading | Is this the schema meant by the mark (the words yzt/ztx, xyz/yzt, xyz/txy joined by two strokes, middle of p. 75)? | Yes: it is the only schema of three-letter words joined by strokes on p. 75. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 83 10-3 | reading | Do the cube's edges stop short of the corners on the page? | Whether the pen strokes reach the corners or stop a little short, the figure is the same cube; the redraw stands. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 83 10-4 | reading | Do the cube's edges stop short of the corners on the page? | Whether the pen strokes reach the corners or stop a little short, the figure is the same cube; the redraw stands. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 83 11-4 | disagreement | Are « f, f′ » above the cube labels of the figure, and is there a diagonal i? | « f, f′ » are the words of the text line « Si f, f′ sont adjacentes » (given as text by the transcription itself), and i is a lone letter inside the cube with no segment; the transcription's « diagonale i » should read « la lettre i ». [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 83 03-2 | disagreement | Is there a star of diagonals inside the pentagon? | The inside holds short dashes, consistent with a star drawn in broken strokes; the redraw places each dash where it stands, which shows the same thing under either reading. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 83 01-5 | reading | Left of the star (p. 15, upper figure), is the label one « v » with a heavy overwritten subscript, or two labels v₂ and v₃ one under the other? (The vertex t below is clear and settled.) | Two labels: v₂ at the left vertex, v₃ just below it at the start of the stroke to t | One label, v₃ (or v₂) with an overinked subscript

## Folder 57

- [x] 57 08-4 | reading | Are the strokes of the dense sketch groups right? | Redrawn group by group, approximate | 
- [x] 57 08-6 | reading | Are the strokes of the dense sketch groups right? | Redrawn group by group, approximate | 
- [x] 57 07-1 | reading | Are the labels right? | As in the transcription | 
- [x] 57 01-1 | strike | Is the left-out part of the top row struck out on the page? | Left out as struck | 
- [x] 57 14-1 | disagreement | How many triangles are there? | Two | Four, as in the transcription

## Folder 146

- [x] 146 04-6 | disagreement | Is the left figure a hexagon (two triangles side by side and their diagonals)? | A pentagon whose centre is joined to all five vertices | A hexagon, as in the transcription
- [x] 146 04-9 | disagreement | What does the figure show, and what are its labels? | One thin line through three points, the middle labelled 0 and the left end ∞ written upright (an 8); no large ellipse with ∞ in this region: the redraw stands and the transcription's description is to be corrected. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 146 03-6 | strike | Are the ellipse, the sphere in lunes, the tetrahedron and the bottom-right sphere all struck out? | Yes: each of the four is crossed by a zigzag, long oblique strokes or a scribble; they stay left out. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 146 03-6 | reading | Is the « ℤ » a letter, or the start of the zigzag stroke? | A letter: a heavy Z with a doubled stroke, in a heavier pen than the thin zigzag over the tetrahedron and apart from it. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 146 04-4 | strike | Are the first D12 sphere and the label D2 struck out? | Left out as struck | 
- [x] 146 01-5 | disagreement | How many looped points are on the equator? | Five arrowed loops on the equator (two left, one at the back, two right), not counting R̃_s; the transcription's « quatre » is a miscount. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 146 07-2 | disagreement | Which vertex does « a » label, and does the right side bend? | The right side bends at a vertex, which « a » labels | « a » at the top vertex, as in the transcription
- [x] 146 02-2 | reading | Is the top label Q+ or Q with a bar? | The sign at the top pole is a bare dash raised like the + of P₊, so a minus: the poles being the pair Q₊, Q₋, the top is Q₋ and the bottom Q₊; the two labels are exchanged in the redraw, and the transcription has them the other way round. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 146 04-14 | reading | Does the whole-page redraw match the overdrawn pencil? | As redrawn | 

## Folder 79

- [x] 79 15-10 | disagreement | How many triangles are there round the vertex? | Counted again: eight strokes leave the centre and seven outer strokes close seven sectors, the eighth (left) being open; seven triangles, as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 79 15-12 | disagreement | Is it a pentagon with all its diagonals? | The outline has six distinct corners and the six inner strokes are the sides of the two triangles on alternate corners: a hexagon with two interlaced triangles, as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 79 14-2 | disagreement | How are s, t, u, v joined, and where are the small circles? | The sentence above the figure asks for an A_0-chain (s, u, v, t): the figure is the path s - u - v - t, and the small circle beside each segment is the 0 of A_0, not a vertex; as drawn. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 79 14-2 | strike | Is the scribbled trial under the schema struck out? | The trial under the schema is crossed by a zigzag and several strokes: struck. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 79 14-3 | reading | Is A₀ a label on a side? | By the proof beside the figure and by 14-2, A_0 is marked by the small circles on the two upper sides and A is written on the lower sides and the diagonal; there is no label A_0 (the scrawl is text), and the grey A_0 is removed. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 79 15-5 | reading | What are the labels of the rhombus and of the far-right quadrilateral (crop widened)? | The sheet is written turned a quarter turn; read turned, at 600 dpi, the rhombus carries t (top) and lambda s (bottom) and the far-right quadrilateral is s, t, t', lambda^{-1}s; all marks read s_-, t_- are s', t'; redraw corrected (one further rhombus label stays unread and left out). [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 79 15-7 | reading | Page 285, turned a quarter turn to the left: does the label along the dotted square (under it once turned) read « s − λ⁻¹t », and the one at its corner « λ⁻¹t »? | Labels left out | Set as read: s − λ⁻¹t and λ⁻¹t
- [x] 79 15-3 | reading | How many superposed strokes are in the lower figure? | At 600 dpi: two strokes from the upper point to the lower t, one straight and one bent through the end of s - t, as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 79 15-3 | strike | Is the short stroke right of the column struck out? | The short mark right of the column is blotted out with heavy strokes: struck. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 79 15-13 | reading | Does the faint circle pass through λt = t′? | The faint circle crosses the line at the right end of the segment t - lambda t, at the dot of lambda t = t' to within about one and a half units; as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |

## Folder 127

- [x] 127 01-4 | disagreement | In what order are T′ → T and X′ → X, and does T′ – T carry an arrowhead? | On the page X′ → X stands above T′ → T, and T′ → T carries a small faint arrowhead, now drawn; the transcription's order is the other one. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 127 01-2 | disagreement | Is X_n → X a plain arrow? | X_n and Y_n are infinitesimal neighbourhoods, closed in X and Y, so the hooked strokes (inclusions) on the page are right and stay drawn. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 127 01-2 | reading | Are the labels G_n and U_n? | The upper label reads G_{U_n} (the page's own diagram has i_{n*}(G_{U_n})), now drawn so; the lower one is U_n, its last strokes an overwriting. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 127 01-2 | strike | Is the word after « Ass U^ » struck out? | Yes: the blot after « Ass U^ » is a word struck with a heavy stroke; it stays left out. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 127 01-3 | reading | What are the labels beside X′ in the right sketch? | On a 300 dpi crop the two labels read x₀ and x′₀, as in the left sketch and as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 127 01-1 | reading | Is the last letter of the pencil formula T_y? | T_y: the union of (T_y ∩ U) and (T_y ∩ Z) is contained in T_y, and the curl is the subscript y. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 127 01-8 | reading | Bottom of p. 19: do the six small sketches of surfaces and curves (two of them labelled Z′, Φ′ and Φ, Z) match the page in shape and order? | Schematic, placed by eye |

## Folder 148

- [x] 148 04-1 | disagreement | Is there a region label A_{∞1}? | Six region labels are on p. 66: A_{0∞}, A_{01}, A_{10}, A_{1∞} in a row, A_{∞0} under A_{0∞} at the left, and A_{∞1} at the far right; the redraw had the far-right one as A_{∞0}, now corrected to A_{∞1}, and A_{∞0} added (commit 21097d1). [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 148 04-2 | disagreement | How many ringed vertices and nested red curves are there? | Eleven ringed vertices, eight closed red curves | Nine and nine, as in the transcription
- [x] 148 02-1 | reading | What colour are the long arc and the edge from the left vertex? | The colour of the arc and of the edge does not change the figure (the arc is a brown stroke by a stain, the edge is ink); drawing kept. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 148 01-4 | reading | Which four small triangles form the heavy rhombus? | On a 300 dpi crop the heavy strokes are the spokes and sides of the six small triangles around one inner vertex (a small hexagon) plus one more side, not a rhombus of four; the redraw already shows the heavy strokes as they are, so it is kept and no four triangles are singled out. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |

## Folder 138

- [ ] 138 07-6 | reading | Page 126, upper right: the small pentagon is too overinked to count its triangles. Is the schematic redraw (fifteen rays from the centre and one ring of chords) acceptable as it is? | Schematic: rays plus a ring of chords, not his exact triangulation | Redraw stroke by stroke from a 900 dpi crop
- [x] 138 06-14 | reading | Are the nested pencil curves drawn over the typed notice right? | Laid over the crop, each nested curve of the redraw follows a stroke of the page between the same end points and closes on the right vertex 8; as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 138 03-6 | disagreement | Is the long curve one stroke with an arrowhead at each end? | At 600 dpi the long curve is one continuous stroke with an arrowhead at X_2 and one at its upper end beside the top node, as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 138 06-50 | strike | Are the left-out parts of the framed sketches struck out? | The three left-out parts (the Z in the frame, the circle right of the lens, the zigzag under it) are each scribbled over on the page: struck. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 138 07-8 | reading | Are the inner cells right? | At 600 dpi the fan has five rays to the five vertices of the right side, as drawn; the unlabelled wavy curve and side shapes are freehand and their exact course does not change the figure. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 138 04-8 | disagreement | What do the labels read, and is « 1/2 » an « h »? | The circles through -1, 2 and through 0, 1 meet on the line Re z = 1/2 at -j and -j-bar, so the minus signs are right, and the tick between 0 and 1 on that line is 1/2; as drawn. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 138 06-12 | disagreement | Is there an « X~ » or an « a » near the hexagon? | « X~ » and « a » are on the page, alone, below right of the hexagon and outside its frame: isolated text, not labels of the figure; the redraw stands and the transcription is right that they exist. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 138 07-5 | reading | Does the label read 1/2 or 1/3? | The label reads 1/2 (a 1 over a 2) at 600 dpi, as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 138 04-6 | reading | What is the overinked first label beside D₁₂? | The overinked label is a first writing of the same back vertex, rewritten clearly as D_12 beside it; the equator has only D_20, D_01, D_12. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |

## Folders 45, 72, 78, 80, 87

- [x] 80 01-2 | reading | Are the solids of this whole page right (sphere as contour, equator and meridian; pyramid over bipyramid; the five inked octahedron vertices and eight edges; the square/hexagon polyhedron)? | As redrawn; the cube with grid lines schematic; pencil cubes and calculations left out | 
- [x] 80 04-1 | reading | What are the labels D, D′, Γ, Γ′, and does Γ pass through u? | At 450 dpi the oblique passes through u (the crossing of D and Δ) and carries the label Γ at its upper right end; the thickened horizontal passes through u′ and is Γ′ by the text (« Γ … mais par u », « Γ′ … mais par u′ »); D, D′ and Γ′ are not labelled on the page; drawing corrected (Γ through u, Γ′ through u′, label Γ set), status ok. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 45 02-1 | reading | Is the right set of elements drawn on this whole sheet? | The mark itself gives only the legible fragments of this scratch sheet; what is left out (reference lines, turned text, isolated heavy letters) changes no figure. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 45 03-1 | strike | p. 52, right of the implication scheme: do the two long horizontal lines and the three oblique lines between them cross out the three lines of text there (then leave them all out), or are they reference lines? | Reference lines, drawn | A crossing-out frame, to leave out
- [x] 45 03-1 | disagreement | Where does the large curve « triviale » end? | The curve passes above (iii) and above the double arrow and reaches (i″), where it runs on as one stroke into the lower line, as drawn; « triviale » stands beside the double arrow (iii′) ⇒ (iii). [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 45 04-1 | strike | Is the whole sketch struck out? | Yes: one zigzag runs from the top mark down across the three formulas; only the vertical stroke is not crossed. The drawing is unchanged (strike not drawn). [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 72 02-3 | disagreement | Are there dots L₁, …, L_i and L′₂, …, L′_i? | No: the rows read L₀, L₁, L_i, L_{i+1} and L′₀, L′₁, L′₂, L′_i, L′_{i+1} with no dots of ellipsis; a single dot stands between L_i and L_{i+1}. The transcription's « … » are an editorial addition. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 72 02-2 | reading | What are the small marks along the upper branch (a τ-like sign, a short heavy stroke)? | The sign has the shape of the τ of τ₀ with a short heavy stroke as index, and the schema below on the page labels its strokes τ₀, τ₁, …: it is τ₁, now drawn. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 87 02-2 | strike | Is the horizontal stroke above the diamond (heavy cross at its left end, small arrowheads, a crossed x) part of the struck first attempt? | Left out as struck | Part of the diagram, to draw
- [ ] 87 02-1 | disagreement | How many segments leave the central point? | Five, two of them inked heavily | Four, as in the transcription
- [ ] 87 01-1 | reading | What are the small signs inside the hatched region? | Not read; one may be a letter, possibly C | 
- [x] 78 01-1 | reading | Is the overinked knot just above A₄ a vertex? | No: it lies on the straight side A₃A₄, which does not turn there, and has no label; the nine labels A₀ … A₈ all stand elsewhere. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 78 05-2 | reading | Which label is σ₀: the heavy one by its axis, or the lighter σ at the top of that axis? | Both marks name the same axis: the other dashed line carries σ₁, and the line they stand on crosses s₀s₁, as σ₀s₁ = s₀ requires; the lighter σ is a first writing of the heavy σ₀, drawn once. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |

## Folders 119, 33, 34, 67, 81, 85, 86

- [x] 119 08-1 | reading | Is the bottom node labelled PB or PD? | PB: the arrow « identité » from the top PB ends there, and an identity joins PB to PB; the B is written like that of the top label. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 119 08-1 | reading | Is the vertical line from the top PB one arrow PB → PB « identité » through the EPC point? | One arrow PB → PB: « identité » can only join PB to PB, and the heads at the EPC point belong to the arrows arriving from EPCR and PBC. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 119 08-10 | reading | Does a stroke run from the top vertex to the dot near the word « ce »? | Yes: at 700 dpi a solid stroke runs from the top vertex to a full dot before « ce », and a thin one from near that vertex to the top of the second triangle; the dot is not joined to it, so no third closed triangle. Both are now drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 119 08-11 | reading | What are the upper-right label and the faint letter under the bottom vertex? | The upper-right label reads v′ and the faint letter under the bottom vertex reads u; a faint u′ above the top vertex is added, so the axis reads u′, u, (a, b), u′, u. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 119 08-12 | reading | Are the hidden edge of the centre-left tetrahedron and the inner diagonals of the left pyramid drawn on the page? | Drawn: both the inner strokes of the centre-left tetrahedron and the two crossing base diagonals of the left pyramid are in ink on the page. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 33 01-1 | reading | Is the sheet to be read turned 180°? | Yes: turned 180°, every letter and the whole square Y, Y′, X, X′ read upright; the sheet was scanned upside down. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 33 01-1 | disagreement | Are there a vertical arrow crossing k → k′ beside the hatched circle, and a faint short arrow after A? | Yes, both are on the page: the vertical arrow across k → k′ beside the hatched circle (head at the bottom) and a faint short stroke after A; they stay drawn, and the transcription's description could name them. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 33 08-1 | reading | Is there a fourth apex in the lozenge row, between X, Y and F? | The lozenge row is a doodle of crossing lines drawn over the writing; one apex more or less changes nothing mathematical, and the redraw stands. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 34 09-5 | reading | Is the short vertical stroke across X ⇐ X̃ under X_Ũ a plain stroke? | The stroke runs from under X_Ũ to just above Ū, so it is most likely the vertical edge X_Ũ → Ū of the cube (as X_K over U); the redraw shows it as on the page, the same figure under either reading. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 34 08-1 | strike | Is the group of oblique strokes with a V and S̄ at the right struck out? | Yes: one continuous zigzag covers that group (its V, its S̄ and their joining strokes), while the V over S to its left is untouched; it stays left out. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 67 01-2 | disagreement | Is the collar hatched? | No hatching visible, not drawn | Hatched, as in the transcription
- [x] 67 01-2 | reading | Which middle curve is Γ_i? | The label Γ_i is written between the two overlapping middle curves at the lower left and the redraw places it there; both are closed curves in the collar, drawn as on the page, so naming one of them does not change the figure (the alternatives of the line describe an earlier redraw). [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 67 02-1 | disagreement | Is a point x marked? | Yes: at 600 dpi a small x-shaped mark stands inside the sphere at the upper right, just right of z, where the curve from the upper right begins; the letter x is added to the redraw there (no dot, the page has none). [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 67 05-1 | reading | What colours are the felt-pen strokes? | The facsimile is in colour (the earlier pass rendered it in grey): sphere 1 blue-green fill with a black network; spheres 2, 3, 6 and the small contour brown; the large sphere 4 orange; sphere 5 brown with orange and blue-green arcs; sphere 7 brown chords, outline and arcs in orange and blue-green; spheres 8 and 9 thin dark pen with a heavy orange arc; the redraw now carries these colours. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 85 04-1 | strike | Is the upper sketch of oscillating curves struck out? | Yes: the left part of the sketch carries crossed X strokes and a loop is drawn round it and the words under it; the transcription also says « croquis barré »; it stays left out. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 86 02-3 | disagreement | Where is the vertex v, and what is the second letter inside the pentagon? | The letter outside the lower right vertex is v: it stands at a vertex like the u under the bottom vertex, and the marginal « NB a ~ {u, v} » names exactly the two vertices u and v; the redraw writes v there, and the inner letters are a, s, f (the flag of the text). [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |

## Folders with one or two partial drawings

- [x] 156-7 04-1 | disagreement | Is the first segment subdivided in two or in three? | Three: the segment carries four ticks, its two ends and two between; the transcription's « en deux » is a miscount. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 76 01-1 | disagreement | Which arrow does the cross strike? | The crossed stroke lies on the line from D02 to D2 and continues the right leg of the caret under D02, and D02 maps only to D0 and D2 in the lattice of flags, so the crossed arrow is D02 → D2; the strokes of the redraw are unchanged (the transcription's « D02 → D1 barrée » is for the transcription skill to correct). [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 77 01-3 | reading | What is the label left of the vertical stroke? | The label is f₃ (long f with subscript 3, same hand as f₁ and f₂), as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 77 05-1 | strike | p. 83, top: are the three large arcs and the three falling strokes a crossing-out of the words « dans Δ^ν … ∂ ∈ A* » (then there is no figure), or a sketch of three wedges? | A sketch, drawn whole | A crossing-out: no figure to draw
- [x] 147 04-5 | strike | Is this « schéma raturé » struck as a whole? | No stroke cancels the figure: labels and segment are untouched and the strokes crossing at the upper right end the contour; it stays drawn whole. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 136 02-1 | reading | Are the arrows « à double pointe » double chevrons, or heads at both ends? | Double chevrons along each stroke, as the legend of two arrows beside the box shows (single head, double head). [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 136 02-1 | reading | What is in the box? | The box reads G, g₁, [gap], g_k (the caption below has « Mot en les g_i »); the label is corrected and the transcription's g, g′, gh is to be corrected there. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 136 02-1 | strike | Are the three long oblique strokes strikes? | Yes: the three strokes run far beyond the figure, over the box corner, the caption and the lines below; they stay left out. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-5 01-1 | disagreement | Does curve A surround x and z? | The text gives A° = A∖D = {x} and D = {z}, so A = {x, z}: the curve is an open arc embracing z and x on their left, as the brace C embraces z and y; it does not close, and is drawn as on the page («entoure» is loose but not wrong). [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-5 01-1 | reading | Is the long stroke from Φ joining curve A part of the figure? | Part of the text layout: it runs from the line « 𝔏 = {A, B, C, D} » down and round the line « A° = {x}, … », an insertion line (the transcription places that formula after B° = {t}); it is no longer drawn. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 43 06-1 | disagreement | Where are the sketches on p. 107? | Both sketches are in the left half of p. 107; the « à droite » of the transcription is wrong for them (to correct in the transcription), the drawing is unaffected. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 43 06-1 | reading | Is the short upright stroke before X the subscript 1? | The stroke stands before the X at the height of its top, in both places where the symbol occurs on the page (« ∅ ≠ ′X » and « = (′X) »); the label stays ′X as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 43 06-1 | reading | P. 107, upper left of the two sketches: do the angle sign and the two looped letters along the oblique stroke read « α_p »? | Left out as unread | « α_p », to add at the upper left
- [x] 43 04-1 | reading | Which small figure is « the parallelogram marked with a point »? | They are two separate sketches, both on p. 63 and both drawn: the small parallelogram next to the A is the one this mark names; the larger curved quadrilateral at the lower left is the sketch a later note of the transcription describes. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 23 04-2 | reading | Is the struck letter X′ or X? | X, struck and left out; the prime belongs to the X′ written above it | « un X′ biffé »
- [ ] 23 04-2 | reading | Where is the illegible word? | Just above the line, at the foot of the second diagonal | « sous le trait »
- [ ] 12 08-2 | reading | Is Q″ at the upper right legible? | Only « Q′ + » drawn; the rest is cut by the sheet edge | Q′ + Q″
- [x] 15 11-1 | reading | Where is the ℚ? | ℚ is the looped, overwritten letter at the bottom left of the second diagram, under k₀ and joined to it (k₀ is an extension of ℚ, the foot of the tower); it is now drawn as a label. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 73 01-5 | reading | Does u_{i+1} start at the vertex of u_i? | Yes: u_{i+1} is the side following u_i in the polygon, so it starts at the end of u_i; the gap on the page is where the overwritten vertex label is written, and the redraw now joins the two sides. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 73 01-5 | reading | Under the bottom side of the figure of p. 20, left of « u_{i−1} »: is the label λ_{i+1} or λ_{i−1} (its sign is blotted)? | Left out | λ_{i+1}
- [x] 75 01-1 | reading | What is the vertex set? | The sketch is an example of a graph with double edges, an isolated edge and an isolated vertex; whether undotted junctions count as vertices does not change what it shows. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 76 01-2 | reading | Is the ladder framed? | No: a heavy bar stands above 2, 3, 4 (with a short drop at its right end) and a heavy bracket with an uptick at each end under 3, 4, 5; there is no closed frame and no vertical at the left, and the redraw is corrected to show this. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 91 05-1 | reading | Is the faint pencil oval behind U_f part of the figure? | The faint oval is light pencil under the ink and adds nothing to the figure; it stays drawn in pencil. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 91 06-1 | reading | p. 103, left margin: is the small J-like mark just above the middle of the short segment the letter y? | Left out | y, placed there
- [x] 117 02-1 | reading | Which ringed vertex is Y? | Y is the ringed vertex at the bottom left, under X and joined to it by a downward arrow (the staircase has the row Y ← X; a faint Y-shaped mark stands left of the ring); label added. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 137 03-1 | reading | p. 58 (sheet upside down), label under the curved arrow left of centre: « B^rés » or « B^{rés.le} »? | B^rés | B^{rés.le}
- [x] 137 03-1 | strike | Is the long oblique stroke a strike? | Yes: the stroke crosses the whole sheet through unrelated lines above and below the scheme; it stays left out. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-7 05-1 | reading | Is x a separate letter above the cross? | No: the upper arc carries one small cross and no letter; the other x stands in the legend by the lower arc. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-9 06-1 | reading | Where is C, and which stroke is C → 1? | As drawn: in the cube lattice C receives a and b′ and sends one arrow to 1; the long vertical stroke to 1 starts exactly where the arrows from a and b′ meet, with the letter C just left of it. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 158 04-2 | reading | Does « Σ¹X » above the cones belong to this drawing or to 04-1? | « Σ¹X » is set in the transcription as a displayed formula before the mark of 04-1: it is text and belongs to neither drawing. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 100 01-4 | reading | Is the long upper stroke the top of the region or the bottom of the frame above? | The stroke forms a corner with the left side of the box above, so it is the bottom of the frame, and the region's sides run up to it: it bounds the region too, and is drawn at the same place under either reading. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 121 03-1 | reading | Are the U″ rings, the I/II dumbbell and the 1°)–6°) sequence right? | The differences named are offsets of 1 to 3 units in a whole-page figure; no element changes, and the record stays partial. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |

## Struck material in drawings marked ok

A whole figure that is crossed out is drawn in ink without its crossing-out strokes. A struck sketch beside other drawings is left out entirely. The first questions ask whether that rule is right.

- [ ] 43 10-1 | strike | P. 183 is crossed out by three long oblique strokes, but the framed schema under them is intact: keep it drawn? | Yes: drawn, the three strokes left out | No: record it as struck, with an empty redraw
- [ ] 142 06-3 | strike | Page 105, middle: this figure is wholly crossed out by zigzags. Keep its redraw (yes) or publish it as an empty « struck » figure (no)? | Drawn in ink, the zigzags left out | Not drawn
- [x] 156-1 02-1 | strike | The « figure barrée » is crossed by four strokes: should it be drawn? | The strokes strike the figure of case a), whose text is struck beside it, but the same figure stands in the transcription as a diagram just above the mark, so the reader has it either way; the redraw is kept. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 156-6 04-2 | strike | A question of rule, asked once: when a figure is wholly crossed out (here the hexagon of p. 73, redone fair on p. 74 as 04-3; also 78 07-3), is what lies under the strike drawn? | Yes: drawn in ink, without the strike | No: an empty record saying it is struck
- [ ] 7 04-1 | strike | Top of p. 67, small sketch under the struck line: is the zigzag inside the frame a crossing-out, or the content of the sketch (a curve from the lower left corner ending in a small loop on the base)? | A crossing-out, left out: frame, loop and ticks drawn | The content of the sketch: to be drawn
- [x] 78 07-3 | strike | The square is covered by strike loops: should it be drawn? | Same question of rule as 156-6 04-2 (a figure wholly crossed out: is what lies under the strike drawn?); here the loops plainly cover the whole square, and the answer given there applies. [duplicate; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 74 05-4 | reading | What lies under the hatching? | Three rows, each a point, an arrow and a point (the last ending in a small cross-like mark), as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 119 08-7 | strike | Is the square outline itself struck, or only its contents? | Row (2″) is « 1 / 1 / square », the partition 1+1+4, so one square stands for the four points: the scrawled first square is a false start redone at its right and stays left out. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 154 07-15 | strike | Are the a⁺, b⁺ above the scribbled copy struck too? | The labels belong to the struck copy, whose content the kept figure repeats; left out with it. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 146 04-13 | reading | Is the lower-left label of the right triangle scribbled out, like the ∞? | Yes: it is a scribbled blot like the struck ∞, unlike the clean 1 at the lower right; it stays left out. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-6 04-6 | strike | Is the ⇔ between At 11′ and « At 11 … fini » struck, or only overinked? | Not struck: it is gone over along its own length, heads clean, with no stroke across it, unlike the slashed and scribbled « ⇔ At 11 » at the end of the last line. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 144 07-3 | reading | Where does the arrow to uu′(a) start? | The formula (u,l)(u',l') = (uu', u(l')l) makes the upper path a -> u(a) -> uu'(a): the middle node, whose first label u'(a) is struck and replaced by u(a) above, is u(a), so the arrow starts at u(a) as drawn. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 79 15-4 | strike | Which λt is the struck one? | Whichever of the two lambda t under the vertex is the kept one, the vertex carries the label lambda t once and the line s - t - lambda t - s' is the same. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 34 08-2 | strike | Is the label i struck, or only the scribble before it? | Only the scribble before it: the letter i stands clear of it and is clean, as the transcription reads it. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 136 05-1 | strike | With the struck stroke removed, the second Φ′ has no stroke from k: is that right? | The first Φ′ already carries the stroke u′ from k and the second Φ′ is the same object written again, so no relation is lost either way. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |

## Folder 154, further passes

- [ ] 154 03-5 | strike | Is the wavy red stroke right of the lower network (loops over a straight line) a strike-out or a deliberate wavy line? | Drawn as the plain straight line | Wavy, or left out as struck
- [ ] 154 03-5 | reading | Against the right rim, which strand of the circle doubles back where? | Strands traced up to the rim; the doubling back not reproduced | Strands with cusps or curls inside the tangle
- [x] 154 03-5 | reading | Is the tiny red tick at the top left part of the figure? | A tick of a millimetre with no label and no incidence; kept as drawn. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 154 03-5 | reading | Is the left pencil sketch (two faint lines meeting at a dot) part of the figure? | Two faint pencil lines beside the figure, touching nothing in it; kept in pencil. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 154 04-6 | reading | What is the legend before « (a′,b′) »? | « ou », as in the transcription | Another short word or sign
- [x] 154 04-6 | reading | In the right figure, do the two red strands meet exactly at the black point? | Whether the strands bend slightly at the black point or cross a stroke's width below it, the same two strands meet at the same marked vertex. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 154 04-8 | reading | Are the faint pencil lines (a guide above ω_D, a line along the right red strand, a short stroke by the left one) part of the figure? | Pencil guides under and beside inked strokes; drawn in pencil, they add no incidence. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |

## Folders 81, 85, 86: the large drawings redrawn

- [ ] 81 01-2 | strike | Row 2, second disk, with OK written beside it: are the big zigzags that run out of the disk a strike, or hatching? | Hatching: four chords, the region between the two long diagonals hatched | A struck disk, not drawn
- [ ] 81 01-2 | reading | Row 2, « ou ( … ) », left small disk: is its dark centre a small filled triangle or a quadrilateral? (The right one is settled: chords through one point.) | A small hatched quadrilateral | A small filled triangle
- [x] 81 01-2 | disagreement | Is the vertical axis of the right-hand figure arrowed? | No: the vertical axis is a bundle of strokes ending without a head, only the horizontal one has a hook; the head the redraw had drawn on it is removed, and the transcription's « deux axes fléchés » is to be corrected. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 81 01-2 | reading | How are the crossing curves at the right grouped? | The curves carry no label and no text refers to them: drawn stroke by stroke, the figure is the same however the strokes are grouped. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 81 01-1 | reading | Is the region of the disk with three chords (row 3, second disk) hatched, or scribbled out? | A hatched polygon bounded by the three chords and the curved fourth side | A loose zigzag scribbling-out
- [x] 85 05-2 | disagreement | What is the middle node of 1 → S22? | F2, as it looks on the page | Z2, as in the transcription
- [x] 85 05-2 | disagreement | What is the bottom of the small diamond? | F2: at 500 dpi the letter is a double-struck F (two bars, none at the foot) with index 2, the same vertex as F2 in the fair copy of the lattice on p. 97; the drawing stands, the transcription's E2 is to correct. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 85 05-2 | disagreement | Is there a node A′3 at the start of the dashed lower square? | Yes: the label A′3 is written under the node where the dashed arrows to D′3 and S̃′3 start; the drawing stands, the transcription's list lacks it. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 85 05-2 | disagreement | Is the label S̃3 or S̃3 = S3 × S′2? | S̃3 = S3 × S′2 is written in full on the page; the drawing stands. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 85 05-3 | disagreement | What is the middle group of the row « D3 ↔ ? ↔ D3 ↔ S3 × S″2 »? | A3: the letter is the script A of A4 two rows above, not his gothic S; the drawing stands, the transcription's S3 is to correct. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 85 05-3 | reading | Do the V-shaped arrows (S3 × S″2 and A4 → S5, D3 → A5) go down to a turning point and back up? | Yes: on the page both paths run down to a turning point below the lattice and back up (the second along the hatched band); the drawing stands. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 85 05-3 | reading | P. 97, bottom right of the small rectangle S2 — S3 — ?: in the second factor a gothic S and a double-struck D are written one over the other; which one stands? | S3 × S′3 (the D struck over) | S3 × D′3 (the S corrected to D)
- [x] 86 01-1 | disagreement | Is the left back vertex of C1 and C2 v′ or u′? | v′: the antipode of v lies on the side of u in this view, the equality Π_{t,u} = Π_{s′,v′} needs it, and in (C₂) the left outer vertex is plainly written v′ on the page; the overinked letter at the left of (C₁) is read accordingly and the redraw is unchanged. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 86 01-1 | reading | What are the small c-shaped mark at the centre of C2 and the two small marks below s′ and above t′? | The two small marks under s′ and above t′ repeat the labels of those vertices (the lower one reads t′) and the small hook at the centre is attached to no vertex; they stay left out and the figure is the same either way. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 154 02-10 | reading | In the band at the centre right, which ends pair up where the lower-left chord meets the chord from the left rim? | The lower-left chord crosses the left chord at a grazing angle and goes to the right rim; the left chord goes to the lower right rim | The two are swapped and only touch
- [ ] 154 02-11 | disagreement | How many regions are next to the rim? | Four next to the rim, plus four small inner ones | « cinq régions voisines du bord », as in the transcription
- [x] 154 02-12 | reading | What colour are the short segments joining the ends of D and D′ in the first disk? | The colour of the two short segments (grey-blue or green) does not change the figure; the redraw keeps the colour seen on the scan. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 154 02-12 | reading | Is the dark doubled vertical stroke in the third disk a chord? | A chord from the top rim stopping on the diagonal chord | A correction of D′, not a chord
- [ ] 154 02-13 | reading | What is the blue-grey dotted stroke in the third disk? | A dashed pencil line | A struck or erased chord
- [ ] 154 02-16 | reading | How many arrows go with each number 1–4? | Two per number, both ways along the rim | One per number
- [x] 154 01-1 | reading | In the lower disk, do the two strands meeting near the bottom cross or only touch? | Two pseudo-lines of an arrangement cross exactly once, so the two strands that meet near the bottom cross: as drawn. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 154 01-2 | reading | Several strands stop a little short of the rim on the page: should they? | Every strand of an arrangement in a disk runs from rim to rim, so the strands are drawn to the rim. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 154 06-15 | reading | Do the four doubled pairs cross exactly on the green rim, or just outside it, under the black detour? | On the rim | Just outside the rim
- [ ] 154 06-15 | reading | Does the black reinforcement at the lower left loop round the left crossing? | Drawn straight through it | A small loop, as at the other three crossings
- [ ] 154 06-14 | reading | Is the thin dark green diagonal across the right of the band part of the figure? | Drawn | A stray stroke from another figure, to leave out
- [ ] 154 06-16 | reading | On which vertical does the lower right black bar end? | The left one of the two | The right one: the ink stops between the two
- [ ] 154 06-16 | reading | Are the short red stubs at the right dark points of the band ends, or strands crossing through the point? | One stub ending at the point | A strand crossing through the point
- [ ] 154 07-16 | disagreement | What are the side labels of the middle sphere? | « 1 » left, « −1 » right, as read on the page | −1 left, +1 right, as in the earlier record
- [ ] 154 06-13 | reading | What is the label on the top side of the left square? | « (3) » | « (2) », as in the earlier redraw
- [ ] 154 07-4 | reading | Where do the two upper dashed orange fan edges end? | On the bent dashed blue side, where the green dashed edges begin | At separate points off the blue side
- [x] 154 03-7 | reading | Should the first stretch of the right figure's green line join the first orange-ringed point? | A gap of a stroke's width before the ringed point: the line is the same line through the same point. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 154 03-7 | reading | Does the left dark green segment reach the point of concurrence? | Drawn stopping short, as on the page | Ended on the point (« relie le point de concours à un sommet »)
- [ ] 154 04-9 | strike | Is the second, scribbled δ1 beside the vertex δ1 overwritten? | Left out as overwritten | A label, to keep
- [ ] 154 04-9 | reading | Is the middle red « pair » three strokes, or one pseudoline pair with a redrawn branch? | Three strokes | One pair, the branch a redrawing
- [ ] 154 04-9 | reading | At the left, where the dashed rows cross D near x, which dashes belong to D1 and which to D2? | Each dash drawn from its own ink, not assigned | Continuous dashed pseudolines through x
- [x] 154 05-5 | reading | Is the black oval of the upper drawing centred on the crossing of the middle pair? | The oval is 1.3 mm from the crossing it marks: a placement, the marked crossing is the same. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 154 05-5 | reading | What are the left-hand pencil arrows of the lower drawing and the upside-down « g »? | Two pencil curves with arrowheads, plus a label « g » | An arrow ↔ legend
- [x] 154 01-3 | reading | Near the centre, two strands from the top make a tight knot: one crossing, or a touch and then a crossing? | Two pseudo-lines cross exactly once, so the knot is one crossing: as drawn. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 154 01-3 | reading | How many rays are there, and how do red and yellow alternate? | 10 red and 20 yellow, two yellow between neighbouring red rays | About 28, alternating, as in the earlier record
- [ ] 154 01-13 | reading | In the star at D (margin), is the black point the vertex, or only the tail of the arrow? | The vertex, at the meeting point | The tail of the arrow, apart from the vertex
- [ ] 154 01-13 | disagreement | What is the label of the lower marginal point? | a′ | a, as in the transcription
- [ ] 154 01-13 | reading | At the foot, which dashed arc ends on which brown line? | The outer on the upper line, the inner on the lower | The other way round
- [ ] 154 02-4 | reading | Where are the borders of the hatched regions t′, T and t? | t′ left of the line going down left from the central vertex; T the triangle under the vertex down to the green line; t right of the vertex above the generisation | Other borders
- [x] 154 02-4 | reading | Is the right small bar broken where the middle line crosses it? | A bar broken where a line crosses it is the same bar. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 154 02-8 | reading | Do the short pencil dashes in the upper faces join vertices? | Not drawn | Further dashed edges from map vertices to dual vertices
- [ ] 154 06-1 | disagreement | Is it a map with pentagonal and hexagonal faces? | A ribbon graph: a wheel with five spokes (green vertices in orange disks, edges as green bands with brown borders), with the blue dual | « faces pentagonales et hexagonales », as in the transcription
- [x] 154 06-1 | reading | Are the two short gaps in the brown face sides, where green spokes end, on the page? | Two short gaps in the brown sides where spokes end: same faces, same incidences. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 154 06-2 | reading | In the top-right disk, is the bent strand one pseudoline or two strands? | One bent pseudoline | Two separate strands
- [ ] 154 06-2 | reading | Does the oval in the centre carry a chord? | No chord: an empty oval with a brown dot | A brown chord across it, as in the earlier redraw
- [ ] 154 06-2 | reading | In the large disk, how many green curves are there, and where do they gather? | A pencil of 8 curves through one point of the lower-left rim and one near the top | Another count or other ends
- [ ] 154 06-2 | reading | Are there rim numbers 12 and 14 near the top right? | No: only the transcription's numbers | 12 and 14 present
- [ ] 154 06-4 | reading | In the middle-right, lower-right and bottom figures, does the line pass through the crossing? | Drawn concurrent | The line passes just beside the crossing
- [ ] 154 06-4 | reading | Is there a y′ at the top of the vertical axis of the frame? | No: x and y only | y′ there
- [ ] 154 06-6 | reading | In the right figure, does the short black piece on the green line end on a red leg? | Drawn where it is, not on a leg | It belongs to the left leg of the right crossing
- [ ] 154 07-14 | reading | Two strands of the half-disk cross twice (near the middle and again at a dot), which a pseudoline arrangement should not do: is it a slip on the page? | Drawn as on the page, crossing twice | The lower ends are swapped, so they only touch at that dot
- [ ] 154 07-14 | reading | Where are the small « 1 » and « 2 » marks at the two base vertices? | One « 1 » at the left vertex, one « 2 » at the right | Each vertex carries both
- [ ] 154 07-9 | disagreement | On the first spindle, which numbers are written at the left ends of the brown curves? | Only « 3 » and « 2 » readable | 1 to 5 at both ends, as in the transcription
- [ ] 154 07-9 | reading | In the right half of the second spindle, are the broken brown curves continuous? | Drawn as pieces, approximate | Continuous curves 5→8, 4→7, 3→6, as the end numbers suggest
- [ ] 154 07-13 | reading | Is the orange cross under the top spindle meant to sit on its light green line? | Kept above the line, as drawn | On the line
- [ ] 154 04-10 | reading | In disk 3, how do the two strands crossing at the black point left of centre pair up? | The strand from the top turns to the lower right through the black points; the dotted strand from the upper right runs on to the lower left | The opposite pairing, but then the two would touch without crossing
- [ ] 154 04-10 | reading | In disk 2, is the wavy ink part of the strand it lies on? | One strand | A separate ink stroke over a pencil line
- [ ] 154 05-2 | reading | Where do the light orange curves go under the band? | Each drawn from the rim to the band's border; no pairing under the band | Single strands crossing the band
- [ ] 154 02-7 | reading | In the lower left of disk C, are there two separate strands, or a straight strand with a stroke ending on it at its apex? | Two separate strands | One straight strand, the other stroke ending on it
- [ ] 154 02-7 | reading | What are the dark green labels by the two arrows near the gluing point, and the middle sign between p and q at the top of D? | Left out; the middle sign read « ? » | Sign pairs such as p:q; the middle sign a « J » or a mirrored p
- [ ] 154 02-7 | reading | Which way does the arc on D's right rim point? | Arrowhead at the upper end | Pointing down, as in the earlier redraw

## Répondu dans #131, appliqué

Réponses reportées dans `drawings.json` ou dans la transcription ; les cases sont cochées.

- [x] 84 07-1 | reading | What are the primes of the labels? | L_i, E′_i, M′_i / L″_i, E″_i, M_i / L‴_i, E‴_i, M′_i / L′_i, E′_i, M_i; the bottom E may be E″_i | The transcription's L, L′, L″, L‴ scheme
- [x] 86 02-4 | disagreement | Is there a star of three lines a′, b, c with side a dotted? | Not found on the page | Present, as in the transcription
- [x] 70 04-6 | disagreement | What are the proportions of the rectangle? | About 3:4 | Golden, as in the transcription
- [x] 70 04-5 | reading | Do s₁ and s″₃ carry a bar on the page? | Barred, as in the transcription | No bar visible
- [x] 70 04-8 | disagreement | How is the top vertex labelled? | s′₀ | As in the transcription
- [x] 78 05-4 | reading | Which long line is the axis and which the arrow a, and what are the second « 1 » and the « 0 » at the top? | As redrawn; D through the origin | 
- [x] 70 04-1 | strike | Is everything left out of this drawing struck out on the page? | Left out as struck: the wavy scribble along the top, the inked blot inside the triangle, the overwritten strokes right of the σ₀ line, four faint erased lines | 
- [x] 70 04-3 | strike | Is everything left out of this drawing struck out on the page? | Left out as struck: the formulas over the left trihedron, the zigzag "hatched plane", a scribbled Z and W, the sinusoid | The sinusoid belongs to the drawing
- [x] 70 04-2 | reading | Is the solid triangle a deliberate fill? | A deliberate fill, drawn filled | A strike-out, to leave out
- [x] 70 03-1 | disagreement | What follows « ≤ » on the page? | One index, read j+1 | « j−1, j+1 », as in the transcription
- [x] 70 05-1 | disagreement | Is there an s₂ label on the polyhedron? | No s₂ visible | s₂ as in the transcription
- [x] 70 06-1 | disagreement | What is struck in this sketch? | One sign only | The whole sketch
- [x] 70 07-1 | reading | Are σ₁ and σ₂ placed right? | Placed after the transcription; on the page they run into the formulas | 
- [x] 70 01-3 | reading | Are the matrix entries where the page has them, with the struck ones left out? | As redrawn | 
- [x] 154 04-3 | reading | Does the red X cross on the dark green line? | Yes, snapped onto it | 

## Folder 154, later passes

- [ ] 154 09-7 | reading | Just right of the left node, under the blue stroke, where do the strands go? | Two arcs from the left node and one from the left end of the black segment reach the upper right node; a short strand from the left node ends on the blue stroke | The third upper arc comes from the left node
- [ ] 154 09-7 | reading | Is the lowest braid strand one curve? | One strand along the bottom edge, from the blue stroke to the lower right node | Two pieces, leaving the crop and coming back
- [ ] 154 08-16 | disagreement | Is the letter in F′ δ or δ′? | δ, no prime visible | δ′, as in the transcription
- [ ] 154 08-16 | disagreement | Is the label at the right end D or D_i? | D (the crop may cut an index) | D_i, as in the transcription
- [ ] 154 08-16 | reading | Is there a t in F next to the star mark? | Drawn | Only δ and s, as in the transcription
- [ ] 154 08-14 | reading | Which labels go round the middle point of the right sketch? | β′ above, γ′ at the lower right, α′ below, as in the transcription | Both upper glyphs β′
- [x] 154 07-6 | disagreement | How many branches has the blue star? | At 400 dpi the blue star has seven branches (three end in a blue dot); the transcription's « huit branches » is to be corrected. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 154 07-6 | disagreement | Is the last figure a hexagon? | At 400 dpi the last figure has five green vertices and five blue rays from the centre, plus one dashed stub: a pentagon; the transcription's « hexagone » is to be corrected. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 154 07-6 | reading | Near the centre of the first figure, do the blue, green and orange stubs stop short on purpose, or should they meet? | Stubs stopping 0.45 mm short of the common point: the same edges at the same vertex. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 154 07-6 | reading | Does the green edge from the top-left free end reach the upper green vertex? | Joined to the vertex | A free end, 1.6 mm short
- [ ] 154 07-1 | reading | In the green disk, is the upper-left red corner inside the disk or on the rim? | Inside the disk | On the rim
- [ ] 154 07-1 | reading | In the green disk, from which top-right rim point does the right-hand red curve start? | The top point, passing next to the upper-right one | The upper-right point
- [ ] 154 07-1 | reading | At the hexagon's corner 5, do both thin orange lines pass through the corner? | One through the corner, one ending at it | Both through the corner
- [ ] 154 07-1 | reading | Are the two faint orange strokes in the middle band an X? | An X on the faint orange line | Two separate strokes
- [ ] 154 06-8 | reading | Is the central pencil of the D/D̄ figure three or four orange lines? | Four | Three, the fourth top end a doubled stroke
- [ ] 154 06-8 | reading | Are the three orange lines of the right crossings concurrent on the brown line? | Concurrent at one point of the brown line | Three nearby pairwise crossings
- [ ] 154 06-8 | reading | Which middle labels carry a bar? | r, r̄, t̄, t above; r′, s′, t′ below | Bars on other letters
- [ ] 154 06-8 | strike | Is the label left of ā in the top version overwritten? | Left out | A second ā or ā′
- [ ] 154 06-11 | reading | What are the marks on the green arcs: tildes or dashes? | ~3, 2~, 1~, ′3, 1− | 2–, 1– with dashes
- [x] 154 06-11 | reading | Is the upper tangent pencil circle a circle? | A slightly narrow ellipse or a circle: the same tangent circle. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 154 06-12 | reading | Should the pencil lines from the black dots reach the lower end dots? | Pencil lines stopping just short of the end dots they point at: same lines, same ends. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 154 06-17 | reading | Are the arrowed marks inside the top contour « 7 » and « 4 », and is there a second « 4 » under the 2 in the bottom figure? | Left out | Region or arc labels, to draw
- [ ] 154 06-17 | reading | Do the two crossings lie on the light green line? | On it | Slightly off it
- [ ] 154 06-18 | reading | Do the red crossings of the colour figure lie on the blackened line? | On it | About 0.7 mm above it
- [ ] 154 06-18 | reading | Is the edge set of the pencil parallelepiped right? | 25 edges between 12 vertices | Fewer edges: some strokes are erased lines

## Folder 154, last pass

- [ ] 154 05-8 | reading | Do the two arcs from the top end on the right spindle strand, or cross it and run on a little? | They end at one shared point on the strand | They cross and continue about 1 mm past it
- [x] 154 05-8 | reading | Do the two zigzag strands meet three times? | Both answers describe the same drawing, three meetings as the ink shows; the record's note already says that it is not an arrangement. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 154 05-4 | reading | Is the label under the fan σ_s? | σ_s | « a f s »
- [ ] 154 05-6 | reading | In the left disk, in what order do the strands end on β and α? | On β, top to bottom: E2, E1, the arch, E3; on α: the arch, E7, E6 | Another order among the strands that end close together
- [ ] 154 05-6 | reading | How many strands are in the small centre disk? | Nine, drawn as chords | Another number: the bundles could not be separated
- [ ] 154 05-7 | reading | Where does the strand from the top-left rim of the upper disk end? | On the bottom black arc, next to the vertical strand | On the rim below the arc
- [ ] 154 05-7 | reading | Where do the strands of the first small disk go? | Three strands fan from the top to the left, bottom and right arcs, plus an arch joining the left and right arcs | Another pairing: the bundle is tight
- [ ] 154 05-7 | disagreement | Is the first small disk's rim green? | Green, as on the facsimile | No colour given (« deux petits disques du même type »)
- [ ] 154 07-2 | reading | In the left disk, near the right rim, do two red strands cross twice? | They cross twice, as on the page | One meeting is only a touch, or the strands pair differently at one crossing
- [ ] 154 07-2 | reading | In the same disk, do three red strands pass through one point with a dark dot? | A triple point | Two crossings close together
- [ ] 154 07-2 | reading | In the left disk, does one red strand end free just short of the rim? | It ends free | Meant to reach the rim
- [ ] 154 07-2 | reading | In the half-disk, does the near-horizontal red strand pass through two triple points and start inside the rim? | Two triple points, start inside the rim | It meets the rim, and the crossings are separate pairs
- [ ] 154 09-1 | disagreement | Is the lower-right red rectangle cut in two by a light green band? | Two red boxes joined by light-green pieces of their sides, the bottom line drawn separately | « coupé en deux par une bande vert clair », as in the transcription
- [ ] 154 09-1 | reading | In the small red disk at the centre, what is the first right-hand number? | Read 5′, 4′, 3′, 2′ from top to bottom | 1′
- [ ] 154 09-1 | reading | Is the second red stroke along the lower-right rim of the top-middle disk the rim drawn twice, or an extra strand end? | Not drawn | The rim drawn twice, or a strand end

## Folder 154, schematic drawings redrawn (9 November, evening)

- [ ] 154 09-2 | disagreement | Are the lobes of the figure of eight pseudoline arrangements? In each lobe two strands cross twice, at the two black dots | Drawn as on the page, crossing twice, so neither lobe is an arrangement | Each pair crosses once, a dot read as a touching point
- [ ] 154 09-1 | reading | Rim numbers of the top disk (the transcription reads only 1, 1', 2', 4', 5) | 1 (twice), 1', 2, 3, 4, 5 on the left; 2', 3', 4' on the right | 2, 3, 4, 3' unread
- [ ] 154 09-1 | disagreement | A pencil circle with a dot and a horizontal line, below the α/β half-disk, is not in the transcription | Drawn | Omit it
- [ ] 154 09-1 | reading | Numbers on the arcs of the small a/b disk | 2, 3, 4, 5 on the left; 1', 4', 3', 2' on the right | 1–5 and 1'–5', as in the transcription
- [ ] 154 09-2 | reading | Numbers of the middle disk (the transcription gives 0'–5' without 2') | 0, 1 at the top and inside; 2–5 on the left; 0', 1' at the bottom; 4', 5' twice round the bay; 3', 2' on the right | As in the transcription
- [ ] 154 09-2 | reading | Rim marks of the pencil disk | α (twice), 1, 2, 3, 4, 5, 1', 2', 3', 5' | The transcription's list, which includes 4'
- [ ] 154 08-17 | reading | Top-left label over the first vertical | 1, overwritten on w' | 1 alone
- [ ] 154 08-17 | strike | Scribbles at the right end of the glued x/y form | Read as struck, not drawn | Marks to draw
- [ ] 154 08-15 | reading | Label right of the middle line of the stacked rectangles | w' | u'
- [ ] 154 08-15 | reading | Lower-left label at the a level | a' (?), a smudge | No label
- [ ] 154 08-10 | reading | Does the lower bank of the top spindle join the middle bank on the right before the tip? | It joins it | It runs separately to the tip
- [x] 154 08-7 | disagreement | Is the sectored disk cut by eight rays? | On the page the sectored disk is cut by lines through its centre into clearly more than eight sectors, twelve rays as drawn; the transcription's « huit rayons » is to be corrected. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [ ] 154 08-7 | reading | The second region sign (« 3 à longue queue ») | ζ | b or 5 (earlier pass), or another glyph
- [ ] 154 08-7 | reading | Strands of the small green disks, the faint disks at the right edge and the disk at the bottom right | Read from the crop | Other continuations at the dense crossings
- [ ] 154 08-2 | disagreement | Seventh letter below the rectangle | D (H G F E D C D A, as written) | An uncertain letter, as in the transcription
- [ ] 154 08-2 | strike | Wavy hatched stroke from C/G to B/E, and the scribble left of B/C, in the top diagram | Struck, left out | Part of the diagram, to draw
- [ ] 154 08-2 | reading | Route of C between the C/G and B/C crossings (overinked) | Through the B/C point | Another route
- [ ] 154 07-8 | reading | Top-left label of the pencil rectangle | 1 | 5
- [ ] 154 07-8 | reading | Labels on the violet disk | 0, 0′ | Other digits
- [ ] 154 07-8 | strike | Faint « 10 6 5 » inside the disk with two green arcs, and the scribble below the ξ circle | Struck, left out | Text to draw
- [ ] 154 08-1 | reading | Which pencil line continues which in the left disk and the lower circle; the ink path between the hub and the first star | As drawn | Other continuations
- [ ] 154 08-5 | reading | Long faint lines of the arrangement; the three dashed lines | Drawn straight | Slightly curved, other continuations
- [x] 154 08-4 | reading | Middle network of pencil arrows | Still schematic, main lines placed approximately | To redraw strand by strand
- [ ] 154 09-3 | reading | Overwritten label under the second D in the upper oval | D | x or y
- [ ] 154 09-3 | disagreement | « deux croix vert clair » at the top right | Three light green lines with two crossings, plus a small green cross below the banner | Two separate crosses, as in the transcription
- [ ] 154 09-5 | reading | Digits beside the left spindles | 1, 1, 1, 0 above; 0, 3, 2, 1 below | Other digits
- [ ] 154 09-5 | reading | Where do the strands D, D′, D″ cross the stacked arcs? | Approximate | Another crossing order
- [ ] 154 09-6 | disagreement | Region numbers (the transcription lists 12, 14, 15, 17, 21, 24, 27) | A second 12 near 17 | A single 12
- [ ] 154 09-7 | reading | Overinked digit in the middle of the braid lens | Left out | 2 or 3
- [x] 154 09-8 | reading | Does the lower-left strand of the left disk run on into the middle disk? | Yes, to its right contact; one strand starts on another near the top | It ends on the left rim
- [x] 154 09-8 | reading | The two right-disk strands from the upper-left contact | Two strands, one ending on the right rim | A third strand (dropped because it would cross another twice)
- [x] 154 09-8 | disagreement | Pencil « deux petits triangles » of the transcription | Not found on the crop | Present but faint
- [ ] 154 09-9 | reading | Labels round the half-crowned disk | 3, 4′, 5 left; 2′ top; 1′, 2′, 3′ bottom; 4′, 5′ right; 4′, 3′, 2′ outside upper right | Right-hand labels 4, 5 unprimed
- [ ] 154 09-9 | reading | Top-left label group « 1 5′ 4′ » and small top digits « 1′ 1 1 3 » | Not reproduced | As read
- [ ] 154 05-9 | reading | Which stroke continues which in the knot at the lower left of the bowl, and in the lower half of the square? | As redrawn | Other pairings
- [ ] 154 05-9 | disagreement | Faint pencil curved triangle and vase, not in the transcription | Drawn | Leave them out
- [ ] 154 07-2 | reading | In the large disk's lower half, are B6 and the end of Q3 separate pieces ending on Q1? | Ending on Q1 | Continuations of other strands
- [ ] 154 07-2 | disagreement | Two strands of the small disk's right group cross twice, and many pairs in the large disk cross more than once | Drawn as on the page | A simple arrangement
- [ ] 154 07-2 | disagreement | « croisement orange posé sur une droite verte »: the green line is not in the crop | Crossing drawn, line not drawn | The line is below the crop
- [ ] 154 07-3 | reading | Pencil digits next to the arrows | 4, 3, 2, =5 | 1 to 5, as in the transcription
- [ ] 154 07-3 | disagreement | Two thick red arcs « sur le bord » of the disk | The thick parts are the ends of one chord inside the rim | On the rim, as in the transcription
- [ ] 154 07-3 | reading | Is the red X on the black line two curves touching at one point of the line? | Touching | A crossing
- [ ] 154 07-5 | reading | In the column of disks, do the orange and red strands only touch at the tangency? | Touching, no exchange | They cross
- [ ] 154 07-5 | reading | Bump disk: two strands start side by side at the left notch and both end at the right notch; the vertical lens's upper ends are separate | As redrawn | Other pairings
- [ ] 154 07-7 | reading | Is each yellow wedge bounded by the two strands through its marked point and the outer rim? | As redrawn | Bounded by the green dip curve
- [ ] 154 07-7 | reading | Placement and count of the + and − signs | 7 +, 3 − | + above, − below, as in the transcription

## Folders 156-3 and 156-4, sketches marked and vectorised (9 November, evening)

- [x] 156-3 01-1 | disagreement | Is the sketch of p. 3 two points joined by one line, or two short vertical strokes joined by two curved strokes? | Two short vertical strokes joined by two lines (an upper straight one, a lower curved one), as drawn; the note's wording is loose. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-3 01-2 | disagreement | Same sketch on p. 4, where the lower line does not reach the left stroke | The same sketch, the lower line starting with a small hook short of the left stroke, as drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-3 02-1 | reading | Glyph at the right end of the second arc | b: each arc carries its letter at both ends (y–y, a–a, x–x). [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-3 02-1 | reading | Label at the lower end of the arc x, which leaves the band at the same point as arc a | x | t
- [x] 156-4 03-3 | reading | Primes of the first top and bottom nodes (one prime each on the crop) | F̄″, Ḡ″, as in the transcription | F̄′, Ḡ′
- [x] 156-4 03-3 | reading | Third top node: a bar and a small arrow, no clear prime | No prime on the page: an F under a bar with a small arrow added; the cube at the foot of the page has the same chain F′ ⊂ F⃗ ≃→ F with F⃗ over Ḡ, so the node is F⃗ (now set so); the transcription's F̄′ is to be corrected. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-4 03-4 | reading | Does the middle bottom node carry a tilde as well as the bar? | Ḡ only: the mark above the bar is the small vertical inclusion cup (the same cup stands above the tilde of G̃ in the next column), and the cube below has the same row G̃ ≃→ Ḡ ≃→ G. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-4 03-5 | strike | Is the F′ at the far left of the cube, joined by a double stroke to the hatched scribble, part of that struck insertion? | Struck: the double stroke that leads into the scribble runs across that F′, no arrow reaches it, and the cube has its one F′ in the middle with its arrows. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-4 04-1 | strike | Is the subdivision sign between F and F′ struck, or only overwritten? | Overwritten, not struck: heavy curved strokes forming a curly ≼ pointing to F; the only stroke across it is one of the long obliques that strike the whole paragraph. It is now drawn as ≼. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |

## Folders 156-2, 156-6 and 156-7, figures marked and redrawn (10 November)

- [ ] 156-2 01-5 | reading | P. 2, just above « Ẇ_t »: is this a sketch (a thin wedge hatched at its tip, joined by a stroke to the gloss « cl∖i ») or an interlinear word struck by a double line? | A sketch, drawn | A struck word: no drawing
- [x] 156-6 02-1 | reading | Is the small chevron before the central point a sign or a pen start? | The text names the figure « disque avec pt marqué », so the heavy point is the one marked point and the chevron is not a second one; it stays as the small stroke it is on the page. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-6 05-3 | disagreement | Where is the point on the triangle? | On the left side, about its middle, away from the vertices; the note's « près d'un sommet » is to be corrected. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-6 05-4 | reading | Are the top and bottom marks on the circle two marked points, or the start and join of the pen stroke? | Two points: the circle is drawn in two strokes, a left and a right arc, meeting at the two marks, which a single pen stroke would not give; an example with two edges sharing both ends also fits the passage on simplicial ateliers. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-7 01-3 | disagreement | Is the diameter vertical, with small crosses around? | No: the diameter is the quadrilateral's oblique diagonal, with two crosses outside (right and below); the note's wording is to be corrected. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-7 01-3 | reading | What is the small mark inside the quadrilateral, left of the circle? | A small cross of two short strokes, like the two outside; it is now drawn. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 156-7 04-3 | reading | Is the last label aₙ? | The glyph does not tell n from m and no formula nearby fixes it; either way the figure is the same segment a₁, a₂, …, up to a last point, and aₙ, as the transcription reads, stands. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |

## Folders 81 and 161-6, sketches marked and redrawn (10 November)

- [x] 161-6 01-5 | disagreement | In what cyclic order do the decagon's vertices run on p. 18? | The order is A₁, A′₃, A₀, A′₂, A₄, A′₁, A₃, A′₀, A₂, A′₄: the left letter reads A₂, and only A₃ at the bottom lets the pentagon of the Aᵢ run with indices decreasing by one, as the pentagon of the A′ᵢ does; the drawing stands and the transcription's note of p. 18 has A₂ and A₃ exchanged. [settled by the mathematics; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 161-6 01-5 | reading | Is the upper-right letter left as α₀, not rewritten into A₀? | The upper-right letter is α₀, not rewritten; the drawing stands. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 161-6 01-2 | disagreement | How many strokes leave the centre of the p. 12 circle? | Six strokes leave the inner point (five about 72° apart and a horizontal one to the left); the drawing stands and the note's « cinq rayons » is one short. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 161-6 01-4 | disagreement | Do u₁ and the circled u₀ sit in the innermost of three nested ovals? | Three nested ovals, u₁ and the circled u₀ both in the innermost; the drawing stands. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 161-6 01-4 | reading | How many vertices has the graph with rings and crosses on p. 16 (not redrawn)? | Eight vertices, the graph of the cube (a square inside a square, corners joined); it is now drawn in 01-4. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 161-6 02-3 | disagreement | What crosses the first circle of p. 21? | A bundle of three or four near-coincident strokes from the top and a separate oblique double stroke; the drawing stands. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 161-6 02-2 | reading | Which strokes of the margin icosahedron are edges? | On a 400 dpi crop: ten vertices and 21 edges as drawn; one hidden edge (upper left vertex to left inner vertex) made broken and one line weight moved. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 161-6 02-6 | disagreement | Is the second « disque » on p. 25 a full circle? | Not a full circle: the second outline leaves the first disc and returns to it; the drawing stands. [settled on the page; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 161-6 02-8 | reading | Should the doubtful « dans le » in the inner disc be drawn? | « dans le » is a line of the oblique marginal note crossing the ring; it stays out of the drawing, the figure (two nested closed curves) is the same either way. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 81 03-2 | disagreement | How many points does the p. 42 circle carry, and which are full? | 21: 7 full, 14 open (the grey point at the lower left drawn open) | About twenty, with another full/open split
- [x] 81 03-4 | disagreement | On which side of the text is the p. 47 circle with three chords? | At the left, in the margin | At the right, as in the note
- [x] 81 03-7 | disagreement | What stands at the top and foot of the band on p. 53 (also 03-8)? | A pair of opposite arrows, one above the other | A double arrow, as in the note
- [x] 81 01-5 | reading | How is the tangle at the lower left of the p. 10 polygon to be read? | A knot of thin unlabelled strokes over a small circle, to which no text refers: the redraw keeps the strokes that can be followed, and another grouping would not change the sketch. [of no consequence for the figure; machine pass on the facsimile, 2026-11-12, not checked by a reader] |
- [x] 81 02-3 | reading | Is the first sign of the p. 26 legend ⊃ or a hooked arrow like the others? | ⊃, as the transcription reads | ↩, written like the other hooks

## Folder 154, the three drawings completed on 10 November (07-7, 08-4, 09-8)

- [x] 154 07-7 | reading | Lower disk of the bottom-left pair: is the strand that turns a corner at the left one strand? | One strand with a corner; both stubs of the two crossing strokes drawn | Two separate strands that cross there
- [x] 154 07-7 | reading | Lower disk of the bottom-left pair: is the yellow region at the lower left one region, crossed by the cornered strand? | One region between two strands and the rim | Two regions, only one of them yellow
- [x] 154 07-7 | reading | Do the two disks of the bottom-left pair touch? | No, about 1.5 mm apart, as on the page | Tangent, as in the other figures of eight
- [x] 154 07-7 | reading | Top-right figure, upper disk: what are the thick red strokes from the top point to the two black marked crossings? | Thick parts of the two lens strands | Separate short strokes over the lens strands
- [x] 154 08-4 | reading | Middle network: which heavy stroke ends are arrowheads? | 18 arrowheads, only where barbs are visible | More (several heavy ends could be blunt arrowheads) or fewer
- [x] 154 08-4 | reading | Middle network: does the left arrow run on, faintly, to the marked crossing of the star? | Drawn as a thin pencil line reaching the star's dotted crossing | An unrelated faint mark; the arrow stops at its dot
- [x] 154 09-8 | reading | Is the arch over the first contact one strand with the lower-left strand of the left disk and the bottom strand of the middle and right disks? | Yes, one strand through all three disks, ending at the top of the right rim | Separate strands meeting at the feet of the arch
- [x] 154 09-8 | reading | Do two long strands cross twice at the first contact (the kite straddling the rims)? | Once in the left disk and once in the middle disk, the kite yellow | A single crossing, the kite being an effect of the overlapping rims
- [x] 154 09-8 | reading | Do neighbouring disks overlap in a narrow lens? | Yes, rims overlapping by about 1 mm at both contacts, as on the page | Disks glued along a common arc
- [x] 154 09-8 | reading | Is the strip between the two rims at the first contact yellow? | Yellow below the kite (two pieces), white above it | The whole strip is orange overpainting of the middle rim, not regions
- [x] 154 09-8 | disagreement | Where are the pencil « deux petits triangles » of the transcription? | Not found as triangles; four short pencil strokes beside red strands, drawn as underdrawing | Small triangles these strokes form with the strands, or marks no longer visible
- [x] 154 09-8 | disagreement | Right figure: is the main line light green, cut by four red lines? | A red horizontal line through the crossings, a light green line above and a second one climbing through the second crossing | The main line is light green, as in the transcription


## Finishing pass of 12 November: new questions

Raised while the sketches described only in notes were marked and redrawn; only doubts that neither the page nor the mathematics settles.

- [ ] 80 01-3 | reading | P. 9, centre of the big figure (see the enlarged inset): do the three curves D_A, D_B, D_C form one small triangle in the middle of the hexagon A, B′, C, A′, B, C′, each curve passing just beside two opposite vertices of the hexagon without going through them? | Yes: a small central triangle, the curves passing close to the vertices (simple crossings only, 37 regions) | No: the curves pass through hexagon vertices (triple points), or cross elsewhere under the blots
- [ ] 76 02-1 | reading | In the row of marks under the two overlapping segments (left margin of p. 28), which letters stand between « i » and the long dash before « n »? | Left out (they look like α, β and a j or γ) | i, α, β, j
