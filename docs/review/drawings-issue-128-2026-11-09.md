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

## Folder 70

- [ ] 70 04-1 | strike | Is everything left out of this drawing struck out on the page? | Left out as struck: the wavy scribble along the top, the inked blot inside the triangle, the overwritten strokes right of the σ₀ line, four faint erased lines | 
- [ ] 70 04-3 | strike | Is everything left out of this drawing struck out on the page? | Left out as struck: the formulas over the left trihedron, the zigzag "hatched plane", a scribbled Z and W, the sinusoid | The sinusoid belongs to the drawing
- [ ] 70 04-2 | reading | Is the solid triangle a deliberate fill? | A deliberate fill, drawn filled | A strike-out, to leave out
- [ ] 70 04-5 | reading | Do s₁ and s″₃ carry a bar on the page? | Barred, as in the transcription | No bar visible
- [ ] 70 03-1 | disagreement | What follows « ≤ » on the page? | One index, read j+1 | « j−1, j+1 », as in the transcription
- [ ] 70 04-8 | disagreement | How is the top vertex labelled? | s′₀ | As in the transcription
- [ ] 70 05-1 | disagreement | Is there an s₂ label on the polyhedron? | No s₂ visible | s₂ as in the transcription
- [ ] 70 04-6 | disagreement | What are the proportions of the rectangle? | About 3:4 | Golden, as in the transcription
- [ ] 70 06-1 | disagreement | What is struck in this sketch? | One sign only | The whole sketch
- [ ] 70 07-1 | reading | Are σ₁ and σ₂ placed right? | Placed after the transcription; on the page they run into the formulas | 
- [ ] 70 01-3 | reading | Are the matrix entries where the page has them, with the struck ones left out? | As redrawn | 

## Folder 154

- [ ] 154 04-3 | reading | Does the red X cross on the dark green line? | Yes, snapped onto it | 
- [ ] 154 02-2 | reading | Do the three orange lines meet at the apex of the dashed arc? | Yes, with a black point drawn there | 
- [ ] 154 01-7 | reading | Does the snapped drawing still match the page? | As redrawn | 
- [ ] 154 06-8 | reading | Does the snapped drawing still match the page? | As redrawn | 
- [ ] 154 08-3 | reading | Does the snapped drawing still match the page? | As redrawn | 
- [ ] 154 08-4 | reading | Does the snapped drawing still match the page? | As redrawn | 
- [ ] 154 02-6 | reading | Does the snapped drawing still match the page? | As redrawn | 
- [ ] 154 07-4 | reading | Should these nearby stroke ends meet at one corner? | Merged into one corner | Separate ends
- [ ] 154 06-16 | reading | Should these nearby stroke ends meet at one corner? | Merged into one corner | Separate ends
- [ ] 154 02-5 | reading | At the four antipodal blue marks, are the strands paired right? | The two near-vertical strands and the two near-horizontal ones meet only at the marks | 
- [ ] 154 02-9 | reading | On the right, near the small yellow region, which strand continues which? | The upper-left strand goes on to the lower-right rim, the top strand to the dark green arc; one strand ends at that crossing | 
- [ ] 154 02-9 | disagreement | How many small triangles are there near the rim? | Five orange wedges at the rim, plus five small regions inside | Six, as in the transcription
- [ ] 154 02-14 | reading | In the lower isolated disk, are the strands paired right, and are the pencil ticks rightly left out? | As redrawn | 
- [ ] 154 09-4 | reading | In the left disk, is the dashed path a closed loop along the strands, with three triple points? | Yes | 
- [ ] 154 09-7 | disagreement | Which labels does the orange disk carry? | Also 4, 4′, 5′, 6, 7, 7′, 8, 9′ | Only 1, 2, 3, 1′, 2′, 3′, 5, 6′, 8′, 9, as in the transcription
- [ ] 154 09-7 | disagreement | How many blue arcs has the pencil circle? | Three, plus a pencil arrowhead on the right | Four, as in the transcription
- [ ] 154 09-7 | disagreement | In what order do the small disk's labels run, from the top? | 1, 0, 4, 5, …, 9, as in the sequence written above it | 9, 0, 1, 2, 3, 4, as in the transcription
- [ ] 154 02-15 | reading | In disk A, does the short solid strand from the top rim end where D₁ crosses the dashed strand? | Yes | 
- [ ] 154 02-15 | reading | In disk B, does a short solid stroke run from D₀ to the right-hand dashed strand, closing the hatched region? | Yes | 
- [ ] 154 02-15 | reading | In disk D, does a solid strand start on the lower dashed strand, cross D₀ once and reach the bottom rim? | Yes | 
- [ ] 154 05-1 | reading | Are the grey pencil lines strands of the arrangements, or the underdrawing? | Not yet decided; the drawing is left as it was | 

## Folder 74

- [ ] 74 03-1 | reading | Do the hexagon's sides end in arrowheads? | Yes, small hooks read as arrowheads | No arrowheads, as in the earlier redraw
- [ ] 74 03-5 | disagreement | Is the glyph a ξ or a pair of braces? | ξ, the same glyph as elsewhere on the page | Braces {1 2} … {i, i+2}, as in the transcription
- [ ] 74 03-4 | disagreement | Where are the labels ξ12, ξ25, … and x1…x6? | ξ on the upper hexagon's vertices, x1…x6 on the lower | Pairs beside two hexagons on x1…x6, as in the transcription
- [ ] 74 03-7 | disagreement | What are the labels? | τ, τ′, τ″ and their bars; no dotted diagonals visible | τ1, τ2, τ3 with dotted diagonals, as in the transcription
- [ ] 74 04-3 | disagreement | Where is k, and which vertices is u joined to? | k at the bottom left; u joined to j, q, r | A rectangle i p q k, u joined to p, q, r
- [ ] 74 06-6 | disagreement | Where are s and t? | Below the triangle, each joined to its own bold point | As in the transcription
- [ ] 74 02-4 | disagreement | Which cone carries α, β, γ? | The left (first) cone; the 3×3 square stands by the second | As in the transcription
- [ ] 74 07-4 | strike | Is the first sketch struck out? | Left out as struck | An abandoned start of the same chain, to draw
- [ ] 74 07-9 | reading | Which strokes of the cube are dashed? | As redrawn | 
- [ ] 74 06-4 | reading | Are the vertex letters placed right? | As redrawn | 

## Folder 69

- [ ] 69 04-5 | reading | Does the whole-page redraw match the page, including the arrowed parallelogram kept from the earlier redraw? | As redrawn | 
- [ ] 69 04-8 | reading | Are the large polyhedron and the middle figure read right from the overdrawn strokes? | As redrawn | 
- [ ] 69 06-12 | reading | Is the faint plane outline rightly left out? | Left out | To draw
- [ ] 69 01-10 | reading | Are D₆ and D₇ right, and where is w‴? | D₆, D₇ approximate; w‴ not located | 
- [ ] 69 05-2 | reading | What are the end labels of the c and b fans? | Illegible, left out | 
- [ ] 69 03-1 | disagreement | Where does the branch leave the bar, and are α, β written at its ends? | From the left end; α, β not visible | From the middle, with α, β, as in the transcription
- [ ] 69 05-12 | disagreement | Is the second bracketed diagonal matrix (λ₁, λ₁⁻¹ … λ_r, λ_r⁻¹) a drawing to mark? | On the page, with no mark | 
- [ ] 69 01-14 | disagreement | Is it a three-branch star? | A central triangle with two spikes at each vertex | A three-branch star, as in the transcription
- [ ] 69 05-3 | disagreement | How many points do the broken lines show? | About 4 and 3 | 3 and 2, as in the transcription
- [ ] 69 06-4 | disagreement | What are the small prism's two upper labels? | Like 6 and 4′, left out | Primes, as in the transcription

## Folder 142

- [ ] 142 06-18 | reading | Do the three lines through the centre meet at one point on the page? | One line rerouted through the computed centre | 
- [ ] 142 06-12 | reading | Are the three bands and their label indices right? | Bands drawn as smooth closed curves; indices a reading | 
- [ ] 142 06-15 | reading | Are the schematic arrows acceptable? | Inked and rotation arrows schematic; many pencil strokes left out | 
- [ ] 142 03-3 | disagreement | Is it an octahedron? | A triangular bipyramid (three Q vertices: 5 vertices, 9 edges) | An octahedron, as in the transcription
- [ ] 142 03-2 | disagreement | Where do the incisions start? | From P_ε′ at the bottom | From P_ε, as in the transcription
- [ ] 142 03-4 | disagreement | What does the label by the bottom hole read? | ≃R₀ | R_{ω′i} ≃ R₁, as in the transcription
- [ ] 142 06-6 | disagreement | What are the circle labels? | 1, i, i, 1 | 1, i, −1, −i, as in the transcription
- [ ] 142 06-7 | disagreement | How many times is « β relevé » written? | Twice | Once, as in the transcription
- [ ] 142 06-9 | disagreement | What is the inscription in the loop? | (a₁⁻⁻ a₁⁻⁺) | (a₁⁻ a₁⁺)⁻¹, as in the transcription
- [ ] 142 06-17 | disagreement | Which indices do the labels carry, and how many copies of 0 and ∞ are there? | R^{∞,1}_r; one copy each of 0 and ∞ | R^{∞,0}_r; two copies of each vertex, as in the transcription

## Folder 144

- [ ] 144 03-8 | reading | In which sense do the small rotation arrows of the frames turn? | Not drawn: their senses are not legible | 
- [ ] 144 07-9 | reading | In the crowded centre, which nodes do the short strokes join? | As redrawn | 
- [ ] 144 07-10 | disagreement | What is the index on M′^! → M′? | 6 | σ
- [ ] 144 07-11 | disagreement | Is there a node M under Z^!_{0ρ} = M(j̄)? | Yes, read M | Not in the transcription's list
- [ ] 144 09-3 | reading | Is the stack of boxes read right from the overinked sketch? | As redrawn, hatching as a pattern on one face | 
- [ ] 144 07-2 | reading | Which of ũ, ṽ, ρ̃, σ̃ is each turned label? | A reading, uncertain | 
- [ ] 144 03-4 | disagreement | How many triangles carry a frame label? | Nine; τ₀τ∞r occurs twice | Ten, as in the transcription
- [ ] 144 07-1 | disagreement | Which labels are underlined? | M^{!∘} and M^∘ look underlined; the stroke under M^! may be an edge | M^! underlined, the others plain, as in the transcription
- [ ] 144 07-7 | disagreement | Is there a label Π′ in the second row? | Yes | Not in the transcription's list
- [ ] 144 07-8 | disagreement | What is the overwritten middle node? | S | Not in the transcription's list
- [ ] 144 04-5 | disagreement | Do the three equator dots carry labels 0, 1, ∞? | No legible label | 0, 1, ∞, as in the transcription

## Folder 83

- [ ] 83 01-6 | disagreement | How are the triangle's vertices labelled? | v₁ at the top, v₂ on the left, v₀ on the right; the centre unlabelled under a blot; no u or u₀ on the figure | u₀ at the top and u, as in the transcription, which omits v₀
- [ ] 83 04-1 | reading | Is this the schema meant by the mark (the words yzt/ztx, xyz/yzt, xyz/txy joined by two strokes, middle of p. 75)? | Yes, relocated there from the brackets under a formula | 
- [ ] 83 10-3 | reading | Do the cube's edges stop short of the corners on the page? | As redrawn | 
- [ ] 83 10-4 | reading | Do the cube's edges stop short of the corners on the page? | As redrawn | 
- [ ] 83 11-4 | disagreement | Are « f, f′ » above the cube labels of the figure, and is there a diagonal i? | Words of the text line (« Si f, f′ sont »); only a letter i in the back face | Labels f, f′ and a diagonal i, as in the transcription
- [ ] 83 03-2 | disagreement | Is there a star of diagonals inside the pentagon? | Only fragments | A star of diagonals, as in the transcription
- [ ] 83 01-5 | reading | Is there a vertex labelled t, and what is at the vertex v₃? | Strokes lead to a vertex t; v₃ placed after the transcription | 

## Folder 57

- [ ] 57 08-4 | reading | Are the strokes of the dense sketch groups right? | Redrawn group by group, approximate | 
- [ ] 57 08-6 | reading | Are the strokes of the dense sketch groups right? | Redrawn group by group, approximate | 
- [ ] 57 07-1 | reading | Are the labels right? | As in the transcription | 
- [ ] 57 01-1 | strike | Is the left-out part of the top row struck out on the page? | Left out as struck | 
- [ ] 57 14-1 | disagreement | How many triangles are there? | Two | Four, as in the transcription

## Folder 146

- [ ] 146 04-6 | disagreement | Is the left figure a hexagon (two triangles side by side and their diagonals)? | A pentagon whose centre is joined to all five vertices | A hexagon, as in the transcription
- [ ] 146 04-9 | disagreement | What does the figure show, and what are its labels? | A path of two edges through three points, middle label 0, left label a sideways ∞ (or 8); no large ellipse with ∞ in this region | A dessin 0 – 1 – 0 with a large ellipse carrying ∞, as in the transcription
- [ ] 146 03-6 | strike | Are the ellipse, the sphere in lunes, the tetrahedron and the bottom-right sphere all struck out? | Left out as struck; only the small sphere, the arrows, the legends and D1 drawn | 
- [ ] 146 03-6 | reading | Is the « ℤ » a letter, or the start of the zigzag stroke? | ℤ, as in the transcription | The start of the zigzag stroke
- [ ] 146 04-4 | strike | Are the first D12 sphere and the label D2 struck out? | Left out as struck | 
- [ ] 146 01-5 | disagreement | How many looped points are on the equator? | Five | Four, as in the transcription
- [ ] 146 07-2 | disagreement | Which vertex does « a » label, and does the right side bend? | The right side bends at a vertex, which « a » labels | « a » at the top vertex, as in the transcription
- [ ] 146 02-2 | reading | Is the top label Q+ or Q with a bar? | Q+, as in the transcription | Q̄
- [ ] 146 04-14 | reading | Does the whole-page redraw match the overdrawn pencil? | As redrawn | 

## Folder 79

- [ ] 79 15-10 | disagreement | How many triangles are there round the vertex? | Seven triangles, eight spokes, one sector open on the left | Six triangles, as in the transcription
- [ ] 79 15-12 | disagreement | Is it a pentagon with all its diagonals? | A hexagon (short top side) with two interlaced triangles; the stroke from the lower left vertex stops short of the right side | A pentagon with all vertices joined, as in the transcription
- [ ] 79 14-2 | disagreement | How are s, t, u, v joined, and where are the small circles? | A path s – u – v – t of three segments, one small circle beside each segment | s, t joined to u, v, small circles marking the vertices, as in the transcription
- [ ] 79 14-2 | strike | Is the scribbled trial under the schema struck out? | Left out as struck | 
- [ ] 79 14-3 | reading | Is A₀ a label on a side? | A₀ placed at the lower left after the transcription | The scrawl there reads « A d … » and may be text
- [ ] 79 15-5 | reading | What are the labels of the rhombus and of the far-right quadrilateral (crop widened)? | Rhombus labels left out; lower left vertex of the far-right quadrilateral read s′ | An overinked letter by the rhombus; a mark (perhaps λ) above s′
- [ ] 79 15-7 | reading | Are s, t, λ⁻¹s, λ⁻¹t written round the dotted square? | Left out: sideways, small, not legible | Written sideways at the sides of the square
- [ ] 79 15-3 | reading | How many superposed strokes are in the lower figure? | Two strokes from the upper point to the lower t, one bent through the end of s–t | Uncertain: overinked
- [ ] 79 15-3 | strike | Is the short stroke right of the column struck out? | Left out as struck | 
- [ ] 79 15-13 | reading | Does the faint circle pass through λt = t′? | Drawn whole, through λt = t′ | 

## Folder 127

- [ ] 127 01-4 | disagreement | In what order are T′ → T and X′ → X, and does T′ – T carry an arrowhead? | X′ → X above T′ – T, with no visible arrowhead on T′ – T | T′ → T above X′ → X, as in the transcription
- [ ] 127 01-2 | disagreement | Is X_n → X a plain arrow? | Like Y_n, a hooked stroke ending at the brace | A plain arrow, as in the transcription
- [ ] 127 01-2 | reading | Are the labels G_n and U_n? | G_n, U_n, as in the transcription | They read like G_{U_n} and U_{nn}
- [ ] 127 01-2 | strike | Is the word after « Ass U^ » struck out? | Left out as struck | 
- [ ] 127 01-3 | reading | What are the labels beside X′ in the right sketch? | x₀, x′₀, by analogy with the left sketch | Small overinked marks, prime placement unclear
- [ ] 127 01-1 | reading | Is the last letter of the pencil formula T_y? | T_y | A T with a curl
- [ ] 127 01-8 | reading | Are the bottom sketches right? | Schematic | 

## Folder 148

- [ ] 148 04-1 | disagreement | Is there a region label A_{∞1}? | Not found: five A-labels seen | Listed by the transcription
- [ ] 148 04-2 | disagreement | How many ringed vertices and nested red curves are there? | Eleven ringed vertices, eight closed red curves | Nine and nine, as in the transcription
- [ ] 148 02-1 | reading | What colour are the long arc and the edge from the left vertex? | Arc red-brown, edge plain ink | The arc may be a stain; the earlier redraw drew the edge red-brown
- [ ] 148 01-4 | reading | Which four small triangles form the heavy rhombus? | Not singled out; seven heavy small triangles drawn thick | 
