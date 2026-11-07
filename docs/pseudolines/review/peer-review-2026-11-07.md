# Pre-submission report: "Pseudoline arrangements, continued: cells, skeleta and added pseudolines"

Working draft, 7 November 2026. Simulated referee report requested by the author (Michel Hua) on his own manuscript `docs/pseudolines/article.tex`, before submission to Hexagon. Local processing only; no manuscript text was sent to an external service (only bibliographic metadata of cited works was looked up, see `citations-2026-11-07.md`). Intake validated with the peer-review skill's `validate_review_intake.py` (status READY_FOR_LOCAL_REVIEW; capacity: author-requested reader; no conflicts; review model of the venue assumed single-anonymised).

Competence limits: this is an automated, simulated report. It re-derives the proof steps, compares every statement with the Lean sources and the transcriptions, and ran one Lean check; it is not an independent expert report. The oriented-matroid part (Theorem 3.2 and its use with Folkman–Lawrence) should be read by a specialist.

Materials used: the manuscript; `lean/Grothendieck/Folder80Maps1.lean`, `Folder80Maps3.lean` (and the `PseudolineMap` structure of `Folder80Maps2.lean`), `Folder80Signs.lean`, `Folder154.lean`; `docs/lean/sections/80.tex`; the findings `80-lattice-criterion`, `80-skeleton-full-faithfulness`, `154-cyclic-order-determines-position`, `154-generisation-cube` in `src/content/findings.ts`; the transcriptions `transcripts/80/batch-02.fr.tex`, `batch-03.fr.tex` and `transcripts/154/batch-01.fr.tex`, `batch-08.fr.tex`; `docs/problems/article.tex`.

## Summary of the submission

Three statements from folders 80 and 154 are examined. (1) The criterion of folder 80, p. 26, for the closed cells to meet pairwise in a closed cell is refuted by five real lines, and replaced by the correct criterion (no two points carry all the lines), proved for every symmetric composition-closed set of sign vectors. (2) The full faithfulness of the skeleton functor (p. 54) is proved for combinatorial maps when every triangle has a fourth pseudoline avoiding its vertices; the remaining case is reduced to a sign lemma on chirotopes and the Folkman–Lawrence theorem. (3) Two statements of folder 154 (pp. 18 and 153) are proved for single-element extensions of rank-3 oriented matroids.

## Overall assessment

Parts (1) and (3) are correct and match the Lean statements. Part (2) is correct for Theorem 3.1. The chirotope part has a serious problem on the formal side (M1): the Lean theorem cited for it has inconsistent hypotheses and therefore verifies nothing. The mathematical argument itself survives, since it uses alternation only on bases, but the manuscript must stop saying it is formalised, and the statement must be given in the form actually proved. Several attributions and page numbers need correcting (M7, M8), and two claims are stronger than the evidence (M3, M6).

## Verification of the claims

| Claim | Check | Result |
|---|---|---|
| Prop. 2.2 (II'_{3,2} not latticial) | Lean `II32_not_lattice`, `lattice_criterion_false`, `II32_no_bigon`; by hand: each line carries ≥ 3 vertices; the corner faces x>2,y>1 ∪ x<0,y<0 (F) and x<0,y>1 ∪ x>2,y<0 (G) glue through the line at infinity; their closures use different edges of x = 0, x = 2, y = 0, y = 1 (the parts y>1 and y<0 of x = 0 are different edges, separated by [0:1:0]) and share only [0:1:0], [1:0:0] | correct; figure 1 shading matches |
| "Only if" half of p. 26 | `not_lattice_of_bigonal`, `not_lattice_of_four` (lines); the intersection of the cells v∘w and v∘(−w) is exactly {±v, ±w} when v, w are vertices | correct for lines; pseudolines via Folkman–Lawrence |
| Thm 2.3 | `lattice_iff_not_twoPencil`; `TwoPencil` takes two points not on all lines | correct |
| Thm 2.4 | `lattice_iff`: `Lattice L` is "for non-zero X, Y in L, PCl X ∩ PCl Y is empty or equals PCl W for some non-zero W ∈ L", PCl X being the non-zero covectors conformal to X or −X | statement correct; sketch of the converse too vague, see M5 |
| Abstract on "latticial" | Matches `Lattice` once "closed cell" means the set of cells conformal to ±X; the phrase "form a lattice" needs a bottom and top adjoined | minor wording, see m6 |
| Mohar–Thomassen sentence | No proof that latticial is equivalent to a polyhedral embedding of the dual; the finding register records that a face-width pointer for this folder was withdrawn | see M6 |
| Thm 3.1(1) | `faithful`: maps of flags commuting with α1 that agree on vertices and edges are equal | correct; sketch inaccurate, see m2 |
| Thm 3.1(2) | `lift_iff` | correct |
| Thm 3.1(3) | `finrank_Z1_le` (dim Z1 ≤ dim B1 + 1), `lineChain_not_mem`, `parity` (with transversality hypotheses), `triangle_iff` | correct; the parity statement needs "crossing transversally", see m1; (A5) is on p. 51, see M8 |
| Thm 3.1(4) | `full_of_fourth'` (FourthLine on the source arrangement only), `fourth_at`, `full_of_simpleCorner`, `full_simple`; uniqueness from `faithful` | correct |
| Combinatorial model | `PseudolineMap`: also every vertex on at least two lines (`two`); `Straight` | omission, see m1 |
| Thm 3.2 | `reorientation_of_sameSeparation` | **Lean hypotheses inconsistent**, see M1; statement shape differs, see M2 |
| "assertion of pp. 39–54 in all cases" | Needs Folkman–Lawrence, the rank-2 dictionary (cyclic order ↦ separation relation), and an argument that the homeomorphism induces the given skeleton isomorphism | overstated, see M3 |
| Thm 4.1 | `problem17_holds` (`Chirotope3` with SignType alternation, consistent) | correct |
| Thm 4.2 | `IsPosition.eq_of_zero_on_line`, `IsPosition.of_spec`, `genEquiv_spec_iff`, `cubeFace_subset_iff`, `card_gen`, `card_gen_stable`, `card_gen_substable` | correct; "not all zero" missing from the criterion; attribution too strong, see M7 |
| Page 18 of folder 154 | Transcription: the canonical map to antipody-compatible polygonal structures on Ĩ, and « il ne devrait pas être difficile de montrer que cette application est l'injection » | correct |
| Page 150, page 153 | p. 150: the cellular surface X* = Rel(Σ) of relative positions; p. 153: stable generisations ↔ vertices of a ν-cube, sub-stable ↔ edges, incidence = specialisation, counts 2^ν and ν2^{ν−1} | correct pages; 3^ν and the face poset are the edition's |
| Folder 154 title and date | Catalogue: « [Système de pseudo-droites] : notes manuscrites (1983-1984, s.d.) »; dated pages 23.12.83 to 2.2.84 | not given in the article, see m4 |
| Folder 80 pages | p. 22 (cas cruciaux), p. 24 (Théorème, boxed list with « I'_{3,2} », called « latticiels »), p. 26 (Cas latticiel, Prop.), p. 39 (Th. with orientation ω), p. 41 (théorème général des cartes, (19)–(21)), p. 42 ((23) c_2 = c(K)), p. 46 (« Bien entendu » for (A1)–(A3)), p. 47 ((A4)), pp. 50–51 (triangle orientation, (A5) on p. 51), pp. 52–53 ((A6), III_6 on p. 53), p. 54 (Théorème), p. 60 (definition by maps) | corrections, see M8 |

## Comments to the author

### Major

**M1. The Lean theorem for Theorem 3.2 is vacuous.**
- Location: §3, Theorem 3.2; abstract, last sentence; §5.
- Observation: in `Folder80Signs.lean`, `reorientation_of_sameSeparation`, `reorientation_of_locallyEquivalent` and `locallyEquivalent_of_sameSeparation` take alternation hypotheses `a12 : ∀ i j l, χ j i l = χ i j l + 1` and `a23 : ∀ i j l, χ i l j = χ i j l + 1` over all triples, with values in `ZMod 2`. Taking `j = i` gives `χ i i l = χ i i l + 1`, i.e. `1 = 0`.
- Evidence: checked with `lean_run_code`: from `a12 i i i` one derives `False` (four lines, compiles with no errors). So no χ satisfies the hypotheses as soon as there is one line, and the three theorems are true vacuously.
- Why it matters: the article says the proofs are formalised. For Theorem 3.2 they are not.
- Requested action: say in the article that Theorem 3.2 is not formally verified as it stands, and why. The mathematical proof uses alternation only on bases (and symmetry of the product only for pairs in distinct classes), so restricting `a12`, `a23` to `Basis on i j l` should repair the Lean file; that change is outside this article and is reported to the author. **Done in the article** (Theorem 3.2 labelled as not formalised, abstract and §5 corrected).

**M2. Theorem 3.2 is not stated in the form proved.**
- Location: Theorem 3.2.
- Observation: the manuscript speaks of "chirotopes of two bigon-free arrangements and a bijection σ preserving incidences, such that the cyclic orders agree up to reversal, that is, the same separation relations". The argument (and the intended Lean statement) concerns one incidence structure (two lines meet in exactly one point, every point on at least two lines, every line carries at least three points), two alternating sign functions on its bases (triples of distinct lines without common point), and the hypothesis that their four-term sums along each line agree. No Grassmann–Plücker relation is used. The identification of these sums with the cyclic order up to reversal is a rank-2 fact about actual arrangements, not part of the proof.
- Requested action: state the theorem for one incidence structure with sign functions on bases, define the separation sums, and put the passage from cyclic orders to separation sums in the paragraph that applies the theorem. **Done.**

**M3. "this gives the assertion of pages 39–54 in all cases".**
- Location: paragraph after Theorem 3.2.
- Observation: the conclusion needs (i) the topological representation theorem, (ii) the rank-2 dictionary (on an arrangement the separation sums along a pseudoline are those of the cyclic order of its vertices), (iii) a check that the homeomorphism induces the given isomorphism of skeleta (true because a bigon-free pseudoline carries at least three vertices, so an edge is determined by its pseudoline and its ends), and it concerns topological arrangements, whereas Theorem 3.1 is about combinatorial maps. Point (i) and (ii) are not formalised and the Lean statement for the sign step is vacuous (M1).
- Requested action: soften to "for topological arrangements, these steps give the assertion for every bigon-free arrangement, modulo (i) and (ii); the argument is the edition's and has not been checked by a specialist". **Done.**

**M4. Reading of page 26.**
- Location: §2, quoted Proposition.
- Observation: « bigonales » is an uncertain reading, and b) « pas de type II_4 » is read as "not of type II_4" by the edition (the finding records this; "contains no II_4" would exclude II_5, which page 24 calls latticial). Page 24 writes the configuration « I'_{3,2} ».
- Requested action: say so. **Done.**

**M5. Sketch of Theorem 2.4, converse.**
- Location: proof of Theorem 2.4.
- Observation: "take a maximal common face; any common face is conformal to it unless ..." does not say which common faces nor why. The Lean proof: if some non-zero covector is a face of X and of −Y, replace Y by −Y; then no non-zero face of X is a face of −Y (otherwise two faces with disjoint supports appear). The common faces of X and Y are closed under composition, so the one with largest support, M, has every other one as a face (M ∘ Z is again common, with support at least that of M, hence equal), and the intersection is the closed cell of M.
- Requested action: replace the sketch with this argument. **Done.**

**M6. Polyhedral embeddings.**
- Location: end of §2.
- Observation: the sentence "latticial says that the dual cell structure is a polyhedral embedding; compare face-width ≥ 3" is not proved, and the cell intersections involved (cells of all dimensions) are not those of the definition of a polyhedral embedding (faces only). The finding register records that an earlier face-width pointer for this folder had to be withdrawn.
- Requested action: remove the sentence and the reference. **Done** (Mohar–Thomassen removed).

**M7. Attribution and model in §4.**
- Location: §4, opening paragraph and Theorem 4.2.
- Observation: (a) Las Vergnas's theorem (1978; Björner et al., Th. 7.1.8) says a cocircuit signature defines a single-element extension iff it does so on every rank-2 minor; the line-by-line form "+…+ (0) −…−, at most one zero" is its specialisation in rank 3, written by the edition, and it needs "not all zero" (which excludes the pseudolines of Σ themselves) and the orientation signs comparing each chosen cocircuit with the orientation of the line. (b) Page 153 states only that stable generisations correspond to the vertices of a ν-cube and sub-stable ones to its edges, with the two counts; the 3^ν generisations, the face poset and the oriented-matroid model are the edition's.
- Requested action: cite Las Vergnas 1978 and the book; label Theorem 4.2 "after p. 153" and say what the page states. **Done.**

**M8. Page numbers in §3.**
- Location: §3 assertion and Theorem 3.1(3).
- Observation: the « Théorème » is on p. 54 (p. 39 states full faithfulness for skeleta with an orientation ω); (A5) is stated on p. 51 (the triangle discussion is pp. 50–51); « Bien entendu » on p. 46 concerns (A1)–(A3), not (A1)–(A6); (A6) is on pp. 52–53, the complete quadrangle on p. 53.
- Requested action: correct. **Done.**

### Minor

- **m1.** Location: §3, model and Theorem 3.1(3). Observation: the model omits "every vertex lies on at least two pseudolines" (`two`); the parity statement in Lean assumes the pseudoline crosses the boundary transversally (no edge in common, crossing straight at each common vertex). Action: add both. **Done.**
- **m2.** Location: proof of Theorem 3.1(1). Observation: "determined by the image of one flag" is not the argument and needs connectedness. Lean: a flag and its α2-image have the same vertex and edge, and their α1-images lie on different edges (bigon-freeness); so a map commuting with α1 is fixed by its action on vertices and edges. Action: rewrite. **Done.**
- **m3.** Location: same proof, (3). Observation: "z + D" with D undefined. Action: define D as the cycle of a pseudoline. **Done.**
- **m4.** Location: §1. Observation: folder 154's title and dates are not given. Action: add « [Système de pseudo-droites] », notes dated December 1983 to February 1984. **Done.**
- **m5.** Location: figures. Observation: in Figure 2 the triangle's fill is drawn over its sides, which makes the apex look broken, and the caption's last sentence speaks of ∂T not bounding, which is impossible for the boundary of the face T; in Figure 3 the label "D = (0,0)" collides with "(+,0)". Action: redraw; rephrase the caption in terms of the eight triangle cycles; add a figure of a vertex, its corners and a three-edge face path. **Done.**
- **m6.** Location: §2, definition. Observation: the closed cells form a lattice only after a least and a greatest element are adjoined. Action: say so. **Done.**
- **m7.** Location: §3. Observation: for simple line arrangements, determination by local sequences is classical (Goodman–Pollack, see Felsner–Goodman §5.2). Action: one sentence of context. **Done.**

## Limitations of this report

The Lean files were read, not rebuilt; only the inconsistency of M1 was checked by running Lean. The facsimiles were not consulted; page numbers were checked against the transcriptions. The rank-2 dictionary and the use of Folkman–Lawrence in M3 were checked by argument only.

## Confidential comments to the editor

None (author-requested report).
