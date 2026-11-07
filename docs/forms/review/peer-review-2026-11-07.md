# Peer-review working draft — FORMS-SELF-2026-11-07

> Working draft prepared at the author's request on his own manuscript (`docs/forms/article.tex`, version of 7 November 2026, before submission to *Hexagon*). Local only. It is not a journal review and announces no editorial decision. The author remains accountable for every statement below and for the revised text.

## Intake record

- Reviewer capacity: `author_requested_reader` (simulated referee, AI-assisted, disclosed)
- Peer-review model: `open` (author and reader known to each other; pre-submission)
- Declared processing plan: `approved_ai_assistance`, local only, no external service received manuscript text
- Intake validator: `READY_FOR_LOCAL_REVIEW` (warnings: no confidential editor channel; competence limit declared)
- Reporting guidelines: none of the clinical/biomedical checklists applies to a mathematics article; the selector was not run.

Sources used for the check: the French Lean-appendix sections `docs/lean/sections/156-1.tex`, `156-2.tex`, `156-3.tex`, `156-4.tex`, `121.tex`; the modernised readings `transcripts/156-*/156-*.modern.tex` and `transcripts/121/121.modern.tex`; the Lean files `lean/Grothendieck/Folder156_1.lean` … `Folder156_4.lean`, `Folder121.lean`; the findings in `src/content/findings.ts`. The Lean files were read, not rebuilt.

# Comments to authors

## Evidence-bounded summary

The paper states and proves five groups of results drawn from Grothendieck's notes of June 1986 (folders 156-1 to 156-4) and the folder *Topologie modérée* (121): (1) a segment model of a one-dimensional form is the same as a bounded, dense, two-sided locally directed partial order (a biorder); (2) the order of an ordered stretch is determined up to reversal by comparability and the unlabelled partitions of the sets C(ε) into pieces; (3) the map from the sides of a subset A to the clopen sets of a space of local sides over A is an injective morphism of Boolean algebras, for any A in any space; (4) the saturated parts of a poset with a symmetric relation form a complete ortholattice, which need not be distributive (a seven-element counterexample to the Boolean presumption of folder 156-4, p. 68); (5) a Boolean algebra of tame subsets satisfying (c bis), (d), (e) admits a coarsest admissible cell decomposition for every finite family, and a coarsest one with connected cells under (f). Each result is said to be formalised in Lean.

## Strengths

- Every theorem is stated precisely enough to be checked, and the paper is honest about what the pages do and do not prove.
- All sixteen Lean names cited in Section 7 exist in the repository (checked by name; none of the five files contains `sorry`).
- The hexagon counterexample is small, explicit and decisive; I re-derived it by hand (below).
- The observation that the large betweenness needs a comparability clause is correct and well chosen.

## Major comments

### Major comment M1

*Circular description of the order from betweenness.*

- Location: proof of Theorem 3.2.
- Observation: the description reads "u ≤ v iff there are x, y … such that x ≤ u ≤ y, x ≤ v ≤ y and u lies weakly between x and v". The first two conditions are stated with ≤, the very relation being reconstructed, so the description is not expressed in betweenness and comparability.
- Evidence or criterion: `ReadLe` and `le_iff_readLe` in `Folder156_3.lean` use the large betweenness R̄ for all three conditions: R̄(x,u,y), R̄(x,v,y), R̄(x,u,v), with x = a or R(b,a,x), y = b or R(a,b,y). The proof that this characterises ≤ uses x ≤ a < b ≤ y, which forces R̄(x,u,y) into the form x ≤ u ≤ y.
- Why it matters: as written, the key step of the theorem does not transport along the bijection.
- Requested action: state the three conditions with R̄ and give the two-line argument for the converse direction.

### Major comment M2

*Proof sketch of Theorem 6.1 removes the wrong set.*

- Location: proof sketch of Theorem 6.1.
- Observation: the sketch removes "the union of the frontiers, relative to Z, of the members of the family and of their closures". The proof (and the Lean step `step`) removes only X′ = ⋃ bd_Z(Y ∩ Z), Y ∈ 𝓛. The closures enter one level down: the removed closed part X′ is decomposed by induction for the family {Y ∩ X′} ∪ {Ū ∩ X′ : U an open cell}. That second family is what makes the frontier condition hold between an open cell and the cells of X′, and it is missing from the sketch. The coarsest-ness argument also needs that the restriction of a competing decomposition to X′ is good for this enlarged family.
- Evidence or criterion: Lean `Folder121.lean`, theorem `step`: `X' := ⋃ Y ∈ L, bd Z (Y ∩ Z)` and the recursive family `L' := L.image (· ∩ X') ∪ U.image (closure · ∩ X')`.
- Why it matters: A reader following the sketch would build a different (and unjustified) induction; the frontier condition between open cells and cells of X′ would be unexplained.
- Requested action: rewrite the sketch accordingly.

### Major comment M3

*Page 15 of folder 156-2 misreported.*

- Location: Section 4, paragraph before Theorem 4.1.
- Observation: the text says the page writes "injective", with "bijective if X is paracompact" added above the line. The transcription and the finding `156-2-rives-cut-along-closed-set` say the opposite: the page first writes « bijective si X paracompact » and adds « injective, et » above the line.
- Evidence or criterion: Transcription footnote in `transcripts/156-2/156-2.modern.tex` (« La page écrit d'abord « bijective », puis ajoute « injective, et » au dessus de la ligne ») and the basis of finding `156-2-rives-cut-along-closed-set`.
- Why it matters: A factual error about the source in an edition paper.
- Requested action: correct.

### Major comment M4

*Attributions.*

- Location: Theorem 2.1, Lemma 3.1, Theorem 5.2, Section 2 after Theorem 2.1.
- Observation: five attribution problems.
  - Theorem 2.1 is labelled "Grothendieck, pp. 10–13". Pages 12–13 state both directions, but neither is proved, the hypothesis F′3 is the edition's reconstruction of a mostly illegible note at the foot of page 6, and the "locally directed upwards" clause is read only in part. "After …" with a sentence on what the page provides is more accurate.
  - "The order need not be total, as the reading of the folder notes" — the pages do not say this; the modern reading stresses it, and the example is the edition's. "The reading" is also undefined for a reader of the article.
  - "Axiom F3 of the page is a weaker form of F′3": unsupported. F3 compares two segments issued from a place; F′3 is a directedness condition inside one segment, which the page's margin says is missing (« Il manque … F′3 ») for the transitivity of "same branch". Neither implies the other in an obvious way, and the paper uses no such implication.
  - Lemma 3.1: the iff form is the edition's; the page computes the three pieces and the disjointness pattern. Label "after p. 15".
  - Theorem 5.2 is the edition's counterexample to page 68, not a statement "after" page 68.
- Evidence or criterion: the rule of the edition ("Grothendieck, folder N, p. X" only where the page states it), the transcriptions, and the findings `156-1-segment-biorder`, `156-3-betweenness-from-cuts`, `156-4-supports-boolean-presumption`.
- Why it matters: attributions are the main historical claim of the paper.
- Requested action: adjust labels and sentences.

### Major comment M5

*Topology on Ã and the map not stated precisely.*

- Location: Section 4.
- Observation: "the topology generated by the sets where a locally constant function on W ∖ A takes the value 1" does not say what "takes the value 1" means at a point (x, χ) of Ã, and the map Riv(A, X) → Comp(Ã) is never written. The theorem depends on both choices.
- Evidence: `Spec`, its `TopologicalSpace` instance and `toSpecSet` in `Folder156_2.lean`: basic opens {(y, χ) : y ∈ W, χ(f_y) = 1}, W open in X, f locally constant on W ∖ A, f_y its germ at y; the map sends ρ to {(x, χ) : χ(ρ_x) = 1}.
- Evidence or criterion: See Observation.
- Why it matters: Without the topology the statement "the image of each side is clopen" has no content.
- Requested action: state both. Also replace "Stone-type space" in the abstract (Ã need not be compact or Hausdorff).

## Minor comments

### Minor comment m1

*F5 and branches undefined.*

- Location: axiom list, Section 2.
- Observation: "branch" and "order 2" are not defined; F5 reads as if every two segments define different branches.
- Evidence or criterion: Definition of `SameBranch` and `OrderTwo` in `Folder156_1.lean`; reading of 156-1, p. 6.
- Why it matters: The axiom list is otherwise unreadable on its own.
- Requested action: define "same branch at x" (a common initial subsegment I_{x,z} = J_{x,z} with z interior to both) and write "there are two segments issued from it that define different branches".

### Minor comment m2

*Biorder undefined.*

- Location: Section 2.
- Observation: "biorder" is used in Section 2 but not defined.
- Evidence or criterion: Reading of 156-1, p. 13: « une paire d'ordres opposés ».
- Why it matters: The word is the title of the section and is used before it is defined.
- Requested action: define a biorder as a pair of mutually opposite orders (a partial order up to reversal).

### Minor comment m3

*Abstract.*

- Location: abstract.
- Observation: "bounded, dense partial order" omits "with distinct least and greatest elements".
- Evidence or criterion: Theorem 2.1 requires x₁ ≠ x₀.
- Why it matters: Without distinct bounds a one-point order would qualify.
- Requested action: add "with distinct least and greatest elements".

### Minor comment m4

*Directedness in Theorem 3.2's remark.*

- Location: remark after Theorem 3.2.
- Observation: "dense partial order directed in both directions" uses global directedness (any two elements have a common lower and a common upper bound), not the local directedness of Section 2. Say so. Also the margin's own large form (« {a, b, c} of cardinality ≤ 2 ») fails already for a = c ≠ b; the paper only discusses the reading's substitute.
- Evidence or criterion: `Troncon.low`, `Troncon.high` and `order_eq_or_dual` in `Folder156_3.lean`; finding `156-3-order-from-betweenness`.
- Why it matters: Two different notions of directedness appear in the paper.
- Requested action: state the global directedness and mention the margin's form.

### Minor comment m5

*Hexagon proof.*

- Location: proof of Theorem 5.2.
- Observation: "the cosupport of a part is the set of common neighbours" holds for nonempty parts of {a, b, c, d}; a part containing some v has empty cosupport (v is disjoint from nothing), and ∅′ = 𝓜. Both facts are used.
- Evidence or criterion: Hand computation above; `hexagon_saturated`.
- Why it matters: The proof as written skips the cases with a v.
- Requested action: add the two missing cases.

Hand check of Theorem 5.2: R relates x, y iff both lie under a common element; disjoint pairs need R and no common lower bound, so they are exactly ab, bc, cd (each v has a common lower bound with each of its neighbours and is incompatible with the other two v's). Nonempty Φ ⊆ {a,b,c,d}: {a}″ = {b}′ = {a,c}; {b}″ = {a,c}′ = {b}; {c}″ = {b,d}′ = {c}; {d}″ = {c}′ = {b,d}; any part containing two adjacent vertices, or {a,d}, has cosupport ∅ and support 𝓜; {a,c}′ = {b}, {b,d}′ = {c}. Parts with a v: support 𝓜. ∅″ = 𝓜′ = ∅. Saturated parts: ∅, {b}, {c}, {a,c}, {b,d}, 𝓜. Order: {b} ⊂ {b,d}, {c} ⊂ {a,c}, no other inclusions between the middle four: the hexagon O₆. {b} ∨ {c} = {b,c}″ = 𝓜, hence {b,d} ∧ ({b} ∨ {c}) = {b,d}, while ({b,d} ∧ {b}) ∨ ({b,d} ∧ {c}) = {b} ∨ ∅ = {b}. Correct.

### Minor comment m6

*Boolean case.*

- Location: end of Section 5.
- Observation: "When R is always true, the saturated parts are the regular open sets of (𝓜, ≤)" — correct, but the topology must be named (open sets = down-sets) and the fact is not formalised. One line suffices: Φ′ = 𝓜 ∖ cl(↓Φ), so Φ″ = int cl(↓Φ).
- Evidence or criterion: Standard fact on Alexandrov topologies; the French section lists it as not proved.
- Why it matters: An unproved claim stated as fact.
- Requested action: name the topology and give the one-line argument, or flag it as classical.

### Minor comment m7

*Figure 2 inaccurate.*

- Location: Figure 2.
- Observation: the dashed rays from (1, ½) end at (1.5, 1), outside T; the part of the cone of (1, ½) inside T is the open square with vertices (1, ½), (1.25, ¾), (2, 0), (1.75, −¼). The horizontal arrow is unexplained, the label "(1, ½)" collides with the arrow, and the drawn boundary of the square is not in T (only the two end vertices are).
- Evidence or criterion: Direct computation: the ray of slope 1 from (1, ½) meets the edge x + y = 2 at (1.25, 0.75).
- Why it matters: A figure should not contradict the example.
- Requested action: redraw.

### Minor comment m8

*Figure 5 example.*

- Location: Figure 5 and Section 6.
- Observation: the claimed coarsest connected decomposition {U₁, U₂, Y} is right (a cell meeting Y lies in Y, cells off Y are connected and so lie in U₁ or U₂; the recursion on X′ = Y finds no frontier). The semialgebraic subsets of the closed disc do satisfy (c bis), (d), (e), (f), but the paper gives no reason: (c bis) and (f) are standard (closure, finitely many semialgebraic connected components); (d) follows from dim(cl B ∖ B) < dim B applied to B = A ∩ W for a semialgebraic W open in cl A on which cl A ∖ A would be dense; (e) follows because a closed semialgebraic set nowhere dense in a closed semialgebraic Z has smaller local dimension, so dimension drops along the chain. A sentence and a reference (van den Dries 1998, Ch. 3–4) are needed. The non-connected coarsest decomposition {X ∖ Y, Y} would be worth stating to show the difference.
- Evidence or criterion: van den Dries 1998, Ch. 3–4 (dimension of the frontier; definably connected components).
- Why it matters: The example is offered as an instance of the theorem's hypotheses.
- Requested action: add a justification and the reference.

### Minor comment m9

*Lean section typesetting.*

- Location: Section 7.
- Observation: long identifiers break without hyphens (`order_eq` / `_or_dual`); several names behind the statements (`le_swap`, `intervals_le_iff`, `example_segModel`, `btw_transport`, `le_iff_readLe`, `isOpen_toSpecSet`, `toComp_one`, `toSpecSet_compl`, `hexagon_hyp`, `rare_bd`, `subset_bd`) are not cited.
- Evidence or criterion: Rendered PDF, page 6.
- Why it matters: Readability and traceability of the formal check.
- Requested action: a short table, one row per result.

### Minor comment m10

*Sides: an example.*

- Location: Section 4.
- Observation: no example. A chord of a disc (two sides, Riv has four elements, Ã = A × {±1}) against a slit inside a disc (Riv = {0, 1}; two local sides over each interior point, one over each end) would show what Ã records and that injectivity, not bijectivity, is the content in general.
- Evidence or criterion: Section 4 has no figure or example.
- Why it matters: The construction is abstract; an example shows what is gained.
- Requested action: add such an example with a figure.

## Methods, statistics, and reproducibility

Not applicable (no data or statistics). Reproducibility rests on the Lean files; I checked names and the absence of `sorry`, not a fresh build. The docstring at the top of `Folder121.lean` still says the connected-cells version is "not formalised", although `page16` proves it further down; this does not affect the article but should be corrected in the repository.

## Ethics, transparency, figures, tables, and citations

The AI statement is present. Citations are checked separately (`citations-2026-11-07.md`). Figures: see m7, m8; Figure 4's lattice is drawn correctly but the vertical edges are very short.

## Limitations of this review

Readings of the manuscript pages were taken from the edition's transcriptions and findings, not from the facsimiles. The Lean development was not recompiled. The bijectivity statement for paracompact X is outside the paper and was not examined.

# Confidential comments to editor

Not applicable: author-requested pre-submission reading.

## Reviewer disclosures

Prepared with Claude (Anthropic) at the author's request, as stated in the article's AI statement.


# Author's follow-up (applied to article.tex the same day)

M1: the description now uses R̄ in all three conditions, with the argument. M2: the proof of Theorem 6.1 is rewritten (X′ = union of the frontiers of the members; recursion on X′ with the family {Y ∩ X′} ∪ {Ū ∩ X′}; coarsest-ness argument; connected version). M3: corrected (« bijective » first, « injective, et » added). M4: Theorem 2.1 and Lemma 3.1 are now "after", Theorem 5.2 is a "counterexample to" p. 68; the F3/F′3 sentence and the non-totality sentence are rewritten. M5: Ã, its topology and the map are written out, and the proof is given in full. m1–m6: done. m7: Figure 2 redrawn. m8: the semialgebraic example is justified in the text (with van den Dries, Ch. 2–4), and Figure 6 shows both decompositions. m9: Lean table. m10: new Figure 4 (chord and slit). Citations: see citations-2026-11-07.md.
