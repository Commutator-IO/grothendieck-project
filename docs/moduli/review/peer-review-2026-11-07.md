# Referee report (simulated), working draft: "Small moduli problems over Spec Z"

Requested by the author on his own manuscript (docs/moduli/article.tex, version of 7 November 2026, intended for Hexagon). Local working draft; the accountable human reviewer is the author. No editorial outcome is stated. The intake was validated locally (author_requested_reader, local only). The Hexagon review and AI policy was not re-read for this draft.

Sources compared: the French sections docs/lean/sections/84.tex, 83.tex, 85.tex, 64.tex, 93.tex; the Lean files lean/Grothendieck/Folder84.lean, Folder83.lean, Folder85.lean, Folder64.lean, Folder93.lean (theorem names and hypotheses read from the source; Lean was not re-run). The polynomial identities of Sections 2, 3 and 5 were re-expanded with sympy. The manuscripts themselves were not re-read.

# Comments to the author

## Summary

The paper gathers five small moduli problems from Grothendieck's folders 84, 83, 85, 64 and 93, written over Spec Z without inverting 2, 3 or 5: quadratic algebras, their classification by triples (L, delta, T0) and their product; the line of Hamilton-Cayley structures on H (x) H' and its Azumaya criterion Q(t) a unit; the invariant A(g) of an element of PGL2 and the orders 3 to 6; the string group G2 and its invariants; the octahedral configuration in characteristic 5; the Schwarzian written with divided derivatives and its rigidity at Frobenius level p or p^2. Every proved statement is said to be formalised in Lean.

## Strengths

- The statements are elementary, checkable and stated over arbitrary rings; the characteristic 2 and 3 phenomena are the point and are shown by explicit examples (F2 for triples, Z[X] for the invariants, F5 for the octahedron and for the determinant normalisation).
- The separation between what is proved and what is only Grothendieck's statement is mostly kept (Statement 4.3, the G2 moduli, folder 64's relative statements).
- All the identities I re-expanded are correct: the page-64 identity, b^2 - 4c = delta1 delta2, the identity Q(b'U + bV - 2UV) = (2V - b')^2 (U^2 - bU + c) + delta (V^2 - b'V + c'), disc Q = delta delta', Q(bb' - t) = Q(t), the cocycle identity for N, the order polynomials P3 to P6, the fixer computation 5a - 4 = 1.

## Major comments

### M1. Sign conventions between folders 84 and 83 (Section 3, paragraph after Theorem 3.1)

- Location: "up to the sign conventions, u * v is the generator U of the product of H and H'".
- Observation: folder 84 writes U^2 + bU + c = 0 (trace -b), folder 83 writes u^2 - bu + c = 0 (trace b). With H = A(-b, c) and H' = A(-b', c') in the notation of Section 2, the product generator is 2UV - bV - b'U = -(u * v), and the product equation P(T) = T^2 + bb'T + (b^2c' + b'^2c - 4cc') satisfies Q(t) = P(-t). So u * v is minus the generator, not the generator; R[t]/(Q) and A(bb', b^2c' + b'^2c - 4cc') are identified by t -> -U.
- Why it matters: the link between Sections 2 and 3 is the main conceptual claim; an unstated sign leaves the reader to guess.
- Requested action: state the dictionary exactly (done in the revision).

### M2. Statement 3.1(2) and 3.1(4): attribution and corrected pages

- Observation: the French section records that page 138 writes the constant term of Q as b^2b' + b'^2b - 4cc' and that page 143 gives det(u * v) = b^2c + b'^2c' - 4cc'; the edition corrects both to b^2c' + b'^2c - 4cc'. The article does not mention these corrections. The Azumaya criterion is the theorem of page 98; its validity in characteristic 2 comes from the edition's proof (through the determinant of the trace form), not from the page.
- Requested action: mention both corrections; attribute the criterion to p. 98 and say that the proof given covers characteristic 2.

### M3. Theorem 2.1: hypotheses misplaced

- Observation: (a) morphisms of covers and of triples are isomorphisms phi: L -> L' in the source and in Lean (isCoverHom over a linear equivalence); the article writes phi: L -> L'. (b) Essential surjectivity (every triple with T0^2 = delta mod 4 comes from a cover) holds over every ring (triplet_ess_surj), but the article puts it under "2 a non-zero-divisor". (c) The reconstruction formulas of pages 49 to 52 quoted in the proof sketch are proved in the free case A = A(b, c); for non-trivial L only the legitimacy of the divisions is proved. (d) The F2 example is the edition's.
- Requested action: correct (a) to (d).

### M4. Theorem 2.4: what is the page's and what is the edition's

- Observation: the Z[X] example and the converse "after every base change" proof are the edition's; the page states the corollary with the base-change hypothesis. In Theorem 2.5 the statement "an identification exists iff gamma chi = 2 exists" holds among maps inducing the identity on L and on M (push_pull_unit_iff), a restriction the article omits; the Z, chi = 4 example is the edition's.
- Requested action: add the restriction, mark the edition's additions.

### M5. Theorem 4.4 (fixer): the proof assumes what it must prove

- Observation: the statement is about any a with z -> az + (a - 1) mapping {0, 1, i, -i} into itself; the proof begins "the map is an automorphism, so a != 0". The case a = 0 must be excluded directly: then every point goes to -1, which is not in the set when 2 != 0. Also the claim that Theorem 4.4 shows "5 invertible is needed" for the relative correspondence of pages 44 to 52 overstates: the counterexample shows that 5 must be invertible where the pages identify Aut(X, Delta) with the octahedral rotation group.
- Requested action: add the a = 0 case and the distinctness of the four points; narrow the necessity claim.

### M6. Section 5: the remark on the factor 12 is wrong at p = 2

- Location: last paragraph of Section 5, "G0 sees the third divided derivative, which vanishes on X^p only when p > 3".
- Observation: D^(3)(X^2) = binom(2,3) = 0. At p = 2 the obstruction is D^(2)(X^2) = 1, at p = 3 it is D^(3)(X^3) = 1; in general D^(k)(X^p) = binom(p, k) X^(p-k) is non-zero for k = p only. The examples t -> t + t^2 (G0 = 1 in characteristic 2) and t -> t + t^3 (G0 = -1 in characteristic 3), proved in Lean (char_two, char_three), make this concrete.
- Requested action: replace the sentence.

### M7. Section 5: scope of the alpha != 0 case

- Observation: the reduction from alpha to 0 is proved over a local ring (rigidity_alpha_local and its three corollaries) and also over any ring with Pic(A) = 0 (rigidity_alpha_pic and corollaries); the sketch omits the descent of the osculating homography from B = A[T]/(T^q - alpha) to A, which is the substantive step.
- Requested action: mention the descent and the Pic(A) = 0 version.

## Minor comments

### m1. Theorem 4.1: "order nu at every point" is used but not defined

- Requested action: define it (g^nu scalar and g^m nowhere scalar for every proper divisor m of nu), as in the source and in Lean (order_four_iff, order_six_iff).

### m2. Example 4.2: the icosahedral subgroup

- Observation: the homomorphism A5 -> PGL2(Z[zeta5]) and its injectivity on every fibre follow from the simplicity of A5 and the (2, 3, 5) presentation, but this step is not formalised.
- Requested action: say so.

### m3. Notation G2

- Requested action: say that G2 is the page's notation for the group with relations tau_i^2, (tau0 tau2)^2 (the Coxeter group [infinity, infinity]), not the exceptional group.

### m4. Section 2, "L (the quotient A/O, up to sign)"

- Requested action: replace by a precise phrase; in the free case L is generated by the class of U.

### m5. Abstract and introduction

- Observation: "In the early 1980s" conflicts with folders 84 and 83 (to about 1986, April 1986). The folder 85 inventory title is spelled "1-polygônes". The abstract is long.
- Requested action: "in the 1980s"; tighten the abstract.

### m6. Verification section

- Observation: no Lean theorem names are given, so a reader cannot locate the formal statements.
- Requested action: list the names per section (done in the revision; every name was checked against the source files).

### m7. Figures

- Observation: the octahedral configuration, the line of twists with its degenerate locus, and the reading of orders on A(g) would each be clearer with a diagram.

## Citations

Checked separately (docs/moduli/review/citations-2026-11-07.md).

## Limitations of this review

The handwritten pages were not re-read; agreement with the pages is checked against the French sections only. Lean was not re-run; the theorem names and hypotheses were read in the source files. No Hexagon policy text was consulted for this draft.

# Confidential comments to editor

None (author-requested review).
