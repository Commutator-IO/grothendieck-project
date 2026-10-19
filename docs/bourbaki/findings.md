# Bourbaki rédactions: candidate findings (find-novelty pass, 2026-10-18)

Git-ignored working file. Sources: transcripts-bourbaki/*/batch-*.fr.tex (first machine passes, Opus 5.5, unchecked against the facsimile; rights pending with AHP/ACNB, #50). Pages are PDF pages (`\page{}`). No modernised reading exists for these documents, so `ours` records what this pass itself supplied. Historical facts are in outreach/rhm-bourbaki-facts.md and are not repeated. Method: targeted grep of statements, questions, « faux », « suspecte », marginal objections; not every page was read. The web search tool failed in this session, so most `literature` entries are from the pass's own knowledge and say so: those lines name what to open, not what was opened.

Ranked by interest. Lean column: cheap / medium / no.

---

## 1. bourbaki-307-universes-question  (refuted as stated; Lean: no)
- cote: Bourbaki n° 307 (Nov. 1958), « Univers » — pages: PDF 9–11
- kind: mathematical
- claim: The text asks whether there are universes other than the empty one and the U_n, and answers « Cela semble bien probable ». With U_n defined as the smallest universe containing the earlier U_n', and with (A 6) (every object is in some U_n), the answer is no. With the second definition he says comes to the same thing, U_n = T(∪ U_n'), the answer cannot be decided in ZFC with these axioms. The two definitions differ at every inaccessible that is a limit of inaccessibles.
- basis: p. 10 gives both definitions with « ou, ce qui revient au même » and states (A 6). p. 11 asks the question. p. 8–9 show U_0 = T∅ is countable, i.e. hereditarily finite sets.
- ours: The whole argument is the pass's own. (a) (A 6) gives well-foundedness (the AHP skim already records Sabbay's n° 453 showing this), so every non-empty universe is V_κ with κ = ω or strongly inaccessible. (b) Under the first definition the U_n list {ω} ∪ Inacc in increasing order, so every universe is some U_n. (c) Under the second definition V_κ is skipped when κ = sup of the earlier κ_n' and κ is itself inaccessible. Such a κ exists iff there is an inaccessible that is a limit of inaccessibles, which ZFC plus « every cardinal lies below an inaccessible » does not prove (take V_κ for the least such κ). Minor: read literally, the first definition gives U_0 = ∅, not T∅. On p. 11 the fixed point of the F_n(E) contains E as a subset, not as an element, so « le plus petit Univers contenant E comme élément » needs to start from {E}.
- literature (from knowledge, not reopened in this session): SGA 4 Exp. I, Appendice (« Univers », N. Bourbaki): universes are V_κ with κ inaccessible, assuming foundation. N. H. Williams, « On Grothendieck universes », Compositio Math. 21 (1969). OpenAlex lists « Dependent products and 1-inaccessible universes » (TAC, 2021) on 1-inaccessible universes, not opened.
- status: refuted (the text's conjecture fails under definition 1; « revient au même » fails as written)
- settle: Open SGA 4 I App. and Williams 1969 and check that the classification of universes as V_κ is stated there under foundation, so that (a) and (b) can be cited rather than argued. Check on the facsimile that p. 10 really gives both definitions.

## 2. bourbaki-288-exponential-law-nonhausdorff  (unsearched; Lean: medium for the Hausdorff half)
- cote: Bourbaki n° 288 (May 1958), counter-draft of Top. Gén. X — pages: PDF 32–33
- kind: mathematical
- claim: Corollary 2 states that for F locally compact and E Hausdorff, currying is a homeomorphism C_c(E×F, G) ≅ C_c(E, C_c(F, G)). A typed N.B. suspects the statement fails when E is not Hausdorff, and leaves it to Dieudonné as an exercise.
- basis: The statement and proof are typed and legible. The N.B. calls the « ancienne rédaction » proof « canulée » and says the corollary is trivial for uniformisable G. The proof uses E Hausdorff exactly once: to cover a compact M ⊂ E×F by finitely many compact rectangles inside an open set.
- ours: Locating where the Hausdorff hypothesis is used is the pass's own. The pass found no counterexample and no proof for non-Hausdorff E.
- literature (from knowledge, not reopened): the Hausdorff case is classical: J. R. Jackson, Proc. AMS 3 (1952); Engelking, General Topology §3.4; the printed TG X §3 n° 4. mathlib (Topology/CompactOpen.lean, read in this session) has `Homeomorph.curry` only for X and Y both locally compact. It does not have the « X Hausdorff, Y locally compact » version. Escardó–Heckmann, « Topologies on spaces of continuous functions » (Topology Proc. 2001–02) is the place to look for the non-Hausdorff case. Not opened.
- status: unsearched
- settle: (1) Check whether the printed TG X §3 n° 4 keeps « E séparé » and whether a §3 exercise gives a counterexample (« Dieudonné exercicera »). (2) Check Escardó–Heckmann for a non-Hausdorff counterexample or a proof.
- Lean: the Hausdorff half (`[T2Space X] [LocallyCompactSpace Y] [T2Space Y]`, the curry map is a homeomorphism) is self-contained, uses the existing CompactOpen API, and does not seem to be in mathlib. It is a possible upstream lemma.

## 3. bourbaki-243-local-category  (unsearched; Lean: no)
- cote: n° 243 (July 1956), « Esquisse du chap. I … Topologie Élémentaire » — pages: PDF 11–12, 15–16
- kind: mathematical
- claim: n° 243 defines a « catégorie locale » over a space. In current terms this is a stack: a pseudo-functor with coherence, plus gluing of morphisms and of objects with the triple-overlap condition. If no earlier source has this, it anticipates Giraud 1966/1971.
- basis: Typed, but the copy is « faint, blurred ». The facts file (fact 1, caution) asks for a word-by-word check of axiom (ii) before use.
- ours: The identification with the modern definition is the pass's (and the facts file's).
- literature: none searched in this pass. Candidates: Grothendieck's Kansas report (1955), « A general theory of fibre spaces with structure sheaf »; P. Frenkel, Bull. SMF 85 (1957); J. Giraud, Cohomologie non abélienne (1971), whose introduction says where the notion comes from.
- status: unsearched
- settle: Read the Kansas report and Frenkel 1957 for gluing of categories over opens. Read Giraud 1971's introduction for its sources.

## 4. bourbaki-346-invertible-ideal-degenerate  (unsearched; Lean: no)
- cote: n° 346 (Sept. 1960), Alg. Comm. II draft, « Idéaux inversibles » — pages: PDF 21–22
- kind: mathematical
- claim: Remark 6.4 and the comment after Definition 6.5 assert that when the total ring of fractions K is not semi-local, an ideal of A can be an invertible A-module without being an invertible fractional ideal, so the injection of the ideal class group into Pic(A) (Prop. 6.8) need not be onto.
- basis: Typed. It points to an exercise for the example. The example is not in the transcribed pages.
- ours: The pass notes that such an A must be non-Noetherian, since for Noetherian A the ring K is semi-local.
- literature (from knowledge, not reopened): the printed Alg. Comm. II §5 (1961), exercises to n° 6–7, probably contain it; Kleiman, « Misconceptions about K_X » (1979) is the scheme-level analogue.
- status: unsearched (probably matched in the printed AC II)
- settle: Open AC II §5 exercises. If the example is there, mark matched.

## 5. bourbaki-222-effaceable-coherent  (unsearched; Lean: no)
- cote: n° 222 (July 1955), cohomology of sheaves — pages: PDF 15
- kind: mathematical
- claim: The text says that it follows from Serre's theorems that the Čech H^p_m are effaceable on coherent algebraic sheaves on « une variété algébrique ». FAC gives this for affine and projective varieties. For an arbitrary (non-quasi-projective) variety it would need every coherent sheaf to embed in a coherent sheaf without higher cohomology, which FAC does not give.
- basis: Typed, legible. The same paragraph guesses that the Čech groups « fort probablement » coincide with derived-functor cohomology. That guess is true (Tôhoku 1957 with Leray's theorem), and it is a match.
- ours: Spotting the gap is the pass's own.
- literature: Serre, FAC (1955) §§ 44–47, 65–66 (from knowledge).
- status: unsearched
- settle: Decide whether « variété algébrique » in 222 means the projective case. If not, look for a coherent sheaf on a complete non-projective variety that does not embed in a coherent sheaf acyclic in positive degrees.

## 6. bourbaki-457-degree-card-homs  (refuted as written; Lean: medium)
- cote: n° 457 (Oct. 1965), Alg. V reissue project — pages: PDF 32–33
- kind: mathematical
- claim: Corollary 6 states [A:k] = card P(A) for an integral separable algebra A. This fails for infinite degree. The reader's margin says « faux en dim. ∞ | dénombrable | continu », and the text's own N.B. concedes that card has been given the single value ∞. Only the finiteness criterion holds.
- basis: Typed statement, ink marginal, typed N.B.
- ours: A cheap counterexample (the pass's): A = the locally constant k-valued functions on the Cantor set. It has countable degree when k is countable, and P(A) has the cardinality of the continuum.
- literature: printed Algèbre V (1981), §§ on étale algebras, not checked.
- status: refuted (as written; acknowledged in the text and by the reader)
- settle: Nothing left to settle mathematically. Check how the printed Alg. V words it.

## 7. bourbaki-222-corollary-swap  (refuted as written; Lean: no)
- cote: n° 222 — pages: PDF 11–12
- kind: mathematical
- claim: The Corollary on p. 12 swaps the effaceable and coeffaceable conditions of the Theorem on p. 11. This is a slip that no hand corrects. Already recorded as fact 9 in rhm-bourbaki-facts.md and listed here only for completeness.
- status: refuted (slip)
- settle: Check the facsimile for a faint correction.

## 8. bourbaki-288-old-remark-3  (unsearched; Lean: no)
- cote: n° 288 — pages: PDF 35
- kind: mathematical
- claim: The text says remark 3 after Theorem 4 of the old (1949) TG X §3 is « sans doute fausse ». If that remark survived into print, it would be a false printed statement.
- basis: Typed. The remark itself is not quoted in 288.
- ours: null
- literature: none
- status: unsearched
- settle: Read TG X 1st ed. (1949) §3, remarks after Th. 4, and check whether remark 3 reaches the 1961 edition.

## 9. bourbaki-243-twisted-coboundary  (unsearched; Lean: no)
- cote: n° 243 — pages: PDF 37 (§ 14)
- kind: mathematical
- claim: Twisting a structure sheaf by c ∈ H¹(X, H) to define the second coboundary into H² of a nonabelian extension. This is probably a match (Frenkel 1957; Grothendieck, Tôhoku-era notes; Giraud 1971).
- status: unsearched (expected matched)
- settle: Compare with Frenkel 1957 §§ on the exact sequence for central extensions.

---

## Matched (kept so nobody re-checks them)
- bourbaki-999-topological-mittag-leffler. Item 999, PDF 2–3: exactness of lim for metrisable complete groups under the topological Mittag-Leffler condition. Matched: Bourbaki TG II §3 n° 5 Th. 1 (1961 ed.); EGA 0_III 13.2.4. Status: matched (from knowledge).
- bourbaki-327-adic-limits. n° 327, PDF 9–11, Prop. 4 and its corollaries and example: a projective limit of A_j/J_j^{i+1} with J_1/J_1² finitely generated is adic, and the completion for an ideal with I/I² of finite type. Matched: EGA 0_I 7.2.7–7.2.12 (1960). Status: matched (from knowledge).
- bourbaki-457-p-basis-lifting. n° 457, PDF 119–120, Cor. 7.2 and Th. 7.1: formal smoothness of separable extensions and MacLane's criterion. The text itself cites EGA 0_IV 19.6.1 and 21.2.7. Status: matched.
- bourbaki-457-prop12-separable. n° 457, PDF 27, Prop. 12 (stability of « séparable » = geometrically reduced). Matched: EGA IV 4.6. The reader's « Non !! » is terminological. Status: matched (from knowledge).
- bourbaki-307-universe-axiom-inaccessibles. n° 307, PDF 9 and 11: (A 5 bis) together with (A 6) is equivalent to « every cardinal lies below a strongly inaccessible one ». A universe with an infinite element exists iff an inaccessible exists. Matched: SGA 4 I App.; Tarski 1938. Status: matched (from knowledge).
- bourbaki-243-species-classification. n° 243, PDF 9–11: indecomposable species on C(A) correspond to subgroups of Aut A up to conjugacy. This is the classification of transitive G-sets. Status: matched.
- bourbaki-222-cech-equals-derived. n° 222, PDF 15: the guess that Čech equals derived-functor cohomology for coherent sheaves is true (Tôhoku 1957 and Leray). Status: matched.
