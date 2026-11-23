# Peer review (working draft): docs/kostant/article.tex, 22 November 2026

Local self-review of the author's own draft, done at the author's request. Intake validated with the skill's `validate_review_intake.py` (READY_FOR_LOCAL_REVIEW, local only, warnings: no confidential-editor channel, competence limits to disclose). Working draft for Michel Hua, who remains accountable for the text. The Kassis et al. citation proposed by the skill was not added.

Limits: no specialist in algebraic groups read it; the Lean file was not rebuilt locally (the project's CI is the judge).

## Map of the claims

| ID | Claim | Evidence in the text |
|---|---|---|
| C1 | In $\mathrm{PGL}_n$, every $E'$-stable subspace of dimension $k$ meets $F_{n-k}$ trivially (Thm 2.1) | weighted-shift proof (§3), checked again by hand; Vandermonde proof (§4); Lean |
| C2 | Hence every Borel through $T'$ is in general position with $B$ | translation argued in §2, not formalised |
| C3 | $n=2$, $c_1=0$: the hypothesis is necessary | one line, checked |
| C4 | $B_2$, $G_2$ (and $A_2$): only opposite pairs over $\mathbf F_q$ | script `computations/kostant`, five $q$ per type |
| C5 | number of classes in type $A$: $((n-1)!)^2/\varphi(n)$ | arithmetic from the formula of the letter |
| C6 | Types $B_n$, $C_n$: every $E'$-stable subspace of dimension $k$ meets $F_{N-k}$ trivially (Thm 6.1 (1)) | proof in §6 (type $C$ reduces to type $A$; type $B$ with the map $G$); Lean, `Folder123KostantClassical.lean` |
| C7 | Type $D_n$, $n \ge 3$: isotropic $E'$-stable subspaces of dimension $k < n$ are transverse (Thm 6.1 (2)) | proof in §6; Lean, same file |
| C8 | Type $D$: the middle step holds for one of the two maximal isotropic subspaces only | numerical computation for $n = 3, 4, 5$ reported in the Lean file's docstring, not redone for the article |

## Comments

**M1. The definition of apposition is second-hand.** *Location:* §1 and the sentence after Thm 2.1. *Observation:* the description of tori in apposition by cyclic elements, and the claim that every quadruple is conjugate to the form studied, come from the letter and our note, not from Kostant's paper. *Why it matters:* C1 answers Grothendieck's question only if that description is right. *Action taken:* a sentence in §1 says the description was not checked against the paper. *Open:* read Kostant 1959 and cite the section.

**M2. Two standard facts are argued, not cited.** *Location:* §2. *Observation:* that Borel subgroups through $T'$ are stabilisers of $E'$-stable flags, that general position means $V_k\cap F_{n-k}=0$, and that two Borel subgroups share a maximal torus (used in §5). *Action requested:* give a textbook reference for each (for instance Humphreys or Borel, linear algebraic groups); we did not look up theorem numbers and did not invent them.

**M3. The finite-field computation is not reproducible from the text alone.** *Location:* §5. *Action taken:* the script path is now given. *Remark:* five values of $q$ per type are evidence, not proof; the text says so.

**Minor.** The recount $((n-1)!)^2/\varphi(n)$ gives $1, 2, 18$ for $n=2,3,4$ and agrees with the note for $n=2,3$. The Lean statement fixes the field $\mathbf C$; §3 remarks that the proof works over any field, which the Lean file does not state.

Verified in this pass: both proofs of Thm 2.1 re-derived line by line (indices of $S$, absence of wrap-around since $p+k\le n-1$, Vandermonde exponents); the Lean docstring and the article agree on the statement.

## Revision of 22 November 2026: the classical types

Section 6 added after GrothendieckArchivesProofs #61 (`Grothendieck/Folder123KostantClassical.lean`), with the title and the abstract widened to types $B$ and $C$. What was checked: the article's statement of Thm 6.1 against the Lean statements `KostantOppositeTypeB`, `KostantOppositeTypeC`, `KostantOppositeTypeD` and the module docstring (what is proved, what is not formalised); the proof sketch follows the docstring's « How ». Not checked: the Lean file was not rebuilt locally (`main` of the proofs repository is green at `9918f42`), and the numerical computation behind C8 was not redone. The translation from flags to Borel subgroups in types $B$ and $C$ (the longest Weyl element acts by $-1$, so general position is the opposition of the completed flags) is argued in §6, not formalised, and falls under M2: a textbook reference is still wanted. In type $D$ the article does not state a conclusion on the relative position of the Borel subgroups.


## Revision of 23 November 2026: every type

New Section 2: Theorem 2.1 answers Grothendieck's first question in every type (every Borel subgroup through T′ is opposite to B and to B⁻), by two lemmas: t′ contains an element of f + b with nonzero components on every −α_i (Killing duality for the Coxeter grading, then a nilpotency argument), and a Borel subalgebra containing such an element is opposite to b (the Bruhat argument of Bălibanu, Lemma 4.5). Both proofs re-derived line by line in this pass, including the case h = 2. The A, B, C, D sections are kept as the explicit flag form, with their Lean proofs; type A's operator S is the element of Lemma 2.2.

What changed on the earlier comments: M1 is answered in part — the definition of apposition (relative to the principal element P, p. 1018), Thm 6.7, Cor. 8.6 and Thm 8.6 are now cited, but from secondary sources (Brillon–Schechtman, Guest–Ho, Kostant 2010), the 1959 paper still not read; the text says so. The novelty is stated as « a short consequence of published results », not claimed. New check: `computations/kostant/kostant_bn.py`, B_2 to B_7 modulo primes, run in this pass. Still open: reading Kostant 1959 to confirm the numbers; M2 (textbook references for the flag translation).

Page 1018 of Kostant 1959 read from a screenshot (23 November 2026): the definition of apposition (conditions (1) g^P = h_1, (2) h'_1 stable under P with a primitive s-th root of unity among the eigenvalues of P on h'_1), « By Theorem 6.7 it is clear that h' is in apposition to h with respect to P_0 », and Theorem 7.3 (two triples in apposition are conjugate). Correction: the converse is Theorem 7.3, not Theorem 8.6 as the secondary sources suggested. Theorem 6.7 and Corollary 8.6 are still cited from secondary sources.

Pages 1013–1015 read from screenshots (23 November 2026): Theorem 6.7 states, for nonzero c_1..c_l and c_0 = 1, that z_0 = e_0 + e_{−ψ} and z̃_0 = Σ (q_i/c_i) e_{−α_i} + e_ψ are regular, commute, and have the same centraliser h′, orthogonal to h, stable under P_0 with eigenvalues ω^{k_i} and y_l = z̃_0. The article now cites it directly for the element of Lemma 2.2. The « only if » direction (all c_i nonzero) is still cited from Kostant 2010, Thm 1.2, and Corollary 8.6 from secondary sources.
