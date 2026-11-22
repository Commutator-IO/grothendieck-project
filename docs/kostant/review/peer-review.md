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

## Comments

**M1. The definition of apposition is second-hand.** *Location:* §1 and the sentence after Thm 2.1. *Observation:* the description of tori in apposition by cyclic elements, and the claim that every quadruple is conjugate to the form studied, come from the letter and our note, not from Kostant's paper. *Why it matters:* C1 answers Grothendieck's question only if that description is right. *Action taken:* a sentence in §1 says the description was not checked against the paper. *Open:* read Kostant 1959 and cite the section.

**M2. Two standard facts are argued, not cited.** *Location:* §2. *Observation:* that Borel subgroups through $T'$ are stabilisers of $E'$-stable flags, that general position means $V_k\cap F_{n-k}=0$, and that two Borel subgroups share a maximal torus (used in §5). *Action requested:* give a textbook reference for each (for instance Humphreys or Borel, linear algebraic groups); we did not look up theorem numbers and did not invent them.

**M3. The finite-field computation is not reproducible from the text alone.** *Location:* §5. *Action taken:* the script path is now given. *Remark:* five values of $q$ per type are evidence, not proof; the text says so.

**Minor.** The recount $((n-1)!)^2/\varphi(n)$ gives $1, 2, 18$ for $n=2,3,4$ and agrees with the note for $n=2,3$. The Lean statement fixes the field $\mathbf C$; §3 remarks that the proof works over any field, which the Lean file does not state.

Verified in this pass: both proofs of Thm 2.1 re-derived line by line (indices of $S$, absence of wrap-around since $p+k\le n-1$, Vandermonde exponents); the Lean docstring and the article agree on the statement.
