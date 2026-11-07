# Referee report (simulated, requested by the author), 2026-11-07

Manuscript: docs/polytopes/article.tex, "Regular polytopes realised over arbitrary rings, after Grothendieck's working notes" (M. Hua), intended for Hexagon.
Status: working draft by an AI assistant, at the author's request, on his own manuscript; local only. Every point below must be checked by the author before use.
Sources compared: docs/lean/sections/{70,72,78,86}.tex; lean/Grothendieck/Folder{70,72,78,86}.lean (no `sorry`, no `axiom`; all 28 declarations named in the Verification section exist).

## Summary of the submission

The paper states and proves results from four Montpellier folders (70, 72, 78, 86): the closure criterion u_alpha^n = 1 iff F_n(alpha) = 0 for regular polygons over any commutative ring; two-line 2p-gons in characteristic p; universal reflection formulae with the order criterion for p = 3, 4, 5 over any nonzero ring and for every p over fields of characteristic 0; the classification of pinned pseudo-reflection realisations and their automorphisms; the icosahedron over Z[alpha], faithful in every characteristic, its quadric and the conic modulo 5; and the five trihedra and the hemi-icosahedron. Everything is formalised in Lean.

## Re-derivations done for this report

- Closure criterion: Cassini identity for Q_m (both directions), the base values s_0, s_1, s_{-1}, the recurrence X_{n+1} = alpha X_n - X_{n-1} + 1, and the Bezout step (b)=>(d). Checked by hand; correct. Counterexample to the page-113 coefficient at n = 4 (gives 1 - U - U^2): correct.
- Lucas sequence identification F_{2m}(alpha) = U_m, F_{2m+1}(alpha) = U_{m+1} + U_m: correct.
- Strip polygons: vertices, determinant 1, order 2p, the improper polygon v, sigma_1 v sigma_1 = v^{-1}, determinants -1 and 1: correct. Figure 1 coordinates (x - y, x + y) checked vertex by vertex.
- Universal formulae: l_i(w_i) = -2, l_{k+1}(w_k) = 1, l_k(w_{k+1}) = 2 + alpha_k, the 2x2 matrix of rho on W (trace alpha, det 1), the three geometric sums for p = 3, 4, 5, and the iterates of s_k up to rho^5 s_k: all recomputed; correct. The "coordinate 1 where s_k has 0" argument for exact order checked for each m < p.
- Theorem 3.2 (cyclotomic): correct; two small gaps filled (constant of proportionality between T and Phi_p; m >= 1 and distinctness of the roots of chi).
- Pinned realisations: n = 1 value rho = mu_0 mu_1 - beta_0 recomputed; U_rho law, u_lambda u_lambda' = u_{lambda*lambda'}, det u_lambda = 1 + rho lambda: correct. Figure 3 values (d at -1, 0.6, 1.56) correct.
- Icosahedron: q vanishes at the 12 vertices, invariance under sigma_0, sigma_1, sigma_2, the 9x9 minor 13 alpha + 21 and its inverse 13 alpha - 8, the 4x4 polar determinant -alpha - 3, the norm 5 and (-alpha-3)^2 = 5(alpha + 2): checked numerically at both roots of x^2 + x - 1. Units +-(1+alpha), +-(2+alpha), +-(3+2alpha) have norm +-1: correct. Third coordinates of the nine other vertices: correct.
- Modulo 5: 24 nonzero isotropic vectors = the 12 s-bar and their doubles; value counts 1 or 4 on 60 vectors and 2 or 3 on 40: recomputed by enumeration of F_5^3; correct.
- Trihedra: the thick trihedron of the new Figure 5 checked against `colTab` (label 0) and `nbrs` in Folder86.lean.

## Major comments

M1. Section 4, proof sketch of Theorem 4.1 (formerly "Under (B), <s_i, a'_i> = nu_i/nu_{i-1}").
Observation: under (B), <s_{i-1}, a'_i> = 0, so <s_i, a'_i> = <s_{i-1}, a'_{i-1}><a_{i-1}, a'_i>, which gives <s_i, a'_i> = nu_i by induction (as in the French section 72). The quotient was wrong. Why it matters: the triangularity argument rests on this value. Action: FIXED in the text.

M2. Theorem 5.2(3) and the abstract: "smooth iff 5 is invertible in R".
Observation: Lean proves (isUnit_det_qMat4_iff, qHom_smooth) that the discriminant is a unit iff 5 is, and then that the partial derivatives have no common nonzero zero; and, over a field, singular iff characteristic 5 (qHom_singular_iff). The converse over an arbitrary ring is false for the definition used: over R = Z[alpha], 5 is not a unit but the polar matrix is injective (domain, nonzero determinant). It is true in the scheme sense, which is not proved here. Action: FIXED; statement now "the discriminant is invertible iff 5 is, and then 0 is the only common zero of the partial derivatives"; abstract now "smooth whenever 5 is invertible and, over a field, singular only in characteristic 5".

M3. Corollary 4.5 (irreducibility on C), proof.
Observation: the proof showed only why rho != 0 is needed; it did not show that some beta_i = 0 gives a proper nonzero stable subspace of C. Action: FIXED (Z*_i contains h_{i+1} and not h_0, which lies in C; as in the French section and `irreducible_on_C_iff`).

M4. Two-line 2p-gons versus Korchmaros-Szonyi.
Observation: the text cited "[Th. 2.1-2.3]" for "every affinely regular polygon lies on an irreducible conic"; that statement is Lemma 2.2 of the survey, and it is about non-degenerate polygons (no three collinear vertices). For p >= 3 the 2p-gons have p collinear vertices on each line, so they are degenerate in that sense; they do not contradict the lemma. Action: FIXED; the paragraph now says this explicitly and cites Lemma 2.2 and Th. 2.1, 2.3 separately.

## Minor comments

m1. (3.4) of Korchmaros-Szonyi says "nontrivial solution iff c = +-2 or x^2 - cx + 1 divides x^n - 1"; the exception c = +-2 was dropped. FIXED. Note for the author: the survey writes the system as v_0 + c v_1 + v_2 = 0 with the polynomial x^2 - cx + 1, which looks sign-inconsistent (an eigenvector computation gives x^2 + cx + 1). The article only reports their statement; worth not leaning on it.
m2. Theorem 3.2(2) proof: "Hence T = Phi_p" skipped that the quotient is a constant equal to 1. FIXED.
m3. Theorem 3.2(3) proof: simple roots of t^m - 1 need m >= 1; the condition zeta^2 != 1 comes from the distinctness of 1, zeta, zeta^{-1}. FIXED (parenthetical).
m4. Novelty statement on the F_5 conic: "we have not found the icosahedron drawn as a conic in P^2(F_5) in print" is a priority-type claim. Softened to "we do not know a printed source that reads the reduction modulo 5 of the icosahedron as this conic and its exterior and interior points". UNRESOLVED: a literature search (finite geometry of PG(2,5), the hemi-icosahedron and the conic, Monson-Schulte part III) has not been done.
m5. Missing related work on affinely regular polygons and Chebyshev polynomials: Fisher-Jamison, Geom. Dedicata 69 (1998), is cited by Korchmaros-Szonyi for exactly that link. ADDED one sentence and the reference. The novelty of Theorem 2.1 over rings with zero divisors is still stated only as a comparison, not as priority.
m6. Esquisse context added (supported by the text of section 4): the 2n + 1 count agrees with the footnote on pseudo-polyhedra; the footnote on the circumscribed hyperquadric; in characteristic 2 the conic at infinity stays smooth (half-discriminant 1, proved) and iota is a translation (proved), which matches the Esquisse's "centre sent off to infinity". Ji's unresolved "cosines versus doubles" remark is now mentioned next to the explanation of the doubles of the cosines.
m7. Character "o double acute" in "Szonyi" was not rendered by the T1/lmodern font (missing-glyph warning). FIXED with \H{o}.
m8. "In positive characteristic the criterion for arbitrary p is not proved here." Suggestion for the author (not added, since it is not formalised): Theorem 3.2(1) gives rho^m = 1 iff chi | t^m - 1 over any ring, and the homogenised matrix of u_alpha has the cyclic vector (0,0,1) (determinant 1 against its two images), so u_alpha^m = id iff chi | t^m - 1 too. With Theorem 2.1 this would give rho^m = 1 iff F_m(alpha_k) = 0 over every commutative ring, which is page 67's statement literally, with F of folder 78. Worth formalising before stating.

## Points checked and found correct as written

Attributions "Grothendieck, folder N, p. X" (Theorems 2.1, 4.4, 5.2, 6.1) match the French sections; the others are "after". Page references agree with the French sections. Quotations from the manuscripts are a few words each ("c'est en fait faux en car. 2 !", "deux icos.", "merveille", "F_n(alpha) = 1").

## Limits of this review

The Lean files were not rebuilt (no `lake build`); the check was textual (declarations exist, no sorry or axiom). The facsimiles were not consulted. Monson-Schulte 2004 was checked only through its zbMATH review (publisher page 403).
