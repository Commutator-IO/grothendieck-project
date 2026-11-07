# Referee report (simulated), docs/algebra/article.tex

Working draft, 7 November 2026. Requested by the author on his own manuscript before submission to Hexagon; local processing only. Prepared with the `peer-review` skill (intake validated as READY_FOR_LOCAL_REVIEW, capacity "author-requested reader"). Every statement was checked against the French Lean-appendix sections `docs/lean/sections/{2,22,46,153,77,158}.tex` and the Lean files `lean/Grothendieck/Folder{2,22,46,153,77,158}.lean`. This is not a venue review and makes no recommendation on publication.

## Summary of the submission

Six independent short notes, each a statement from a Montpellier folder, with a proof (the edition's or the page's) and a pointer to a Lean formalisation: a Chern ring that differs from the graded gamma-ring (folder 2); non-formal-smoothness of power series over a field with infinite-dimensional differentials, and a kernel of differentials in characteristic p (folder 22); lifting non-abelian 1-cocycles through reduction modulo m (folder 46); co-operations on relative integer-valued polynomials (folder 153); the even-rank universal discriminant modulo 4 (folder 77); finite cofiltered monoids and categories (folder 158).

## Strengths

- The statements are precise. Each matches the Lean statement I checked, apart from the points below.
- The attribution convention ("Grothendieck, folder N, p. X" against "after ...") is stated in the introduction, and most sections follow it.
- The counterexamples (necessity of p not dividing |Gamma|, the other sign in folder 77, the disconnected category in folder 158) make the hypotheses easy to see.

## Major comments

**M1. Folder 22, proof sketch of the power-series theorem (Section 2).**
- *Observation.* The sketch writes D(f) = sum_{j<N} t^j (x) dc_j + t^N D(g_N). This leaves out the terms c_j D(t^j) = j c_j t^{j-1} D(t) and the term N t^{N-1} g_N D(t). The sentence that "the t^j-coefficients of D(f) must contain all the dc_j" is not an argument either: A (x)_K Omega is a free A-module, and nothing has been said about how coefficients in t are read off in it.
- *Criterion.* The French section and Lean (`no_derivation`, `no_derivation_of_field`, `no_derivation_mv`) use another argument. Fix a basis (b_i) of Omega_{K/k} containing the dc_n. Compose D with an A-linear coordinate p_i. Since D(f) and D(t) have only finitely many non-zero coordinates, there is an n with p_{i_n}(D f) = p_{i_n}(D t) = 0. Then E = p_{i_n} o D is a derivation A -> A with E(t) = 0, so E(t^m g) = t^m E(g), and E(c_m) = delta_{mn}. The coefficient of t^n in E(f) is then 1, a contradiction. The n-variable case reduces to one variable through t -> t_1 and the projection t_i -> 0 for i >= 2. Formal smoothness gives D through the Jacobi–Zariski sequence (H_1(L_{A/K}) = 0 and Omega_{A/K} projective, so A (x) Omega_{K/k} -> Omega_{A/k} has a retraction).
- *Why it matters.* As written, the sketch is not a proof.
- *Requested action.* Replace it with the coordinate argument, and say that it is the edition's, since page 24 stops at the construction of the series. Note that D must be k-linear.

**M2. Folder 158, Proposition 1: the "sketch following the page" is wrong (Section 6).**
- *Observation.* The sketch says M acts by right multiplication, takes a minimal image E_0 = uE, and concludes that "E_0 is a single point p". All three points are wrong. In the proof (page and Lean `proposition1`) M acts by left multiplication x -> ux. The set is E_0 = pM, where p lies in every principal right ideal uM (Lean `etape1`). The map to the permutation group of E_0 is trivial, so every u fixes E_0 pointwise. Then up = p because p = p.1 lies in E_0. E_0 need not be a point. In the monoid {1, a, b} with xa = a and xb = b (Lean `contre_pseudoCofiltrant`, `contre_noyau_non_ponctuel`), aM = {a, b}.
- *Criterion.* French section 158, proof of Proposition 1, and its remark on the Rees kernel.
- *Why it matters.* The sketch credits the page with a false step, and the "single point" claim contradicts a counterexample that the edition itself proves.
- *Requested action.* Give the proof in full (it is short). Say what comes from the page: pseudo-cofiltrance, M acting on a set, and the finiteness step "u(E_0) = E_0". Say what is the edition's: E_0 = pM, the lemma that gives p, and the observation that "E_0 finite" holds because E_0 lies inside M (the page struck out "finite" before E).

**M3. Folder 77, proof of the mod-4 theorem (Section 5).**
- *Observation.* I re-derived the permutation count, and it is correct. Group permutations by reversing their cycles of length >= 3. The orbit of sigma, with f fixed points and c long cycles, has 2^c elements with the same sign and product, and that product carries 2^f. The orbit therefore contributes 2^{f+c} times a monomial, which vanishes modulo 4 unless f + c <= 1. On an even set f = 1, c = 0 is impossible. Two cases remain: perfect matchings (sign (-1)^n, product a square) and orbits {sigma, sigma^{-1}} with f = 0, c = 1, whose long cycle has even length >= 4. On the B^2 side, a union M u M' with c >= 1 alternating cycles arises from 2^c ordered pairs, that is 2^{c-1} unordered pairs, giving 2^c times a monomial. This vanishes modulo 4 for c >= 2. For c = 1, an even cycle of length >= 4 together with double edges splits in exactly one way into an unordered pair of matchings, and this is the bijection with the orbits of type (b). The manuscript states each step, but tersely. Two things should be fixed: "every other configuration carries a factor 4" should give the reason (2^{f+c}), and "signs being irrelevant modulo 4" should say that 2 and -2 agree modulo 4.
- *Criterion.* This proof follows the method of pages 65–71 (graph expansion, then pairs of matchings). Lean (`four_dvd_disc_sub_hafnian_sq`, `disc_even_rank`) proves the theorem another way. It uses the antisymmetric matrix K = U - U^t. A first-order expansion gives det K = (1 - 2n) det P mod 4. Then det K = r^2 with r in Z[Y], since Z[Y] is integrally closed (r is the Pfaffian up to sign). Finally r = B mod 2.
- *Requested action.* Keep the counting proof with the two clarifications. State that it is the edition's write-up of the pages' comparison, and that the formal proof follows the Pfaffian route; give that route in a remark.

**M4. Folder 158, Theorem on finite categories: no proof, and "cofiltered" is not defined for categories.**
- *Requested action.* Define a cofiltered category. Give a proof sketch following French section 158: the gluing cocycle for common ancestors, an object e mapping to every object, a minimal idempotent of End(e), and the local system L(z) = {f : e -> z | fp = f}. Mark the converse for monoids as the edition's statement (`simplyConnected_of_cofiltrant`).

## Minor comments

- **m1. Folder 2, Theorem.** The page states only n >= 3. The case n <= 2 and the proof that zeta^n != 0 are the edition's. The label "Grothendieck, p. 21" should say so. The presentation of CK by zeta and the single relation c(xi^n) = 1 is the page's reduction and is not formalised. The torsion-freeness of GK needs one line of proof.
- **m2. Folder 22, Proposition.** The kernel element should be written 1 (x) dy - y' (x) dx, since y' lies in K and not in k. The reduction "page 22 presumes" is accurate.
- **m3. Folder 46, inertia theorem.** The element of trace one is for Gamma (sum over all sigma in Gamma), and it exists because |Gamma_i| is invertible in k. "For Gamma_i" is wrong. The closing paragraph says the semi-local statement "is not proved here". In fact the edition proves (in Lean) the semi-local base under a trace-one hypothesis (`isCohomologous_of_semilocal`, `isCohomologous_of_restrict_inertia_semilocal`). What remains open is the wild case and the finite residue field. The phrase "the page argues differently" is right: the page works layer by layer along m^n A/m^{n+1} A (abelian averaging) and uses Artin–Rees in the finite case. That should be said.
- **m4. Folder 46, hypotheses.** I checked them against Lean `ker_trivial_of_pow_smul_eq_bot`, `ker_trivial`, `injective`, `isCohomologous_of_map`, `ker_trivial_restrict`, `injective_sylow_comm` and `isCohomologous_of_restrict_inertia`. Injectivity under "m^N A = 0" follows from `isCohomologous_of_map` with the nilpotence lemma. The theorem named `injective` assumes A finite. For non-commutative A, the Sylow injectivity is proved only under a twisted lifting hypothesis; it is worth one sentence.
- **m5. Folder 153.** Omega is defined for an inclusion k_0 ⊆ K_0, but the theorem allows any k_0-algebra. Define Omega with the structure map. Elliott's paper is relevant beyond Int(Z): its criterion, that Int(D) (x) Int(D) -> Int(D^2) be an isomorphism, is the analogue of part (2).
- **m6. Folder 77.** "the hafnian description ... is what the pages add" is a priority claim without support; remove it. The Knus citation should be worded more loosely.
- **m7. Verification section.** List the Lean theorem names.
- **m8. Abstract (6).** "for monoids, the pages' Proposition 1" should say that it is the finite case.

## Figures

There is a single figure (folder 77). Diagrams for the averaging argument (folder 46), the graph types in the determinant expansion (folder 77) and the square uu' = vv' (folder 158) would help.

## Limits of this report

Simulated, pre-submission. The facsimile pages were not consulted; statements about what a page says rely on the French sections. The Lean files were read but not re-compiled.
