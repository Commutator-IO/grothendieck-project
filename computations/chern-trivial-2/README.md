# Folder 2, p. 13: a non-zero class with total Chern class 1

**Statement** (docs/lean/sections/2.tex, `\nonverifie` box; transcripts/2/2.modern.tex around
« Conséquence » and the *N.B.*): X an elliptic curve, a ≠ 0 with a + a = 0, x = (a) − (0) ∈ K(X).
Then y = i_!(x) ∈ K(X × P³) is non-zero and c(y) = 1. More generally, if Y ⊂ X is a divisor whose
class x′ is non-zero but killed by (r−1)!, then i_!(O_Y) is non-zero with c = 1,
**« ce qui n'est possible que pour r ≥ 3 »**. The modernised reading says: « Comme (r−1)! = 1 pour
r ≤ 2, l'hypothèse force alors x′ = 0 : le phénomène demande r ≥ 3. »

**Already in Lean.** The Chern-class identities (`chernPoint`, `chernImmersion`, `chernRatio`,
`chernCurve`, `chernEllipticNB`, Folder2.lean) are proved. The open parts are non-nullity and the
restriction r ≥ 3.

**What the script does** (`python3 check.py 8`, about 50 s, exact sympy arithmetic). It works in
the splitting-principle model of the reading: A(X × Pʳ) = A(X)[η]/(η^{r+1}), p, q the classes of
the points 0, a with p² = q² = 0, and i_!x = Σᵢ (−1)ⁱ C(r,i)([O(−0)L⁻ⁱ] − [O(−a)L⁻ⁱ]). For
r = 1..8 it computes c(i_!x) in two independent ways:
- route A: the product of the factors (1 − p − iη)^{±}/(1 − q − iη)^{±};
- route B: ch(i_!x) = (e^{−p} − e^{−q})(1 − e^{−η})ʳ, then log c = Σₖ (−1)^{k−1}(k−1)! chₖ.

**Result** (results.txt). Both routes give exactly c(i_!x) = 1 + (−1)^{r−1} r! (p − q) ηʳ. So
c(i_!x) = 1 if and only if r!(p − q) = 0 in A¹(X), not (r−1)!(p − q) = 0. Here p − q has the
order N of a in Pic⁰(X). For the page's own N = 2, this already holds at **r = 2**.

**Counterexample to « ce qui n'est possible que pour r ≥ 3 ».** X the elliptic curve of the N.B.,
a of order 2, r = 2. Then c(i_!x) = 1 − 2(p − q)η² = 1 in A(X × P²). Yet i_!x = x·ξ² ≠ 0 in
K(X × P²) = ⊕ₖ K(X)ξᵏ (projective bundle formula), because x ≠ 0: det x = O(a − 0) is a
non-trivial line bundle. The same holds for the "more general" form. The exact coefficient is
(−1)^{r−1}(r−1)!(1 − (1 − x′)^{−r}), which for x′² = 0 is −(−1)^{r−1} r! x′. So for r = 2 it
suffices that 2x′ = 0 (and x′² = 0). The hypothesis « (r−1)! x′ = 0 » is sufficient but not
necessary, and only that hypothesis forces r ≥ 3. For r = 1, c = 1 + (p − q)η ≠ 1. The page
itself chooses r = 3 (« cas le plus simple »). The claim that r ≥ 3 is necessary comes from the
reading (edition), not visibly from the page.

**Limits.** The computation runs in the splitting model, for r ≤ 8 and torsion orders N ≤ 8.
Non-nullity of x·ξʳ uses the projective bundle formula and det x ≠ 0, which are geometric inputs
the script does not compute. Side remark, not computed: on a projective X an effective divisor
cannot have a torsion class (its degree is positive), so the "more general" form needs a virtual
class (as in the N.B.) or a non-proper X.
