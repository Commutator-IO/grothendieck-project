# Folder 62, pp. 41–53: three descriptions of the triples (X, X′, s)

**Statement** (docs/lean/sections/62.tex, appendix row « D'après les pages 41 à 53, trois
descriptions des triplets »; transcripts/62/62.modern.tex, section IV). Over a base where 6
is invertible, triples (X, X′, s) (a genus-0 curve, an étale trisection, a section disjoint
from it) are described equivalently by
(A) an S₃-torsor T with t ∈ Γ(T, O), t and t − 1 invertible, g·t = g(t) (p. 49);
(B) an invertible sheaf M with a zero-sum étale trisection of V(M) (p. 53), locally a cubic
    x³ + bx + c with invertible discriminant;
(C) the invariant j = q(s) of formula (11), which determines the triple where j(j − 1) is
    invertible (pp. 41–43).
Lean (lean/Grothendieck/Folder62.lean) has the invariant fibre by fibre over a field; the
descriptions over a base are not formalised.

**How.** Over S = Spec F_p, p = 5, 7, …, 31, the groupoid of triples is computed four ways,
recording each isomorphism class with its invariant j and the order of its automorphism
group:
- (D) from the definition: s is a rational point, so X ≅ P¹; put s = ∞; X′ is a squarefree
  cubic; classes are orbits of the affine group x ↦ λx + μ;
- (A) orbits of S₃ (by conjugation on σ and anharmonic action on t₀) on pairs (σ, t₀),
  σ ∈ S₃ the Frobenius cocycle of T, t₀ ∈ P¹(F̄_p) ∖ {0, 1, ∞} with Frob(t₀) = σ(t₀)
  (t₀ in F_p, F_{p²} or F_{p³}); j = formula (11) at t₀;
- (B) pairs (b, c), 4b³ + 27c² ≠ 0, modulo (b, c) ~ (u²b, u³c) (change of coordinate on M);
  j = 27c²/(4b³ + 27c²);
and a symbolic check that formula (11) at t = (r₂ − r₃)/(r₂ − r₁), for roots r₁ + r₂ + r₃ = 0
of x³ + bx + c, is 27c²/(4b³ + 27c²), which ties (A) to (B) and (C).

**Result.** Agrees: for every p the multisets of (j, |Aut|) from (A), (B), (D) coincide
(p + 1 classes for p ≡ 2 mod 3, p + 3 for p ≡ 1 mod 3); every j with j(j − 1) ≠ 0 carries
exactly one class, with trivial automorphisms; j = 0 carries 2 classes (H¹(F_p, Z/2)) and
j = 1 carries 3 or 1 (H¹(F_p, Z/3)), as pp. 45–47 say. About 17 s; output in results.txt.

**Side finding.** The footnote of the modernised reading on p. 53 writes the cubic as
« définie à (b, c) ↦ (u⁴b, u⁶c) près ». For triples the normalisation is (u²b, u³c);
(u⁴, u⁶) is the one for elliptic curves, and it gives twice as many classes (e.g. 12 instead
of 6 over F₅). Explicit case: over F₅, x³ + x and x³ + 4x have roots {0, 2, 3} and {0, 1, 4};
x ↦ 2x maps the second set onto the first and fixes ∞, so the triples are isomorphic, yet
(1, 0) and (4, 0) are not related by (u⁴, u⁶), since u⁴ = 1 on F₅^×. findings.ts already says
« weights 2, 3 ».

**Limits.** Only S = Spec F_p, p ≤ 31 prime: fibres, not the descriptions over a general base
(non-trivial M, torsors that do not come from a field, the non-reduced case). Over a field
X always has the rational point s, so twisted conics do not show up. Description (B)'s
equivalence (barycentre) is tested through the class counts, not as a functor.

Run: `python3 check.py`
