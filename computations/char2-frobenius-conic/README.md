# Folder 82, page 78, (61): the conic of a quaternion algebra in characteristic 2

**Statement** (docs/lean/sections/82.tex, appendix row « 82, page 78, (61) »;
transcripts/82/82.modern.tex, pp. 77–78). For a quaternion algebra M over a base with
2 = 0, g̃ = {Trd = 0} ⊃ O·1 = ker φ (φ(u,v) = Trd(uv), q = −det), X = Var(q) the conic of
isotropic lines; the map (60) X → P(g̃/O), L ↦ L^⊥, is the relative Frobenius
X → X^(2) followed by a canonical isomorphism (61) P(g̃/O) ≅ X^(2); it is finite, flat of
rank 2 and radicial. The split case is proved in Lean (lean/Grothendieck/Folder82.lean);
the twisted case was unchecked.

**What is tested.** The algebras [a,b): i² = i + a, j² = b, ji = (i+1)j, b a unit — the
generic twisted algebra in characteristic 2 (over F₂(a,b) it is a division algebra).
1. Symbolically over F₂[a, b, 1/b]: associativity; Trd, Nrd are the reduced trace and norm
   (x² = Trd(x)x + Nrd(x), Nrd multiplicative); φ = Trd(uv) is the polar form of q on
   g̃ = ⟨1, j, ij⟩, φ = b(x₂y₃ + x₃y₂), kernel O·1. The map (60) is (x₀:x₂:x₃) ↦ (x₂:x₃).
   With X^(2): U₀² + b²(U₂² + U₂U₃ + a²U₃²) = 0 and F(x) = (x₀² : x₂² : x₃²), the map
   ψ(U) = (U₂ : B) = (B : U₃), B = U₀/b + U₂ + aU₃ (projection of X^(2) from its rational
   point (ab : 0 : 1)) is well defined, satisfies ψ∘F = (60) as polynomial identities
   modulo q, and has the inverse (s:t) ↦ (b(s² + st + at²) : s² : t²). So (60) factors
   through F with an isomorphism X^(2) ≅ P¹ = P(g̃/O). Since F is faithfully flat (an
   epimorphism), the factorisation is unique, hence canonical; F is finite locally free of
   rank 2 and radicial as the Frobenius of a smooth relative curve.
2. Independently, on points: for R = F₂, F₄, F₈, F₂[ε]/ε², F₂[ε]/ε³, F₄[ε]/ε² and every
   (a, b) ∈ R × R^×, at every point of X(R), (60) is defined and equals ψ(F(x)), and
   ψ : X^(2)(R) → P¹(R) is a bijection (about 2 minutes).

**Result.** Agrees: every identity holds, every point check passes (results.txt).

**Limits.** Only algebras with a presentation [a,b) with b a unit. Locally on a base every
quaternion algebra in characteristic 2 has one with a, b sections (a quadratic étale
subalgebra O[i], i² = i + a, and j with ji = (i+1)j); that this holds Zariski-locally with
b a unit is assumed here, not checked. The canonicity of (61) rests on the uniqueness of the
factorisation through F, not on a separate computation; compatibility with automorphisms of
M is not tested. No Lean.

Run: `python3 check.py`
