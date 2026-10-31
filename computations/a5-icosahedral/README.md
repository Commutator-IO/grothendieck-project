# Folder 85, pp. 10 and 40: icosahedral subgroups, Spec ℤ[T]/(T²+T−1)

Check for issue #91 (« Calculatoires »), appendix row « pages 10 et 40, sous-groupes
icosaédraux » (`docs/lean/sections/85.tex`, the `\nonverifie` corollary
`85-a5-pgl2-moduli-spec-z-phi`). Lean proves the order-5 computation over every base and
the ℤ[ζ₅] model. Rigidity and representability are not proved, and the finding is still a
`candidate`. Not settled.

## What is tested

1. **Symbolic, in ℤ[T]/(T²+T−1) and ℤ[ζ₅]** (sympy):
   - g⁵ = x₅g + y₅ with x₅ = det²(A² + A − 1);
   - A(g²) = A(g)² − 2 ≡ −1 − A(g);
   - Δ(−1, T) = (T + 2)(T − 1) ≡ −1, so the page-4 discriminant is a unit at (ν₀, ν₁) = (3, 5)
     over all of ℤ[T]/(T²+T−1);
   - the page-40 model s, p over ℤ[ζ₅]: s² = −1, (sp)³ = −1, p⁵ scalar, det p = 1, and
     A(p) = ζ² + ζ³ is a root of T² + T − 1.
2. **Points over finite fields** (`check.py`). Every form of PGL₂ over F_q is split, and
   Aut(PGL₂) = PGL₂. So rigidity plus representability predict
   #{monomorphisms 𝔄₅ → PGL₂(F_q)} = |PGL₂(F_q)| · #{x ∈ F_q : x² + x − 1 = 0},
   with each root equal to A(φ(π)) for one free conjugacy orbit. The script uses
   𝔄₅ = ⟨s, p | s², p⁵, (sp)³⟩, of order 60 and simple, so every non-trivial
   homomorphism is injective, and it enumerates all pairs (s, p).
3. **The non-reduced fibre at 5** (`dual_numbers.py`). T² + T − 1 ≡ (T − 2)² mod 5, so
   F_q-points cannot see the scheme structure there. Over R = F_q[ε]/(ε²) the claim predicts
   |PGL₂(R)| · #{roots in R} homomorphisms that are injective on the closed fibre. For
   R = F₅[ε] that is 15 000 × 5, because every 2 + yε is a root.

## Run

    python3 computations/a5-icosahedral/check.py         # about 20 s, rewrites results.txt
    python3 computations/a5-icosahedral/dual_numbers.py  # about 25 s, appends to results.txt

## Result

Everything agrees.
- All symbolic identities hold.
- q = 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31: the number of monomorphisms
  is |PGL₂(F_q)| times the number of roots. That gives 0 when 5 is not a square in F_q
  (q = 2, 3, 7, 8, 13, 17, 23, 27), 120 for F₄ and for F₅, and 59 520 for F₃₁. Each root is
  hit by exactly one free orbit, including characteristics 2, 3 and 5.
- F₂[ε], F₃[ε], F₄[ε], F₅[ε]: 0, 0, 7680 = 3840 × 2 and 75 000 = 15 000 × 5. So the
  non-reduced structure at 5 shows up exactly as Spec ℤ[T]/(T²+T−1) predicts, to first order.

## Limits

- Only finite fields up to q = 31, and dual numbers over F_q for q ≤ 5.
- Bases with non-split forms of PGL₂, higher-order thickenings at 5 (F₅[ε]/(ε³), ℤ/25) and
  general schemes are not tested.
- The test checks the R-points of the moduli for these R. It does not prove representability.
