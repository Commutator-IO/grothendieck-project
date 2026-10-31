# Folder 85, pp. 4–7: moduli of representations of G₂ in PGL₂

Check for issue #91 (« Calculatoires »), appendix row « D'après les pages 4 à 7, modules des
représentations de $G_2$, reformulation de l'édition » (`docs/lean/sections/85.tex`, the
`\nonverifie` theorem `85-g2-pgl2-moduli-over-z`). Lean (`lean/Grothendieck/Folder85.lean`)
proves the trace identities, the rigidity and a normal form over any ring, but not the
representability by the complement of three lines in 𝔸²_ℤ. That part is not settled.

## What is tested

`G₂ = ⟨τ₀, τ₁, τ₂ | τᵢ², (τ₀τ₂)²⟩`, `ρ₀ = τ₀τ₁`, `ρ₁ = τ₁τ₂`, `A(g) = tr(g)²/det(g) − 2`,
`Δ = (α₀+2)(α₁+2)(α₀+α₁)`, and (*) = « ρ₀² ≠ 1, ρ₁² ≠ 1, ρ₀ρ₁ ≠ ρ₁ρ₀ ».

1. **Symbolic** (sympy): for traceless 2×2 matrices, `Δ·d₀²d₁³d₂² + t₀₁²t₁₂²T²` lies in the
   ideal `(t₀₂)`. So the discriminant is minus a square of traces once `t₀₂ = 0`. Also
   `ρ₀ρ₁ − ρ₁ρ₀ = −T τ₁`.
2. **F_q-points of the moduli claim.** Over a finite field every form of PGL₂ is split (Lang)
   and Aut(PGL₂) = PGL₂. So, if the theorem holds, the homomorphisms G₂ → PGL₂(F_q)
   satisfying (*) are |PGL₂(F_q)| × #{(α₀, α₁) ∈ F_q² : Δ ≠ 0} in number, and each admissible
   pair is one free conjugacy orbit. The script lists all triples of elements of PGL₂(F_q)
   with square 1 (the identity included) and checks:
   - (*) ⇒ Δ ≠ 0;
   - every admissible pair occurs, with exactly |PGL₂(F_q)| homomorphisms;
   - these form a single orbit under conjugation, with trivial stabiliser;
   - the number of admissible pairs is q² − 3q + 3, or q² − 3q + 2 in characteristic 2,
     where the three lines meet in one point.
3. **The corollary on orders (pp. 6–7).** For every g ≠ 1 in PGL₂(F_q) and 2 ≤ ν ≤ 30:
   ord(g) = ν ⇒ Ψ_ν(A(g)) = 0. Conversely, Ψ_ν(A(g)) = 0 ⇒ ord(g) = ν whenever ν is prime
   or invertible in F_q. Here Ψ_ν is the minimal polynomial of 2cos(2π/ν), with Ψ₂ = x + 2.

## Run

    python3 computations/g2-pgl2-moduli/check.py     # about 10 s, writes results.txt

Python 3 standard library plus sympy. `gf.py` is a small finite-field module.

## Result

Everything agrees, for q = 2, 3, 4, 5, 7, 8, 9, 11, 13 (see `results.txt`). For example,
over F₁₃ there are 290 472 = 2184 × 133 homomorphisms with (*), one free orbit per pair.
Over F₂ there are none, consistent with q² − 3q + 2 = 0. The order criterion has no
exception. Without its proviso it fails: for every q some composite ν divisible by p has
Ψ_ν(A(g)) = 0 while g has another order, e.g. ν = 22 over F₁₁ and ν = 4, 6 over F₂.
So the condition « νᵢ invertible if νᵢ is not prime » is needed.

## Limits

- Only finite fields, so only F_q-points of the moduli. The scheme structure over ℤ,
  non-split forms over general bases, and representability itself are not tested.
  (On F_q-points representability reduces to the counts above.)
- q ≤ 13 and ν ≤ 30.
- The symbolic identity is checked by division by the single generator t₀₂. That is a
  valid membership test for a principal ideal.
