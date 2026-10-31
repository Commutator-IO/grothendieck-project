# Folder 5, page 7: the quotients W^(ν,r)

**Statement** (docs/lean/sections/5.tex, appendix row « 5, page 7, les quotients W^{(ν,r)} »;
transcripts/5/5.modern.tex, Lemme (page 7)). In
A^(ν) = W[Λ₀,…,Λ_ν]/(Λᵢ^p − qᵢΛᵢ₊₁ (i < ν), Λ_ν^p), with Λᵢ = λᵢ + Θᵢ,
λᵢ = p^{p^i}/(p^i)!, qᵢ = (p^{i+1})!/((p^i)!)^p, an element Σ w_a Θ^a
(0 ≤ aᵢ ≤ p−1) lies in I_{ν,r} = (Θ₀,…,Θ_r) iff
a) w_a ∈ p^{i−r}W when the first non-zero aᵢ has i > r (no condition for i ≤ r),
b) w₀ ∈ p^{c(ν)−r}W, c(ν) = ν + p·v_p(λ_ν).

The case r = 0 is the page-5 lemma, already proved in Lean (lean/Folder5.lean);
the quotients r ≥ 1 are not formalised. This script checks all r, 0 ≤ r ≤ ν.

**How.** W = Z_(p) (the statement only involves Z_(p)-coefficients, so it base-changes
to any W). Arithmetic in Z/p^N, N = c(ν)+1. The script builds the multiplication of
A^(ν) in the Λ-basis (carry Λᵢ^p = qᵢΛᵢ₊₁), the unitriangular change of basis to the
Θ^a, and the W-span of the generators Θ_j·Θ^a (j ≤ r, all a) in Θ-coordinates. It checks
(1) every generator lies in the diagonal lattice L of a), b), so I ⊆ L;
(2) the length of A/(I + p^N A), from a Smith form over Z/p^N, equals the length of A/L.
Since p^N A ⊆ pL, (1)+(2) give I + pL = L, hence I = L by Nakayama: an exact check, not a
truncation. As a control, shifting any exponent of the lattice by ±1 makes the check fail.

**Result.** Agrees in every case tried: (p, ν) = (2,1…6), (3,1…4), (5,1), (5,2), (7,1),
(7,2), (11,1), (13,1), every r from 0 to ν (56 cases, about 4 s). Output in results.txt.
For r = ν the quotient is W/p^{p·v_p(λ_ν)}, as the edition's footnote says.

**Limits.** Finitely many (p, ν); no proof for general p, ν. The normal-form corollary of
page 7 follows from the lemma (the lattice is diagonal in the Θ^a basis) and is not
tested separately.

Run: `python3 check.py`
