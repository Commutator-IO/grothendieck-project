# Folder 1, pp. 71–72: the system (16) for compact operators

**Statement** (docs/lean/sections/1.tex, `\nonverifie` box « Pages 71 et 72, opérateurs compacts »):
for compact operators u, v between Hilbert spaces and 0 ≤ m ≤ n,
σₙᵐ(u+v) ≤ Σₚ σₙᵖ(u) σₙᵐ⁻ᵖ(v), where σₙᵐ(w) = eₘ(s₀(w), …, sₙ₋₁(w)); hence the product form
∏_{i<n}(1 + r sᵢ(u+v)) ≤ ∏(1 + r sᵢ(u)) ∏(1 + r sᵢ(v)) for r ≥ 0.

**Status.** In finite dimension this is proved in Lean (`sigma_system`, `sigma_system_real`,
`prod_one_add_singularValues_add_le_real`, lean/Grothendieck/Folder1.lean). What is not formalised
is only the passage to compact operators. That step is not a finite computation: if P_N is the
projection on the first N vectors of a basis, ‖P_N w P_N − w‖ → 0 for compact w, and
|sᵢ(a) − sᵢ(b)| ≤ ‖a − b‖ (Weyl), so each side, a polynomial in finitely many sᵢ, is the limit
of the finite-dimensional one. A computer can only test matrices, which Lean already covers.

**What the script does** (`python3 check.py 60`, under a second, mpmath at 30 digits):
1. A sanity check of the matrix case: 60 random complex pairs u, v of size a × b with a, b ≤ 5
   (generic, near-cancelling v ≈ −u, and rank one), every n ≤ min(a,b)+1 and m ≤ n, and the
   product form for r ∈ {0.1, 1, 10}.
2. The truncation argument on two explicit compact operators of ℓ²: u = diag(1/(k+1)) and the
   weighted shift v eₖ = eₖ₊₁/√(k+1), truncated at N = 8, 16, 32, with n ≤ 5.

**Result** (results.txt): no violation. The largest value of LHS − RHS is 0, reached only at m = 0
where both sides are 1. The product form holds with margin. The first five sᵢ(u+v) of the
truncations agree to 6 digits from N = 16 on.

**Limits.** Numerical floating point, with matrices of size at most 5 and two particular operators.
It says nothing that the Lean proof plus Weyl's inequality do not already give. The verdict is
« not-checkable »: the open part (compact operators) has no finite content.
