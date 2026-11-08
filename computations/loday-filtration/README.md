# The rank filtration on the span of the n-cycles

Scripts for the note `docs/loday-filtration/article.tex` (PDF on the Method tab, « Sub-articles »).

Everything happens in the group algebra ℚ[Σ_n]. For a partition λ of n, V_λ is the irreducible
representation of shape λ and ℓ(λ) its number of rows. The rank filtration is

    F_i = ⊕_{ℓ(λ) ≤ i} End(V_λ)  ⊂  ℚ[Σ_n],

the image of the gl_i-coinvariants of gl_i^{⊗n}, by Schur–Weyl duality. k(U_n) is the span of the
(n − 1)! n-cycles. The scripts compute dim F_i k(U_n) = dim (k(U_n) ∩ F_i).

Test used: an element x of k(U_n) lies in F_i iff x·e_λ = 0 for every λ with ℓ(λ) > i (e_λ the
central idempotent), iff G x = 0, where G is the integer positive semidefinite matrix
G[c, c'] = Σ_{ℓ(λ)>i} dim(λ) χ_λ(c⁻¹c') on the n-cycles. Characters by Murnaghan–Nakayama,
checked by Σ dim(λ)² = n! and column orthogonality.

## Files

- `common.py`: partitions, characters, cycle types, the n-cycles.
- `gram.py n`: ranks of G modulo two primes (1000003, 998244353) for i = 1..n. A full rank mod p
  gives full rank over ℚ, hence dim F_i k(U_n) = 0 exactly; otherwise the output is an upper bound.
- `mktable.py n [LQ]` and `rankmod.c`: the same in C, for n = 7, 8.
  `cc -O2 -o rankmod rankmod.c; python3 mktable.py 8; ./rankmod table_8.txt 998244353`.
  Output for n = 8 in `rank8.txt`.
- `witness.py 6 3`: exact kernel of G over ℚ (15 vectors, in `witness_n6_i3.txt`, one per line,
  `coefficient:permutation` with permutations in one-line notation p(0)p(1)…p(5)), an independent
  check of x·Σ_g χ_λ(g) g = 0 in ℚ[Σ_6] for the four λ with more than 3 rows, and the character
  of Σ_6 acting by conjugation (result: V_(3,3) ⊕ V_(3,1,1,1)). About 7 s.
- `youngsub.py 8 4 R 24`: exact dimension of F_4 k(U_8) without eliminating on the 5040 × 5040
  matrix. For Young subgroups Σ_ν and ε ∈ {trivial, sign} it computes the (Σ_ν, ε)-isotypic part
  of the kernel by fraction-free elimination over ℤ, and solves the Kostka system for the
  multiplicities. Output in `young_8_4.txt` (dimension 1708). About 80 s.
- `lqreading.py n`: the index-reversed annihilator reading, dim k(U_n) ∩ ⊕_{ℓ(λ)>r}; it vanishes
  iff n ≤ 2r for n ≤ 8, as the Amitsur–Levitzki theorem predicts.

## Results

| n | i = 1 | 2 | 3 | 4 |
|---|---|---|---|---|
| 4 | 0 | 0 | (5) | |
| 5 | 0 | 0 | (12) | |
| 6 | 0 | 0 | **15** | (100) |
| 7 | 0 | 0 | 0 | (444) |
| 8 | 0 | 0 | 0 | **1708** |

Bold: i = n/2 with n even, where the statement F_i k(U_n) = 0 for i ≤ n/2 fails. In parentheses:
i > n/2, outside that statement. For n ≤ 8, F_i k(U_n) = 0 whenever 2i < n; at 2i = n it vanishes
for n = 2, 4 and not for n = 6, 8.

The scripts are the edition's own code. No text from the Quillen notebooks is reproduced here.
