# Counting Kostant rigidifications (A2, B2, G2 over F_q)

This is the computer check that the problem « Counting Kostant rigidifications »
(`p:kostant` in `docs/problems/article.tex`; finding `123-kostant-rigidifications-count`;
folder 123, pp. 21, 28, 30, 34) asks for. It counts the orbits of G(F_q) on Kostant
rigidifications (T, B, T', B') for the split adjoint groups of type A2, B2 and G2.
It compares them with the folder's numbers card(W)^2/(h z phi(h)), and card(W)^2/(h z)
once a generator of T ∩ N(T') is fixed.

## Run

    python3 computations/kostant/kostant_count.py          # all cases; writes results.json
    python3 computations/kostant/kostant_count.py G2       # one type, prints only

It uses the Python 3 standard library only and takes about 30 s in total.

## Result

| type | q covered        | h | z | orbits | page | with generator | page | |N(T)∩N(T')| | h z phi(h) |
|------|------------------|---|---|--------|------|----------------|------|---------------|------------|
| A2   | 7, 13, 19, 31, 37 | 3 | 3 | 2  | 2  | 4  | 4  | 18 | 18 |
| B2   | 5, 13, 17, 29, 37 | 4 | 2 | 4  | 4  | 8  | 8  | 16 | 16 |
| G2   | 7, 13, 19, 31, 37 | 6 | 1 | 12 | 12 | 24 | 24 | 12 | 12 |

For every q tested, the counts agree with the page. The action is free: every orbit has
exactly |T(F_q)| = (q-1)^2 elements. Also, for every q:

- T ∩ T' = 1;
- T ∩ N(T') is cyclic of order h;
- the image of N(T) ∩ N(T') in W has order z·phi(h) (6, 4, 2), so the group is an
  extension of order h·z·phi(h), as the letter's footnote says;
- the number of rational split tori in apposition with a fixed T is
  |W|(q-1)^2 / (h z phi(h)), so they form a single N(T)(F_q)-orbit.

An extra fact, which bears on the letter's question: in every orbit, dim(Lie B ∩ Lie B') = 2 = rank.
So B and B' are opposite, and B ∩ B' is a maximal torus, for all classes in these three types.

The counts are the same for all five q of each type. This is evidence that the finite
étale quotient RigKos/G is constant over F_q for q ≡ 1 mod h, with rank equal to these counts.

## Conventions

- Lie algebras. A2 is sl3. B2 is so5, for Q = v0² + v1v₋1 + v2v₋2. G2 is the stabiliser in gl7
  of the split-octonion 3-form v0∧(v1∧v₋1 + v2∧v₋2 + v3∧v₋3) + v1∧v2∧v3 + v₋1∧v₋2∧v₋3.
  Each one is computed as a kernel mod p, and the script checks its dimension (8, 10, 14).
  The diagonal Cartan subalgebra is t0 = Lie T0.
- Group. G = G_ad(F_q). It acts on g through automorphisms. T0(F_q) is Hom(Q, F_q^*): it scales
  e_α by χ(α). Weyl lifts are n_α = exp(ad e)exp(-ad f)exp(ad e).
- Tori and Borels. A maximal torus is described by its Lie algebra, and a Borel by its
  Borel subalgebra. Both are stored as subspaces of g in reduced echelon form.
- Apposition (Kostant). T' is in apposition with T if, for some positive system of
  Φ(T) with simple roots β1, β2 and highest root θ, Lie T' is the centraliser of
  e = c1 e_β1 + c2 e_β2 + c0 e_₋θ with all c_i ≠ 0. This is page 34's
  e = Σ e_αi + e_₋ψ, read up to the action of T and up to scaling.

## Reduction (what is enumerated, and what is argued)

1. Assume (T, B, T', B') is rational. Then T and T' are split, because each lies in a
   rational Borel. G(F_q) acts transitively on rational pairs (T, B), with stabiliser
   T(F_q), by Lang's theorem and B ∩ N(T) = T. So the orbits counted are the orbits of
   T0(F_q) on pairs (t', b') with b = b0 fixed. These pairs are enumerated, and each orbit
   is generated element by element.
2. Fix q ≡ 1 mod h. Then κ(μ_h) ⊂ T0(F_q). For a rational T' in apposition, the line
   D = Lie T' ∩ g_ζ (the eigenline of Ad κ(ζ)) is Frobenius-stable. So e can be taken
   rational. Up to T0(F_q), it can then be taken to be e_β1 + e_β2 + c e_₋θ with
   c ∈ F_q^*. The script enumerates every positive system and every c. It keeps the
   centralisers that are regular and split (some c give non-split T', which carry no
   rational B'). The Borels containing t' come from the simultaneous eigenspaces of ad t'.
   Their number is checked to be |W|.
3. Freeness is checked on the computer: every orbit has size |T0(F_q)|.
   |N(T) ∩ N(T')| is counted directly over all t·n_w.
4. Fixing a generator of T ∩ N(T') multiplies the count by phi(h). The group T acts
   trivially on its own elements, and the action is free, so this is exact once
   T ∩ N(T') ≅ Z/h has been verified. The script records the factor; it does not
   enumerate the generators separately.

## Limits

- Only prime fields with q ≡ 1 mod h were covered (B2 includes q = 5). The case
  q ≢ 1 mod h is not treated: there, step 2 needs a Galois-descent argument, and the
  rational count can be smaller than the rank.
- The geometric rank is inferred from the rational counts being constant across five
  primes. It was not computed over F̄_q.
- Steps 1 and 2 are standard arguments. They are not machine-checked; only the
  enumeration after them is.
- This is not a proof for general G. Larger ranks (A3, B3, ...) were not attempted.
