# Picard group of the stack [U₀,₃/𝔖₃] (folder 140-1, pp. 22, 24, 29)

Tests what Lean leaves open in « Picard du champ [U₀,₃/𝔖₃] » (appendix of
`docs/lean/article.tex`; Findings piste `140-1-equivariant-pic-u03`). Run
`python3 check.py` (about 3 s); the output is `results.txt`.

## Already settled in Lean

`lean/Grothendieck/Folder140_1.lean` (see `lean/README.md`, row 140-1) proves
the following:

* H¹(𝔖₃, O(U₀,₃)^*) ≅ ℤ/6, and ℤ/3 when 2 = 0, in the model k^* × V(J) of the
  units, for a domain k. The generator there is the tangent class.
* The units of k[λ, 1/λ, 1/(1−λ)] are the model, as abelian groups
  (`unitsEquiv`).
* Pic(U₀,₃) = 0 over a field.

Lean leaves open: the 𝔖₃-action on the ring and the equivariance of
`unitsEquiv`, Hochschild–Serre, a general base S, and the page's generator
O(1).

## What is tested here

* **E. Equivariance.** 𝔖₃ acts on P¹ by the Möbius maps that permute 0, 1, ∞,
  and on functions by σ·u = u ∘ h, where h induces σ⁻¹ on the three points.
  This is the convention of the docstring of `sgnExp`. For every σ and every
  u = λ^a (1−λ)^b with |a|, |b| ≤ 4, sympy checks that σ·u equals
  (−1)^{sgnExp σ v} λ^{a'} (1−λ)^{b'}. Here v = (a, b, −a−b) is the divisor on
  (0, 1, ∞), (a', b', ·) = σ·v with (σ·v)_i = v_{σ⁻¹ i}, and `wt` is copied
  from Lean. The script also checks that this is a left action on λ and 1 − λ
  (all 36 pairs σ, τ). The identities hold over ℤ, hence over every ring, and
  both sides are multiplicative in u. Together these give the equivariance of
  `unitsEquiv` for the actual ring action.
* **O. The generator O(1).** Σ_J = P(V_J) carries its natural
  𝔖₃-linearisation. The script checks that Σ_J^* ≅ U₀,₃ via
  λ = (x₁−x₂)/(x₁−x₃) and that the induced action on λ is the six anharmonic
  substitutions. By unique factorisation, the invertible sections of O(n) on
  Σ_J^* are c ∏ (x_j − x_k)^{a_jk} with Σ a_jk = n. [O(1)]^n = 0 in the
  equivariant Picard group exactly when one of these sections is invariant.
  The script searches n = 1 to 12, |a_jk| ≤ 12, in characteristic 0, 2, 3, 5
  and 7. It screens exponent vectors for invariance under the induced
  permutation of the pairs. For the survivors it has sympy compute σ(f)/f for
  a transposition and a 3-cycle and tests whether it is 1 mod p.

## Result

* E holds in 486 of 486 cases, with no left-action failure. The ring action is
  the model's action, signs included.
* O: the least n is **6** in characteristic 0, 3, 5 and 7, given by
  ∏(x_j − x_k)², which is −Δ. In characteristic 2 it is **3**, given by
  ∏(x_j − x_k). So [O(1)] has order 6 (resp. 3). Lean shows that the H¹ has
  order dividing 6 (resp. 3), so O(1) generates it. This is the page's claim,
  with characteristic 3 included. **Agrees.**

## Limits

* Fields of characteristic 0, 2, 3, 5 and 7 only, in the sense that
  constants are tested mod p. The O check is done over ℤ and then reduced.
* The search box is |a_jk| ≤ 12. This is enough, since the invariant vectors
  are (m, m, m).
* Two steps rest on theory and are not computed:
  * the passage from H¹(𝔖₃, O(U)^*) to the Picard group of the stack (an
    equivariant line bundle with trivial underlying bundle is a 1-cocycle,
    together with Pic(U₀,₃) = 0);
  * a general regular base S with Pic(S) = 0.

  The « caractéristique générique 2 » clause is only checked for fields of
  characteristic 2.
