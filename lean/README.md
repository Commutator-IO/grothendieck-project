# Lean

The Lean proofs of the Grothendieck fonds (the folders, the Buffalo lectures of 1973, the open
problems) and the vendored Stacks files now live in
**[Commutator-IO/GrothendieckArchivesProofs](https://github.com/Commutator-IO/GrothendieckArchivesProofs)**.
Look there for them, their build and their CI.

Two libraries stay in this repository: `Bourbaki/` (the rédactions of the Bourbaki archive) and
`Quillen/` (Daniel Quillen's notebooks).

## Bourbaki and Quillen

Lean 4 proofs, against mathlib, of statements made by a rédaction of the Bourbaki archive or a
page of Quillen's notebooks. A proof here says that what the reading states **holds together**,
not that it is what the page says: a perfectly formalised statement can be a perfectly
formalised misreading.

```bash
cd lean && lake exe cache get && lake build Bourbaki Quillen   # fails on any warning, so on any sorry
```

Mathlib is pinned to a revision of its `master` (`rev` in `lakefile.toml`, with the toolchain in
`lean-toolchain`). To move the pin: set `rev` to the new SHA, copy `lean-toolchain` from that
Mathlib revision, run `lake update mathlib` (it fetches the cache), then build the libraries one
at a time, since a process that imports Mathlib takes about 2 GB. A deprecation in Mathlib fails
the build; the compiler names the replacement.

| Source | File | Scope | Found |
|---|---|---|---|
| Bourbaki 288 | `Bourbaki/Redaction288.lean` | Rédaction n° 288 (1958), Cor. 2, PDF pp. 32–33: currying C(X × Y, Z) ≃ₜ C(X, C(Y, Z)) is a homeomorphism for the compact-open topologies when Y is locally compact and every point of a compact subset K of X has small neighbourhoods in K that are compact (true for X locally compact, R1, hence Hausdorff); curry is continuous under the hypothesis on X alone | holds with E preregular and F locally compact in mathlib's sense, no Hausdorff hypothesis on F; mathlib's `Homeomorph.curry` asks X locally compact; the page uses E Hausdorff exactly where the proof covers a compact M ⊆ E × F by compact rectangles; whether E Hausdorff can be dropped is not decided |
| Bourbaki 457 | `Bourbaki/Redaction457.lean` | Rédaction n° 457 (Oct. 1965), Cor. 6 of Prop. 14, PDF pp. 32–33, refuted: for any field k, the k-algebra A of functions on the Cantor set ℕ → Bool depending on finitely many coordinates (the locally constant ones) is integral, each element a root of a separable polynomial split over k, has [A : k] ≤ ℵ₀, and has at least 𝔠 k-algebra maps into any nonzero k-algebra Ω (evaluations at points), so [A : k] ≠ card P(A) | the page's proof only shows P(A) infinite, which its N.B. and a reader's margin concede; the identification of A with locally constant functions, [A : k] = ℵ₀, P(A) ≃ C, and the true finite-degree case are not formalised |
| Bourbaki 205 | `Bourbaki/Redaction205.lean` | Rédaction n° 205 (n.d.), Exercise 2, p. 45: discrete fibres and unique lifting of maps from the square characterise coverings | false as typed, over [0, 1]: a union of sheets accumulating on a segment has discrete fibres and unique lifts from connected spaces but is not locally injective; the correct statement (add local homeomorphism) is textbook |
| Bourbaki 239 | `Bourbaki/Redaction239.lean` | Rédaction n° 239 (June 1956), p. 86: is every soft sheaf fine? | answered no: on [0, 1], U ↦ C(U, 𝕋) is soft but not fine (not fine over any connected space); candidate, MathOverflow 423444 unanswered |
| Bourbaki 128 | `Bourbaki/Redaction128.lean` | Rédaction n° 128 (Mar. 1950), Commentaires, Props. A, A′, B: bounded semilinear maps from a first-countable space are continuous; a Baire space is barrelled | already in mathlib (`LinearMap.continuous_of_locally_bounded`, `BaireSpace.instBarrelledSpace`); the file only cites them |
| Bourbaki 321 | `Bourbaki/Redaction321.lean` | Rédaction n° 321 (1959), Props. 2, 4, 5, pp. 4–5: pullback / pushout squares in an abelian category iff the biproduct sequence is exact; a pullback with an epi side is a pushout, and dually; base change of epis | holds; the dual of Prop. 4 as typed (bottom arrow mono) is false, the intended arrow is the top one |
| Bourbaki 402 | `Bourbaki/Redaction402.lean` | Rédaction n° 402 (June 1964), § 5 n° 1, Def. 1, Props. 1–2 and corollaries, pp. 10–11: localizable distances (infimum of the lengths of W-chains for every neighbourhood W of the diagonal) | holds; connectedness follows and is not needed; the ε-chain variant of the facing note is strictly weaker (ℚ) |
| Bourbaki 438 | `Bourbaki/Redaction438.lean` | Rédaction n° 438 (Mar. 1965), Lemma 1, p. 35: one triangle identity and the other composite invertible give an adjunction | holds, by idempotence (shorter than the page); probably Johnstone, Elephant A1.1.1, unchecked |
| Bourbaki 448 | `Bourbaki/Redaction448.lean` | Rédaction n° 448 (Aug. 1965), Remark p. 20: can the hypothesis on the D(i) be dropped for free objects over a diagram? | answered no: a cofree (and a free) object over a diagram whose value is not cofree (free) pointwise |
| Bourbaki 453 | `Bourbaki/Redaction453.lean` | Rédaction n° 453 (Sept. 1965), step a): under axiom (AG) on τ, universes form a chain | holds for any family of sets satisfying (AG); step b) and the artinian conclusion not formalised |
| Bourbaki 461 | `Bourbaki/Redaction461.lean` | Rédaction n° 461 (Feb. 1966), § 2.6, pp. 65–77: semi-cartesian squares, Def. 3, Props. 13–15, Cors. 1, 2, 4 | holds; Prop. 13 in an equivalent form of the edition; Prop. 15 under weaker hypotheses; Props. 16 (Cor. 1), 17, 17 bis not formalised; candidate (Freyd 1964, Mitchell 1965 to check) |
| Bourbaki 469 | `Bourbaki/Redaction469.lean` | Rédaction n° 469 (May–June 1966), errata p. 52: for C nonempty, const : A ⥤ (C ⥤ A) creates limits and colimits; A inherits limits, a zero object, abelianness | holds; the abelian corollary takes A preadditive; candidate |
| Bourbaki 476 | `Bourbaki/Redaction476.lean` | Rédaction n° 476 (Oct. 1966), Exercises 2 and 3, p. 6: orientations of trees, period of a quiver | both false as typed (infinite star; a three-vertex quiver without strong connectivity); trees with a ray proved |
| Bourbaki 582 | `Bourbaki/Redaction582.lean` | Rédaction n° 582 (June 1972), n° 3, p. 12: Schur indices over ℝ | the typed (m, e) = (2, 2) for ℂ and ℍ is false; (2, 1) and (1, 2) from the dimensions |
| Bourbaki 596 | `Bourbaki/Redaction596.lean` | Rédaction n° 596 (May 1974), § 10, Prop. 3 a): every class in a Grothendieck group is a difference | holds for any additive map whose image generates; modules and K(C) not formalised |
| Quillen 1968-14 | `Quillen/Notebook1968_14.lean` | Notebook 1968-14 (Clay), remark p. 28 after the proposition of p. 27: for f : V → X \ A continuous, f⁻¹B compact for every closed B ⊆ X disjoint from A iff f is proper to X \ A and closure (f V) is compact (`preimage_compact_iff`) | holds for X metrizable, A any subset, V any space: no local compactness, no σ-compactness of V (the page's exhaustion), A need not be closed; the converse needs nothing on X; whether metrizability can be weakened is not decided |
| Quillen 1971-11 | `Quillen/Notebook1971_11.lean` | Notebook 1971-11 (Clay), lemma p. 68, proof p. 69: for p ≥ 3, θ with θ^p = 1 trivial on the elements killed by p, on an abelian p-primary group, p(θ − 1) = 0 (`nsmul_sub_one_eq_zero`, `addEquiv_nsmul_sub_one_eq_zero`) | holds for any p-primary torsion abelian group (no finiteness) and any endomorphism; induction on the order instead of the page's dual; false for p = 2 (`zmod8_neg`: ℤ/8, θ = −1); the propositions of pp. 69–71 not formalised |
| Quillen 1983-10 | `Quillen/Notebook1983_10.lean` | Notebook 1983-10 (Clay), p. 31: the question whether tr((e₁ − e₂)^(2n+1)) is independent of n; in finite dimension tr((P − Q)^(2k+1)) = tr P − tr Q for idempotent matrices (`trace_sub_pow_odd`) | holds over every commutative ring, characteristic 2 included (the anticommutation proof divides by 2; this one does not); the infinite-dimensional statement is Avron–Seiler–Simon, J. Funct. Anal. 120 (1994), not formalised |
