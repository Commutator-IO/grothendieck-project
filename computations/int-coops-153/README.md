# Folder 153, pp. 3 and 9: co-operations of relative Int, over ℤ

**Statement** (docs/lean/sections/153.tex, `\nonverifie` box « forme corrigée par l'édition »):
let K₀ be a commutative k₀-algebra with K₀ ⊗_{k₀} K₀ = K₀, and Ω = {F ∈ K₀[T] : F(k₀) ⊂ k₀}, assumed
free over k₀. Then F(X+Y) and F(XY) are images of unique elements of Ω ⊗ Ω.

**Already in Lean.** The case where K₀ is a localisation, and the case where K₀ is flat with
K₀ ⊗ K₀ = K₀, are proved (Folder153.lean, the statements « co-opérations » and « sans
localisation » (3)). What is open is the non-flat case.

**Reduction over k₀ = ℤ (argument, checked on examples).** If K₀ has a non-zero element t′ with
p t′ = 0 for a prime p, then F = t′(T^p − T) is a non-zero element of Ω (F(m) = 0 for all m ∈ ℤ)
and p F = 0. So Ω is not free. Hence a free Ω forces K₀ to be torsion-free, that is flat over ℤ,
and the statement over ℤ is the Lean-proved flat case. The script exhibits this torsion for the
non-flat epimorphisms K₀ = ℤ/n × ℤ[1/n] (n = 2, 3, 4, 6, 10, 12), where K₀ ⊗ K₀ = K₀ holds.

**What the script does** (`python3 check.py 16`, about 5 s, exact arithmetic). For
K₀ ∈ {ℚ, ℤ, ℤ[1/2], ℤ[1/3], ℤ[1/5], ℤ[1/6], ℤ[1/30]}, Ω = Int(ℤ) ∩ K₀[T]:
- It computes a ℤ-basis of Ω_{≤16} by Smith normal form. In binomial coordinates the lattice is
  {c ∈ ℤ^{d+1} : c ∈ B·ℤ_S^{d+1}}, B being the monomial-to-binomial matrix.
- It checks that this lattice is all of Ω_{≤16}. Each basis vector has ℤ_S coefficients and
  integer values. Also |det| = ∏ⱼ 1/aⱼ, where aⱼ is the S-part of j!, and this is the smallest
  covolume any lattice of leading coefficients allows.
- For every basis element F, it writes F(X+Y) and F(XY) in the basis eᵢ(X)eⱼ(Y). This basis is
  unique since the eᵢ are ℚ-independent, and Ω_{≤d} is a direct summand of Ω. The script checks
  that all the coefficients are integers.
- Negative control: a lattice that is not Ω (2·C(T,2) in place of C(T,2)) is rejected.

**Result** (results.txt): 0 non-integral coefficients in all 7 cases up to degree 16. The control
fails as it should. For ℤ/n × ℤ[1/n], Ω has torsion, so the hypothesis is never met there.
Verdict: agrees.

**Limits.** k₀ = ℤ only, degrees ≤ 16, seven localisations. Every free case over ℤ is flat and so
already covered by Lean. Whether the non-flat case can occur with Ω free over another k₀ (where
the edition's form would say something new) is not tested.
