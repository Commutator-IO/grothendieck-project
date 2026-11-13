import Mathlib

/-!
# Quillen, notebook 1971-12, pp. 23–24: a group with `F V = V F = p ^ d` and `F = p ^ (d + r)`

Daniel Quillen's research notebook 1971-12 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201971/1971-12.pdf>) considers,
on pp. 22–24 (September 1971), the Frobenius `F` and its transfer `V` on the `K`-groups of a ring
of characteristic `p`, for which `V F = F V = p ^ d`. To combine this with a conjecture on the
`γ`-filtration he isolates a lemma on abelian groups (p. 23, his p. 2), proved on p. 24. In our
words: let `M` be an abelian group with two endomorphisms `F`, `V` such that
`F V = V F = p ^ d` and `F = p ^ (d + r)` with `r > 0`. Then `M` is the direct sum of `p ^ d M`
and of the subgroup `M[p ^ d]` of elements killed by `p ^ d`; the first is the largest
`p`-divisible subgroup and the second is the whole `p`-torsion subgroup.

His proof shows `p ^ d (x - p ^ r V x) = 0`, uses that `1 - p ^ r V` is an automorphism of
`M[p ^ d]` to split `M`, and iterates `x = p ^ r V x` on the kernel. This file proves the lemma
by iterating the first identity on every element instead: for each `n`,
`x = t + p ^ (n r) Vⁿ x` with `p ^ d t = 0`. The number `p` need not be prime.

* `nsmul_sub_eq_zero`: `p ^ d (x - p ^ r V x) = 0`;
* `nsmul_eq_zero_of_nsmul_add`, `nsmul_eq_zero_of_pow_nsmul`: an element killed by a power of
  `p` is killed by `p ^ d`, so `M[p ^ d]` is the whole `p`-power torsion;
* `exists_decomp`: `x = t + p ^ (n r) Vⁿ x` with `p ^ d t = 0`;
* `exists_nsmul_eq`: `p ^ d M ⊆ p ^ s M` for every `s`, so `p ^ d M` is `p`-divisible;
* `le_range_of_divisible`: a subgroup `D` with `D ⊆ p D` lies in `p ^ d M`, so `p ^ d M` is the
  largest `p`-divisible subgroup;
* `isCompl_range_ker`: **the lemma of the page**, `M = p ^ d M ⊕ M[p ^ d]`.
-/

namespace Quillen.Notebook1971_12

variable {M : Type*} [AddCommGroup M] {p d r : ℕ} {F V : M →+ M}

/-- `p ^ d (x - p ^ r V x) = 0`: the first line of the proof of p. 24. -/
theorem nsmul_sub_eq_zero (hFV : ∀ x, F (V x) = p ^ d • x) (hF : ∀ x, F x = p ^ (d + r) • x)
    (x : M) : p ^ d • (x - p ^ r • V x) = 0 := by
  rw [smul_sub, smul_smul, ← pow_add, ← hF (V x), hFV, sub_self]

/-- An element killed by `p ^ (d + r)` is killed by `p ^ d`. -/
theorem nsmul_eq_zero_of_nsmul_add (hVF : ∀ x, V (F x) = p ^ d • x)
    (hF : ∀ x, F x = p ^ (d + r) • x) {x : M} (h : p ^ (d + r) • x = 0) : p ^ d • x = 0 := by
  rw [← hVF x, hF x, h, map_zero]

/-- An element killed by a power of `p` is killed by `p ^ d`: the subgroup `M[p ^ d]` is the
whole `p`-power torsion of `M`. -/
theorem nsmul_eq_zero_of_pow_nsmul (hVF : ∀ x, V (F x) = p ^ d • x)
    (hF : ∀ x, F x = p ^ (d + r) • x) (hr : 0 < r) :
    ∀ (s : ℕ) (x : M), p ^ s • x = 0 → p ^ d • x = 0 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro x hx
    by_cases hs : s ≤ d + r
    · apply nsmul_eq_zero_of_nsmul_add hVF hF
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
      rw [hk, pow_add, mul_comm, mul_smul, hx, smul_zero]
    · have h1 : p ^ (d + r) • (p ^ (s - r - d) • x) = 0 := by
        rw [smul_smul, ← pow_add, show d + r + (s - r - d) = s by omega, hx]
      have h2 := nsmul_eq_zero_of_nsmul_add hVF hF h1
      rw [smul_smul, ← pow_add, show d + (s - r - d) = s - r by omega] at h2
      exact ih (s - r) (by omega) x h2

/-- For every `n`, `x = t + p ^ (n r) Vⁿ x` with `p ^ d t = 0`. -/
theorem exists_decomp (hFV : ∀ x, F (V x) = p ^ d • x) (hF : ∀ x, F x = p ^ (d + r) • x)
    (n : ℕ) (x : M) : ∃ t : M, p ^ d • t = 0 ∧ x = t + p ^ (n * r) • (V^[n]) x := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨t, ht, hx⟩ := ih
    refine ⟨t + p ^ (n * r) • ((V^[n]) x - p ^ r • V ((V^[n]) x)), ?_, ?_⟩
    · rw [smul_add, ht, zero_add, smul_comm, nsmul_sub_eq_zero hFV hF, smul_zero]
    · rw [Function.iterate_succ_apply', show (n + 1) * r = n * r + r by ring, pow_add, mul_smul,
        smul_sub]
      conv_lhs => rw [hx]
      abel

/-- `p ^ d M ⊆ p ^ s M` for every `s`: the subgroup `p ^ d M` is `p`-divisible. -/
theorem exists_nsmul_eq (hFV : ∀ x, F (V x) = p ^ d • x) (hF : ∀ x, F x = p ^ (d + r) • x)
    (hr : 0 < r) (s : ℕ) (x : M) : ∃ z : M, p ^ d • x = p ^ s • z := by
  obtain ⟨t, ht, hx⟩ := exists_decomp hFV hF s x
  have hs : s ≤ s * r := Nat.le_mul_of_pos_right s hr
  refine ⟨p ^ (d + s * r - s) • (V^[s]) x, ?_⟩
  rw [smul_smul, ← pow_add, show s + (d + s * r - s) = d + s * r by omega]
  conv_lhs => rw [hx]
  rw [smul_add, ht, zero_add, smul_smul, ← pow_add]

/-- A subgroup `D` with `D ⊆ p D` lies in `p ^ d M` (no hypothesis on `F`, `V`): together with
`exists_nsmul_eq`, `p ^ d M` is the largest `p`-divisible subgroup. -/
theorem le_range_of_divisible (D : AddSubgroup M) (hD : ∀ x ∈ D, ∃ y ∈ D, x = p • y) :
    ∀ (k : ℕ), ∀ x ∈ D, ∃ y ∈ D, x = p ^ k • y := by
  intro k
  induction k with
  | zero => exact fun x hx => ⟨x, hx, by simp⟩
  | succ k ih =>
    intro x hx
    obtain ⟨y, hy, rfl⟩ := ih x hx
    obtain ⟨z, hz, rfl⟩ := hD y hy
    exact ⟨z, hz, by rw [smul_smul, ← pow_succ]⟩

/-- **Quillen, notebook 1971-12, p. 23.** Let `M` be an abelian group with endomorphisms `F`,
`V` such that `F V = V F = p ^ d` and `F = p ^ (d + r)`, `r > 0`. Then `M` is the direct sum of
`p ^ d M` and of the subgroup of elements killed by `p ^ d`. -/
theorem isCompl_range_ker (hFV : ∀ x, F (V x) = p ^ d • x) (hVF : ∀ x, V (F x) = p ^ d • x)
    (hF : ∀ x, F x = p ^ (d + r) • x) (hr : 0 < r) :
    IsCompl (nsmulAddMonoidHom (α := M) (p ^ d)).range
      (nsmulAddMonoidHom (α := M) (p ^ d)).ker := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨⟨y, rfl⟩, hx⟩
    simpa using nsmul_eq_zero_of_pow_nsmul hVF hF hr (d + d) y (by rw [pow_add, mul_smul]; exact hx)
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨t, ht, hx⟩ := exists_decomp hFV hF d x
    have hd : d ≤ d * r := Nat.le_mul_of_pos_right d hr
    rw [hx, add_comm]
    refine AddSubgroup.add_mem_sup ⟨p ^ (d * r - d) • (V^[d]) x, ?_⟩ ht
    simp only [nsmulAddMonoidHom_apply, smul_smul, ← pow_add]
    rw [show d + (d * r - d) = d * r by omega]

end Quillen.Notebook1971_12
