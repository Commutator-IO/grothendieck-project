import Mathlib

/-!
# Quillen, notebook 1971-11, pp. 68–69: automorphisms of order `p` trivial on `Ω₁`

Daniel Quillen's research notebook 1971-11 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201971/1971-11.pdf>) opens, on
p. 68 (a run dated August 24, 1971, headed « p odd »), with a lemma used for the maximal normal
elementary abelian subgroups of a `p`-group on pp. 69–71. In our words: let `θ` be an automorphism
of an abelian `p`-group `B` with `θ ^ p = 1` that fixes every element of order `p`; then
`θ - 1` sends `B` into the elements of order dividing `p`, that is `p • (θ - 1) = 0`. His proof
(p. 69) passes to the dual group, writes `θ = 1 + N` and compares the terms of the binomial
expansion of `(1 + N) ^ p`; the inequality `p ≥ 3` is where the last term `N ^ p` becomes small
enough.

This file proves the lemma by induction on the order of an element, directly in `B`.

* `sub_one_nsmul_eq_zero_of_nsmul`: if `p ^ (k + 1) • b = 0` then `p ^ k • (θ b - b) = 0`
  (the endomorphism `θ - 1` lowers the exponent by one);
* `sum_apply`, `pow_apply_eq_sum`: the binomial expansion of `θ ^ n = (1 + (θ - 1)) ^ n`,
  evaluated at a point;
* `nsmul_sub_one_eq_zero`: the lemma, for an additive endomorphism `θ` of an abelian group in
  which every element is killed by a power of `p`, with `θ ^ p = 1` and `θ = 1` on the elements
  killed by `p`, and `p ≥ 3`. Neither finiteness nor bijectivity is assumed (bijectivity follows
  from `θ ^ p = 1`);
* `addEquiv_nsmul_sub_one_eq_zero`: the same statement for an automorphism `θ : B ≃+ B` whose
  `p`-th iterate is the identity, as on the page;
* `zmod8_neg`: for `p = 2` the lemma fails: on `ZMod 8`, `θ = -1` has order 2, fixes `0` and
  `4`, and `2 • (θ 1 - 1) = 4 ≠ 0`.
-/

namespace Quillen.Notebook1971_11

variable {B : Type*} [AddCommGroup B]

/-- If `θ` fixes the elements killed by `p`, then `θ - 1` lowers the exponent: an element killed
by `p ^ (k + 1)` is sent to an element killed by `p ^ k`. -/
theorem sub_one_nsmul_eq_zero_of_nsmul {p : ℕ} (θ : AddMonoid.End B)
    (h1 : ∀ b : B, p • b = 0 → θ b = b) {k : ℕ} {b : B} (hb : p ^ (k + 1) • b = 0) :
    p ^ k • ((θ - 1) b) = 0 := by
  change p ^ k • (θ b - b) = 0
  rw [nsmul_sub, ← map_nsmul θ, h1 _ (by rw [← mul_nsmul, ← pow_succ]; exact hb), sub_self]

/-- A finite sum of endomorphisms is evaluated term by term. -/
theorem sum_apply (s : Finset ℕ) (f : ℕ → AddMonoid.End B) (b : B) :
    (∑ i ∈ s, f i) b = ∑ i ∈ s, f i b :=
  AddMonoidHom.finsetSum_apply f s b

/-- The binomial expansion of `θ ^ p = (1 + δ) ^ p`, evaluated at `b`, with `δ = θ - 1`. -/
theorem pow_apply_eq_sum (θ : AddMonoid.End B) (n : ℕ) (b : B) :
    (θ ^ n) b = ∑ m ∈ Finset.range (n + 1), n.choose m • ((θ - 1) ^ m) b := by
  have h : θ = (θ - 1) + 1 := by abel
  conv_lhs => rw [h, (Commute.one_right (θ - 1)).add_pow]
  simp only [one_pow, mul_one]
  rw [sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  change ((θ - 1) ^ m) (((n.choose m : ℕ) : AddMonoid.End B) b) = _
  rw [AddMonoid.End.natCast_apply, map_nsmul]

/-- **Quillen, notebook 1971-11, p. 68.** Let `p ≥ 3` be a prime, `B` an abelian group in which
every element is killed by a power of `p`, and `θ` an additive endomorphism of `B` with
`θ ^ p = 1` that fixes the elements killed by `p`. Then `p • (θ b - b) = 0` for every `b`. -/
theorem nsmul_sub_one_eq_zero {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hB : ∀ b : B, ∃ k : ℕ, p ^ k • b = 0) (θ : AddMonoid.End B) (hθ : θ ^ p = 1)
    (h1 : ∀ b : B, p • b = 0 → θ b = b) (b : B) : p • (θ b - b) = 0 := by
  set δ : AddMonoid.End B := θ - 1 with hδ
  have hδb : ∀ c, δ c = θ c - c := fun c => rfl
  -- `δ` kills the elements killed by `p`.
  have hker : ∀ c : B, p • c = 0 → δ c = 0 := fun c hc => by rw [hδb, h1 c hc, sub_self]
  -- Induction on the exponent of `b`.
  obtain ⟨k, hk⟩ := hB b
  suffices H : ∀ k : ℕ, ∀ c : B, p ^ k • c = 0 → p • δ c = 0 from (hδb b) ▸ H k b hk
  intro k
  induction k with
  | zero => intro c hc; simp at hc; simp [hc]
  | succ k ih =>
    intro c hc
    -- `δ c` is killed by `p ^ k`, so `p • δ² c = 0`, hence `δ³ c = 0`.
    have h2 : p • (δ ^ 2) c = 0 := by
      rw [pow_two]
      exact ih _ (sub_one_nsmul_eq_zero_of_nsmul θ h1 hc)
    have h3 : ∀ m, 3 ≤ m → (δ ^ m) c = 0 := by
      intro m hm
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
      rw [show 3 + j = j + 1 + 2 by omega, pow_add, pow_succ]
      change (δ ^ j) (δ ((δ ^ 2) c)) = 0
      rw [hker _ h2, map_zero]
    have hge2 : ∀ m, 2 ≤ m → p • (δ ^ m) c = 0 := by
      intro m hm
      rcases Nat.lt_or_ge m 3 with h | h
      · rw [show m = 2 by omega]; exact h2
      · rw [h3 m h, smul_zero]
    -- The binomial expansion of `θ ^ p c = c`.
    have hexp := pow_apply_eq_sum θ p c
    rw [hθ, AddMonoid.End.coe_one, id_eq] at hexp
    rw [Finset.sum_eq_add (0 : ℕ) 1 (by norm_num)] at hexp
    · simp only [Nat.choose_zero_right, pow_zero, AddMonoid.End.coe_one, id_eq, one_smul,
        Nat.choose_one_right, pow_one] at hexp
      simpa using (congrArg (· - c) hexp).symm
    · intro m hm hm01
      have hm2 : 2 ≤ m := by omega
      have hmp : m ≤ p := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hm
      rcases Nat.lt_or_ge m p with hlt | hge
      · obtain ⟨q, hq⟩ := hp.dvd_choose_self (by omega) hlt
        rw [hq, mul_nsmul, hge2 m hm2, smul_zero]
      · rw [show m = p by omega, h3 p hp3, smul_zero]
    · intro h; simp at h
    · intro h; simp at h; omega

/-- **Quillen, notebook 1971-11, p. 68**, for an additive automorphism `θ : B ≃+ B` whose
`p`-th iterate is the identity, as on the page. -/
theorem addEquiv_nsmul_sub_one_eq_zero {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hB : ∀ b : B, ∃ k : ℕ, p ^ k • b = 0) (θ : B ≃+ B) (hθ : ∀ b, θ^[p] b = b)
    (h1 : ∀ b : B, p • b = 0 → θ b = b) (b : B) : p • (θ b - b) = 0 := by
  let φ : AddMonoid.End B := θ.toAddMonoidHom
  exact nsmul_sub_one_eq_zero hp hp3 hB φ (by ext c; rw [AddMonoid.End.coe_pow]; exact hθ c) h1 b

/-- For `p = 2` the lemma fails: on `ZMod 8`, negation has order 2, fixes the elements killed
by 2 (namely `0` and `4`), and `2 • (θ 1 - 1) = -4 ≠ 0`. -/
theorem zmod8_neg :
    (∀ b : ZMod 8, ∃ k : ℕ, 2 ^ k • b = 0) ∧
    (-(1 : AddMonoid.End (ZMod 8))) ^ 2 = 1 ∧
    (∀ b : ZMod 8, 2 • b = 0 → -b = b) ∧
    2 • ((-(1 : ZMod 8)) - 1) ≠ 0 := by
  refine ⟨fun b => ⟨3, ?_⟩, by ext x; change -(-x) = x; exact neg_neg x, ?_, by decide⟩
  · revert b; decide
  · decide

end Quillen.Notebook1971_11
