import Mathlib

/-!
# Folder 136, pages 19–31: the binomial lemma behind the « ombres »

The modernised reading `transcripts/136/136.modern.tex` (« Coefficients binomiaux
modulo `p` », pages 19 to 22, and « Le théorème sur `M ⊗_k S` », pages 26 to 34)
states, with `c_{a,b} = binom(a + b, a)`:

> **Théorème 1 (p. 22).** Let `E` be an abelian group, `N ∈ ℕ`, and `(xᵢ)` in `E`
> with `binom(j, i) (x_j − x_i) = 0` for `j > i ≥ N`. Then `xᵢ = x_N` for every
> `i ≥ N`.
>
> **Théorème (pp. 26–31).** Let `0 ≤ i ≤ N`, `M` an abelian group and `(ξ_k)_{k ≥ N}`
> in `M` with `c_{l,k} ξ_k = c_{l,k−i} ξ_{k+l}` for `k ≥ N`, `l ≥ 0`. There is a
> unique `ξ ∈ M` with `ξ_k = binom(k, i) ξ` for every `k ≥ N`.

Théorème 1 is the arithmetic core of finding `136-shadow-full-faithfulness` of
`src/content/findings.ts` (it gives Corollary 1: `ω_N : M ↦ M ⊗_k S^{+(N)}` is fully
faithful, a morphism being a family `u_k : M → M'` with `c_{k,j}(u_{k+j} − u_k) = 0`,
that is Théorème 1 in the group `M →+ M'`). The second theorem is the degree-`i`
form, `M T^{(i)} ≃ Hom^i(τ_{N−i} S, M ⊗_k S)`, written on coefficients. Proving them
says only that the claims hold as stated; whether they stand in the literature is a
separate question.

What is formalised.

* The second theorem, for every `i` (the hypothesis `i ≤ N` is not used)
  (`binomial_shadow_existsUnique`). The proof is not the page's: no localisation and
  no `p`-adic digit shift. With `K = p^r − 1` above `k` and `k'`, every `binom(K, ·)`
  is prime to `p` (`not_dvd_choose_pow_sub_one`, the « aucune retenue » of p. 31),
  and the relations from `k` and `k'` up to `K`, with the identity
  `binom(k+l, l) binom(k, i) = binom(k+l, i) binom(k+l−i, l)` (`choose_add_mul_choose`),
  give that `binom(k, i) ξ_{k'} − binom(k', i) ξ_k` is killed by an integer prime to
  `p`; for every `p` this forces it to vanish (`eq_zero_of_forall_prime_smul`, through
  the additive order). The `binom(k, i)`, `k ≥ N`, generate the unit ideal of `ℤ`
  (`span_choose_eq_top`), and a Bézout combination `∑ mₐ binom(kₐ, i) = 1` defines
  `ξ = ∑ mₐ ξ_{kₐ}` and gives its uniqueness, as on page 27.
* Théorème 1 (`binomial_constant`) is the case `i = 0`; the family of additive maps
  of Corollary 1 is its instance in `M →+ M'` (`hom_family_constant`).

Not formalised: the full faithfulness of `ω_N` and the isomorphism
`M ⊗_k S → φ_N τ_N (M ⊗_k S)` over the divided-power algebra `k{T}` as statements
about graded modules; Lemma 2 of page 21 (the `ℤ_(p)`-local form with few indices).
-/

namespace Grothendieck.Folder136

/-- No carry is possible: `p` divides no `binom(p^r − 1, b)`, `b ≤ p^r − 1`
(p. 31, « `μ + ν = p^r − 1` entraîne `c_{μ,ν} ≢ 0` »). In `ZMod p` the value is
`(-1)^b`. -/
theorem choose_pow_sub_one_zmod {p : ℕ} (hp : p.Prime) (r : ℕ) :
    ∀ b, b ≤ p ^ r - 1 → ((p ^ r - 1).choose b : ZMod p) = (-1) ^ b := by
  have := Fact.mk hp
  have hpos : 0 < p ^ r := pow_pos hp.pos r
  intro b
  induction b with
  | zero => simp
  | succ b ih =>
    intro hb
    have hdvd : p ∣ (p ^ r).choose (b + 1) :=
      hp.dvd_choose_pow (by omega) (by omega)
    have hpascal : (p ^ r).choose (b + 1) =
        (p ^ r - 1).choose b + (p ^ r - 1).choose (b + 1) := by
      conv_lhs => rw [show p ^ r = (p ^ r - 1) + 1 by omega]
      exact Nat.choose_succ_succ _ _
    have h0 : ((p ^ r).choose (b + 1) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    rw [hpascal, Nat.cast_add, ih (by omega)] at h0
    rw [pow_succ]
    linear_combination h0

theorem not_dvd_choose_pow_sub_one {p : ℕ} (hp : p.Prime) (r b : ℕ)
    (hb : b ≤ p ^ r - 1) : ¬ p ∣ (p ^ r - 1).choose b := by
  have := Fact.mk hp
  intro h
  have h1 := choose_pow_sub_one_zmod hp r b hb
  rw [(ZMod.natCast_eq_zero_iff _ _).2 h] at h1
  exact (pow_ne_zero b (neg_ne_zero.2 one_ne_zero) h1.symm).elim

/-- `binom(k+l, l) binom(k, i) = binom(k+l, i) binom(k+l−i, l)` for all `k, l, i`. -/
theorem choose_add_mul_choose (k l i : ℕ) :
    (k + l).choose l * k.choose i = (k + l).choose i * (k + l - i).choose l := by
  rcases le_or_gt i k with hik | hik
  · have h := Nat.choose_mul (n := k + l) hik
    rw [Nat.choose_symm_add, Nat.choose_symm_of_eq_add (show k + l - i = (k - i) + l by omega)]
      at h
    exact h
  · rw [Nat.choose_eq_zero_of_lt hik, mul_zero]
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp [Nat.choose_eq_zero_of_lt hik]
    · rw [Nat.choose_eq_zero_of_lt (show k + l - i < l by omega), mul_zero]

/-- An element killed, for every prime `p`, by an integer prime to `p` is zero. -/
theorem eq_zero_of_forall_prime_smul {A : Type*} [AddCommGroup A] (z : A)
    (h : ∀ p : ℕ, p.Prime → ∃ c : ℕ, ¬ p ∣ c ∧ c • z = 0) : z = 0 := by
  by_contra hz
  have h1 : addOrderOf z ≠ 1 := by rwa [Ne, AddMonoid.addOrderOf_eq_one_iff]
  obtain ⟨c, hc, hcz⟩ := h _ (Nat.minFac_prime h1)
  exact hc ((Nat.minFac_dvd _).trans (addOrderOf_dvd_of_nsmul_eq_zero hcz))

/-- For every prime `p` some `K = p^r − 1 ≥ m` exists. -/
theorem exists_pow_sub_one_ge {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ∃ r, m ≤ p ^ r - 1 := by
  refine ⟨m + 1, ?_⟩
  have := Nat.lt_pow_self (n := m + 1) hp.one_lt
  omega

/-- The cross relation `binom(k, i) ξ_{k'} = binom(k', i) ξ_k` for `k, k' ≥ N`. -/
theorem cross_relation {A : Type*} [AddCommGroup A] (ξ : ℕ → A) (N i : ℕ)
    (h : ∀ k l, N ≤ k → (k + l).choose l • ξ k = (k + l - i).choose l • ξ (k + l))
    {k k' : ℕ} (hk : N ≤ k) (hk' : N ≤ k') :
    k.choose i • ξ k' = k'.choose i • ξ k := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_prime_smul
  intro p hp
  obtain ⟨r, hr⟩ := exists_pow_sub_one_ge hp (k + k')
  set K := p ^ r - 1 with hK
  have e : k + (K - k) = K := by omega
  have e' : k' + (K - k') = K := by omega
  have h1 := h k (K - k) hk
  have h2 := h k' (K - k') hk'
  rw [e] at h1
  rw [e'] at h2
  have i1 := choose_add_mul_choose k (K - k) i
  have i2 := choose_add_mul_choose k' (K - k') i
  rw [e] at i1
  rw [e'] at i2
  set u := K.choose (K - k)
  set u' := K.choose (K - k')
  set a := (K - i).choose (K - k)
  set a' := (K - i).choose (K - k')
  refine ⟨u * u', fun hd => ?_, ?_⟩
  · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
    · exact not_dvd_choose_pow_sub_one hp r _ (by omega) hd
    · exact not_dvd_choose_pow_sub_one hp r _ (by omega) hd
  · rw [smul_sub, smul_smul, smul_smul,
      show u * u' * k.choose i = (u * k.choose i) * u' by ring,
      show u * u' * k'.choose i = (u' * k'.choose i) * u by ring,
      mul_smul, mul_smul (u' * _), h1, h2, i1, i2, smul_smul, smul_smul]
    rw [show K.choose i * a * a' = K.choose i * a' * a by ring, sub_self]

/-- The binomial coefficients `binom(N + n, i)`, `n ∈ ℕ`, generate the unit ideal
of `ℤ`: for each `p`, `binom(p^r − 1, i)` with `p^r − 1 ≥ N + i` is prime to `p`. -/
theorem span_choose_eq_top (N i : ℕ) :
    Ideal.span (Set.range fun n : ℕ => ((N + n).choose i : ℤ)) = ⊤ := by
  set I := Ideal.span (Set.range fun n : ℕ => ((N + n).choose i : ℤ))
  obtain ⟨g, hg⟩ := (inferInstance : Submodule.IsPrincipal I)
  by_cases h1 : g.natAbs = 1
  · rw [hg, Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]
    exact Int.isUnit_iff_natAbs_eq.2 h1
  · exfalso
    set p := Nat.minFac g.natAbs with hpdef
    have hp : p.Prime := Nat.minFac_prime h1
    obtain ⟨r, hr⟩ := exists_pow_sub_one_ge hp (N + i)
    have hmem : ((N + (p ^ r - 1 - N)).choose i : ℤ) ∈ I :=
      Ideal.subset_span ⟨_, rfl⟩
    rw [hg, Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hmem
    have hdvd : (p : ℤ) ∣ g :=
      Int.natCast_dvd.2 (Nat.minFac_dvd _)
    have := Int.natCast_dvd_natCast.1 (hdvd.trans hmem)
    rw [show N + (p ^ r - 1 - N) = p ^ r - 1 by omega] at this
    exact not_dvd_choose_pow_sub_one hp r i (by omega) this

/-- **The theorem of pages 26–31**, for every `i`: if
`c_{l,k} ξ_k = c_{l,k−i} ξ_{k+l}` for `k ≥ N`, `l ≥ 0`, with `c_{a,b} = binom(a+b, a)`,
there is a unique `ξ` with `ξ_k = binom(k, i) ξ` for every `k ≥ N`. -/
theorem binomial_shadow_existsUnique {A : Type*} [AddCommGroup A] (ξ : ℕ → A) (N i : ℕ)
    (h : ∀ k l, N ≤ k → (k + l).choose l • ξ k = (k + l - i).choose l • ξ (k + l)) :
    ∃! x : A, ∀ k, N ≤ k → ξ k = k.choose i • x := by
  have h1 : (1 : ℤ) ∈ Submodule.span ℤ (Set.range fun n : ℕ => ((N + n).choose i : ℤ)) := by
    have := span_choose_eq_top N i
    rw [Ideal.span, Submodule.eq_top_iff'] at this
    exact this 1
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h1
  simp only [smul_eq_mul] at hc
  -- `ξ = ∑ mₐ ξ_{N+a}` and, for any `y`, `y = ∑ mₐ binom(N+a, i) y`
  have hone : ∀ y : A, (c.sum fun n m => (m * ((N + n).choose i : ℤ)) • y) = y := by
    intro y
    unfold Finsupp.sum
    rw [← Finset.sum_smul]
    unfold Finsupp.sum at hc
    rw [hc, one_smul]
  refine ⟨c.sum fun n m => m • ξ (N + n), ?_, ?_⟩
  · intro k hk
    rw [← natCast_zsmul, Finsupp.smul_sum]
    conv_lhs => rw [← hone (ξ k)]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only
    rw [mul_smul, natCast_zsmul,
      ← cross_relation ξ N i h hk (show N ≤ N + n by omega), ← natCast_zsmul]
    exact smul_comm _ _ _
  · intro y hy
    rw [← hone y]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only
    rw [mul_smul, natCast_zsmul, ← hy (N + n) (by omega)]

/-- **Théorème 1 (p. 22).** If `binom(j, i)(x_j − x_i) = 0` for all `j > i ≥ N` in an
abelian group, then `x_j = x_N` for every `j ≥ N`. -/
theorem binomial_constant {A : Type*} [AddCommGroup A] (x : ℕ → A) (N : ℕ)
    (h : ∀ i j, N ≤ i → i < j → j.choose i • (x j - x i) = 0) :
    ∀ j, N ≤ j → x j = x N := by
  have h' : ∀ k l, N ≤ k → (k + l).choose l • x k = (k + l - 0).choose l • x (k + l) := by
    intro k l hk
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp
    · have := h k (k + l) hk (by omega)
      rw [Nat.choose_symm_add, smul_sub, sub_eq_zero] at this
      rw [Nat.sub_zero, this]
  obtain ⟨y, hy, -⟩ := binomial_shadow_existsUnique x N 0 h'
  intro j hj
  rw [hy j hj, hy N le_rfl, Nat.choose_zero_right, Nat.choose_zero_right]

/-- Corollary 1 a) on coefficients: a family of additive maps `u_k : M → M'` with
`binom(j, k)(u_j − u_k) = 0` for `j > k ≥ N` is constant from `N` on. -/
theorem hom_family_constant {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    (u : ℕ → M →+ M') (N : ℕ)
    (h : ∀ i j, N ≤ i → i < j → j.choose i • (u j - u i) = 0) :
    ∀ j, N ≤ j → u j = u N :=
  binomial_constant u N h

end Grothendieck.Folder136
