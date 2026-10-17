import Mathlib

/-!
# Folder 29, page 120: the determinant criterion on tame inertia

The modernised reading `transcripts/29/29.modern.tex` (« Comportement fonctoriel des
groupes d'inertie », number 4, page 120) draws, for a morphism of strictly local regular
schemes with normal crossings divisors whose branches are indexed by `C` and `C'`, the
square in which the map on tame inertia is the map

  `N : ∏_{ℓ ≠ p} ℤ_ℓ(1)^C → ∏_{ℓ ≠ p} ℤ_ℓ(1)^{C'}`

of the integer matrix of multiplicities `(n_{c,c'})`, and states the criterion: `N` is an
isomorphism iff `card C = card C'` and the ordinary integer `det N` is `± p^r`, `p` the
characteristic exponent of the residue fields.

This is the criterion of finding `29-inertia-matrix-determinant` of
`src/content/findings.ts`. That the map on inertia is `N` (the Kummer computation of the
page) is not formalised: mathlib has no tame inertia of regular schemes. What is proved is
the criterion itself, for any integer matrix, `ℤ_ℓ(1)` being free of rank one over `ℤ_ℓ`.

* `inertiaMap N ℓ`: the map `ℤ_ℓ^C → ℤ_ℓ^{C'}` of an integer matrix `N` (rows `C'`,
  columns `C`).
* `card_eq_of_bijective`: if it is bijective for one `ℓ`, then `card C = card C'`.
* `bijective_iff_not_dvd_det`: for a square integer matrix, bijective over `ℤ_ℓ` iff
  `ℓ ∤ det`.
* `forall_not_dvd_iff`: an integer is prime to every prime `ℓ ≠ p` iff it is `± p^k`
  (`p` prime, or `p = 1`, the characteristic exponent in characteristic zero).
* `criterion_of_equiv`: once `C'` and `C` are matched by a bijection `e`, `N` is bijective
  over `ℤ_ℓ` for every `ℓ ≠ p` iff `det (N.submatrix id e) = ± p^k`; the choice of `e`
  changes the determinant only by a sign.
* `criterion` (the page's criterion): `N` is bijective over `ℤ_ℓ` for every prime `ℓ ≠ p`
  iff `card C = card C'` and the determinant is `± p^k`.
-/

open Matrix

namespace Folder29

variable {C C' : Type*} [Fintype C] [Fintype C']

/-- The map `ℤ_ℓ^C → ℤ_ℓ^{C'}` of an integer matrix with rows indexed by `C'` and columns
by `C`. -/
noncomputable def inertiaMap (N : Matrix C' C ℤ) (ℓ : ℕ) [Fact ℓ.Prime] :
    (C → ℤ_[ℓ]) → (C' → ℤ_[ℓ]) :=
  (N.map (Int.cast : ℤ → ℤ_[ℓ])).mulVec

/-- A matrix bijective over `ℤ_ℓ` for one `ℓ` is square. -/
theorem card_eq_of_bijective (N : Matrix C' C ℤ) (ℓ : ℕ) [Fact ℓ.Prime]
    (h : Function.Bijective (inertiaMap N ℓ)) : Fintype.card C = Fintype.card C' := by
  let f := LinearEquiv.ofBijective (N.map (Int.cast : ℤ → ℤ_[ℓ])).mulVecLin h
  simpa using f.finrank_eq

/-- A square integer matrix is bijective over `ℤ_ℓ` iff `ℓ` does not divide its
determinant. -/
theorem bijective_iff_not_dvd_det [DecidableEq C'] (M : Matrix C' C' ℤ) (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Bijective (inertiaMap M ℓ) ↔ ¬ (ℓ : ℤ) ∣ M.det := by
  have hdet : (M.map (Int.cast : ℤ → ℤ_[ℓ])).det = (M.det : ℤ_[ℓ]) :=
    ((Int.castRingHom ℤ_[ℓ]).map_det M).symm
  have key : IsUnit (M.map (Int.cast : ℤ → ℤ_[ℓ])) ↔ ¬ (ℓ : ℤ) ∣ M.det := by
    rw [isUnit_iff_isUnit_det, hdet, PadicInt.isUnit_iff, ← PadicInt.norm_intCast_lt_one_iff]
    exact ⟨fun h => h.symm ▸ lt_irrefl 1, fun h => le_antisymm (PadicInt.norm_le_one _)
      (not_lt.1 h)⟩
  refine ⟨fun h => key.1 (mulVec_surjective_iff_isUnit.1 h.2), fun h => ?_⟩
  have hu := key.2 h
  refine ⟨fun v w hvw => ?_, mulVec_surjective_iff_isUnit.2 hu⟩
  have := congrArg ((M.map (Int.cast : ℤ → ℤ_[ℓ]))⁻¹).mulVec hvw
  simpa [inertiaMap, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hu)]
    using this

/-- An integer is prime to every prime `ℓ ≠ p` iff it is `± p^k`, for `p` prime or
`p = 1`. -/
theorem forall_not_dvd_iff {p : ℕ} (hp : p = 1 ∨ p.Prime) (d : ℤ) :
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ¬ (ℓ : ℤ) ∣ d) ↔ ∃ k : ℕ, d = p ^ k ∨ d = -(p ^ k : ℤ) := by
  constructor
  · intro h
    obtain ⟨ℓ, hℓp, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
    have hd : d ≠ 0 := fun hd => h ℓ hℓ (by omega) (hd ▸ dvd_zero _)
    have hn : d.natAbs = p ^ d.natAbs.primeFactorsList.length := by
      rcases hp with rfl | hp
      · rw [one_pow, Nat.eq_one_iff_not_exists_prime_dvd]
        exact fun q hq hqd => h q hq hq.one_lt.ne' (Int.natCast_dvd.2 hqd)
      · refine Nat.eq_prime_pow_of_unique_prime_dvd (Int.natAbs_ne_zero.2 hd) fun {q} hq hqd => ?_
        by_contra hqp
        exact h q hq hqp (Int.natCast_dvd.2 hqd)
    generalize d.natAbs.primeFactorsList.length = k at hn
    have hn' : (d.natAbs : ℤ) = (p : ℤ) ^ k := by exact_mod_cast hn
    refine ⟨k, ?_⟩
    rcases Int.natAbs_eq d with h' | h' <;> rw [h', hn'] <;> simp
  · rintro ⟨k, hk⟩ ℓ hℓ hℓp hdvd
    have : ℓ ∣ p ^ k := by
      rcases hk with rfl | rfl <;> simpa [← Int.natCast_dvd_natCast] using hdvd
    rcases hp with rfl | hp
    · exact hℓ.one_lt.ne' (Nat.dvd_one.1 (by simpa using this))
    · exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow this))

/-- Reindexing the columns by a bijection does not change bijectivity. -/
theorem bijective_submatrix_iff (N : Matrix C' C ℤ) (e : C' ≃ C) (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Bijective (inertiaMap (N.submatrix id e) ℓ) ↔
      Function.Bijective (inertiaMap N ℓ) := by
  have : inertiaMap (N.submatrix id e) ℓ = inertiaMap N ℓ ∘ (· ∘ e.symm) := by
    ext v
    simp [inertiaMap, ← submatrix_map, submatrix_mulVec_equiv]
  rw [this, Function.Bijective.of_comp_iff]
  exact (e.arrowCongr (Equiv.refl ℤ_[ℓ])).bijective

/-- The criterion once `C'` and `C` are matched by `e`. -/
theorem criterion_of_equiv [DecidableEq C'] {p : ℕ} (hp : p = 1 ∨ p.Prime) (N : Matrix C' C ℤ)
    (e : C' ≃ C) :
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → Function.Bijective (inertiaMap N ℓ)) ↔
      ∃ k : ℕ, (N.submatrix id e).det = p ^ k ∨
        (N.submatrix id e).det = -(p ^ k : ℤ) := by
  rw [← forall_not_dvd_iff hp]
  refine ⟨fun h ℓ hℓ hℓp => ?_, fun h ℓ _ hℓp => ?_⟩
  · have := Fact.mk hℓ
    exact (bijective_iff_not_dvd_det _ ℓ).1 ((bijective_submatrix_iff N e ℓ).2 (h ℓ hℓp))
  · exact (bijective_submatrix_iff N e ℓ).1
      ((bijective_iff_not_dvd_det _ ℓ).2 (h ℓ Fact.out hℓp))

/-- **The criterion of page 120.** The integer matrix `N` is bijective over `ℤ_ℓ` for every
prime `ℓ ≠ p` iff `card C = card C'` and, the columns being matched with the rows by some
bijection, `det N = ± p^k`. -/
theorem criterion [DecidableEq C'] {p : ℕ} (hp : p = 1 ∨ p.Prime) (N : Matrix C' C ℤ) :
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → Function.Bijective (inertiaMap N ℓ)) ↔
      Fintype.card C = Fintype.card C' ∧ ∃ e : C' ≃ C, ∃ k : ℕ,
        (N.submatrix id e).det = p ^ k ∨ (N.submatrix id e).det = -(p ^ k : ℤ) := by
  constructor
  · intro h
    obtain ⟨ℓ, hℓp, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
    have := Fact.mk hℓ
    have hc := card_eq_of_bijective N ℓ (h ℓ (by omega))
    let e : C' ≃ C := Fintype.equivOfCardEq hc.symm
    exact ⟨hc, e, (criterion_of_equiv hp N e).1 h⟩
  · rintro ⟨-, e, he⟩
    exact (criterion_of_equiv hp N e).2 he

end Folder29
