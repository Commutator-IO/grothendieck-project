import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Folder 39, the formal preparation theorem (pages 18–19): the adic and discrete cases

The modernised reading `transcripts/39/39.modern.tex` (manuscript pages 18–19)
states:

> **Théorème** (« de préparation “formel” »). Soit `A` un anneau linéairement
> topologisé, séparé et complet, `Z` une indéterminée,
> `F = ∑ aᵢ Zⁱ ∈ A[[Z]]`, et `N ∈ ℕ` tel que (i) `aᵢ` est topologiquement
> nilpotent pour `0 ⩽ i ⩽ N-1` ; (ii) `a_N` est inversible. Alors `F` est un
> élément régulier de `A[[Z]]`, et … tout `G ∈ A[[Z]]` s'écrit de façon unique
> `G = QF + ∑_{0 ⩽ i ⩽ N-1} bᵢ Zⁱ`, `Q ∈ A[[Z]]`, `bᵢ ∈ A`.
>
> *Démonstration.* `A` est limite projective de ses quotients discrets `A/I` …
> on peut supposer `A` discret. Alors (i) signifie que `a₀, …, a_{N-1}` sont
> nilpotents. Soit `𝔪` l'idéal qu'ils engendrent : il est de type fini et
> engendré par des nilpotents, donc nilpotent. …

**This is a partial formalisation.** What is proved:

* `preparation_adique` — the theorem for `A` complete and separated for an
  `I`-adic topology, with `aᵢ ∈ I` for `i < N` and `a_N` a unit (in the `I`-adic
  topology « topologiquement nilpotent » means `aᵢ ∈ √I`, slightly weaker than
  `aᵢ ∈ I`; that gap is not closed here): `F` is regular,
  and every `G` is uniquely `QF + r` with `r` a polynomial of degree `< N`
  (which is `∑_{i<N} bᵢ Zⁱ`). This is a short application of mathlib's
  Weierstrass division (`PowerSeries.IsWeierstrassDivisorAt`), once one checks
  that the order of `F` modulo `I` is exactly `N`.
* `preparation_discrete` — the case the proof reduces to: `A` any commutative
  ring, `a₀, …, a_{N-1}` nilpotent, `a_N` a unit. As the reading says, the ideal
  `𝔪` they generate is nilpotent (`ideal_nilpotent`), so `A` is `𝔪`-adically
  complete (`isAdicComplete_of_nilpotent`) and the adic case applies.

Not formalised: the general linearly topologised case, i.e. the passage from
the discrete quotients `A/J` back to `A = lim A/J`. mathlib has the vocabulary
(`IsLinearTopology`, `IsTopologicallyNilpotent`) but not the identification of
`A[[Z]]` with `lim (A/J)[[Z]]` that the gluing needs; building it is beyond the
scope of a check. The rest of the folder (classes of formal functions and their
axioms, pages 2–16) is not formalised either.

**What the formalisation finds.** Nothing false, and the discrete step is exactly
as the reading gives it: finitely many nilpotents generate a nilpotent ideal,
and a ring is complete for a nilpotent ideal. The formalisation confirms that
the hypotheses are used only as stated — (ii) is the unit condition mathlib calls
a Weierstrass divisor, and (i) is what makes the order of `F` modulo the ideal
equal to `N`. In the adic form no finiteness of the ideal is needed (the reading
uses « de type fini » only to get `𝔪ʲA[[Z]] = 𝔪ʲ[[Z]]` inside its own proof).

What this certifies is that the reading holds together at this point, not that
it is what the pages say (issue #26).
-/

namespace Grothendieck.Folder39

open PowerSeries Polynomial

variable {A : Type*} [CommRing A]

/-- A ring is complete and separated for a nilpotent ideal. -/
theorem isAdicComplete_of_nilpotent {I : Ideal A} (hI : IsNilpotent I) : IsAdicComplete I A := by
  obtain ⟨k, hk⟩ := hI
  have hk' : ∀ n, k ≤ n → (I ^ n • ⊤ : Submodule A A) = ⊥ := fun n hn => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, eq_bot_iff, ← Ideal.zero_eq_bot, ← hk]
    exact Ideal.pow_le_pow_right hn
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ⟨f k, fun n => ?_⟩ }
  · have := hx k
    rw [hk' k le_rfl, SModEq.zero, Submodule.mem_bot] at this
    exact this
  · rcases le_total n k with h | h
    · exact hf h
    · have := hf h
      rw [hk' k le_rfl, SModEq.bot] at this
      rw [← this]

/-- **Formal preparation, adic case.** `A` complete and separated for the
`I`-adic topology, `aᵢ ∈ I` for `i < N`, `a_N` a unit: `F` is regular, and every
`G` is uniquely `QF + r` with `deg r < N`. -/
theorem preparation_adique (I : Ideal A) [IsAdicComplete I A] (F : A⟦X⟧) (N : ℕ)
    (h1 : ∀ i < N, coeff i F ∈ I) (h2 : IsUnit (coeff N F)) :
    (∀ H : A⟦X⟧, F * H = 0 → H = 0) ∧
      ∀ G : A⟦X⟧, ∃! qr : A⟦X⟧ × A[X], qr.2.degree < N ∧ G = qr.1 * F + qr.2 := by
  rcases eq_or_ne I ⊤ with rfl | hI
  · -- `A` is the zero ring.
    have := ‹IsAdicComplete ⊤ A›.subsingleton
    exact ⟨fun H _ => Subsingleton.elim _ _, fun G =>
      ⟨(0, 0), ⟨by simp, Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩⟩
  have := Ideal.Quotient.nontrivial_iff.2 hI
  -- The order of `F` modulo `I` is `N`.
  have hord : (F.map (Ideal.Quotient.mk I)).order.toNat = N := by
    have : (F.map (Ideal.Quotient.mk I)).order = N := by
      rw [PowerSeries.order_eq_nat]
      refine ⟨?_, fun i hi => ?_⟩
      · rw [PowerSeries.coeff_map]
        exact (h2.map _).ne_zero
      · rw [PowerSeries.coeff_map, Ideal.Quotient.eq_zero_iff_mem]
        exact h1 i hi
    rw [this, ENat.toNat_natCast]
  have H : F.IsWeierstrassDivisorAt I := by
    rw [IsWeierstrassDivisorAt, hord]
    exact h2
  refine ⟨fun Q hQ => ?_, fun G => ?_⟩
  · have hdeg : (0 : A[X]).degree < ((F.map (Ideal.Quotient.mk I)).order.toNat : WithBot ℕ) := by
      rw [Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    exact (H.eq_zero_of_mul_eq hdeg (by rw [hQ, Polynomial.coe_zero])).1
  · have hdiv := H.isWeierstrassDivisionAt_div_mod G
    have hdeg := hdiv.degree_lt
    rw [hord] at hdeg
    refine ⟨(H.div G, H.mod G), ⟨hdeg, ?_⟩, ?_⟩
    · show G = H.div G * F + ↑(H.mod G)
      rw [mul_comm]
      exact hdiv.eq_mul_add
    rintro ⟨q, r⟩ ⟨hr, hG⟩
    simp only at hr hG
    have hr' : r.degree < ((F.map (Ideal.Quotient.mk I)).order.toNat : WithBot ℕ) := by
      rw [hord]; exact hr
    have hmod : (H.mod G).degree <
        ((F.map (Ideal.Quotient.mk I)).order.toNat : WithBot ℕ) := by
      rw [hord]; exact hdeg
    have heq : F * q + ↑r = F * H.div G + ↑(H.mod G) := by
      rw [mul_comm F q, ← hG]
      exact hdiv.eq_mul_add
    have := H.eq_of_mul_add_eq_mul_add hr' hmod heq
    exact Prod.ext this.1 this.2

/-- « il est de type fini et engendré par des nilpotents, donc nilpotent ». -/
theorem ideal_nilpotent (F : A⟦X⟧) (N : ℕ) (h1 : ∀ i < N, IsNilpotent (coeff i F)) :
    IsNilpotent (Ideal.span (Set.range fun i : Fin N => coeff (i : ℕ) F)) := by
  classical
  rw [(Ideal.FG.isNilpotent_iff_le_nilradical
    ⟨Finset.univ.image fun i : Fin N => coeff (i : ℕ) F, by simp⟩), Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact h1 i i.2

/-- **Formal preparation, discrete case.** Over any commutative ring, if
`a₀, …, a_{N-1}` are nilpotent and `a_N` is a unit, `F` is regular and every `G`
is uniquely `QF + r` with `deg r < N`. -/
theorem preparation_discrete (F : A⟦X⟧) (N : ℕ) (h1 : ∀ i < N, IsNilpotent (coeff i F))
    (h2 : IsUnit (coeff N F)) :
    (∀ H : A⟦X⟧, F * H = 0 → H = 0) ∧
      ∀ G : A⟦X⟧, ∃! qr : A⟦X⟧ × A[X], qr.2.degree < N ∧ G = qr.1 * F + qr.2 := by
  have := isAdicComplete_of_nilpotent (ideal_nilpotent F N h1)
  exact preparation_adique (Ideal.span (Set.range fun i : Fin N => coeff (i : ℕ) F)) F N
    (fun i hi => Ideal.subset_span ⟨⟨i, hi⟩, rfl⟩) h2

end Grothendieck.Folder39
