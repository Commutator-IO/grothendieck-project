import Mathlib

/-!
# Folder 42, Lemme 2

The modernised reading `transcripts/42/42.modern.tex` (manuscript pages 4–5)
states:

> **Lemme 2.** Let `A` be a Noetherian ring and `𝔭` a prime ideal of `A`. Then
> 1. there exists `f ∈ A - 𝔭` such that `A_f → A_𝔭` is injective;
> 2. if moreover `A → A_𝔭` is already injective, then `A_𝔮 → A_𝔭` is injective
>    for every prime ideal `𝔮 ⊇ 𝔭`.

Both are proved here as the reading states them, with no hypothesis added. What
this certifies is that the reading holds together, not that it is what the page
says (issue #26): that is for a reader with the leaf in front of them.

Two things the proof makes plain. Part 2 does not use the Noetherian hypothesis;
it holds for every commutative ring. Part 1 uses it only to make the kernel of
`A → A_𝔭` finitely generated — which is where the reading's first footnote bears:
the kernel is the set of elements killed by *some* element outside `𝔭`, not by
every one, and the proof takes one killer per generator.
-/

namespace Grothendieck.Folder42

open IsLocalization

variable {A : Type*} [CommRing A]

/-- A map out of a localisation `S = M⁻¹A`, induced by `g : A → P`, is injective
as soon as everything `g` kills is already killed in `S`. -/
theorem lift_injective {M : Submonoid A} {S : Type*} [CommRing S] [Algebra A S]
    [IsLocalization M S] {P : Type*} [CommRing P] {g : A →+* P}
    (hg : ∀ y : M, IsUnit (g y)) (h : ∀ x, g x = 0 → algebraMap A S x = 0) :
    Function.Injective (IsLocalization.lift (S := S) hg) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M z
  have hgx : g x = 0 := by
    have := congrArg (IsLocalization.lift (S := S) hg) e
    rw [map_mul, hz, zero_mul, IsLocalization.lift_eq] at this
    exact this.symm
  rw [h x hgx] at e
  exact (IsLocalization.map_units S s).mul_left_eq_zero.mp e

variable (p : Ideal A) [p.IsPrime]

/-- The map `A_f → A_𝔭`, for `f ∉ 𝔭`. -/
noncomputable def awayToAtPrime (f : A) (hf : f ∉ p) :
    Localization.Away f →+* Localization.AtPrime p :=
  IsLocalization.lift (M := Submonoid.powers f)
    (fun y => IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p)
      ⟨y, (Submonoid.powers_le.2 (show f ∈ p.primeCompl from hf)) y.2⟩)

/-- The map `A_𝔮 → A_𝔭`, for primes `𝔭 ⊆ 𝔮`. -/
noncomputable def atPrimeToAtPrime (q : Ideal A) [q.IsPrime] (hpq : p ≤ q) :
    Localization.AtPrime q →+* Localization.AtPrime p :=
  IsLocalization.lift (M := q.primeCompl)
    (fun y => IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p)
      ⟨y, fun h => y.2 (hpq h)⟩)

/-- **Lemme 2 (1).** Over a Noetherian ring, some `f ∉ 𝔭` makes `A_f → A_𝔭`
injective. -/
theorem lemme2_1 [IsNoetherianRing A] :
    ∃ (f : A) (hf : f ∉ p), Function.Injective (awayToAtPrime p f hf) := by
  classical
  -- `J`, the kernel of `A → A_𝔭`, is finitely generated.
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian
    (RingHom.ker (algebraMap A (Localization.AtPrime p))) : Submodule.FG _)
  -- Each generator is killed by some element outside `𝔭` …
  have kill : ∀ x ∈ t, ∃ s : p.primeCompl, (s : A) * x = 0 := fun x hx => by
    have : x ∈ RingHom.ker (algebraMap A (Localization.AtPrime p)) :=
      ht ▸ Submodule.subset_span hx
    exact (IsLocalization.map_eq_zero_iff p.primeCompl _ x).1 this
  choose! s hs using kill
  -- … and `f`, their product, is outside `𝔭` and kills all of `J`.
  let f : A := ∏ x ∈ t, (s x : A)
  have hf : f ∈ p.primeCompl := Submonoid.prod_mem _ fun x _ => (s x).2
  have hspan : ∀ y ∈ Submodule.span A (t : Set A), f * y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun x => (s x : A)) hx
      show (∏ x ∈ t, (s x : A)) * x = 0
      rw [hc, mul_comm (s x : A) c, mul_assoc, hs x hx, mul_zero]
    | zero => exact mul_zero f
    | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
    | smul c a _ ha => rw [smul_eq_mul, mul_left_comm, ha, mul_zero]
  have hJ : ∀ y, algebraMap A (Localization.AtPrime p) y = 0 → f * y = 0 :=
    fun y hy => hspan y (ht.symm ▸ hy)
  refine ⟨f, hf, lift_injective _ fun y hy => ?_⟩
  exact (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ y).2
    ⟨⟨f, Submonoid.mem_powers f⟩, hJ y hy⟩

/-- **Lemme 2 (2).** If `A → A_𝔭` is injective, so is `A_𝔮 → A_𝔭` for every
prime `𝔮 ⊇ 𝔭`. No Noetherian hypothesis is needed. -/
theorem lemme2_2 (hinj : Function.Injective (algebraMap A (Localization.AtPrime p)))
    (q : Ideal A) [q.IsPrime] (hpq : p ≤ q) :
    Function.Injective (atPrimeToAtPrime p q hpq) :=
  lift_injective _ fun x hx => by
    rw [hinj (hx.trans (map_zero _).symm), map_zero]

end Grothendieck.Folder42
