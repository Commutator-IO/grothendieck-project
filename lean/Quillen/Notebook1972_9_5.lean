import Mathlib

/-!
# Quillen, notebook 1972-9.5: `⋂ πⁿE` is divisible

Daniel Quillen's research notebook 1972-9.5 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201972/1972-9.5.pdf>).

* p. 3: if `π` acts injectively on `E` (a torsion-free module over a discrete valuation ring with
  uniformiser `π`), then `W = ⋂ₙ πⁿE` is `π`-divisible: every `x ∈ W` is `π y` with `y ∈ W`
  (`divisible_iInf`), and it contains every `π`-divisible subset (`mem_iInf_of_divisible`): the
  largest `π`-divisible part of `E`, a vector space over the fraction field.

The transversality sorites of p. 5 (`A + B = X` iff `X → X/A × X/B` is onto) is proved in
`Quillen.Notebook1972_11`.
-/

namespace Quillen.Notebook1972_9_5

/-- **p. 3.** If `π` acts injectively on `E` (`E` torsion-free over a DVR with uniformiser `π`),
then `⋂ₙ πⁿE` is `π`-divisible: each of its elements is `π y` with `y` in it. -/
theorem divisible_iInf {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E] {π : R}
    (hπ : Function.Injective (π • · : E → E)) {x : E} (hx : ∀ n : ℕ, ∃ e : E, π ^ n • e = x) :
    ∃ y, (∀ n : ℕ, ∃ e : E, π ^ n • e = y) ∧ π • y = x := by
  choose e he using hx
  have key : ∀ n, π ^ n • e (n + 1) = e 1 := fun n => hπ (by
    change π • π ^ n • e (n + 1) = π • e 1
    rw [smul_smul, ← pow_succ', he, ← he 1, pow_one])
  exact ⟨e 1, fun n => ⟨e (n + 1), key n⟩, by simpa using he 1⟩

/-- And it is the largest such: every `π`-divisible subset `D` (each element `π` times an element
of `D`) lies in `⋂ₙ πⁿE`. -/
theorem mem_iInf_of_divisible {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E] {π : R}
    {D : Set E} (hD : ∀ x ∈ D, ∃ y ∈ D, π • y = x) : ∀ x ∈ D, ∀ n : ℕ, ∃ e : E, π ^ n • e = x := by
  intro x hx n
  induction n generalizing x with
  | zero => exact ⟨x, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy, rfl⟩ := hD x hx
    obtain ⟨e, rfl⟩ := ih y hy
    exact ⟨e, by rw [pow_succ', mul_smul]⟩

end Quillen.Notebook1972_9_5
