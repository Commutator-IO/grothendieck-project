import Mathlib

/-!
# Quillen, notebook 1971-3, pp. 32–34: the swindle that makes a compactly supported homeomorphism a commutator

Daniel Quillen's research notebook 1971-3 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201971/1971-3.pdf>) starts, on
p. 32, to read Mather's theorem that the group `G` of compactly supported homeomorphisms of
`ℝⁿ` is acyclic. To see that `G` is perfect, he takes `g` supported in a ball `B₀`, an element
`z` moving `B₀` to `B₁`, `B₁` to `B₂`, … (balls shrinking to a point), `σ(x) = z x z⁻¹`, and the
convergent infinite product `T = σ(g) σ²(g) ⋯`. Then `T = σ(g T)`, and the page concludes that
`g` is a commutator, with the formula `g = T⁻¹ z⁻¹ T z`.

The topology only serves to build `T`; once `T = z (g T) z⁻¹` holds the conclusion is group
theory, proved here in any group:

* `eq_commutator`: from `T = z (g T) z⁻¹`, `g = ⁅z⁻¹, T⁆ = z⁻¹ T z T⁻¹`, so `g` is a commutator
  (`mem_commutator`);
* `page_formula_eq`: the page's `T⁻¹ z⁻¹ T z` is `T⁻¹ g T`, the conjugate of `g` by `T`, which is
  also a commutator but equals `g` only when `g` commutes with `T`;
* `page_formula_ne`: an example (in the symmetric group on three letters) with
  `T = z (g T) z⁻¹` and `T⁻¹ z⁻¹ T z ≠ g`. The conclusion of the page stands; its formula is to be
  read up to that conjugation.

On p. 34 he asks whether the same holds for homology, and records the abelian case as a
question of the form « `φ ∘ σ = φ` for an inner `σ` ». `hom_eq_one` is the abstract form: if
`σ` is an endomorphism of `G` such that `x ↦ x σ(x)⁻¹` is onto, then every homomorphism to an
abelian group that is invariant under `σ` is trivial.
-/

namespace Quillen.Notebook1971_3

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **Quillen, notebook 1971-3, p. 32 (corrected formula).** If `T = z (g T) z⁻¹`, then
`g = ⁅z⁻¹, T⁆`. -/
theorem conj_eq {g z T : G} (hT : T = z * (g * T) * z⁻¹) : z⁻¹ * T * z = g * T := by
  nth_rewrite 1 [hT]
  group

theorem eq_commutator {g z T : G} (hT : T = z * (g * T) * z⁻¹) : g = ⁅z⁻¹, T⁆ := by
  rw [commutatorElement_def, inv_inv, conj_eq hT]
  group

/-- **Quillen, notebook 1971-3, pp. 32–33.** If `T = z (g T) z⁻¹`, then `g` is a commutator. -/
theorem mem_commutator {g z T : G} (hT : T = z * (g * T) * z⁻¹) : g ∈ commutator G := by
  rw [eq_commutator hT]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The formula of the page, `T⁻¹ z⁻¹ T z`, is the conjugate `T⁻¹ g T`. -/
theorem page_formula_eq {g z T : G} (hT : T = z * (g * T) * z⁻¹) :
    T⁻¹ * z⁻¹ * T * z = T⁻¹ * g * T := by
  rw [mul_assoc T⁻¹ z⁻¹ T, mul_assoc, conj_eq hT, mul_assoc]

/-- The formula of the page is `g` exactly when `g` commutes with `T`. -/
theorem page_formula_eq_iff {g z T : G} (hT : T = z * (g * T) * z⁻¹) :
    T⁻¹ * z⁻¹ * T * z = g ↔ Commute g T := by
  rw [page_formula_eq hT, Commute, SemiconjBy, mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]

/-- **The formula of the page does not hold in general**: in `S₃`, with `z = (1 2)`,
`T = (0 1)` and `g = z⁻¹ T z T⁻¹`, one has `T = z (g T) z⁻¹` but `T⁻¹ z⁻¹ T z ≠ g`. -/
theorem page_formula_ne :
    ∃ g z T : Equiv.Perm (Fin 3), T = z * (g * T) * z⁻¹ ∧ T⁻¹ * z⁻¹ * T * z ≠ g := by
  refine ⟨Equiv.swap 1 2 * Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1,
    Equiv.swap 1 2, Equiv.swap 0 1, by decide, by decide⟩

/-- **Quillen, notebook 1971-3, p. 34, the abelian case.** If `x ↦ x σ(x)⁻¹` is onto, every
homomorphism `φ` to an abelian group with `φ ∘ σ = φ` is trivial. -/
theorem hom_eq_one {A : Type*} [CommGroup A] (σ : G →* G)
    (hσ : Function.Surjective fun x => x * (σ x)⁻¹) (φ : G →* A) (hφ : φ.comp σ = φ) :
    φ = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := hσ y
  have : φ (σ x) = φ x := DFunLike.congr_fun hφ x
  simp [map_mul, map_inv, this]

end Quillen.Notebook1971_3
