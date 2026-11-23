/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.DeMorgan
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.CategoryTheory.SingleObj

import Bridges.Monoids

/-!
# De Morgan topoi of finite monoids and of transformation monoids

The bridge `isDeMorganTopos_singleObj_iff` says that the topos `(SingleObj M)ᵒᵖ ⥤ Type` of
right `M`-sets is De Morgan iff any two elements of `M` have a common right multiple,
`a * c = b * d`. Composition in `SingleObj M` is `f ≫ g = g * f`, and a cospan `a, b` is completed
by `c, d` with `c ≫ a = d ≫ b`, that is `a * c = b * d`: the right Ore condition on `SingleObj M`
is the existence of common *right* multiples, not of common left multiples `c * a = d * b`.

* `forall_exists_mul_eq_mul_iff_existsUnique_minimal`: a finite monoid has common right
  multiples iff it has a unique minimal right ideal, a right ideal being a non-empty subset `I`
  with `I * M ⊆ I` (`IsRightIdeal`);
* `isDeMorganTopos_singleObj_iff_existsUnique_minimal`: hence the topos of right `M`-sets of a
  finite monoid is De Morgan iff `M` has a unique minimal right ideal.

For a submonoid `S` of the monoid `Function.End Q` of maps `Q → Q` (with `f * g = f ∘ g`), a
constant map `κ` is a left zero, `κ * f = κ`. Hence:

* `exists_mul_eq_mul_of_const_mem`: if `S` contains a constant map (a reset word of a
  synchronizing automaton), any two elements of `S` have a common *left* multiple, and the
  topos of left `S`-sets, the right `Sᵐᵒᵖ`-sets, is De Morgan
  (`isDeMorganTopos_singleObj_mulOpposite_of_const_mem`);
* `not_forall_exists_mul_eq_mul_of_const_mem`: if moreover `S` acts transitively on a set `Q`
  with two elements, two distinct constant maps have no common *right* multiple, and the topos
  of right `S`-sets is not De Morgan (`not_isDeMorganTopos_singleObj_of_const_mem`). The
  statement « a transitive transformation monoid with a constant map has common right
  multiples » is thus false; it holds on the left, without finiteness or transitivity.
-/

@[expose] public section

namespace LeanPool.ToposTheoreticBridges.Examples

open CategoryTheory

section RightIdeal

variable {M : Type*} [Monoid M]

/-- A right ideal of a monoid `M`: a non-empty subset `I` with `I * M ⊆ I`. -/
def IsRightIdeal (I : Set M) : Prop :=
  I.Nonempty ∧ ∀ x ∈ I, ∀ m : M, x * m ∈ I

/-- The whole monoid is a right ideal. -/
theorem isRightIdeal_univ : IsRightIdeal (Set.univ : Set M) :=
  ⟨Set.univ_nonempty, fun _ _ _ => Set.mem_univ _⟩

/-- The principal right ideal `a * M`. -/
theorem isRightIdeal_range_mul (a : M) : IsRightIdeal (Set.range (a * ·)) :=
  ⟨⟨a, 1, mul_one a⟩, by
    rintro _ ⟨c, rfl⟩ m
    exact ⟨c * m, (mul_assoc a c m).symm⟩⟩

/-- If any two elements have a common right multiple, two right ideals meet in a right
ideal. -/
theorem IsRightIdeal.inter (h : ∀ a b : M, ∃ c d : M, a * c = b * d) {I J : Set M}
    (hI : IsRightIdeal I) (hJ : IsRightIdeal J) : IsRightIdeal (I ∩ J) := by
  obtain ⟨a, ha⟩ := hI.1
  obtain ⟨b, hb⟩ := hJ.1
  obtain ⟨c, d, hcd⟩ := h a b
  exact ⟨⟨a * c, hI.2 a ha c, hcd ▸ hJ.2 b hb d⟩,
    fun x hx m => ⟨hI.2 x hx.1 m, hJ.2 x hx.2 m⟩⟩

/-- If any two elements have a common right multiple, there is at most one minimal right
ideal. -/
theorem eq_of_minimal_isRightIdeal (h : ∀ a b : M, ∃ c d : M, a * c = b * d) {I J : Set M}
    (hI : Minimal IsRightIdeal I) (hJ : Minimal IsRightIdeal J) : I = J := by
  have hIJ := hI.1.inter h hJ.1
  have h₁ : I ⊆ I ∩ J := hI.2 hIJ Set.inter_subset_left
  have h₂ : J ⊆ I ∩ J := hJ.2 hIJ Set.inter_subset_right
  exact (h₁.trans Set.inter_subset_right).antisymm (h₂.trans Set.inter_subset_left)

/-- **Common right multiples in finite monoids.** A finite monoid has common right multiples,
`∀ a b, ∃ c d, a * c = b * d`, iff it has a unique minimal right ideal. -/
theorem forall_exists_mul_eq_mul_iff_existsUnique_minimal [Finite M] :
    (∀ a b : M, ∃ c d : M, a * c = b * d) ↔ ∃! I : Set M, Minimal IsRightIdeal I := by
  constructor
  · intro h
    obtain ⟨I, -, hI⟩ := Finite.exists_le_minimal (isRightIdeal_univ (M := M))
    exact ⟨I, hI, fun J hJ => eq_of_minimal_isRightIdeal h hJ hI⟩
  · rintro ⟨K, hK, hK'⟩ a b
    have key : ∀ x : M, K ⊆ Set.range (x * ·) := fun x => by
      obtain ⟨I, hIle, hI⟩ := Finite.exists_le_minimal (isRightIdeal_range_mul x)
      rw [← hK' I hI]
      exact hIle
    obtain ⟨k, hk⟩ := hK.1.1
    obtain ⟨c, hc⟩ := key a hk
    obtain ⟨d, hd⟩ := key b hk
    exact ⟨c, d, (show a * c = k from hc).trans (show b * d = k from hd).symm⟩

end RightIdeal

/-- **De Morgan topoi of finite monoids.** The topos of right `M`-sets of a finite monoid `M` is
De Morgan iff `M` has a unique minimal right ideal. -/
theorem isDeMorganTopos_singleObj_iff_existsUnique_minimal {M : Type} [Monoid M] [Finite M] :
    IsDeMorganTopos ((SingleObj M)ᵒᵖ ⥤ Type) ↔ ∃! I : Set M, Minimal IsRightIdeal I :=
  isDeMorganTopos_singleObj_iff.trans forall_exists_mul_eq_mul_iff_existsUnique_minimal

section Transformation

variable {Q : Type} {S : Submonoid (Function.End Q)} {q₀ : Q}

/-- A constant map is a left zero of `Function.End Q`: a monoid of maps containing a constant
map has common left multiples. -/
theorem exists_mul_eq_mul_of_const_mem (hconst : (fun _ => q₀ : Function.End Q) ∈ S)
    (a b : S) : ∃ c d : S, c * a = d * b :=
  ⟨⟨_, hconst⟩, ⟨_, hconst⟩, rfl⟩

/-- **Synchronizing automata.** If a monoid `S` of maps `Q → Q` contains a constant map, the topos
of left `S`-sets, that is of right `Sᵐᵒᵖ`-sets, is De Morgan. -/
theorem isDeMorganTopos_singleObj_mulOpposite_of_const_mem
    (hconst : (fun _ => q₀ : Function.End Q) ∈ S) :
    IsDeMorganTopos ((SingleObj Sᵐᵒᵖ)ᵒᵖ ⥤ Type) := by
  rw [isDeMorganTopos_singleObj_iff]
  intro a b
  obtain ⟨c, d, h⟩ := exists_mul_eq_mul_of_const_mem hconst a.unop b.unop
  exact ⟨MulOpposite.op c, MulOpposite.op d, MulOpposite.unop_injective h⟩

/-- If a monoid `S` of maps `Q → Q` contains a constant map and acts transitively on a set `Q`
with two elements, two distinct constant maps of `S` have no common right multiple. -/
theorem not_forall_exists_mul_eq_mul_of_const_mem [Nontrivial Q]
    (hconst : (fun _ => q₀ : Function.End Q) ∈ S) (htrans : ∀ q r : Q, ∃ m ∈ S, m q = r) :
    ¬ ∀ a b : S, ∃ c d : S, a * c = b * d := by
  intro h
  obtain ⟨q₁, q₂, hne⟩ := exists_pair_ne Q
  obtain ⟨m₁, hm₁, h₁⟩ := htrans q₀ q₁
  obtain ⟨m₂, hm₂, h₂⟩ := htrans q₀ q₂
  obtain ⟨c, d, hcd⟩ := h (⟨m₁, hm₁⟩ * ⟨_, hconst⟩) (⟨m₂, hm₂⟩ * ⟨_, hconst⟩)
  have := congrArg (fun f : S => (f : Function.End Q) q₀) hcd
  change m₁ q₀ = m₂ q₀ at this
  exact hne (h₁ ▸ h₂ ▸ this)

/-- If a monoid `S` of maps `Q → Q` contains a constant map and acts transitively on a set with
two elements, the topos of right `S`-sets is not De Morgan. -/
theorem not_isDeMorganTopos_singleObj_of_const_mem [Nontrivial Q]
    (hconst : (fun _ => q₀ : Function.End Q) ∈ S) (htrans : ∀ q r : Q, ∃ m ∈ S, m q = r) :
    ¬ IsDeMorganTopos ((SingleObj S)ᵒᵖ ⥤ Type) := by
  rw [isDeMorganTopos_singleObj_iff]
  exact not_forall_exists_mul_eq_mul_of_const_mem hconst htrans

end Transformation

end LeanPool.ToposTheoreticBridges.Examples
