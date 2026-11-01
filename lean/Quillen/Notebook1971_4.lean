import Mathlib

/-!
# Quillen, notebook 1971-4, p. 25: a monoid and its group completion

Daniel Quillen's notebook 1971-4 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201971/1971-4.pdf>, March 20 to
April 11, 1971) studies torsors under a small category `C` over a space or a topos. On PDF p. 24
(his « 8 » in the second pagination) he calls a functor `u : C₁ → C₂` *strongly cofinal* when
`(u_!, u^*)` is a morphism of presheaf topoi, equivalently when for every object `Y` of `C₂` the
functor `X ↦ Hom(Y, u X)` is a pro-object of `C₁`, i.e. when its category of elements is
cofiltered (« left-filtering »). On PDF p. 25 (his « 9 ») he tests this on the universal map from
a commutative monoid `M` to its group completion `G`, seen as a functor between one-object
categories. The condition becomes: the category whose objects are the elements of `G` and whose
arrows are given by `M` acting by translation is cofiltered. He checks the two axioms in a few
lines: two arrows `g → g'` given by `m₁, m₂` are equalised after multiplying by a suitable `m`,
and two elements `g₁, g₂` are translates of a common one, found by writing both over a common
denominator.

In Mathlib the condition is `CategoryTheory.RepresentablyFlat`: every comma category
`StructuredArrow X F` is cofiltered. For `F` the functor `SingleObj M ⥤ SingleObj G(M)` induced by
`Algebra.GrothendieckGroup.of`, the objects of `StructuredArrow X F` are the elements of `G(M)`
and an arrow `g → g'` is an `m : M` with `m g = g'`, which is exactly Quillen's category. The
proof below follows his two axioms, isolated as statements about the Grothendieck group.

* `exists_mul_eq_of`: every `x ∈ G(M)` satisfies `b x = a` for some `a, b ∈ M`;
* `exists_common`: the product axiom (p. 25, ii), `g₁ = m₁ g` and `g₂ = m₂ g`;
* `exists_mul_eq_mul`: the equaliser axiom (p. 25, i), `m₁ = m₂` in `G(M)` implies
  `c m₁ = c m₂` in `M` for some `c`;
* `toGroupFunctor`: the functor `SingleObj M ⥤ SingleObj (GrothendieckGroup M)`;
* `representablyFlat_toGroupFunctor`: it is representably flat;
* `final_toGroupFunctor`: hence final.

The monoid is written multiplicatively, as on the page. Not formalised: the remark of p. 24 that
a strongly cofinal functor induces isomorphisms `R^q lim_{C₂} F ≅ R^q lim_{C₁} u^* F`, and the
torsor statements around it (mathlib has no torsors under a small category).

Literature: folklore of group completion. Flat functors and their categories of elements are in
SGA 4, Exp. I and IV; Mac Lane–Moerdijk, *Sheaves in Geometry and Logic*, VII.6. Mathlib has
`RepresentablyFlat` and the Grothendieck group but not this example.
-/

namespace Quillen.Notebook1971_4

open CategoryTheory Algebra

universe u

variable {M : Type u} [CommMonoid M]

/-- Every element of the Grothendieck group becomes an element of `M` after multiplication by an
element of `M`. -/
lemma exists_mul_eq_of (x : GrothendieckGroup M) : ∃ b a : M, GrothendieckGroup.of b * x =
    GrothendieckGroup.of a := by
  obtain ⟨⟨a, b⟩, h⟩ := (Localization.monoidOf (⊤ : Submonoid M)).surj x
  exact ⟨b, a, by rw [mul_comm]; exact h⟩

/-- **Product axiom** (1971-4, p. 25, ii): any two elements of the Grothendieck group are
translates of a common element by elements of `M`. -/
theorem exists_common (g₁ g₂ : GrothendieckGroup M) :
    ∃ (g : GrothendieckGroup M) (m₁ m₂ : M),
      GrothendieckGroup.of m₁ * g = g₁ ∧ GrothendieckGroup.of m₂ * g = g₂ := by
  obtain ⟨b₁, a₁, h₁⟩ := exists_mul_eq_of g₁
  obtain ⟨b₂, a₂, h₂⟩ := exists_mul_eq_of g₂
  refine ⟨(GrothendieckGroup.of (b₁ * b₂))⁻¹, b₂ * a₁, b₁ * a₂, ?_, ?_⟩
  · rw [map_mul, map_mul, ← h₁, mul_inv_eq_iff_eq_mul]
    ac_rfl
  · rw [map_mul, map_mul, ← h₂, mul_inv_eq_iff_eq_mul]
    ac_rfl

/-- **Equaliser axiom** (1971-4, p. 25, i): two elements of `M` with the same image in the
Grothendieck group are equalised by multiplication by an element of `M`. -/
theorem exists_mul_eq_mul {m₁ m₂ : M} (h : GrothendieckGroup.of m₁ = GrothendieckGroup.of m₂) :
    ∃ c : M, c * m₁ = c * m₂ := by
  obtain ⟨⟨c, _⟩, hc⟩ := (Localization.monoidOf (⊤ : Submonoid M)).eq_iff_exists.1 h
  exact ⟨c, hc⟩

/-- The canonical map `M → G(M)` as a functor between one-object categories. -/
abbrev toGroupFunctor (M : Type u) [CommMonoid M] :
    SingleObj M ⥤ SingleObj (GrothendieckGroup M) :=
  (GrothendieckGroup.of (M := M)).toFunctor

/-- **The map from a commutative monoid to its Grothendieck group is representably flat**
(1971-4, p. 25): for the unique object `X`, the category `X / u` of elements of `G(M)` with
arrows given by `M` is cofiltered. -/
theorem representablyFlat_toGroupFunctor : RepresentablyFlat (toGroupFunctor M) where
  cofiltered X :=
    { cone_objs Y₁ Y₂ := by
        obtain ⟨g, m₁, m₂, h₁, h₂⟩ := exists_common (M := M) Y₁.hom Y₂.hom
        exact ⟨StructuredArrow.mk (Y := SingleObj.star M) g, StructuredArrow.homMk m₁ h₁,
          StructuredArrow.homMk m₂ h₂, trivial⟩
      cone_maps Y Y' φ ψ := by
        have hφ := StructuredArrow.w φ
        have hψ := StructuredArrow.w ψ
        obtain ⟨c, hc⟩ := exists_mul_eq_mul (M := M) (m₁ := φ.right) (m₂ := ψ.right)
          (mul_right_cancel (hφ.trans hψ.symm))
        refine ⟨StructuredArrow.mk (Y := SingleObj.star M)
          ((GrothendieckGroup.of c)⁻¹ * Y.hom), StructuredArrow.homMk c
            (mul_inv_cancel_left (GrothendieckGroup.of c) Y.hom), StructuredArrow.hom_ext _ _ ?_⟩
        change φ.right * c = ψ.right * c
        rw [mul_comm, hc, mul_comm]
      nonempty := ⟨StructuredArrow.mk (Y := SingleObj.star M) (1 : GrothendieckGroup M)⟩ }

/-- Consequently `M → G(M)` is a final functor (`CategoryTheory.final_of_representablyFlat`):
colimits over the one-object category of `G(M)` may be computed over that of `M`. -/
theorem final_toGroupFunctor : (toGroupFunctor M).Final :=
  have := representablyFlat_toGroupFunctor (M := M)
  final_of_representablyFlat _

end Quillen.Notebook1971_4
