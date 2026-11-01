import Quillen.Upstream.RepResFunctor

/-!
# Quillen, notebook 1968-13, p. 4: when restriction of representations is full

Daniel Quillen's notebook 1968-13 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201968/1968-13.pdf>) opens,
in « Fall 68 », with a Whitehead theorem for small categories: a functor `f : C₁ → C₂` should be a
weak equivalence when pulling back along it is an equivalence of derived categories of locally
constant coefficients. In the proof of « (i) ⇒ (ii) » (PDF p. 4) he reduces to the case of a
group homomorphism and needs a small lemma, which he states in parentheses: restriction of
modules along a group homomorphism is fully faithful exactly when the homomorphism is
surjective, and an equivalence exactly when it is bijective. Surjectivity comes from comparing
the invariants of the permutation module `ℤ[G ⧸ f(H)]` under the two groups (rank one for the big
group, rank at least two for the small one if `f` is not onto); injectivity from the fact that the
kernel acts trivially on every restricted module. (On the page the letters `G` and `H` are
swapped between the statement and the rank argument.)

Here the coefficients are any nontrivial commutative ring `k` (Quillen's case is `k = ℤ`), and
restriction is Mathlib's `Rep.resFunctor f : Rep k G ⥤ Rep k H` for `f : H →* G`. It is always
faithful, so « fully faithful » reduces to « full ». The invariant count is replaced by the
equivalent observation that the projection of `k[G ⧸ f(H)]` onto the line of the base coset
commutes with `H` but not with `G`.

* `cosetRep`, `baseCoset`, `smul_baseCoset`: the permutation representation `k[G ⧸ f(H)]` and its
  base point, fixed exactly by `f(H)`;
* `proj`, `proj_apply`, `proj_comm`, `projHom`: the projection onto the base coset, an
  endomorphism of the restriction to `H`;
* `surjective_of_full`, `full_resFunctor_iff`: restriction is full iff `f` is surjective;
* `regRep`, `injective_of_essSurj`: if restriction is essentially surjective, `f` is injective
  (test on the regular representation `k[H]`);
* `essSurj_of_bijective`, `isEquivalence_resFunctor_iff`: restriction is an equivalence iff `f`
  is bijective.

The representations live in the universe `max u v₁ v₂` (`k : Type u`, `G : Type v₁`,
`H : Type v₂`), large enough to hold the test objects; `ULift` moves them there.

Literature: folklore (restriction along a quotient map, « inflation », identifies
`G ⧸ N`-modules with the `G`-modules on which `N` acts trivially, a full subcategory). Mathlib has
the direction « surjective ⇒ full » (`Rep.full_res`, and `Action.full_res` for actions) but
neither converse nor the equivalence criterion.

The proofs are general and live in `Quillen.Upstream.RepResFunctor` (`Rep.full_resFunctor_iff`,
`Rep.isEquivalence_resFunctor_iff`, the test objects in `Rep.ResFunctor`); the declarations below
keep the names of this page.
-/

namespace Quillen.Notebook1968_13Rep

open CategoryTheory

universe u v₁ v₂

variable {k : Type u} [CommRing k] {G : Type v₁} {H : Type v₂} [Group G] [Group H]

/-- The permutation representation `k[G ⧸ f(H)]`, lifted to the universe of `Rep.resFunctor`. -/
noncomputable abbrev cosetRep (f : H →* G) : Rep.{max u v₁ v₂} k G :=
  Rep.ResFunctor.cosetRep f

/-- The base coset `f(H)` as a point of `ULift (G ⧸ f(H))`. -/
abbrev baseCoset (f : H →* G) : ULift.{v₂} (G ⧸ f.range) := Rep.ResFunctor.baseCoset f

lemma smul_baseCoset (f : H →* G) (g : G) :
    g • baseCoset f = baseCoset f ↔ g ∈ f.range :=
  Rep.ResFunctor.smul_baseCoset f g

/-- The projection of `k[G ⧸ f(H)]` onto the line spanned by the base coset. -/
noncomputable abbrev proj (f : H →* G) :
    (cosetRep (k := k) f).V →ₗ[k] (cosetRep (k := k) f).V :=
  Rep.ResFunctor.proj f

lemma proj_apply (f : H →* G) (x : (cosetRep (k := k) f).V) :
    proj f x = MonoidAlgebra.single (baseCoset f) (x.coeff (baseCoset f)) := rfl

/-- The projection onto the base coset commutes with the action of `H`. -/
lemma proj_comm (f : H →* G) (h : H) (x : (cosetRep (k := k) f).V) :
    proj f ((cosetRep (k := k) f).ρ (f h) x) = (cosetRep (k := k) f).ρ (f h) (proj f x) :=
  Rep.ResFunctor.proj_comm f h x

/-- The projection onto the base coset, as an endomorphism of the restriction to `H`. -/
noncomputable abbrev projHom (f : H →* G) :
    (Rep.resFunctor f).obj (cosetRep (k := k) f) ⟶ (Rep.resFunctor f).obj (cosetRep (k := k) f) :=
  Rep.ResFunctor.projHom f

/-- If restriction along `f` is full, then `f` is surjective (p. 4): the projection of
`k[G ⧸ f(H)]` onto the base coset is `H`-linear, and it is `G`-linear only if `f(H) = G`. -/
theorem surjective_of_full [Nontrivial k] (f : H →* G)
    [(Rep.resFunctor.{max u v₁ v₂} (k := k) f).Full] : Function.Surjective f :=
  Rep.surjective_of_full_resFunctor (k := k) f

/-- **Restriction is full iff the homomorphism is surjective** (1968-13, p. 4). The direction
`←` is Mathlib's `Rep.full_res`. -/
theorem full_resFunctor_iff [Nontrivial k] (f : H →* G) :
    (Rep.resFunctor.{max u v₁ v₂} (k := k) f).Full ↔ Function.Surjective f :=
  Rep.full_resFunctor_iff f

/-- The regular representation `k[H]`, lifted to the universe of `Rep.resFunctor`. -/
noncomputable abbrev regRep (H : Type v₂) [Group H] : Rep.{max u v₁ v₂} k H :=
  Rep.ResFunctor.regRep.{u, v₁} H

/-- If every representation of `H` is, up to isomorphism, restricted from `G`, then `f` is
injective (p. 4): the kernel of `f` acts trivially on a restriction, but faithfully on `k[H]`. -/
theorem injective_of_essSurj [Nontrivial k] (f : H →* G)
    [(Rep.resFunctor.{max u v₁ v₂} (k := k) f).EssSurj] : Function.Injective f :=
  Rep.injective_of_essSurj_resFunctor (k := k) f

/-- For a bijective `f`, every representation of `H` is restricted from `G`: transport it along
the inverse isomorphism. -/
theorem essSurj_of_bijective (f : H →* G) (hf : Function.Bijective f) :
    (Rep.resFunctor.{max u v₁ v₂} (k := k) f).EssSurj :=
  Rep.essSurj_resFunctor_of_bijective f hf

/-- **Restriction is an equivalence iff the homomorphism is bijective** (1968-13, p. 4). -/
theorem isEquivalence_resFunctor_iff [Nontrivial k] (f : H →* G) :
    (Rep.resFunctor.{max u v₁ v₂} (k := k) f).IsEquivalence ↔ Function.Bijective f :=
  Rep.isEquivalence_resFunctor_iff f

end Quillen.Notebook1968_13Rep
