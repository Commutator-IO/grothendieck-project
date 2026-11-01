import Mathlib

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
-/

namespace Quillen.Notebook1968_13Rep

open CategoryTheory

universe u v₁ v₂

variable {k : Type u} [CommRing k] {G : Type v₁} {H : Type v₂} [Group G] [Group H]

/-- The permutation representation `k[G ⧸ f(H)]`, lifted to the universe of `Rep.resFunctor`. -/
noncomputable abbrev cosetRep (f : H →* G) : Rep.{max u v₁ v₂} k G :=
  Rep.ofMulAction k G (ULift.{v₂} (G ⧸ f.range))

/-- The base coset `f(H)` as a point of `ULift (G ⧸ f(H))`. -/
abbrev baseCoset (f : H →* G) : ULift.{v₂} (G ⧸ f.range) := ⟨(1 : G)⟩

lemma smul_baseCoset (f : H →* G) (g : G) :
    g • baseCoset f = baseCoset f ↔ g ∈ f.range := by
  change (ULift.up ((g • ((1 : G) : G ⧸ f.range))) = ULift.up _) ↔ _
  rw [ULift.up_inj, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
  simp

/-- The projection of `k[G ⧸ f(H)]` onto the line spanned by the base coset. -/
noncomputable def proj (f : H →* G) : (cosetRep (k := k) f).V →ₗ[k] (cosetRep (k := k) f).V :=
  (MonoidAlgebra.lsingle (baseCoset f)) ∘ₗ
    (Finsupp.lapply (baseCoset f)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

lemma proj_apply (f : H →* G) (x : (cosetRep (k := k) f).V) :
    proj f x = MonoidAlgebra.single (baseCoset f) (x.coeff (baseCoset f)) := rfl

/-- The projection onto the base coset commutes with the action of `H`. -/
lemma proj_comm (f : H →* G) (h : H) (x : (cosetRep (k := k) f).V) :
    proj f ((cosetRep (k := k) f).ρ (f h) x) = (cosetRep (k := k) f).ρ (f h) (proj f x) := by
  have h1 : f h • baseCoset f = baseCoset f := (smul_baseCoset f _).2 ⟨h, rfl⟩
  have h2 : (f h)⁻¹ • baseCoset f = baseCoset f := (smul_baseCoset f _).2 ⟨h⁻¹, by simp⟩
  rw [proj_apply, proj_apply, Representation.coeff_ofMulAction, h2,
    Representation.ofMulAction_single, h1]

/-- The projection onto the base coset, as an endomorphism of the restriction to `H`. -/
noncomputable def projHom (f : H →* G) :
    (Rep.resFunctor f).obj (cosetRep (k := k) f) ⟶ (Rep.resFunctor f).obj (cosetRep (k := k) f) :=
  Rep.ofHom ⟨proj f, fun h ↦ LinearMap.ext fun x ↦ proj_comm f h x⟩

/-- If restriction along `f` is full, then `f` is surjective (p. 4): the projection of
`k[G ⧸ f(H)]` onto the base coset is `H`-linear, and it is `G`-linear only if `f(H) = G`. -/
theorem surjective_of_full [Nontrivial k] (f : H →* G)
    [(Rep.resFunctor.{max u v₁ v₂} (k := k) f).Full] : Function.Surjective f := by
  obtain ⟨ψ, hψ⟩ := (Rep.resFunctor (k := k) f).map_surjective (projHom f)
  have hψx (x) : ψ.hom x = proj f x := by
    rw [← Rep.resMap_hom_apply f ψ x]
    exact congrArg (fun φ ↦ φ.hom x) hψ
  intro g
  have hc := Rep.hom_comm_apply ψ g (MonoidAlgebra.single (baseCoset f) 1)
  rw [hψx, hψx, proj_apply, proj_apply, Representation.ofMulAction_single] at hc
  by_contra hg
  have hne : g • baseCoset f ≠ baseCoset f := fun h ↦ hg ((smul_baseCoset f g).1 h)
  rw [MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hne.symm] at hc
  rw [MonoidAlgebra.single_zero, Representation.ofMulAction_single] at hc
  exact one_ne_zero (MonoidAlgebra.single_eq_zero.1 hc.symm)

/-- **Restriction is full iff the homomorphism is surjective** (1968-13, p. 4). The direction
`←` is Mathlib's `Rep.full_res`. -/
theorem full_resFunctor_iff [Nontrivial k] (f : H →* G) :
    (Rep.resFunctor.{max u v₁ v₂} (k := k) f).Full ↔ Function.Surjective f :=
  ⟨fun _ ↦ surjective_of_full (k := k) f, Rep.full_res f⟩

/-- The regular representation `k[H]`, lifted to the universe of `Rep.resFunctor`. -/
noncomputable abbrev regRep (H : Type v₂) [Group H] : Rep.{max u v₁ v₂} k H :=
  Rep.ofMulAction k H (ULift.{v₁} H)

/-- If every representation of `H` is, up to isomorphism, restricted from `G`, then `f` is
injective (p. 4): the kernel of `f` acts trivially on a restriction, but faithfully on `k[H]`. -/
theorem injective_of_essSurj [Nontrivial k] (f : H →* G)
    [(Rep.resFunctor.{max u v₁ v₂} (k := k) f).EssSurj] : Function.Injective f := by
  refine (injective_iff_map_eq_one f).2 fun h hh ↦ ?_
  set F := Rep.resFunctor.{max u v₁ v₂} (k := k) f
  let R : Rep.{max u v₁ v₂} k H := regRep.{u, v₁} H
  let e := F.objObjPreimageIso R
  let s : R.V := MonoidAlgebra.single ⟨1⟩ 1
  have hc := Rep.hom_comm_apply e.hom h (e.inv.hom s)
  have h1 : (F.obj (F.objPreimage R)).ρ h = LinearMap.id := by
    change (F.objPreimage _).ρ (f h) = _
    rw [hh, map_one]
    rfl
  rw [h1, LinearMap.id_apply, Rep.hom_inv_apply, Representation.ofMulAction_single] at hc
  have := congrArg ULift.down ((MonoidAlgebra.single_left_inj one_ne_zero).1 hc)
  simpa using this.symm

/-- For a bijective `f`, every representation of `H` is restricted from `G`: transport it along
the inverse isomorphism. -/
theorem essSurj_of_bijective (f : H →* G) (hf : Function.Bijective f) :
    (Rep.resFunctor.{max u v₁ v₂} (k := k) f).EssSurj where
  mem_essImage Y := by
    let e := MulEquiv.ofBijective f hf
    refine ⟨Rep.of (Y.ρ.comp e.symm.toMonoidHom), ⟨Rep.mkIso
      (Representation.Equiv.mk (LinearEquiv.refl k Y.V) fun h ↦ ?_)⟩⟩
    ext y
    change Y.ρ (e.symm (e h)) y = Y.ρ h y
    rw [MulEquiv.symm_apply_apply]

/-- **Restriction is an equivalence iff the homomorphism is bijective** (1968-13, p. 4). -/
theorem isEquivalence_resFunctor_iff [Nontrivial k] (f : H →* G) :
    (Rep.resFunctor.{max u v₁ v₂} (k := k) f).IsEquivalence ↔ Function.Bijective f := by
  refine ⟨fun _ ↦ ⟨injective_of_essSurj (k := k) f, surjective_of_full (k := k) f⟩,
    fun hf ↦ ?_⟩
  have := Rep.full_res (k := k) f hf.2
  have := essSurj_of_bijective (k := k) f hf
  exact { }

end Quillen.Notebook1968_13Rep
