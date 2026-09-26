import Mathlib.Algebra.Module.Injective
import Mathlib.RingTheory.Filtration
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Folder 21, Proposition 2.15 and Corollaire 2.16: `I`-torsion and injectivity

The modernised reading `transcripts/21/21.modern.tex` (typescript pages 11–13)
states, for `A` a commutative Noetherian ring and `I` an ideal:

> **Proposition 2.15.** Avec les notations précédentes, pour que `H` soit un
> `A`-module injectif, il faut et il suffit que le foncteur
> `T_H(M) = Hom(M,H)` sur la catégorie `𝒞` des `A`-modules de type fini annulés
> par une puissance de `I` soit exact à droite, donc exact.
>
> La nécessité est triviale. Pour la suffisance, il suffit — c'est le critère
> de Baer — de vérifier que pour tout sous-module `N` de `A`, l'application
> `Hom(A,H) → Hom(N,H)` est surjective … Soit donc `u : N → H`. Son image est un
> sous-module de type fini de `H`, donc annulé par une puissance de `I` : `u`
> est nul sur `IⁿN`. Par le lemme d'Artin–Rees, il existe `m` tel que
> `N ∩ IᵐM ⊂ IⁿN`. …
>
> **Corollaire 2.16.** Soit `K` un `A`-module et soit `H⁰_I(K)` le sous-module
> des éléments annulés par une puissance de `I`. Si `K` est injectif, `H⁰_I(K)`
> l'est aussi.

Here `H` is, as « avec les notations précédentes » says (2.9, 2.14), an
`A`-module every element of which is killed by a power of `I`. "`Hom(-,H)` exact
à droite on `𝒞`" is: for every `M ∈ 𝒞` and every submodule `N ⊆ M`, every
`N → H` extends to `M` (`ExactSurC`).

What is proved, as the reading states it:

* `proposition2_15` — for `A` Noetherian and `H` of `I`-power torsion,
  `H` injective ⟺ `Hom(-,H)` exact on `𝒞`. The proof is the typescript's:
  Baer's criterion, the image of `u` killed by one power `Iⁿ`, Artin–Rees in
  the form `N ∩ I^{n+k} ⊆ IⁿN`, and the extension along `N/(N ∩ Iᵐ) ↪ A/Iᵐ`.
* `corollaire2_16` — `Γ_I` preserves injectives over a Noetherian ring.

The bulk of the folder (2.1–2.14: abelian categories, cohomological functors,
Eilenberg–Watts, associated primes of the representing module; the sheaf and
fibered-category halves, pp. 15–28) is not formalised here.

**What the formalisation finds.** Nothing false. The Artin–Rees containment
the proof needs is `N ∩ IᵐA ⊆ IⁿN`, with the ambient module on the left — the
reading's correction of the page (the page writes `N ∩ IᵐN`, for which the
containment is trivially true for `m ⩾ n` and useless). Two small observations:
the hypothesis "`M` of finite type" on the test objects is used only through the
cyclic modules `A/Iᵐ`, so the criterion already holds when `Hom(-,H)` is only
known to be exact on inclusions `N ↪ A/Iᵐ`; and the argument of 2.16 uses no
finiteness of `M` — an extension to `M` of a map into `K` lands in `H⁰_I(K)` as
soon as `M` is killed by a power of `I` — so its Noetherian hypothesis is there
only to invoke 2.15 (Artin–Rees).

What this certifies is that the reading holds together at these points, not
that it is what the pages say (issue #26).
-/

namespace Grothendieck.Folder21

universe u

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- `M` is killed by a power of `I`. -/
def TueParPuissance (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  ∃ n : ℕ, ∀ a ∈ I ^ n, ∀ x : M, a • x = 0

/-- Every element of `H` is killed by some power of `I`. -/
def TorsionI (H : Type*) [AddCommGroup H] [Module A H] : Prop :=
  ∀ x : H, ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0

/-- `Hom(-,H)` is right exact on the category `𝒞` of finitely generated modules
killed by a power of `I`: maps into `H` extend along every inclusion `N ⊆ M` in
`𝒞`. -/
def ExactSurC (H : Type u) [AddCommGroup H] [Module A H] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module A M], Module.Finite A M → TueParPuissance I M →
    ∀ (N : Submodule A M) (f : N →ₗ[A] H), ∃ w : M →ₗ[A] H, ∀ x : N, w x = f x

/-- `H⁰_I(K)`, the elements of `K` killed by a power of `I`. -/
def gammaI (K : Type*) [AddCommGroup K] [Module A K] : Submodule A K where
  carrier := {x | ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0}
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, fun a ha => ?_⟩
    rw [smul_add, hn a (Ideal.pow_le_pow_right (le_max_left n m) ha),
      hm a (Ideal.pow_le_pow_right (le_max_right n m) ha), add_zero]
  zero_mem' := ⟨0, fun a _ => smul_zero a⟩
  smul_mem' := by
    rintro c x ⟨n, hn⟩
    exact ⟨n, fun a ha => by rw [smul_comm, hn a ha, smul_zero]⟩

/-- A finitely generated module all of whose elements are killed by powers of `I`
is killed by a single power: « son image est un sous-module de type fini de `H`,
donc annulé par une puissance de `I` ». -/
theorem tue_de_type_fini {H M : Type*} [AddCommGroup H] [Module A H] [AddCommGroup M]
    [Module A M] [Module.Finite A M] (hH : TorsionI I H) (g : M →ₗ[A] H) :
    ∃ n : ℕ, ∀ a ∈ I ^ n, ∀ x : M, a • g x = 0 := by
  classical
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  choose e he using fun i => hH (g (s i))
  refine ⟨Finset.univ.sup e, fun a ha x => ?_⟩
  have hx : x ∈ Submodule.span A (Set.range s) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact he i a (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i)) ha)
  | zero => rw [map_zero, smul_zero]
  | add y z _ _ hy hz => rw [map_add, smul_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, smul_comm, hy, smul_zero]

/-- **Proposition 2.15.** Over a Noetherian ring, an `I`-power-torsion module `H`
is injective if and only if `Hom(-,H)` is right exact on `𝒞`. -/
theorem proposition2_15 [IsNoetherianRing A] (H : Type u) [AddCommGroup H] [Module A H]
    (hH : TorsionI I H) : Module.Injective A H ↔ ExactSurC I H := by
  constructor
  · -- La nécessité est triviale.
    intro hinj M _ _ _ _ N f
    obtain ⟨w, hw⟩ := hinj.out N.subtype N.injective_subtype f
    exact ⟨w, hw⟩
  · intro hC
    refine Module.Baer.injective fun J g => ?_
    -- The image of `g` is killed by one power `Iⁿ` …
    obtain ⟨n, hn⟩ := tue_de_type_fini I hH g
    -- … so `g` vanishes on `IⁿJ`.
    have hgIJ : ∀ x (hx : x ∈ I ^ n • J), g ⟨x, Submodule.smul_le_right hx⟩ = 0 := by
      intro x hx
      induction hx using Submodule.smul_induction_on' with
      | smul a ha y hy =>
        have : (⟨a • y, Submodule.smul_le_right (Submodule.smul_mem_smul ha hy)⟩ : J) =
          a • ⟨y, hy⟩ := rfl
        rw [this, map_smul, hn a ha]
      | add x hx y hy hx' hy' =>
        have : (⟨x + y, Submodule.smul_le_right (Submodule.add_mem _ hx hy)⟩ : J) =
          ⟨x, Submodule.smul_le_right hx⟩ + ⟨y, Submodule.smul_le_right hy⟩ := rfl
        rw [this, map_add, hx', hy', add_zero]
    -- Artin–Rees: `J ∩ I^{n+k} ⊆ IⁿJ`.
    obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I J
    set m := n + k
    have hAR : ∀ x ∈ J, x ∈ I ^ m → x ∈ I ^ n • J := by
      intro x hxJ hxm
      have h1 : x ∈ I ^ m • (⊤ : Ideal A) ⊓ J := by
        refine ⟨?_, hxJ⟩
        rw [Ideal.smul_eq_mul, Ideal.mul_top]
        exact hxm
      rw [hk m (by omega), show m - k = n by omega] at h1
      exact Submodule.smul_mono le_rfl inf_le_right h1
    -- `J → A/Iᵐ`, whose kernel is `J ∩ Iᵐ`, on which `g` vanishes.
    let φ : J →ₗ[A] A ⧸ I ^ m := (I ^ m).mkQ ∘ₗ J.subtype
    have hker : LinearMap.ker φ ≤ LinearMap.ker g := by
      intro x hx
      have h0 : Ideal.Quotient.mk (I ^ m) (x : A) = 0 := by simpa [φ] using hx
      have hxm : (x : A) ∈ I ^ m := Ideal.Quotient.eq_zero_iff_mem.1 h0
      have := hgIJ x (hAR x x.2 hxm)
      simpa using this
    let u' : LinearMap.range φ →ₗ[A] H :=
      (LinearMap.ker φ).liftQ g hker ∘ₗ φ.quotKerEquivRange.symm.toLinearMap
    -- `A/Iᵐ` is in `𝒞`, so `u'` extends to it.
    have hM : TueParPuissance I (A ⧸ I ^ m) := by
      refine ⟨m, fun a ha x => ?_⟩
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right b _ ha
    obtain ⟨w, hw⟩ := hC (A ⧸ I ^ m) inferInstance hM (LinearMap.range φ) u'
    refine ⟨w ∘ₗ (I ^ m).mkQ, fun x hx => ?_⟩
    have := hw ⟨φ ⟨x, hx⟩, LinearMap.mem_range_self φ _⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, u', LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image] at this
    exact this

/-- **Corollaire 2.16.** Over a Noetherian ring, if `K` is injective then so is
`H⁰_I(K)`. -/
theorem corollaire2_16 [IsNoetherianRing A] (K : Type u) [AddCommGroup K] [Module A K]
    [hK : Module.Injective A K] : Module.Injective A (gammaI I K) := by
  rw [proposition2_15 I _ fun x => x.2.imp fun n hn a ha => Subtype.ext (hn a ha)]
  intro M _ _ _ ⟨n, hn⟩ N f
  obtain ⟨v, hv⟩ := hK.out N.subtype N.injective_subtype ((gammaI I K).subtype ∘ₗ f)
  -- The extension lands in `H⁰_I(K)`, because `M` is killed by `Iⁿ`.
  let w : M →ₗ[A] gammaI I K :=
    v.codRestrict (gammaI I K) fun x => ⟨n, fun a ha => by rw [← map_smul, hn a ha, map_zero]⟩
  exact ⟨w, fun x => Subtype.ext (hv x)⟩

end Grothendieck.Folder21
