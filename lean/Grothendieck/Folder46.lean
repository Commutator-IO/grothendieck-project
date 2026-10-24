import Mathlib

/-!
# Folder 46, pages 90–92: lifting `H¹(Γ, A*)` through `A → A/𝔪A` when `p ∤ |Γ|`

Pages 90 to 92 of folder 46 (« Petits fourbis cohomologiques », transcription
`transcripts/46/batch-05.fr.tex`) take a local ring `𝒪` with residue field `k` of
characteristic `p`, a finite group `Γ`, a finite `(𝒪, Γ)`-algebra `A` (possibly
noncommutative: the margin of page 90 has `A = M_n(𝒪)`), and claim that
`H¹(Γ, A*) → H¹(Γ, (A/𝔪A)*) × H¹(Λ, A*)` is injective, `Λ` a Sylow `p`-subgroup — « en
particulier », when `p ∤ |Γ|`, that `H¹(Γ, A*) → H¹(Γ, (A/𝔪A)*)` is injective. The text
assumes that `Γ` acts trivially on `A/𝔪A`, the largely illegible margin « plus généralement »
that `A^Γ → A/𝔪A` is onto. The proof reduces to the kernel, then corrects a cocycle step by
step modulo `𝔪ⁿA`, using that `[Γ : Λ]` is invertible on each `𝔪ⁱA/𝔪ⁱ⁺¹A` and the
surjectivity of `A^Γ → A/𝔪A` to make the correcting element a unit.

This file proves the case `p ∤ |Γ|` of the kernel statement (the modernised reading's
« en particulier »; forme reconstituée par l'édition d'après les pages 90–92), by a one-shot
average in place of the induction: for a cocycle `c` and any `w`, `b = Σ_σ c(σ) σ(w)`
satisfies `c(γ) γ(b) = b` (the averaging of Hilbert's Theorem 90), and `b` is a unit when `w`
lifts `v⁻¹`, `v` trivialising `c` modulo `𝔪A`, since then `b ≡ |Γ| w`. Neither the
triviality of `Γ` on `A/𝔪A` nor the surjectivity of `A^Γ → A/𝔪A` is used, nor any action of
`Γ` on `𝒪`.
* `IsCocycle`, `IsCoboundary`: nonabelian 1-cocycles `Γ → Aˣ`, `c(gh) = c(g) · g(c(h))`, and
  those cohomologous to `1`, `c(g) = u⁻¹ g(u)`;
* `mul_smul_sum`, `isCoboundary_of_isUnit_sum`: the averaging identity, and its consequence;
* `isCoboundary_of_sub_one_mem`: a cocycle congruent to `1` modulo an ideal `I` with
  `1 + I ⊂ Aˣ` is a coboundary when `|Γ|` is invertible in `A`;
* `isCoboundary_of_map_isCoboundary`: the kernel of `H¹(Γ, A*) → H¹(Γ, B*)` is trivial for a
  surjective equivariant `π : A → B` with `1 + Ker π ⊂ Aˣ`, `|Γ|` invertible in `A`;
* `isNilpotent_of_mem_smul_top`, `isUnit_one_add_of_mem_smul_top`: elements of `𝔪A` are
  nilpotent when `𝔪ᴺA = 0`, and `1 + 𝔪A ⊂ Aˣ` when `A` is finite over `𝒪` (Nakayama);
* `ker_trivial_of_pow_smul_eq_bot` (case `𝔪ᴺA = 0`) and `ker_trivial` (`A` finite over `𝒪`):
  if `p ∤ |Γ|`, the kernel of `H¹(Γ, A*) → H¹(Γ, (A/𝔪A)*)` is trivial;
* `signCocycle_isCocycle`, `signCocycle_sub_one_mem`, `not_isCoboundary_signCocycle`: for
  `Γ = C₂` acting trivially on `ℤ/4` (`𝔪 = (2)`, `𝔪² = 0`, `p = 2 = |Γ|`), `γ ↦ ±1` is a
  cocycle trivial modulo `𝔪` and not a coboundary: `p ∤ |Γ|` cannot be dropped.

* `mul_smul_sum_twist`, `isCohomologous_of_map`, `injective`: injectivity itself, not only
  the trivial kernel: two cocycles with cohomologous images are cohomologous. The average
  `u = Σ_σ c'(σ) σ(w) c(σ)⁻¹` satisfies `c'(γ) γ(u) = u c(γ)`; this is the averaging for the
  action twisted by `c'` (pages 86–89), written without changing the action.

Not formalised: the Sylow form (the factor `H¹(Λ, A*)`), the semi-local base with its
decomposition and inertia groups (pages 84–89), and the passage from `𝔪ⁿA` to `A` by
Artin–Rees (which the finite case here makes unnecessary).
-/

open Finset IsLocalRing

namespace Grothendieck.Folder46

section Cocycles

variable {Γ A : Type*} [Group Γ] [Ring A] [MulSemiringAction Γ A]

/-- A (nonabelian) 1-cocycle of `Γ` with values in `Aˣ`: `c(gh) = c(g) · g(c(h))`. -/
def IsCocycle (c : Γ → Aˣ) : Prop :=
  ∀ g h, (c (g * h) : A) = c g * g • (c h : A)

/-- A cocycle cohomologous to the trivial one: `c(g) = u⁻¹ · g(u)` for a unit `u`. -/
def IsCoboundary (c : Γ → Aˣ) : Prop :=
  ∃ u : Aˣ, ∀ g, (c g : A) = ↑u⁻¹ * g • (u : A)

variable [Fintype Γ]

/-- The averaging of Hilbert's Theorem 90: `b = Σ_σ c(σ) σ(w)` satisfies `c(γ) γ(b) = b`. -/
theorem mul_smul_sum {c : Γ → Aˣ} (hc : IsCocycle c) (w : A) (g : Γ) :
    (c g : A) * g • ∑ s, (c s : A) * s • w = ∑ s, (c s : A) * s • w := by
  unfold IsCocycle at hc
  rw [smul_sum, mul_sum]
  simp_rw [smul_mul', ← mul_assoc, ← hc, smul_smul]
  exact Equiv.sum_comp (Equiv.mulLeft g) fun s => (c s : A) * s • w

/-- If the average `Σ_σ c(σ) σ(w)` is a unit, the cocycle `c` is a coboundary. -/
theorem isCoboundary_of_isUnit_sum {c : Γ → Aˣ} (hc : IsCocycle c) (w : A)
    (hb : IsUnit (∑ s, (c s : A) * s • w)) : IsCoboundary c := by
  obtain ⟨b, hb⟩ := hb
  refine ⟨b⁻¹, fun g => ?_⟩
  have h : (c g : A) * g • (b : A) = b := hb ▸ mul_smul_sum hc w g
  calc (c g : A) = c g * (g • (b : A) * g • ((b⁻¹ : Aˣ) : A)) := by
        rw [← smul_mul', Units.mul_inv, smul_one, mul_one]
    _ = _ := by rw [← mul_assoc, h, inv_inv]

/-- An element with a unit of the form `1 + x`, `x ∈ I`, on either side, `I` an ideal with
`1 + I ⊂ Aˣ`, is a unit: the case of an element invertible modulo `I`. -/
theorem isUnit_of_mul_sub_one_mem (I : Ideal A) (hI : ∀ x ∈ I, IsUnit (1 + x)) {a a' : A}
    (h₁ : a * a' - 1 ∈ I) (h₂ : a' * a - 1 ∈ I) : IsUnit a := by
  obtain ⟨u, hu⟩ := hI _ h₁
  obtain ⟨v, hv⟩ := hI _ h₂
  rw [add_sub_cancel] at hu hv
  refine isUnit_iff_exists_and_exists.2 ⟨⟨a' * ↑u⁻¹, ?_⟩, ⟨↑v⁻¹ * a', ?_⟩⟩
  · rw [← mul_assoc, ← hu, Units.mul_inv]
  · rw [mul_assoc, ← hv, Units.inv_mul]

/-- A cocycle congruent to `1` modulo an ideal `I` with `1 + I ⊂ Aˣ` is a coboundary when
`|Γ|` is invertible in `A`. -/
theorem isCoboundary_of_sub_one_mem (I : Ideal A) (hI : ∀ x ∈ I, IsUnit (1 + x))
    (hn : IsUnit (Fintype.card Γ : A)) {c : Γ → Aˣ} (hc : IsCocycle c)
    (h1 : ∀ g, (c g : A) - 1 ∈ I) : IsCoboundary c := by
  refine isCoboundary_of_isUnit_sum hc 1 ?_
  obtain ⟨n, hn⟩ := hn
  have hy : ∑ s, ((c s : A) - 1) ∈ I := I.sum_mem fun s _ => h1 s
  have : ∑ s, (c s : A) * s • (1 : A) = n * (1 + ↑n⁻¹ * ∑ s, ((c s : A) - 1)) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul, sum_sub_distrib, hn]
    simp
  rw [this]
  exact n.isUnit.mul (hI _ (I.mul_mem_left _ hy))

variable {B : Type*} [Ring B] [MulSemiringAction Γ B]

/-- The kernel of `H¹(Γ, A*) → H¹(Γ, B*)` is trivial for a surjective `Γ`-equivariant ring
map `π : A → B` with `1 + Ker π ⊂ Aˣ`, when `|Γ|` is invertible in `A`. -/
theorem isCoboundary_of_map_isCoboundary (π : A →+* B) (hπ : Function.Surjective π)
    (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    (hker : ∀ x, π x = 0 → IsUnit (1 + x)) (hn : IsUnit (Fintype.card Γ : A))
    {c : Γ → Aˣ} (hc : IsCocycle c) (hπc : ∃ v : Bˣ, ∀ g, π (c g) = ↑v⁻¹ * g • (v : B)) :
    IsCoboundary c := by
  obtain ⟨v, hv⟩ := hπc
  obtain ⟨w, hw⟩ := hπ ↑v⁻¹
  obtain ⟨w', hw'⟩ := hπ ↑v
  have hwu : IsUnit w := isUnit_of_mul_sub_one_mem (RingHom.ker π) (fun x hx => hker x hx)
    (a' := w') (by simp [RingHom.mem_ker, hw, hw']) (by simp [RingHom.mem_ker, hw, hw'])
  refine isCoboundary_of_isUnit_sum hc w ?_
  obtain ⟨m, hm⟩ := hn.mul hwu
  set x := ∑ s, (c s : A) * s • w - m
  have hx : π x = 0 := by
    have : ∀ s : Γ, π ((c s : A) * s • w) = ↑v⁻¹ := fun s => by
      rw [map_mul, hv, hequiv, hw, mul_assoc, ← smul_mul', Units.mul_inv, smul_one, mul_one]
    simp [x, this, hm, hw]
  have : ∑ s, (c s : A) * s • w = m * (1 + ↑m⁻¹ * x) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul, add_sub_cancel]
  rw [this]
  exact m.isUnit.mul (hker _ (by rw [map_mul, hx, mul_zero]))

/-! ### Injectivity: comparing two cocycles (pages 86–90) -/

omit [Fintype Γ] in
theorem smul_inv_eq {c : Γ → Aˣ} (hc : IsCocycle c) (g s : Γ) :
    g • ((↑(c s)⁻¹ : Aˣ) : A) = ↑(c (g * s))⁻¹ * c g := by
  rw [Units.eq_inv_mul_iff_mul_eq, hc, mul_assoc, ← smul_mul', Units.mul_inv, smul_one, mul_one]

/-- The averaging for two cocycles: `u = Σ_σ c'(σ) σ(w) c(σ)⁻¹` satisfies
`c'(γ) γ(u) = u c(γ)`. This is the averaging of the twisted action
`γ ⋆ a = c'(γ) γ(a) c'(γ)⁻¹` of pages 86–89, written without changing the action. -/
theorem mul_smul_sum_twist {c c' : Γ → Aˣ} (hc : IsCocycle c) (hc' : IsCocycle c') (w : A)
    (g : Γ) :
    (c' g : A) * g • ∑ s, (c' s : A) * s • w * ↑(c s)⁻¹ =
      (∑ s, (c' s : A) * s • w * ↑(c s)⁻¹) * c g := by
  rw [smul_sum, mul_sum, sum_mul,
    ← Equiv.sum_comp (Equiv.mulLeft g) (fun s => (c' s : A) * s • w * ↑(c s)⁻¹ * c g)]
  refine sum_congr rfl fun s _ => ?_
  simp only [Equiv.coe_mulLeft]
  rw [smul_mul', smul_mul', smul_inv_eq hc, smul_smul, hc' g s]
  simp only [mul_assoc]

/-- If the average is a unit `u`, then `c(γ) = u⁻¹ c'(γ) γ(u)`: `c` and `c'` are cohomologous. -/
theorem isCohomologous_of_isUnit_sum {c c' : Γ → Aˣ} (hc : IsCocycle c) (hc' : IsCocycle c')
    (w : A) (hb : IsUnit (∑ s, (c' s : A) * s • w * ↑(c s)⁻¹)) :
    ∃ u : Aˣ, ∀ g, (c g : A) = ↑u⁻¹ * c' g * g • (u : A) := by
  obtain ⟨u, hu⟩ := hb
  refine ⟨u, fun g => ?_⟩
  have h := mul_smul_sum_twist hc hc' w g
  rw [← hu] at h
  rw [mul_assoc, h, ← mul_assoc, Units.inv_mul, one_mul]

/-- **`H¹(Γ, A*) → H¹(Γ, B*)` is injective** (not only of trivial kernel) for a surjective
`Γ`-equivariant ring map `π : A → B` with `1 + Ker π ⊂ Aˣ`, when `|Γ|` is invertible in `A`:
two cocycles whose images are cohomologous are cohomologous. -/
theorem isCohomologous_of_map (π : A →+* B) (hπ : Function.Surjective π)
    (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    (hker : ∀ x, π x = 0 → IsUnit (1 + x)) (hn : IsUnit (Fintype.card Γ : A))
    {c c' : Γ → Aˣ} (hc : IsCocycle c) (hc' : IsCocycle c')
    (hπc : ∃ v : Bˣ, ∀ g, π (c g) = ↑v⁻¹ * π (c' g) * g • (v : B)) :
    ∃ u : Aˣ, ∀ g, (c g : A) = ↑u⁻¹ * c' g * g • (u : A) := by
  obtain ⟨v, hv⟩ := hπc
  obtain ⟨w, hw⟩ := hπ ↑v
  obtain ⟨w', hw'⟩ := hπ ↑v⁻¹
  have hwu : IsUnit w := isUnit_of_mul_sub_one_mem (RingHom.ker π) (fun x hx => hker x hx)
    (a' := w') (by simp [RingHom.mem_ker, hw, hw']) (by simp [RingHom.mem_ker, hw, hw'])
  refine isCohomologous_of_isUnit_sum hc hc' w ?_
  obtain ⟨m, hm⟩ := hn.mul hwu
  set x := ∑ s, (c' s : A) * s • w * ↑(c s)⁻¹ - m
  have hx : π x = 0 := by
    have : ∀ s : Γ, π ((c' s : A) * s • w * ↑(c s)⁻¹) = ↑v := fun s => by
      have h1 : π (c s) * π ↑(c s)⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      rw [hv s] at h1
      rw [map_mul, map_mul, hequiv, hw]
      calc π (c' s) * s • (v : B) * π ↑(c s)⁻¹
          = ↑v * (↑v⁻¹ * π (c' s) * s • (v : B) * π ↑(c s)⁻¹) := by
            simp only [← mul_assoc, Units.mul_inv, one_mul]
        _ = ↑v := by rw [h1, mul_one]
    simp [x, this, hm, hw]
  have : ∑ s, (c' s : A) * s • w * ↑(c s)⁻¹ = m * (1 + ↑m⁻¹ * x) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul, add_sub_cancel]
  rw [this]
  exact m.isUnit.mul (hker _ (by rw [map_mul, hx, mul_zero]))

end Cocycles

section LocalRing

variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]

/-- `I • ⊤` is stable under every `O`-linear endomorphism of `A`. -/
theorem map_mem_smul_top (I : Ideal O) (f : A →ₗ[O] A) {x : A}
    (hx : x ∈ I • (⊤ : Submodule O A)) : f x ∈ I • (⊤ : Submodule O A) :=
  Submodule.smul_mono le_rfl le_top
    (Submodule.map_smul'' I ⊤ f ▸ Submodule.mem_map_of_mem hx)

/-- `(I • A) (J • A) ⊂ (I J) • A`. -/
theorem mul_mem_smul_top {I J : Ideal O} {x y : A} (hx : x ∈ I • (⊤ : Submodule O A))
    (hy : y ∈ J • (⊤ : Submodule O A)) : x * y ∈ (I * J) • (⊤ : Submodule O A) := by
  rw [mul_comm, Submodule.mul_smul]
  have h := Submodule.map_smul'' J ⊤ (LinearMap.mulLeft O x) ▸
    Submodule.mem_map_of_mem (f := LinearMap.mulLeft O x) hy
  refine Submodule.smul_mono le_rfl ?_ h
  rintro _ ⟨a, -, rfl⟩
  exact map_mem_smul_top I (LinearMap.mulRight O a) hx

variable [IsLocalRing O]

/-- In the case `𝔪ᴺA = 0`, the elements of `𝔪A` are nilpotent. -/
theorem isNilpotent_of_mem_smul_top {N : ℕ}
    (hN : maximalIdeal O ^ N • (⊤ : Submodule O A) = ⊥) {x : A}
    (hx : x ∈ maximalIdeal O • (⊤ : Submodule O A)) : IsNilpotent x := by
  have : ∀ k, x ^ k ∈ maximalIdeal O ^ k • (⊤ : Submodule O A) := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ]; exact mul_mem_smul_top ih hx
  exact ⟨N, by simpa [hN] using this N⟩

/-- For `A` finite over the local ring `O`, `1 + 𝔪A ⊂ Aˣ` (Nakayama). -/
theorem isUnit_one_add_of_mem_smul_top [Module.Finite O A] {x : A}
    (hx : x ∈ maximalIdeal O • (⊤ : Submodule O A)) : IsUnit (1 + x) := by
  have key : ∀ f : A →ₗ[O] A, (∀ a, a - f a ∈ maximalIdeal O • (⊤ : Submodule O A)) →
      ∃ y, f y = 1 := fun f hf => by
    have : (⊤ : Submodule O A) ≤ LinearMap.range f :=
      Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
        (maximalIdeal_le_jacobson _) fun a _ => by
          rw [← add_sub_cancel (f a) a]
          exact Submodule.add_mem_sup ⟨a, rfl⟩ (hf a)
    exact this (Submodule.mem_top (x := 1))
  obtain ⟨y, hy⟩ := key (LinearMap.mulLeft O (1 + x)) fun a => by
    simpa [add_mul] using Submodule.neg_mem _ (map_mem_smul_top _ (LinearMap.mulRight O a) hx)
  obtain ⟨z, hz⟩ := key (LinearMap.mulRight O (1 + x)) fun a => by
    simpa [mul_add] using Submodule.neg_mem _ (map_mem_smul_top _ (LinearMap.mulLeft O a) hx)
  exact isUnit_iff_exists_and_exists.2 ⟨⟨y, hy⟩, ⟨z, hz⟩⟩

variable {Γ B : Type*} [Group Γ] [Fintype Γ] [MulSemiringAction Γ A] [Ring B]
  [MulSemiringAction Γ B]

omit [Group Γ] [MulSemiringAction Γ A] in
/-- `p ∤ |Γ|`, `p` the residue characteristic, makes `|Γ|` invertible in `A`. -/
theorem isUnit_card (hp : ¬ ringChar (ResidueField O) ∣ Fintype.card Γ) :
    IsUnit (Fintype.card Γ : A) := by
  have : IsUnit (Fintype.card Γ : O) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    exact fun h => hp ((ringChar.spec _ _).1 h)
  simpa using this.map (algebraMap O A)

/-- Pages 90–92, case `𝔪ᴺA = 0` and `p ∤ |Γ|`: for `π : A → B` a surjective equivariant ring
map with kernel in `𝔪A` (e.g. `B = A/𝔪A`), the kernel of `H¹(Γ, A*) → H¹(Γ, B*)` is trivial
(d'après les pages 90–92, forme reconstituée par l'édition). -/
theorem ker_trivial_of_pow_smul_eq_bot {N : ℕ}
    (hN : maximalIdeal O ^ N • (⊤ : Submodule O A) = ⊥)
    (hp : ¬ ringChar (ResidueField O) ∣ Fintype.card Γ) (π : A →+* B)
    (hπ : Function.Surjective π) (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    (hker : ∀ x, π x = 0 → x ∈ maximalIdeal O • (⊤ : Submodule O A)) {c : Γ → Aˣ}
    (hc : IsCocycle c) (hπc : ∃ v : Bˣ, ∀ g, π (c g) = ↑v⁻¹ * g • (v : B)) :
    IsCoboundary c :=
  isCoboundary_of_map_isCoboundary π hπ hequiv
    (fun x hx => (isNilpotent_of_mem_smul_top hN (hker x hx)).isUnit_one_add) (isUnit_card hp)
    hc hπc

/-- Pages 90–92, `A` finite over `𝒪` and `p ∤ |Γ|`: the kernel of `H¹(Γ, A*) → H¹(Γ, B*)`,
`B = A/𝔪A` or any surjective equivariant image with kernel in `𝔪A`, is trivial, without
`𝔪` nilpotent and without Artin–Rees (d'après les pages 90–92, forme reconstituée par
l'édition). -/
theorem ker_trivial [Module.Finite O A] (hp : ¬ ringChar (ResidueField O) ∣ Fintype.card Γ)
    (π : A →+* B) (hπ : Function.Surjective π) (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    (hker : ∀ x, π x = 0 → x ∈ maximalIdeal O • (⊤ : Submodule O A)) {c : Γ → Aˣ}
    (hc : IsCocycle c) (hπc : ∃ v : Bˣ, ∀ g, π (c g) = ↑v⁻¹ * g • (v : B)) :
    IsCoboundary c :=
  isCoboundary_of_map_isCoboundary π hπ hequiv
    (fun x hx => isUnit_one_add_of_mem_smul_top (hker x hx)) (isUnit_card hp) hc hπc

/-- **Page 90, injectivity**, `A` finite over `𝒪` and `p ∤ |Γ|`: two cocycles `Γ → A*` whose
images in `B = A/𝔪A` (or any surjective equivariant image with kernel in `𝔪A`) are cohomologous
are cohomologous. -/
theorem injective [Module.Finite O A] (hp : ¬ ringChar (ResidueField O) ∣ Fintype.card Γ)
    (π : A →+* B) (hπ : Function.Surjective π) (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    (hker : ∀ x, π x = 0 → x ∈ maximalIdeal O • (⊤ : Submodule O A)) {c c' : Γ → Aˣ}
    (hc : IsCocycle c) (hc' : IsCocycle c')
    (hπc : ∃ v : Bˣ, ∀ g, π (c g) = ↑v⁻¹ * π (c' g) * g • (v : B)) :
    ∃ u : Aˣ, ∀ g, (c g : A) = ↑u⁻¹ * c' g * g • (u : A) :=
  isCohomologous_of_map π hπ hequiv
    (fun x hx => isUnit_one_add_of_mem_smul_top (hker x hx)) (isUnit_card hp) hc hc' hπc

end LocalRing

section Counterexample

/-- The trivial action of `C₂ = Multiplicative (ZMod 2)` on `ZMod 4`. -/
abbrev trivialAction : MulSemiringAction (Multiplicative (ZMod 2)) (ZMod 4) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

attribute [local instance] trivialAction

/-- The cocycle `γ ↦ ±1` of `C₂` in `(ℤ/4)*`, for the trivial action. -/
def signCocycle (g : Multiplicative (ZMod 2)) : (ZMod 4)ˣ := if g = 1 then 1 else -1

theorem signCocycle_isCocycle : IsCocycle signCocycle := by
  unfold IsCocycle signCocycle
  decide

/-- `signCocycle` is trivial modulo `𝔪 = (2)`, where `𝔪² = 0`. -/
theorem signCocycle_sub_one_mem (g : Multiplicative (ZMod 2)) :
    (signCocycle g : ZMod 4) - 1 ∈ Ideal.span {(2 : ZMod 4)} := by
  rw [Ideal.mem_span_singleton, signCocycle]
  split_ifs
  exacts [⟨0, by decide⟩, ⟨1, by decide⟩]

/-- The edition's counterexample: for `p = 2 = |Γ|`, a cocycle trivial modulo `𝔪` need not be
a coboundary, so `p ∤ |Γ|` cannot be dropped. -/
theorem not_isCoboundary_signCocycle : ¬ IsCoboundary signCocycle := by
  rintro ⟨u, hu⟩
  have h : _ = ↑u⁻¹ * (u : ZMod 4) := hu (Multiplicative.ofAdd 1)
  rw [Units.inv_mul] at h
  exact absurd h (by decide)

end Counterexample

end Grothendieck.Folder46
