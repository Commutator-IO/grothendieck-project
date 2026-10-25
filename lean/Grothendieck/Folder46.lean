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

* `mul_smul_sum_cosets`, `isCoboundary_of_restrict`, `ker_trivial_restrict`,
  `ker_trivial_sylow`: the Sylow form, the page's full statement at the level of the kernel:
  with `Λ` a Sylow `p`-subgroup (any subgroup of index prime to `p`) and the margin's
  surjectivity `A^Λ → A/𝔪A` (implied by `A^Γ → A/𝔪A`), a cocycle trivial modulo `𝔪A` and on
  `Λ` is a coboundary — the average over `Γ/Λ`.

Not formalised: injectivity in the Sylow form for noncommutative `A`, the semi-local base with its
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

/-! ### The Sylow form (page 90, with the margin), #83

For `Λ` a subgroup of index prime to `p` (a Sylow `p`-subgroup), the average is taken over the
cosets `Γ/Λ` instead of `Γ`: if `c(λ) λ(z) = z` on `Λ`, the summand `c(g) g(z)` only depends on
`gΛ` and `b = Σ_{gΛ} c(g) g(z)` satisfies `c(γ) γ(b) = b` (`mul_smul_sum_cosets`). When `c` is a
coboundary `u⁻¹ λ(u)` on `Λ` and trivialised by `v` modulo `𝔪A`, the element `z = u⁻¹ w`, with
`w ∈ A^Λ` lifting `π(u) v⁻¹` (the margin's surjectivity `A^Λ → A/𝔪A`, which `A^Γ → A/𝔪A`
implies), satisfies this, and `b ≡ [Γ : Λ] v⁻¹` is a unit: `isCoboundary_of_restrict`,
`ker_trivial_restrict`, `ker_trivial_sylow`. This is the kernel of
`H¹(Γ, A*) → H¹(Γ, (A/𝔪A)*) × H¹(Λ, A*)`; for `A` commutative it is injectivity. -/

section Sylow

variable {Γ A B : Type*} [Group Γ] [Fintype Γ] [Ring A] [MulSemiringAction Γ A] [Ring B]
  [MulSemiringAction Γ B]

omit [Fintype Γ] in
/-- The cocycle rule on the summands of the average over cosets. -/
theorem mul_smul_cocycle {c : Γ → Aˣ} (hc : IsCocycle c) (z : A) (g h : Γ) :
    (c g : A) * g • ((c h : A) * h • z) = (c (g * h) : A) * (g * h) • z := by
  rw [smul_mul', ← mul_assoc, ← hc, smul_smul]

omit [Fintype Γ] in
/-- If `c(γ) γ(b) = b` for a unit `b`, then `c` is a coboundary. -/
theorem isCoboundary_of_fixed {c : Γ → Aˣ} (b : Aˣ) (h : ∀ g, (c g : A) * g • (b : A) = b) :
    IsCoboundary c := by
  refine ⟨b⁻¹, fun g => ?_⟩
  calc (c g : A) = c g * (g • (b : A) * g • ((b⁻¹ : Aˣ) : A)) := by
        rw [← smul_mul', Units.mul_inv, smul_one, mul_one]
    _ = _ := by rw [← mul_assoc, h, inv_inv]

open scoped Classical in
/-- The average over the cosets `Γ/Λ`: if `c(λ) λ(z) = z` for `λ ∈ Λ`, then
`b = Σ_{gΛ} c(g) g(z)` is well defined and satisfies `c(γ) γ(b) = b`. -/
theorem mul_smul_sum_cosets {c : Γ → Aˣ} (hc : IsCocycle c) (Λ : Subgroup Γ) (z : A)
    (hz : ∀ l ∈ Λ, (c l : A) * l • z = z) (g : Γ) :
    (c g : A) * g • ∑ q : Γ ⧸ Λ, (c q.out : A) * q.out • z =
      ∑ q : Γ ⧸ Λ, (c q.out : A) * q.out • z := by
  have hf : ∀ h, ∀ l ∈ Λ, (c (h * l) : A) * (h * l) • z = (c h : A) * h • z := fun h l hl => by
    rw [← mul_smul_cocycle hc, hz l hl]
  rw [smul_sum, mul_sum]
  simp_rw [mul_smul_cocycle hc]
  refine (Equiv.sum_comp (MulAction.toPerm g) _).symm.trans (sum_congr rfl fun q _ => ?_) |>.symm
  obtain ⟨⟨l, hl⟩, hq⟩ := QuotientGroup.mk_out_eq_mul Λ (g * q.out)
  have e : (MulAction.toPerm g q : Γ ⧸ Λ) = (g * q.out : Γ) := by
    conv_lhs => rw [← q.out_eq']
    rfl
  simp only [e, hq, hf _ l hl]

open scoped Classical in
/-- **The Sylow form, at the level of rings.** For a surjective equivariant `π : A → B` with
`1 + Ker π ⊂ Aˣ`, a subgroup `Λ` of index invertible in `A` and `A^Λ → B` onto (the margin of
page 90), a cocycle `c` that is a coboundary modulo `Ker π` and on `Λ` is a coboundary. -/
theorem isCoboundary_of_restrict (π : A →+* B) (hπ : Function.Surjective π)
    (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    (hker : ∀ x, π x = 0 → IsUnit (1 + x)) (Λ : Subgroup Γ) (hn : IsUnit (Λ.index : A))
    (hlift : ∀ y, ∃ w, (∀ l ∈ Λ, l • w = w) ∧ π w = y) {c : Γ → Aˣ} (hc : IsCocycle c)
    (hΛ : ∃ u : Aˣ, ∀ l ∈ Λ, (c l : A) = ↑u⁻¹ * l • (u : A))
    (hπc : ∃ v : Bˣ, ∀ g, π (c g) = ↑v⁻¹ * g • (v : B)) : IsCoboundary c := by
  obtain ⟨u, hu⟩ := hΛ
  obtain ⟨v, hv⟩ := hπc
  obtain ⟨w, hwΛ, hw⟩ := hlift (π u * ↑v⁻¹)
  set z := ↑u⁻¹ * w
  have hz : ∀ l ∈ Λ, (c l : A) * l • z = z := fun l hl => by
    rw [hu l hl, smul_mul', hwΛ l hl, mul_assoc, ← mul_assoc (l • (u : A)), ← smul_mul',
      Units.mul_inv, smul_one, one_mul]
  have hπz : π z = ↑v⁻¹ := by
    rw [map_mul, hw, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  obtain ⟨z', hz'⟩ := hπ ↑v
  have hzu : IsUnit z := isUnit_of_mul_sub_one_mem (RingHom.ker π) (fun x hx => hker x hx)
    (a' := z') (by simp [RingHom.mem_ker, hπz, hz']) (by simp [RingHom.mem_ker, hπz, hz'])
  obtain ⟨m, hm⟩ := hn.mul hzu
  set b := ∑ q : Γ ⧸ Λ, (c q.out : A) * q.out • z
  set x := b - m
  have hx : π x = 0 := by
    have : ∀ s : Γ, π ((c s : A) * s • z) = ↑v⁻¹ := fun s => by
      rw [map_mul, hv, hequiv, hπz, mul_assoc, ← smul_mul', Units.mul_inv, smul_one, mul_one]
    have hm' : π (m : A) = (Λ.index : B) * ↑v⁻¹ := by rw [hm, map_mul, map_natCast, hπz]
    simp only [x, b, map_sub, map_sum, this, sum_const, card_univ, hm', nsmul_eq_mul,
      sub_eq_zero, Λ.index_eq_card, Nat.card_eq_fintype_card]
  have hb : b = m * (1 + ↑m⁻¹ * x) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul, add_sub_cancel]
  obtain ⟨b', hb'⟩ : IsUnit b := hb ▸ m.isUnit.mul (hker _ (by rw [map_mul, hx, mul_zero]))
  exact isCoboundary_of_fixed b' fun g => hb' ▸ mul_smul_sum_cosets hc Λ z hz g

end Sylow

section SylowLocal

variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A] [IsLocalRing O]
  {Γ B : Type*} [Group Γ] [Fintype Γ] [MulSemiringAction Γ A] [Ring B] [MulSemiringAction Γ B]

omit [Fintype Γ] [MulSemiringAction Γ A] in
/-- `p ∤ [Γ : Λ]` makes the index invertible in `A`. -/
theorem isUnit_index (Λ : Subgroup Γ) (hp : ¬ ringChar (ResidueField O) ∣ Λ.index) :
    IsUnit (Λ.index : A) := by
  have : IsUnit (Λ.index : O) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    exact fun h => hp ((ringChar.spec _ _).1 h)
  simpa using this.map (algebraMap O A)

/-- **Pages 90–92, the Sylow form** (forme reconstituée par l'édition): `A` finite over `𝒪`,
`π : A → B` onto with kernel in `𝔪A`, `Λ` of index prime to `p` and `A^Λ → B` onto. The kernel
of `H¹(Γ, A*) → H¹(Γ, B*) × H¹(Λ, A*)` is trivial. -/
theorem ker_trivial_restrict [Module.Finite O A] (Λ : Subgroup Γ)
    (hp : ¬ ringChar (ResidueField O) ∣ Λ.index) (π : A →+* B) (hπ : Function.Surjective π)
    (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    (hker : ∀ x, π x = 0 → x ∈ maximalIdeal O • (⊤ : Submodule O A))
    (hlift : ∀ y, ∃ w, (∀ l ∈ Λ, l • w = w) ∧ π w = y) {c : Γ → Aˣ} (hc : IsCocycle c)
    (hΛ : ∃ u : Aˣ, ∀ l ∈ Λ, (c l : A) = ↑u⁻¹ * l • (u : A))
    (hπc : ∃ v : Bˣ, ∀ g, π (c g) = ↑v⁻¹ * g • (v : B)) : IsCoboundary c :=
  isCoboundary_of_restrict π hπ hequiv (fun x hx => isUnit_one_add_of_mem_smul_top (hker x hx))
    Λ (isUnit_index Λ hp) hlift hc hΛ hπc

/-- The statement of page 90 with `Λ` a Sylow `p`-subgroup, `p` the residue characteristic. -/
theorem ker_trivial_sylow [Module.Finite O A] [Fact (ringChar (ResidueField O)).Prime]
    (Λ : Sylow (ringChar (ResidueField O)) Γ) (π : A →+* B) (hπ : Function.Surjective π)
    (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    (hker : ∀ x, π x = 0 → x ∈ maximalIdeal O • (⊤ : Submodule O A))
    (hlift : ∀ y, ∃ w, (∀ l ∈ (Λ : Subgroup Γ), l • w = w) ∧ π w = y) {c : Γ → Aˣ}
    (hc : IsCocycle c) (hΛ : ∃ u : Aˣ, ∀ l ∈ (Λ : Subgroup Γ), (c l : A) = ↑u⁻¹ * l • (u : A))
    (hπc : ∃ v : Bˣ, ∀ g, π (c g) = ↑v⁻¹ * g • (v : B)) : IsCoboundary c :=
  ker_trivial_restrict (Λ : Subgroup Γ) Λ.not_dvd_index π hπ hequiv hker hlift hc hΛ hπc

end SylowLocal

end Grothendieck.Folder46

/-!
## Folder 46, pages 84–89: Hilbert 90 relative to the inertia

Page 84 claims, for `𝒪` semi-local noetherian, `Γ` finite acting transitively on its maximal
ideals and `A` a finite `𝒪`-algebra with semilinear `Γ`-action, that
`H¹(Γ, A*) → H¹(Γ_d, A_𝔪*) → H¹(Γ_i, A_𝔪*)` are injective. Pages 86–89 treat the second arrow
for `𝒪` local (`Γ = Γ_d`): twist, inflation–restriction down to `Γ/Γ_i` acting on `A^{Γ_i}`
(admitting, « on sait que », that `Γ/Γ_i` is faithful on the residue field of `𝒪^{Γ_i}`), then
the case `Γ_i = {e}` by the field case of pages 82–83 and a dévissage along `𝔪ⁿA` closed by
Artin–Rees.

This part proves the second arrow for `𝒪` local when the residue field `k` is infinite and
`|Γ_i|` is invertible in `k` (tame inertia), with no hypothesis of normality, no passage to
`𝒪^{Γ_i}`, no dévissage and no Artin–Rees:
* `sum_inertia_eq_zero`: Dedekind's independence of characters, grouped along the fibres of
  `Γ → Aut k`; `exists_sum_smul_ne_zero`: the trace `k → k` is nonzero when `|Γ_i| ≠ 0` in `k`;
* `mem_span_fixed`: Speiser's lemma for the twisted action `x ↦ c'(γ) γ(x) c(γ)⁻¹` on a
  `k`-algebra `B`: an element fixed by `Γ_i` lies in the `k`-span of the elements fixed by `Γ`;
* `isCohomologous_of_eqOn_inertia`: for `B` finite-dimensional over infinite `k`, two cocycles
  `Γ → B*` that agree on `Γ_i` are cohomologous (with `Γ_i = {e}`: `H¹(Γ, B*) = 1`, the field
  case of pages 82–83, for any finite `k`-algebra): a `k^Γ`-combination of invariants that is a
  unit, found by evaluating `det(y ↦ xy)` off its zero set (`k^Γ` is infinite);
* `exists_sum_smul_eq_one`, `isCohomologous_of_map_of_sum_eq_one`: an element `λ ∈ 𝒪` with
  `Σ_σ σ(λ) = 1` lifts cohomology classes from `B = A/𝔪A` to `A` in one average,
  `u = Σ_σ c'(σ) σ(λw) c(σ)⁻¹`, which replaces the dévissage and Artin–Rees;
* `isCohomologous_of_restrict_inertia`: `H¹(Γ, A*) → H¹(Γ_i, A*)` is injective;
  `isCohomologous_of_faithful`: `H¹(Γ, A*) = 1` when `Γ_i = {e}`.

Not formalised: the semi-local base and the first arrow (completion, Shapiro's lemma,
localisation `A_𝔪`), wild inertia (`p ∣ |Γ_i|`, where the page passes to `𝒪^{Γ_i}` and admits the
« on sait que »), and a finite residue field (Lang's theorem).
-/


namespace Grothendieck.Folder46

section Inertia

variable {Γ k : Type*} [Group Γ] [Fintype Γ] [Field k] [MulSemiringAction Γ k]

variable (Γ k) in
/-- The inertia group, as a finite set: the elements of `Γ` acting trivially on `k`. -/
noncomputable def inertia : Finset Γ := by
  classical exact univ.filter fun g => ∀ μ : k, g • μ = μ

theorem mem_inertia {g : Γ} : g ∈ inertia Γ k ↔ ∀ μ : k, g • μ = μ := by
  unfold inertia; simp

/-- Dedekind's independence of characters, grouped by fibres: if `Σ_σ a(σ) σ(μ) = 0` for every
`μ ∈ k`, the coefficients over the inertia (the fibre of the identity) sum to `0`. -/
theorem sum_inertia_eq_zero (a : Γ → k) (h : ∀ μ : k, ∑ s, a s * s • μ = 0) :
    ∑ s ∈ inertia Γ k, a s = 0 := by
  classical
  let φ : Γ → (k →* k) := fun s => (MulSemiringAction.toRingHom Γ k s : k →* k)
  have hli := linearIndependent_iff'.1 (linearIndependent_monoidHom k k)
  have key : ∑ ψ ∈ univ.image φ, (∑ s ∈ univ.filter (fun s => φ s = ψ), a s) • (ψ : k → k)
      = 0 := by
    calc _ = ∑ ψ ∈ univ.image φ, ∑ s ∈ univ.filter (fun s => φ s = ψ), a s • (φ s : k → k) := by
          refine sum_congr rfl fun ψ _ => ?_
          rw [sum_smul]
          refine sum_congr rfl fun s hs => ?_
          rw [(mem_filter.1 hs).2]
      _ = ∑ s, a s • (φ s : k → k) :=
          sum_fiberwise_of_maps_to (fun s _ => mem_image_of_mem φ (mem_univ s)) _
      _ = 0 := funext fun μ => by simpa [φ] using h μ
  have := hli _ _ key (φ 1) (mem_image_of_mem φ (mem_univ 1))
  rw [← this]
  refine sum_congr ?_ fun _ _ => rfl
  ext s
  simp only [mem_inertia, mem_filter, mem_univ, true_and, φ, MonoidHom.ext_iff]
  simp

/-- When `|Γ_i|` is invertible in `k`, the trace `μ ↦ Σ_σ σ(μ)` is not identically zero. -/
theorem exists_sum_smul_ne_zero (hN : ((inertia Γ k).card : k) ≠ 0) :
    ∃ μ : k, ∑ s : Γ, s • μ ≠ 0 := by
  by_contra! h
  apply hN
  have := sum_inertia_eq_zero (fun _ => (1 : k)) (fun μ => by simpa using h μ)
  simpa using this

variable {B : Type*} [Ring B] [Algebra k B] [MulSemiringAction Γ B]

/-- **Speiser's lemma, twisted.** For cocycles `c, c'` and `B` a `k`-algebra with semilinear
`Γ`-action, every `v` fixed by the inertia for the twisted action `x ↦ c'(γ) γ(x) c(γ)⁻¹` lies in
the `k`-span of the elements fixed by all of `Γ`, when `|Γ_i|` is invertible in `k`. -/
theorem mem_span_fixed (hB : ∀ (g : Γ) (μ : k), g • algebraMap k B μ = algebraMap k B (g • μ))
    (hN : ((inertia Γ k).card : k) ≠ 0) {c c' : Γ → Bˣ} (hc : IsCocycle c) (hc' : IsCocycle c')
    {v : B} (hv : ∀ n ∈ inertia Γ k, (c' n : B) * n • v * ↑(c n)⁻¹ = v) :
    v ∈ Submodule.span k {x : B | ∀ g, (c' g : B) * g • x = x * c g} := by
  by_contra hv'
  obtain ⟨f, hfv, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv' inferInstance
  have hf0 : ∀ x ∈ Submodule.span k {x : B | ∀ g, (c' g : B) * g • x = x * c g}, f x = 0 :=
    fun x hx => by simpa [hf] using Submodule.mem_map_of_mem (f := f) hx
  apply hfv
  have key : ∀ μ : k, ∑ s, f ((c' s : B) * s • v * ↑(c s)⁻¹) * s • μ = 0 := by
    intro μ
    have hmem : ∑ s, (c' s : B) * s • (algebraMap k B μ * v) * ↑(c s)⁻¹ ∈
        {x : B | ∀ g, (c' g : B) * g • x = x * c g} := fun g =>
      mul_smul_sum_twist hc hc' _ g
    rw [← hf0 _ (Submodule.subset_span hmem), map_sum]
    refine sum_congr rfl fun s _ => ?_
    have e : (c' s : B) * s • (algebraMap k B μ * v) * ↑(c s)⁻¹ =
        (s • μ) • ((c' s : B) * s • v * ↑(c s)⁻¹) := by
      rw [smul_mul', hB, Algebra.smul_def]
      simp only [mul_assoc]
      rw [← mul_assoc (c' s : B), ← Algebra.commutes, mul_assoc]
    rw [e, map_smul, smul_eq_mul, mul_comm]
  have := sum_inertia_eq_zero _ key
  rw [sum_congr rfl fun n hn => by rw [hv n hn], sum_const, nsmul_eq_mul] at this
  exact (mul_eq_zero.1 this).resolve_left hN

theorem isCocycle_one_eq {Γ A : Type*} [Group Γ] [Ring A] [MulSemiringAction Γ A]
    {c : Γ → Aˣ} (hc : IsCocycle c) : c 1 = 1 := by
  have h := hc 1 1
  rw [mul_one, one_smul] at h
  exact mul_eq_left.1 (Units.ext h.symm)

/-- The fixed field `k^Γ` is infinite when `k` is (`[k : k^Γ] ≤ |Γ|`). -/
theorem infinite_fixedPoints [Infinite k] :
    (FixedPoints.subfield Γ k : Set k).Infinite := by
  rw [← Set.infinite_coe_iff]
  by_contra h
  rw [not_infinite_iff_finite] at h
  have : Finite k := Module.finite_of_finite (FixedPoints.subfield Γ k)
  exact not_finite k

/-- A finite-dimensional `k`-algebra: `x` is a unit as soon as `det(y ↦ xy) ≠ 0`. -/
theorem isUnit_of_det_mulLeft_ne_zero [FiniteDimensional k B] {x : B}
    (h : LinearMap.det (LinearMap.mulLeft k x) ≠ 0) : IsUnit x := by
  obtain ⟨φ, hφ⟩ := (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  set y := (↑φ⁻¹ : Module.End k B) 1
  have h1 : x * y = 1 := by
    change LinearMap.mulLeft k x y = 1
    rw [← hφ]
    change ((φ * φ⁻¹ : (Module.End k B)ˣ) : Module.End k B) 1 = 1
    rw [mul_inv_cancel]; rfl
  have hy : (↑φ⁻¹ : Module.End k B) = LinearMap.mulLeft k y := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hφ]
    ext z
    simp [← mul_assoc, h1]
  have h2 : y * x = 1 := by
    have : (↑φ⁻¹ : Module.End k B) ((φ : Module.End k B) 1) = 1 := by
      change ((φ⁻¹ * φ : (Module.End k B)ˣ) : Module.End k B) 1 = 1
      rw [inv_mul_cancel]; rfl
    rw [hy, hφ] at this
    simpa using this
  exact ⟨⟨x, y, h1, h2⟩, rfl⟩

/-- **Hilbert 90 for finite algebras over an infinite field, relative to the inertia** (the field
case of pages 82–83 used on page 88): two cocycles `Γ → B*` that agree on the inertia are
cohomologous, when `|Γ_i|` is invertible in `k`. With `Γ` faithful on `k`, `H¹(Γ, B*) = 1`. -/
theorem isCohomologous_of_eqOn_inertia [Infinite k] [FiniteDimensional k B]
    (hB : ∀ (g : Γ) (μ : k), g • algebraMap k B μ = algebraMap k B (g • μ))
    (hN : ((inertia Γ k).card : k) ≠ 0) {c c' : Γ → Bˣ} (hc : IsCocycle c) (hc' : IsCocycle c')
    (hcc' : ∀ n ∈ inertia Γ k, c n = c' n) :
    ∃ u : Bˣ, ∀ g, (c g : B) = ↑u⁻¹ * c' g * g • (u : B) := by
  set X := {x : B | ∀ g, (c' g : B) * g • x = x * c g}
  have h1 : (1 : B) ∈ Submodule.span k X :=
    mem_span_fixed hB hN hc hc' fun n hn => by rw [smul_one, mul_one, hcc' n hn, Units.mul_inv]
  obtain ⟨n, t, e, he⟩ := Submodule.mem_span_set'.1 h1
  let b := Module.finBasis k B
  let M : Fin n → Matrix (Fin (Module.finrank k B)) (Fin (Module.finrank k B)) k :=
    fun i => LinearMap.toMatrix b b (LinearMap.mulLeft k (e i : B))
  let P : MvPolynomial (Fin n) k := (∑ i, (MvPolynomial.X i : MvPolynomial (Fin n) k) • (M i).map MvPolynomial.C).det
  have heval : ∀ x : Fin n → k,
      MvPolynomial.eval x P = LinearMap.det (LinearMap.mulLeft k (∑ i, x i • (e i : B))) := by
    intro x
    rw [← LinearMap.det_toMatrix b, RingHom.map_det]
    congr 1
    have : LinearMap.mulLeft k (∑ i, x i • (e i : B)) = ∑ i, x i • LinearMap.mulLeft k (e i : B) := by
      ext; simp [sum_mul]
    rw [this, map_sum]
    ext p q
    simp [M, Matrix.sum_apply]
  have hP1 : MvPolynomial.eval t P = 1 := by rw [heval, he]; simp
  obtain ⟨x, hx, hPx⟩ : ∃ x ∈ Set.pi Set.univ fun _ : Fin n => (FixedPoints.subfield Γ k : Set k),
      MvPolynomial.eval x P ≠ 0 := by
    by_contra! h
    have := MvPolynomial.funext_set _ (fun _ => infinite_fixedPoints (Γ := Γ)) (p := P) (q := 0)
      (by simpa using h)
    rw [this] at hP1
    simp at hP1
  rw [heval] at hPx
  obtain ⟨u, hu⟩ := isUnit_of_det_mulLeft_ne_zero hPx
  have hfix : ∀ g, (c' g : B) * g • (u : B) = u * c g := by
    intro g
    rw [hu, smul_sum, mul_sum, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    have hxi : g • x i = x i := hx i (Set.mem_univ i) g
    rw [Algebra.smul_def, smul_mul', hB, hxi, Algebra.left_comm, (e i).2 g, mul_assoc]
  refine ⟨u, fun g => ?_⟩
  rw [mul_assoc, hfix, ← mul_assoc, Units.inv_mul, one_mul]

end Inertia

section TraceOne

variable {Γ O A B : Type*} [Group Γ] [Fintype Γ] [CommRing O] [MulSemiringAction Γ O]
  [Ring A] [Algebra O A] [MulSemiringAction Γ A] [Ring B] [MulSemiringAction Γ B]

/-- **Lifting along `π : A → B` with an element of trace one.** If `λ ∈ 𝒪` has
`Σ_σ σ(λ) = 1`, then `H¹(Γ, A*) → H¹(Γ, B*)` is injective for a surjective equivariant
`π : A → B` with `1 + Ker π ⊂ Aˣ`: the average `u = Σ_σ c'(σ) σ(λw) c(σ)⁻¹` lifts the given
`v = π(w)`. With `λ = 1/|Γ|` this is `isCohomologous_of_map`. -/
theorem isCohomologous_of_map_of_sum_eq_one
    (hO : ∀ (g : Γ) (a : O), g • algebraMap O A a = algebraMap O A (g • a))
    {l : O} (hl : ∑ s : Γ, s • l = 1) (π : A →+* B) (hπ : Function.Surjective π)
    (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    (hker : ∀ x, π x = 0 → IsUnit (1 + x))
    {c c' : Γ → Aˣ} (hc : IsCocycle c) (hc' : IsCocycle c')
    (hπc : ∃ v : Bˣ, ∀ g, π (c g) = ↑v⁻¹ * π (c' g) * g • (v : B)) :
    ∃ u : Aˣ, ∀ g, (c g : A) = ↑u⁻¹ * c' g * g • (u : A) := by
  obtain ⟨v, hv⟩ := hπc
  obtain ⟨w, hw⟩ := hπ ↑v
  obtain ⟨w', hw'⟩ := hπ ↑v⁻¹
  have hwu : IsUnit w := isUnit_of_mul_sub_one_mem (RingHom.ker π) (fun x hx => hker x hx)
    (a' := w') (by simp [RingHom.mem_ker, hw, hw']) (by simp [RingHom.mem_ker, hw, hw'])
  refine isCohomologous_of_isUnit_sum hc hc' (algebraMap O A l * w) ?_
  set u := ∑ s, (c' s : A) * s • (algebraMap O A l * w) * ↑(c s)⁻¹
  have hs : ∀ s : Γ, π ((c' s : A) * s • w * ↑(c s)⁻¹) = ↑v := fun s => by
    have h1 : π (c s) * π ↑(c s)⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    rw [hv s] at h1
    rw [map_mul, map_mul, hequiv, hw]
    calc π (c' s) * s • (v : B) * π ↑(c s)⁻¹
        = ↑v * (↑v⁻¹ * π (c' s) * s • (v : B) * π ↑(c s)⁻¹) := by
          simp only [← mul_assoc, Units.mul_inv, one_mul]
      _ = ↑v := by rw [h1, mul_one]
  have hu : π u = π w := by
    have : u = ∑ s, algebraMap O A (s • l) * ((c' s : A) * s • w * ↑(c s)⁻¹) := by
      refine sum_congr rfl fun s _ => ?_
      rw [smul_mul', hO, Algebra.left_comm, mul_assoc]
    rw [this, map_sum, sum_congr rfl fun s _ => by rw [map_mul, hs], ← sum_mul, ← map_sum,
      ← map_sum, hl, map_one, map_one, one_mul, hw]
  obtain ⟨W, rfl⟩ := hwu
  have : u = W * (1 + ↑W⁻¹ * (u - W)) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul, add_sub_cancel]
  rw [this]
  exact W.isUnit.mul (hker _ (by rw [map_mul, map_sub, hu, sub_self, mul_zero]))

variable [IsLocalRing O]

/-- **An element of trace one.** For `𝒪` local and `|Γ_i|` invertible in the residue field `k`,
there is `λ ∈ 𝒪` with `Σ_σ σ(λ) = 1`: a `μ ∈ k` of nonzero trace (Dedekind) lifted, divided by
its trace, a `Γ`-invariant unit. -/
theorem exists_sum_smul_eq_one (hN : ((inertia Γ (ResidueField O)).card : ResidueField O) ≠ 0) :
    ∃ l : O, ∑ s : Γ, s • l = 1 := by
  obtain ⟨μ, hμ⟩ := exists_sum_smul_ne_zero hN
  obtain ⟨l₀, rfl⟩ := residue_surjective μ
  set t := ∑ s : Γ, s • l₀
  have ht : IsUnit t := by
    rw [← residue_ne_zero_iff_isUnit, map_sum]
    simpa using hμ
  have hg : ∀ g : Γ, g • t = t := fun g => by
    rw [smul_sum]
    simp_rw [smul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft g) fun s => s • l₀
  obtain ⟨T, hT⟩ := ht
  refine ⟨l₀ * ↑T⁻¹, ?_⟩
  have hTi : ∀ g : Γ, g • (↑T⁻¹ : O) = ↑T⁻¹ := fun g => by
    have h : g • (↑T⁻¹ : O) * T = 1 := by
      rw [hT, ← hg g, ← hT, ← smul_mul', Units.inv_mul, smul_one]
    calc g • (↑T⁻¹ : O) = g • (↑T⁻¹ : O) * T * ↑T⁻¹ := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = ↑T⁻¹ := by rw [h, one_mul]
  simp_rw [smul_mul', hTi, ← sum_mul]
  rw [show (∑ i : Γ, i • l₀) = T from hT.symm, Units.mul_inv]

end TraceOne

section InertiaLocal

variable {Γ O A B : Type*} [Group Γ] [Fintype Γ] [CommRing O] [IsLocalRing O]
  [MulSemiringAction Γ O] [Ring A] [Algebra O A] [MulSemiringAction Γ A]
  [Ring B] [Algebra (ResidueField O) B] [MulSemiringAction Γ B]

omit [Fintype Γ] in
/-- A cocycle twisted by a unit, `g ↦ u⁻¹ c(g) g(u)`, is a cocycle. -/
theorem isCocycle_twist {c : Γ → Aˣ} (hc : IsCocycle c) (u : Aˣ) :
    IsCocycle fun g => u⁻¹ * c g * Units.map (MulSemiringAction.toRingHom Γ A g : A →* A) u := by
  intro g h
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, MulSemiringAction.toRingHom_apply,
    smul_mul', hc g h, mul_smul, mul_assoc]
  congr 2
  rw [← mul_assoc (g • (u : A)), ← smul_mul' g (u : A), Units.mul_inv, smul_one, one_mul]

omit [Fintype Γ] in
/-- The image of a cocycle under an equivariant ring map is a cocycle. -/
theorem isCocycle_map (π : A →+* B) (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    {c : Γ → Aˣ} (hc : IsCocycle c) : IsCocycle fun g => Units.map (π : A →* B) (c g) := by
  intro g h
  simp only [Units.coe_map, MonoidHom.coe_ofClass, hc g h, map_mul, hequiv]

/-- **Pages 86–89, the second arrow, local case with tame inertia and infinite residue
field: `H¹(Γ_d, A*) → H¹(Γ_i, A*)` is injective.** Let `𝒪` be local with residue field `k`
infinite, `Γ` finite acting on `𝒪` (so `Γ = Γ_d`), `Γ_i` the inertia (acting trivially on `k`)
with `|Γ_i|` invertible in `k`, `A` a finite `𝒪`-algebra, not necessarily commutative, with
semilinear `Γ`-action, and `π : A → B` onto `B = A/𝔪A` (any surjective equivariant map to a
finite-dimensional `k`-algebra with semilinear action, with kernel in `𝔪A`). Two cocycles
`Γ → A*` cohomologous on `Γ_i` are cohomologous on `Γ`. -/
theorem isCohomologous_of_restrict_inertia [Module.Finite O A] [Infinite (ResidueField O)]
    [FiniteDimensional (ResidueField O) B]
    (hO : ∀ (g : Γ) (a : O), g • algebraMap O A a = algebraMap O A (g • a))
    (hB : ∀ (g : Γ) (μ : ResidueField O),
      g • algebraMap (ResidueField O) B μ = algebraMap (ResidueField O) B (g • μ))
    (hN : ((inertia Γ (ResidueField O)).card : ResidueField O) ≠ 0)
    (π : A →+* B) (hπ : Function.Surjective π) (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    (hker : ∀ x, π x = 0 → x ∈ maximalIdeal O • (⊤ : Submodule O A))
    {c c' : Γ → Aˣ} (hc : IsCocycle c) (hc' : IsCocycle c')
    (hres : ∃ u₀ : Aˣ, ∀ n ∈ inertia Γ (ResidueField O),
      (c n : A) = ↑u₀⁻¹ * c' n * n • (u₀ : A)) :
    ∃ u : Aˣ, ∀ g, (c g : A) = ↑u⁻¹ * c' g * g • (u : A) := by
  obtain ⟨u₀, hu₀⟩ := hres
  set c'' := fun g => u₀⁻¹ * c' g * Units.map (MulSemiringAction.toRingHom Γ A g : A →* A) u₀
  have hc'' : IsCocycle c'' := isCocycle_twist hc' u₀
  have hval : ∀ g, (c'' g : A) = ↑u₀⁻¹ * c' g * g • (u₀ : A) := fun g => by
    simp [c'']
  obtain ⟨v, hv⟩ := isCohomologous_of_eqOn_inertia hB hN (isCocycle_map π hequiv hc)
    (isCocycle_map π hequiv hc'') fun n hn => by
      ext; simp only [Units.coe_map, MonoidHom.coe_ofClass, hu₀ n hn, hval]
  obtain ⟨l, hl⟩ := exists_sum_smul_eq_one hN
  obtain ⟨u, hu⟩ := isCohomologous_of_map_of_sum_eq_one hO hl π hπ hequiv
    (fun x hx => isUnit_one_add_of_mem_smul_top (hker x hx)) hc hc''
    ⟨v, fun g => by simpa using hv g⟩
  refine ⟨u₀ * u, fun g => ?_⟩
  rw [hu, hval, mul_inv_rev, Units.val_mul, Units.val_mul, smul_mul']
  simp only [mul_assoc]

/-- **The case `Γ_i = {e}` (page 88): `H¹(Γ, A*) = 1`.** If `Γ` acts faithfully on the infinite
residue field `k`, any two cocycles `Γ → A*` are cohomologous. No dévissage along `𝔪ⁿ` and no
Artin–Rees: an element of trace one in `𝒪` lifts the field case in one average. -/
theorem isCohomologous_of_faithful [Module.Finite O A] [Infinite (ResidueField O)]
    [FaithfulSMul Γ (ResidueField O)] [FiniteDimensional (ResidueField O) B]
    (hO : ∀ (g : Γ) (a : O), g • algebraMap O A a = algebraMap O A (g • a))
    (hB : ∀ (g : Γ) (μ : ResidueField O),
      g • algebraMap (ResidueField O) B μ = algebraMap (ResidueField O) B (g • μ))
    (π : A →+* B) (hπ : Function.Surjective π) (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    (hker : ∀ x, π x = 0 → x ∈ maximalIdeal O • (⊤ : Submodule O A))
    {c c' : Γ → Aˣ} (hc : IsCocycle c) (hc' : IsCocycle c') :
    ∃ u : Aˣ, ∀ g, (c g : A) = ↑u⁻¹ * c' g * g • (u : A) := by
  have h1 : inertia Γ (ResidueField O) = {1} := by
    ext g
    simp only [mem_inertia, mem_singleton]
    refine ⟨fun h => FaithfulSMul.eq_of_smul_eq_smul fun μ => by rw [h, one_smul], ?_⟩
    rintro rfl μ
    exact one_smul _ μ
  refine isCohomologous_of_restrict_inertia hO hB (by simp [h1]) π hπ hequiv hker hc hc'
    ⟨1, fun n hn => ?_⟩
  rw [h1, mem_singleton] at hn
  subst hn
  simp [isCocycle_one_eq hc, isCocycle_one_eq hc']

end InertiaLocal

end Grothendieck.Folder46
