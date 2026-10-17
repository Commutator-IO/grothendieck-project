import Mathlib

/-!
# Folder 140-1, page 22: the bound on `H¹(U_{0,3}, 𝔖₃; 𝔾_m)`

The modernised reading `transcripts/140-1/140-1.modern.tex` (« Le lemme :
`H¹(U_{0,3}, 𝔖₃; 𝔾_m) ≃ ℤ/6` ») gives the boxed lemma of page 22: for `S` regular integral
with `Pic(S) = 0`, the group of `𝔖₃`-equivariant `𝔾_m`-torsors on `U_{0,3} = ℙ¹ − {0, 1, ∞}`
is `ℤ/6`, and `ℤ/3` in generic characteristic `2`. A marginal note bounds it by two exact
sequences: the equivariant `H¹` is `H¹(𝔖₃, O(U_{0,3})^*)`, and
`0 → O(S)^* → O(U_{0,3})^* → V(J) → 0` with `V(J) = Ker(ℤ^J → ℤ)` the divisors of the units.
The reading adds the computations the page does not write: `H¹(𝔖₃, O(S)^*) = μ₂(S)` and
`H¹(𝔖₃, V(J)) = ℤ/3`, hence an order dividing `6` (resp. `3`). This is the reachable part of
finding `140-1-equivariant-pic-u03` of `src/content/findings.ts`.

`H¹` is mathlib's group cohomology `groupCohomology.H1` of the representation
`Rep.ofDistribMulAction ℤ G M`; `H1Equiv` identifies it with cocycles modulo coboundaries
(`Z1`, `B1`, `Q`), where the work is done.

* `exact_mapQ`, `card_dvd_of_exact`: for a short exact sequence `0 → A → M → N → 0` of
  `G`-modules, `H¹(A) → H¹(M) → H¹(N)` is exact in the middle, so `|H¹(M)|` divides
  `|H¹(A)| |H¹(N)|`.
* `card_H1_VJ` (with `H1_VJ`): `H¹(𝔖₃, V(J)) ≃ ℤ/3`. A cocycle `f` with values in `V(J)` is the
  coboundary, in `ℤ^J`, of its potential `m_j = −f(τ_j)_j` (`τ_j` the transposition of `0` and
  `j`, `cocycle_eq_pot`): this is `H¹(𝔖₃, ℤ^J) = 0` made explicit; its class is `∑ m_j mod 3`.
* `card_H1_triv`, `card_mu2_dvd`, `card_mu2_char_two`: for `k` a domain and the trivial
  action, `H¹(𝔖₃, k^*) = Hom(𝔖₃, k^*) = μ₂(k)`, of order dividing `2`, and `1` if `2 = 0`.
* `card_H1_dvd`: the « majoration » — for every extension `0 → k^* → M → V(J) → 0` of
  `𝔖₃`-modules, `|H¹(𝔖₃, M)|` divides `6`, and `3` if `2 = 0` in `k`.

Not formalised: that `O(U_{0,3})^*` is such an extension (the units of `U_{0,3}`),
`Pic(U_{0,3}) = 0` and the Hochschild–Serre sequence, and the lower bound — the class of
`O(1)` of order exactly `6` (resp. `3`), page 24.
-/

namespace Grothendieck.Folder140_1

open groupCohomology

/-! ## Cocycles modulo coboundaries -/

section General

variable {G : Type} [Group G]

/-- The `ℤ`-linear representation of `G` on an abelian group with a distributive action. -/
abbrev R (G M : Type) [Group G] [AddCommGroup M] [DistribMulAction G M] : Rep ℤ G :=
  Rep.ofDistribMulAction ℤ G M

variable {M N : Type} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup N]
  [DistribMulAction G N]

variable (G M) in
/-- The 1-cocycles `f(gh) = g f(h) + f(g)`. -/
def Z1 : AddSubgroup (G → M) where
  carrier := {f | IsCocycle₁ f}
  add_mem' {f f'} hf hf' g h := by
    simp only [Pi.add_apply, hf g h, hf' g h, smul_add]; abel
  zero_mem' g h := by simp
  neg_mem' {f} hf g h := by simp only [Pi.neg_apply, hf g h, smul_neg]; abel

lemma Z1_apply_mul (f : Z1 G M) (g h : G) : (f : G → M) (g * h) = g • f.1 h + f.1 g := f.2 g h

variable (G M) in
/-- The 1-coboundaries `g ↦ g m - m`, inside the cocycles. -/
def B1 : AddSubgroup (Z1 G M) where
  carrier := {f | IsCoboundary₁ (f : G → M)}
  add_mem' {f f'} hf hf' := by
    obtain ⟨x, hx⟩ := hf
    obtain ⟨x', hx'⟩ := hf'
    refine ⟨x + x', fun g => ?_⟩
    change g • (x + x') - (x + x') = (f : G → M) g + (f' : G → M) g
    rw [smul_add, ← hx, ← hx']
    abel
  zero_mem' := ⟨0, fun g => by simp⟩
  neg_mem' {f} hf := by
    obtain ⟨x, hx⟩ := hf
    refine ⟨-x, fun g => ?_⟩
    change g • (-x) - (-x) = -(f : G → M) g
    rw [smul_neg, ← hx]
    abel

variable (G M) in
/-- `Z¹ / B¹`. -/
abbrev Q := Z1 G M ⧸ B1 G M

/-- Mathlib's cocycles are these cocycles. -/
def cocyclesEquiv : cocycles₁ (R G M) ≃+ Z1 G M where
  toFun f := ⟨f.1, isCocycle₁_of_mem_cocycles₁ _ f.2⟩
  invFun f := ⟨f.1, (cocyclesOfIsCocycle₁ (k := ℤ) f.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable (G M) in
/-- `H¹(G, M)` (Mathlib's, for the representation on `M`) is cocycles modulo coboundaries. -/
noncomputable def H1Equiv : Q G M ≃+ H1 (R G M) :=
  let ψ : Z1 G M →+ H1 (R G M) :=
    (H1π (R G M)).hom.toAddMonoidHom.comp (cocyclesEquiv (G := G) (M := M)).symm.toAddMonoidHom
  have hψ : Function.Surjective ψ := fun y => by
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective (H1π (R G M))).1 inferInstance y
    exact ⟨cocyclesEquiv x, by simpa [ψ] using hx⟩
  have hk : ψ.ker = B1 G M := by
    ext f
    change (H1π (R G M)) (cocyclesEquiv.symm f) = 0 ↔ IsCoboundary₁ (f : G → M)
    rw [H1π_eq_zero_iff]
    exact ⟨isCoboundary₁_of_mem_coboundaries₁ _,
      fun h => (coboundariesOfIsCoboundary₁ (k := ℤ) h).2⟩
  (QuotientAddGroup.quotientAddEquivOfEq hk.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ)

lemma card_H1 : Nat.card (H1 (R G M)) = Nat.card (Q G M) :=
  (Nat.card_congr (H1Equiv G M).toEquiv).symm

/-- A `G`-map `M → N` on cocycles. -/
def mapZ (φ : M →+ N) (hφ : ∀ (g : G) m, φ (g • m) = g • φ m) : Z1 G M →+ Z1 G N where
  toFun f := ⟨φ ∘ f, fun g h => by simp [Z1_apply_mul, hφ]⟩
  map_zero' := by ext; simp
  map_add' f f' := by ext; simp

@[simp] lemma mapZ_apply (φ : M →+ N) (hφ : ∀ (g : G) m, φ (g • m) = g • φ m)
    (f : Z1 G M) (g : G) : (mapZ φ hφ f : G → N) g = φ ((f : G → M) g) := rfl

/-- A `G`-map `M → N` on `Z¹/B¹`. -/
def mapQ (φ : M →+ N) (hφ : ∀ (g : G) m, φ (g • m) = g • φ m) : Q G M →+ Q G N :=
  QuotientAddGroup.map _ _ (mapZ φ hφ) fun f hf => by
    obtain ⟨x, hx⟩ := hf
    exact ⟨φ x, fun g => by simp [← hx, hφ]⟩

variable {A : Type} [AddCommGroup A] [DistribMulAction G A]

/-- Exactness in the middle of `H¹(A) → H¹(M) → H¹(N)` for a short exact sequence of
`G`-modules. -/
theorem exact_mapQ (i : A →+ M) (p : M →+ N) (hi : ∀ (g : G) a, i (g • a) = g • i a)
    (hp : ∀ (g : G) m, p (g • m) = g • p m) (hinj : Function.Injective i)
    (hsurj : Function.Surjective p) (hex : ∀ m, p m = 0 ↔ ∃ a, i a = m) :
    (mapQ p hp).ker = (mapQ i hi).range := by
  ext x
  induction x using QuotientAddGroup.induction_on with | H f
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  change (QuotientAddGroup.mk (mapZ p hp f) : Q G N) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨m, rfl⟩ := hsurj v
    have h0 : ∀ g, p ((f : G → M) g - (g • m - m)) = 0 := fun g => by
      have := hv g
      simp only [mapZ_apply] at this
      rw [map_sub, map_sub, hp, this, sub_self]
    choose a ha using fun g => (hex _).1 (h0 g)
    have hac : IsCocycle₁ a := fun g h => hinj (by
      rw [map_add, hi, ha, ha, ha, Z1_apply_mul, mul_smul]; simp only [smul_sub]; abel)
    refine ⟨QuotientAddGroup.mk ⟨a, hac⟩, ?_⟩
    change (QuotientAddGroup.mk (mapZ i hi ⟨a, hac⟩) : Q G M) = QuotientAddGroup.mk f
    rw [QuotientAddGroup.eq]
    exact ⟨m, fun g => by
      change _ = -i (a g) + (f : G → M) g
      rw [ha]; abel⟩
  · rintro ⟨y, hy⟩
    induction y using QuotientAddGroup.induction_on with | H a
    change (QuotientAddGroup.mk (mapZ i hi a) : Q G M) = QuotientAddGroup.mk f at hy
    rw [QuotientAddGroup.eq] at hy
    obtain ⟨m, hm⟩ := hy
    refine ⟨p m, fun g => ?_⟩
    have := congrArg p (hm g)
    change p (g • m - m) = p (-i ((a : G → A) g) + (f : G → M) g) at this
    have hpi : p (i ((a : G → A) g)) = 0 := (hex _).2 ⟨_, rfl⟩
    rw [← hp, ← map_sub, this, map_add, map_neg, hpi, neg_zero, zero_add]
    rfl

/-- In an exact sequence `P → Q' → S` of abelian groups, `|Q'|` divides `|P| |S|`. -/
lemma card_dvd_of_exact {P Q' S : Type} [AddCommGroup P] [AddCommGroup Q'] [AddCommGroup S]
    (α : P →+ Q') (β : Q' →+ S) (h : β.ker = α.range) :
    Nat.card Q' ∣ Nat.card P * Nat.card S := by
  rw [← AddSubgroup.card_ker_mul_card_range β, h]
  exact mul_dvd_mul (AddSubgroup.card_range_dvd α) (AddSubgroup.card_addSubgroup_dvd_card _)

end General

/-! ## `𝔖₃` and `V(J)` -/

/-- `𝔖₃ = 𝔖_J`, `J = {0, 1, 2}`. -/
abbrev G3 := Equiv.Perm (Fin 3)

/-- `V(J) = Ker(ℤ^J → ℤ)`, the divisors of the units of `U_{0,3}`. -/
def VJ : AddSubgroup (Fin 3 → ℤ) where
  carrier := {x | ∑ j, x j = 0}
  add_mem' {x y} hx hy := by simp_all [Finset.sum_add_distrib]
  zero_mem' := by simp
  neg_mem' {x} hx := by simp_all

lemma sum_perm (σ : G3) (x : Fin 3 → ℤ) : ∑ j, x (σ⁻¹ j) = ∑ j, x j :=
  Equiv.sum_comp σ⁻¹ x

/-- `𝔖₃` permutes the coordinates: `(σ x)_j = x_{σ⁻¹ j}`. -/
instance : DistribMulAction G3 VJ where
  smul σ x := ⟨fun j => (x : Fin 3 → ℤ) (σ⁻¹ j), by
    change ∑ j, _ = 0; rw [sum_perm]; exact x.2⟩
  one_smul x := rfl
  mul_smul σ τ x := by ext j; rfl
  smul_zero σ := rfl
  smul_add σ x y := rfl

@[simp] lemma smul_VJ (σ : G3) (x : VJ) (j : Fin 3) :
    ((σ • x : VJ) : Fin 3 → ℤ) j = (x : Fin 3 → ℤ) (σ⁻¹ j) := rfl

lemma stab_sq : ∀ s : G3, s 0 = 0 → s * s = 1 := by decide

/-- The potential `m_j = -f(swap 0 j)_j` of a cocycle. -/
def pot (f : G3 → VJ) (j : Fin 3) : ℤ := -(f (Equiv.swap 0 j) : Fin 3 → ℤ) j

/-- `H¹(𝔖₃, ℤ^J) = 0`, explicitly: a cocycle with values in `V(J)` is the coboundary of its
potential in `ℤ^J`. -/
lemma cocycle_eq_pot {f : G3 → VJ} (hf : IsCocycle₁ f) (g : G3) (j : Fin 3) :
    (f g : Fin 3 → ℤ) j = pot f (g⁻¹ j) - pot f j := by
  have h1 : f 1 = 0 := by
    have := hf 1 1; simp only [one_mul, one_smul] at this
    simpa using this
  have hs : ∀ s : G3, s 0 = 0 → (f s : Fin 3 → ℤ) 0 = 0 := fun s hs0 => by
    have := congrArg (fun x : VJ => (x : Fin 3 → ℤ) 0) (hf s s)
    have hinv : s⁻¹ 0 = 0 := by rw [Equiv.Perm.inv_eq_iff_eq, hs0]
    simp only [stab_sq s hs0, h1, AddSubgroup.coe_add, Pi.add_apply, smul_VJ, hinv,
      ZeroMemClass.coe_zero, Pi.zero_apply] at this
    omega
  set k := g⁻¹ j
  set s : G3 := (Equiv.swap 0 j)⁻¹ * g * Equiv.swap 0 k with hsdef
  have hs0 : s 0 = 0 := by
    simp [hsdef, k, Equiv.swap_inv]
  have hgs : g * Equiv.swap 0 k = Equiv.swap 0 j * s := by
    simp [hsdef, ← mul_assoc]
  have hf' : ∀ g h, f (g * h) = g • f h + f g := hf
  have e := congrArg (fun x : VJ => (x : Fin 3 → ℤ) j) (congrArg f hgs)
  simp only [hf', AddSubgroup.coe_add, Pi.add_apply, smul_VJ, Equiv.swap_inv,
    Equiv.swap_apply_right, hs s hs0] at e
  simp only [pot, k] at e ⊢
  omega

/-- The class of a cocycle: the sum of its potential, modulo `3`. -/
def psi : Z1 G3 VJ →+ ZMod 3 where
  toFun f := ((∑ j, pot f j : ℤ) : ZMod 3)
  map_zero' := by simp [pot]
  map_add' f f' := by
    simp only [pot, AddSubgroup.coe_add, Pi.add_apply, Finset.sum_add_distrib, neg_add]
    push_cast; ring

lemma psi_eq_zero_iff (f : Z1 G3 VJ) : psi f = 0 ↔ IsCoboundary₁ (f : G3 → VJ) := by
  have hf : IsCocycle₁ (f : G3 → VJ) := f.2
  change ((∑ j, pot f j : ℤ) : ZMod 3) = 0 ↔ _
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨⟨fun j => pot f j - t, ?_⟩, fun g => ?_⟩
    · change ∑ j, (pot f j - t) = 0
      rw [Finset.sum_sub_distrib, ht]; simp
    · ext j
      simp [cocycle_eq_pot hf g j]
  · rintro ⟨v, hv⟩
    refine ⟨-(v : Fin 3 → ℤ) 0, ?_⟩
    have hp : ∀ j, pot f j = (v : Fin 3 → ℤ) j - (v : Fin 3 → ℤ) 0 := fun j => by
      simp [pot, ← hv, Equiv.swap_inv]
    have hv0 : ∑ j, (v : Fin 3 → ℤ) j = 0 := v.2
    simp only [hp, Finset.sum_sub_distrib, hv0]
    simp

/-- The first basis vector of `ℤ^J`. -/
def e0 : Fin 3 → ℤ := fun j => if j = 0 then 1 else 0

/-- Its coboundary in `ℤ^J`, a cocycle with values in `V(J)`. -/
def f0 : Z1 G3 VJ :=
  ⟨fun g => ⟨fun j => e0 (g⁻¹ j) - e0 j, by
      change ∑ j, (e0 (g⁻¹ j) - e0 j) = 0
      rw [Finset.sum_sub_distrib, sum_perm g e0, sub_self]⟩,
    fun g h => by ext j; simp [mul_inv_rev]⟩

lemma psi_f0 : psi f0 = 1 := by
  change ((∑ j, pot f0 j : ℤ) : ZMod 3) = 1
  simp only [pot, f0, Fin.sum_univ_three, Equiv.swap_inv, e0, Fin.isValue, sub_self,
    Equiv.swap_apply_right, neg_sub, zero_add, Int.cast_add, Int.cast_sub]
  decide

lemma psi_surjective : Function.Surjective psi := fun z => ⟨(z.val : ℤ) • f0, by
  rw [map_zsmul, psi_f0]; simp⟩

/-- `H¹(𝔖₃, V(J)) ≃ ℤ/3`, the reading's computation for the marginal note of page 22. -/
noncomputable def H1_VJ : Q G3 VJ ≃+ ZMod 3 :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
      ext f; rw [AddMonoidHom.mem_ker, psi_eq_zero_iff]; rfl)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective psi psi_surjective)

theorem card_H1_VJ : Nat.card (H1 (R G3 VJ)) = 3 := by
  rw [card_H1, Nat.card_congr H1_VJ.toEquiv, Nat.card_zmod]

/-! ## Constants: `H¹(𝔖₃, k^*) = μ₂(k)` -/

/-- The units of a ring `k` (the units of the base `S`), written additively, with the trivial
action of `𝔖₃`. -/
def Triv (k : Type) [CommRing k] := Additive kˣ

instance (k : Type) [CommRing k] : AddCommGroup (Triv k) :=
  inferInstanceAs (AddCommGroup (Additive kˣ))

instance (k : Type) [CommRing k] : DistribMulAction G3 (Triv k) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

variable {k : Type} [CommRing k]

@[simp] lemma smul_triv (g : G3) (x : Triv k) : g • x = x := rfl

/-- The elements of order dividing `2`: `μ₂(k)`, written additively. -/
def mu2 (k : Type) [CommRing k] := {x : Triv k // x + x = 0}

/-- The odd permutations go to `x`, the even ones to `0`. -/
def signCocycle (x : mu2 k) : Z1 G3 (Triv k) :=
  ⟨fun g => if Equiv.Perm.sign g = 1 then 0 else x.1, fun g h => by
    have hx := x.2
    simp only [smul_triv, map_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign h) with hh | hh <;>
    simp [hg, hh, hx]⟩

lemma perm3_cases : ∀ g : G3, g = 1 ∨ g = Equiv.swap 0 1 ∨ g = Equiv.swap 1 2 ∨
    g = Equiv.swap 0 1 * Equiv.swap 1 2 ∨ g = Equiv.swap 1 2 * Equiv.swap 0 1 ∨
    g = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 := by decide

section Triv

variable (f : Z1 G3 (Triv k))

lemma cocycle_triv_mul (g h : G3) : (f : G3 → Triv k) (g * h) = f.1 h + f.1 g := f.2 g h

lemma cocycle_triv_one : (f : G3 → Triv k) 1 = 0 := by
  have := cocycle_triv_mul f 1 1
  simpa using this

lemma cocycle_triv_two : (f : G3 → Triv k) (Equiv.swap 0 1) + f.1 (Equiv.swap 0 1) = 0 := by
  rw [← cocycle_triv_mul, show Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 1 = 1 by decide]
  exact cocycle_triv_one f

/-- A cocycle for the trivial action is the sign cocycle of its value at a transposition. -/
lemma cocycle_triv_eq : f = signCocycle ⟨_, cocycle_triv_two f⟩ := by
  have h1 := cocycle_triv_one f
  have haa : f.1 (Equiv.swap 0 1) + f.1 (Equiv.swap 0 1) = 0 := cocycle_triv_two f
  have hbb : f.1 (Equiv.swap 1 2) + f.1 (Equiv.swap 1 2) = 0 := by
    rw [← cocycle_triv_mul, show Equiv.swap (1 : Fin 3) 2 * Equiv.swap 1 2 = 1 by decide, h1]
  have e := congrArg f.1 (show Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 * Equiv.swap 0 1 =
    Equiv.swap 1 2 * Equiv.swap 0 1 * Equiv.swap 1 2 by decide)
  simp only [cocycle_triv_mul] at e
  have key : f.1 (Equiv.swap 1 2) = f.1 (Equiv.swap 0 1) :=
    calc f.1 (Equiv.swap 1 2)
        = f.1 (Equiv.swap 1 2) + (f.1 (Equiv.swap 0 1) + f.1 (Equiv.swap 0 1)) := by
          rw [haa, add_zero]
      _ = f.1 (Equiv.swap 0 1) + (f.1 (Equiv.swap 1 2) + f.1 (Equiv.swap 0 1)) := by abel
      _ = f.1 (Equiv.swap 1 2) + (f.1 (Equiv.swap 0 1) + f.1 (Equiv.swap 1 2)) := e
      _ = f.1 (Equiv.swap 0 1) + (f.1 (Equiv.swap 1 2) + f.1 (Equiv.swap 1 2)) := by abel
      _ = f.1 (Equiv.swap 0 1) := by rw [hbb, add_zero]
  have sa : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = -1 := by decide
  have sb : Equiv.Perm.sign (Equiv.swap (1 : Fin 3) 2) = -1 := by decide
  apply Subtype.ext
  funext g
  rcases perm3_cases g with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [signCocycle, cocycle_triv_mul, h1, key, map_mul, sa, sb, map_one] <;>
    simp [haa]

end Triv

/-- Cocycles for the trivial action are `μ₂(k)`, by the value at a transposition. -/
def cocyclesTrivEquiv : Z1 G3 (Triv k) ≃ mu2 k where
  toFun f := ⟨_, cocycle_triv_two f⟩
  invFun := signCocycle
  left_inv f := (cocycle_triv_eq f).symm
  right_inv x := Subtype.ext (by simp [signCocycle])

lemma B1_triv : B1 G3 (Triv k) = ⊥ := by
  rw [eq_bot_iff]
  rintro f ⟨x, hx⟩
  rw [AddSubgroup.mem_bot]
  apply Subtype.ext
  funext g
  simp [← hx g]

/-- `H¹(𝔖₃, k^*) = Hom(𝔖₃, k^*) = μ₂(k)` for the trivial action. -/
theorem card_H1_triv : Nat.card (H1 (R G3 (Triv k))) = Nat.card (mu2 k) := by
  rw [card_H1, Nat.card_congr ((QuotientAddGroup.quotientAddEquivOfEq B1_triv).trans
    QuotientAddGroup.quotientBot).toEquiv, Nat.card_congr cocyclesTrivEquiv]

/-- An element of `μ₂(k)`, as an element of `k`. -/
def val (x : mu2 k) : k := ((Additive.toMul (show Additive kˣ from x.1) : kˣ) : k)

/-- An element of `μ₂(k)` is `1` or `-1` when `k` is a domain. -/
lemma mu2_eq [IsDomain k] (x : mu2 k) : val x = 1 ∨ val x = -1 := by
  have h : (Additive.toMul (show Additive kˣ from x.1) : kˣ) *
      Additive.toMul (show Additive kˣ from x.1) = 1 := congrArg Additive.toMul x.2
  have h' := congrArg (fun u : kˣ => (u : k)) h
  simp only [Units.val_mul, Units.val_one] at h'
  have : val x - 1 = 0 ∨ val x + 1 = 0 := mul_eq_zero.1 (by unfold val; linear_combination h')
  rcases this with h1 | h1
  · left; linear_combination h1
  · right; linear_combination h1

lemma mu2_ext {x y : mu2 k} (h : val x = val y) : x = y :=
  Subtype.ext (Additive.toMul.injective (Units.ext h))

lemma val_zero : val (⟨0, add_zero 0⟩ : mu2 k) = 1 := rfl

/-- `μ₂(k)` has one or two elements: its order divides `2`. -/
theorem card_mu2_dvd [IsDomain k] : Nat.card (mu2 k) ∣ 2 := by
  classical
  let ψ : mu2 k → ({1, -1} : Finset k) := fun x => ⟨val x, by
    rcases mu2_eq x with h | h <;> simp [h]⟩
  have hψ : Function.Injective ψ := fun x y h => mu2_ext (congrArg Subtype.val h)
  have : Finite (mu2 k) := Finite.of_injective ψ hψ
  have : Nonempty (mu2 k) := ⟨⟨0, add_zero 0⟩⟩
  have h1 := Nat.card_pos (α := mu2 k)
  have h2 : Nat.card (mu2 k) ≤ 2 := (Nat.card_le_card_of_injective ψ hψ).trans (by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact Finset.card_le_two)
  interval_cases h : Nat.card (mu2 k) <;> simp

/-- In characteristic `2`, `μ₂(k)` is trivial. -/
theorem card_mu2_char_two [IsDomain k] (h2 : (2 : k) = 0) : Nat.card (mu2 k) = 1 := by
  have hm : (-1 : k) = 1 := by linear_combination -h2
  have h : ∀ x : mu2 k, x = ⟨0, add_zero 0⟩ := fun x => mu2_ext (by
    rw [val_zero]
    rcases mu2_eq x with hx | hx
    · exact hx
    · rw [hx, hm])
  have : Unique (mu2 k) := ⟨⟨⟨0, add_zero 0⟩⟩, h⟩
  exact Nat.card_unique

/-! ## The bound of the marginal note of page 22 -/

/-- The « majoration » of page 22, with the reading's computations: for an extension of
`𝔖₃`-modules `0 → k^* → M → V(J) → 0` (`k^*` with the trivial action, `k` a domain), the
order of `H¹(𝔖₃, M)` divides `6`, and divides `3` in characteristic `2`. For `M` the units of
`U_{0,3}` over `S = Spec k` this bounds `H¹(U_{0,3}, 𝔖₃; 𝔾_m)`. -/
theorem card_H1_dvd [IsDomain k] (M : Type) [AddCommGroup M] [DistribMulAction G3 M]
    (i : Triv k →+ M) (p : M →+ VJ) (hi : ∀ (g : G3) a, i a = g • i a)
    (hp : ∀ (g : G3) m, p (g • m) = g • p m) (hinj : Function.Injective i)
    (hsurj : Function.Surjective p) (hex : ∀ m, p m = 0 ↔ ∃ a, i a = m) :
    Nat.card (H1 (R G3 M)) ∣ 6 ∧ ((2 : k) = 0 → Nat.card (H1 (R G3 M)) ∣ 3) := by
  have hi' : ∀ (g : G3) a, i (g • a) = g • i a := fun g a => hi g a
  have hex' := exact_mapQ (G := G3) i p hi' hp hinj hsurj hex
  have key : Nat.card (Q G3 M) ∣ Nat.card (Q G3 (Triv k)) * Nat.card (Q G3 VJ) :=
    card_dvd_of_exact (mapQ i hi') (mapQ p hp) hex'
  have hA : Nat.card (Q G3 (Triv k)) = Nat.card (mu2 k) :=
    (card_H1 (G := G3) (M := Triv k)).symm.trans card_H1_triv
  have hV : Nat.card (Q G3 VJ) = 3 := (card_H1 (G := G3) (M := VJ)).symm.trans card_H1_VJ
  have hM : Nat.card (H1 (R G3 M)) = Nat.card (Q G3 M) := card_H1
  rw [hA, hV] at key
  rw [hM]
  refine ⟨key.trans ?_, fun h2 => ?_⟩
  · exact mul_dvd_mul_right card_mu2_dvd 3
  · rwa [card_mu2_char_two h2, one_mul] at key

end Grothendieck.Folder140_1
