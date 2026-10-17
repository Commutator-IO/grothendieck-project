import Mathlib

/-!
# Folder 10, pages 191–197: the indecomposables of `𝔾_a ⋊ 𝔾_m`

The modernised reading `transcripts/10/10.modern.tex` (« III. Le produit semi-direct »)
takes `G = k ⋊ k^*` over a field of characteristic `0`, `k^*` acting on `k` by
`λ ↦ λ^p`. Its Lie algebra has generators `X` (of `𝔾_a`) and `Y` (of `𝔾_m`) with
`[Y, X] = p X` (p. 191). The page classifies the indecomposable representations as the
strings `e_{n,k}` (`n ∈ ℤ`, `k ≥ 1`): `k[Z]/Z^k`, `X` the multiplication by `Z`, weights
`n, n + p, …, n + p(k - 1)`; they are pairwise inequivalent, `ě_{n,k} = e_{-n-p(k-1),k}`
(p. 194), and the ring of classes is `Λ[ξ]`, `Λ = ℤ[ℤ]`, `ξ = e_{0,2}` (p. 197), the key
being that `ξ^n` has leading term `e_{0,n+1}`. This is the reachable part of finding
`10-split-ring-ga-rtimes-gm` of `src/content/findings.ts`.

What is formalised. A representation is read as the reading reads it, through its Lie
algebra: a vector space with two endomorphisms `X`, `Y`; maps of representations are linear
maps commuting with both (`IsoRep`). The string `e_{n,k}` is `Fin k → K` with
`X zⱼ = zⱼ₊₁` (`sX`) and `Y zⱼ = (n + p j) zⱼ` (`sY`).

* `sY_sX`: `[Y, X] = p X` on every string.
* `string_end_scalar`, `string_indecomposable`: in characteristic `0` with `p ≥ 1`, an
  endomorphism of `e_{n,k}` is a scalar, so `e_{n,k}` is indecomposable.
* `string_iso_imp`: `e_{n,k} ≅ e_{n',k'}` with `k ≥ 1` forces `k = k'` and `n = n'`
  (dimension and trace of `Y`).
* `string_dual`: the dual representation `(-Xᵀ, -Yᵀ)` of `e_{n,k}` is `e_{-n-p(k-1),k}`.
* `xi_tensor_string`: `ξ ⊗ e_{n,k} ≅ e_{n,k+1} ⊕ e_{n+p,k-1}` for `k ≥ 2`, as soon as `k`
  is invertible in `K`; no hypothesis on `p`. This is the step that makes `ξ^n` triangular
  with leading coefficient `1` (`α = 0` on page 197).

Not formalised: that every indecomposable is a string (Lemmes 1 and 2), and the ring
`R(G) = Λ[ξ]` itself, which needs that classification and the Krull–Schmidt theorem,
neither in mathlib; the algebraic-group packaging.
-/

namespace Grothendieck.Folder10

open TensorProduct

variable {K : Type*} [Field K]

/-- Two representations `(V, X, Y)` and `(W, X', Y')` are isomorphic. -/
def IsoRep {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (X Y : Module.End K V) (X' Y' : Module.End K W) : Prop :=
  ∃ e : V ≃ₗ[K] W, (e : V →ₗ[K] W) ∘ₗ X = X' ∘ₗ e ∧ (e : V →ₗ[K] W) ∘ₗ Y = Y' ∘ₗ e

/-- The weight `n + p i`. -/
def wt (p : ℕ) (n : ℤ) (i : ℕ) : K := (n : K) + p * i

/-- `X` on the string of length `k`: `zⱼ ↦ zⱼ₊₁`, `z_{k-1} ↦ 0`. -/
def sX (k : ℕ) : Module.End K (Fin k → K) where
  toFun u i := if h : 0 < (i : ℕ) then u ⟨i - 1, by omega⟩ else 0
  map_add' u v := by ext i; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c u := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

/-- `Y` on the string `e_{n,k}`: `zⱼ ↦ (n + p j) zⱼ`. -/
def sY (p : ℕ) (n : ℤ) (k : ℕ) : Module.End K (Fin k → K) where
  toFun u i := wt p n i * u i
  map_add' u v := by ext i; simp only [Pi.add_apply]; ring
  map_smul' c u := by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma sX_apply {k : ℕ} (u : Fin k → K) (i : Fin k) :
    sX k u i = if h : 0 < (i : ℕ) then u ⟨i - 1, by omega⟩ else 0 := rfl

lemma sY_apply (p : ℕ) (n : ℤ) {k : ℕ} (u : Fin k → K) (i : Fin k) :
    sY p n k u i = wt p n i * u i := rfl

lemma sX_single {k : ℕ} (j : Fin k) :
    sX k (Pi.single j (1 : K)) = if h : (j : ℕ) + 1 < k then Pi.single ⟨j + 1, h⟩ 1 else 0 := by
  ext i
  rw [sX_apply]
  split_ifs with h1 h2 h2 <;>
    simp only [Pi.single_apply, Fin.ext_iff, Pi.zero_apply] <;>
    split_ifs <;> first | rfl | (exfalso; omega)

lemma sY_single (p : ℕ) (n : ℤ) {k : ℕ} (j : Fin k) :
    sY p n k (Pi.single j (1 : K)) = (wt p n j : K) • Pi.single j (1 : K) := by
  ext i
  rw [sY_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- The Lie relation `[Y, X] = p X` (p. 191) on every string. -/
theorem sY_sX (p : ℕ) (n : ℤ) {k : ℕ} (u : Fin k → K) :
    sY p n k (sX k u) = sX k (sY p n k u) + (p : K) • sX k u := by
  ext i
  simp only [sY_apply, sX_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, wt]
  split_ifs with h
  · simp only [Nat.cast_sub (show 1 ≤ (i : ℕ) by omega)]; push_cast; ring
  · simp

/-! ## Endomorphisms of a string -/

/-- In characteristic `0` with `p ≥ 1`, every endomorphism of `e_{n,k}` is a scalar. -/
theorem string_end_scalar [CharZero K] {p : ℕ} (hp : p ≠ 0) (n : ℤ) {k : ℕ}
    (f : Module.End K (Fin k → K)) (hX : f ∘ₗ sX k = sX k ∘ₗ f)
    (hY : f ∘ₗ sY p n k = sY p n k ∘ₗ f) : ∃ c : K, f = c • LinearMap.id := by
  -- `f zⱼ = cⱼ zⱼ`
  have hdiag : ∀ j i : Fin k, i ≠ j → f (Pi.single j 1) i = 0 := by
    intro j i hij
    have h := congrArg (fun g => g (Pi.single j (1 : K)) i) hY
    simp only [LinearMap.comp_apply, sY_single, map_smul, Pi.smul_apply, smul_eq_mul,
      sY_apply] at h
    have hw : wt p n j ≠ (wt p n i : K) := by
      intro hw
      apply hij
      simp only [wt, add_right_inj, mul_eq_mul_left_iff, Nat.cast_inj,
        Nat.cast_eq_zero, hp, or_false] at hw
      exact Fin.ext hw.symm
    have := sub_ne_zero.mpr hw
    have h' : (wt p n j - wt p n i) * f (Pi.single j 1) i = 0 := by rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left this
  have hsingle : ∀ j : Fin k, f (Pi.single j 1) = f (Pi.single j 1) j • Pi.single j 1 := by
    intro j; ext i
    by_cases h : i = j
    · subst h; simp
    · simp [h, hdiag j i h]
  -- the coefficients are constant along `X`
  have hstep : ∀ (j : ℕ) (h : j + 1 < k),
      f (Pi.single ⟨j + 1, h⟩ 1) ⟨j + 1, h⟩ = f (Pi.single ⟨j, by omega⟩ 1) ⟨j, by omega⟩ := by
    intro j h
    have e := congrArg (fun g => g (Pi.single ⟨j, by omega⟩ (1 : K)) ⟨j + 1, h⟩) hX
    simp only [LinearMap.comp_apply, sX_single, h, ↓reduceDIte] at e
    rw [e, sX_apply]
    simp
  have hconst : ∀ (j : ℕ) (h : j < k),
      f (Pi.single ⟨j, h⟩ 1) ⟨j, h⟩ = f (Pi.single ⟨0, by omega⟩ 1) ⟨0, by omega⟩ := by
    intro j
    induction j with
    | zero => intro h; rfl
    | succ j ih => intro h; rw [hstep j h, ih]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact ⟨0, LinearMap.ext fun u => funext fun i => i.elim0⟩
  refine ⟨f (Pi.single ⟨0, hk⟩ 1) ⟨0, hk⟩, (Pi.basisFun K (Fin k)).ext fun j => ?_⟩
  rw [Pi.basisFun_apply, hsingle j, hconst j j.2]
  rfl

/-- `e_{n,k}` is indecomposable: an idempotent endomorphism is `0` or the identity. -/
theorem string_indecomposable [CharZero K] {p : ℕ} (hp : p ≠ 0) (n : ℤ) {k : ℕ}
    (f : Module.End K (Fin k → K)) (hX : f ∘ₗ sX k = sX k ∘ₗ f)
    (hY : f ∘ₗ sY p n k = sY p n k ∘ₗ f) (hf : f * f = f) : f = 0 ∨ f = 1 := by
  obtain ⟨c, rfl⟩ := string_end_scalar hp n f hX hY
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    left; exact LinearMap.ext fun u => funext fun i => i.elim0
  have h := congrArg (fun g : Module.End K (Fin k → K) => g (Pi.single ⟨0, hk⟩ 1) ⟨0, hk⟩) hf
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
    Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h
  have h2 : c * (c - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with hc | hc
  · left; rw [hc, zero_smul]
  · right; rw [sub_eq_zero.mp hc, one_smul]; rfl

/-! ## Strings are pairwise inequivalent -/

lemma trace_sY (p : ℕ) (n : ℤ) (k : ℕ) :
    LinearMap.trace K _ (sY p n k) = ∑ i : Fin k, wt p n i := by
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin k)), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr, sY_single]
  simp

/-- `e_{n,k} ≅ e_{n',k'}` with `k ≥ 1` forces `(n, k) = (n', k')`. -/
theorem string_iso_imp [CharZero K] (p : ℕ) {n n' : ℤ} {k k' : ℕ} (hk : 0 < k)
    (h : IsoRep (sX k) (sY p n k) (sX (K := K) k') (sY p n' k')) : k = k' ∧ n = n' := by
  obtain ⟨e, -, hY⟩ := h
  have hkk : k = k' := by
    have := e.finrank_eq
    simpa only [Module.finrank_fin_fun] using this
  subst hkk
  refine ⟨rfl, ?_⟩
  have hconj : e.conj (sY p n k) = sY p n' k := by
    refine LinearMap.ext fun w => ?_
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    have := congrArg (fun g => g (e.symm w)) hY
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
    simpa only [LinearEquiv.coe_coe] using this
  have ht := LinearMap.trace_conj' (sY p n k) e
  rw [hconj, trace_sY, trace_sY] at ht
  simp only [wt, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, add_left_inj] at ht
  have hk' : (k : K) ≠ 0 := by exact_mod_cast hk.ne'
  have := mul_left_cancel₀ hk' ht
  exact_mod_cast this.symm

/-! ## The dual of a string -/

/-- The dual basis `ε`, reversed and signed: `B j = (-1)^j ε_{k-1-j}`. -/
noncomputable def dualStringBasis (k : ℕ) : Module.Basis (Fin k) K (Module.Dual K (Fin k → K)) :=
  (((Pi.basisFun K (Fin k)).dualBasis).reindex Fin.revPerm).unitsSMul
    fun j => (-1 : Kˣ) ^ (j : ℕ)

lemma dualStringBasis_apply {k : ℕ} (j : Fin k) (u : Fin k → K) :
    dualStringBasis k j u = (-1) ^ (j : ℕ) * u (Fin.rev j) := by
  simp [dualStringBasis, Module.Basis.unitsSMul_apply, Module.Basis.reindex_apply,
    Pi.basisFun_repr, Units.smul_def]

/-- **Page 194**: the dual `(-Xᵀ, -Yᵀ)` of `e_{n,k}` is `e_{-n-p(k-1),k}`. -/
theorem string_dual (p : ℕ) (n : ℤ) (k : ℕ) :
    IsoRep (sX k) (sY p (-n - p * ((k : ℤ) - 1)) k)
      (-(sX (K := K) k).dualMap) (-(sY p n k).dualMap) := by
  let e := (Pi.basisFun K (Fin k)).equiv (dualStringBasis k) (Equiv.refl _)
  have he : ∀ j, e (Pi.single j 1) = dualStringBasis k j := fun j => by
    rw [← Pi.basisFun_apply, Module.Basis.equiv_apply]; rfl
  refine ⟨e, (Pi.basisFun K (Fin k)).ext fun j => ?_, (Pi.basisFun K (Fin k)).ext fun j => ?_⟩
  · refine LinearMap.ext fun u => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply, sX_single, he,
      LinearMap.neg_apply, LinearMap.dualMap_apply, dualStringBasis_apply, sX_apply]
    have hr : ((Fin.rev j : Fin k) : ℕ) = k - (j + 1) := Fin.val_rev j
    split_ifs with h1 h2 h2
    · rw [he, dualStringBasis_apply]
      have : Fin.rev (⟨j + 1, h1⟩ : Fin k) = ⟨Fin.rev j - 1, by omega⟩ := by
        ext; simp only [Fin.val_rev]; omega
      rw [this, pow_succ]; ring
    · exfalso; omega
    · exfalso; omega
    · simp
  · refine LinearMap.ext fun u => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply, sY_single,
      map_smul, he, LinearMap.neg_apply, LinearMap.dualMap_apply, dualStringBasis_apply,
      sY_apply, LinearMap.smul_apply, smul_eq_mul, wt]
    have hr : ((Fin.rev j : Fin k) : ℕ) = k - (j + 1) := Fin.val_rev j
    rw [hr, Nat.cast_sub (by omega)]
    push_cast
    ring

/-! ## `ξ ⊗ e_{n,k}` -/

section Tensor

variable (p : ℕ) (n : ℤ) (m : ℕ)

/-- `X` on `ξ ⊗ e_{n,m+2}`: `X ⊗ 1 + 1 ⊗ X`. -/
noncomputable def tX : Module.End K ((Fin 2 → K) ⊗[K] (Fin (m + 2) → K)) :=
  TensorProduct.map (sX 2) LinearMap.id + TensorProduct.map LinearMap.id (sX (m + 2))

/-- `Y` on `ξ ⊗ e_{n,m+2}`, `ξ = e_{0,2}`. -/
noncomputable def tY : Module.End K ((Fin 2 → K) ⊗[K] (Fin (m + 2) → K)) :=
  TensorProduct.map (sY p 0 2) LinearMap.id + TensorProduct.map LinearMap.id (sY p n (m + 2))

variable {p n m}

lemma tX_tmul (x : Fin 2 → K) (y : Fin (m + 2) → K) :
    tX m (x ⊗ₜ y) = sX 2 x ⊗ₜ y + x ⊗ₜ sX (m + 2) y := by
  simp [tX, TensorProduct.map_tmul]

lemma tY_tmul (x : Fin 2 → K) (y : Fin (m + 2) → K) :
    tY p n m (x ⊗ₜ y) = sY p 0 2 x ⊗ₜ y + x ⊗ₜ sY p n (m + 2) y := by
  simp [tY, TensorProduct.map_tmul]

lemma tY_eigen {x : Fin 2 → K} {y : Fin (m + 2) → K} {c d : K} (hx : sY p 0 2 x = c • x)
    (hy : sY p n (m + 2) y = d • y) : tY p n m (x ⊗ₜ y) = (c + d) • (x ⊗ₜ y) := by
  rw [tY_tmul, hx, hy, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, add_smul]

lemma tY_tX (u : (Fin 2 → K) ⊗[K] (Fin (m + 2) → K)) :
    tY p n m (tX m u) = tX m (tY p n m u) + (p : K) • tX m u := by
  induction u using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [tX_tmul, tY_tmul, map_add, sY_sX, TensorProduct.add_tmul, TensorProduct.tmul_add,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]
    abel
  | add u v hu hv =>
    simp only [map_add, hu, hv, smul_add]
    abel

lemma tY_tX_pow {u : (Fin 2 → K) ⊗[K] (Fin (m + 2) → K)} {c : K} (hu : tY p n m u = c • u)
    (j : ℕ) : tY p n m ((tX (K := K) m ^ j) u) = (c + p * j) • (tX (K := K) m ^ j) u := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, tY_tX, ih, map_smul]
    push_cast
    module

lemma tX_pow_tmul {x : Fin 2 → K} (hx : sX 2 (sX 2 x) = 0) (y : Fin (m + 2) → K) (c : ℕ) :
    (tX (K := K) m ^ c) (x ⊗ₜ y) =
      x ⊗ₜ (sX (m + 2) ^ c) y + (c : K) • (sX 2 x ⊗ₜ (sX (m + 2) ^ (c - 1)) y) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, tX_tmul, tX_tmul, hx,
      TensorProduct.zero_tmul, zero_add]
    rcases c with _ | c
    · simp [pow_succ']
      abel
    · simp only [Nat.add_sub_cancel, pow_succ', Module.End.mul_apply]
      push_cast
      module

/-- The basis vectors of `ξ`: `a = z₀` (weight `0`), `b = z₁` (weight `p`). -/
abbrev va : Fin 2 → K := Pi.single 0 1
abbrev vb : Fin 2 → K := Pi.single 1 1

lemma sX_va : sX (K := K) 2 va = vb := by
  rw [sX_single]; simp

lemma sX_vb : sX (K := K) 2 vb = 0 := by
  rw [sX_single]; simp

/-- `Z c = X^c z₀` in `e_{n,m+2}`. -/
noncomputable abbrev Z (c : ℕ) : Fin (m + 2) → K := (sX (m + 2) ^ c) (Pi.single 0 1)

lemma Z_eq_single {c : ℕ} (h : c < m + 2) : Z (K := K) (m := m) c = Pi.single ⟨c, h⟩ 1 := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [Z, pow_succ', Module.End.mul_apply, ← Z, ih (by omega), sX_single]
    simp [h]

lemma Z_eq_zero {c : ℕ} (h : m + 2 ≤ c) : Z (K := K) (m := m) c = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero =>
    change Z (K := K) (m := m) (m + 2) = 0
    rw [Z, pow_succ', Module.End.mul_apply, ← Z, Z_eq_single (by omega),
      sX_single]
    simp
  | succ d ih =>
    rw [Z, ← Nat.add_assoc, pow_succ', Module.End.mul_apply, ← Z, ih (by omega), map_zero]

lemma sX_pow_Z (i c : ℕ) : (sX (m + 2) ^ i) (Z (K := K) (m := m) c) = Z (i + c) := by
  rw [Z, Z, ← Module.End.mul_apply, ← pow_add]

/-- The two strings in `ξ ⊗ e_{n,m+2}`: `vⱼ = X^j (a ⊗ z₀)` (length `m + 3`) and
`wᵢ = X^i w₀`, `w₀ = a ⊗ z₁ - (m + 1) b ⊗ z₀` (length `m + 1`). -/
noncomputable def strings : Fin (m + 3) ⊕ Fin (m + 1) → (Fin 2 → K) ⊗[K] (Fin (m + 2) → K)
  | Sum.inl j => (tX (K := K) m ^ (j : ℕ)) (va ⊗ₜ Z 0)
  | Sum.inr i => (tX (K := K) m ^ (i : ℕ)) (va ⊗ₜ Z 1 - ((m : K) + 1) • (vb ⊗ₜ Z 0))

lemma tX_pow_va (c : ℕ) (y : Fin (m + 2) → K) :
    (tX (K := K) m ^ c) (va ⊗ₜ y) =
      va ⊗ₜ (sX (m + 2) ^ c) y + (c : K) • (vb ⊗ₜ (sX (m + 2) ^ (c - 1)) y) := by
  rw [tX_pow_tmul (by rw [sX_va, sX_vb]), sX_va]

lemma tX_pow_vb (c : ℕ) (y : Fin (m + 2) → K) :
    (tX (K := K) m ^ c) (vb ⊗ₜ y) = vb ⊗ₜ (sX (m + 2) ^ c) y := by
  rw [tX_pow_tmul (by rw [sX_vb, map_zero]), sX_vb, TensorProduct.zero_tmul, smul_zero, add_zero]

lemma strings_inl (c : ℕ) :
    (tX (K := K) m ^ c) (va ⊗ₜ Z 0) = va ⊗ₜ Z c + (c : K) • (vb ⊗ₜ Z (c - 1)) := by
  rw [tX_pow_va, sX_pow_Z, sX_pow_Z]
  simp only [Nat.add_zero]

lemma strings_inr (c : ℕ) :
    (tX (K := K) m ^ c) (va ⊗ₜ Z 1 - ((m : K) + 1) • (vb ⊗ₜ Z 0)) =
      va ⊗ₜ Z (c + 1) + ((c : K) - (m + 1)) • (vb ⊗ₜ Z c) := by
  rw [map_sub, map_smul, tX_pow_va, tX_pow_vb, sX_pow_Z, sX_pow_Z, sX_pow_Z]
  rcases c with _ | c
  · simp only [Nat.cast_zero, zero_smul, add_zero]
    module
  · simp only [Nat.add_sub_cancel, Nat.add_zero]
    module

lemma top_le_span (hk : ((m : K) + 2) ≠ 0) :
    ⊤ ≤ Submodule.span K (Set.range (strings (K := K) (m := m))) := by
  set S := Submodule.span K (Set.range (strings (K := K) (m := m)))
  have hl : ∀ (j : ℕ) (h : j < m + 3), (tX (K := K) m ^ j) (va ⊗ₜ Z 0) ∈ S := fun j h =>
    Submodule.subset_span ⟨Sum.inl ⟨j, h⟩, rfl⟩
  have hr : ∀ (i : ℕ) (h : i < m + 1),
      (tX (K := K) m ^ i) (va ⊗ₜ Z 1 - ((m : K) + 1) • (vb ⊗ₜ Z 0)) ∈ S := fun i h =>
    Submodule.subset_span ⟨Sum.inr ⟨i, h⟩, rfl⟩
  have hb : ∀ c : ℕ, vb ⊗ₜ Z (K := K) (m := m) c ∈ S := by
    intro c
    rcases lt_trichotomy c (m + 1) with hc | rfl | hc
    · have e : vb ⊗ₜ Z (K := K) (m := m) c =
          ((m : K) + 2)⁻¹ • ((tX (K := K) m ^ (c + 1)) (va ⊗ₜ Z 0) -
            (tX (K := K) m ^ c) (va ⊗ₜ Z 1 - ((m : K) + 1) • (vb ⊗ₜ Z 0))) := by
        rw [strings_inl, strings_inr, Nat.add_sub_cancel]
        rw [show (va ⊗ₜ Z (c + 1) + ((c + 1 : ℕ) : K) • (vb ⊗ₜ Z c) -
            (va ⊗ₜ Z (c + 1) + ((c : K) - (m + 1)) • (vb ⊗ₜ Z c)) : _) =
            ((m : K) + 2) • (vb ⊗ₜ Z (K := K) (m := m) c) by push_cast; module]
        rw [smul_smul, inv_mul_cancel₀ hk, one_smul]
      rw [e]
      exact S.smul_mem _ (S.sub_mem (hl _ (by omega)) (hr _ hc))
    · have e : vb ⊗ₜ Z (K := K) (m := m) (m + 1) =
          ((m : K) + 2)⁻¹ • (tX (K := K) m ^ (m + 2)) (va ⊗ₜ Z 0) := by
        rw [strings_inl, Z_eq_zero le_rfl, TensorProduct.tmul_zero, zero_add, smul_smul,
          show m + 2 - 1 = m + 1 by omega]
        push_cast
        rw [inv_mul_cancel₀ hk, one_smul]
      rw [e]
      exact S.smul_mem _ (hl _ (by omega))
    · rw [Z_eq_zero (by omega), TensorProduct.tmul_zero]
      exact S.zero_mem
  have ha : ∀ c : ℕ, va ⊗ₜ Z (K := K) (m := m) c ∈ S := by
    intro c
    by_cases hc : c < m + 3
    · have e : va ⊗ₜ Z (K := K) (m := m) c =
          (tX (K := K) m ^ c) (va ⊗ₜ Z 0) - (c : K) • (vb ⊗ₜ Z (c - 1)) := by
        rw [strings_inl]; abel
      rw [e]
      exact S.sub_mem (hl c hc) (S.smul_mem _ (hb _))
    · rw [Z_eq_zero (by omega), TensorProduct.tmul_zero]
      exact S.zero_mem
  rw [← (Module.Basis.tensorProduct (Pi.basisFun K (Fin 2))
    (Pi.basisFun K (Fin (m + 2)))).span_eq, Submodule.span_le]
  rintro _ ⟨⟨i, c⟩, rfl⟩
  rw [Module.Basis.tensorProduct_apply, Pi.basisFun_apply, Pi.basisFun_apply,
    ← Z_eq_single c.2]
  fin_cases i
  · exact ha c
  · exact hb c

variable (n p) in
/-- **Page 197, the leading term**: `ξ ⊗ e_{n,k} ≅ e_{n,k+1} ⊕ e_{n+p,k-1}` for `k = m + 2`,
whenever `k` is invertible in `K`. -/
theorem xi_tensor_string (hk : ((m : K) + 2) ≠ 0) :
    IsoRep (LinearMap.prodMap (sX (m + 3)) (sX (m + 1)))
      (LinearMap.prodMap (sY p n (m + 3)) (sY p (n + p) (m + 1)))
      (tX (K := K) m) (tY p n m) := by
  have hli : LinearIndependent K (strings (K := K) (m := m)) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank (top_le_span hk) (by
      rw [Module.finrank_tensorProduct, Module.finrank_fin_fun, Module.finrank_fin_fun,
        Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
      ring)
  let B := Module.Basis.mk hli (top_le_span hk)
  let src := (Pi.basisFun K (Fin (m + 3))).prod (Pi.basisFun K (Fin (m + 1)))
  let e := src.equiv B (Equiv.refl _)
  have he : ∀ i, e (src i) = strings i := fun i => by
    rw [Module.Basis.equiv_apply]; exact Module.Basis.mk_apply _ _ _
  have hsrc_l : ∀ j, src (Sum.inl j) = (Pi.single j 1, 0) := fun j => by
    simp [src, Pi.basisFun_apply]
  have hsrc_r : ∀ i, src (Sum.inr i) = (0, Pi.single i 1) := fun i => by
    simp [src, Pi.basisFun_apply]
  have ea : sY p 0 2 (va (K := K)) = (0 : K) • va := by rw [sY_single]; simp [wt]
  have eb : sY p 0 2 (vb (K := K)) = (p : K) • vb := by rw [sY_single]; simp [wt]
  have e0 : sY p n (m + 2) (Z (K := K) (m := m) 0) = (n : K) • Z 0 := by
    rw [Z_eq_single (by omega), sY_single]; simp [wt]
  have e1 : sY p n (m + 2) (Z (K := K) (m := m) 1) = ((n : K) + p) • Z 1 := by
    rw [Z_eq_single (by omega), sY_single]; simp [wt]
  have hwt0 : tY (K := K) p n m (va ⊗ₜ Z 0) = (n : K) • (va ⊗ₜ Z (K := K) (m := m) 0) := by
    rw [tY_eigen ea e0, zero_add]
  have hwt1 : tY (K := K) p n m (va ⊗ₜ Z 1 - ((m : K) + 1) • (vb ⊗ₜ Z 0)) =
      ((n : K) + p) • (va ⊗ₜ Z (K := K) (m := m) 1 - ((m : K) + 1) • (vb ⊗ₜ Z 0)) := by
    rw [map_sub, map_smul, tY_eigen ea e1, tY_eigen eb e0]
    module
  refine ⟨e, src.ext fun i => ?_, src.ext fun i => ?_⟩
  · rcases i with j | i
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, he, hsrc_l,
        LinearMap.prodMap_apply, map_zero, sX_single]
      split_ifs with h
      · rw [← hsrc_l, he]
        simp only [strings]
        rw [pow_succ', Module.End.mul_apply]
      · rw [show ((0 : Fin (m + 3) → K), (0 : Fin (m + 1) → K)) = 0 from rfl, map_zero]
        simp only [strings]
        rw [← Module.End.mul_apply, ← pow_succ', strings_inl, Z_eq_zero (by omega),
          Z_eq_zero (by omega), TensorProduct.tmul_zero, TensorProduct.tmul_zero, smul_zero,
          add_zero]
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, he, hsrc_r,
        LinearMap.prodMap_apply, map_zero, sX_single]
      split_ifs with h
      · rw [← hsrc_r, he]
        simp only [strings]
        rw [pow_succ', Module.End.mul_apply]
      · rw [show ((0 : Fin (m + 3) → K), (0 : Fin (m + 1) → K)) = 0 from rfl, map_zero]
        simp only [strings]
        have hi : (i : ℕ) = m := by omega
        rw [← Module.End.mul_apply, ← pow_succ', strings_inr, hi, Z_eq_zero le_rfl,
          TensorProduct.tmul_zero, zero_add]
        rw [show ((m + 1 : ℕ) : K) - (m + 1) = 0 by push_cast; ring, zero_smul]
  · rcases i with j | i
    · have hs : ((wt p n j : K) • Pi.single j (1 : K), (0 : Fin (m + 1) → K)) =
          (wt p n j : K) • src (Sum.inl j) := by rw [hsrc_l, Prod.smul_mk, smul_zero]
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, he, hsrc_l,
        LinearMap.prodMap_apply, map_zero, sY_single, hs, map_smul, he]
      simp only [strings]
      rw [tY_tX_pow hwt0]
      rfl
    · have hs : ((0 : Fin (m + 3) → K), (wt p (n + p) i : K) • Pi.single i (1 : K)) =
          (wt p (n + p) i : K) • src (Sum.inr i) := by rw [hsrc_r, Prod.smul_mk, smul_zero]
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, he, hsrc_r,
        LinearMap.prodMap_apply, map_zero, sY_single, hs, map_smul, he]
      simp only [strings]
      rw [tY_tX_pow hwt1]
      simp [wt]

end Tensor

end Grothendieck.Folder10
