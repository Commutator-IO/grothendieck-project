import Mathlib

/-!
# Folder 1: the system (16) of page 71 for `m ≤ 1`, and (16) ⟹ (15)

The modernised reading `transcripts/1/1.modern.tex` (manuscript pages 71–73, Théorème 2)
states, for compact `u, v` and `0 ≤ m ≤ n`,

> `σ_n^m(u+v) ≤ ∑_{p=0}^{m} σ_n^p(u) σ_n^{m-p}(v)`  (16),

where `σ_n^m(w)` is the elementary symmetric function of degree `m` of the first `n`
singular values of `w` (17), and the product form

> `∏_{i≤n} (1 + r s_i(u+v)) ≤ ∏_{i≤n} (1 + r s_i(u)) ∏_{i≤n} (1 + r s_i(v))`, `r ≥ 0`  (15).

This is the finding `1-sigma-nm-system` of `src/content/findings.ts`. Proved here, for
linear maps between finite-dimensional inner product spaces over `ℝ` or `ℂ`, with mathlib's
`LinearMap.singularValues` (zero-indexed, so `s_0` is the largest):

* `sum_singularValues_add_le`: Ky Fan's inequality, the case `m = 1` of (16), for every `n`;
* `sigma_system_of_le_one`: (16) for `m ≤ 1` and every `n`;
* `prod_le_of_sigma_system`: (16) for all `m ≤ n` implies (15) for that `n`;
* `one_add_singularValues_zero_le`: (15) for `n = 1`.

Ky Fan's maximum principle (`norm_sum_inner_le`) is proved for families that are pairwise
orthogonal of norm `≤ 1`, not only orthonormal. Not proved: (16) for `2 ≤ m ≤ n`, which the
page derives from exterior powers and the trace norm on them (Prop. 2, Cor. 2, Prop. 3), and
the passage to compact operators. A proof says only that the claim holds as stated; whether
the system is in the literature stays open.
-/

namespace Grothendieck.Folder1

open Finset Module InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Bessel's inequality for a finite family of pairwise orthogonal vectors of norm `≤ 1`. -/
theorem sum_norm_inner_sq_le {ι : Type*} (s : Finset ι) (y : ι → E)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪y i, y j⟫_𝕜 = 0) (hle : ∀ i ∈ s, ‖y i‖ ≤ 1)
    (z : E) : ∑ i ∈ s, ‖⟪y i, z⟫_𝕜‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  classical
  set c : ι → 𝕜 := fun i => ⟪y i, z⟫_𝕜 with hc
  set p : E := ∑ i ∈ s, c i • y i with hp
  set S : ℝ := ∑ i ∈ s, ‖c i‖ ^ 2 with hS
  have hS0 : 0 ≤ S := sum_nonneg fun i _ => by positivity
  have hpz : ⟪p, z⟫_𝕜 = (S : 𝕜) := by
    rw [hp, sum_inner, hS]
    push_cast
    refine sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, hc, RCLike.conj_mul]
  have hyp : ∀ i ∈ s, ⟪y i, p⟫_𝕜 = c i * ⟪y i, y i⟫_𝕜 := by
    intro i hi
    rw [hp, inner_sum, sum_eq_single i]
    · rw [inner_smul_right]
    · intro j hj hji
      rw [inner_smul_right, horth i hi j hj (Ne.symm hji), mul_zero]
    · intro h; exact absurd hi h
  have hpp : ‖p‖ ^ 2 ≤ S := by
    have h1 : ‖p‖ ^ 2 = ∑ i ∈ s, ‖c i‖ ^ 2 * ‖y i‖ ^ 2 := by
      rw [← @inner_self_eq_norm_sq 𝕜, hp, sum_inner, map_sum]
      refine sum_congr rfl fun i hi => ?_
      rw [inner_smul_left, ← hp, hyp i hi, ← mul_assoc, RCLike.conj_mul,
        inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [h1, hS]
    refine sum_le_sum fun i hi => ?_
    have := hle i hi
    have h0 : 0 ≤ ‖y i‖ := norm_nonneg _
    have : ‖y i‖ ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ‖c i‖]
  have hSle : S ≤ ‖p‖ * ‖z‖ := by
    have := norm_inner_le_norm (𝕜 := 𝕜) p z
    rw [hpz, RCLike.norm_ofReal, abs_of_nonneg hS0] at this
    exact this
  have hp0 : 0 ≤ ‖p‖ := norm_nonneg _
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  rcases hS0.eq_or_lt with h | h
  · rw [← h]; positivity
  · by_contra hcon
    rw [not_le] at hcon
    have : S ^ 2 ≤ S * ‖z‖ ^ 2 := by
      calc S ^ 2 ≤ (‖p‖ * ‖z‖) ^ 2 := by gcongr
        _ = ‖p‖ ^ 2 * ‖z‖ ^ 2 := by ring
        _ ≤ S * ‖z‖ ^ 2 := by gcongr
    nlinarith


/-- The key counting step: for `s` antitone and nonnegative, and weights `0 ≤ c j ≤ 1` of total
mass `≤ n`, the weighted sum `∑ s j c j` is at most the sum of the `n` largest `s j`. -/
theorem sum_mul_le_sum_range {d : ℕ} (s : ℕ → ℝ) (hs : Antitone s) (hs0 : ∀ j, 0 ≤ s j)
    (c : Fin d → ℝ) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1) {n : ℕ}
    (hcn : ∑ j, c j ≤ n) : ∑ j : Fin d, s j * c j ≤ ∑ j ∈ range n, s j := by
  classical
  have key : ∀ j : Fin d, s j * c j ≤ (if (j : ℕ) < n then s j else 0)
      + s n * (c j - if (j : ℕ) < n then 1 else 0) := by
    intro j
    split_ifs with hj
    · have := hs hj.le
      nlinarith [hc1 j]
    · have := hs (not_lt.mp hj)
      nlinarith [hc0 j]
  have hcard : ∑ j : Fin d, c j ≤ ∑ j : Fin d, (if (j : ℕ) < n then (1 : ℝ) else 0) := by
    rw [sum_boole, Fin.card_filter_val_lt]
    rcases le_total d n with h | h
    · rw [min_eq_left h]
      calc ∑ j, c j ≤ ∑ _j : Fin d, (1 : ℝ) := sum_le_sum fun j _ => hc1 j
        _ = d := by simp
    · rw [min_eq_right h]; exact hcn
  have hfin : ∑ j : Fin d, (if (j : ℕ) < n then s j else 0) ≤ ∑ j ∈ range n, s j := by
    have h1 : ∑ j : Fin d, (if (j : ℕ) < n then s j else 0) =
        ∑ k ∈ range d, (if k < n then s k else 0) :=
      Fin.sum_univ_eq_sum_range (fun k => if k < n then s k else 0) d
    rw [h1, ← sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      simp only [mem_filter, mem_range] at hk ⊢
      exact hk.2
    · intro k _ _; exact hs0 k
  calc ∑ j : Fin d, s j * c j ≤ ∑ j : Fin d, ((if (j : ℕ) < n then s j else 0)
        + s n * (c j - if (j : ℕ) < n then 1 else 0)) := sum_le_sum fun j _ => key j
    _ = ∑ j : Fin d, (if (j : ℕ) < n then s j else 0)
        + s n * (∑ j : Fin d, c j - ∑ j : Fin d, (if (j : ℕ) < n then (1 : ℝ) else 0)) := by
          rw [sum_add_distrib, ← mul_sum, sum_sub_distrib]
    _ ≤ ∑ j ∈ range n, s j + s n * 0 :=
          add_le_add hfin (mul_le_mul_of_nonneg_left (by linarith) (hs0 n))
    _ = _ := by ring

section SVD

variable [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- An orthonormal basis `(e_j)` of `E` made of eigenvectors of `T* T`, in the order of
decreasing eigenvalues `s_j(T)²`. -/
noncomputable def ebasis (T : E →ₗ[𝕜] F) : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

theorem inner_apply_ebasis (T : E →ₗ[𝕜] F) (j k : Fin (finrank 𝕜 E)) :
    ⟪T (ebasis T j), T (ebasis T k)⟫_𝕜 =
      ((T.singularValues k ^ 2 : ℝ) : 𝕜) * ⟪ebasis T j, ebasis T k⟫_𝕜 := by
  rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply (LinearMap.adjoint T) T, ebasis,
    LinearMap.IsSymmetric.apply_eigenvectorBasis, inner_smul_right, T.sq_singularValues_fin rfl]

theorem norm_apply_ebasis (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) :
    ‖T (ebasis T j)‖ = T.singularValues j := by
  have h := inner_apply_ebasis T j j
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, (ebasis T).orthonormal.1 j] at h
  simp only [RCLike.ofReal_one, one_pow, mul_one] at h
  norm_cast at h
  exact (sq_eq_sq₀ (norm_nonneg _) (T.singularValues_nonneg _)).mp h

theorem inner_apply_ebasis_of_ne (T : E →ₗ[𝕜] F) {j k : Fin (finrank 𝕜 E)} (h : j ≠ k) :
    ⟪T (ebasis T j), T (ebasis T k)⟫_𝕜 = 0 := by
  rw [inner_apply_ebasis, (ebasis T).orthonormal.2 h, mul_zero]

/-- The second Schmidt family `f_j = s_j⁻¹ T e_j` (zero when `s_j = 0`). -/
noncomputable def fvec (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) : F :=
  (((T.singularValues j)⁻¹ : ℝ) : 𝕜) • T (ebasis T j)

theorem apply_ebasis_eq (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) :
    T (ebasis T j) = ((T.singularValues j : ℝ) : 𝕜) • fvec T j := by
  rcases eq_or_ne (T.singularValues j) 0 with h | h
  · have h0 : T (ebasis T j) = 0 := by rw [← norm_eq_zero, norm_apply_ebasis, h]
    rw [h0, h, RCLike.ofReal_zero, zero_smul]
  · rw [fvec, smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ h, RCLike.ofReal_one, one_smul]

theorem inner_fvec_of_ne (T : E →ₗ[𝕜] F) {j k : Fin (finrank 𝕜 E)} (h : j ≠ k) :
    ⟪fvec T j, fvec T k⟫_𝕜 = 0 := by
  rw [fvec, fvec, inner_smul_left, inner_smul_right, inner_apply_ebasis_of_ne T h, mul_zero,
    mul_zero]

theorem norm_fvec_le (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) : ‖fvec T j‖ ≤ 1 := by
  rw [fvec, norm_smul, norm_apply_ebasis, RCLike.norm_ofReal, abs_inv,
    abs_of_nonneg (T.singularValues_nonneg _)]
  rcases eq_or_ne (T.singularValues j) 0 with h | h
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem inner_fvec_apply_ebasis (T : E →ₗ[𝕜] F) (j : Fin (finrank 𝕜 E)) :
    ⟪fvec T j, T (ebasis T j)⟫_𝕜 = ((T.singularValues j : ℝ) : 𝕜) := by
  rw [fvec, inner_smul_left, inner_self_eq_norm_sq_to_K, norm_apply_ebasis, RCLike.conj_ofReal]
  rcases eq_or_ne (T.singularValues j) 0 with h | h
  · simp [h]
  · rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, sq, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- **Ky Fan's maximum principle, upper bound.** For families `(x_i)` in `E` and `(y_i)` in `F`
indexed by a set of `≤ n` elements, each pairwise orthogonal and of norm `≤ 1`,
`|∑ ⟪y_i, T x_i⟫| ≤ s_0(T) + ⋯ + s_{n-1}(T)`. -/
theorem norm_sum_inner_le {ι : Type*} (s : Finset ι) (x : ι → E) (y : ι → F)
    (hx : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪x i, x j⟫_𝕜 = 0) (hx1 : ∀ i ∈ s, ‖x i‖ ≤ 1)
    (hy : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪y i, y j⟫_𝕜 = 0) (hy1 : ∀ i ∈ s, ‖y i‖ ≤ 1)
    (T : E →ₗ[𝕜] F) {n : ℕ} (hn : #s ≤ n) :
    ‖∑ i ∈ s, ⟪y i, T (x i)⟫_𝕜‖ ≤ ∑ j ∈ range n, T.singularValues j := by
  have hexp : ∑ i ∈ s, ⟪y i, T (x i)⟫_𝕜 =
      ∑ j, ∑ i ∈ s, ⟪ebasis T j, x i⟫_𝕜 *
        (((T.singularValues j : ℝ) : 𝕜) * ⟪y i, fvec T j⟫_𝕜) := by
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    calc ⟪y i, T (x i)⟫_𝕜 = ⟪y i, T (∑ j, ⟪ebasis T j, x i⟫_𝕜 • ebasis T j)⟫_𝕜 := by
          rw [(ebasis T).sum_repr']
      _ = _ := by
          rw [map_sum, inner_sum]
          refine sum_congr rfl fun j _ => ?_
          rw [map_smul, inner_smul_right, apply_ebasis_eq, inner_smul_right]
  have hbound : ‖∑ i ∈ s, ⟪y i, T (x i)⟫_𝕜‖ ≤
      ∑ j : Fin (finrank 𝕜 E), T.singularValues j * ((∑ i ∈ s, ‖⟪x i, ebasis T j⟫_𝕜‖ ^ 2
        + ∑ i ∈ s, ‖⟪y i, fvec T j⟫_𝕜‖ ^ 2) / 2) := by
    rw [hexp]
    refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    rw [← sum_add_distrib, sum_div, mul_sum]
    refine sum_le_sum fun i _ => ?_
    rw [norm_mul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (T.singularValues_nonneg _),
      norm_inner_symm (ebasis T j) (x i)]
    have hσ := T.singularValues_nonneg j
    nlinarith [mul_nonneg hσ (sq_nonneg (‖⟪x i, ebasis T j⟫_𝕜‖ - ‖⟪y i, fvec T j⟫_𝕜‖))]
  have ha1 : ∀ j, ∑ i ∈ s, ‖⟪x i, ebasis T j⟫_𝕜‖ ^ 2 ≤ 1 := fun j => by
    have := sum_norm_inner_sq_le s x hx hx1 (ebasis T j)
    rwa [(ebasis T).orthonormal.1 j, one_pow] at this
  have hb1 : ∀ j, ∑ i ∈ s, ‖⟪y i, fvec T j⟫_𝕜‖ ^ 2 ≤ 1 := fun j => by
    have := sum_norm_inner_sq_le s y hy hy1 (fvec T j)
    have h2 : ‖fvec T j‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_fvec_le T j)
    linarith
  have ha : ∑ j, ∑ i ∈ s, ‖⟪x i, ebasis T j⟫_𝕜‖ ^ 2 ≤ #s := by
    rw [sum_comm]
    calc ∑ i ∈ s, ∑ j, ‖⟪x i, ebasis T j⟫_𝕜‖ ^ 2 ≤ ∑ _i ∈ s, (1 : ℝ) := by
          refine sum_le_sum fun i hi => ?_
          have h1 := sum_norm_inner_sq_le univ (ebasis T)
            (fun j _ k _ h => (ebasis T).orthonormal.2 h)
            (fun j _ => ((ebasis T).orthonormal.1 j).le) (x i)
          have h1' : ∑ j, ‖⟪x i, ebasis T j⟫_𝕜‖ ^ 2 = ∑ j, ‖⟪ebasis T j, x i⟫_𝕜‖ ^ 2 :=
            sum_congr rfl fun j _ => by rw [norm_inner_symm]
          have h3 : ‖x i‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hx1 i hi)
          linarith
      _ = #s := by simp
  have hb : ∑ j, ∑ i ∈ s, ‖⟪y i, fvec T j⟫_𝕜‖ ^ 2 ≤ #s := by
    rw [sum_comm]
    calc ∑ i ∈ s, ∑ j, ‖⟪y i, fvec T j⟫_𝕜‖ ^ 2 ≤ ∑ _i ∈ s, (1 : ℝ) := by
          refine sum_le_sum fun i hi => ?_
          have h1 := sum_norm_inner_sq_le univ (fvec T)
            (fun j _ k _ h => inner_fvec_of_ne T h) (fun j _ => norm_fvec_le T j) (y i)
          have h1' : ∑ j, ‖⟪y i, fvec T j⟫_𝕜‖ ^ 2 = ∑ j, ‖⟪fvec T j, y i⟫_𝕜‖ ^ 2 :=
            sum_congr rfl fun j _ => by rw [norm_inner_symm]
          have h3 : ‖y i‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hy1 i hi)
          linarith
      _ = #s := by simp
  refine hbound.trans (sum_mul_le_sum_range T.singularValues T.singularValues_antitone
    T.singularValues_nonneg
    (fun j => (∑ i ∈ s, ‖⟪x i, ebasis T j⟫_𝕜‖ ^ 2 + ∑ i ∈ s, ‖⟪y i, fvec T j⟫_𝕜‖ ^ 2) / 2)
    (fun j => by positivity) (fun j => by linarith [ha1 j, hb1 j]) ?_)
  rw [← sum_div, sum_add_distrib]
  have : (#s : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- The sum of the first `n` singular values, as a sum over the indices `j < dim E`. -/
theorem sum_range_singularValues_eq (T : E →ₗ[𝕜] F) (n : ℕ) :
    ∑ j ∈ range n, T.singularValues j =
      ∑ j ∈ univ.filter (fun j : Fin (finrank 𝕜 E) => (j : ℕ) < n), T.singularValues j := by
  have h1 : ∑ j : Fin (finrank 𝕜 E), (if (j : ℕ) < n then T.singularValues j else 0) =
      ∑ k ∈ range (finrank 𝕜 E), (if k < n then T.singularValues k else 0) :=
    Fin.sum_univ_eq_sum_range (fun k => if k < n then T.singularValues k else 0) _
  rw [sum_filter, h1, ← sum_filter]
  symm
  apply sum_subset
  · intro k hk
    simp only [mem_filter, mem_range] at hk ⊢
    exact hk.2
  · intro k hk hk'
    simp only [mem_filter, mem_range, not_and, not_lt] at hk hk'
    exact T.singularValues_of_finrank_le (not_lt.mp fun h => (not_lt.mpr (hk' h)) hk)

/-- **Ky Fan's inequality** (the case `m = 1` of the system of page 71):
`s_0(u+v) + ⋯ + s_{n-1}(u+v) ≤ (s_0(u) + ⋯ + s_{n-1}(u)) + (s_0(v) + ⋯ + s_{n-1}(v))`. -/
theorem sum_singularValues_add_le (u v : E →ₗ[𝕜] F) (n : ℕ) :
    ∑ j ∈ range n, (u + v).singularValues j ≤
      ∑ j ∈ range n, u.singularValues j + ∑ j ∈ range n, v.singularValues j := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (finrank 𝕜 E)),
      S = univ.filter (fun j : Fin (finrank 𝕜 E) => (j : ℕ) < n) := ⟨_, rfl⟩
  have hSn : #S ≤ n := by rw [hS, Fin.card_filter_val_lt]; exact min_le_right _ _
  rw [sum_range_singularValues_eq, ← hS]
  have key : ((∑ j ∈ S, (u + v).singularValues j : ℝ) : 𝕜) =
      ∑ j ∈ S, ⟪fvec (u + v) j, u (ebasis (u + v) j)⟫_𝕜 +
        ∑ j ∈ S, ⟪fvec (u + v) j, v (ebasis (u + v) j)⟫_𝕜 := by
    rw [← sum_add_distrib, RCLike.ofReal_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [← inner_add_right, ← LinearMap.add_apply, inner_fvec_apply_ebasis]
  have hxo : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪ebasis (u + v) i, ebasis (u + v) j⟫_𝕜 = 0 :=
    fun i _ j _ h => (ebasis (u + v)).orthonormal.2 h
  have hx1 : ∀ i ∈ S, ‖ebasis (u + v) i‖ ≤ 1 := fun i _ => ((ebasis (u + v)).orthonormal.1 i).le
  have hyo : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⟪fvec (u + v) i, fvec (u + v) j⟫_𝕜 = 0 :=
    fun i _ j _ h => inner_fvec_of_ne (u + v) h
  have hy1 : ∀ i ∈ S, ‖fvec (u + v) i‖ ≤ 1 := fun i _ => norm_fvec_le (u + v) i
  have hu := norm_sum_inner_le S (ebasis (u + v)) (fvec (u + v)) hxo hx1 hyo hy1 u hSn
  have hv := norm_sum_inner_le S (ebasis (u + v)) (fvec (u + v)) hxo hx1 hyo hy1 v hSn
  calc ∑ j ∈ S, (u + v).singularValues j
      = ‖((∑ j ∈ S, (u + v).singularValues j : ℝ) : 𝕜)‖ := by
        rw [RCLike.norm_ofReal,
          abs_of_nonneg (sum_nonneg fun j _ => (u + v).singularValues_nonneg _)]
    _ ≤ ‖∑ j ∈ S, ⟪fvec (u + v) j, u (ebasis (u + v) j)⟫_𝕜‖ +
        ‖∑ j ∈ S, ⟪fvec (u + v) j, v (ebasis (u + v) j)⟫_𝕜‖ := by
        rw [key]; exact norm_add_le _ _
    _ ≤ _ := add_le_add hu hv

/-- `σ_n^m(T)`, the elementary symmetric function of degree `m` of the first `n` singular
values `s_0(T), …, s_{n-1}(T)` (page 71, (17)). -/
noncomputable def sigma (n m : ℕ) (T : E →ₗ[𝕜] F) : ℝ :=
  ∑ t ∈ (range n).powersetCard m, ∏ i ∈ t, T.singularValues i

theorem sigma_nonneg (n m : ℕ) (T : E →ₗ[𝕜] F) : 0 ≤ sigma n m T :=
  sum_nonneg fun _ _ => prod_nonneg fun i _ => T.singularValues_nonneg i

theorem sigma_zero (n : ℕ) (T : E →ₗ[𝕜] F) : sigma n 0 T = 1 := by simp [sigma]

theorem sigma_one (n : ℕ) (T : E →ₗ[𝕜] F) :
    sigma n 1 T = ∑ j ∈ range n, T.singularValues j := by
  simp [sigma, powersetCard_one]

/-- **The system (16) of page 71 for `m ≤ 1`**:
`σ_n^m(u+v) ≤ ∑_{p=0}^{m} σ_n^p(u) σ_n^{m-p}(v)`. For `m = 0` both sides are `1`; for `m = 1`
this is Ky Fan's inequality. -/
theorem sigma_system_of_le_one (u v : E →ₗ[𝕜] F) (n m : ℕ) (hm : m ≤ 1) :
    sigma n m (u + v) ≤ ∑ p ∈ range (m + 1), sigma n p u * sigma n (m - p) v := by
  interval_cases m
  · simp [sigma_zero]
  · simp only [sum_range_succ, sum_range_zero, zero_add, Nat.sub_zero, Nat.sub_self,
      sigma_zero, sigma_one, one_mul, mul_one]
    linarith [sum_singularValues_add_le u v n]

end SVD

/-- `∏_{i<n} (1 + r a_i) = ∑_{m=0}^{n} r^m e_m(a_0, …, a_{n-1})`. -/
theorem prod_one_add_eq (a : ℕ → ℝ) (n : ℕ) (r : ℝ) :
    ∏ i ∈ range n, (1 + r * a i) =
      ∑ m ∈ range (n + 1), r ^ m * ∑ t ∈ (range n).powersetCard m, ∏ i ∈ t, a i := by
  rw [prod_one_add, sum_powerset, card_range]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun t ht => ?_
  rw [prod_mul_distrib, prod_const, (mem_powersetCard.mp ht).2]

/-- The Cauchy-product step: coefficientwise bounds `C_m ≤ ∑_{p ≤ m} A_p B_{m-p}` for `m ≤ n`
give `∑_{m ≤ n} r^m C_m ≤ (∑_{m ≤ n} r^m A_m)(∑_{m ≤ n} r^m B_m)` for `r ≥ 0`. -/
theorem sum_pow_mul_le {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (A B C : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m)
    (hB : ∀ m, 0 ≤ B m) (h : ∀ m ≤ n, C m ≤ ∑ p ∈ range (m + 1), A p * B (m - p)) :
    ∑ m ∈ range (n + 1), r ^ m * C m ≤
      (∑ m ∈ range (n + 1), r ^ m * A m) * ∑ m ∈ range (n + 1), r ^ m * B m := by
  have g0 : ∀ p k, 0 ≤ r ^ p * A p * (r ^ k * B k) := fun p k => by
    have := hA p; have := hB k; positivity
  have hcomm := sum_Ico_Ico_comm 0 (n + 1) (fun p m => r ^ p * A p * (r ^ (m - p) * B (m - p)))
  simp only [Nat.Ico_zero_eq_range] at hcomm
  calc ∑ m ∈ range (n + 1), r ^ m * C m
      ≤ ∑ m ∈ range (n + 1), ∑ p ∈ range (m + 1), r ^ p * A p * (r ^ (m - p) * B (m - p)) := by
        refine sum_le_sum fun m hm => ?_
        have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
        calc r ^ m * C m ≤ r ^ m * ∑ p ∈ range (m + 1), A p * B (m - p) :=
              mul_le_mul_of_nonneg_left (h m hmn) (pow_nonneg hr m)
          _ = _ := by
            rw [mul_sum]
            refine sum_congr rfl fun p hp => ?_
            have hpm : p ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hp)
            rw [show r ^ m = r ^ p * r ^ (m - p) by rw [← pow_add, Nat.add_sub_cancel' hpm]]
            ring
    _ = ∑ p ∈ range (n + 1), ∑ m ∈ Ico p (n + 1), r ^ p * A p * (r ^ (m - p) * B (m - p)) :=
        hcomm.symm
    _ = ∑ p ∈ range (n + 1), ∑ k ∈ range (n + 1 - p), r ^ p * A p * (r ^ k * B k) := by
        refine sum_congr rfl fun p _ => ?_
        rw [sum_Ico_eq_sum_range]
        refine sum_congr rfl fun k _ => ?_
        rw [Nat.add_sub_cancel_left]
    _ ≤ ∑ p ∈ range (n + 1), ∑ k ∈ range (n + 1), r ^ p * A p * (r ^ k * B k) := by
        refine sum_le_sum fun p _ => sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => g0 p k
        intro k hk
        exact mem_range.mpr ((mem_range.mp hk).trans_le (Nat.sub_le _ _))
    _ = _ := by rw [sum_mul_sum]

section Product

variable [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **The system (16) implies the product form (15)** (page 71): if
`σ_n^m(u+v) ≤ ∑_{p ≤ m} σ_n^p(u) σ_n^{m-p}(v)` for all `m ≤ n`, then for `r ≥ 0`,
`∏_{i<n} (1 + r s_i(u+v)) ≤ ∏_{i<n} (1 + r s_i(u)) ∏_{i<n} (1 + r s_i(v))`. -/
theorem prod_le_of_sigma_system (u v : E →ₗ[𝕜] F) (n : ℕ)
    (h : ∀ m ≤ n, sigma n m (u + v) ≤ ∑ p ∈ range (m + 1), sigma n p u * sigma n (m - p) v)
    {r : ℝ} (hr : 0 ≤ r) :
    ∏ i ∈ range n, (1 + r * (u + v).singularValues i) ≤
      (∏ i ∈ range n, (1 + r * u.singularValues i)) *
        ∏ i ∈ range n, (1 + r * v.singularValues i) := by
  rw [prod_one_add_eq, prod_one_add_eq, prod_one_add_eq]
  exact sum_pow_mul_le hr (fun m => sigma n m u) (fun m => sigma n m v)
    (fun m => sigma n m (u + v)) (fun m => sigma_nonneg n m u) (fun m => sigma_nonneg n m v) h

/-- The product form (15) for `n = 1`: `1 + r s_0(u+v) ≤ (1 + r s_0(u)) (1 + r s_0(v))`. -/
theorem one_add_singularValues_zero_le (u v : E →ₗ[𝕜] F) {r : ℝ} (hr : 0 ≤ r) :
    1 + r * (u + v).singularValues 0 ≤
      (1 + r * u.singularValues 0) * (1 + r * v.singularValues 0) := by
  have := prod_le_of_sigma_system u v 1
    (fun m hm => sigma_system_of_le_one u v 1 m hm) hr
  simpa using this

end Product

end Grothendieck.Folder1
