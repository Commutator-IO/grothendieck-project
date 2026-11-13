import Mathlib

/-!
# Quillen, notebook 1987-14, p. 49: the kernel of the contraction by `(1, …, 1)`

Daniel Quillen's research notebook 1987-14 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201987/1987-14.pdf>), p. 49.
For `v = (1, …, 1)`, the contraction `ι_v : Λ^q(K^k) → Λ^{q−1}(K^k)` has a kernel of dimension
`C(k − 1, q)`, the dimension of `Λ^q(K^{k−1})`.

We prove it for any nonzero linear form `d` on a finite-dimensional vector space `M` of
dimension `k` (the page's `ι_v` is the contraction with the form `d = Σ xᵢ`, `d(v) = k`
being irrelevant: only `d ≠ 0` matters), with mathlib's contraction `d⌋` on the exterior
algebra (`CliffordAlgebra.contractLeft` for the zero quadratic form):

* `contractLeft_mem` : `d⌋` maps `⋀^{q+1} M` into `⋀^q M`; `contr d q` is the restriction;
* `ker_contr` : the complex is exact, `Ker(d⌋ on ⋀^{q+1}) = Im(d⌋ on ⋀^{q+2})`, by the homotopy
  `d⌋(m ∧ x) + m ∧ (d⌋x) = d(m) x` with `d(m) = 1`;
* `finrank_range_contr`, `finrank_ker_contr` : by rank-nullity and Pascal's rule, the image of
  `d⌋ : ⋀^{q+1} → ⋀^q` has dimension `C(k − 1, q)` and its kernel `C(k − 1, q + 1)`;
* `finrank_ker_sum` : the page's case, `d = Σ xᵢ` on `K^k`.
-/

namespace Quillen.Notebook1987_14

open CliffordAlgebra Module

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

local notation "Λ" => ExteriorAlgebra K M

/-- The contraction on the exterior algebra. -/
abbrev contr' (d : Module.Dual K M) : Λ →ₗ[K] Λ := contractLeft (Q := (0 : QuadraticForm K M)) d

theorem exteriorPower_succ (q : ℕ) :
    ⋀[K]^(q + 1) M = LinearMap.range (ExteriorAlgebra.ι K : M →ₗ[K] Λ) * ⋀[K]^q M := by
  rw [ExteriorAlgebra.exteriorPower, ExteriorAlgebra.exteriorPower, pow_succ']

/-- `d⌋` lowers the degree by one. -/
theorem contractLeft_mem (d : Module.Dual K M) : ∀ (q : ℕ) (x : Λ),
    x ∈ ⋀[K]^(q + 1) M → contr' d x ∈ ⋀[K]^q M
  | 0, x, hx => by
    rw [exteriorPower_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · rintro _ ⟨m, rfl⟩ y hy
      rw [contr', contractLeft_ι_mul]
      have : contractLeft (Q := (0 : QuadraticForm K M)) d y = 0 := by
        rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.one_eq_range] at hy
        obtain ⟨r, rfl⟩ := hy
        exact contractLeft_algebraMap (Q := (0 : QuadraticForm K M)) (d := d) r
      rw [this, mul_zero, sub_zero]
      exact Submodule.smul_mem _ _ hy
    · intro a b ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  | q + 1, x, hx => by
    rw [exteriorPower_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · rintro _ ⟨m, rfl⟩ y hy
      rw [contr', contractLeft_ι_mul]
      refine Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) ?_
      rw [exteriorPower_succ]
      exact Submodule.mul_mem_mul ⟨m, rfl⟩ (contractLeft_mem d q y hy)
    · intro a b ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb

/-- `d⌋ : ⋀^{q+1} M → ⋀^q M`. -/
def contr (d : Module.Dual K M) (q : ℕ) : ⋀[K]^(q + 1) M →ₗ[K] ⋀[K]^q M :=
  (contr' d).restrict fun x hx => contractLeft_mem d q x hx

theorem contr_apply (d : Module.Dual K M) (q : ℕ) (x : ⋀[K]^(q + 1) M) :
    (contr d q x : Λ) = contr' d x := rfl

theorem ι_mul_mem {q : ℕ} (m : M) {x : Λ} (hx : x ∈ ⋀[K]^q M) :
    ExteriorAlgebra.ι K m * x ∈ ⋀[K]^(q + 1) M := by
  rw [exteriorPower_succ]; exact Submodule.mul_mem_mul ⟨m, rfl⟩ hx

/-- `d⌋ ∘ d⌋ = 0`, between exterior powers. -/
theorem contr_comp_contr (d : Module.Dual K M) (q : ℕ) : contr d q ∘ₗ contr d (q + 1) = 0 :=
  LinearMap.ext fun x => Subtype.ext (contractLeft_contractLeft (Q := (0 : QuadraticForm K M)) d x)

/-- **Exactness**: for `d ≠ 0`, `Ker(d⌋ on ⋀^{q+1}) = Im(d⌋ on ⋀^{q+2})`. -/
theorem ker_contr {d : Module.Dual K M} (hd : d ≠ 0) (q : ℕ) :
    LinearMap.ker (contr d q) = LinearMap.range (contr d (q + 1)) := by
  obtain ⟨m₀, hm₀⟩ := DFunLike.ne_iff.mp hd
  replace hm₀ : d m₀ ≠ 0 := hm₀
  set m := (d m₀)⁻¹ • m₀
  have hm : d m = 1 := by simp [m, hm₀]
  apply le_antisymm
  · intro x hx
    refine ⟨⟨ExteriorAlgebra.ι K m * x, ι_mul_mem m x.2⟩, ?_⟩
    apply Subtype.ext
    have hx' : contr' d x = 0 := by simpa [contr_apply] using congrArg Subtype.val hx
    rw [contr_apply, contr', contractLeft_ι_mul]
    erw [hx']
    rw [hm, one_smul, mul_zero, sub_zero]
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, contr_comp_contr, LinearMap.zero_apply]

/-- `d⌋ : ⋀^1 → ⋀^0` is onto for `d ≠ 0`. -/
theorem range_contr_zero {d : Module.Dual K M} (hd : d ≠ 0) : LinearMap.range (contr d 0) = ⊤ := by
  obtain ⟨m₀, hm₀⟩ := DFunLike.ne_iff.mp hd
  replace hm₀ : d m₀ ≠ 0 := hm₀
  rw [eq_top_iff]
  rintro ⟨y, hy⟩ -
  have hy' := hy
  rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.one_eq_range] at hy'
  obtain ⟨r, rfl⟩ := hy'
  refine ⟨⟨ExteriorAlgebra.ι K ((r / d m₀) • m₀), ?_⟩, ?_⟩
  · rw [ExteriorAlgebra.exteriorPower, pow_one]; exact ⟨_, rfl⟩
  · apply Subtype.ext
    rw [contr_apply]
    change contractLeft (Q := (0 : QuadraticForm K M)) d (CliffordAlgebra.ι _ _) = _
    rw [contractLeft_ι, map_smul, smul_eq_mul, div_mul_cancel₀ _ hm₀]
    rfl

variable [FiniteDimensional K M]

/-- The image of `d⌋ : ⋀^{q+1} M → ⋀^q M` has dimension `C(k − 1, q)`, `k = dim M`. -/
theorem finrank_range_contr {d : Module.Dual K M} (hd : d ≠ 0) : ∀ q : ℕ,
    finrank K (LinearMap.range (contr d q)) = (finrank K M - 1).choose q
  | 0 => by
    rw [range_contr_zero hd, finrank_top, exteriorPower.finrank_eq, Nat.choose_zero_right,
      Nat.choose_zero_right]
  | q + 1 => by
    have hk : 0 < finrank K M := by
      obtain ⟨m₀, hm₀⟩ := DFunLike.ne_iff.mp hd
      exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨m₀, fun h => hm₀ (by simp [h])⟩
    have hrn := LinearMap.finrank_range_add_finrank_ker (contr d q)
    rw [ker_contr hd, finrank_range_contr hd q, exteriorPower.finrank_eq] at hrn
    obtain ⟨k, hk'⟩ : ∃ k, finrank K M = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hk).symm⟩
    rw [hk', Nat.choose_succ_succ] at hrn
    rw [hk', Nat.add_sub_cancel]
    simp only [Nat.add_sub_cancel, Nat.succ_eq_add_one] at hrn
    omega

/-- **Quillen, notebook 1987-14, p. 49**: for `d ≠ 0`, the kernel of `d⌋ : ⋀^{q+1} M → ⋀^q M`
has dimension `C(k − 1, q + 1)`. -/
theorem finrank_ker_contr {d : Module.Dual K M} (hd : d ≠ 0) (q : ℕ) :
    finrank K (LinearMap.ker (contr d q)) = (finrank K M - 1).choose (q + 1) := by
  rw [ker_contr hd, finrank_range_contr hd]

/-- The page's case: the contraction with `(1, …, 1)`, i.e. with the form `Σ xᵢ` on `K^k`,
`k ≥ 1`, has on `⋀^{q+1}(K^k)` a kernel of dimension `C(k − 1, q + 1)`. -/
theorem finrank_ker_sum {k : ℕ} (hk : 0 < k) (q : ℕ) :
    finrank K (LinearMap.ker (contr (M := Fin k → K)
      (∑ i, LinearMap.proj i : Module.Dual K (Fin k → K)) q)) = (k - 1).choose (q + 1) := by
  have hd : (∑ i, LinearMap.proj i : Module.Dual K (Fin k → K)) ≠ 0 := fun h => by
    simpa using LinearMap.congr_fun h (Pi.single ⟨0, hk⟩ 1)
  rw [finrank_ker_contr hd, Module.finrank_fin_fun]

end Quillen.Notebook1987_14
