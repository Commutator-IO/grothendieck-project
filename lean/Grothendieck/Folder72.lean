import Mathlib

/-!
# Folder 72: regular polytopes and pseudo-reflections in any dimension

## The group `𝒰_ρ` and the automorphisms of a realisation (pages 37–38, 87–88)

Finding `72-automorphisms-deform-gm-to-ga` (`src/content/findings.ts`), on the
reading `transcripts/72/72.modern.tex`, section IX and section XV D). Page 37
defines `𝒰_ρ = Spec 𝒪_S[T]_{(1+ρT)}` with the law `λ * λ' = λ + λ' + ρλλ'`, and
its action `u_λ = id + λ π ⊗ c̃` on `E`; the « Théorème » of page 38 says that
`𝔾_m × 𝒰_ρ → Aut(E, (τᵢ))` and `𝒰_ρ → Aut(X, (τᵢ))` are isomorphisms and that
`D₀ ∖ {c, d}` is a torsor under `𝒰_ρ`, trivialised by `s₀`. No proof is on the
pages.

**The coordinates.** Over a commutative ring `R`, take `E = R^{n+2}` with basis
`e₀ = s₀, e₁ = a₀, …, e_{n+1} = aₙ` (the basis `(s₀, a₀, …, aₙ)` of condition
(12) of page 96), and the pseudo-reflections `τᵢ = id + a'ᵢ ⊗ aᵢ` with
`⟨a_{i−1}, a'ᵢ⟩ = 1`, `⟨aᵢ, a'ᵢ⟩ = μᵢ`, `⟨a_{i+1}, a'ᵢ⟩ = βᵢ`, all other
pairings `0` (the conventions of the reading). Here `a'ᵢ = F i`, so
`F i x = x_i + μᵢ x_{i+1} + βᵢ x_{i+2}`, and `π` is the coordinate `x₀`. By the theorem
of pages 96–100, every pinned non-degenerate realisation is isomorphic to this
one.

* `U ρ`: the `R`-points of `𝒰_ρ`, a commutative group; `toUnits : λ ↦ 1 + ρλ`
  is an isomorphism onto `Rˣ` when `ρ` is a unit (`toUnitsEquiv`), and
  `U 0 ≃* Multiplicative R` (`U_zero`). `forall_surjective_iff`: `λ ↦ 1 + ρλ`
  is surjective over every `R`-algebra iff `ρ` is a unit (test algebra: the dual
  numbers, unit `1 + ε`).
* `ct` is `c̃` (back-substitution, `F_ct`, `co_ct_top`), `ρ = π(c̃)`;
  `ρ_one`: for `n = 1`, `ρ = μ₀μ₁ − β₀`, `4 − β₀` for reflections, as page 41.
* `u_mul`: `u_λ u_λ' = u_{λ * λ'}`; `τ_mul_P`, `P_mul_τ`: `u_λ` commutes with the
  `τᵢ`; `det_u`: `det u_λ = 1 + ρλ`.
* `commute_iff` (the computation under the « Théorème »): an endomorphism of `E`
  commutes with all `τᵢ` iff it is `c + t π ⊗ c̃`, with `(c, t)` unique
  (`coeff_unique`); `isUnit_iff`: it is invertible iff `c` and `c + tρ` are units.
  `centraliserEquiv : Rˣ × U ρ ≃* centraliser`: the linear form of the theorem,
  `𝔾_m × 𝒰_ρ ≅ Aut(E, (τᵢ))`, on `R`-points.
* `mem_D0_iff`, `mem_startPoints_iff`, `u_e0_injective`, `u_u_e0`: the points of
  `D₀ = H₁ ∩ ⋯ ∩ Hₙ` are the `a s₀ + t c̃`; the start points off `c` and `d`,
  normalised by `⟨s, a'₀⟩ = 1`, are exactly the `u_λ s₀ = s₀ + λ c̃`, each
  for one `λ`, and `u_μ (u_λ s₀) = u_{λ * μ} s₀`: a trivial torsor under `𝒰_ρ`.

Not formalised: the group scheme, its smoothness, the projective statement over
a base (automorphisms of `X` commuting with the projective `τᵢ`), the torsor of
flags itself (page 87 C, the bijection flags ↔ start points).
-/

namespace Grothendieck.Folder72

universe u

variable {R : Type u} [CommRing R]

/-! ### The group `𝒰_ρ` -/

/-- The `R`-points of `𝒰_ρ = Spec R[T]_{(1+ρT)}`. -/
@[ext]
structure U (ρ : R) where
  /-- the coordinate `λ` -/
  val : R
  isUnit : IsUnit (1 + ρ * val)

namespace U

variable {ρ : R}

instance : One (U ρ) := ⟨⟨0, by simp⟩⟩

instance : Mul (U ρ) :=
  ⟨fun x y => ⟨x.val + y.val + ρ * x.val * y.val, by
    have : 1 + ρ * (x.val + y.val + ρ * x.val * y.val) = (1 + ρ * x.val) * (1 + ρ * y.val) := by
      ring
    rw [this]; exact x.isUnit.mul y.isUnit⟩⟩

lemma inv_isUnit (x : U ρ) : IsUnit (1 + ρ * (-x.val * ↑x.isUnit.unit⁻¹)) := by
  have h := x.isUnit.mul_val_inv
  have : 1 + ρ * (-x.val * ↑x.isUnit.unit⁻¹) = ↑x.isUnit.unit⁻¹ := by
    linear_combination (-1 : R) * h
  rw [this]; exact Units.isUnit _

noncomputable instance : Inv (U ρ) := ⟨fun x => ⟨-x.val * ↑x.isUnit.unit⁻¹, inv_isUnit x⟩⟩

@[simp] lemma one_val : (1 : U ρ).val = 0 := rfl
@[simp] lemma mul_val (x y : U ρ) : (x * y).val = x.val + y.val + ρ * x.val * y.val := rfl
lemma inv_val (x : U ρ) : (x⁻¹).val = -x.val * ↑x.isUnit.unit⁻¹ := rfl

noncomputable instance : CommGroup (U ρ) where
  mul_assoc x y z := by ext; simp; ring
  one_mul x := by ext; simp
  mul_one x := by ext; simp
  inv_mul_cancel x := by
    ext; simp only [mul_val, inv_val, one_val]
    linear_combination (-x.val) * x.isUnit.mul_val_inv
  mul_comm x y := by ext; simp; ring

/-- `λ ↦ 1 + ρλ`, the homomorphism `𝒰_ρ → 𝔾_m`. -/
noncomputable def toGm : U ρ →* Rˣ where
  toFun x := x.isUnit.unit
  map_one' := by ext; simp
  map_mul' x y := by ext; simp; ring

@[simp] lemma toGm_val (x : U ρ) : (toGm x : R) = 1 + ρ * x.val := rfl

end U

open U

theorem toGm_bijective {ρ : R} (hρ : IsUnit ρ) : Function.Bijective (toGm (ρ := ρ)) :=
    ⟨fun x y h => by
      have h' : 1 + ρ * x.val = 1 + ρ * y.val := by
        simpa using congrArg (fun v : Rˣ => (v : R)) h
      ext; exact hρ.mul_left_cancel (by linear_combination h'),
     fun v => ⟨⟨↑hρ.unit⁻¹ * ((v : R) - 1), by
        have : 1 + ρ * (↑hρ.unit⁻¹ * ((v : R) - 1)) = v := by
          linear_combination ((v : R) - 1) * hρ.mul_val_inv
        rw [this]; exact v.isUnit⟩, by
        ext; simp only [toGm_val]; linear_combination ((v : R) - 1) * hρ.mul_val_inv⟩⟩

/-- Where `ρ` is invertible, `𝒰_ρ ≅ 𝔾_m` (the centre at finite distance). -/
noncomputable def toUnitsEquiv {ρ : R} (hρ : IsUnit ρ) : U ρ ≃* Rˣ :=
  MulEquiv.ofBijective toGm (toGm_bijective hρ)

/-- For `ρ = 0`, `𝒰₀ = 𝔾_a` (the centre at infinity). -/
def U_zero : U (0 : R) ≃* Multiplicative R where
  toFun x := Multiplicative.ofAdd x.val
  invFun a := ⟨a.toAdd, by simp⟩
  left_inv x := by ext; simp
  right_inv a := by simp
  map_mul' x y := by simp [← ofAdd_add]

/-- `λ ↦ 1 + ρλ` is onto the units over every `R`-algebra iff `ρ` is a unit: the
morphism `𝒰_ρ → 𝔾_m` is an isomorphism exactly where the centre is at finite
distance. -/
theorem forall_surjective_iff (ρ : R) :
    (∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Surjective (toGm (ρ := algebraMap R A ρ))) ↔ IsUnit ρ := by
  constructor
  · intro h
    let ε : DualNumber R := DualNumber.eps
    have hu : IsUnit (1 + ε) :=
      IsUnit.of_mul_eq_one (1 - ε) (by
        have : ε * ε = 0 := DualNumber.eps_mul_eps
        linear_combination (-1 : DualNumber R) * this)
    obtain ⟨x, hx⟩ := h (DualNumber R) hu.unit
    have h1 : 1 + algebraMap R (DualNumber R) ρ * x.val = 1 + ε := by
      simpa using congrArg (fun v : (DualNumber R)ˣ => (v : DualNumber R)) hx
    have h2 : algebraMap R (DualNumber R) ρ * x.val = ε := add_left_cancel h1
    have h3 : ρ * x.val.snd = 1 := by
      simpa [ε, TrivSqZeroExt.algebraMap_eq_inl] using congrArg TrivSqZeroExt.snd h2
    exact IsUnit.of_mul_eq_one _ h3
  · intro hρ A _ _
    exact (toGm_bijective (hρ.map (algebraMap R A))).2

/-! ### The realisation in coordinates -/

variable (n : ℕ) (μ β : ℕ → R)

/-- The coordinate of index `k`, zero beyond `n + 1`. -/
def co (k : ℕ) : (Fin (n + 2) → R) →ₗ[R] R :=
  if h : k < n + 2 then LinearMap.proj (⟨k, h⟩ : Fin (n + 2)) else 0

/-- The basis vector `e_k` (`e₀ = s₀`, `e_{i+1} = aᵢ`). -/
def e (k : ℕ) : Fin (n + 2) → R := fun j => if (j : ℕ) = k then 1 else 0

/-- The form `a'ᵢ`: `⟨a_{i−1}, a'ᵢ⟩ = 1`, `⟨aᵢ, a'ᵢ⟩ = μᵢ`, `⟨a_{i+1}, a'ᵢ⟩ = βᵢ`. -/
def F (i : ℕ) : (Fin (n + 2) → R) →ₗ[R] R :=
  co n i + μ i • co n (i + 1) + β i • co n (i + 2)

/-- The pseudo-reflection `τᵢ = id + a'ᵢ ⊗ aᵢ`. -/
def τ (i : ℕ) : Module.End R (Fin (n + 2) → R) :=
  1 + (F n μ β i).smulRight (e n (i + 1))

variable {n}

lemma co_of_lt {k : ℕ} (h : k < n + 2) (x : Fin (n + 2) → R) :
    co n k x = x ⟨k, h⟩ := by simp [co, h]

lemma co_of_le {k : ℕ} (h : n + 2 ≤ k) (x : Fin (n + 2) → R) : co n k x = 0 := by
  simp [co, show ¬ k < n + 2 by omega]

lemma co_e (j k : ℕ) (hk : k < n + 2) :
    co n j (e n k : Fin (n + 2) → R) = if j = k then 1 else 0 := by
  by_cases hj : j < n + 2
  · simp [co_of_lt hj, e]
  · rw [co_of_le (by omega)]; simp [show j ≠ k by omega]

lemma co_zero_apply (x : Fin (n + 2) → R) : co n 0 x = x 0 := by
  rw [co_of_lt (by omega)]; rfl

lemma co_e_self (k : ℕ) (hk : k < n + 2) : co n k (e n k : Fin (n + 2) → R) = 1 := by
  simp [co_of_lt hk, e]

lemma co_e_ne {j k : ℕ} (h : j ≠ k) : co n j (e n k : Fin (n + 2) → R) = 0 := by
  by_cases hj : j < n + 2
  · simp [co_of_lt hj, e, h]
  · exact co_of_le (by omega) _

lemma e_val (j : Fin (n + 2)) (r : R) : Pi.single j r = r • (e n j : Fin (n + 2) → R) := by
  funext k; simp [e, Pi.single_apply, Fin.ext_iff]

lemma τ_apply (i : ℕ) (x : Fin (n + 2) → R) :
    τ n μ β i x = x + F n μ β i x • e n (i + 1) := rfl

lemma co_τ_zero (i : ℕ) (x : Fin (n + 2) → R) : co n 0 (τ n μ β i x) = co n 0 x := by
  simp [τ_apply, co_e_ne (show 0 ≠ i + 1 by omega)]

lemma F_e_far {i k : ℕ} (h0 : k ≠ i) (h1 : k ≠ i + 1) (h2 : k ≠ i + 2) :
    F n μ β i (e n k) = 0 := by
  simp [F, co_e_ne (Ne.symm h0), co_e_ne (Ne.symm h1), co_e_ne (Ne.symm h2)]

/-- The non-consecutive `τᵢ` commute (relation (7) of page 96). -/
theorem τ_comm {i j : ℕ} (hij : i + 2 ≤ j) :
    τ n μ β i * τ n μ β j = τ n μ β j * τ n μ β i := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, τ_apply, map_add, map_smul, F_e_far μ β (show j + 1 ≠ i by omega)
    (show j + 1 ≠ i + 1 by omega) (show j + 1 ≠ i + 2 by omega),
    F_e_far μ β (show i + 1 ≠ j by omega) (show i + 1 ≠ j + 1 by omega)
      (show i + 1 ≠ j + 2 by omega),
    zero_smul, add_zero]
  abel

/-! ### Back-substitution: the vector `c̃` -/

/-- `(y_{top−m}, y_{top−m+1})` for the solution of `F_k y = 0` (`k < top`) with
`y_top = 1`, `y_k = 0` for `k > top`. -/
def cc (top : ℕ) : ℕ → R × R
  | 0 => (1, 0)
  | m + 1 => (-(μ (top - 1 - m) * (cc top m).1 + β (top - 1 - m) * (cc top m).2), (cc top m).1)

/-- The coordinates of the back-substituted vector with top index `top`. -/
def y (top k : ℕ) : R := if k ≤ top then (cc μ β top (top - k)).1 else 0

variable {μ β}

lemma y_top (top : ℕ) : y μ β top top = 1 := by simp [y, cc]

lemma y_of_lt {top k : ℕ} (h : top < k) : y μ β top k = 0 := by
  simp [y, show ¬ k ≤ top by omega]

lemma y_rec {top k : ℕ} (h : k < top) :
    y μ β top k = -(μ k * y μ β top (k + 1) + β k * y μ β top (k + 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, top = k + 1 + m := ⟨top - k - 1, by omega⟩
  have hA : y μ β (k + 1 + m) k =
      -(μ k * (cc μ β (k + 1 + m) m).1 + β k * (cc μ β (k + 1 + m) m).2) := by
    simp only [y, show k ≤ k + 1 + m by omega, ↓reduceIte, show k + 1 + m - k = m + 1 by omega, cc,
      show k + 1 + m - 1 - m = k by omega]
  have hB : y μ β (k + 1 + m) (k + 1) = (cc μ β (k + 1 + m) m).1 := by
    simp only [y, show k + 1 ≤ k + 1 + m by omega, ↓reduceIte,
      show k + 1 + m - (k + 1) = m by omega]
  have hC : y μ β (k + 1 + m) (k + 2) = (cc μ β (k + 1 + m) m).2 := by
    rcases m with _ | m
    · simp [y, cc]
    · simp only [y, show k + 2 ≤ k + 1 + (m + 1) by omega, ↓reduceIte,
        show k + 1 + (m + 1) - (k + 2) = m by omega, cc]
  rw [hA, hB, hC]

variable (μ β) in
/-- The vector with coordinates `y top`. -/
def vec (top : ℕ) : Fin (n + 2) → R := fun j => y μ β top j

lemma co_vec {top : ℕ} (htop : top ≤ n + 1) (k : ℕ) :
    co n k (vec μ β top) = y μ β top k := by
  by_cases hk : k < n + 2
  · rw [co_of_lt hk]; rfl
  · rw [co_of_le (by omega), y_of_lt (by omega)]

lemma F_apply (i : ℕ) (x : Fin (n + 2) → R) :
    F n μ β i x = co n i x + μ i * co n (i + 1) x + β i * co n (i + 2) x := rfl

lemma F_vec {top i : ℕ} (htop : top ≤ n + 1) (hi : i < top) : F n μ β i (vec μ β top) = 0 := by
  rw [F_apply, co_vec htop, co_vec htop, co_vec htop, y_rec hi]; ring

/-- The kernel of `F₀, …, F_{top−1}` among the vectors supported in `[0, top]` is the
line of `vec top`. -/
theorem eq_smul_vec {top : ℕ} (htop : top ≤ n + 1) (v : Fin (n + 2) → R)
    (hsupp : ∀ k, top < k → co n k v = 0) (hF : ∀ i < top, F n μ β i v = 0) :
    v = co n top v • vec μ β top := by
  set w := v - co n top v • vec μ β top with hw
  have hco : ∀ k, co n k w = co n k v - co n top v * y μ β top k := by
    intro k; simp [hw, co_vec htop]
  have hFw : ∀ i < top, F n μ β i w = 0 := by
    intro i hi; simp [hw, hF i hi, F_vec htop hi]
  have key : ∀ m k, top ≤ k + m → co n k w = 0 := by
    intro m
    induction m with
    | zero =>
      intro k hk
      rcases (show top < k ∨ k = top by omega) with h | rfl
      · rw [hco, hsupp k h, y_of_lt h]; ring
      · rw [hco, y_top]; ring
    | succ m ih =>
      intro k hk
      by_cases h : top ≤ k + m
      · exact ih k h
      · have hkt : k < top := by omega
        have h1 := ih (k + 1) (by omega)
        have h2 := ih (k + 2) (by omega)
        have := hFw k hkt
        rw [F_apply, h1, h2] at this
        simpa using this
  have hw0 : w = 0 := by
    funext j
    have := key top j (by omega)
    rwa [co_of_lt j.isLt] at this
  exact sub_eq_zero.mp hw0

/-! ### `c̃`, `ρ` and the action `u_λ` -/

variable (n μ β)

/-- `c̃`: killed by every `a'ᵢ`, coordinate `1` on `aₙ`. -/
def ct : Fin (n + 2) → R := vec μ β (n + 1)

/-- `ρ = π(c̃)`. -/
def ρ : R := y μ β (n + 1) 0

/-- `π ⊗ c̃`. -/
def P : Module.End R (Fin (n + 2) → R) := (co n 0).smulRight (ct n μ β)

/-- `u_λ = id + λ π ⊗ c̃`. -/
def u (t : R) : Module.End R (Fin (n + 2) → R) := 1 + t • P n μ β

variable {n μ β}

lemma F_ct {i : ℕ} (hi : i ≤ n) : F n μ β i (ct n μ β) = 0 := F_vec le_rfl (by omega)

lemma co_ct_top : co n (n + 1) (ct n μ β) = 1 := by rw [ct, co_vec le_rfl, y_top]

lemma co_ct_zero : co n 0 (ct n μ β) = ρ n μ β := by rw [ct, co_vec le_rfl]; rfl

/-- For `n = 1`, `ρ = μ₀μ₁ − β₀`; for reflections (`μᵢ = −2`), `4 − β₀`. -/
theorem ρ_one : ρ 1 μ β = μ 0 * μ 1 - β 0 := by
  simp [ρ, y, cc]; ring

lemma P_apply (x : Fin (n + 2) → R) : P n μ β x = co n 0 x • ct n μ β := rfl

lemma P_mul_P : P n μ β * P n μ β = ρ n μ β • P n μ β := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, P_apply, LinearMap.smul_apply, map_smul, co_ct_zero, smul_smul]
  rw [mul_comm]

lemma u_apply (t : R) (x : Fin (n + 2) → R) :
    u n μ β t x = x + (t * co n 0 x) • ct n μ β := by
  simp [u, P_apply, smul_smul]

/-- `u_λ u_λ' = u_{λ + λ' + ρλλ'}`. -/
theorem u_mul (s t : R) : u n μ β s * u n μ β t = u n μ β (s + t + ρ n μ β * s * t) := by
  simp only [u, add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, P_mul_P, smul_smul,
    add_smul]
  rw [show s * t * ρ n μ β = ρ n μ β * s * t by ring]; abel

lemma τ_mul_P {i : ℕ} (hi : i ≤ n) : τ n μ β i * P n μ β = P n μ β := by
  refine LinearMap.ext fun x => ?_
  simp [P_apply, τ_apply, F_ct hi]

lemma P_mul_τ (i : ℕ) : P n μ β * τ n μ β i = P n μ β := by
  refine LinearMap.ext fun x => ?_
  simp [P_apply, co_τ_zero]

/-- `u_λ` commutes with the `τᵢ`. -/
theorem u_comm {i : ℕ} (hi : i ≤ n) (t : R) : u n μ β t * τ n μ β i = τ n μ β i * u n μ β t := by
  simp [u, add_mul, mul_add, P_mul_τ, τ_mul_P hi]

/-- `det u_λ = 1 + ρλ`. -/
theorem det_u (t : R) : LinearMap.det (u n μ β t) = 1 + ρ n μ β * t := by
  have hm : LinearMap.toMatrix' (u n μ β t) =
      1 + Matrix.replicateCol Unit (t • ct n μ β) *
        Matrix.replicateRow Unit (Pi.single 0 1 : Fin (n + 2) → R) := by
    ext i j
    rw [LinearMap.toMatrix'_apply, u_apply, co_zero_apply]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Finset.univ_unique,
      Finset.sum_singleton, Pi.single_apply]
    by_cases hj : j = 0
    · simp only [hj, ↓reduceIte]; ring
    · simp only [hj, Ne.symm hj, ↓reduceIte]; ring
  rw [← LinearMap.det_toMatrix', hm, Matrix.det_one_add_replicateCol_mul_replicateRow,
    single_dotProduct]
  simp only [Pi.smul_apply, smul_eq_mul, one_mul, ct, vec, ρ, Fin.val_zero]
  ring

/-! ### The automorphisms of the realisation -/

lemma comm_iff_apply (g : Module.End R (Fin (n + 2) → R)) (i : ℕ) :
    g * τ n μ β i = τ n μ β i * g ↔
      ∀ x, F n μ β i x • g (e n (i + 1)) = F n μ β i (g x) • e n (i + 1) := by
  constructor
  · intro h x
    have := congrArg (fun f => f x) h
    simpa [τ_apply] using this
  · intro h; refine LinearMap.ext fun x => ?_; simp [τ_apply, h x]

lemma F_e_self (i : ℕ) (hi : i ≤ n) : F n μ β i (e n i) = 1 := by
  simp [F_apply, co_e _ i (show i < n + 2 by omega)]

lemma F_e_zero {i : ℕ} (hi : 1 ≤ i) : F n μ β i (e n 0) = 0 := by
  simp [F_apply, co_e _ 0 (show 0 < n + 2 by omega), show i ≠ 0 by omega]

/-- The commutant of the `τᵢ`: an endomorphism commutes with all of them iff it is
`c + t π ⊗ c̃`. -/
theorem commute_iff (g : Module.End R (Fin (n + 2) → R)) :
    (∀ i ≤ n, g * τ n μ β i = τ n μ β i * g) ↔
      ∃ c t : R, g = c • 1 + t • P n μ β := by
  constructor
  · intro h
    -- `g aᵢ = cᵢ aᵢ` and `a'ᵢ ∘ g = cᵢ a'ᵢ`, with `cᵢ = a'ᵢ(g e_i)`
    have hga : ∀ i ≤ n, g (e n (i + 1)) = F n μ β i (g (e n i)) • e n (i + 1) := by
      intro i hi
      have := (comm_iff_apply g i).1 (h i hi) (e n i)
      rwa [F_e_self i hi, one_smul] at this
    have hFg : ∀ i ≤ n, ∀ x, F n μ β i (g x) = F n μ β i (g (e n i)) * F n μ β i x := by
      intro i hi x
      have h1 := (comm_iff_apply g i).1 (h i hi) x
      rw [hga i hi, smul_smul] at h1
      have h2 := congrArg (co n (i + 1)) h1
      simp only [map_smul, co_e _ _ (show i + 1 < n + 2 by omega), ↓reduceIte,
        smul_eq_mul, mul_one] at h2
      rw [← h2, mul_comm]
    set c := F n μ β 0 (g (e n 0)) with hc
    have hci : ∀ i ≤ n, F n μ β i (g (e n i)) = c := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [hga i (by omega), map_smul, F_e_self _ hi, ih (by omega), smul_eq_mul, mul_one]
    have hgk : ∀ k, 1 ≤ k → k ≤ n + 1 → g (e n k) = c • e n k := by
      intro k hk1 hk2
      obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      rw [hga i (by omega), hci i (by omega)]
    set w := g (e n 0) - c • e n 0 with hw
    have hFw : ∀ i < n + 1, F n μ β i w = 0 := by
      intro i hi
      rw [hw, map_sub, map_smul, hFg i (by omega), hci i (by omega), smul_eq_mul, sub_self]
    have hwct : w = co n (n + 1) w • ct n μ β :=
      eq_smul_vec le_rfl w (fun k hk => co_of_le (by omega) w) hFw
    refine ⟨c, co n (n + 1) w, ?_⟩
    apply LinearMap.pi_ext
    intro j r
    rw [e_val, map_smul, map_smul]
    congr 1
    rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
    · rw [h0, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
        Module.End.one_apply, P_apply, co_e_self 0 (by omega), one_smul, ← hwct, hw]
      abel
    · rw [hgk j hpos (by omega)]
      simp [P_apply, co_e 0 (j : ℕ) j.isLt, show (0 : ℕ) ≠ j by omega]
  · rintro ⟨c, t, rfl⟩ i hi
    simp [add_mul, mul_add, P_mul_τ, τ_mul_P hi]

/-- The pair `(c, t)` is unique. -/
theorem coeff_unique {c t c' t' : R}
    (h : c • (1 : Module.End R (Fin (n + 2) → R)) + t • P n μ β = c' • 1 + t' • P n μ β) :
    c = c' ∧ t = t' := by
  have h1 : c = c' := by
    simpa [P_apply, co_e 0 1 (show 1 < n + 2 by omega), co_e 1 1 (show 1 < n + 2 by omega)]
      using congrArg (fun f => co n 1 (f (e n 1))) h
  subst h1
  have h2 : t = t' := by
    simpa [P_apply, co_e 0 0 (show 0 < n + 2 by omega), co_e (n + 1) 0 (show 0 < n + 2 by omega),
      co_ct_top] using congrArg (fun f => co n (n + 1) (f (e n 0))) h
  exact ⟨rfl, h2⟩

lemma smul_one_add_mul (c t c' t' : R) :
    (c • (1 : Module.End R (Fin (n + 2) → R)) + t • P n μ β) * (c' • 1 + t' • P n μ β) =
      (c * c') • 1 + (c * t' + t * c' + t * t' * ρ n μ β) • P n μ β := by
  simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, P_mul_P, smul_smul, add_smul]
  abel

/-- `c + t π ⊗ c̃` is invertible iff `c` and `c + tρ` are units. -/
theorem isUnit_iff (c t : R) :
    IsUnit (c • (1 : Module.End R (Fin (n + 2) → R)) + t • P n μ β) ↔
      IsUnit c ∧ IsUnit (c + t * ρ n μ β) := by
  constructor
  · intro hg
    obtain ⟨g, hg⟩ := hg
    have hcomm : ∀ i ≤ n, (↑g⁻¹ : Module.End R (Fin (n + 2) → R)) * τ n μ β i =
        τ n μ β i * ↑g⁻¹ := by
      intro i hi
      have h1 : (↑g : Module.End R (Fin (n + 2) → R)) * τ n μ β i = τ n μ β i * ↑g := by
        rw [hg]; exact (commute_iff _).2 ⟨c, t, rfl⟩ i hi
      calc (↑g⁻¹ : Module.End R (Fin (n + 2) → R)) * τ n μ β i
          = ↑g⁻¹ * (τ n μ β i * ↑g) * ↑g⁻¹ := by simp [mul_assoc]
        _ = ↑g⁻¹ * (↑g * τ n μ β i) * ↑g⁻¹ := by rw [h1]
        _ = τ n μ β i * ↑g⁻¹ := by simp [← mul_assoc]
    obtain ⟨c', t', hinv⟩ := (commute_iff _).1 hcomm
    have hmul : (c • (1 : Module.End R (Fin (n + 2) → R)) + t • P n μ β) *
        (c' • 1 + t' • P n μ β) = 1 := by rw [← hg, ← hinv]; simp
    rw [smul_one_add_mul] at hmul
    obtain ⟨h1, h2⟩ := coeff_unique (n := n) (μ := μ) (β := β) (c := c * c')
      (t := c * t' + t * c' + t * t' * ρ n μ β) (c' := (1 : R)) (t' := 0) (by rw [hmul]; simp)
    refine ⟨IsUnit.of_mul_eq_one _ h1, IsUnit.of_mul_eq_one (c' + t' * ρ n μ β) ?_⟩
    linear_combination h1 + ρ n μ β * h2
  · rintro ⟨hc, hd⟩
    set a : R := ↑hc.unit⁻¹
    set b : R := ↑hd.unit⁻¹
    have e1 : c * a = 1 := hc.mul_val_inv
    have e2 : (c + t * ρ n μ β) * b = 1 := hd.mul_val_inv
    have key : ∀ c₁ t₁ c₂ t₂ : R, c₁ * c₂ = 1 → c₁ * t₂ + t₁ * c₂ + t₁ * t₂ * ρ n μ β = 0 →
        (c₁ • (1 : Module.End R (Fin (n + 2) → R)) + t₁ • P n μ β) *
          (c₂ • 1 + t₂ • P n μ β) = 1 := by
      intro c₁ t₁ c₂ t₂ h1 h2; rw [smul_one_add_mul, h1, h2]; simp
    have h0 : c * (-t * a * b) + t * a + t * (-t * a * b) * ρ n μ β = 0 := by
      linear_combination (-(t * a)) * e2
    exact ⟨⟨_, a • 1 + (-t * a * b) • P n μ β, key _ _ _ _ e1 h0,
      key _ _ _ _ (by rw [mul_comm]; exact e1) (by linear_combination (-(t * a)) * e2)⟩, rfl⟩

/-- The automorphisms of `(E, (τᵢ))`. -/
def centraliser (n : ℕ) (μ β : ℕ → R) : Subgroup (Module.End R (Fin (n + 2) → R))ˣ where
  carrier := {g | ∀ i ≤ n, (↑g : Module.End R (Fin (n + 2) → R)) * τ n μ β i = τ n μ β i * ↑g}
  one_mem' := by intro i _; simp
  mul_mem' := by
    intro a b ha hb i hi
    change (↑a * ↑b : Module.End R (Fin (n + 2) → R)) * τ n μ β i = τ n μ β i * (↑a * ↑b)
    rw [mul_assoc, hb i hi, ← mul_assoc, ha i hi, mul_assoc]
  inv_mem' := by
    intro a ha i hi
    calc (↑a⁻¹ : Module.End R (Fin (n + 2) → R)) * τ n μ β i
        = ↑a⁻¹ * (τ n μ β i * ↑a) * ↑a⁻¹ := by simp [mul_assoc]
      _ = ↑a⁻¹ * (↑a * τ n μ β i) * ↑a⁻¹ := by rw [ha i hi]
      _ = τ n μ β i * ↑a⁻¹ := by simp [← mul_assoc]

lemma u_zero : u n μ β 0 = 1 := by simp [u]

/-- `c • u_λ`, as a unit. -/
noncomputable def cu (p : Rˣ × U (ρ n μ β)) : (Module.End R (Fin (n + 2) → R))ˣ where
  val := (p.1 : R) • u n μ β p.2.val
  inv := (↑p.1⁻¹ : R) • u n μ β (p.2⁻¹).val
  val_inv := by
    rw [smul_mul_smul_comm, u_mul, ← U.mul_val, mul_inv_cancel, U.one_val, u_zero]; simp
  inv_val := by
    rw [smul_mul_smul_comm, u_mul, ← U.mul_val, inv_mul_cancel, U.one_val, u_zero]; simp

lemma cu_val (p : Rˣ × U (ρ n μ β)) :
    (cu p : Module.End R _) = (p.1 : R) • 1 + ((p.1 : R) * p.2.val) • P n μ β := by
  simp [cu, u, smul_add, smul_smul]

lemma cu_mem (p : Rˣ × U (ρ n μ β)) : cu p ∈ centraliser n μ β := by
  intro i hi
  rw [cu_val]; exact (commute_iff _).2 ⟨_, _, rfl⟩ i hi

/-- `(c, λ) ↦ c u_λ`. -/
noncomputable def cuHom : Rˣ × U (ρ n μ β) →* centraliser n μ β where
  toFun p := ⟨cu p, cu_mem p⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    change ((1 : Rˣ) : R) • u n μ β (1 : U (ρ n μ β)).val = 1
    simp [u_zero]
  map_mul' p q := by
    apply Subtype.ext; apply Units.ext
    change ((p * q).1 : R) • u n μ β (p * q).2.val =
      ((p.1 : R) • u n μ β p.2.val) * ((q.1 : R) • u n μ β q.2.val)
    rw [smul_mul_smul_comm, u_mul]
    simp

/-- **`𝔾_m × 𝒰_ρ ≅ Aut(E, (τᵢ))`** on `R`-points: `(c, λ) ↦ c u_λ`. -/
noncomputable def centraliserEquiv : Rˣ × U (ρ n μ β) ≃* centraliser n μ β :=
  MulEquiv.ofBijective cuHom
    ⟨by
      intro p q h
      have h' := congrArg (fun g : centraliser n μ β =>
        ((g : (Module.End R (Fin (n + 2) → R))ˣ) : Module.End R (Fin (n + 2) → R))) h
      change (↑(cu p) : Module.End R (Fin (n + 2) → R)) = ↑(cu q) at h'
      rw [cu_val, cu_val] at h'
      obtain ⟨h1, h2⟩ := coeff_unique h'
      have h1' : p.1 = q.1 := Units.ext h1
      rw [h1] at h2
      exact Prod.ext h1' (U.ext (q.1.isUnit.mul_left_cancel h2)),
     by
      rintro ⟨g, hg⟩
      have hg' : ∀ i ≤ n, (↑g : Module.End R (Fin (n + 2) → R)) * τ n μ β i = τ n μ β i * ↑g := hg
      obtain ⟨c, t, hct⟩ := (commute_iff (↑g : Module.End R (Fin (n + 2) → R))).1 hg'
      obtain ⟨hc, hd⟩ := (isUnit_iff c t).1 (hct ▸ g.isUnit)
      refine ⟨(hc.unit, ⟨↑hc.unit⁻¹ * t, ?_⟩), ?_⟩
      · have : 1 + ρ n μ β * (↑hc.unit⁻¹ * t) = ↑hc.unit⁻¹ * (c + t * ρ n μ β) := by
          linear_combination (-1 : R) * hc.val_inv_mul
        rw [this]; exact (Units.isUnit _).mul hd
      · apply Subtype.ext; apply Units.ext
        change (hc.unit : R) • u n μ β (↑hc.unit⁻¹ * t) = ↑g
        rw [hct]
        simp only [u, IsUnit.unit_spec, smul_add, smul_smul]
        rw [← mul_assoc, hc.mul_val_inv, one_mul]⟩

/-! ### The start points: a torsor under `𝒰_ρ` -/

/-- The points of `D₀ = H₁ ∩ ⋯ ∩ Hₙ` are the `a s₀ + t c̃`. -/
theorem mem_D0_iff (s : Fin (n + 2) → R) :
    (∀ i, 1 ≤ i → i ≤ n → F n μ β i s = 0) ↔ ∃ a t : R, s = a • e n 0 + t • ct n μ β := by
  constructor
  · intro h
    set v := s - F n μ β 0 s • e n 0 with hv
    have hFv : ∀ i < n + 1, F n μ β i v = 0 := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · simp [hv, F_e_self 0 (by omega)]
      · simp [hv, h i hpos (by omega), F_e_zero hpos]
    have hv' : v = co n (n + 1) v • ct n μ β :=
      eq_smul_vec le_rfl v (fun k hk => co_of_le (by omega) v) hFv
    refine ⟨F n μ β 0 s, co n (n + 1) v, ?_⟩
    rw [← hv', hv]; abel
  · rintro ⟨a, t, rfl⟩ i hi1 hi2
    simp [F_e_zero hi1, F_ct hi2]

lemma u_e0 (t : R) : u n μ β t (e n 0) = e n 0 + t • ct n μ β := by
  simp [u_apply, co_e 0 0 (show 0 < n + 2 by omega)]

/-- The start points off `c` (`⟨s, a'₀⟩` a unit, normalised to `1`) and off `d`
(`π(s)` a unit), in `D₀`. -/
def startPoints : Set (Fin (n + 2) → R) :=
  {s | (∀ i, 1 ≤ i → i ≤ n → F n μ β i s = 0) ∧ F n μ β 0 s = 1 ∧ IsUnit (co n 0 s)}

/-- `D₀ ∖ {c, d} = 𝒰_ρ · s₀`. -/
theorem mem_startPoints_iff (s : Fin (n + 2) → R) :
    s ∈ startPoints (n := n) (μ := μ) (β := β) ↔ ∃ x : U (ρ n μ β), s = u n μ β x.val (e n 0) := by
  constructor
  · rintro ⟨hD, hF0, hπ⟩
    obtain ⟨a, t, rfl⟩ := (mem_D0_iff s).1 hD
    have ha : a = 1 := by simpa [F_e_self 0 (by omega), F_ct (show 0 ≤ n by omega)] using hF0
    subst ha
    refine ⟨⟨t, ?_⟩, by rw [u_e0, one_smul]⟩
    have : co n 0 ((1 : R) • e n 0 + t • ct n μ β) = 1 + ρ n μ β * t := by
      simp [co_e 0 0 (show 0 < n + 2 by omega), co_ct_zero, mul_comm]
    convert hπ using 1; exact this.symm
  · rintro ⟨x, rfl⟩
    rw [u_e0]
    refine ⟨fun i hi1 hi2 => by simp [F_e_zero hi1, F_ct hi2], ?_, ?_⟩
    · simp [F_e_self 0 (by omega), F_ct (show 0 ≤ n by omega)]
    · have : co n 0 (e n 0 + x.val • ct n μ β) = 1 + ρ n μ β * x.val := by
        simp [co_e 0 0 (show 0 < n + 2 by omega), co_ct_zero, mul_comm]
      rw [this]; exact x.isUnit

/-- The orbit map `λ ↦ u_λ s₀` is injective: the action is free. -/
theorem u_e0_injective {x y : U (ρ n μ β)}
    (h : u n μ β x.val (e n 0) = u n μ β y.val (e n 0)) : x = y := by
  exact U.ext (by
    simpa [u_e0, co_e (n + 1) 0 (show 0 < n + 2 by omega), co_ct_top]
      using congrArg (co n (n + 1)) h)

/-- The action: `u_μ (u_λ s₀) = u_{λ * μ} s₀`. -/
theorem u_u_e0 (x y : U (ρ n μ β)) :
    u n μ β y.val (u n μ β x.val (e n 0)) = u n μ β (x * y).val (e n 0) := by
  rw [← Module.End.mul_apply, u_mul, U.mul_val]
  congr 2; ring

end Grothendieck.Folder72
