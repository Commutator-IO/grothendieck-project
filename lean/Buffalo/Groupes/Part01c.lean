import Buffalo.Groupes.Part01a

/-!
# Buffalo, algebraic groups, Part 01 (c): `μ_n`, `SL_n`, `PGL_n`, `α_{p^i}` and Frobenius

Entries `_lTf_L0yvrU-6199` to `_lTf_L0yvrU-8015` of `docs/buffalo-groupes/index.tex` (6 June and
the beginning of 11 June 1973). Statuses in `docs/buffalo-groupes/lean/Part01.json`.

Dual numbers `k[ε]` (Mathlib `DualNumber k`) serve as the test algebra on which the infinitesimal
groups `μ_p`, `α_p` and the Frobenius kernels have non-trivial points.
-/

namespace Buffalo.Groupes.Part01

open Polynomial

universe u

variable (k : Type u) [CommRing k]

/-! ## The groups `μ_n` -/

/-- _lTf_L0yvrU-6199 (1:43:19) [def] `μ_n` is the kernel of `λ ↦ λⁿ` on `𝔾_m`. -/
theorem rootsOfUnity_eq_ker (n : ℕ) (A : Type*) [CommMonoid A] :
    rootsOfUnity n A = (powMonoidHom n : Aˣ →* Aˣ).ker := by
  ext; simp [mem_rootsOfUnity]

/-- _lTf_L0yvrU-6328 (1:45:28) [prop] `μ_n` is represented by `k[t]/(tⁿ - 1)`. -/
noncomputable def mu_repr (n : ℕ) [NeZero n] (A : Type u) [CommRing A] [Algebra k A] :
    (AdjoinRoot (X ^ n - C 1 : k[X]) →ₐ[k] A) ≃ rootsOfUnity n A :=
  (adjoinRootHomEquiv k _ A).trans
  { toFun a := ⟨Units.ofPowEqOne a.1 n (by have := a.2; simp_all [sub_eq_zero]) (NeZero.ne n), by
      rw [mem_rootsOfUnity]; ext; have := a.2; simp_all [sub_eq_zero]⟩
    invFun ζ := ⟨(ζ : Aˣ), by simpa [sub_eq_zero] using congrArg Units.val ζ.2⟩
    left_inv _ := Subtype.ext rfl
    right_inv _ := Subtype.ext (Units.ext rfl) }

/-- _lTf_L0yvrU-6328 (1:45:28) [prop] `k[t]/(tⁿ - 1)` is free of rank `n`, with basis
`1, x, …, x^{n-1}` (Mathlib `AdjoinRoot.powerBasis'`). -/
theorem mu_rank [Nontrivial k] (n : ℕ) (hn : n ≠ 0) :
    (AdjoinRoot.powerBasis' (monic_X_pow_sub_C (1 : k) hn)).dim = n := by
  simp only [AdjoinRoot.powerBasis']
  exact natDegree_X_pow_sub_C

/-- _lTf_L0yvrU-6393 (1:46:33) [def] An affine space is finite over `k` when its algebra is a
finitely generated `k`-module; `μ_n` is finite. -/
theorem mu_finite (n : ℕ) (hn : n ≠ 0) : Module.Finite k (AdjoinRoot (X ^ n - C 1 : k[X])) :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C (1 : k) hn)).finite

/-- In characteristic `p`, `y^{p^v} = 1` iff `y = 1`, in a reduced ring. -/
theorem pow_char_pow_eq_one_iff {K : Type*} [CommRing K] [IsReduced K] (p : ℕ) [ExpChar K p]
    (v : ℕ) (y : K) : y ^ p ^ v = 1 ↔ y = 1 := by
  constructor
  · intro h
    have : (y - 1) ^ p ^ v = 0 := by rw [sub_pow_expChar_pow, h, one_pow, sub_self]
    exact sub_eq_zero.mp (IsReduced.eq_zero _ ⟨_, this⟩)
  · rintro rfl; exact one_pow _

/-- In characteristic `p`, on a reduced ring, `μ_{p^v m} = μ_m`. -/
theorem rootsOfUnity_char_mul {K : Type*} [CommRing K] [IsReduced K] (p : ℕ) [ExpChar K p]
    (v m : ℕ) : rootsOfUnity (p ^ v * m) K = rootsOfUnity m K := by
  ext ζ
  simp only [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
  rw [mul_comm, pow_mul, pow_char_pow_eq_one_iff]

/-- _lTf_L0yvrU-6521 (1:48:41) [prop] Over an algebraically closed field `K` of characteristic `p`,
`μ_n(K)` is cyclic of order `n'`, the prime-to-`p` part of `n = p^v n'`. -/
theorem mu_algClosed (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (v n' : ℕ) (hn' : ¬ p ∣ n') :
    rootsOfUnity (p ^ v * n') K = rootsOfUnity n' K ∧ Nat.card (rootsOfUnity n' K) = n' ∧
      IsCyclic (rootsOfUnity n' K) := by
  have : NeZero (n' : K) := ⟨fun h ↦ hn' ((CharP.cast_eq_zero_iff K p n').mp h)⟩
  have : NeZero n' := .of_neZero_natCast K
  exact ⟨rootsOfUnity_char_mul p v n', HasEnoughRootsOfUnity.natCard_rootsOfUnity K n',
    inferInstance⟩

/-- `1 + ε`, a unit of the dual numbers. -/
def onePlusEps : (DualNumber k)ˣ where
  val := 1 + DualNumber.eps
  inv := 1 - DualNumber.eps
  val_inv := by rw [mul_sub, mul_one, add_mul, one_mul, DualNumber.eps_mul_eps, add_zero,
    add_sub_cancel_right]
  inv_val := by rw [mul_add, mul_one, sub_mul, one_mul, DualNumber.eps_mul_eps, sub_zero,
    sub_add_cancel]

theorem onePlusEps_pow (m : ℕ) :
    ((onePlusEps k ^ m : (DualNumber k)ˣ) : DualNumber k) = 1 + (m : DualNumber k) * DualNumber.eps := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Units.val_mul, ih]
    simp only [onePlusEps]
    rw [add_mul, one_mul, mul_add, mul_one, mul_assoc, DualNumber.eps_mul_eps, mul_zero, add_zero]
    push_cast; ring

theorem onePlusEps_ne_one [Nontrivial k] : onePlusEps k ≠ 1 := by
  intro h
  have := congrArg (fun u : (DualNumber k)ˣ ↦ TrivSqZeroExt.snd (u : DualNumber k)) h
  simp [onePlusEps] at this

/-- _lTf_L0yvrU-6586 (1:49:46) [cex] In characteristic `p`, `μ_{p^i}(K)` is trivial for every
field `K` (indeed every reduced ring)… -/
theorem mu_p_trivial {K : Type*} [CommRing K] [IsReduced K] (p : ℕ) [ExpChar K p] (i : ℕ)
    (ζ : rootsOfUnity (p ^ i) K) : ζ = 1 := by
  have := ζ.2
  rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one,
    pow_char_pow_eq_one_iff] at this
  exact Subtype.ext (Units.ext this)

/-- _lTf_L0yvrU-6586 (1:49:46) [cex] … yet `μ_{p^i}` (`i ≥ 1`) is not the trivial group: `1 + ε` is
a non-trivial point over `k[ε]` (`k ≠ 0` of characteristic `p`). -/
theorem mu_p_nontrivial [Nontrivial k] (p : ℕ) [CharP k p] (i : ℕ) (hi : i ≠ 0) :
    onePlusEps k ∈ rootsOfUnity (p ^ i) (DualNumber k) ∧ onePlusEps k ≠ 1 := by
  refine ⟨?_, onePlusEps_ne_one k⟩
  rw [mem_rootsOfUnity]
  apply Units.ext
  rw [onePlusEps_pow, Units.val_one]
  have : ((p ^ i : ℕ) : DualNumber k) = 0 := by
    rw [← map_natCast (algebraMap k (DualNumber k)), (CharP.cast_eq_zero_iff k p _).mpr
      (dvd_pow_self p hi), map_zero]
  rw [this, zero_mul, add_zero]

/-- The Frobenius `λ ↦ λ^p` on `𝔾_m`, on points. -/
def frobUnits (A : Type*) [CommRing A] (p : ℕ) : Aˣ →* Aˣ := powMonoidHom p

/-- _lTf_L0yvrU-6715 (1:51:55) [cex] On a perfect field `K` of characteristic `p`, `λ ↦ λ^p` is
bijective on `𝔾_m(K)`… -/
theorem frobUnits_bijective (K : Type*) [Field K] (p : ℕ) [ExpChar K p] [PerfectField K] :
    Function.Bijective (frobUnits K p) := by
  have hb : Function.Bijective (frobenius K p) := bijective_frobenius K p
  refine ⟨fun a b h ↦ Units.ext (hb.1 (by
    rw [frobenius_def, frobenius_def]; simpa [frobUnits] using congrArg Units.val h)),
    fun u ↦ ?_⟩
  obtain ⟨x, hx⟩ := hb.2 u
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hx
    exact u.ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, Units.ext (by simp [frobUnits, ← hx, frobenius_def])⟩

/-- _lTf_L0yvrU-6715 (1:51:55) [cex] … but it is not an isomorphism `𝔾_m → 𝔾_m`: it is not
injective on `k[ε]`-points (its kernel `μ_p` contains `1 + ε`). -/
theorem frobUnits_not_injective [Nontrivial k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    ¬ Function.Injective (frobUnits (DualNumber k) p) := by
  intro h
  apply onePlusEps_ne_one k
  apply h
  have := (mu_p_nontrivial k p 1 one_ne_zero).1
  rw [mem_rootsOfUnity, pow_one] at this
  simpa [frobUnits] using this

/-! ## `SL_n`, `PGL_n` and centers -/

/-- _lTf_L0yvrU-6843 (1:54:03) [def] `SL_n` is the kernel of `det : GL_n → 𝔾_m`. -/
theorem SL_eq_ker_det (n : Type) [Fintype n] [DecidableEq n] (A : Type*) [CommRing A] :
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup n A →* _).range =
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup n A →* Aˣ).ker := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    ext
    simp
  · intro hg
    refine ⟨⟨g, by simpa [Units.ext_iff] using hg⟩, ?_⟩
    ext; rfl

/-- _lTf_L0yvrU-6906 (1:55:06) [prop] The center of `GL_n` is `𝔾_m` embedded as the scalar
matrices (Mathlib `Matrix.GeneralLinearGroup.center_eq_range_scalar`). -/
theorem center_GL (n : Type) [Fintype n] [DecidableEq n] (A : Type*) [CommRing A] :
    Subgroup.center (Matrix.GeneralLinearGroup n A) = (Matrix.GeneralLinearGroup.scalar n).range :=
  Matrix.GeneralLinearGroup.center_eq_range_scalar

/-- _lTf_L0yvrU-7035 (1:57:15) [prop] `SL_n ∩ (scalars) = μ_n`: `det(λ I_n) = λⁿ`. -/
theorem scalar_det_eq_one_iff (n : Type) [Fintype n] [DecidableEq n] {A : Type*} [CommRing A]
    (c : Aˣ) : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar n c) = 1 ↔
      c ∈ rootsOfUnity (Fintype.card n) A := by
  rw [mem_rootsOfUnity, Units.ext_iff, Units.ext_iff]
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_diagonal]

/-- _lTf_L0yvrU-7099 (1:58:19) [prop] The center of `SL_n` is `μ_n` (Mathlib
`Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity`; `n ≥ 1`). -/
noncomputable def center_SL (n : Type) [Fintype n] [DecidableEq n] (A : Type*) [CommRing A] :
    Subgroup.center (Matrix.SpecialLinearGroup n A) ≃*
      rootsOfUnity (max (Fintype.card n) 1) A :=
  Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity

/-- _lTf_L0yvrU-7164 (1:59:24) [prop] On points over an algebraically closed field,
`GL_n/(center) = PGL_n ≃ SL_n/μ_n = PSL_n` (Mathlib
`Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed`); the quotients as group schemes are not formalised. -/
noncomputable def PGL_eq_PSL (n : Type) [Fintype n] [DecidableEq n] (F : Type*) [Field F]
    [IsAlgClosed F] :
    Matrix.ProjGenLinGroup n F ≃* Matrix.ProjectiveSpecialLinearGroup n F :=
  Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed

/-- _lTf_L0yvrU-7227 (2:00:27) [cex] In characteristic `p`, the kernel `μ_p` of `SL_p → PGL_p` is
non-trivial: `(1+ε) I_p ∈ SL_p(k[ε])` is a non-trivial central (scalar) element, although
`μ_p(K) = 1` for every field `K` (`mu_p_trivial`). -/
theorem SL_p_scalar_nontrivial [Nontrivial k] (p : ℕ) [CharP k p] (hp : p ≠ 0) :
    Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (Fin p) (onePlusEps k)) = 1 ∧
      Matrix.GeneralLinearGroup.scalar (Fin p) (onePlusEps k) ≠ 1 ∧
      Matrix.GeneralLinearGroup.scalar (Fin p) (onePlusEps k) ∈
        Subgroup.center (Matrix.GeneralLinearGroup (Fin p) (DualNumber k)) := by
  have hmem := (mu_p_nontrivial k p 1 one_ne_zero).1
  rw [pow_one] at hmem
  refine ⟨(scalar_det_eq_one_iff (Fin p) _).mpr (by simpa using hmem), ?_, ?_⟩
  · intro h
    have : NeZero p := ⟨hp⟩
    have := congrArg (fun g : Matrix.GeneralLinearGroup (Fin p) (DualNumber k) ↦
      TrivSqZeroExt.snd ((g : Matrix (Fin p) (Fin p) (DualNumber k)) 0 0)) h
    simp [Matrix.GeneralLinearGroup.scalar, onePlusEps] at this
  · rw [center_GL]; exact ⟨_, rfl⟩

/-! ## The groups `α_{p^i}` and the Frobenius -/

/-- _lTf_L0yvrU-7290 (2:01:30) [prop] In characteristic `p`, `λ ↦ λ^p` is a ring endomorphism
(Mathlib `frobenius`), natural in the algebra (`map_frobenius`); likewise `λ ↦ λ^{p^i}`
(`iterateFrobenius`). -/
theorem frobenius_natural {A B : Type*} [CommRing A] [CommRing B] (p : ℕ) [ExpChar A p]
    [ExpChar B p] (f : A →+* B) (x : A) : f (frobenius A p x) = frobenius B p (f x) :=
  RingHom.map_frobenius f p x

theorem iterateFrobenius_apply' {A : Type*} [CommRing A] (p : ℕ) [ExpChar A p] (i : ℕ) (x : A) :
    iterateFrobenius A p i x = x ^ p ^ i :=
  iterateFrobenius_def p i x

/-- Lucas: if `n ≥ 2` is not a power of `p`, some `C(n, j)`, `0 < j < n`, is prime to `p`. -/
theorem exists_choose_not_dvd (p : ℕ) [hp : Fact p.Prime] :
    ∀ n : ℕ, 2 ≤ n → (∀ i, n ≠ p ^ i) → ∃ j, 0 < j ∧ j < n ∧ ¬ p ∣ n.choose j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hpow
  by_cases hr : n % p = 0
  · obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero hr
    have hp1 := hp.out.one_lt
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at hn
      · exact h
    have hm2 : 2 ≤ m := by
      rcases hm1.eq_or_lt with h | h
      · exact absurd (by rw [← h, mul_one, pow_one]) (hpow 1)
      · exact h
    obtain ⟨j, hj0, hjm, hj⟩ := ih m (by nlinarith) hm2
      (fun i h ↦ hpow (i + 1) (by rw [h, pow_succ, mul_comm]))
    refine ⟨p * j, by positivity, by nlinarith, fun hdvd ↦ hj ?_⟩
    have := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := p * m) (k := p * j) (p := p)
    rw [Nat.mul_mod_right, Nat.mul_mod_right, Nat.choose_self, one_mul,
      Nat.mul_div_cancel_left _ hp.out.pos, Nat.mul_div_cancel_left _ hp.out.pos] at this
    exact (Nat.modEq_zero_iff_dvd.mp (this.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)))
  · refine ⟨1, one_pos, hn, ?_⟩
    rw [Nat.choose_one_right]
    exact fun h ↦ hr (Nat.mod_eq_zero_of_dvd h)

/-- `f(X + Y) = f(X) + f(Y)`, written in `k[Y][X]` with `taylor`. -/
def IsAdditivePoly (f : k[X]) : Prop :=
  taylor (X : k[X]) (f.map C) = f.map C + C f

theorem eval_X_map_C (g : k[X]) : (g.map C).eval (X : k[X]) = g := by
  rw [eval_map, eval₂_C_X]

/-- The cast of an integer prime to `p` is a unit in an algebra of characteristic `p`. -/
theorem isUnit_natCast_of_not_dvd (p : ℕ) [Fact p.Prime] [CharP k p] (c : ℕ) (hc : ¬ p ∣ c) :
    IsUnit (c : k) := by
  have h : IsUnit (c : ZMod p) := by
    rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]; exact hc
  simpa using h.map (ZMod.castHom (dvd_refl p) k)

/-- _lTf_L0yvrU-7417 (2:03:37) [thm] In characteristic `p` (over any `𝔽_p`-algebra `k`), the
additive polynomials `f(X+Y) = f(X) + f(Y)` — the endomorphisms of `𝔾_a` — are exactly the
`∑ a_i X^{p^i}`: every coefficient of `f` outside the degrees `p^i` vanishes. -/
theorem isAdditivePoly_iff (p : ℕ) [Fact p.Prime] [CharP k p] (f : k[X]) :
    IsAdditivePoly k f ↔ ∀ n, f.coeff n ≠ 0 → ∃ i, n = p ^ i := by
  constructor
  · intro h n hn
    have hcoeff : ∀ j, hasseDeriv j f = (f.map C + C f).coeff j := by
      intro j
      have := congrArg (fun q ↦ q.coeff j) h
      simp only [taylor_coeff, hasseDeriv_map, eval_X_map_C] at this
      exact this
    by_contra hpow
    push Not at hpow
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · interval_cases n
      · have := hcoeff 0
        simp only [hasseDeriv_zero, LinearMap.id_apply, coeff_add, coeff_map, coeff_C_zero] at this
        exact hn (C_eq_zero.mp (by linear_combination -this))
      · exact hpow 0 (by simp)
    · obtain ⟨j, hj0, hjn, hj⟩ := exists_choose_not_dvd p n hn2 (fun i h ↦ hpow i h)
      have := congrArg (fun q : k[X] ↦ q.coeff (n - j)) (hcoeff j)
      simp only [hasseDeriv_coeff, coeff_add, coeff_map, coeff_C, hj0.ne', ite_false, add_zero,
        Nat.sub_add_cancel hjn.le, Nat.sub_ne_zero_of_lt hjn] at this
      exact hn ((isUnit_natCast_of_not_dvd k p _ hj).mul_right_eq_zero.mp this)
  · intro h
    have key : ∀ n ∈ f.support, IsAdditivePoly k (C (f.coeff n) * X ^ n) := by
      intro n hn
      obtain ⟨i, rfl⟩ := h n (mem_support_iff.mp hn)
      simp only [IsAdditivePoly, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, taylor_mul,
        taylor_C, taylor_X_pow, add_pow_char_pow, map_mul, map_pow]
      ring
    rw [IsAdditivePoly, f.as_sum_support_C_mul_X_pow, Polynomial.map_sum, map_sum, map_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have := key n hn
    rwa [IsAdditivePoly] at this

/-- _lTf_L0yvrU-7480 (2:04:40) [def] `α_{p^i}`, the kernel of `λ ↦ λ^{p^i}` on `𝔾_a`:
`α_{p^i}(A) = {λ | λ^{p^i} = 0}`, an additive subgroup in characteristic `p`. -/
def alpha (A : Type*) [CommRing A] (p : ℕ) [ExpChar A p] (i : ℕ) : AddSubgroup A :=
  (iterateFrobenius A p i).toAddMonoidHom.ker

theorem mem_alpha {A : Type*} [CommRing A] (p : ℕ) [ExpChar A p] (i : ℕ) (x : A) :
    x ∈ alpha A p i ↔ x ^ p ^ i = 0 := by
  simp [alpha, iterateFrobenius_def]

/-- _lTf_L0yvrU-7480 (2:04:40) [def] `α_{p^i}` is trivial on reduced rings. -/
theorem alpha_reduced {A : Type*} [CommRing A] [IsReduced A] (p : ℕ) [ExpChar A p] (i : ℕ) :
    alpha A p i = ⊥ := by
  ext x
  rw [mem_alpha, AddSubgroup.mem_bot]
  exact ⟨fun h ↦ IsReduced.eq_zero _ ⟨_, h⟩, fun h ↦ by rw [h]; exact zero_pow (pow_pos (expChar_pos A p) i).ne'⟩

/-- _lTf_L0yvrU-7545 (2:05:45) [prop] `α_{p^i}` is represented by `k[t]/(t^{p^i})`… -/
noncomputable def alpha_repr (m : ℕ) (A : Type u) [CommRing A] [Algebra k A] :
    (AdjoinRoot (X ^ m : k[X]) →ₐ[k] A) ≃ {a : A // a ^ m = 0} :=
  (adjoinRootHomEquiv k _ A).trans (Equiv.subtypeEquivRight fun a ↦ by simp)

/-- _lTf_L0yvrU-7545 (2:05:45) [prop] … free of rank `p^i`… -/
theorem alpha_rank [Nontrivial k] (m : ℕ) : (AdjoinRoot.powerBasis' (monic_X_pow (R := k) m)).dim = m := by
  simp only [AdjoinRoot.powerBasis']
  exact natDegree_X_pow m

/-- _lTf_L0yvrU-7545 (2:05:45) [prop] … and not trivial: `ε ≠ 0` and `ε^{m} = 0` (`m ≥ 2`) in the
dual numbers. -/
theorem alpha_nontrivial [Nontrivial k] (m : ℕ) (hm : 2 ≤ m) :
    (DualNumber.eps : DualNumber k) ^ m = 0 ∧ (DualNumber.eps : DualNumber k) ≠ 0 := by
  refine ⟨?_, fun h ↦ ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, sq, DualNumber.eps_mul_eps, zero_mul]
  · have := congrArg TrivSqZeroExt.snd h
    simp at this

/-- _lTf_L0yvrU-7625 (2:07:05) [def] An affine space has rank `n` when its algebra is free of
rank `n`; for a group, the rank is the order. -/
def HasRank (R : Type*) [Ring R] [Algebra k R] (n : ℕ) : Prop :=
  Module.Free k R ∧ Module.finrank k R = n

/-- _lTf_L0yvrU-7690 (2:08:10) [prop] `μ_n` has order `n` and `α_{p^i}` order `p^i` (for `k ≠ 0`),
and the group of points with values in a field (or a domain) `L` of a group of order `n` has at
most `n` elements (Mathlib `card_algHom_le_finrank`). -/
theorem order_mu_alpha [Nontrivial k] (n : ℕ) (hn : n ≠ 0) (m : ℕ) :
    HasRank k (AdjoinRoot (X ^ n - C 1 : k[X])) n ∧ HasRank k (AdjoinRoot (X ^ m : k[X])) m := by
  refine ⟨⟨Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_X_pow_sub_C (1 : k) hn)).basis, ?_⟩,
    ⟨Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_X_pow (R := k) m)).basis, ?_⟩⟩
  · rw [PowerBasis.finrank, mu_rank k n hn]
  · rw [PowerBasis.finrank, alpha_rank]

theorem card_points_le (R : Type*) [CommRing R] [Algebra k R] [Module.Free k R]
    [Module.Finite k R] (L : Type*) [CommRing L] [IsDomain L] [Algebra k L] :
    Nat.card (R →ₐ[k] L) ≤ Module.finrank k R :=
  card_algHom_le_finrank k R L

/-- _lTf_L0yvrU-7841 (2:10:41) [prop] In characteristic `p`, `F_G : (λ_{ij}) ↦ (λ_{ij}^p)` is an
endomorphism of `GL_n`. -/
def frobGL (n : Type) [Fintype n] [DecidableEq n] (A : Type*) [CommRing A] (p : ℕ) [ExpChar A p] :
    Matrix.GeneralLinearGroup n A →* Matrix.GeneralLinearGroup n A :=
  Units.map (frobenius A p).mapMatrix.toMonoidHom

/-- _lTf_L0yvrU-7907 (2:11:47) [prop] The kernel of `F_G` on `GL_n`: the matrices with
`λ_{ij}^p = 0` (`i ≠ j`) and `λ_{ii}^p = 1`. -/
theorem mem_ker_frobGL (n : Type) [Fintype n] [DecidableEq n] {A : Type*} [CommRing A] (p : ℕ)
    [ExpChar A p] (g : Matrix.GeneralLinearGroup n A) :
    g ∈ (frobGL n A p).ker ↔
      ∀ i j, (g : Matrix n n A) i j ^ p = if i = j then 1 else 0 := by
  rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  simp [frobGL, Matrix.one_apply, frobenius_def]


/-- Points of a quotient by a family of equations. -/
noncomputable def quotFamHomEquiv {R : Type u} [CommRing R] [Algebra k R] {ι : Type*} (g : ι → R)
    (A : Type u) [CommRing A] [Algebra k A] :
    (R ⧸ Ideal.span (Set.range g) →ₐ[k] A) ≃ {φ : R →ₐ[k] A // ∀ i, φ (g i) = 0} where
  toFun φ := ⟨φ.comp (Ideal.Quotient.mkₐ k _), fun i ↦ by
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))]⟩
  invFun φ := Ideal.Quotient.liftₐ _ φ.1 (fun x hx ↦ by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact φ.2 i
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx])
  left_inv φ := by ext x; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x; rfl
  right_inv φ := rfl

/-- The equations `t_{ij}^p = δ_{ij}` of the Frobenius kernel of `GL_n`. -/
noncomputable def frobKerEqs (n : Type) [DecidableEq n] (p : ℕ) (q : n × n) :
    MvPolynomial (n × n) k :=
  MvPolynomial.X q ^ p - if q.1 = q.2 then 1 else 0

/-- _lTf_L0yvrU-7949 (2:12:29) [prop] The Frobenius kernel of `GL_n` is represented by
`k[t_{ij}]/(t_{ij}^p (i ≠ j), t_{ii}^p - 1)`: its points are the matrices with
`λ_{ij}^p = δ_{ij}`… -/
noncomputable def frobKer_repr (n : Type) [DecidableEq n] (p : ℕ) (A : Type u) [CommRing A]
    [Algebra k A] :
    (MvPolynomial (n × n) k ⧸ Ideal.span (Set.range (frobKerEqs k n p)) →ₐ[k] A) ≃
      {M : Matrix n n A // ∀ i j, M i j ^ p = if i = j then 1 else 0} :=
  (quotFamHomEquiv k _ A).trans
    (((mvHomEquiv k _ A).subtypeEquiv
      (q := fun x : n × n → A ↦ ∀ q : n × n, x q ^ p = if q.1 = q.2 then 1 else 0)
      (fun φ ↦ forall_congr' fun q ↦ by
        simp only [frobKerEqs, mvHomEquiv, Equiv.coe_fn_mk, map_sub, map_pow]
        split_ifs <;> simp [sub_eq_zero])).trans
    { toFun x := ⟨Matrix.of fun i j ↦ x.1 (i, j), fun i j ↦ x.2 (i, j)⟩
      invFun M := ⟨fun q ↦ M.1 q.1 q.2, fun q ↦ M.2 q.1 q.2⟩
      left_inv _ := rfl
      right_inv _ := rfl })

/-- _lTf_L0yvrU-7949 (2:12:29) [prop] … which are invertible (in characteristic `p`,
`det(M)^p = det(M^{(p)}) = 1`), so that these points are the kernel of `F_G`… -/
theorem frobKer_isUnit (n : Type) [Fintype n] [DecidableEq n] {A : Type*} [CommRing A] (p : ℕ)
    [ExpChar A p] (M : Matrix n n A) (hM : ∀ i j, M i j ^ p = if i = j then 1 else 0) :
    IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h1 : (frobenius A p).mapMatrix M = 1 := by
    ext i j; simp [frobenius_def, hM, Matrix.one_apply]
  have := RingHom.map_det (frobenius A p) M
  rw [h1, Matrix.det_one, frobenius_def] at this
  exact (Units.ofPowEqOne _ p this (expChar_pos A p).ne').isUnit

/-- _lTf_L0yvrU-7949 (2:12:29) [prop] … an infinitesimal group: trivial on reduced rings… -/
theorem frobKer_reduced (n : Type) [Fintype n] [DecidableEq n] {A : Type*} [CommRing A]
    [IsReduced A] (p : ℕ) [ExpChar A p] (g : Matrix.GeneralLinearGroup n A)
    (hg : g ∈ (frobGL n A p).ker) : g = 1 := by
  rw [mem_ker_frobGL] at hg
  ext i j
  have := hg i j
  rw [Units.val_one, Matrix.one_apply]
  split_ifs at this ⊢ with h
  · exact (pow_char_pow_eq_one_iff p 1 _).mp (by simpa using this)
  · exact IsReduced.eq_zero _ ⟨_, this⟩

/-- The entries of `1 + x E_{ij}` satisfy `λ_{ab}^p = δ_{ab}` when `x^p = 0`. -/
theorem transvection_frobKer {B : Type*} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    (p : ℕ) (hp0 : p ≠ 0) {i j : n} (hij : i ≠ j) (x : B) (hx : x ^ p = 0) (a b : n) :
    Matrix.transvection i j x a b ^ p = if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst hab
    have hn : ¬ (i = a ∧ j = a) := fun h ↦ hij (h.1.trans h.2.symm)
    simp [Matrix.transvection, hn]
  · simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, hab, ite_false, zero_add,
      Matrix.single_apply]
    split_ifs <;> simp [hx, hp0]

/-- `1 + x E_{ij}` and `1 + y E_{ji}` do not commute when `xy ≠ 0`. -/
theorem transvection_noncomm {B : Type*} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    {i j : n} (hij : i ≠ j) (x y : B) (hxy : x * y ≠ 0) :
    Matrix.transvection i j x * Matrix.transvection j i y ≠
      Matrix.transvection j i y * Matrix.transvection i j x := by
  intro h
  have := congrFun (congrFun h i) i
  simp only [Matrix.transvection, add_mul, mul_add, one_mul, mul_one,
    Matrix.single_mul_single_same, Matrix.add_apply, Matrix.single_apply_same,
    Matrix.single_apply_of_row_ne hij.symm] at this
  apply hxy
  linear_combination this

/-- _lTf_L0yvrU-7949 (2:12:29) [prop] … and non-commutative for `n ≥ 2`: over
`B = k[ε][ε']`, the transvections `1 + ε' E_{ij}` and `1 + ε E_{ji}` are in it (they have
determinant `1`) and do not commute, `ε' ε ≠ 0`. -/
theorem frobKer_noncomm [Nontrivial k] {n : Type} [Fintype n] [DecidableEq n] (p : ℕ) (hp : 2 ≤ p)
    {i j : n} (hij : i ≠ j) :
    let x : DualNumber (DualNumber k) := DualNumber.eps
    let y : DualNumber (DualNumber k) := TrivSqZeroExt.inl DualNumber.eps
    (∀ a b, Matrix.transvection i j x a b ^ p = if a = b then 1 else 0) ∧
      (∀ a b, Matrix.transvection j i y a b ^ p = if a = b then 1 else 0) ∧
      Matrix.transvection i j x * Matrix.transvection j i y ≠
        Matrix.transvection j i y * Matrix.transvection i j x := by
  intro x y
  have hp0 : p ≠ 0 := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hp
  have hx : x ^ (2 + m) = 0 := by
    rw [pow_add, sq, DualNumber.eps_mul_eps, zero_mul]
  have hy : y ^ (2 + m) = 0 := by
    rw [pow_add, sq, ← TrivSqZeroExt.inl_mul, DualNumber.eps_mul_eps, TrivSqZeroExt.inl_zero,
      zero_mul]
  have hxy : x * y ≠ 0 := by
    intro h
    have h2 := congrArg TrivSqZeroExt.snd h
    simp only [x, y, DualNumber.snd_eps, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl] at h2
    have h3 := congrArg TrivSqZeroExt.snd (h2 : _)
    simp at h2 h3
  exact ⟨transvection_frobKer _ hp0 hij x hx, transvection_frobKer _ hp0 hij.symm y hy,
    transvection_noncomm hij x y hxy⟩

/-- _lTf_L0yvrU-8015 (2:13:35) [prop] `F_G : GL_n → GL_n` is not an isomorphism (`n ≥ 2`): its
kernel has the non-trivial point `1 + ε E_{ij}` over `k[ε]`. -/
theorem frobGL_kernel_nontrivial [Nontrivial k] {n : Type} [Fintype n] [DecidableEq n] (p : ℕ)
    (hp : 2 ≤ p) {i j : n} (hij : i ≠ j) :
    (∀ a b, Matrix.transvection i j (DualNumber.eps : DualNumber k) a b ^ p =
      if a = b then 1 else 0) ∧ Matrix.transvection i j (DualNumber.eps : DualNumber k) ≠ 1 := by
  have hx : (DualNumber.eps : DualNumber k) ^ p = 0 := (alpha_nontrivial k p hp).1
  have hp0 : p ≠ 0 := by omega
  refine ⟨transvection_frobKer _ hp0 hij _ hx, fun h ↦ ?_⟩
  · have := congrFun (congrFun h i) j
    simp [Matrix.transvection, hij] at this
    exact (alpha_nontrivial k p hp).2 this

end Buffalo.Groupes.Part01
