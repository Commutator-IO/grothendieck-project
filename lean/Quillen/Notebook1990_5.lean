import Mathlib

/-!
# Quillen, notebook 1990-5: full idempotents; the splitting lemma; `e = (1 + ε)/2`

Daniel Quillen's research notebook 1990-5 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201990/1990-5.pdf>).

* p. 26, full idempotents. For an idempotent `e` of a ring `R`, `ReR = R` (some
  `Σ aᵢ e bᵢ = 1`) iff there is a surjection `(Re)ⁿ → R` of left `R`-modules
  (`full_iff_exists_surjective`); every `R`-linear `φ : Re → R` is right multiplication by
  `φ(e)` (`hom_apply_eq_mul`), and `φ(e) = eφ(e)`. The page works with right modules `eR`;
  the statement is the same in the opposite ring.
* p. 67, the splitting lemma: for `i : E' → E` injective, `p : E → E''` surjective with
  `p ∘ i = 0`, and `h`, `k` with `i ∘ k + h ∘ p = 1`: `k ∘ i = 1`, `p ∘ h = 1`, `k ∘ h = 0`
  (`splitting`).
* pp. 27-28: in a `ℚ`-algebra with `ε² = F² = 1`, `εF = −Fε`, the element `e = (1 + ε)/2` is
  idempotent, `FeF = 1 − e` and `eFe = 0` (`half_one_add`).
-/

namespace Quillen.Notebook1990_5

section Full

variable {R : Type*} [Ring R] {e : R}

/-- An `R`-linear map `Re → R` is right multiplication by the image of `e`. -/
theorem hom_apply_eq_mul (he : IsIdempotentElem e) (φ : Ideal.span ({e} : Set R) →ₗ[R] R)
    (x : Ideal.span ({e} : Set R)) :
    φ x = (x : R) * φ ⟨e, Ideal.mem_span_singleton_self e⟩ := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.2
  have hx : x = a • (⟨e, Ideal.mem_span_singleton_self e⟩ : Ideal.span ({e} : Set R)) := by
    ext; simp [ha]
  have hee : φ ⟨e, Ideal.mem_span_singleton_self e⟩ = e * φ ⟨e, Ideal.mem_span_singleton_self e⟩ := by
    conv_lhs => rw [show (⟨e, Ideal.mem_span_singleton_self e⟩ : Ideal.span ({e} : Set R)) =
      e • ⟨e, Ideal.mem_span_singleton_self e⟩ by ext; simp [he.eq]]
    rw [map_smul, smul_eq_mul]
  rw [hx, map_smul, smul_eq_mul, Submodule.coe_smul, smul_eq_mul, mul_assoc, ← hee]

/-- **Notebook 1990-5, p. 26**: an idempotent `e` is full (`ReR = R`) iff some `(Re)ⁿ` maps
onto `R`. -/
theorem full_iff_exists_surjective (he : IsIdempotentElem e) :
    (∃ (n : ℕ) (a b : Fin n → R), ∑ i, a i * e * b i = 1) ↔
      ∃ (n : ℕ) (f : (Fin n → Ideal.span ({e} : Set R)) →ₗ[R] R), Function.Surjective f := by
  constructor
  · rintro ⟨n, a, b, hab⟩
    let f : (Fin n → Ideal.span ({e} : Set R)) →ₗ[R] R :=
      { toFun := fun v => ∑ i, (v i : R) * b i
        map_add' := fun v w => by simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun r v => by simp [Finset.mul_sum, mul_assoc] }
    refine ⟨n, f, fun r => ?_⟩
    refine ⟨fun i => ⟨r * a i * e, Ideal.mem_span_singleton'.mpr ⟨r * a i, rfl⟩⟩, ?_⟩
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk]
    calc ∑ i, r * a i * e * b i = r * ∑ i, a i * e * b i := by
          rw [Finset.mul_sum]; simp only [mul_assoc]
      _ = r := by rw [hab, mul_one]
  · rintro ⟨n, f, hf⟩
    obtain ⟨v, hv⟩ := hf 1
    let eₛ : Ideal.span ({e} : Set R) := ⟨e, Ideal.mem_span_singleton_self e⟩
    choose a ha using fun i => Ideal.mem_span_singleton'.mp (v i).2
    refine ⟨n, a, fun i => f (Pi.single i eₛ), ?_⟩
    rw [← hv]
    conv_rhs => rw [show v = ∑ i, Pi.single i (v i) from (Finset.univ_sum_single v).symm]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hom_apply_eq_mul he (f.comp (LinearMap.single R (fun _ => Ideal.span ({e} : Set R)) i)) (v i)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single] at this
    rw [this, ← ha i]

end Full

section Splitting

variable {S : Type*} [Ring S] {E' E E'' : Type*} [AddCommGroup E'] [AddCommGroup E]
  [AddCommGroup E''] [Module S E'] [Module S E] [Module S E'']

/-- **Notebook 1990-5, p. 67**, the splitting lemma. -/
theorem splitting {i : E' →ₗ[S] E} {p : E →ₗ[S] E''} {h : E'' →ₗ[S] E} {k : E →ₗ[S] E'}
    (hi : Function.Injective i) (hp : Function.Surjective p) (hpi : p ∘ₗ i = 0)
    (hs : i ∘ₗ k + h ∘ₗ p = LinearMap.id) :
    k ∘ₗ i = LinearMap.id ∧ p ∘ₗ h = LinearMap.id ∧ k ∘ₗ h = 0 := by
  have hs' : ∀ x, i (k x) + h (p x) = x := fun x => by
    simpa using LinearMap.congr_fun hs x
  have hpi' : ∀ x, p (i x) = 0 := fun x => by simpa using LinearMap.congr_fun hpi x
  have hph : ∀ y, p (h y) = y := by
    intro y
    obtain ⟨z, rfl⟩ := hp y
    have := congrArg p (hs' z)
    rwa [map_add, hpi', zero_add] at this
  refine ⟨?_, ?_, ?_⟩
  · ext x
    apply hi
    have := hs' (i x)
    rw [hpi', map_zero, add_zero] at this
    simpa using this
  · ext y; simpa using hph y
  · ext y
    apply hi
    have := hs' (h y)
    rw [hph, add_eq_right] at this
    simpa using this

end Splitting

section Half

variable {R : Type*} [Ring R] [Algebra ℚ R] {ε F : R}

/-- **Notebook 1990-5, pp. 27-28**: `e = (1 + ε)/2` is idempotent, `FeF = 1 − e`, `eFe = 0`. -/
theorem half_one_add (hε : ε * ε = 1) (hF : F * F = 1) (hεF : ε * F = -(F * ε)) :
    IsIdempotentElem ((2⁻¹ : ℚ) • (1 + ε)) ∧
      F * ((2⁻¹ : ℚ) • (1 + ε)) * F = 1 - (2⁻¹ : ℚ) • (1 + ε) ∧
      (2⁻¹ : ℚ) • (1 + ε) * F * ((2⁻¹ : ℚ) • (1 + ε)) = 0 := by
  have h1 : (1 + ε) * (1 + ε) = (2 : ℚ) • (1 + ε) := by
    have : (1 + ε) * (1 + ε) = 1 + ε + ε * ε + ε := by noncomm_ring
    rw [this, hε, two_smul]; abel
  have h2 : F * (1 + ε) * F = 1 - ε := by
    have : F * (1 + ε) * F = F * F + F * (ε * F) := by noncomm_ring
    rw [this, hεF, mul_neg, ← mul_assoc, hF, one_mul, sub_eq_add_neg]
  have h3 : (1 + ε) * F * (1 + ε) = 0 := by
    have : (1 + ε) * F * (1 + ε) = F + F * ε + ε * F + ε * F * ε := by noncomm_ring
    rw [this, hεF, neg_mul, mul_assoc, hε, mul_one]; abel
  refine ⟨?_, ?_, ?_⟩
  · unfold IsIdempotentElem
    rw [smul_mul_smul, h1, smul_smul]; norm_num
  · rw [mul_smul_comm, smul_mul_assoc, h2]
    module
  · rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, h3, smul_zero, smul_zero]

end Half

end Quillen.Notebook1990_5
