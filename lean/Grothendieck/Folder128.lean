import Mathlib

/-!
# Folder 128, pages 12–13: the equivalence ideals of a rank-2 algebra over a field

The modernised reading `transcripts/128/128.modern.tex` (« Résultats auxiliaires sur les
relations d'équivalence », pages 12 to 18) defines, after Prop. 3 of N° 1 (pages 9–11), an
*equivalence ideal* of `A' ⊗_A A'`: an ideal `J` with
* (reflexivity) `J ⊂ Δ = Ker(A' ⊗_A A' → A')`,
* (symmetry) `J` stable under the exchange of the two factors,
* (transitivity) `p₁₃(J) ⊂ p₁₂(J) + p₂₃(J)` in `A' ⊗_A A' ⊗_A A'`, where
  `p₁₂(a ⊗ b) = a ⊗ b ⊗ 1`, `p₁₃(a ⊗ b) = a ⊗ 1 ⊗ b`, `p₂₃(a ⊗ b) = 1 ⊗ a ⊗ b`
  (the closed subscheme it defines in `Spec A' ×_A Spec A'` is then an equivalence relation).

Prop. 1 (i), page 12 (Grothendieck, page 12): if `A'/A ≅ A/𝔪` there are exactly two equivalence
relations on `Spec A'` over `Spec A`, the finest (`J = Δ`) and the coarsest (`J = 0`). Page 13
reduces it, through Prop. 3, Cor. 2 of N° 1, to `A = k` a field and `A'` a `k`-algebra of
rank `2`, treats `k × k` and stops after « `A' ≃ k[ε]` ».

This file proves that field case, for any field `k` (not only algebraically closed) and any
commutative `k`-algebra `A` with `finrank k A = 2` — so `k × k`, `k[ε]` and quadratic field
extensions alike, without classifying them first:
* `IsEquivalenceIdeal`: the three conditions above;
* `eq_bot_or_eq_ker`: an equivalence ideal of `A ⊗[k] A` is `0` or `Δ`;
* `isEquivalenceIdeal_bot`, `isEquivalenceIdeal_ker`: both are equivalence ideals.

The proof. For `x ∉ k`, `Δ = A · (1 ⊗ x − x ⊗ 1)` (from `1 ⊗ s − s ⊗ 1` spanning `Δ`). If `A`
is a field, a nonzero element of `J` is `a • δ` with `a` a unit, so `δ ∈ J`. Otherwise a
nonzero non-unit `e` satisfies `e² = r e`: if `r ≠ 0`, `f = e/r` is an idempotent and symmetry
gives `δ ∈ J` (the case `k × k`); if `e² = 0`, `J ⊂ k (e ⊗ e)` unless `δ ∈ J`, and `e ⊗ e`
fails transitivity, as `e ⊗ 1 ⊗ e` survives the map `a ⊗ b ⊗ c ↦ χ(b) a ⊗ c` (`χ(e) = 0`)
which kills `p₁₂(J)` and `p₂₃(J)` (the case `k[ε]`, the edition's).

Not formalised: the reduction to the field case (Prop. 3 and its Cor. 2, the artinian
reduction modulo `𝔪`), nor the passage from ideals to closed subschemes.
-/

open TensorProduct

namespace Grothendieck.Folder128

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

variable (k A) in
/-- `p₁₂ : a ⊗ b ↦ a ⊗ b ⊗ 1`. -/
noncomputable abbrev p12 : A ⊗[k] A →ₐ[k] (A ⊗[k] A) ⊗[k] A :=
  Algebra.TensorProduct.includeLeft

variable (k A) in
/-- `p₁₃ : a ⊗ b ↦ a ⊗ 1 ⊗ b`. -/
noncomputable abbrev p13 : A ⊗[k] A →ₐ[k] (A ⊗[k] A) ⊗[k] A :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeLeft (AlgHom.id k A)

variable (k A) in
/-- `p₂₃ : a ⊗ b ↦ 1 ⊗ a ⊗ b`. -/
noncomputable abbrev p23 : A ⊗[k] A →ₐ[k] (A ⊗[k] A) ⊗[k] A :=
  Algebra.TensorProduct.map Algebra.TensorProduct.includeRight (AlgHom.id k A)

/-- An equivalence ideal of `A ⊗[k] A` (folder 128, page 11 and the reading's definition):
reflexive, symmetric and transitive. -/
structure IsEquivalenceIdeal (I : Ideal (A ⊗[k] A)) : Prop where
  /-- Reflexivity: `I ⊂ Δ = Ker(A ⊗ A → A)`. -/
  refl : I ≤ RingHom.ker (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A)
  /-- Symmetry: `I` is stable under `a ⊗ b ↦ b ⊗ a`. -/
  symm : ∀ t ∈ I, Algebra.TensorProduct.comm k A A t ∈ I
  /-- Transitivity: `p₁₃(I) ⊂ p₁₂(I) + p₂₃(I)`. -/
  trans : I.map (p13 k A) ≤ I.map (p12 k A) ⊔ I.map (p23 k A)

/-- Coordinates in the basis `1, x` when `x ∉ k`. -/
lemma coords (h2 : Module.finrank k A = 2) {x : A} (hx : ∀ c : k, c • (1 : A) ≠ x) :
    ∃ f₀ f₁ : A →ₗ[k] k, (∀ a, f₀ a • 1 + f₁ a • x = a) ∧ f₀ 1 = 1 ∧ f₀ x = 0 ∧ f₁ 1 = 0 ∧
      f₁ x = 1 := by
  have : Nontrivial A := Module.nontrivial_of_finrank_eq_succ h2
  have hli : LinearIndependent k ![(1 : A), x] := (LinearIndependent.pair_iff' one_ne_zero).2 hx
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = x := by simp [b]
  refine ⟨b.coord 0, b.coord 1, fun a => ?_, ?_, ?_, ?_, ?_⟩
  · have := b.sum_repr a
    rwa [Fin.sum_univ_two, hb0, hb1] at this
  all_goals simp [← hb0, ← hb1]

/-- `Δ = A · (1 ⊗ x − x ⊗ 1)` for `x ∉ k`. -/
lemma exists_smul_delta (h2 : Module.finrank k A = 2) {x : A} (hx : ∀ c : k, c • (1 : A) ≠ x)
    {t : A ⊗[k] A} (ht : t ∈ RingHom.ker (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A)) :
    ∃ a : A, a • ((1 : A) ⊗ₜ[k] x - x ⊗ₜ 1) = t := by
  obtain ⟨f₀, f₁, hf, -⟩ := coords h2 hx
  have ht' : t ∈ Submodule.span A (Set.range fun s : A => (1 : A) ⊗ₜ[k] s - s ⊗ₜ 1) := by
    rwa [KaehlerDifferential.submodule_span_range_eq_ideal]
  rw [← Submodule.mem_span_singleton (R := A)]
  refine Submodule.span_le.2 ?_ ht'
  rintro _ ⟨s, rfl⟩
  have : (1 : A) ⊗ₜ[k] s - s ⊗ₜ 1 = f₁ s • ((1 : A) ⊗ₜ[k] x - x ⊗ₜ 1) := by
    conv_lhs => rw [← hf s]
    simp only [tmul_add, add_tmul, tmul_smul, ← smul_tmul', smul_sub]
    abel
  simpa only [this, SetLike.mem_coe] using
    Submodule.smul_of_tower_mem _ _ (Submodule.mem_span_singleton_self _)

lemma smul_mem {I : Ideal (A ⊗[k] A)} (a : A) {t : A ⊗[k] A} (ht : t ∈ I) : a • t ∈ I := by
  rw [Algebra.smul_def]; exact I.mul_mem_left _ ht

/-- If `δ = 1 ⊗ x − x ⊗ 1 ∈ I` then `Δ ⊂ I`. -/
lemma ker_le (h2 : Module.finrank k A = 2) {x : A} (hx : ∀ c : k, c • (1 : A) ≠ x)
    {I : Ideal (A ⊗[k] A)} (hδ : (1 : A) ⊗ₜ[k] x - x ⊗ₜ 1 ∈ I) :
    RingHom.ker (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A) ≤ I := fun t ht => by
  obtain ⟨a, rfl⟩ := exists_smul_delta h2 hx ht
  exact smul_mem a hδ

lemma mem_of_smul_mem {I : Ideal (A ⊗[k] A)} {c : k} (hc : c ≠ 0) {t : A ⊗[k] A}
    (ht : c • t ∈ I) : t ∈ I := by
  simpa [smul_smul, inv_mul_cancel₀ hc] using Submodule.smul_of_tower_mem I c⁻¹ ht

/-- `a • δ` for `a = c + d e`, `e² = r e`. -/
lemma smul_delta {e : A} {r : k} (he : e * e = r • e) (c d : k) :
    (c • (1 : A) + d • e) • ((1 : A) ⊗ₜ[k] e - e ⊗ₜ 1) =
      c • ((1 : A) ⊗ₜ[k] e) + d • (e ⊗ₜ[k] e) - (c + d * r) • (e ⊗ₜ[k] (1 : A)) := by
  simp only [smul_sub, smul_tmul', smul_eq_mul, mul_one, add_mul, smul_mul_assoc, one_mul, he]
  simp only [add_tmul, ← smul_tmul', smul_smul]
  module

/-- The case of an idempotent `e ∉ k` (`A ≃ k × k`): symmetry. -/
lemma idem_case (h2 : Module.finrank k A = 2) {I : Ideal (A ⊗[k] A)} (hI : IsEquivalenceIdeal I)
    {e : A} (hx : ∀ c : k, c • (1 : A) ≠ e) (he : e * e = e) :
    I = ⊥ ∨ (1 : A) ⊗ₜ[k] e - e ⊗ₜ 1 ∈ I := by
  obtain ⟨f₀, f₁, hf, -⟩ := coords h2 hx
  refine or_iff_not_imp_left.2 fun hI0 => ?_
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨a, rfl⟩ := exists_smul_delta h2 hx (hI.refl ht)
  obtain ⟨c, d, rfl⟩ : ∃ c d : k, c • 1 + d • e = a := ⟨_, _, hf a⟩
  have he' : e * e = (1 : k) • e := by rw [one_smul, he]
  rw [smul_delta he'] at ht ht0
  have key : ∀ w ∈ I, w - Algebra.TensorProduct.comm k A A w = (1 : A) ⊗ₜ[k] e - e ⊗ₜ 1 →
      (1 : A) ⊗ₜ[k] e - e ⊗ₜ 1 ∈ I := fun w hw h => h ▸ sub_mem hw (hI.symm w hw)
  by_cases hc : c = 0
  · subst hc
    have hd : d ≠ 0 := by rintro rfl; simp at ht0
    refine key (e ⊗ₜ[k] e - e ⊗ₜ 1) (mem_of_smul_mem (c := d) (by simpa using hd) ?_) ?_
    · convert I.mul_mem_left (e ⊗ₜ[k] (1 : A)) ht using 1
      simp only [mul_sub, mul_add, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, he,
        one_mul, mul_one]
      module
    · simp only [map_sub, Algebra.TensorProduct.comm_tmul]; abel
  · refine key ((1 : A) ⊗ₜ[k] e - e ⊗ₜ e) (mem_of_smul_mem hc ?_) ?_
    · convert I.mul_mem_left ((1 : A) ⊗ₜ[k] (1 : A) - e ⊗ₜ 1) ht using 1
      simp only [sub_mul, mul_sub, mul_add, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul,
        he, one_mul, mul_one]
      module
    · simp only [map_sub, Algebra.TensorProduct.comm_tmul]; abel

/-- The case of `e ∉ k` with `e² = 0` (`A ≃ k[ε]`): transitivity. -/
lemma nil_case (h2 : Module.finrank k A = 2) {I : Ideal (A ⊗[k] A)} (hI : IsEquivalenceIdeal I)
    {e : A} (hx : ∀ c : k, c • (1 : A) ≠ e) (he : e * e = 0) :
    I = ⊥ ∨ (1 : A) ⊗ₜ[k] e - e ⊗ₜ 1 ∈ I := by
  obtain ⟨f₀, f₁, hf, h01, h0e, -, h1e⟩ := coords h2 hx
  have he' : e * e = (0 : k) • e := by rw [zero_smul, he]
  refine or_iff_not_imp_left.2 fun hI0 => by_contra fun hδ => ?_
  -- every element of `I` is a multiple of `e ⊗ e`
  have claim : ∀ t ∈ I, ∃ d : k, t = d • (e ⊗ₜ[k] e) := fun t ht => by
    obtain ⟨a, rfl⟩ := exists_smul_delta h2 hx (hI.refl ht)
    obtain ⟨c, d, rfl⟩ : ∃ c d : k, c • 1 + d • e = a := ⟨_, _, hf a⟩
    rw [smul_delta he'] at ht ⊢
    by_cases hc : c = 0
    · exact ⟨d, by simp [hc]⟩
    have hee : e ⊗ₜ[k] e ∈ I := by
      refine mem_of_smul_mem hc ?_
      convert I.mul_mem_left (e ⊗ₜ[k] (1 : A)) ht using 1
      simp only [mul_sub, mul_add, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, he,
        one_mul, mul_one, zero_tmul, smul_zero]
      module
    refine absurd (mem_of_smul_mem hc ?_) hδ
    convert sub_mem ht (Submodule.smul_of_tower_mem I d hee) using 1
    module
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨d, rfl⟩ := claim t ht
  have hd : d ≠ 0 := by rintro rfl; simp at ht0
  have hee : e ⊗ₜ[k] e ∈ I := mem_of_smul_mem hd ht
  -- the character `χ(c + d e) = c`
  let χ : A →ₐ[k] k := AlgHom.ofLinearMap f₀ h01 fun a b => by
    obtain ⟨c, d, rfl⟩ : ∃ c d : k, c • 1 + d • e = a := ⟨_, _, hf a⟩
    obtain ⟨c', d', rfl⟩ : ∃ c d : k, c • 1 + d • e = b := ⟨_, _, hf b⟩
    simp [mul_add, he, h01, h0e, mul_comm]
  let F : A ⊗[k] A →ₐ[k] A :=
    (Algebra.TensorProduct.rid k k A).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id k A) χ)
  let φ := Algebra.TensorProduct.map F (AlgHom.id k A)
  have hχe : χ e = 0 := h0e
  have hle : I.map (p12 k A) ⊔ I.map (p23 k A) ≤ RingHom.ker φ := by
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun t ht => ?_)
      (Ideal.map_le_iff_le_comap.2 fun t ht => ?_) <;>
    · obtain ⟨d, rfl⟩ := claim t ht
      simp [φ, F, hχe]
  have h0 : e ⊗ₜ[k] e = 0 := by
    simpa [φ, F, RingHom.mem_ker] using hle (hI.trans (Ideal.mem_map_of_mem (p13 k A) hee))
  have : e = 0 := by simpa [h1e] using congr(TensorProduct.rid k A (LinearMap.lTensor A f₁ $h0))
  exact hx 0 (by simp [this])

/-- **Folder 128, Prop. 1 (i), field case** (Grothendieck, page 12; the reduction to rank `2`
is page 13). For `A` a commutative algebra of rank `2` over a field `k`, an equivalence ideal
of `A ⊗[k] A` is `0` or the diagonal ideal `Δ = Ker(A ⊗[k] A → A)`. -/
theorem eq_bot_or_eq_ker (h2 : Module.finrank k A = 2) {I : Ideal (A ⊗[k] A)}
    (hI : IsEquivalenceIdeal I) :
    I = ⊥ ∨ I = RingHom.ker (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A) := by
  suffices ∃ x : A, (∀ c : k, c • (1 : A) ≠ x) ∧ (I = ⊥ ∨ (1 : A) ⊗ₜ[k] x - x ⊗ₜ 1 ∈ I) by
    obtain ⟨x, hx, h | h⟩ := this
    exacts [Or.inl h, Or.inr (le_antisymm hI.refl (ker_le h2 hx h))]
  by_cases hf : ∀ a : A, a ≠ 0 → IsUnit a
  · obtain ⟨x, hx⟩ : ∃ x : A, ∀ c : k, c • (1 : A) ≠ x := by
      by_contra! h
      have := finrank_le_one (1 : A) h
      omega
    refine ⟨x, hx, or_iff_not_imp_left.2 fun hI0 => ?_⟩
    obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    obtain ⟨a, rfl⟩ := exists_smul_delta h2 hx (hI.refl ht)
    obtain ⟨u, rfl⟩ := hf a (by rintro rfl; simp at ht0)
    simpa [smul_smul] using smul_mem (↑u⁻¹ : A) ht
  obtain ⟨e, he0, heu⟩ : ∃ e : A, e ≠ 0 ∧ ¬IsUnit e := by simpa using hf
  have hx : ∀ c : k, c • (1 : A) ≠ e := by
    rintro c rfl
    have hc : c ≠ 0 := by rintro rfl; simp at he0
    exact heu (by rw [← Algebra.algebraMap_eq_smul_one]; exact (IsUnit.mk0 c hc).map _)
  obtain ⟨f₀, f₁, hf, -⟩ := coords h2 hx
  set s := f₀ (e * e)
  set r := f₁ (e * e)
  have hee : e * e = s • 1 + r • e := (hf _).symm
  have hs : s = 0 := by
    by_contra hs
    refine heu (IsUnit.of_mul_eq_one (s⁻¹ • (e - r • 1)) ?_)
    rw [mul_smul_comm, mul_sub, mul_smul_comm, mul_one, hee, add_sub_cancel_right, smul_smul,
      inv_mul_cancel₀ hs, one_smul]
  rw [hs, zero_smul, zero_add] at hee
  by_cases hr : r = 0
  · exact ⟨e, hx, nil_case h2 hI hx (by simp [hee, hr])⟩
  refine ⟨r⁻¹ • e, fun c h => hx (r * c) ?_, idem_case h2 hI (fun c h => hx (r * c) ?_) ?_⟩
  · rw [mul_smul, h, smul_smul, mul_inv_cancel₀ hr, one_smul]
  · rw [mul_smul, h, smul_smul, mul_inv_cancel₀ hr, one_smul]
  · rw [smul_mul_smul, hee, smul_smul, mul_assoc, inv_mul_cancel₀ hr, mul_one]

/-- `0` is an equivalence ideal (the coarsest relation, the whole fibre product). -/
theorem isEquivalenceIdeal_bot : IsEquivalenceIdeal (⊥ : Ideal (A ⊗[k] A)) where
  refl := bot_le
  symm t ht := by rw [Ideal.mem_bot.1 ht, map_zero]; exact zero_mem _
  trans := by rw [Ideal.map_bot]; exact bot_le

/-- `Δ` is an equivalence ideal (the finest relation, the diagonal). -/
theorem isEquivalenceIdeal_ker :
    IsEquivalenceIdeal (RingHom.ker (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A)) where
  refl := le_rfl
  symm t ht := RingHom.mem_ker.2 <| (LinearMap.mul'_comm (R := k) t).trans ht
  trans := by
    rw [show RingHom.ker _ = _ from (KaehlerDifferential.span_range_eq_ideal k A).symm,
      Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    have : p13 k A ((1 : A) ⊗ₜ[k] s - s ⊗ₜ 1) =
        p12 k A ((1 : A) ⊗ₜ[k] s - s ⊗ₜ 1) + p23 k A ((1 : A) ⊗ₜ[k] s - s ⊗ₜ 1) := by
      simp [sub_tmul]
    rw [this]
    exact add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨s, rfl⟩)))
      (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨s, rfl⟩)))

end Grothendieck.Folder128
