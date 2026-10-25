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

/-!
## Pages 14–18, Prop. 2: the colength criterion, field case

Prop. 2 (pages 14–18): `A` local artinian, `A'` finite over `A` with trivial residue extensions,
`J` an equivalence ideal with `A → A' ⇉ A'' = (A' ⊗_A A')/J` exact and `δ(x') = p₂(x') − p₁(x')`
generating `Δ/J` for every `x' ∉ A`; then `A'/A` has length `≤ 1`, and `A'' = A' ⊗_A A'` when it
is `1`. Here `A = k` is a field (the case both branches of the page reduce to) and `A` below is
the reading's `A'`:
* `Colength.finrank_le_two`: `dim_k A ≤ 2`, for any ideal `J ⊂ Δ` (neither symmetry nor
  transitivity is used);
* `Colength.eq_bot_of_finrank_eq_two`, `Colength.prop2`: if `dim_k A = 2`, `J = 0`.

The proof differs from the page's (radiciel / non radiciel, `A' ≃ kⁿ` or `k ⊕ V`): for a point
`χ : A → k` with ideal `𝔪_χ`, `φ_χ : a ⊗ b ↦ χ(a) b` sends `δ(x)` to `x − χ(x)`, so the hypothesis
gives `𝔪_χ ⊂ A z + φ_χ(J)` for every `0 ≠ z ∈ 𝔪_χ`. Either `φ_χ(J) = 0` for some `χ`, and then
`𝔪_χ` is a simple module, of dimension `1` (residue fields are `k`); or `𝔪_χ ⊂ φ_χ(J)` for all `χ`,
and since `f ≡ δ(φ_χ f)` modulo `𝔪_χ Δ`, `Δ ⊂ J + 𝔪 Δ` for every maximal `𝔪`, so `Δ ⊂ J` by
Nakayama and exactness gives `A = k`.

Not formalised: the reduction from `A` local artinian to `A = k` (`𝔪A' = 𝔪`, through Prop. 3 and
Cor. 2 of N° 1), and the passage from ideals to subschemes.
-/

namespace Colength

open Module

variable (k A) in
/-- `δ(x) = p₂(x) − p₁(x) = 1 ⊗ x − x ⊗ 1`, as a `k`-linear map. -/
noncomputable def delta : A →ₗ[k] A ⊗[k] A :=
  TensorProduct.mk k A A 1 - (TensorProduct.mk k A A).flip 1

lemma delta_apply (x : A) : delta k A x = (1 : A) ⊗ₜ[k] x - x ⊗ₜ 1 := rfl

variable (k A) in
/-- The augmentation ideal `Δ = Ker(A ⊗ A → A)`. -/
noncomputable abbrev diag : Ideal (A ⊗[k] A) :=
  RingHom.ker (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A)

lemma delta_mem (x : A) : delta k A x ∈ diag k A := by
  simp [delta_apply, RingHom.mem_ker]

lemma delta_algebraMap (c : k) : delta k A (algebraMap k A c) = 0 := by
  simp [delta_apply, Algebra.algebraMap_eq_smul_one]

/-- `φ_χ : a ⊗ b ↦ χ(a) b`, restriction of the first factor to the point `χ`. -/
noncomputable def phi (χ : A →ₐ[k] k) : A ⊗[k] A →ₐ[k] A :=
  (Algebra.TensorProduct.lid k A).toAlgHom.comp (Algebra.TensorProduct.map χ (AlgHom.id k A))

lemma phi_tmul (χ : A →ₐ[k] k) (a b : A) : phi χ (a ⊗ₜ b) = χ a • b := by simp [phi]

lemma phi_delta (χ : A →ₐ[k] k) (x : A) :
    phi χ (delta k A x) = x - algebraMap k A (χ x) := by
  simp [delta_apply, phi_tmul, Algebra.algebraMap_eq_smul_one]

lemma phi_smul (χ : A →ₐ[k] k) (a : A) (t : A ⊗[k] A) : phi χ (a • t) = χ a • phi χ t := by
  rw [Algebra.smul_def, map_mul, show algebraMap A (A ⊗[k] A) a = a ⊗ₜ 1 from rfl, phi_tmul,
    smul_mul_assoc, one_mul]

lemma chi_phi (χ : A →ₐ[k] k) (t : A ⊗[k] A) : χ (phi χ t) = χ (Algebra.TensorProduct.lmul' k t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp [phi_tmul]
  | add s t hs ht => simp only [map_add, hs, ht]

lemma mem_span_delta {t : A ⊗[k] A} (ht : t ∈ diag k A) :
    t ∈ Submodule.span A (Set.range (delta k A)) := by
  rwa [show Set.range (delta k A) = Set.range fun s : A => (1 : A) ⊗ₜ[k] s - s ⊗ₜ 1 from rfl,
    KaehlerDifferential.submodule_span_range_eq_ideal]

/-- `f ≡ δ(φ_χ f)` modulo `𝔪_χ · Δ`, for `f ∈ Δ`. -/
lemma sub_delta_phi_mem (χ : A →ₐ[k] k) {f : A ⊗[k] A} (hf : f ∈ diag k A) :
    f - delta k A (phi χ f) ∈ RingHom.ker χ • (diag k A).restrictScalars A := by
  suffices ∀ t ∈ Submodule.span A (Set.range (delta k A)),
      t - delta k A (phi χ t) ∈ RingHom.ker χ • (diag k A).restrictScalars A from
    this f (mem_span_delta hf)
  intro t ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    simp [phi_delta, delta_algebraMap]
  | zero => simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1; simp only [map_add]; abel
  | smul a x hx' hx =>
    have hxD : x ∈ (diag k A).restrictScalars A := by
      rw [← KaehlerDifferential.submodule_span_range_eq_ideal]; exact hx'
    have h1 : (a - algebraMap k A (χ a)) • x ∈ RingHom.ker χ • (diag k A).restrictScalars A :=
      Submodule.smul_mem_smul (by simp [RingHom.mem_ker]) hxD
    convert add_mem h1 (Submodule.smul_of_tower_mem _ (χ a) hx) using 1
    rw [phi_smul, map_smul, sub_smul, algebraMap_smul, smul_sub]
    abel

/-- Nakayama at every maximal ideal: if `N ⊂ N' + 𝔪 N` for every maximal `𝔪`, then `N ⊂ N'`. -/
lemma le_of_forall_le_sup_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {N N' : Submodule R M} (hN : N.FG) (h : ∀ m : Ideal R, m.IsMaximal → N ≤ N' ⊔ m • N) :
    N ≤ N' := by
  suffices N'.colon N = ⊤ by
    intro n hn
    have := Submodule.mem_colon.1 (this ▸ Submodule.mem_top (x := (1 : R))) n hn
    rwa [one_smul] at this
  by_contra hC
  obtain ⟨m, hm, hCm⟩ := Ideal.exists_le_maximal _ hC
  have hle : N.map N'.mkQ ≤ m • N.map N'.mkQ := by
    rw [← Submodule.map_smul'']
    calc N.map N'.mkQ ≤ (N' ⊔ m • N).map N'.mkQ := Submodule.map_mono (h m hm)
      _ = _ := by rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
  obtain ⟨r, hr, hr0⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m _ (hN.map _) hle
  have hrC : r ∈ N'.colon N := Submodule.mem_colon.2 fun n hn => by
    have := hr0 _ (Submodule.mem_map_of_mem hn)
    rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem (hCm hrC) hr))

/-- If a nonzero `z ∈ 𝔪_χ` generates the ideal `𝔪_χ` whatever it is, `A = k ⊕ 𝔪_χ` with
`𝔪_χ` simple, hence of dimension `≤ 1`: the case where `J` does not meet the fibre of `χ`. -/
lemma finrank_le_two_of_simple [Module.Finite k A]
    (hres : ∀ m : Ideal A, m.IsMaximal → ∃ χ : A →ₐ[k] k, RingHom.ker χ = m) (χ : A →ₐ[k] k)
    (h : ∀ z ∈ RingHom.ker χ, z ≠ 0 → ∀ y ∈ RingHom.ker χ, y ∈ Ideal.span {z}) :
    finrank k A ≤ 2 := by
  have hsplit : ∀ (ψ : A →ₐ[k] k) (a : A), a - algebraMap k A (ψ a) ∈ RingHom.ker ψ :=
    fun ψ a => by simp [RingHom.mem_ker]
  by_cases hm : ∀ z ∈ RingHom.ker χ, z = 0
  · refine (finrank_le_one (1 : A) fun a => ⟨χ a, ?_⟩).trans (by norm_num)
    rw [← Algebra.algebraMap_eq_smul_one, ← sub_eq_zero, ← neg_sub, hm _ (hsplit χ a), neg_zero]
  push Not at hm
  obtain ⟨z, hz, hz0⟩ := hm
  obtain ⟨n, hn, hIn⟩ := Ideal.exists_le_maximal (LinearMap.ker (LinearMap.toSpanSingleton A A z))
    (by rw [Ne, Submodule.eq_top_iff']; push Not; exact ⟨1, by simpa using hz0⟩)
  obtain ⟨χ', rfl⟩ := hres n hn
  -- `𝔪_{χ'}` kills `z`
  have hkill : ∀ w ∈ RingHom.ker χ', w * z = 0 := fun w hw => by
    by_contra hwz
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1
      (h (w * z) (Ideal.mul_mem_left _ w hz) hwz z hz)
    have : 1 - b * w ∈ RingHom.ker χ' := hIn (by
      simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul]
      rw [sub_mul, one_mul, mul_assoc, hb, sub_self])
    exact hn.ne_top ((Ideal.eq_top_iff_one _).2 (by
      simpa using add_mem this (Ideal.mul_mem_left _ b hw)))
  -- so `𝔪_χ = k z`, and `(c, d) ↦ c + d z` is onto
  let f : k × k →ₗ[k] A := (LinearMap.toSpanSingleton k A 1).coprod (LinearMap.toSpanSingleton k A z)
  have hf : Function.Surjective f := fun a => by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (h z hz hz0 _ (hsplit χ a))
    refine ⟨(χ a, χ' b), ?_⟩
    have e : b * z = χ' b • z := by
      rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul]; exact hkill _ (hsplit χ' b)
    simp only [f, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply, ← e, hb,
      ← Algebra.algebraMap_eq_smul_one, add_sub_cancel]
  have := LinearMap.finrank_range_le f
  rw [LinearMap.range_eq_top.2 hf, finrank_top, Module.finrank_prod, Module.finrank_self] at this
  exact this

/-- For `0 ≠ z ∈ 𝔪_χ` and `y ∈ 𝔪_χ`, the hypothesis `Δ ⊂ (δ z) + J` read through `φ_χ`. -/
lemma phi_decomp {J : Ideal (A ⊗[k] A)}
    (hgen : ∀ x : A, x ∉ Set.range (algebraMap k A) → diag k A ≤ Ideal.span {delta k A x} ⊔ J)
    (χ : A →ₐ[k] k) {z : A} (hz : z ∈ RingHom.ker χ) (hz0 : z ≠ 0) {y : A}
    (hy : y ∈ RingHom.ker χ) : ∃ u : A ⊗[k] A, ∃ j ∈ J, phi χ u * z + phi χ j = y := by
  have hzk : z ∉ Set.range (algebraMap k A) := by
    rintro ⟨c, rfl⟩
    exact hz0 (by simp [(by simpa [RingHom.mem_ker] using hz : c = 0)])
  obtain ⟨u, j, hj, e⟩ := Ideal.mem_span_singleton_sup.1 (hgen z hzk (delta_mem y))
  refine ⟨u, j, hj, ?_⟩
  have := congr(phi χ $e)
  rw [map_add, map_mul, phi_delta, phi_delta, (RingHom.mem_ker).1 hz,
    (RingHom.mem_ker).1 hy] at this
  simpa using this

/-- **Folder 128, Prop. 2, field case** (Grothendieck, pages 14–18). Let `A` be a finite
commutative algebra over a field `k` whose residue fields are all `k` (every maximal ideal is the
kernel of a `k`-point), and `J ⊂ Δ` an ideal of `A ⊗[k] A` such that
* (exactness of `k → A ⇉ (A ⊗ A)/J`) `δ(x) ∈ J` only for `x ∈ k`;
* (`δ(x)` generates `Δ/J` in `(A ⊗ A)/J`) `Δ ⊂ (δ(x)) + J` for every `x ∉ k`.
Then `dim_k A ≤ 2`, i.e. `A/k` has length `≤ 1`. Neither symmetry nor transitivity of `J` is
used, and there is no case split radiciel / non radiciel. -/
theorem finrank_le_two [Module.Finite k A]
    (hres : ∀ m : Ideal A, m.IsMaximal → ∃ χ : A →ₐ[k] k, RingHom.ker χ = m)
    {J : Ideal (A ⊗[k] A)} (hJ : J ≤ diag k A)
    (hexact : ∀ x : A, delta k A x ∈ J → x ∈ Set.range (algebraMap k A))
    (hgen : ∀ x : A, x ∉ Set.range (algebraMap k A) → diag k A ≤ Ideal.span {delta k A x} ⊔ J) :
    finrank k A ≤ 2 := by
  by_contra hlt
  -- at each point `χ`, either `J` misses the fibre (then `dim A ≤ 2`) or `𝔪_χ ⊂ φ_χ(J)`
  have hfib : ∀ χ : A →ₐ[k] k, ∀ y ∈ RingHom.ker χ, ∃ f ∈ J, phi χ f = y := by
    intro χ
    by_cases hK : ∃ f ∈ J, phi χ f ≠ 0
    · obtain ⟨f, hf, hf0⟩ := hK
      have hfm : phi χ f ∈ RingHom.ker χ := by
        rw [RingHom.mem_ker, chi_phi, (RingHom.mem_ker).1 (hJ hf), map_zero]
      intro y hy
      obtain ⟨u, j, hj, e⟩ := phi_decomp hgen χ hfm hf0 hy
      exact ⟨u * f + j, J.add_mem (J.mul_mem_left u hf) hj, by rw [map_add, map_mul, e]⟩
    · push Not at hK
      refine absurd (finrank_le_two_of_simple hres χ fun z hz hz0 y hy => ?_) hlt
      obtain ⟨u, j, hj, e⟩ := phi_decomp hgen χ hz hz0 hy
      rw [hK j hj, add_zero] at e
      exact Ideal.mem_span_singleton'.2 ⟨_, e⟩
  -- hence `Δ ⊂ J + 𝔪 Δ` for every maximal `𝔪`, and `Δ ⊂ J` by Nakayama
  have hD : (diag k A).restrictScalars A ≤ J.restrictScalars A := by
    have : IsNoetherian A (A ⊗[k] A) := isNoetherian_of_tower k inferInstance
    refine le_of_forall_le_sup_smul (IsNoetherian.noetherian _) fun m hm => ?_
    obtain ⟨χ, rfl⟩ := hres m hm
    intro t ht
    rw [← KaehlerDifferential.submodule_span_range_eq_ideal] at ht
    refine (Submodule.span_le.2 ?_) ht
    rintro _ ⟨x, rfl⟩
    obtain ⟨f, hf, e⟩ := hfib χ _ (show x - algebraMap k A (χ x) ∈ RingHom.ker χ by
      simp [RingHom.mem_ker])
    have : (1 : A) ⊗ₜ[k] x - x ⊗ₜ 1 = f - (f - delta k A (phi χ f)) := by
      rw [sub_sub_cancel, e, map_sub, delta_algebraMap, sub_zero, delta_apply]
    change (1 : A) ⊗ₜ[k] x - x ⊗ₜ 1 ∈ _
    rw [this]
    exact sub_mem (Submodule.mem_sup_left hf) (Submodule.mem_sup_right (sub_delta_phi_mem χ (hJ hf)))
  -- exactness: `δ(x) ∈ Δ ⊂ J` forces `x ∈ k`, so `dim A ≤ 1`
  refine hlt ((finrank_le_one (1 : A) fun a => ?_).trans (by norm_num))
  obtain ⟨c, hc⟩ := hexact a (hD (delta_mem a))
  exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩

/-- Prop. 2, last assertion: if `A/k` has length `1`, an exact equivalence ideal is `0`, so
`(A ⊗ A)/J = A ⊗ A` (by `eq_bot_or_eq_ker`, `J = Δ` contradicting exactness). -/
theorem eq_bot_of_finrank_eq_two (h2 : finrank k A = 2) {J : Ideal (A ⊗[k] A)}
    (hJ : IsEquivalenceIdeal J)
    (hexact : ∀ x : A, delta k A x ∈ J → x ∈ Set.range (algebraMap k A)) : J = ⊥ := by
  refine (eq_bot_or_eq_ker h2 hJ).resolve_right fun hJD => ?_
  obtain ⟨x, hx⟩ : ∃ x : A, ∀ c : k, c • (1 : A) ≠ x := by
    by_contra! h
    have := finrank_le_one (1 : A) h
    omega
  obtain ⟨c, hc⟩ := hexact x (hJD ▸ delta_mem x)
  exact hx c (by rw [← hc, Algebra.algebraMap_eq_smul_one])

/-- **Folder 128, Prop. 2, field case, as stated** (pages 14–18): for an equivalence ideal `J`
of `A ⊗[k] A` with `k → A ⇉ (A ⊗ A)/J` exact and `δ(x)` generating `Δ/J` for every `x ∉ k`,
`A/k` has length `≤ 1`, and if it is `1` then `J = 0`. -/
theorem prop2 [Module.Finite k A]
    (hres : ∀ m : Ideal A, m.IsMaximal → ∃ χ : A →ₐ[k] k, RingHom.ker χ = m)
    {J : Ideal (A ⊗[k] A)} (hJ : IsEquivalenceIdeal J)
    (hexact : ∀ x : A, delta k A x ∈ J → x ∈ Set.range (algebraMap k A))
    (hgen : ∀ x : A, x ∉ Set.range (algebraMap k A) → diag k A ≤ Ideal.span {delta k A x} ⊔ J) :
    finrank k A ≤ 2 ∧ (finrank k A = 2 → J = ⊥) :=
  ⟨finrank_le_two hres hJ.refl hexact hgen, fun h2 => eq_bot_of_finrank_eq_two h2 hJ hexact⟩

end Colength

end Grothendieck.Folder128

