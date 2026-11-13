import Mathlib

/-!
# Quillen, notebook 1987-14, p. 45: the cyclic embeddings of `{1, …, k − 1}` into `{1, …, k}`

Daniel Quillen's research notebook 1987-14 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201987/1987-14.pdf>), p. 45.
The injective maps from `{1, …, k − 1}` to `{1, …, k}` that preserve the cyclic order are
`k(k − 1)` in number, the rotations of both sides acting simply transitively on them.

Here `k = n + 2` (for `k = 1` the count is `1`, the empty map, not `k(k − 1) = 0`), with
`Fin (n + 1) → Fin (n + 2)` and mathlib's circular order on `Fin` (`sbtw a b c` iff `a, b, c` are
distinct and in increasing cyclic order).

* `IsCyclic f` : `f` is injective and preserves `sbtw`;
* `emb r s` : `x ↦ (x + s) + r`, with `x + s` taken in `Fin (n + 1)` and then included in
  `Fin (n + 2)`; it is cyclic (`isCyclic_emb`);
* `rotation_of_cyclic` : a cyclic bijection of `Fin (n + 1)` is a rotation, `h x = x + h 0`;
* `emb_injective`, `exists_emb` : every cyclic map is some `emb r s`, for a unique `(r, s)`;
* `card_isCyclic` (p. 45): there are `(n + 2)(n + 1)` cyclic maps.
-/

namespace Quillen.Notebook1987_14Cyclic

open Fin

/-- `f` is injective and preserves the cyclic order. -/
def IsCyclic {m k : ℕ} (f : Fin m → Fin k) : Prop :=
  Function.Injective f ∧ ∀ a b c, sbtw a b c → sbtw (f a) (f b) (f c)

theorem sbtw_add {m : ℕ} {a b c : Fin m} (r : Fin m) (h : sbtw a b c) :
    sbtw (a + r) (b + r) (c + r) := by
  rw [Fin.sbtw_iff] at h ⊢
  simp only [Fin.lt_def, Fin.val_add_eq_ite] at h ⊢
  have := a.2; have := b.2; have := c.2; have := r.2
  split_ifs <;> omega

theorem sbtw_castSucc {m : ℕ} {a b c : Fin m} :
    sbtw a.castSucc b.castSucc c.castSucc ↔ sbtw a b c := by
  simp only [Fin.sbtw_iff, Fin.lt_def, Fin.val_castSucc]

/-- `x + 1` comes right after `x`: every other `y` satisfies `sbtw x (x + 1) y`. -/
theorem sbtw_succ {n : ℕ} {x y : Fin (n + 1)} (h1 : y ≠ x) (h2 : y ≠ x + 1) :
    sbtw x (x + 1) y := by
  rw [Fin.sbtw_iff]
  rw [Ne, Fin.ext_iff] at h1 h2
  simp only [Fin.lt_def, Fin.val_add_eq_ite] at h2 ⊢
  have := x.2; have := y.2
  rcases n with _ | n
  · omega
  · have h1v : ((1 : Fin (n + 2)) : ℕ) = 1 := rfl
    rw [h1v] at h2 ⊢
    split_ifs at h2 ⊢ <;> omega

theorem not_sbtw_swap {m : ℕ} {a b c : Fin m} (h : sbtw a b c) : ¬ sbtw a c b := by
  rw [Fin.sbtw_iff] at h ⊢; simp only [Fin.lt_def] at h ⊢; omega

/-- **A cyclic bijection of `Fin (n + 1)` is a rotation.** -/
theorem rotation_of_cyclic {n : ℕ} {h : Fin (n + 1) → Fin (n + 1)} (hh : IsCyclic h) :
    ∀ x, h x = x + h 0 := by
  have hbij : Function.Bijective h := (Finite.injective_iff_bijective).mp hh.1
  have step : ∀ x, h (x + 1) = h x + 1 := by
    intro x
    obtain ⟨y, hy⟩ := hbij.2 (h x + 1)
    by_contra hne
    have hyx1 : y ≠ x + 1 := fun e => hne (by rw [← e, hy])
    have hyx : y ≠ x := by
      rintro rfl
      -- `h y + 1 = h y` forces `n = 0`, so `x + 1 = x`
      apply hyx1
      have : (1 : Fin (n + 1)) = 0 := by
        have := congrArg (· - h y) hy; simpa using this.symm
      rw [this, add_zero]
    have hs := hh.2 _ _ _ (sbtw_succ hyx hyx1)
    rw [hy] at hs
    have h1 : h (x + 1) ≠ h x := fun e => (by
      have := hh.1 e
      have h0 : (1 : Fin (n + 1)) = 0 := by simpa using congrArg (· - x) this
      exact hyx1 (by rw [h0, add_zero]; exact (hh.1 (by rw [hy]; simp [h0])) ))
    exact not_sbtw_swap hs (sbtw_succ h1 hne)
  intro x
  induction x using Fin.induction with
  | zero => rw [zero_add]
  | succ i ih =>
    rw [← Fin.coeSucc_eq_succ, step, ih, add_right_comm]

variable {n : ℕ}

/-- `emb r s : x ↦ (x + s) + r`. -/
def emb (r : Fin (n + 2)) (s : Fin (n + 1)) : Fin (n + 1) → Fin (n + 2) :=
  fun x => (x + s).castSucc + r

theorem isCyclic_emb (r : Fin (n + 2)) (s : Fin (n + 1)) : IsCyclic (emb r s) := by
  refine ⟨fun x y hxy => ?_, fun a b c h => ?_⟩
  · simpa [emb] using hxy
  · exact sbtw_add r (sbtw_castSucc.mpr (sbtw_add s h))

theorem last_add_not_mem (r : Fin (n + 2)) (s : Fin (n + 1)) (x : Fin (n + 1)) :
    emb r s x ≠ Fin.last (n + 1) + r := by
  intro h
  simp only [emb, add_left_inj] at h
  exact Fin.castSucc_ne_last _ h

theorem emb_injective : Function.Injective fun p : Fin (n + 2) × Fin (n + 1) => emb p.1 p.2 := by
  rintro ⟨r, s⟩ ⟨r', s'⟩ h
  simp only at h
  -- the value missed by `emb r s` is `last + r`
  have hr : r = r' := by
    by_contra hne
    -- `last + r'` is a value of `emb r s`
    have hv : Fin.last (n + 1) + r' - r ≠ Fin.last (n + 1) := by
      intro e
      apply hne
      have := congrArg (· + r) e
      simp only [sub_add_cancel] at this
      exact (add_left_cancel this).symm
    obtain ⟨y, hy⟩ := Fin.exists_castSucc_eq.mpr hv
    have := last_add_not_mem r' s' (y - s)
    rw [← h] at this
    apply this
    simp only [emb, sub_add_cancel, hy, sub_add_cancel]
  subst hr
  have := congrFun h 0
  simp only [emb, zero_add, add_left_inj, Fin.castSucc_inj] at this
  rw [this]

theorem exists_emb {f : Fin (n + 1) → Fin (n + 2)} (hf : IsCyclic f) :
    ∃ r s, emb r s = f := by
  -- a value `p` missed by `f`
  obtain ⟨p, hp⟩ : ∃ p, p ∉ Set.range f := by
    by_contra hc
    push Not at hc
    have hs : Function.Surjective f := fun p => hc p
    have := Fintype.card_le_of_surjective f hs
    simp at this
  set r := p - Fin.last (n + 1)
  have hne : ∀ x, f x - r ≠ Fin.last (n + 1) := fun x e =>
    hp ⟨x, by rw [← sub_add_cancel (f x) r, e]; exact add_sub_cancel _ _⟩
  let h : Fin (n + 1) → Fin (n + 1) := fun x => (f x - r).castPred (hne x)
  have hh : ∀ x, (h x).castSucc = f x - r := fun x => Fin.castSucc_castPred _ _
  have hcyc : IsCyclic h := by
    refine ⟨fun x y e => hf.1 ?_, fun a b c habc => ?_⟩
    · have := congrArg Fin.castSucc e
      rw [hh, hh] at this
      simpa using this
    · rw [← sbtw_castSucc, hh, hh, hh]
      have := sbtw_add (-r) (hf.2 _ _ _ habc)
      simpa [sub_eq_add_neg] using this
  refine ⟨r, h 0, funext fun x => ?_⟩
  simp only [emb, ← rotation_of_cyclic hcyc x, hh, sub_add_cancel]

/-- **Quillen, notebook 1987-14, p. 45**: the cyclic-order-preserving injections from a cyclic set
with `k − 1` elements to one with `k` elements (`k = n + 2`) are `k(k − 1)` in number. -/
theorem card_isCyclic :
    Nat.card {f : Fin (n + 1) → Fin (n + 2) // IsCyclic f} = (n + 2) * (n + 1) := by
  have e : Fin (n + 2) × Fin (n + 1) ≃ {f : Fin (n + 1) → Fin (n + 2) // IsCyclic f} :=
    Equiv.ofBijective (fun p => ⟨emb p.1 p.2, isCyclic_emb p.1 p.2⟩)
      ⟨fun p q h => emb_injective (congrArg Subtype.val h), fun ⟨f, hf⟩ => by
        obtain ⟨r, s, rfl⟩ := exists_emb hf
        exact ⟨(r, s), rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_fin, Fintype.card_fin]

end Quillen.Notebook1987_14Cyclic
