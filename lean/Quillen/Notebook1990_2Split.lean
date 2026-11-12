import Mathlib

/-!
# Quillen, notebook 1990-2, pp. 64-67: endomorphisms of a split extension of complexes

Daniel Quillen's research notebook 1990-2 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201990/1990-2.pdf>).

For an exact sequence of complexes `0 → X → E → Y → 0` (maps `i`, `p`) with a splitting `h`, `k`
compatible with nothing but `ph = 1 = ki`, `ik + hp = 1`, `kh = 0`, and `d` commuting with `i`
and `p`, the class `S = k d h` satisfies `iS = [d, h]`, `Sp = −[d, k]` (`iS_eq`, `Sp_eq`); for an
endomorphism `L` of the sequence, `[L, S] = [d, kLh]` (`commutator_L_S`); a homotopy
`LS = [d, g]` gives `J = Lh − ig`, `I = Lk + gp` with `pJ = L`, `iI + Jp = L`, `Ii = L`,
`[d, J] = [d, I] = 0` (`of_homotopy`), and conversely `pJ = L`, `[d, J] = 0` give
`g = kLh − kJ` with `LS = [d, g]` (`homotopy_of`).

Everything is modelled in one ring (endomorphisms of `X ⊕ E ⊕ Y`), with ordinary commutators
`[a, b] = ab − ba`: the maps `i, p, h, k, L` have degree `0`; the signs of graded commutators
are not formalised. `pi = 0` follows from the relations (`p_mul_i`). The hypothesis
`[d, L] = 0` (`L` a map of complexes) is used for `[L, S] = [d, kLh]`.

Also p. 71: for idempotents `e`, `f` with `ef = fe = 0`, `1 − e − f` is an idempotent killing
`e` and `f` (`annihilating`).
-/

namespace Quillen.Notebook1990_2Split

variable {R : Type*} [Ring R] {d i p h k : R}

/-- The splitting relations of p. 64. -/
structure Split (d i p h k : R) : Prop where
  ph : p * h = 1
  ki : k * i = 1
  ik_hp : i * k + h * p = 1
  kh : k * h = 0
  di : d * i = i * d
  dp : d * p = p * d

theorem p_mul_i (H : Split d i p h k) : p * i = 0 := by
  have h1 : p * (i * k + h * p) * i = p * i := by rw [H.ik_hp, mul_one]
  have h2 : p * (i * k + h * p) * i = p * i + p * i := by
    simp only [mul_add, add_mul, mul_assoc, H.ki, mul_one]
    rw [← mul_assoc p h, H.ph, one_mul]
  have := h1.symm.trans h2
  simpa using this

/-- `iS = [d, h]` for `S = kdh`. -/
theorem iS_eq (H : Split d i p h k) : i * (k * d * h) = d * h - h * d := by
  have : i * k = 1 - h * p := eq_sub_of_add_eq H.ik_hp
  rw [mul_assoc k, ← mul_assoc i, this, sub_mul, one_mul, mul_assoc h p, ← mul_assoc p d,
    ← H.dp, mul_assoc d p h, H.ph, mul_one]

/-- `Sp = −[d, k]` for `S = kdh`. -/
theorem Sp_eq (H : Split d i p h k) : k * d * h * p = -(d * k - k * d) := by
  have : h * p = 1 - i * k := eq_sub_of_add_eq' H.ik_hp
  rw [mul_assoc (k * d), this, mul_sub, mul_one, ← mul_assoc (k * d) i, mul_assoc k d i, H.di,
    ← mul_assoc k i, H.ki, one_mul]
  abel

/-- **Notebook 1990-2, p. 65**: `[L, S] = [d, kLh]` for an endomorphism `L` of the sequence
(`Li = iL`, `pL = Lp`, `dL = Ld`). -/
theorem commutator_L_S (H : Split d i p h k) {L : R} (hLi : L * i = i * L) (hpL : p * L = L * p)
    (hdL : d * L = L * d) :
    L * (k * d * h) - (k * d * h) * L = d * (k * L * h) - (k * L * h) * d := by
  have hdk : d * k = k * d - k * d * h * p := by rw [Sp_eq H]; abel
  have hhd : h * d = d * h - i * (k * d * h) := by rw [iS_eq H]; abel
  have hdL' : ∀ x, d * (L * x) = L * (d * x) := fun x => by rw [← mul_assoc, hdL, mul_assoc]
  have hpL' : ∀ x, p * (L * x) = L * (p * x) := fun x => by rw [← mul_assoc, hpL, mul_assoc]
  have hLi' : ∀ x, L * (i * x) = i * (L * x) := fun x => by rw [← mul_assoc, hLi, mul_assoc]
  have hki' : ∀ x, k * (i * x) = x := fun x => by rw [← mul_assoc, H.ki, one_mul]
  rw [show d * (k * L * h) = (d * k) * L * h by noncomm_ring,
    show k * L * h * d = k * L * (h * d) by noncomm_ring, hdk, hhd]
  simp only [mul_assoc, mul_sub, sub_mul, hdL', hpL', hLi', hki', H.ph, mul_one]
  abel

/-- **Notebook 1990-2, pp. 65-67**: a homotopy `LS = [d, g]` gives maps of complexes
`J = Lh − ig`, `I = Lk + gp` with `pJ = L`, `iI + Jp = L`, `Ii = L`. -/
theorem of_homotopy (H : Split d i p h k) {L g : R} (hLi : L * i = i * L) (hpL : p * L = L * p)
    (hdL : d * L = L * d) (hg : L * (k * d * h) = d * g - g * d) :
    let J := L * h - i * g
    let I := L * k + g * p
    p * J = L ∧ i * I + J * p = L ∧ I * i = L ∧ d * J = J * d ∧ d * I = I * d := by
  intro J I
  have hpi := p_mul_i H
  have hS := iS_eq H
  have hSp := Sp_eq H
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [J, mul_sub, ← mul_assoc, hpL, hpi, zero_mul, sub_zero]
    rw [mul_assoc, H.ph, mul_one]
  · simp only [J, I]
    calc i * (L * k + g * p) + (L * h - i * g) * p = (i * L) * k + L * (h * p) := by noncomm_ring
      _ = L := by rw [← hLi, mul_assoc, ← mul_add, H.ik_hp, mul_one]
  · simp only [I, add_mul, mul_assoc, H.ki, hpi, mul_zero, mul_one, add_zero]
  · -- `[d, J] = L[d, h] − i[d, g] = LiS − iLS = 0`
    simp only [J]
    have e1 : d * (L * h) - L * h * d = L * (i * (k * d * h)) := by
      rw [hS, ← mul_assoc, hdL]; noncomm_ring
    have e2 : d * (i * g) - i * g * d = i * (L * (k * d * h)) := by
      rw [hg, ← mul_assoc, H.di]; noncomm_ring
    have : L * (i * (k * d * h)) = i * (L * (k * d * h)) := by rw [← mul_assoc, hLi, mul_assoc]
    rw [← sub_eq_zero]
    calc d * (L * h - i * g) - (L * h - i * g) * d
        = (d * (L * h) - L * h * d) - (d * (i * g) - i * g * d) := by noncomm_ring
      _ = 0 := by rw [e1, e2, this, sub_self]
  · -- `[d, I] = L[d, k] + [d, g]p = −LSp + LSp = 0`
    simp only [I]
    have e1 : d * (L * k) - L * k * d = -(L * (k * d * h * p)) := by
      rw [hSp, ← mul_assoc, hdL]; noncomm_ring
    have e2 : d * (g * p) - g * p * d = L * (k * d * h) * p := by
      rw [hg, mul_assoc g p d, ← H.dp]; noncomm_ring
    rw [← sub_eq_zero]
    calc d * (L * k + g * p) - (L * k + g * p) * d
        = (d * (L * k) - L * k * d) + (d * (g * p) - g * p * d) := by noncomm_ring
      _ = 0 := by rw [e1, e2]; noncomm_ring

/-- **Notebook 1990-2, pp. 66-67**, the converse: if `pJ = L` and `[d, J] = 0`, then
`g = kLh − kJ` satisfies `ig = Lh − J` and `LS = [d, g]`. -/
theorem homotopy_of (H : Split d i p h k) {L J : R} (hLi : L * i = i * L) (hpL : p * L = L * p)
    (hdL : d * L = L * d) (hpJ : p * J = L) (hdJ : d * J = J * d) :
    let g := k * L * h - k * J
    i * g = L * h - J ∧ L * (k * d * h) = d * g - g * d := by
  intro g
  have hig : i * g = L * h - J := by
    have : i * k = 1 - h * p := eq_sub_of_add_eq H.ik_hp
    calc i * g = (i * k) * L * h - (i * k) * J := by simp only [g]; noncomm_ring
      _ = L * h - h * (p * L) * h - J + h * (p * J) := by rw [this]; noncomm_ring
      _ = L * h - J := by rw [hpL, hpJ]; simp only [mul_assoc, H.ph, mul_one]; abel
  refine ⟨hig, ?_⟩
  -- multiply by `k` on the left: `k i = 1`
  have key : i * (L * (k * d * h)) = i * (d * g - g * d) := by
    have e : i * (d * g - g * d) = d * (i * g) - (i * g) * d := by
      rw [mul_sub, ← mul_assoc, ← H.di]; noncomm_ring
    rw [e, hig, ← mul_assoc, ← hLi, mul_assoc, iS_eq H]
    calc L * (d * h - h * d) = (d * L) * h - L * h * d := by rw [hdL]; noncomm_ring
      _ = d * (L * h - J) - (L * h - J) * d := by rw [mul_sub d, hdJ]; noncomm_ring
  have := congrArg (k * ·) key
  simpa only [← mul_assoc, H.ki, one_mul] using this

/-- **Notebook 1990-2, p. 71**: for idempotents with `ef = fe = 0`, `1 − e − f` is idempotent and
kills `e` and `f`. -/
theorem annihilating {e f : R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0) :
    IsIdempotentElem (1 - e - f) ∧ (1 - e - f) * e = 0 ∧ (1 - e - f) * f = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold IsIdempotentElem
    calc (1 - e - f) * (1 - e - f) = 1 - e - f - e + e * e + e * f - f + f * e + f * f := by
          noncomm_ring
      _ = 1 - e - f := by rw [he.eq, hf.eq, hef, hfe]; abel
  · rw [sub_mul, sub_mul, one_mul, he.eq, hfe]; abel
  · rw [sub_mul, sub_mul, one_mul, hf.eq, hef]; abel

end Quillen.Notebook1990_2Split
