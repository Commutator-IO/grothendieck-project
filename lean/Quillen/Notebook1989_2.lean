import Mathlib

/-!
# Quillen, notebook 1989-2, pp. 76-80: the perturbation lemma, algebraic form

Daniel Quillen's research notebook 1989-2 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201989/1989-2.pdf>) transfers,
on pp. 76-80, a perturbation `θ` of a differential `d` along a homotopy equivalence
`(u, v, h)`, `vu − 1 = [d, h]`, to the perturbation `θ' = u(1 − θh)⁻¹θv`: the basic
perturbation lemma.

Everything is stated in one ring `A` (think of the endomorphisms of `L ⊕ M`, `L` the large
complex and `M` the small one), with plain products of operators, so no signs appear:

* `d`, `dM` the differentials (`dM * dM = 0`), `δ` the perturbation, `(d + δ)² = 0`;
* `i : M → L`, `p : L → M` chain maps (`d * i = i * dM`, `p * d = dM * p`) and
  `h` with `i * p = 1 + d * h + h * d`;
* `w` a two-sided inverse of `1 − δ h`, and `X = w δ`.

Then, with no side conditions:

* `key`: `d X + X d + X² + X (d h + h d) X = 0`;
* `sq_eq_zero`: the transferred differential `dM' = dM + p X i` squares to zero;
* `chain_left`, `chain_right`: `i' = i + h X i` and `p' = p + p X h` are chain maps for
  `d + δ` and `dM'`;
* `homotopy`: `i' p' = 1 + (d + δ) h' + h' (d + δ)` for `h' = h + h X h`;

and, under the side conditions `p i = 1`, `h i = 0`, `p h = 0`, `h² = 0`, `p'i' = 1`
(`retract`).
-/

namespace Quillen.Notebook1989_2

variable {A : Type*} [Ring A] {d δ h w : A}

/-- `1 − hδ` is invertible when `1 − δh` is, with inverse `1 + h w δ`. -/
theorem one_sub_mul_inv_left (hw₂ : (1 - δ * h) * w = 1) :
    (1 - h * δ) * (1 + h * w * δ) = 1 := by
  have : (1 - h * δ) * (1 + h * w * δ) = 1 + h * ((1 - δ * h) * w - 1) * δ := by noncomm_ring
  rw [this, hw₂]; noncomm_ring

theorem one_sub_mul_inv_right (hw₁ : w * (1 - δ * h) = 1) :
    (1 + h * w * δ) * (1 - h * δ) = 1 := by
  have : (1 + h * w * δ) * (1 - h * δ) = 1 + h * (w * (1 - δ * h) - 1) * δ := by noncomm_ring
  rw [this, hw₁]; noncomm_ring

theorem mul_X_left (hw₂ : (1 - δ * h) * w = 1) : (1 - δ * h) * (w * δ) = δ := by
  rw [← mul_assoc, hw₂, one_mul]

theorem mul_X_right (hw₁ : w * (1 - δ * h) = 1) : w * δ * (1 - h * δ) = δ := by
  have : w * δ * (1 - h * δ) = w * (1 - δ * h) * δ := by noncomm_ring
  rw [this, hw₁, one_mul]

/-- **Notebook 1989-2, pp. 76-80**, the key identity: with `X = (1 − δh)⁻¹δ`,
`dX + Xd + X² + X(dh + hd)X = 0` whenever `d² = 0` and `(d + δ)² = 0`. -/
theorem key (hd : d * d = 0) (hD : (d + δ) * (d + δ) = 0) (hw₁ : w * (1 - δ * h) = 1)
    (hw₂ : (1 - δ * h) * w = 1) :
    d * (w * δ) + w * δ * d + w * δ * (w * δ) + w * δ * (d * h + h * d) * (w * δ) = 0 := by
  set X := w * δ with hX
  set E := d * X + X * d + X * X + X * (d * h + h * d) * X
  have hl : (1 - δ * h) * X = δ := mul_X_left hw₂
  have hr : X * (1 - h * δ) = δ := mul_X_right hw₁
  have hmid : (1 - δ * h) * E * (1 - h * δ) = 0 := by
    have e1 : (1 - δ * h) * E * (1 - h * δ) =
        (1 - δ * h) * d * (X * (1 - h * δ)) + (1 - δ * h) * X * d * (1 - h * δ) +
          (1 - δ * h) * X * (X * (1 - h * δ)) +
            (1 - δ * h) * X * (d * h + h * d) * (X * (1 - h * δ)) := by
      simp only [E]; noncomm_ring
    rw [e1, hr, hl]
    have e2 : (1 - δ * h) * d * δ + δ * d * (1 - h * δ) + δ * δ + δ * (d * h + h * d) * δ =
        (d + δ) * (d + δ) - d * d := by noncomm_ring
    rw [e2, hd, hD, sub_zero]
  calc E = (w * (1 - δ * h)) * E * ((1 - h * δ) * (1 + h * w * δ)) := by
        rw [hw₁, one_sub_mul_inv_left hw₂, one_mul, mul_one]
    _ = w * ((1 - δ * h) * E * (1 - h * δ)) * (1 + h * w * δ) := by noncomm_ring
    _ = 0 := by rw [hmid, mul_zero, zero_mul]

variable {dM i p : A}

/-- **Notebook 1989-2**: the transferred differential `dM + p X i` squares to zero. -/
theorem sq_eq_zero (hd : d * d = 0) (hD : (d + δ) * (d + δ) = 0) (hw₁ : w * (1 - δ * h) = 1)
    (hw₂ : (1 - δ * h) * w = 1) (hdM : dM * dM = 0) (hpd : p * d = dM * p)
    (hdi : d * i = i * dM) (hip : i * p = 1 + d * h + h * d) :
    (dM + p * (w * δ) * i) * (dM + p * (w * δ) * i) = 0 := by
  set X := w * δ
  have hk := key hd hD hw₁ hw₂
  calc (dM + p * X * i) * (dM + p * X * i)
        = dM * dM + (dM * p) * X * i + p * X * (i * dM) + p * X * (i * p) * X * i := by
          noncomm_ring
    _ = p * (d * X + X * d + X * X + X * (d * h + h * d) * X) * i := by
          rw [hdM, ← hpd, ← hdi, hip]; noncomm_ring
    _ = 0 := by rw [hk, mul_zero, zero_mul]

/-- **Notebook 1989-2**: `i' = i + h X i` is a chain map, `(d + δ) i' = i' dM'`. -/
theorem chain_left (hd : d * d = 0) (hD : (d + δ) * (d + δ) = 0) (hw₁ : w * (1 - δ * h) = 1)
    (hw₂ : (1 - δ * h) * w = 1) (hdi : d * i = i * dM) (hip : i * p = 1 + d * h + h * d) :
    (d + δ) * (i + h * (w * δ) * i) = (i + h * (w * δ) * i) * (dM + p * (w * δ) * i) := by
  set X := w * δ
  have hk := key hd hD hw₁ hw₂
  have hl : (1 - δ * h) * X = δ := mul_X_left hw₂
  rw [← sub_eq_zero]
  calc (d + δ) * (i + h * X * i) - (i + h * X * i) * (dM + p * X * i)
        = (d + δ) * (i + h * X * i) - (i * dM + (i * p) * X * i + h * X * (i * dM) +
            h * X * (i * p) * X * i) := by noncomm_ring
    _ = -(((1 - δ * h) * X - δ) * i + h * (d * X + X * d + X * X + X * (d * h + h * d) * X) * i)
        := by rw [← hdi, hip]; noncomm_ring
    _ = 0 := by rw [hl, hk]; noncomm_ring

/-- **Notebook 1989-2**: `p' = p + p X h` is a chain map, `p' (d + δ) = dM' p'`. -/
theorem chain_right (hd : d * d = 0) (hD : (d + δ) * (d + δ) = 0) (hw₁ : w * (1 - δ * h) = 1)
    (hw₂ : (1 - δ * h) * w = 1) (hpd : p * d = dM * p) (hip : i * p = 1 + d * h + h * d) :
    (p + p * (w * δ) * h) * (d + δ) = (dM + p * (w * δ) * i) * (p + p * (w * δ) * h) := by
  set X := w * δ
  have hk := key hd hD hw₁ hw₂
  have hr : X * (1 - h * δ) = δ := mul_X_right hw₁
  rw [← sub_eq_zero]
  calc (p + p * X * h) * (d + δ) - (dM + p * X * i) * (p + p * X * h)
        = (p + p * X * h) * (d + δ) - ((dM * p) + (dM * p) * X * h + p * X * (i * p) +
            p * X * (i * p) * X * h) := by noncomm_ring
    _ = -(p * (X * (1 - h * δ) - δ) + p * (d * X + X * d + X * X + X * (d * h + h * d) * X) * h)
        := by rw [← hpd, hip]; noncomm_ring
    _ = 0 := by rw [hr, hk]; noncomm_ring

/-- **Notebook 1989-2**: the homotopy `h' = h + h X h`: `i'p' = 1 + (d + δ)h' + h'(d + δ)`. -/
theorem homotopy (hd : d * d = 0) (hD : (d + δ) * (d + δ) = 0) (hw₁ : w * (1 - δ * h) = 1)
    (hw₂ : (1 - δ * h) * w = 1) (hip : i * p = 1 + d * h + h * d) :
    (i + h * (w * δ) * i) * (p + p * (w * δ) * h) =
      1 + (d + δ) * (h + h * (w * δ) * h) + (h + h * (w * δ) * h) * (d + δ) := by
  set X := w * δ
  have hk := key hd hD hw₁ hw₂
  have hl : (1 - δ * h) * X = δ := mul_X_left hw₂
  have hr : X * (1 - h * δ) = δ := mul_X_right hw₁
  rw [← sub_eq_zero]
  calc (i + h * X * i) * (p + p * X * h) - (1 + (d + δ) * (h + h * X * h) + (h + h * X * h) * (d + δ))
        = (i * p) + (i * p) * X * h + h * X * (i * p) + h * X * (i * p) * X * h -
            (1 + (d + δ) * (h + h * X * h) + (h + h * X * h) * (d + δ)) := by noncomm_ring
    _ = ((1 - δ * h) * X - δ) * h + h * (X * (1 - h * δ) - δ) +
          h * (d * X + X * d + X * X + X * (d * h + h * d) * X) * h := by
        rw [hip]; noncomm_ring
    _ = 0 := by rw [hl, hr, hk]; noncomm_ring

/-- **Notebook 1989-2**: under the side conditions `p i = 1`, `h i = 0`, `p h = 0`, `h² = 0`,
the new data is again a retraction, `p' i' = 1`. -/
theorem retract (hpi : p * i = 1) (hhi : h * i = 0) (hph : p * h = 0) (hhh : h * h = 0) :
    (p + p * (w * δ) * h) * (i + h * (w * δ) * i) = 1 := by
  have : (p + p * (w * δ) * h) * (i + h * (w * δ) * i) =
      p * i + p * (w * δ) * (h * i) + (p * h) * (w * δ) * i +
        p * (w * δ) * (h * h) * (w * δ) * i := by noncomm_ring
  rw [this, hpi, hhi, hph, hhh]; noncomm_ring

end Quillen.Notebook1989_2
