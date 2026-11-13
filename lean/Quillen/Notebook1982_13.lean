import Mathlib

/-!
# Quillen, notebook 1982-13, p. 70: the projections `1 - e(ηⱼ) i(Xⱼ)`

Daniel Quillen's research notebook 1982-13 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201982/1982-13.pdf>), in a run
dated December 23, 1982 on equivariant cohomology by differential forms (pp. 67–71), wants to
identify `Ω(M)` with the subspace of `Λ𝔤* ⊗ Ω(M)` killed by all the contractions `i(X)`,
`X ∈ 𝔤`. In our words: for a basis `Xⱼ` of `𝔤` with dual basis `ηⱼ`, the operators
`Pⱼ = 1 - e(ηⱼ) i(Xⱼ)` (exterior multiplication followed by contraction) commute, are
projections, and `i(Xⱼ) Pⱼ = 0`; so their product is a projection whose image is the joint kernel
of the `i(Xⱼ)` (p. 70).

The computation only uses the canonical anticommutation relations between the `e`'s and the
`i`'s. This file proves it in that generality: in any ring `A` (for instance the endomorphisms of
`Λ𝔤* ⊗ Ω(M)`), for families `e i : ι → A` such that

* `i j * i j = 0` and `e j * i j + i j * e j = 1`,
* for `j ≠ k`, `e j` and `e k`, `i j` and `i k`, `e j` and `i k` anticommute,

we show:

* `idem_proj`, `inc_mul_proj`: `P j = 1 - e j * i j` is idempotent and `i j * P j = 0`;
* `commute_proj`: the `P j` commute pairwise;
* `isIdempotentElem_prodProj`, `inc_mul_prodProj`: for a list `l` without repetition, the
  product `Q l` of the `P j`, `j ∈ l`, is idempotent and killed on the left by every `i k`,
  `k ∈ l`;
* `prodProj_smul_of_inc`, `mem_range_prodProj_iff`: on an `A`-module, `Q l` fixes the vectors
  killed by the `i k`, `k ∈ l`, and its image is exactly their joint kernel;
* `exterior_isCAR`: the hypotheses hold for exterior multiplication and contraction on an exterior
  algebra `Λ V`, along a family `vⱼ` of vectors and a family `fⱼ` of linear forms with
  `fₖ (vⱼ) = δⱼₖ`.

The nilpotency `e j * e j = 0`, true on the page, is not needed.
-/

namespace Quillen.Notebook1982_13

variable {A : Type*} [Ring A] {ι : Type*}

/-- The canonical anticommutation relations used on p. 70 of notebook 1982-13 (the square
`e j * e j = 0` is not required). -/
structure IsCAR (e i : ι → A) : Prop where
  inc_sq : ∀ j, i j * i j = 0
  anticomm_self : ∀ j, e j * i j + i j * e j = 1
  ext_anticomm : ∀ j k, j ≠ k → e j * e k = -(e k * e j)
  inc_anticomm : ∀ j k, j ≠ k → i j * i k = -(i k * i j)
  ext_inc_anticomm : ∀ j k, j ≠ k → e j * i k = -(i k * e j)

/-- The operator `1 - e(ηⱼ) i(Xⱼ)` of the page. -/
def proj (e i : ι → A) (j : ι) : A := 1 - e j * i j

/-- A product of two elements that anticommute with `x` commutes with `x`. -/
theorem commute_mul_of_anticomm {a b x : A} (ha : a * x = -(x * a)) (hb : b * x = -(x * b)) :
    Commute (a * b) x := by
  change a * b * x = x * (a * b)
  rw [mul_assoc, hb, mul_neg, ← mul_assoc, ha, neg_mul, neg_neg, mul_assoc]

variable {e i : ι → A}

theorem mul_self_ext_inc (h : IsCAR e i) (j : ι) : e j * i j * (e j * i j) = e j * i j := by
  have hie : i j * e j = 1 - e j * i j := eq_sub_of_add_eq' (h.anticomm_self j)
  calc e j * i j * (e j * i j) = e j * (i j * e j) * i j := by simp only [mul_assoc]
    _ = e j * i j - e j * e j * (i j * i j) := by rw [hie]; noncomm_ring
    _ = e j * i j := by rw [h.inc_sq j, mul_zero, sub_zero]

/-- **Quillen, notebook 1982-13, p. 70.** Each `1 - e(ηⱼ) i(Xⱼ)` is a projection. -/
theorem idem_proj (h : IsCAR e i) (j : ι) : IsIdempotentElem (proj e i j) := by
  unfold IsIdempotentElem proj
  calc (1 - e j * i j) * (1 - e j * i j)
      = 1 - e j * i j - e j * i j + e j * i j * (e j * i j) := by noncomm_ring
    _ = 1 - e j * i j := by rw [mul_self_ext_inc h j]; abel

/-- **Quillen, notebook 1982-13, p. 70.** `i(Xⱼ) (1 - e(ηⱼ) i(Xⱼ)) = 0`. -/
theorem inc_mul_proj (h : IsCAR e i) (j : ι) : i j * proj e i j = 0 := by
  have hie : i j * e j = 1 - e j * i j := eq_sub_of_add_eq' (h.anticomm_self j)
  unfold proj
  calc i j * (1 - e j * i j) = i j - (i j * e j) * i j := by noncomm_ring
    _ = e j * (i j * i j) := by rw [hie]; noncomm_ring
    _ = 0 := by rw [h.inc_sq j, mul_zero]

/-- For `k ≠ j`, the operator `P j` commutes with `e k`. -/
theorem commute_proj_ext (h : IsCAR e i) {j k : ι} (hjk : j ≠ k) : Commute (proj e i j) (e k) :=
  (Commute.one_left _).sub_left
    (commute_mul_of_anticomm (h.ext_anticomm j k hjk)
      (by rw [h.ext_inc_anticomm k j hjk.symm, neg_neg]))

/-- For `k ≠ j`, the operator `P j` commutes with `i k`. -/
theorem commute_proj_inc (h : IsCAR e i) {j k : ι} (hjk : j ≠ k) : Commute (proj e i j) (i k) :=
  (Commute.one_left _).sub_left
    (commute_mul_of_anticomm (h.ext_inc_anticomm j k hjk) (h.inc_anticomm j k hjk))

/-- **Quillen, notebook 1982-13, p. 70.** The operators `1 - e(ηⱼ) i(Xⱼ)` commute pairwise. -/
theorem commute_proj (h : IsCAR e i) (j k : ι) : Commute (proj e i j) (proj e i k) := by
  obtain rfl | hjk := eq_or_ne j k
  exacts [Commute.refl _, (Commute.one_right _).sub_right
    ((commute_proj_ext h hjk).mul_right (commute_proj_inc h hjk))]

/-- The product of the projections `P j`, `j ∈ l`. -/
def prodProj (e i : ι → A) (l : List ι) : A := (l.map (proj e i)).prod

@[simp] theorem prodProj_nil : prodProj e i [] = 1 := rfl

@[simp] theorem prodProj_cons (a : ι) (l : List ι) :
    prodProj e i (a :: l) = proj e i a * prodProj e i l := by
  simp [prodProj]

theorem commute_proj_prodProj (h : IsCAR e i) (a : ι) (l : List ι) :
    Commute (proj e i a) (prodProj e i l) :=
  Commute.list_prod_right _ _ fun b hb => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hb
    exact commute_proj h a c

/-- **Quillen, notebook 1982-13, p. 70.** The product of the projections is a projection. -/
theorem isIdempotentElem_prodProj (h : IsCAR e i) (l : List ι) :
    IsIdempotentElem (prodProj e i l) := by
  induction l with
  | nil => exact IsIdempotentElem.one
  | cons a l ih =>
    rw [prodProj_cons]
    exact IsIdempotentElem.mul_of_commute (commute_proj_prodProj h a l) (idem_proj h a) ih

/-- **Quillen, notebook 1982-13, p. 70.** The product of the projections is killed on the left by
every contraction `i k` with `k ∈ l`, when `l` has no repetition. -/
theorem inc_mul_prodProj (h : IsCAR e i) {l : List ι} (hl : l.Nodup) {k : ι} (hk : k ∈ l) :
    i k * prodProj e i l = 0 := by
  induction l with
  | nil => simp at hk
  | cons a l ih =>
    rw [prodProj_cons]
    rcases List.mem_cons.1 hk with rfl | hk'
    · rw [← mul_assoc, inc_mul_proj h, zero_mul]
    · have hka : a ≠ k := fun hak => (List.nodup_cons.1 hl).1 (hak ▸ hk')
      rw [← mul_assoc, ← (commute_proj_inc h hka).eq, mul_assoc,
        ih (List.nodup_cons.1 hl).2 hk', mul_zero]

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- **Quillen, notebook 1982-13, p. 70.** The product of the projections fixes every vector
killed by the contractions `i k`, `k ∈ l`. -/
theorem prodProj_smul_of_inc (l : List ι) {v : M} (hv : ∀ k ∈ l, i k • v = 0) :
    prodProj e i l • v = v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [prodProj_cons, mul_smul, ih fun k hk => hv k (List.mem_cons_of_mem a hk), proj,
      sub_smul, one_smul, mul_smul, hv a (List.mem_cons_self), smul_zero, sub_zero]

/-- **Quillen, notebook 1982-13, p. 70.** On a module, the image of the product of the
projections `1 - e(ηⱼ) i(Xⱼ)` is the joint kernel of the contractions `i(Xⱼ)`. -/
theorem mem_range_prodProj_iff (h : IsCAR e i) {l : List ι} (hl : l.Nodup) (v : M) :
    (∃ w : M, prodProj e i l • w = v) ↔ ∀ k ∈ l, i k • v = 0 :=
  ⟨by rintro ⟨w, rfl⟩ k hk; rw [← mul_smul, inc_mul_prodProj h hl hk, zero_smul],
    fun hv => ⟨v, prodProj_smul_of_inc l hv⟩⟩

/-! ### The exterior algebra -/

section Exterior

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- Exterior multiplication by `v` on `Λ V`, as an endomorphism. -/
noncomputable def extMul (v : V) : Module.End R (ExteriorAlgebra R V) :=
  LinearMap.mulLeft R (ExteriorAlgebra.ι R v)

/-- Contraction by the linear form `f` on `Λ V`, as an endomorphism. -/
noncomputable def contr (f : Module.Dual R V) : Module.End R (ExteriorAlgebra R V) :=
  CliffordAlgebra.contractLeft (Q := 0) f

theorem contr_extMul_add (f : Module.Dual R V) (v : V) :
    contr f * extMul v + extMul v * contr f = f v • (1 : Module.End R (ExteriorAlgebra R V)) := by
  refine LinearMap.ext fun x => ?_
  change (CliffordAlgebra.contractLeft (Q := 0) f) (ExteriorAlgebra.ι R v * x) +
      ExteriorAlgebra.ι R v * (CliffordAlgebra.contractLeft (Q := 0) f) x = f v • x
  rw [ExteriorAlgebra.ι, CliffordAlgebra.contractLeft_ι_mul]
  abel

/-- **The hypotheses of p. 70 hold on an exterior algebra**: exterior multiplications by vectors
`v j` and contractions by linear forms `f j` with `f k (v j) = δⱼₖ` satisfy `IsCAR`. -/
theorem exterior_isCAR [DecidableEq ι] (v : ι → V) (f : ι → Module.Dual R V)
    (hfv : ∀ j k, f k (v j) = if j = k then 1 else 0) :
    IsCAR (fun j => extMul (R := R) (v j)) (fun j => contr (f j)) where
  inc_sq j := LinearMap.ext fun x => CliffordAlgebra.contractLeft_contractLeft (Q := 0) (d := f j) x
  anticomm_self j := by rw [add_comm, contr_extMul_add]; simp [hfv]
  ext_anticomm j k _ := by
    refine LinearMap.ext fun x => ?_
    change ExteriorAlgebra.ι R (v j) * (ExteriorAlgebra.ι R (v k) * x) =
      -(ExteriorAlgebra.ι R (v k) * (ExteriorAlgebra.ι R (v j) * x))
    rw [← mul_assoc, ← mul_assoc, ← neg_mul, eq_neg_of_add_eq_zero_left
      (ExteriorAlgebra.ι_add_mul_swap (v j) (v k))]
  inc_anticomm j k _ :=
    LinearMap.ext fun x => CliffordAlgebra.contractLeft_comm (Q := 0) (d := f j) (d' := f k) x
  ext_inc_anticomm j k hjk := eq_neg_of_add_eq_zero_right <| by
    simpa only [hfv, hjk, ↓reduceIte, zero_smul] using contr_extMul_add (R := R) (f k) (v j)

end Exterior

end Quillen.Notebook1982_13
