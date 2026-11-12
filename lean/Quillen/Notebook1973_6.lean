import Mathlib

/-!
# Quillen, notebook 1973-6: elementary matrices (p. 30), a Sylow reduction (p. 45), shift equivalences (pp. 64–68)

Daniel Quillen's research notebook 1973-6 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201973/1973-6.pdf>) holds his
notes of Serre's course on trees of the autumn of 1973.

**p. 30.** To show that `SL_3(ℤ)` has property (FA), the page writes down two commutator
relations between the elementary matrices `ē_ij = 1 + e_ij`, for `i, j, k` distinct:
`(ē_ij, ē_jk) = ē_ik` and `(ē_ij, ē_kj) = ē_ik⁻¹`, and places the six matrices of `SL_3` on a
hexagon, each commuting with its neighbours and being the commutator of its two neighbours.
The first relation holds. The second does not as written: `ē_ij` and `ē_kj` commute (they lie
in the same column), so their commutator is `1`. The relation that holds, and that the
hexagon uses, is `(ē_ij, ē_ki) = ē_kj⁻¹`.

With the commutator `(a, b) = a b a⁻¹ b⁻¹` and `transvection i j c = 1 + c e_ij` (whose
inverse is `transvection i j (-c)`), this file proves, over any commutative ring and for any coefficients:

* `transvection_commutator`: `(t_ij(a), t_jk(b)) = t_ik(a b)`, **the first relation** (already
  in this library for units over any ring, `Quillen.Notebook1968_15.commutator_transvectionUnit`;
  restated here for matrices, with its companion);
* `transvection_commute_col`, `transvection_commute_row`: `t_ij(a)` commutes with `t_kj(b)`
  and with `t_ik(b)`; hence `transvection_commutator_col`: `(t_ij(a), t_kj(b)) = 1`, and
  `not_second_relation`: **the second relation of the page fails** over any nontrivial ring;
* `transvection_commutator'`: `(t_ij(a), t_ki(b)) = t_kj(-b a)`, **the corrected relation**;
* `hexagon_commute`, `hexagon_commutator`: the hexagon of the page, for `3 × 3` matrices.

**p. 45.** In the proof of a divisibility theorem for Euler characteristics, the page reduces
to a Sylow subgroup: if `p^k` divides `[G : G_x]` and `H` is a Sylow `p`-subgroup, then `p^k`
divides `[H : H_x]`, because `[G : G_x]` divides `[G : H_x] = [G : H] [H : H_x]` and `[G : H]`
is prime to `p`. `pow_dvd_relIndex_of_sylow` proves it for any subgroup `K` in place of `G_x`.

**pp. 64–68.** On Williams' problem, Quillen considers objects `A` of a category with an
endomorphism `f_A`, and maps `r : A → B` commuting with the endomorphisms that admit `r'` with
`r' r = f_A^m`, `r r' = f_B^m` (« AR-isomorphisms of filtration `≤ m` »). He checks that such an
`r` has filtration `≤ m + 1` as well, that filtrations add under composition, and that two
inverses `r'`, `r''` of filtrations `m`, `n` satisfy `f_A^m r'' = f_A^n r'` (p. 64); that
`f_A = r' r` gives an isomorphism of filtration `≤ 1` with `f_B = r r'` (p. 67); and, for the
examples, that on a finite set `f` is a bijection of `f^n A` for `n` large, and that on a
finitely generated free abelian group `f` is injective on `f^n A` for `n` large (p. 67).
Composition is written `≫` (first `r`, then `r'`), so the page's `r' r` is `r ≫ r'`.

* `iPow f n`: the `n`-th iterate of an endomorphism, `ipow_add`, `comm_ipow`;
* `IsARInv`: the relation « `r'` is an inverse of filtration `m` of `r` »;
* `IsARInv.succ`, `IsARInv.comp`, `IsARInv.unique`: **the three checks of p. 64**;
* `isARInv_one_of_factor`: **p. 67**, `f_A = r ≫ r'` and `f_B = r' ≫ r`;
* `exists_bijOn_range_iterate`: **p. 67, finite sets**;
* `exists_injOn_range_pow`: **p. 67, free abelian groups**, for any Noetherian module.
The theorem of the page (shift equivalence implies strong shift equivalence over `ℤ`) is not
formalised.
-/

namespace Quillen.Notebook1973_6

open Matrix

section Transvections

/-- The commutator of `1 + x` and `1 + y` in a ring, when `x² = y² = y x = x y x = 0`. -/
theorem commutator_formula {A : Type*} [Ring A] {x y : A} (hxx : x * x = 0) (hyy : y * y = 0)
    (hyx : y * x = 0) (hxyx : x * y * x = 0) :
    (1 + x) * (1 + y) * (1 - x) * (1 - y) = 1 + x * y := by
  have h : (1 + x) * (1 + y) * (1 - x) * (1 - y) = 1 + x * y - x * x - y * x - x * y * x - y * y
      - x * y * y + x * x * y + y * x * y + x * y * x * y := by noncomm_ring
  have e1 : x * y * y = 0 := by rw [mul_assoc, hyy, mul_zero]
  have e2 : x * x * y = 0 := by rw [hxx, zero_mul]
  have e3 : y * x * y = 0 := by rw [hyx, zero_mul]
  have e4 : x * y * x * y = 0 := by rw [hxyx, zero_mul]
  rw [h, e4, e1, e2, e3, hxyx, hxx, hyy, hyx]; abel

/-- The commutator of `1 + x` and `1 + y` in a ring, when `x² = y² = x y = y x y = 0`. -/
theorem commutator_formula' {A : Type*} [Ring A] {x y : A} (hxx : x * x = 0) (hyy : y * y = 0)
    (hxy : x * y = 0) (hyxy : y * x * y = 0) :
    (1 + x) * (1 + y) * (1 - x) * (1 - y) = 1 - y * x := by
  have h : (1 + x) * (1 + y) * (1 - x) * (1 - y) = 1 + x * y - x * x - y * x - x * y * x - y * y
      - x * y * y + x * x * y + y * x * y + x * y * x * y := by noncomm_ring
  have e1 : x * y * y = 0 := by rw [hxy, zero_mul]
  have e2 : x * x * y = 0 := by rw [hxx, zero_mul]
  have e4 : x * y * x * y = 0 := by rw [hxy, zero_mul, zero_mul]
  have e5 : x * y * x = 0 := by rw [hxy, zero_mul]
  rw [h, e4, e1, e2, hyxy, e5, hxx, hyy, hxy]; abel

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

omit [Fintype n] in
theorem transvection_neg (i j : n) (a : R) : transvection i j (-a) = 1 - single i j a := by
  rw [transvection, ← single_neg, sub_eq_add_neg]

/-- The inverse of `t_ij(c)` is `t_ij(-c)`. -/
theorem transvection_mul_neg {i j : n} (h : i ≠ j) (c : R) :
    transvection i j c * transvection i j (-c) = 1 := by
  rw [transvection_mul_transvection_same _ _ h, add_neg_cancel, transvection_zero]

/-- **Quillen, notebook 1973-6, p. 30, first relation.** For `i, j, k` distinct,
`(t_ij(a), t_jk(b)) = t_ik(a b)`. -/
theorem transvection_commutator {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    transvection i j a * transvection j k b * transvection i j (-a) * transvection j k (-b) =
      transvection i k (a * b) := by
  rw [transvection_neg, transvection_neg, transvection, transvection, transvection,
    commutator_formula (by simp [hij.symm]) (by simp [hjk.symm]) (by simp [hik.symm])
      (by rw [single_mul_single_same]; simp [hik.symm]), single_mul_single_same]

/-- Two transvections in the same column commute. -/
theorem transvection_commute_col {i j k : n} (hij : i ≠ j) (hkj : k ≠ j) (a b : R) :
    Commute (transvection i j a) (transvection k j b) := by
  have h : single i j a * single k j b = single k j b * single i j a := by
    simp [hij.symm, hkj.symm]
  simp only [Commute, SemiconjBy, transvection, add_mul, mul_add, one_mul, mul_one, h]
  abel

/-- Two transvections in the same row commute. -/
theorem transvection_commute_row {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (a b : R) :
    Commute (transvection i j a) (transvection i k b) := by
  have h : single i j a * single i k b = single i k b * single i j a := by
    simp [hij.symm, hik.symm]
  simp only [Commute, SemiconjBy, transvection, add_mul, mul_add, one_mul, mul_one, h]
  abel

/-- The commutator of two transvections in the same column is `1`. -/
theorem transvection_commutator_col {i j k : n} (hij : i ≠ j) (hkj : k ≠ j) (a b : R) :
    transvection i j a * transvection k j b * transvection i j (-a) * transvection k j (-b) =
      1 := by
  rw [(transvection_commute_col hij hkj a b).eq, mul_assoc (transvection k j b),
    transvection_mul_neg hij, mul_one, transvection_mul_neg hkj]

/-- **The second relation of p. 30 fails as written.** Over a nontrivial ring, for `i, j, k`
distinct, `(ē_ij, ē_kj)` is not `ē_ik⁻¹ = t_ik(-1)`. -/
theorem not_second_relation [Nontrivial R] {i j k : n} (hij : i ≠ j) (hkj : k ≠ j)
    (hik : i ≠ k) :
    transvection i j (1 : R) * transvection k j 1 * transvection i j (-1) *
      transvection k j (-1) ≠ transvection i k (-1) := by
  rw [transvection_commutator_col hij hkj]
  intro h
  have := congrFun (congrFun h i) k
  simp [transvection, one_apply_ne hik] at this

/-- **The corrected second relation.** For `i, j, k` distinct,
`(t_ij(a), t_ki(b)) = t_kj(-b a)`; with `a = b = 1`, `(ē_ij, ē_ki) = ē_kj⁻¹`. -/
theorem transvection_commutator' {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    transvection i j a * transvection k i b * transvection i j (-a) * transvection k i (-b) =
      transvection k j (-(b * a)) := by
  rw [transvection_neg, transvection_neg, transvection, transvection, transvection_neg,
    commutator_formula' (by simp [hij.symm]) (by simp [hik]) (by simp [hjk])
      (by rw [single_mul_single_same]; simp [hjk]), single_mul_single_same]

/-- The six elementary matrices of `SL_3`, in the cyclic order of the hexagon of p. 30:
`ē_12, ē_13, ē_23, ē_21, ē_31, ē_32`. -/
def hexagon (R : Type*) [CommRing R] (m : Fin 6) : Matrix (Fin 3) (Fin 3) R :=
  match m with
  | 0 => transvection 0 1 1
  | 1 => transvection 0 2 1
  | 2 => transvection 1 2 1
  | 3 => transvection 1 0 1
  | 4 => transvection 2 0 1
  | 5 => transvection 2 1 1

/-- **The hexagon of p. 30, first half.** Each matrix commutes with the next one. -/
theorem hexagon_commute (m : Fin 6) : Commute (hexagon R m) (hexagon R (m + 1)) := by
  fin_cases m
  · exact transvection_commute_row (by decide) (by decide) _ _
  · exact transvection_commute_col (by decide) (by decide) _ _
  · exact transvection_commute_row (by decide) (by decide) _ _
  · exact transvection_commute_col (by decide) (by decide) _ _
  · exact transvection_commute_row (by decide) (by decide) _ _
  · exact (transvection_commute_col (by decide) (by decide) _ _).symm

/-- **The hexagon of p. 30, second half.** Each matrix is the commutator of its two
neighbours `ē_{m-1}` and `ē_{m+1}`, in a suitable order. -/
theorem hexagon_commutator (m : Fin 6) :
    (hexagon R m = hexagon R (m + 1) * hexagon R (m - 1) * (hexagon R (m + 1))⁻¹ *
      (hexagon R (m - 1))⁻¹) ∨
    (hexagon R m = hexagon R (m - 1) * hexagon R (m + 1) * (hexagon R (m - 1))⁻¹ *
      (hexagon R (m + 1))⁻¹) := by
  have inv : ∀ {i j : Fin 3}, i ≠ j →
      (transvection i j (1 : R))⁻¹ = transvection i j (-1) := fun h =>
    Matrix.inv_eq_right_inv (transvection_mul_neg h 1)
  fin_cases m <;>
    simp (disch := decide) only [Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd, Fin.reduceSub,
      hexagon, inv, transvection_commutator, mul_one, true_or, or_true]

end Transvections

section Sylow

/-- **Quillen, notebook 1973-6, p. 45.** Let `H` be a Sylow `p`-subgroup of a finite group `G`
and `K` a subgroup. If `p^k` divides `[G : K]`, then `p^k` divides `[H : H ∩ K]`. -/
theorem pow_dvd_relIndex_of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Sylow p G) (K : Subgroup G) {k : ℕ} (hk : p ^ k ∣ K.index) :
    p ^ k ∣ K.relIndex H := by
  have h1 : K.index ∣ (K ⊓ H).index := Subgroup.index_dvd_of_le inf_le_left
  have h2 : (K ⊓ H).index = K.relIndex H * (H : Subgroup G).index := by
    rw [← Subgroup.relIndex_mul_index (inf_le_right : K ⊓ H ≤ H), Subgroup.inf_relIndex_right]
  have hcop : Nat.Coprime (p ^ k) (H : Subgroup G).index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr H.not_dvd_index)
  exact hcop.dvd_of_dvd_mul_right (h2 ▸ hk.trans h1)

end Sylow


section ShiftEquivalence

open CategoryTheory

variable {C : Type*} [Category C]

/-- The `n`-th iterate of an endomorphism, `f ≫ ⋯ ≫ f`. -/
def iPow {A : C} (f : A ⟶ A) : ℕ → (A ⟶ A)
  | 0 => 𝟙 A
  | n + 1 => iPow f n ≫ f

theorem ipow_add {A : C} (f : A ⟶ A) (m n : ℕ) : iPow f (m + n) = iPow f m ≫ iPow f n := by
  induction n with
  | zero => simp [iPow]
  | succ n ih => rw [← add_assoc, iPow, ih, iPow, Category.assoc]

/-- A map commuting with the endomorphisms commutes with their iterates. -/
theorem comm_ipow {A B : C} {fA : A ⟶ A} {fB : B ⟶ B} {r : A ⟶ B} (hr : r ≫ fB = fA ≫ r)
    (n : ℕ) : r ≫ iPow fB n = iPow fA n ≫ r := by
  induction n with
  | zero => simp [iPow]
  | succ n ih => rw [iPow, iPow, ← Category.assoc, ih, Category.assoc, hr, Category.assoc]

/-- `r' : B ⟶ A` is an inverse of filtration `m` of `r : A ⟶ B`, both commuting with the
endomorphisms: `r ≫ r' = f_A^m` and `r' ≫ r = f_B^m`. -/
structure IsARInv {A B : C} (fA : A ⟶ A) (fB : B ⟶ B) (r : A ⟶ B) (r' : B ⟶ A) (m : ℕ) :
    Prop where
  comm : r ≫ fB = fA ≫ r
  comm' : r' ≫ fA = fB ≫ r'
  left : r ≫ r' = iPow fA m
  right : r' ≫ r = iPow fB m

variable {A B D : C} {fA : A ⟶ A} {fB : B ⟶ B} {fD : D ⟶ D}

/-- **p. 64, check 1.** An inverse of filtration `m` gives one of filtration `m + 1`,
`r' ≫ f_A`. -/
theorem IsARInv.succ {r : A ⟶ B} {r' : B ⟶ A} {m : ℕ} (h : IsARInv fA fB r r' m) :
    IsARInv fA fB r (r' ≫ fA) (m + 1) where
  comm := h.comm
  comm' := by simp only [Category.assoc, h.comm']
  left := by rw [← Category.assoc, h.left, iPow]
  right := by rw [Category.assoc, ← h.comm, ← Category.assoc, h.right, iPow]

/-- **p. 64, check 2.** Filtrations add under composition. -/
theorem IsARInv.comp {r : A ⟶ B} {r' : B ⟶ A} {s : B ⟶ D} {s' : D ⟶ B} {m n : ℕ}
    (h : IsARInv fA fB r r' m) (k : IsARInv fB fD s s' n) :
    IsARInv fA fD (r ≫ s) (s' ≫ r') (m + n) where
  comm := by rw [Category.assoc, k.comm, ← Category.assoc, h.comm, Category.assoc]
  comm' := by rw [Category.assoc, h.comm', ← Category.assoc, k.comm', Category.assoc]
  left := by
    calc (r ≫ s) ≫ s' ≫ r' = r ≫ (s ≫ s') ≫ r' := by simp
      _ = (r ≫ iPow fB n) ≫ r' := by rw [k.left, Category.assoc]
      _ = iPow fA n ≫ r ≫ r' := by rw [comm_ipow h.comm, Category.assoc]
      _ = iPow fA (m + n) := by rw [h.left, ← ipow_add, add_comm]
  right := by
    calc (s' ≫ r') ≫ r ≫ s = s' ≫ (r' ≫ r) ≫ s := by simp
      _ = s' ≫ iPow fB m ≫ s := by rw [h.right]
      _ = s' ≫ s ≫ iPow fD m := by rw [comm_ipow k.comm]
      _ = iPow fD (m + n) := by rw [← Category.assoc, k.right, ← ipow_add, add_comm]

/-- **p. 64, check 3.** Two inverses `r'`, `r''` of filtrations `m`, `n` satisfy
`r'' ≫ f_A^m = r' ≫ f_A^n` (the page's `f_A^m r'' = f_A^n r'`). -/
theorem IsARInv.unique {r : A ⟶ B} {r' r'' : B ⟶ A} {m n : ℕ}
    (h : IsARInv fA fB r r' m) (k : IsARInv fA fB r r'' n) :
    r'' ≫ iPow fA m = r' ≫ iPow fA n := by
  calc r'' ≫ iPow fA m = r'' ≫ r ≫ r' := by rw [h.left]
    _ = (r'' ≫ r) ≫ r' := by simp
    _ = iPow fB n ≫ r' := by rw [k.right]
    _ = r' ≫ iPow fA n := (comm_ipow h.comm' n).symm

/-- **p. 67.** If `f_A = r ≫ r'`, then with `f_B = r' ≫ r` the map `r` is an isomorphism of
filtration `≤ 1` with inverse `r'`. -/
theorem isARInv_one_of_factor (r : A ⟶ B) (r' : B ⟶ A) :
    IsARInv (r ≫ r') (r' ≫ r) r r' 1 where
  comm := by simp
  comm' := by simp
  left := by simp [iPow]
  right := by simp [iPow]

end ShiftEquivalence

section Examples

/-- **p. 67, finite sets.** For a map `f` of a finite set to itself, `f` is a bijection of
`range f^[n]` onto itself for some `n`. -/
theorem exists_bijOn_range_iterate {α : Type*} [Finite α] (f : α → α) :
    ∃ n, Set.BijOn f (Set.range f^[n]) (Set.range f^[n]) := by
  have hsub : ∀ n, Set.range f^[n + 1] ⊆ Set.range f^[n] := by
    rintro n _ ⟨x, rfl⟩
    exact ⟨f x, by rw [Function.iterate_succ_apply]⟩
  have himage : ∀ n, f '' Set.range f^[n] = Set.range f^[n + 1] := by
    intro n
    rw [← Set.range_comp, ← Function.iterate_succ']
  have hle : ∀ n, (Set.range f^[n + 1]).ncard ≤ (Set.range f^[n]).ncard := fun n =>
    Set.ncard_le_ncard (hsub n)
  obtain ⟨n, hn⟩ : ∃ n, (Set.range f^[n + 1]).ncard = (Set.range f^[n]).ncard := by
    by_contra! h
    have : ∀ n, (Set.range f^[n]).ncard + n ≤ (Set.range f^[0]).ncard := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => have := lt_of_le_of_ne (hle n) (h n); omega
    have := this ((Set.range f^[0]).ncard + 1)
    omega
  have heq : Set.range f^[n + 1] = Set.range f^[n] :=
    Set.eq_of_subset_of_ncard_le (hsub n) hn.ge
  refine ⟨n, ?_⟩
  have hmaps : Set.MapsTo f (Set.range f^[n]) (Set.range f^[n]) := by
    intro x hx
    rw [← heq, ← himage]
    exact Set.mem_image_of_mem f hx
  rw [← (Set.toFinite _).surjOn_iff_bijOn_of_mapsTo hmaps]
  intro y hy
  rw [← heq, ← himage] at hy
  exact hy

/-- **p. 67, finitely generated free abelian groups**, for any Noetherian module: an
endomorphism `f` is injective on `range f^n` for `n` large, since `ker f^n` stabilises. -/
theorem exists_injOn_range_pow {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [IsNoetherian R M] (f : Module.End R M) :
    ∃ n, Set.InjOn f (LinearMap.range (f ^ n)) := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp f.eventually_disjoint_ker_pow_range_pow
  have hd := hn (n + 1) (by omega)
  refine ⟨n + 1, fun x hx y hy hxy => ?_⟩
  have hz : x - y ∈ LinearMap.ker (f ^ (n + 1)) := by
    rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, map_sub, hxy, sub_self, map_zero]
  have hz' : x - y ∈ LinearMap.range (f ^ (n + 1)) := Submodule.sub_mem _ hx hy
  have := hd.le_bot ⟨hz, hz'⟩
  exact sub_eq_zero.mp this

end Examples

end Quillen.Notebook1973_6
