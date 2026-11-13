import Mathlib

/-!
# Quillen, notebook 1982-8, p. 63: the symmetrisation of `1/((z₁ − z₂)⋯(z_n − z₁))` vanishes

Daniel Quillen's research notebook 1982-8 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201982/1982-8.pdf>) needs, on
p. 63, that `tr(Kⁿ) = 0` for `n ≥ 3`; the page reduces it to the vanishing of the symmetrisation
of the cyclic function `φ(z₁, …, z_n) = 1/((z₁ − z₂)(z₂ − z₃)⋯(z_{n−1} − z_n)(z_n − z₁))`, and
argues with the Vandermonde product (`ωφ` would be an antisymmetric polynomial of too small a
degree). The page notes that the symmetry `z_i ↦ z_{n+1−i}` only gives the odd case.

This file proves the vanishing over any field, by another argument (partial fractions and a
telescoping sum, the « U(1) decoupling » of the physicists): inserting a new point `y` in every
gap of a cyclic chain multiplies nothing out, since
`(a − b)/((a − y)(y − b)) = 1/(a − y) − 1/(b − y)` telescopes around the cycle.

* `cyc l`: for `l = [z₁, …, z_n]`, the cyclic product `1/((z₁ − z₂)⋯(z_n − z₁))`;
* `sum_insert_path`: the telescoping identity for all insertions of `y` in a path;
* `sum_permutations_cyc`: **the statement of the page**: for distinct `z₁, …, z_n`, `n ≥ 3`, the
  sum of `cyc` over the `n!` orderings is `0`;
* `sum_permutations_cyc_two`: for `n = 2` the sum is `−2/(z₁ − z₂)²`, not `0`.

The sum over orderings is the sum over `List.permutations`, which lists the `n!` orderings of
a list without repetition.
-/

namespace Quillen.Notebook1982_8

open List

variable {K : Type*} [Field K]

/-- `path a [c₁, …, c_k] b = 1/((a − c₁)(c₁ − c₂)⋯(c_k − b))`. -/
def path : K → List K → K → K
  | a, [], b => (a - b)⁻¹
  | a, c :: l, b => (a - c)⁻¹ * path c l b

/-- The cyclic product: `cyc [z₁, …, z_n] = 1/((z₁ − z₂)⋯(z_{n−1} − z_n)(z_n − z₁))`. -/
def cyc : List K → K
  | [] => 1
  | a :: l => path a l a

theorem sum_flatMap' {α : Type*} (l : List α) (f : α → List K) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  rw [flatMap_def, sum_flatten, map_map]; rfl

/-- **Telescoping.** The insertions of `y` in every position of the path `a, l, b` sum to
`path a l b * (1/(a − y) − 1/(b − y))`. -/
theorem sum_insert_path (y : K) :
    ∀ (l : List K) (a b : K), y ≠ a → y ≠ b → y ∉ l → a ∉ l → (l ++ [b]).Nodup →
      (l = [] → a ≠ b) →
      ((permutations'Aux y l).map (fun m => path a m b)).sum =
        path a l b * ((a - y)⁻¹ - (b - y)⁻¹)
  | [], a, b, hya, hyb, _, _, _, hab => by
    have hab := hab rfl
    have h1 : a - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hya)
    have h2 : y - b ≠ 0 := sub_ne_zero.mpr hyb
    have h3 : a - b ≠ 0 := sub_ne_zero.mpr hab
    have h4 : b - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyb)
    simp only [permutations'Aux, map_cons, map_nil, sum_cons, sum_nil, add_zero, path]
    field_simp
    ring
  | c :: l, a, b, hya, hyb, hyl, hal, hnd, _ => by
    simp only [mem_cons, not_or] at hyl hal
    have hnd' : (l ++ [b]).Nodup := (nodup_cons.mp hnd).2
    have hcl : c ∉ l := fun h => (nodup_cons.mp hnd).1 (mem_append_left _ h)
    have hcb : l = [] → c ≠ b := fun _ h => (nodup_cons.mp hnd).1 (by simp [h])
    have ih := sum_insert_path y l c b hyl.1 hyb hyl.2 hcl hnd' hcb
    have hmap : ((permutations'Aux y l).map (cons c)).map (fun m => path a m b) =
        ((permutations'Aux y l).map (fun m => path c m b)).map ((a - c)⁻¹ * ·) := by
      simp only [map_map]; rfl
    simp only [permutations'Aux, map_cons, sum_cons]
    rw [hmap, sum_map_mul_left, map_id', ih]
    simp only [path]
    have h1 : a - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hya)
    have h2 : y - c ≠ 0 := sub_ne_zero.mpr hyl.1
    have h3 : a - c ≠ 0 := sub_ne_zero.mpr hal.1
    have h4 : c - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyl.1)
    have h5 : b - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyb)
    field_simp
    ring

/-- Inserting `x` in every position of a cycle `c :: l` of length at least two sums to the
cycle with `x` at the head (the first and last insertions give the same cycle, the others
telescope). -/
theorem sum_insert_cyc (x c : K) (l : List K) (hl : l ≠ []) (hnd : (x :: c :: l).Nodup) :
    ((permutations'Aux x (c :: l)).map cyc).sum = cyc (x :: c :: l) := by
  simp only [nodup_cons, mem_cons, not_or] at hnd
  obtain ⟨⟨hxc, hxl⟩, hcl, hl'⟩ := hnd
  have key := sum_insert_path x l c c hxc hxc hxl hcl
    ((perm_append_singleton c l).nodup_iff.mpr (nodup_cons.mpr ⟨hcl, hl'⟩))
    (fun h => absurd h hl)
  have hmap : ((permutations'Aux x l).map (cons c)).map cyc =
      (permutations'Aux x l).map (fun m => path c m c) := by
    simp only [map_map]; rfl
  simp only [permutations'Aux, map_cons, sum_cons]
  rw [hmap, key, sub_self, mul_zero, add_zero]

/-- With `x` fixed at the head, the sum over the orderings of the others vanishes when there
are at least two others. -/
theorem sum_permutations'_cons_cyc (x y : K) (us : List K) (hus : us ≠ [])
    (hnd : (x :: y :: us).Nodup) :
    ((permutations' (y :: us)).map (fun l => cyc (x :: l))).sum = 0 := by
  rw [permutations', map_flatMap, sum_flatMap']
  refine sum_eq_zero fun s hs => ?_
  obtain ⟨l', hl', rfl⟩ := mem_map.mp hs
  have hperm : l' ~ us := mem_permutations'.mp hl'
  simp only [nodup_cons, mem_cons, not_or] at hnd
  obtain ⟨⟨hxy, hxus⟩, hyus, hus'⟩ := hnd
  have hnd' : (l' ++ [x]).Nodup :=
    (perm_append_singleton x l').nodup_iff.mpr
      (nodup_cons.mpr ⟨fun h => hxus (hperm.mem_iff.mp h), hperm.nodup_iff.mpr hus'⟩)
  have key := sum_insert_path y l' x x (Ne.symm hxy) (Ne.symm hxy)
    (fun h => hyus (hperm.mem_iff.mp h)) (fun h => hxus (hperm.mem_iff.mp h)) hnd'
    (fun h => absurd (by subst h; exact hperm.symm.eq_nil) hus)
  rw [sub_self, mul_zero] at key
  simpa only [cyc] using key

/-- **Quillen, notebook 1982-8, p. 63.** For `n ≥ 3` distinct elements `z₁, …, z_n` of a
field, the sum over the `n!` orderings of `1/((z_{σ1} − z_{σ2})⋯(z_{σn} − z_{σ1}))` is zero. -/
theorem sum_permutations_cyc (L : List K) (hL : L.Nodup) (hn : 3 ≤ L.length) :
    (L.permutations.map cyc).sum = 0 := by
  rw [((permutations_perm_permutations' L).map cyc).sum_eq]
  obtain ⟨x, y, c, us, rfl⟩ : ∃ x y c us, L = x :: y :: c :: us := by
    match L, hn with
    | x :: y :: c :: us, _ => exact ⟨x, y, c, us, rfl⟩
  rw [permutations', map_flatMap, sum_flatMap']
  have hsum : ∀ l ∈ permutations' (y :: c :: us),
      ((permutations'Aux x l).map cyc).sum = cyc (x :: l) := by
    intro l hl
    have hperm : l ~ y :: c :: us := mem_permutations'.mp hl
    obtain ⟨d, l'', rfl⟩ : ∃ d l'', l = d :: l'' := by
      match l, hperm.length_eq with
      | d :: l'', _ => exact ⟨d, l'', rfl⟩
    have hl'' : l'' ≠ [] := fun h => by subst h; simpa using hperm.length_eq
    exact sum_insert_cyc x d l'' hl'' ((hperm.cons x).nodup_iff.mpr hL)
  rw [map_congr_left hsum]
  exact sum_permutations'_cons_cyc x y (c :: us) (cons_ne_nil _ _) hL

/-- For `n = 2` the symmetrisation does not vanish: it is `−2/(z₁ − z₂)²`. -/
theorem sum_permutations_cyc_two (a b : K) (hab : a ≠ b) :
    ([a, b].permutations.map cyc).sum = -2 / (a - b) ^ 2 := by
  have h : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  simp [permutations, permutationsAux, permutationsAux.rec, cyc, path]
  field_simp
  ring

end Quillen.Notebook1982_8
