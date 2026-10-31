import Grothendieck.Folder80Maps3

/-!
# Folder 80, pages 39–54: the sign algebra behind the three-pencil case

Finding `80-skeleton-full-faithfulness`. `Folder80Maps3` proves page 54 for every bigon-free
arrangement in which each triangle has a fourth line through none of its vertices. What it
leaves is the case where every other line passes through a vertex of some triangle: the
arrangement lies in three pencils, the complete quadrangle `III₆` being the first example.

This file closes that case by another route, through chirotopes. A chirotope is written
additively, `χ i j l : ZMod 2` being the sign bit of the triple (`0` for `+`, `1` for `-`),
defined on the *bases*, the triples of pairwise distinct lines with no common point. An
isomorphism of labelled skeleta gives, along each line `i`, the same points in the same cyclic
order up to reversal; by the representation theorem in rank 2 the two contractions at `i` then
differ by a sign `s i` and a reorientation `ε i`:
`χ' (σ i) (σ j) (σ l) = χ i j l + s i + ε i j + ε i l` (`LocallyEquivalent`).

**What is proved.**
* `eq_zero_of_fourth`: if a sign function is, at each line `i`, of the form
  `ψ i j l = δ i j + δ i l`, it vanishes on a triangle that has a fourth line through none of
  its vertices (the four triples of four lines in general position have equal values, and their
  sum is zero).
* `eq_zero`: in a bigon-free incidence structure where two lines meet once, it vanishes on every
  triangle. A triangle `a, b, c` without a fourth line is split at `a` by a line `x` through
  `b ∩ c`, which exists because `a` carries a third vertex; the triangles `a, b, x` and `a, x, c`
  have fourth lines through `a ∩ c` and `a ∩ b`, which exist because `b` and `c` carry third
  vertices.
* `reorientation_of_locallyEquivalent`: **steps 2–4.** If the two chirotopes are locally
  equivalent along every line, `χ' ∘ σ` is the reorientation of `χ` by `s`.

**Not formalised.** The two representation theorems at the ends: the rank-2 one that turns a
skeleton isomorphism into `LocallyEquivalent`, and Folkman–Lawrence, which turns the
reorientation into a homeomorphism of the projective plane.
-/

namespace Grothendieck.Folder80Signs

open Grothendieck.Folder80Maps3 (BigonFree)

variable {P L : Type*} (on : P → L → Prop)

/-- Three pairwise distinct lines without a common point. -/
def Basis (i j l : L) : Prop :=
  i ≠ j ∧ i ≠ l ∧ j ≠ l ∧ ¬∃ p, on p i ∧ on p j ∧ on p l

/-- Two distinct lines meet in exactly one point, and every point is on two lines. -/
structure Incidence : Prop where
  meet : ∀ l l' : L, l ≠ l' → ∃ p, on p l ∧ on p l'
  unique : ∀ {l l' : L} {p q : P}, l ≠ l' → on p l → on p l' → on q l → on q l' → p = q
  two : ∀ {p : P} {l : L}, on p l → ∃ l', l' ≠ l ∧ on p l'

variable {on}

/-- A sign function that is, at each line `i`, the coboundary of some `δ i` on the other
lines. -/
def LocalForm (ψ : L → L → L → ZMod 2) : Prop :=
  ∃ δ : L → L → ZMod 2, ∀ i j l, Basis on i j l → ψ i j l = δ i j + δ i l

theorem Basis.swap12 {i j l : L} (h : Basis on i j l) : Basis on j i l := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1.symm, h3, h2, fun ⟨p, a, b, c⟩ => h4 ⟨p, b, a, c⟩⟩

theorem Basis.swap23 {i j l : L} (h : Basis on i j l) : Basis on i l j := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h2, h1, h3.symm, fun ⟨p, a, b, c⟩ => h4 ⟨p, a, c, b⟩⟩

/-- A line avoiding a common point of two lines makes a basis with them. -/
theorem basis_of_avoid (hI : Incidence on) {i j m : L} {p : P} (hij : i ≠ j) (pi : on p i)
    (pj : on p j) (hm : ¬on p m) (mi : m ≠ i) (mj : m ≠ j) : Basis on i j m :=
  ⟨hij, mi.symm, mj.symm, fun ⟨_, qi, qj, qm⟩ => hm (hI.unique hij pi pj qi qj ▸ qm)⟩

section Algebra

variable {ψ : L → L → L → ZMod 2}
  (s12 : ∀ i j l, ψ j i l = ψ i j l) (s23 : ∀ i j l, ψ i l j = ψ i j l)
include s12 s23

/-- **Step 3.** Four lines in general position: the triangle `i, j, l` gets the value `0`. The
three relations at `i`, `j` and `l` add up to `ψ i j l`, everything else appearing twice. -/
theorem eq_zero_of_fourth (hψ : LocalForm (on := on) ψ) {i j l m : L} (h : Basis on i j l)
    (hm1 : Basis on i j m) (hm2 : Basis on i l m) (hm3 : Basis on j l m) : ψ i j l = 0 := by
  obtain ⟨δ, hδ⟩ := hψ
  have ei := hδ i j l h
  have ei' := hδ i j m hm1
  have ei'' := hδ i l m hm2
  have ej : ψ i j l = δ j i + δ j l := by rw [← s12]; exact hδ j i l h.swap12
  have ej' : ψ i j m = δ j i + δ j m := by rw [← s12]; exact hδ j i m hm1.swap12
  have ej'' := hδ j l m hm3
  have el : ψ i j l = δ l i + δ l j := by
    rw [← s23 i j l, ← s12 i l j]; exact hδ l i j h.swap23.swap12
  have el' : ψ i l m = δ l i + δ l m := by rw [← s12]; exact hδ l i m hm2.swap12
  have el'' : ψ j l m = δ l j + δ l m := by rw [← s12]; exact hδ l j m hm3.swap12
  have two : (2 : ZMod 2) = 0 := rfl
  linear_combination ei + ei' + ei'' + ej + ej' + ej'' + el + el' + el'' +
    (-ψ i j l - ψ i j m - ψ i l m - ψ j l m + δ i j + δ i l + δ i m + δ j i + δ j l + δ j m +
      δ l i + δ l j + δ l m) * two

/-- **Steps 3 and 4.** In a bigon-free incidence structure, a sign function of local form
vanishes on every basis. -/
theorem eq_zero (hI : Incidence on) (hbf : BigonFree on) (hψ : LocalForm (on := on) ψ)
    {a b c : L} (h : Basis on a b c) : ψ a b c = 0 := by
  have key : ∀ {i j l m : L}, Basis on i j l → Basis on i j m → Basis on i l m →
      Basis on j l m → ψ i j l = 0 := fun h1 h2 h3 h4 => eq_zero_of_fourth s12 s23 hψ h1 h2 h3 h4
  have hB := h
  obtain ⟨hab, hac, hbc, hno⟩ := h
  -- a triangle with a fourth line through none of its vertices: step 3
  by_cases hfourth : ∃ m, Basis on a b m ∧ Basis on a c m ∧ Basis on b c m
  · obtain ⟨m, h1, h2, h3⟩ := hfourth
    exact key hB h1 h2 h3
  push Not at hfourth
  obtain ⟨δ, hδ⟩ := hψ
  obtain ⟨P1, P1b, P1c⟩ := hI.meet b c hbc
  obtain ⟨P2, P2a, P2c⟩ := hI.meet a c hac
  obtain ⟨P3, P3a, P3b⟩ := hI.meet a b hab
  -- with no fourth line, every line other than `a, b, c` passes through a vertex
  have through : ∀ m, m ≠ a → m ≠ b → m ≠ c → on P1 m ∨ on P2 m ∨ on P3 m := by
    intro m ma mb mc
    by_contra hcon
    push Not at hcon
    exact hfourth m (basis_of_avoid hI hab P3a P3b hcon.2.2 ma mb)
      (basis_of_avoid hI hac P2a P2c hcon.2.1 ma mc) (basis_of_avoid hI hbc P1b P1c hcon.1 mb mc)
  -- on a line `l`, a vertex other than two given ones
  have third : ∀ (l : L) (u v : P), ∃ q, on q l ∧ q ≠ u ∧ q ≠ v := by
    intro l u v
    obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := hbf l
    by_cases h1 : p ≠ u ∧ p ≠ v
    · exact ⟨p, hp, h1⟩
    by_cases h2 : q ≠ u ∧ q ≠ v
    · exact ⟨q, hq, h2⟩
    refine ⟨r, hr, ?_, ?_⟩ <;> rintro rfl <;> grind
  -- a second line through a new point `Q` of `a`, `R` of `b`, `S` of `c`
  obtain ⟨Q, Qa, Q2, Q3⟩ := third a P2 P3
  obtain ⟨R, Rb, R1, R3⟩ := third b P1 P3
  obtain ⟨S, Sc, S1, S2⟩ := third c P1 P2
  obtain ⟨x, xa, Qx⟩ := hI.two Qa
  obtain ⟨y, yb, Ry⟩ := hI.two Rb
  obtain ⟨z, zc, Sz⟩ := hI.two Sc
  -- a line meets `a`, `b`, `c` only once
  have xP2 : ¬on P2 x := fun e => Q2 (hI.unique xa.symm Qa Qx P2a e)
  have xP3 : ¬on P3 x := fun e => Q3 (hI.unique xa.symm Qa Qx P3a e)
  have yP1 : ¬on P1 y := fun e => R1 (hI.unique yb.symm Rb Ry P1b e)
  have yP3 : ¬on P3 y := fun e => R3 (hI.unique yb.symm Rb Ry P3b e)
  have zP1 : ¬on P1 z := fun e => S1 (hI.unique zc.symm Sc Sz P1c e)
  have zP2 : ¬on P2 z := fun e => S2 (hI.unique zc.symm Sc Sz P2c e)
  have xb : x ≠ b := fun e => xP3 (e ▸ P3b)
  have xc : x ≠ c := fun e => xP2 (e ▸ P2c)
  have ya : y ≠ a := fun e => yP3 (e ▸ P3a)
  have yc : y ≠ c := fun e => yP1 (e ▸ P1c)
  have za : z ≠ a := fun e => zP2 (e ▸ P2a)
  have zb : z ≠ b := fun e => zP1 (e ▸ P1b)
  -- so `x` passes through `P1`, `y` through `P2`, `z` through `P3`
  have x1 : on P1 x := (through x xa xb xc).resolve_right (not_or.2 ⟨xP2, xP3⟩)
  have y2 : on P2 y := ((through y ya yb yc).resolve_left yP1).resolve_right yP3
  have z3 : on P3 z := ((through z za zb zc).resolve_left zP1).resolve_left zP2
  have yQ : ¬on Q y := fun e => Q2 (hI.unique ya.symm Qa e P2a y2)
  have zQ : ¬on Q z := fun e => Q3 (hI.unique za.symm Qa e P3a z3)
  have xy : y ≠ x := fun e => xP2 (e ▸ y2)
  have xz : z ≠ x := fun e => xP3 (e ▸ z3)
  -- the triangle `a, b, x`, with fourth line `y`
  have Babx := basis_of_avoid hI hab P3a P3b xP3 xa xb
  have h1 : ψ a b x = 0 := key Babx (basis_of_avoid hI hab P3a P3b yP3 ya yb)
    (basis_of_avoid hI xa.symm Qa Qx yQ ya xy) (basis_of_avoid hI xb.symm P1b x1 yP1 yb xy)
  -- the triangle `a, x, c`, with fourth line `z`
  have Baxc := (basis_of_avoid hI hac P2a P2c xP2 xa xc).swap23
  have h2 : ψ a x c = 0 := key Baxc (basis_of_avoid hI xa.symm Qa Qx zQ za xz)
    (basis_of_avoid hI hac P2a P2c zP2 za zc) (basis_of_avoid hI xc x1 P1c zP1 xz zc)
  -- at `a`: `ψ a b c = ψ a b x + ψ a x c`
  have e1 := hδ a b c hB
  have e2 := hδ a b x Babx
  have e3 := hδ a x c Baxc
  have two : (2 : ZMod 2) = 0 := rfl
  linear_combination e1 - e2 - e3 + h1 + h2 - δ a x * two

end Algebra

/-- Two chirotopes, as sign bits on the bases, are *locally equivalent* along every line when the
contractions at `i` and at `σ i` differ by a global sign `s i` and a reorientation `ε i`: what an
isomorphism of labelled skeleta gives, by the representation theorem in rank 2. -/
def LocallyEquivalent (χ χ' : L → L → L → ZMod 2) (σ : L → L) : Prop :=
  ∃ s : L → ZMod 2, ∃ ε : L → L → ZMod 2,
    ∀ i j l, Basis on i j l → χ' (σ i) (σ j) (σ l) = χ i j l + s i + ε i j + ε i l

/-- **Steps 2–4.** In a bigon-free incidence structure, two alternating chirotopes that are
locally equivalent along every line differ by a reorientation: `χ' ∘ σ` is `χ` with the lines in
`r` reversed. -/
theorem reorientation_of_locallyEquivalent (hI : Incidence on) (hbf : BigonFree on)
    {χ χ' : L → L → L → ZMod 2} {σ : L → L}
    (a12 : ∀ i j l, χ j i l = χ i j l + 1) (a23 : ∀ i j l, χ i l j = χ i j l + 1)
    (a12' : ∀ i j l, χ' j i l = χ' i j l + 1) (a23' : ∀ i j l, χ' i l j = χ' i j l + 1)
    (H : LocallyEquivalent (on := on) χ χ' σ) :
    ∃ r : L → ZMod 2, ∀ i j l, Basis on i j l →
      χ' (σ i) (σ j) (σ l) = χ i j l + r i + r j + r l := by
  obtain ⟨s, ε, hε⟩ := H
  refine ⟨s, fun i j l h => ?_⟩
  -- step 2: `ψ` is symmetric, and of local form with `δ i j = ε i j + s j`
  set ψ : L → L → L → ZMod 2 := fun i j l => χ' (σ i) (σ j) (σ l) + χ i j l + s i + s j + s l
  have two : (2 : ZMod 2) = 0 := rfl
  have s12 : ∀ i j l, ψ j i l = ψ i j l := fun i j l => by
    simp only [ψ]; rw [a12, a12']; linear_combination two
  have s23 : ∀ i j l, ψ i l j = ψ i j l := fun i j l => by
    simp only [ψ]; rw [a23, a23']; linear_combination two
  have hloc : LocalForm (on := on) ψ := ⟨fun i j => ε i j + s j, fun i j l h => by
    simp only [ψ]; rw [hε i j l h]; linear_combination (χ i j l + s i) * two⟩
  have h0 := eq_zero s12 s23 hI hbf hloc h
  simp only [ψ] at h0
  linear_combination h0 - (χ i j l + s i + s j + s l) * two

end Grothendieck.Folder80Signs
