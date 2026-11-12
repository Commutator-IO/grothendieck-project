import Mathlib

/-!
# Quillen, notebook 1971-12, pp. 28, 30: marks along a normal `p`-step

Daniel Quillen's research notebook 1971-12 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201971/1971-12.pdf>) studies,
on pp. 27-33, the marks `φ_H(X) = card X^H` of the Burnside ring modulo a prime `p`; the step
used on pp. 28 and 30 is that the marks of `H` and `H'` agree modulo `p` when `H ⊲ H'` and
`H'/H` is a `p`-group (Dress, 1969).

This file proves the step, for a group `G` (the page's `H'`) acting on a finite set `X`, a normal
subgroup `N` (the page's `H`) with `G ⧸ N` a `p`-group: the quotient acts on `X^N`, its fixed
points there are `X^G`, and the `p`-group fixed-point congruence of mathlib applies.

* `quotientAction`: the action of `G ⧸ N` on `X^N`;
* `fixedPointsQuotientEquiv`: `(X^N)^{G ⧸ N} ≃ X^G`;
* `card_fixedPoints_modEq`: **the statement**, `card X^G ≡ card X^N [MOD p]`.

The companion statement of p. 28, `(G/H)^H ≃ N_G(H)/H`, is mathlib's
`Sylow.fixedPointsMulLeftCosetsEquivQuotient` (for `H` finite).
-/

namespace Quillen.Notebook1971_12Marks

open MulAction

variable {G X : Type*} [Group G] [MulAction G X] (N : Subgroup G) [N.Normal]

theorem smul_mem_fixedPoints (g : G) {x : X} (hx : x ∈ fixedPoints N X) :
    g • x ∈ fixedPoints N X := by
  intro n
  have h : ((⟨g⁻¹ * n * g, Subgroup.Normal.conj_mem' ‹_› n.1 n.2 g⟩ : N) • x) = x := hx _
  change (n : G) • g • x = g • x
  calc (n : G) • g • x = g • ((g⁻¹ * n * g) • x) := by
        rw [smul_smul, smul_smul]; group
    _ = g • x := by rw [show (g⁻¹ * n * g) • x = x from h]

omit [N.Normal] in
theorem smul_eq_of_mem {g g' : G} (h : g⁻¹ * g' ∈ N) {x : X} (hx : x ∈ fixedPoints N X) :
    g' • x = g • x := by
  have : ((⟨g⁻¹ * g', h⟩ : N) • x) = x := hx _
  calc g' • x = g • ((g⁻¹ * g') • x) := by rw [smul_smul]; group
    _ = g • x := by rw [show (g⁻¹ * g') • x = x from this]

/-- The action of `G ⧸ N` on the fixed points of `N`. -/
instance quotientAction : MulAction (G ⧸ N) (fixedPoints N X) where
  smul q x := Quotient.liftOn' q (fun g => ⟨g • x.1, smul_mem_fixedPoints N g x.2⟩)
    (fun g g' h => Subtype.ext (smul_eq_of_mem N (QuotientGroup.leftRel_apply.mp h) x.2).symm)
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul q q' x := by
    induction q using QuotientGroup.induction_on
    induction q' using QuotientGroup.induction_on
    exact Subtype.ext (mul_smul _ _ x.1)

@[simp]
theorem coe_mk_smul (g : G) (x : fixedPoints N X) :
    ((((g : G ⧸ N)) • x : fixedPoints N X) : X) = g • (x : X) := rfl

/-- `(X^N)^{G ⧸ N} ≃ X^G`. -/
def fixedPointsQuotientEquiv :
    fixedPoints (G ⧸ N) (fixedPoints N X) ≃ fixedPoints G X where
  toFun y := ⟨y.1.1, fun g => by
    have := y.2 (g : G ⧸ N)
    exact congrArg Subtype.val this⟩
  invFun x := ⟨⟨x.1, fun n => x.2 n⟩, fun q => by
    induction q using QuotientGroup.induction_on with
    | H g => exact Subtype.ext (x.2 g)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Marks along a normal `p`-step** (notebook 1971-12, pp. 28, 30): for `N ⊲ G` with `G ⧸ N`
a `p`-group and `X` a finite `G`-set, `card X^G ≡ card X^N [MOD p]`. -/
theorem card_fixedPoints_modEq {p : ℕ} [Fact p.Prime] [Finite X] (hp : IsPGroup p (G ⧸ N)) :
    Nat.card (fixedPoints G X) ≡ Nat.card (fixedPoints N X) [MOD p] := by
  rw [← Nat.card_congr (fixedPointsQuotientEquiv N)]
  exact (hp.card_modEq_card_fixedPoints (fixedPoints N X)).symm

end Quillen.Notebook1971_12Marks
