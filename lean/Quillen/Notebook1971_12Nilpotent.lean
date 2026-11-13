import Quillen.Notebook1971_12Kaloujnine

/-!
# Quillen, notebook 1971-12, p. 21: automorphisms trivial on `G^ab` form a nilpotent group

Daniel Quillen's research notebook 1971-12 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201971/1971-12.pdf>), p. 21:
a corollary of Kaloujnine's theorem `[A_r, A_s] ≤ A_{r+s}` (proved in
`Quillen.Notebook1971_12Kaloujnine`): for a nilpotent group `G`, the automorphisms inducing
the identity on the abelianization form a nilpotent group.

* `isNilpotent_A_one`: for any antitone sequence of normal subgroups with `G_0 = G` and some
  `G_c = 1`, the group `A_1` is nilpotent (its lower central series lies in the `A_{n+1}`);
* `conj_mem_A`: conjugation by an element of `Γ_k` (lower central series, `Γ_0 = G`) lies in
  `A_{k+1}`; hence `commutator_lowerCentralSeries_le`: `⁅Γ_i, Γ_j⁆ ≤ Γ_{i+j+1}`, also a
  consequence of Kaloujnine's theorem;
* `mem_A_one_iff`: for the lower central series, `θ ∈ A_1` iff `θ(g)g⁻¹ ∈ [G, G]` for all `g`,
  i.e. iff `θ` is trivial on `G^ab`;
* `isNilpotent_trivialOnAb`: **the corollary**.
-/

namespace Quillen.Notebook1971_12Nilpotent

open Quillen.Notebook1971_12Kaloujnine
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The lower central series lies in the Kaloujnine filtration: `(A_1)` has its `n`-th lower
central term in `A_{n+1}`. -/
theorem lowerCentralSeries_le (F : ℕ → Subgroup G) [∀ i, (F i).Normal] (n : ℕ) :
    (A F 1).lowerCentralSeries n ≤ A F (n + 1) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    exact (Subgroup.commutator_mono ih le_rfl).trans (commutator_le (F := F) (n + 1) 1)

theorem A_eq_bot (F : ℕ → Subgroup G) (h0 : F 0 = ⊤) {r : ℕ} (hr : F r = ⊥) : A F r = ⊥ := by
  refine eq_bot_iff.2 fun θ hθ => Subgroup.mem_bot.2 ?_
  ext x
  simpa [h0, hr, mul_inv_eq_one] using hθ.2 0 x

/-- **Kaloujnine's corollary**, general form: `A_1` is nilpotent when `G_0 = G` and `G_c = 1`. -/
theorem isNilpotent_A_one (F : ℕ → Subgroup G) [∀ i, (F i).Normal] (hF : Antitone F)
    (h0 : F 0 = ⊤) {c : ℕ} (hc : F c = ⊥) : Group.IsNilpotent (A F 1) := by
  rw [Subgroup.isNilpotent_iff_lowerCentralSeries]
  refine ⟨c, le_bot_iff.mp ((lowerCentralSeries_le F c).trans ?_)⟩
  rw [A_eq_bot F h0 (r := c + 1) (le_bot_iff.mp (hc ▸ hF (Nat.le_succ c)))]

/-- The lower central series, `Γ 0 = G`, `Γ (i+1) = ⁅Γ i, G⁆`. -/
abbrev Γ (G : Type*) [Group G] (i : ℕ) : Subgroup G := (⊤ : Subgroup G).lowerCentralSeries i

instance (i : ℕ) : (Γ G i).Normal := Subgroup.lowerCentralSeries_normal ⊤ i

theorem Γ_succ (i : ℕ) : Γ G (i + 1) = ⁅Γ G i, ⊤⁆ := rfl

theorem conj_mem_A_one (g : G) : MulAut.conj g ∈ A (Γ G) 1 := by
  refine ⟨fun i x => ?_, fun i x hx => ?_⟩
  · simp only [MulAut.conj_apply]
    exact ⟨fun h => (inferInstance : (Γ G i).Normal).conj_mem x h g, fun h => by
      simpa [mul_assoc] using (inferInstance : (Γ G i).Normal).conj_mem _ h g⁻¹⟩
  · simpa [commutatorElement_def, mul_assoc] using
      (Γ G (i + 1)).inv_mem (Subgroup.commutator_mem_commutator hx (Subgroup.mem_top g))

/-- Conjugation by an element of `Γ_k` lies in `A_{k+1}`. -/
theorem conj_mem_A (k : ℕ) : (Γ G k).map MulAut.conj ≤ A (Γ G) (k + 1) := by
  induction k with
  | zero => exact fun _ ⟨g, _, h⟩ => h ▸ conj_mem_A_one g
  | succ k ih =>
    rw [Γ_succ, Subgroup.map_commutator]
    refine (Subgroup.commutator_mono ih ?_).trans (commutator_le (F := Γ G) (k + 1) 1)
    rintro _ ⟨g, -, rfl⟩
    exact conj_mem_A_one g

/-- `⁅Γ_j, Γ_i⁆ ≤ Γ_{i+j+1}` (with `Γ_0 = G`), from Kaloujnine's theorem. -/
theorem commutator_lowerCentralSeries_le (i j : ℕ) : ⁅Γ G j, Γ G i⁆ ≤ Γ G (i + (j + 1)) :=
  Subgroup.commutator_le.2 fun x hx y hy => by
    simpa [commutatorElement_def, mul_assoc] using (conj_mem_A j ⟨x, hx, rfl⟩).2 i y hy

theorem comm_mod {N : Subgroup G} [N.Normal] {z w : G} (h : ⁅z, w⁆ ∈ N) :
    ((z : G ⧸ N) * w = w * z) := by
  have : ((⁅z, w⁆ : G) : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr h
  rw [show ((⁅z, w⁆ : G) : G ⧸ N) = ⁅(z : G ⧸ N), (w : G ⧸ N)⁆ from
    map_commutatorElement (QuotientGroup.mk' N) z w] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

/-- Trivial on `G / [G, G]` implies trivial on every `Γ_i / Γ_{i+1}`. -/
theorem mem_succ_of_trivial {θ : MulAut G} (hθ : ∀ g, θ g * g⁻¹ ∈ Γ G 1) (i : ℕ) :
    ∀ x ∈ Γ G i, θ x * x⁻¹ ∈ Γ G (i + 1) := by
  induction i with
  | zero => exact fun x _ => hθ x
  | succ i ih =>
    intro x hx
    rw [Γ_succ, Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨p, hp, q, -, rfl⟩ := hy
      set N := Γ G (i + 1 + 1)
      have ha := ih p hp
      have hb := hθ q
      set a := θ p * p⁻¹
      set b := θ q * q⁻¹
      have hp' : θ p = a * p := by simp [a]
      have hq' : θ q = b * q := by simp [b]
      rw [map_commutatorElement, hp', hq', ← div_eq_mul_inv, ← QuotientGroup.eq_iff_div_mem]
      -- `a` is central modulo `N`, `b` commutes with `p` and with `⁅p, q⁆` modulo `N`
      have hA : ∀ w : G, (a : G ⧸ N) * w = w * a := fun w =>
        comm_mod (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top w))
      have hBP : (p : G ⧸ N) * b = b * p := by
        apply comm_mod
        have := commutator_lowerCentralSeries_le (G := G) 1 i
          (Subgroup.commutator_mem_commutator hp hb)
        rwa [show 1 + (i + 1) = i + 1 + 1 by omega] at this
      have hBC : ((⁅p, q⁆ : G) : G ⧸ N) * b = b * ⁅p, q⁆ :=
        comm_mod (Subgroup.commutator_mem_commutator
          (Subgroup.commutator_mem_commutator hp (Subgroup.mem_top q)) (Subgroup.mem_top b))
      have hmk : ∀ u v : G, ((u * v : G) : G ⧸ N) = (u : G ⧸ N) * v := fun _ _ => rfl
      have hinv : ∀ u : G, ((u⁻¹ : G) : G ⧸ N) = (u : G ⧸ N)⁻¹ := fun _ => rfl
      have hcomm : ((⁅p, q⁆ : G) : G ⧸ N) = (p : G ⧸ N) * q * (p : G ⧸ N)⁻¹ * (q : G ⧸ N)⁻¹ := by
        simp [commutatorElement_def, hmk, hinv]
      simp only [commutatorElement_def, hmk, hinv, mul_inv_rev]
      rw [hcomm] at hBC
      have hA' : ∀ w : G ⧸ N, (a : G ⧸ N) * w = w * a := fun w => QuotientGroup.induction_on w hA
      calc (a : G ⧸ N) * p * (b * q) * ((p : G ⧸ N)⁻¹ * (a : G ⧸ N)⁻¹) *
            ((q : G ⧸ N)⁻¹ * (b : G ⧸ N)⁻¹)
          = (a : G ⧸ N) * ((p : G ⧸ N) * (b * q) * (p : G ⧸ N)⁻¹) * (a : G ⧸ N)⁻¹ *
            ((q : G ⧸ N)⁻¹ * (b : G ⧸ N)⁻¹) := by group
        _ = ((p : G ⧸ N) * (b * q) * (p : G ⧸ N)⁻¹) * ((q : G ⧸ N)⁻¹ * (b : G ⧸ N)⁻¹) := by
            rw [hA', mul_inv_cancel_right]
        _ = (b : G ⧸ N) * (p * q * (p : G ⧸ N)⁻¹ * (q : G ⧸ N)⁻¹) * (b : G ⧸ N)⁻¹ := by
            rw [← mul_assoc (p : G ⧸ N) b q, hBP]; group
        _ = (p : G ⧸ N) * q * (p : G ⧸ N)⁻¹ * (q : G ⧸ N)⁻¹ := by
            rw [← hBC]; group
    | one => simp
    | mul x y _ _ hx hy =>
      have := (Γ G (i + 1 + 1)).mul_mem hx ((inferInstance : (Γ G (i + 1 + 1)).Normal).conj_mem
        _ hy x)
      rw [map_mul, mul_inv_rev]
      convert this using 1
      group
    | inv x _ hx =>
      have := (Γ G (i + 1 + 1)).inv_mem
        ((inferInstance : (Γ G (i + 1 + 1)).Normal).conj_mem _ hx x⁻¹)
      rw [map_inv, inv_inv]
      convert this using 1
      group

/-- For the lower central series, `θ ∈ A_1` iff `θ` is trivial on `G / [G, G]`. -/
theorem mem_A_one_iff {θ : MulAut G} :
    θ ∈ A (Γ G) 1 ↔ ∀ g, θ g * g⁻¹ ∈ commutator G := by
  refine ⟨fun h g => h.2 0 g (Subgroup.mem_top g), fun h => ?_⟩
  have h' : ∀ g, θ g * g⁻¹ ∈ Γ G 1 := h
  have hinv : ∀ g, θ⁻¹ g * g⁻¹ ∈ Γ G 1 := fun g => by
    convert (Γ G 1).inv_mem (h' (θ⁻¹ g)) using 1
    rw [show θ (θ⁻¹ g) = g by simp]; group
  have hle : ∀ i, Γ G (i + 1) ≤ Γ G i := fun i =>
    Subgroup.lowerCentralSeries_antitone ⊤ (Nat.le_succ i)
  refine ⟨fun i x => ⟨fun hx => ?_, fun hx => ?_⟩, fun i x hx => mem_succ_of_trivial h' i x hx⟩
  · simpa using (Γ G i).mul_mem (hle i (mem_succ_of_trivial h' i x hx)) hx
  · simpa using (Γ G i).mul_mem (hle i (mem_succ_of_trivial hinv i _ hx)) hx

/-- **Notebook 1971-12, p. 21**: for a nilpotent group, the automorphisms trivial on the
abelianization (`θ(g)g⁻¹ ∈ [G, G]` for all `g`) form a nilpotent group. -/
theorem isNilpotent_trivialOnAb [Group.IsNilpotent G] :
    Group.IsNilpotent (A (Γ G) 1) ∧ ∀ θ : MulAut G, θ ∈ A (Γ G) 1 ↔ ∀ g, θ g * g⁻¹ ∈ commutator G := by
  obtain ⟨c, hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp (inferInstance : Group.IsNilpotent G)
  exact ⟨isNilpotent_A_one (Γ G) (Subgroup.lowerCentralSeries_antitone ⊤) rfl hc,
    fun _ => mem_A_one_iff⟩

end Quillen.Notebook1971_12Nilpotent
