import Mathlib

/-!
# Folder 148, pages 55–58: gluing two circles with `r` marked points is unique

Pages 49–60 of folder 148 (transcription `transcripts/148/batch-03.fr.tex`, modernised reading
`transcripts/148/148.modern.tex`, « D) Recollement ») define the multimarked Teichmüller
groupoid: each cutting circle `a` carries `r(a)` marked points forming a torsor `R_a` under
`ℤ/r(a)`, and two circles `a`, `a'` with `r(a) = r(a')` are glued along an orientation-reversing
homeomorphism once an anti-isomorphism of torsors `R_a → R_{a'}` is given. The page states that the
gluing is then « bien déterminé »; the reading justifies it: the orientation-reversing
homeomorphisms realising a given anti-isomorphism form a non-empty contractible space.

What is modelled. A circle with `r` marked points is `ℝ/ℤ` (oriented by `ℝ`) with the lifted
marked points `p : ℤ → ℝ`, strictly increasing with `p (k + r) = p k + 1` (`Marking r`); the
torsor `R_a` is `ℤ/r` acting by `k ↦ k + 1` (next point along the orientation), so that an
anti-isomorphism `ℤ/r → ℤ/r` is `k ↦ c - k` (`antiIso_eq`). An orientation-reversing
homeomorphism of circles is described by its lifts: continuous strictly antitone `F : ℝ → ℝ`
with `F (x + 1) = F x - 1`; two lifts of the same map differ by an integer, and the lift is
normalised by asking `F (p k) = q (c - k)` for all `k` (`c ∈ ℤ` lifting the anti-isomorphism).
The space `gluings P Q c ⊆ C(ℝ, ℝ)` carries the compact-open topology.
* `gluings_nonempty`: the space is non-empty, for arbitrary positions of the marked points
  (piecewise-linear interpolation `Marking.interpHomeomorph`);
* `convex_gluings`, `contractibleSpace_gluings`, `isPathConnected_gluings`: it is convex, hence
  contractible (straight-line homotopy) and path-connected, so two gluings are isotopic through
  gluings realising the same anti-isomorphism;
* `toHomeomorph`: each element is a homeomorphism of `ℝ`;
* `exists_antiIso`: an equivariant orientation-reversing homeomorphism mapping the marked points
  of `a` onto those of `a'` induces an anti-isomorphism `k ↦ c - k`, so the spaces `gluings P Q c`
  exhaust the gluings respecting the markings.

Not formalised: the identification of the space of lifts with a space of homeomorphisms of the
circle `AddCircle 1`, the case `r = 0` (where `Marking 0` is empty; the reading says the space
then has the homotopy type of a circle, the Dehn twist ambiguity), and the groupoid itself.
-/

open Set Filter Topology

namespace Grothendieck.Folder148

/-! ### Anti-isomorphisms of `ℤ/r`-torsors -/

/-- An anti-isomorphism of the torsor `ℤ/r` (a map with `u (x + 1) = u x - 1`) is `x ↦ u 0 - x`. -/
theorem antiIso_eq {r : ℕ} (u : ZMod r → ZMod r) (hu : ∀ x, u (x + 1) = u x - 1) (x : ZMod r) :
    u x = u 0 - x := by
  have key : ∀ n : ℕ, u n = u 0 - n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => push_cast; rw [hu, ih]; ring
  have hx : ((x.cast : ℤ) : ZMod r) = x := ZMod.intCast_zmod_cast x
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg (x.cast : ℤ)
  · rw [← hx, hn]; push_cast; exact key n
  · -- `x = -n`; use `u (y + n) = u y - n` backwards
    have key' : ∀ (m : ℕ) (y : ZMod r), u (y + m) = u y - m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => intro y; push_cast; rw [← add_assoc, hu, ih]; ring
    have := key' n (-(n : ZMod r))
    rw [neg_add_cancel] at this
    rw [← hx, hn]; push_cast
    linear_combination -this

/-! ### Circles with `r` marked points -/

/-- A circle `ℝ/ℤ` with `r` marked points, given by its lifted marked points: a strictly
increasing `pt : ℤ → ℝ` with `pt (k + r) = pt k + 1`. The marked point `pt k` has label
`k mod r` in the torsor `ℤ/r`. -/
structure Marking (r : ℕ) where
  /-- The lifted marked points. -/
  pt : ℤ → ℝ
  strictMono : StrictMono pt
  periodic : ∀ k, pt (k + r) = pt k + 1

namespace Marking

variable {r : ℕ} (P : Marking r)

/-- The standard marking by the points `k / r`. -/
noncomputable def std (r : ℕ) (hr : 0 < r) : Marking r where
  pt k := k / r
  strictMono := fun a b h => by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    exact div_lt_div_of_pos_right (by exact_mod_cast h) this
  periodic k := by
    have : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast; field_simp

theorem pt_add_mul (k m : ℤ) : P.pt (k + r * m) = P.pt k + m := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
    have := P.periodic (k + r * m)
    rw [show k + r * ((m : ℤ) + 1) = k + r * m + r by ring, this, ih]; push_cast; ring
  | pred m ih =>
    have := P.periodic (k + r * (-(m : ℤ) - 1))
    rw [show k + r * (-(m : ℤ) - 1) + r = k + r * (-(m : ℤ)) by ring, ih] at this
    push_cast at this ⊢; linarith

theorem r_pos (P : Marking r) : 0 < r := by
  rcases Nat.eq_zero_or_pos r with h | h
  · have := P.periodic 0; subst h; simp at this
  · exact h

/-- The piecewise-linear interpolation of the marked points: `interp k = pt k`, affine on each
`[k, k + 1]`. -/
noncomputable def interp (y : ℝ) : ℝ :=
  P.pt ⌊y⌋ + Int.fract y * (P.pt (⌊y⌋ + 1) - P.pt ⌊y⌋)

theorem interp_intCast (k : ℤ) : P.interp k = P.pt k := by
  simp [interp]

theorem interp_add (y : ℝ) : P.interp (y + r) = P.interp y + 1 := by
  simp only [interp, Int.floor_add_natCast, Int.fract_add_natCast]
  rw [P.periodic, show ⌊y⌋ + (r : ℤ) + 1 = ⌊y⌋ + 1 + r by ring, P.periodic]; ring

theorem interp_eqOn (n : ℤ) :
    EqOn P.interp (fun y => P.pt n + (y - n) * (P.pt (n + 1) - P.pt n)) (Icc (n : ℝ) (n + 1)) := by
  intro y ⟨h1, h2⟩
  rcases h2.lt_or_eq with h2 | h2
  · have hf : ⌊y⌋ = n := Int.floor_eq_iff.2 ⟨h1, h2⟩
    simp only [interp, Int.fract, hf]
  · subst h2
    have := P.interp_intCast (n + 1)
    push_cast at this
    rw [this]; ring

theorem continuous_interp : Continuous P.interp := by
  have hlf : LocallyFinite (fun n : ℤ => Icc (n : ℝ) (n + 1)) :=
    locallyFinite_Icc_of_tendsto tendsto_intCast_atTop_atTop
      (tendsto_atBot_add_const_right _ 1 (tendsto_intCast_atBot_iff.2 tendsto_id))
  refine hlf.continuous ?_ (fun _ => isClosed_Icc) fun n => ?_
  · refine eq_univ_of_forall fun y => mem_iUnion.2 ⟨⌊y⌋, Int.floor_le y, (Int.lt_floor_add_one y).le⟩
  · exact (ContinuousOn.congr (by fun_prop) (P.interp_eqOn n))

theorem strictMono_interp : StrictMono P.interp := by
  intro y z hyz
  have hΔ : ∀ k : ℤ, 0 < P.pt (k + 1) - P.pt k := fun k => sub_pos.2 (P.strictMono (by omega))
  rcases (Int.floor_mono hyz.le).lt_or_eq with h | h
  · have h1 : P.interp y < P.pt (⌊y⌋ + 1) := by
      have := mul_lt_mul_of_pos_right (Int.fract_lt_one y) (hΔ ⌊y⌋)
      simp only [interp]; linarith
    have h2 : P.pt (⌊y⌋ + 1) ≤ P.pt ⌊z⌋ := P.strictMono.monotone (by omega)
    have h3 : P.pt ⌊z⌋ ≤ P.interp z := by
      have := mul_nonneg (Int.fract_nonneg z) (hΔ ⌊z⌋).le
      simp only [interp]; linarith
    linarith
  · have hf : Int.fract y < Int.fract z := by
      simp only [Int.fract, h]; linarith
    simp only [interp, h]
    have := mul_lt_mul_of_pos_right hf (hΔ ⌊z⌋)
    linarith

theorem interp_mul (m : ℤ) : P.interp ((r : ℝ) * m) = P.pt 0 + m := by
  have := P.interp_intCast (r * m)
  push_cast at this
  rw [this, show (r : ℤ) * m = 0 + r * m by ring, P.pt_add_mul]

theorem surjective_interp : Function.Surjective P.interp := by
  intro t
  have hr : (0 : ℝ) < r := by exact_mod_cast P.r_pos
  set a := (r : ℝ) * ⌊t - P.pt 0⌋
  set b := (r : ℝ) * ⌈t - P.pt 0⌉
  have hab : a ≤ b := mul_le_mul_of_nonneg_left (by exact_mod_cast Int.floor_le_ceil _) hr.le
  have := intermediate_value_Icc hab P.continuous_interp.continuousOn
  have ht : t ∈ Icc (P.interp a) (P.interp b) := by
    rw [P.interp_mul, P.interp_mul]
    exact ⟨by linarith [Int.floor_le (t - P.pt 0)], by linarith [Int.le_ceil (t - P.pt 0)]⟩
  obtain ⟨y, -, hy⟩ := this ht
  exact ⟨y, hy⟩

/-- The interpolation as an orientation-preserving homeomorphism of `ℝ`. -/
noncomputable def interpHomeomorph : ℝ ≃ₜ ℝ :=
  (P.strictMono_interp.orderIsoOfSurjective P.interp P.surjective_interp).toHomeomorph

@[simp] theorem interpHomeomorph_apply (y : ℝ) : P.interpHomeomorph y = P.interp y := rfl

theorem interpHomeomorph_symm_add (x : ℝ) :
    P.interpHomeomorph.symm (x + 1) = P.interpHomeomorph.symm x + r := by
  apply P.interpHomeomorph.injective
  rw [Homeomorph.apply_symm_apply, interpHomeomorph_apply, interp_add, ← interpHomeomorph_apply,
    Homeomorph.apply_symm_apply]

theorem interpHomeomorph_symm_strictMono : StrictMono P.interpHomeomorph.symm :=
  (P.strictMono_interp.orderIsoOfSurjective P.interp P.surjective_interp).symm.strictMono

theorem interpHomeomorph_symm_pt (k : ℤ) : P.interpHomeomorph.symm (P.pt k) = k := by
  apply P.interpHomeomorph.injective
  rw [Homeomorph.apply_symm_apply, interpHomeomorph_apply, interp_intCast]

end Marking

/-! ### The space of gluings -/

variable {r : ℕ}

/-- The gluings of `a` (marking `P`) to `a'` (marking `Q`) realising the anti-isomorphism
`k ↦ c - k` of `ℤ/r`-torsors: lifts `F` of orientation-reversing homeomorphisms of the circle
(`F` continuous, strictly antitone, `F (x + 1) = F x - 1`), normalised by `F (p k) = q (c - k)`. -/
def gluings (P Q : Marking r) (c : ℤ) : Set C(ℝ, ℝ) :=
  {F | StrictAnti F ∧ (∀ x, F (x + 1) = F x - 1) ∧ ∀ k, F (P.pt k) = Q.pt (c - k)}

/-- The space of gluings is non-empty: `F = interp_Q ∘ (c - ·) ∘ interp_P⁻¹`. -/
theorem gluings_nonempty (P Q : Marking r) (c : ℤ) : (gluings P Q c).Nonempty := by
  refine ⟨⟨fun x => Q.interp (c - P.interpHomeomorph.symm x), by
    exact Q.continuous_interp.comp (continuous_const.sub P.interpHomeomorph.symm.continuous)⟩,
    ?_, ?_, ?_⟩
  · intro x y hxy
    simp only [ContinuousMap.coe_mk]
    apply Q.strictMono_interp
    have := P.interpHomeomorph_symm_strictMono hxy
    linarith
  · intro x
    simp only [ContinuousMap.coe_mk]
    rw [Marking.interpHomeomorph_symm_add, show (c : ℝ) - (P.interpHomeomorph.symm x + r) =
      (c - P.interpHomeomorph.symm x - r) by ring]
    have := Q.interp_add (c - P.interpHomeomorph.symm x - r)
    rw [sub_add_cancel] at this
    linarith
  · intro k
    simp only [ContinuousMap.coe_mk]
    rw [Marking.interpHomeomorph_symm_pt, ← Q.interp_intCast]; push_cast; rfl

/-- The space of gluings is convex in `C(ℝ, ℝ)`. -/
theorem convex_gluings (P Q : Marking r) (c : ℤ) : Convex ℝ (gluings P Q c) := by
  intro F ⟨hF1, hF2, hF3⟩ G ⟨hG1, hG2, hG3⟩ a b ha hb hab
  refine ⟨fun x y hxy => ?_, fun x => ?_, fun k => ?_⟩
  · simp only [ContinuousMap.coe_add, ContinuousMap.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    have h1 := hF1 hxy
    have h2 := hG1 hxy
    rcases ha.lt_or_eq with ha | ha
    · nlinarith [mul_le_mul_of_nonneg_left h2.le hb]
    · subst ha; simp at hab; subst hab; simpa using h2
  · simp only [ContinuousMap.coe_add, ContinuousMap.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hF2, hG2]
    linear_combination -hab
  · simp only [ContinuousMap.coe_add, ContinuousMap.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hF3, hG3]
    linear_combination (Q.pt (c - k)) * hab

theorem gluings_add_intCast {P Q : Marking r} {c : ℤ} {F : C(ℝ, ℝ)} (hF : F ∈ gluings P Q c)
    (x : ℝ) (m : ℤ) : F (x + m) = F x - m := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih => push_cast at ih ⊢; rw [← add_assoc, hF.2.1, ih]; ring
  | pred m ih =>
    have := hF.2.1 (x + (-(m : ℝ) - 1))
    rw [show x + (-(m : ℝ) - 1) + 1 = x + ((-(m : ℤ) : ℤ) : ℝ) by push_cast; ring, ih] at this
    push_cast at this ⊢; linarith

theorem surjective_of_mem_gluings {P Q : Marking r} {c : ℤ} {F : C(ℝ, ℝ)}
    (hF : F ∈ gluings P Q c) : Function.Surjective F := by
  intro t
  set a : ℝ := ((⌊F 0 - t⌋ : ℤ) : ℝ)
  set b : ℝ := ((⌈F 0 - t⌉ : ℤ) : ℝ)
  have hab : a ≤ b := by simp only [a, b]; exact_mod_cast Int.floor_le_ceil _
  have hFa : F a = F 0 - a := by rw [← gluings_add_intCast hF 0, zero_add]
  have hFb : F b = F 0 - b := by rw [← gluings_add_intCast hF 0, zero_add]
  have ht : t ∈ Icc (F b) (F a) := by
    rw [hFa, hFb]
    exact ⟨by linarith [Int.le_ceil (F 0 - t)], by linarith [Int.floor_le (F 0 - t)]⟩
  obtain ⟨y, -, hy⟩ := intermediate_value_Icc' hab F.continuous.continuousOn ht
  exact ⟨y, hy⟩

/-- Each gluing is a homeomorphism of `ℝ` (an orientation-reversing one). -/
noncomputable def toHomeomorph {P Q : Marking r} {c : ℤ} (F : C(ℝ, ℝ)) (hF : F ∈ gluings P Q c) :
    ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (fun x => -F x) (fun _ _ h => neg_lt_neg (hF.1 h))
    (fun t => (surjective_of_mem_gluings hF (-t)).imp fun _ h => by simp [h])).toHomeomorph.trans
    (Homeomorph.neg ℝ)

@[simp] theorem toHomeomorph_apply {P Q : Marking r} {c : ℤ} (F : C(ℝ, ℝ))
    (hF : F ∈ gluings P Q c) (x : ℝ) : toHomeomorph F hF x = F x := by
  simp only [toHomeomorph, Homeomorph.trans_apply, Homeomorph.coe_neg]
  exact neg_neg _

/-- A strictly antitone map sending the marked points of `a` onto those of `a'` induces an
anti-isomorphism `k ↦ c - k` of the labels: the spaces `gluings P Q c` exhaust the gluings
respecting the markings. -/
theorem exists_antiIso (P Q : Marking r) (F : ℝ → ℝ) (hF : StrictAnti F)
    (hmaps : ∀ k, ∃ j, F (P.pt k) = Q.pt j) (honto : ∀ j, ∃ k, F (P.pt k) = Q.pt j) :
    ∃ c : ℤ, ∀ k, F (P.pt k) = Q.pt (c - k) := by
  choose σ hσ using hmaps
  have anti : StrictAnti σ := fun k l hkl => by
    have := hF (P.strictMono hkl)
    rw [hσ, hσ] at this
    exact Q.strictMono.lt_iff_lt.1 this
  have surj : ∀ j, ∃ k, σ k = j := fun j => by
    obtain ⟨k, hk⟩ := honto j
    exact ⟨k, Q.strictMono.injective ((hσ k).symm.trans hk)⟩
  have step : ∀ k, σ (k + 1) = σ k - 1 := fun k => by
    have h1 : σ (k + 1) < σ k := anti (by omega)
    obtain ⟨l, hl⟩ := surj (σ k - 1)
    rcases le_or_gt l k with h | h
    · have := anti.antitone h; omega
    · have := anti.antitone (show k + 1 ≤ l by omega); omega
  refine ⟨σ 0, fun k => ?_⟩
  rw [hσ]
  congr 1
  induction k using Int.induction_on with
  | zero => simp
  | succ m ih => rw [step, ih]; ring
  | pred m ih =>
    have := step (-(m : ℤ) - 1)
    rw [show -(m : ℤ) - 1 + 1 = -m by ring, ih] at this
    omega

/-- **Uniqueness of gluing (pages 55–58).** The orientation-reversing homeomorphisms between two
circles with `r` marked points realising a given anti-isomorphism of `ℤ/r`-torsors form a
non-empty contractible space. -/
theorem contractibleSpace_gluings (P Q : Marking r) (c : ℤ) : ContractibleSpace (gluings P Q c) :=
  (convex_gluings P Q c).contractibleSpace (gluings_nonempty P Q c)

/-- Two gluings realising the same anti-isomorphism are isotopic through such gluings. -/
theorem isPathConnected_gluings (P Q : Marking r) (c : ℤ) : IsPathConnected (gluings P Q c) := by
  have := contractibleSpace_gluings P Q c
  exact isPathConnected_iff_pathConnectedSpace.2 inferInstance

end Grothendieck.Folder148
