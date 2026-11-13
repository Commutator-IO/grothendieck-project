import Mathlib

/-!
# Quillen, notebook 1975-21, pp. 37-38: splitting a filtration indexed by a finite poset

Daniel Quillen's research notebook 1975-21 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201975/1975-21.pdf>), pp. 37-38:
a lattice homomorphism `W` from the order ideals of a finite poset `J` to the subspaces of a
vector space is split by choosing, for each `j`, a complement `V_j` of `W {< j}` in `W {≤ j}`:
then `W Z = ⨆_{j ∈ Z} V_j` for every order ideal `Z`, and the `V_j` are independent.

The proof uses only that the target is a modular lattice (subspaces, submodules over any
ring), that `W` preserves `⊔`, `⊓` and `⊥`, and that `J` is a finite partial order:

* `iSup_eq`: `W Z = ⨆_{j ∈ Z} V_j` (only `⊔` and `⊥` are used);
* `iSupIndep_V`: the `V_j` are independent;
* `submodule`: the case of submodules, as on the page.

The proof removes a maximal element `j` of `Z`: then `Z = (Z ∖ {j}) ∪ {≤ j}` and
`{≤ j} ∩ (Z ∖ {j}) ⊆ {< j}`.
-/

namespace Quillen.Notebook1975_21Filtration

variable {J α : Type*} [PartialOrder J] [Fintype J] [CompleteLattice α] [IsModularLattice α]
  (W : LatticeHom (LowerSet J) α) (hW : W ⊥ = ⊥) (V : J → α)
  (hsup : ∀ j, V j ⊔ W (LowerSet.Iio j) = W (LowerSet.Iic j))
  (hdis : ∀ j, Disjoint (V j) (W (LowerSet.Iio j)))

/-- The lower set of a finset that is a lower set. -/
def ofFinset (s : Finset J) (hs : IsLowerSet (s : Set J)) : LowerSet J := ⟨s, hs⟩

omit [Fintype J] in
include hW hsup hdis in
theorem main (n : ℕ) : ∀ (s : Finset J) (hs : IsLowerSet (s : Set J)), s.card = n →
    W (ofFinset s hs) = s.sup V ∧ s.SupIndep V := by
  classical
  induction n with
  | zero =>
    intro s hs hn
    obtain rfl := Finset.card_eq_zero.mp hn
    refine ⟨?_, Finset.supIndep_empty _⟩
    rw [Finset.sup_empty, ← hW]
    congr 1; ext; simp [ofFinset]
  | succ n ih =>
    intro s hs hn
    obtain ⟨j, hjs, hjmax⟩ := s.exists_maximal (Finset.card_pos.mp (by omega))
    set s' := s.erase j with hs'def
    have hjmax' : ∀ a ∈ s, ¬ j < a := fun a ha hlt => lt_irrefl a (lt_of_le_of_lt (hjmax ha hlt.le) hlt)
    have hs' : IsLowerSet (s' : Set J) := by
      intro a b hba ha
      simp only [hs'def, Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe,
        Set.mem_singleton_iff] at ha ⊢
      refine ⟨hs hba ha.1, fun hbj => ?_⟩
      subst hbj
      exact hjmax' a ha.1 (lt_of_le_of_ne hba (Ne.symm ha.2))
    have hcard : s'.card = n := by rw [Finset.card_erase_of_mem hjs]; omega
    obtain ⟨ihW, ihI⟩ := ih s' hs' hcard
    have hIic : LowerSet.Iic j ≤ ofFinset s hs := fun a ha => hs ha hjs
    have hIio : LowerSet.Iio j ≤ ofFinset s' hs' := fun a (ha : a < j) =>
      show a ∈ (s' : Set J) by rw [hs'def, Finset.coe_erase]; exact ⟨hs ha.le hjs, ha.ne⟩
    have hsplit : ofFinset s hs = ofFinset s' hs' ⊔ LowerSet.Iic j := by
      refine le_antisymm (fun a ha => ?_) (sup_le (fun a ha => ?_) hIic)
      · by_cases haj : a = j
        · exact Or.inr (show a ≤ j from haj.le)
        · exact Or.inl (show a ∈ (s' : Set J) by simp [hs'def, haj, show a ∈ s from ha])
      · exact Finset.mem_of_mem_erase ha
    have hmeet : LowerSet.Iic j ⊓ ofFinset s' hs' ≤ LowerSet.Iio j := by
      rintro a ⟨ha1, ha2⟩
      exact lt_of_le_of_ne ha1 (Finset.ne_of_mem_erase ha2)
    have hsupeq : s.sup V = V j ⊔ s'.sup V := by
      rw [← Finset.insert_erase hjs, Finset.sup_insert]
    have hWs : W (ofFinset s hs) = V j ⊔ W (ofFinset s' hs') := by
      rw [hsplit, map_sup, ← hsup j, sup_comm (V j), ← sup_assoc,
        sup_eq_left.mpr (OrderHomClass.mono W hIio), sup_comm]
    have hdisj : Disjoint (V j) (W (ofFinset s' hs')) := by
      have hVle : V j ≤ W (LowerSet.Iic j) := hsup j ▸ le_sup_left
      rw [disjoint_iff, ← inf_eq_left.mpr hVle, inf_assoc, ← map_inf]
      exact disjoint_iff.mp ((hdis j).mono_right (OrderHomClass.mono W hmeet))
    refine ⟨by rw [hWs, ihW, hsupeq], ?_⟩
    rw [← Finset.insert_erase hjs]
    exact ihI.insert (ihW ▸ hdisj)

include hW hsup hdis in
/-- **Notebook 1975-21, pp. 37-38**: `W Z = ⨆_{j ∈ Z} V_j` for every order ideal `Z`. -/
theorem iSup_eq (Z : LowerSet J) : W Z = ⨆ j ∈ Z, V j := by
  classical
  let s : Finset J := Finset.univ.filter (· ∈ Z)
  have hs : IsLowerSet (s : Set J) := by
    intro a b hba ha
    simp only [s, Finset.coe_filter, Finset.mem_univ, true_and] at ha ⊢
    exact Z.lower hba ha
  have hZ : ofFinset s hs = Z := by ext; simp [ofFinset, s]
  rw [← hZ, (main W hW V hsup hdis s.card s hs rfl).1, Finset.sup_eq_iSup]
  simp [s, ofFinset]

include hW hsup hdis in
/-- **Notebook 1975-21, pp. 37-38**: the `V_j` are independent. -/
theorem iSupIndep_V : iSupIndep V := by
  classical
  rw [iSupIndep_iff_supIndep_univ]
  exact (main W hW V hsup hdis _ Finset.univ (by simp [isLowerSet_univ]) rfl).2

/-- The page's case: subspaces of a vector space (submodules over any ring). Complements
`V_j` exist over a field (`Submodule.exists_isCompl`). -/
theorem submodule {k E : Type*} [Ring k] [AddCommGroup E] [Module k E]
    (W : LatticeHom (LowerSet J) (Submodule k E)) (hW : W ⊥ = ⊥) (V : J → Submodule k E)
    (hsup : ∀ j, V j ⊔ W (LowerSet.Iio j) = W (LowerSet.Iic j))
    (hdis : ∀ j, Disjoint (V j) (W (LowerSet.Iio j))) :
    (∀ Z, W Z = ⨆ j ∈ Z, V j) ∧ iSupIndep V :=
  ⟨iSup_eq W hW V hsup hdis, iSupIndep_V W hW V hsup hdis⟩

end Quillen.Notebook1975_21Filtration
