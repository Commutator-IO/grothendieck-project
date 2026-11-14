import Mathlib

/-!
# Quillen, notebook 1971-15: the poset of infinite, coinfinite subsets of `ℕ` is coned off

Daniel Quillen's research notebook 1971-15 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201971/1971-15.pdf>).

* pp. 3-4: `X` = subsets `x ⊆ ℕ` with `x` and `ℕ ∖ x` infinite, `x ≼ y` iff `x = y` or `x ⊆ y`
  with `y ∖ x` infinite. For a finite family `F` there is an infinite `z` contained in or disjoint
  from each member (`exists_infinite_subset_or_disjoint`); halving `z = c ∪ c'`
  (`exists_split`), `x ↦ x ∪ c` maps `F` into `X`, is monotone on `F`, and `x ≼ x ∪ c ≽ c`
  (`cone`): every finite subset of `X` is coned off, the combinatorial core of the
  contractibility of `X`.
-/

namespace Quillen.Notebook1971_15

open Set

/-- The poset `X` of p. 3: subsets of `ℕ` that are infinite with infinite complement. -/
def X : Set (Set ℕ) := {x | x.Infinite ∧ xᶜ.Infinite}

/-- Its order: `x ≼ y` iff `x = y`, or `x ⊆ y` with `y \ x` infinite. -/
def Le (x y : Set ℕ) : Prop := x = y ∨ x ⊆ y ∧ (y \ x).Infinite

/-- For a finite family `F`, an infinite `z` contained in or disjoint from each member. -/
theorem exists_infinite_subset_or_disjoint (F : Finset (Set ℕ)) :
    ∃ z : Set ℕ, z.Infinite ∧ ∀ x ∈ F, z ⊆ x ∨ Disjoint z x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨univ, infinite_univ, by simp⟩
  | insert a F _ ih =>
    obtain ⟨z, hz, hF⟩ := ih
    by_cases h : (z ∩ a).Infinite
    · refine ⟨z ∩ a, h, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact .inl inter_subset_right
      · exact (hF x hx).imp (inter_subset_left.trans ·) (·.mono_left inter_subset_left)
    · have h' : (z \ a).Infinite := fun hf => hz (by
        simpa [inter_union_sdiff] using (not_infinite.1 h).union hf)
      refine ⟨z \ a, h', fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact .inr disjoint_sdiff_left
      · exact (hF x hx).imp (sdiff_subset.trans ·) (·.mono_left sdiff_subset)

/-- An infinite subset of `ℕ` splits into two disjoint infinite parts. -/
theorem exists_split {z : Set ℕ} (hz : z.Infinite) :
    ∃ z₁ z₂, z₁ ∪ z₂ = z ∧ Disjoint z₁ z₂ ∧ z₁.Infinite ∧ z₂.Infinite := by
  let e := hz.natEmbedding
  let z₁ : Set ℕ := (fun n => (e (2 * n) : ℕ)) '' univ
  refine ⟨z₁, z \ z₁, union_sdiff_cancel ?_, disjoint_sdiff_right,
    (infinite_univ.image fun a _ b _ h => by simpa using e.injective (Subtype.ext h)), ?_⟩
  · rintro _ ⟨n, -, rfl⟩; exact (e _).2
  · refine ((infinite_univ (α := ℕ)).image (f := fun n => (e (2 * n + 1) : ℕ))
      fun a _ b _ h => by simpa using e.injective (Subtype.ext h)).mono ?_
    rintro _ ⟨n, -, rfl⟩
    refine ⟨(e _).2, ?_⟩
    rintro ⟨m, -, h⟩
    have := e.injective (Subtype.ext h); omega

/-- **pp. 3-4.** Every finite subset `F` of `X` is coned off inside `X`: there is `c ∈ X` such that
`x ↦ x ∪ c` maps `F` into `X`, is monotone on `F`, and `x ≼ x ∪ c ≽ c` for all `x ∈ F`. -/
theorem cone (F : Finset (Set ℕ)) (hF : ∀ x ∈ F, x ∈ X) :
    ∃ c ∈ X, ∀ x ∈ F, x ∪ c ∈ X ∧ Le x (x ∪ c) ∧ Le c (x ∪ c) ∧
      ∀ y ∈ F, Le x y → Le (x ∪ c) (y ∪ c) := by
  obtain ⟨z, hz, hzF⟩ := exists_infinite_subset_or_disjoint F
  obtain ⟨c, c', rfl, hcc, hc, hc'⟩ := exists_split hz
  have key : ∀ x ∈ F, c ∪ c' ⊆ x ∨ Disjoint (c ∪ c') x := hzF
  refine ⟨c, ⟨hc, hc'.mono fun n hn hn' => hcc.ne_of_mem hn' hn rfl⟩, fun x hx => ?_⟩
  obtain ⟨hxi, hxc⟩ := hF x hx
  rcases key x hx with hs | hd
  · have hx' : x ∪ c = x := union_eq_left.2 (subset_union_left.trans hs)
    refine ⟨hx'.symm ▸ hF x hx, .inl hx'.symm, .inr ⟨subset_union_right, ?_⟩, fun y hy hxy => ?_⟩
    · exact hc'.mono fun n hn => ⟨.inl (hs (.inr hn)), fun h => hcc.ne_of_mem h hn rfl⟩
    · rcases hxy with rfl | ⟨hxy, hinf⟩
      · exact .inl rfl
      · rw [hx', union_eq_left.2 (subset_union_left.trans (hs.trans hxy))]; exact .inr ⟨hxy, hinf⟩
  · refine ⟨⟨hxi.mono subset_union_left, hc'.mono fun n hn h => ?_⟩, .inr ⟨subset_union_left, ?_⟩,
      .inr ⟨subset_union_right, ?_⟩, fun y hy hxy => ?_⟩
    · rcases h with h | h
      · exact hd.ne_of_mem (.inr hn) h rfl
      · exact hcc.ne_of_mem h hn rfl
    · exact hc.mono fun n hn => ⟨.inr hn, fun h => hd.ne_of_mem (.inl hn) h rfl⟩
    · exact hxi.mono fun n hn => ⟨.inl hn, fun h => hd.ne_of_mem (.inl h) hn rfl⟩
    · rcases hxy with rfl | ⟨hxy, hinf⟩
      · exact .inl rfl
      refine .inr ⟨union_subset_union_left _ hxy, ?_⟩
      rcases key y hy with hs | hd'
      · exact hc'.mono fun n hn => ⟨.inl (hs (.inr hn)),
          fun h => h.elim (hd.ne_of_mem (.inr hn) · rfl) (hcc.ne_of_mem · hn rfl)⟩
      · exact hinf.mono fun n hn => ⟨.inl hn.1,
          fun h => h.elim hn.2 fun h' => hd'.ne_of_mem (Or.inl h') hn.1 rfl⟩

end Quillen.Notebook1971_15
