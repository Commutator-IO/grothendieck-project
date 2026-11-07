import Buffalo.Topos.Part02a

/-!
# Buffalo, topos theory, part 2: board items not covered by an index entry

Items of the reconstructed blackboards `public/buffalo-boards/URU5jgTvjhU-{20201,23160,26072,
29033,30214}.json` (18 and 25 May 1973) that make a claim not formalised by an index entry of
Part02. The status of every board item is in `docs/buffalo-topos/lean/Part02-boards.json`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace Buffalo.Topos.Part02.Boards

noncomputable section

/-- Board URU5jgTvjhU-20201, t = 21715: the arrow `e ⊔ A^* → A` (zero section, inclusion of the
units) is injective iff `0 ≠ 1` in `A` (read on sections: a monomorphism of sheaves iff `0 ≠ 1` in
every nonempty `A(U)`); for the zero ring it is not. -/
theorem unitsZero_injective_iff (R : Type*) [CommRing R] :
    Function.Injective (Sum.elim (fun _ : Unit => (0 : R)) (fun v : Rˣ => (v : R))) ↔
      Nontrivial R := by
  constructor
  · intro h
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    exact Sum.inl_ne_inr (h (a₁ := Sum.inl ()) (a₂ := Sum.inr 1) (Subsingleton.elim _ _))
  · intro _
    rintro (⟨⟩ | v) (⟨⟩ | w) h
    · rfl
    · exact absurd h.symm w.ne_zero
    · exact absurd h v.ne_zero
    · exact congrArg Sum.inr (Units.ext h)

/-- The Sierpiński space: `{True}` is open, `{False}` closed. -/
abbrev sierpinski : TopCat.{0} := TopCat.of Prop

/-- The point `True` is dense in the Sierpiński space. -/
theorem dense_true : Dense ({True} : Set Prop) := by
  intro x
  rw [mem_closure_iff_nhds]
  intro t ht
  by_cases hx : x
  · exact ⟨x, mem_of_mem_nhds ht, by simpa using hx⟩
  · have hxf : x = False := by simpa using hx
    subst hxf
    rw [nhds_false, Filter.mem_top] at ht
    exact ⟨True, by simp [ht], rfl⟩

/-- The sheaf of `Bool`-valued maps on the Sierpiński space. -/
abbrev boolMaps : sierpinski.Presheaf (Type) := sierpinski.presheafToTypes fun _ => Bool

open scoped Classical in
/-- The automorphism of `boolMaps` negating values at `False`. -/
def negAtFalse : boolMaps ⟶ boolMaps where
  app _ := ↾fun s x => if x.1 then s x else !(s x)
  naturality _ _ _ := rfl

/-- Board URU5jgTvjhU-26072, t = 28073: « `f` dominant iff `f^*` faithful » fails. For the dense
point `True` of the Sierpiński space (`f : pt → Y`, `f^*F = F_True`), the stalk functor at `True`
identifies `negAtFalse` with the identity, though it is not the identity: `f` is dominant but `f^*`
is not faithful. -/
theorem dominant_not_faithful :
    negAtFalse ≠ 𝟙 boolMaps ∧
      (TopCat.Presheaf.stalkFunctor (Type) (True : sierpinski)).map negAtFalse =
        (TopCat.Presheaf.stalkFunctor (Type) (True : sierpinski)).map (𝟙 boolMaps) := by
  constructor
  · intro h
    have := congrArg (fun φ : boolMaps ⟶ boolMaps =>
      φ.app (op ⊤) (fun _ => true) ⟨False, trivial⟩) h
    change @ite Bool False (Classical.propDecidable False) true (!true) = true at this
    simp at this
  · apply TopCat.Presheaf.stalk_hom_ext
    intro U hU
    rw [TopCat.Presheaf.stalkFunctor_map_germ, TopCat.Presheaf.stalkFunctor_map_germ]
    ext s
    let W : Opens sierpinski := U ⊓ ⟨{True}, isOpen_singleton_true⟩
    have hW : True ∈ W := ⟨hU, rfl⟩
    let i : W ⟶ U := homOfLE inf_le_left
    change boolMaps.germ U True hU (negAtFalse.app (op U) s) =
      boolMaps.germ U True hU s
    rw [← boolMaps.germ_res_apply i True hW, ← boolMaps.germ_res_apply i True hW]
    congr 1
    funext y
    have hy : y.1 = True := y.2.2
    change @ite Bool y.1 (Classical.propDecidable _) (s ⟨y.1, y.2.1⟩) (!(s ⟨y.1, y.2.1⟩)) =
      s ⟨y.1, y.2.1⟩
    simp [hy]

end

end Buffalo.Topos.Part02.Boards
