import Buffalo.Topos.Part01a

/-!
# Buffalo, topos theory, part 1e: colimits of sheaves and representability (4 April 1973)

Entry URU5jgTvjhU-6861 of `docs/buffalo-topos/index.tex`, left unattempted in the first pass of
Part01. The other entries of Part01 completed later are proved in Part02: URU5jgTvjhU-2745
(`Part02.sheafPtEquiv`), -7768 (`Part02.product_of_epis_not_epi`), -13813
(`Part02.pullback_preservesFiniteLimits`). Statuses in `docs/buffalo-topos/lean/Part01.json`.
-/

universe w v u

open CategoryTheory Limits Opposite

namespace Buffalo.Topos.Part01

noncomputable section

section Criterion

variable {J : Type w} [SmallCategory J] {C : Type*} [Category.{w} C] {D : Type*} [Category.{w} D]
  {ι : C ⥤ D} (hι : ι.FullyFaithful) (K : J ⥤ C) [HasColimit (K ⋙ ι)]

/-- For a full subcategory `ι : C ⊂ D`, the cocones over `K` with vertex `S` are the arrows
`colim (ι ∘ K) → ι S`. -/
def coconesIsoHom :
    K.cocones ≅ ι ⋙ coyoneda.obj (op (colimit (K ⋙ ι))) :=
  NatIso.ofComponents (fun S => Equiv.toIso
    { toFun := fun c => colimit.desc (K ⋙ ι) (ι.mapCocone ⟨S, c⟩)
      invFun := fun g =>
        { app := fun j => hι.preimage (colimit.ι (K ⋙ ι) j ≫ g)
          naturality := fun j j' f => hι.map_injective (by
            simpa using (colimit.w_assoc (K ⋙ ι) f g)) }
      left_inv := fun c => by
        apply NatTrans.ext
        funext j
        apply hι.map_injective
        simp
      right_inv := fun g => by
        apply colimit.hom_ext
        intro j
        simp })
    (fun {S S'} f => by
      ext c
      apply colimit.hom_ext
      intro j
      simp)

include hι in
/-- URU5jgTvjhU-6861 (1:54:21) [prop] (for any full subcategory, here `Sh(X) ⊂ PSh(X)`) A colimit of
`K` exists iff `G ↦ Hom(P, G)` is (co)representable, `P` being the colimit taken in the ambient
category. -/
theorem hasColimit_iff_corepresentable :
    HasColimit K ↔ (ι ⋙ coyoneda.obj (op (colimit (K ⋙ ι)))).IsCorepresentable := by
  constructor
  · intro _
    exact ⟨colimit K, ⟨((colimit.isColimit K).corepresentableBy).ofIso (coconesIsoHom hι K)⟩⟩
  · rintro ⟨X, ⟨h⟩⟩
    exact HasColimit.mk ⟨_, IsColimit.ofCorepresentableBy (h.ofIso (coconesIsoHom hι K).symm)⟩

end Criterion

/-- URU5jgTvjhU-6861 (1:54:21) [prop] The criterion for sheaves on a space. -/
theorem sheaf_hasColimit_iff {X : TopCat.{u}} {J : Type u} [SmallCategory J]
    (K : J ⥤ Sheaf (Opens.grothendieckTopology X) (Type u)) :
    HasColimit K ↔ (sheafToPresheaf (Opens.grothendieckTopology X) (Type u) ⋙
      coyoneda.obj (op (colimit (K ⋙ sheafToPresheaf _ _)))).IsCorepresentable :=
  hasColimit_iff_corepresentable (fullyFaithfulSheafToPresheaf _ _) K

end

end Buffalo.Topos.Part01
