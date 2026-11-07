import Buffalo.Topos.Part01a

/-!
# Buffalo, topos theory, part 1: claims of the blackboards not covered by an index entry

Items of `public/buffalo-boards/URU5jgTvjhU-*.json` (0:03:26–5:34:24) that make a mathematical
claim not already formalised by an entry of `docs/buffalo-topos/lean/Part01.json`. The status of
every board item is in `docs/buffalo-topos/lean/Part01-boards.json`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace Buffalo.Topos.Part01.Boards

/-- Board URU5jgTvjhU-2951, t = 3290: an open embedding (the inclusion of an open set) is étale. -/
theorem openEmbedding_etale {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] {f : A → B}
    (hf : IsOpenEmbedding f) : IsLocalHomeomorph f :=
  hf.isLocalHomeomorph

/-- Board URU5jgTvjhU-2951, t = 3310–3346: for `I` discrete, the projection `I × X → X` is étale. -/
theorem discrete_prod_etale (I B : Type*) [TopologicalSpace I] [DiscreteTopology I]
    [TopologicalSpace B] : IsLocalHomeomorph (Prod.snd : I × B → B) := by
  refine isLocalHomeomorph_of_isOpenMap continuous_snd isOpenMap_snd ?_
  rintro ⟨i, b⟩
  refine ⟨{p | p.1 = i}, (isOpen_discrete {i}).preimage continuous_fst, rfl, ?_⟩
  rintro ⟨i₁, b₁⟩ h₁ ⟨i₂, b₂⟩ h₂ (h : b₁ = b₂)
  rw [show i₁ = i from h₁, show i₂ = i from h₂, h]

/-- Board URU5jgTvjhU-2951, t = 3370: covering spaces are étale. -/
theorem covering_etale {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {f : E → B}
    (hf : IsCoveringMap f) : IsLocalHomeomorph f :=
  hf.isLocalHomeomorph

/-- Board URU5jgTvjhU-2951, t = 4350–4523: products and kernels of pairs of arrows give all
inverse limits. -/
theorem limits_of_products_equalizers {C : Type*} [Category C] [HasProducts.{u} C]
    [HasEqualizers C] : HasLimitsOfSize.{u, u} C :=
  has_limits_of_hasEqualizers_and_products

/-- Board URU5jgTvjhU-2951, t = 4659: `C → Ĉ`, `X ↦ Hom(-, X)`, is fully faithful. -/
def yoneda_fullyFaithful (C : Type*) [Category C] : (yoneda (C := C)).FullyFaithful :=
  Yoneda.fullyFaithful

/-- Board URU5jgTvjhU-2951, t = 5045–5210: inverse limits of sheaves are computed as for
presheaves (the inclusion creates limits). -/
theorem sheaf_createsLimits (X : TopCat.{u}) :
    Nonempty (CreatesLimits (sheafToPresheaf (Opens.grothendieckTopology X) (Type u))) :=
  ⟨inferInstance⟩

/-- Board URU5jgTvjhU-14528, t = 17034: `u` is a monomorphism of sheaves iff every `u_x` is. -/
theorem sheaf_mono_iff_stalks {X : TopCat.{u}} {F G : TopCat.Sheaf (Type u) X} (f : F ⟶ G) :
    Mono f ↔ ∀ x, Mono ((TopCat.Presheaf.stalkFunctor (Type u) x).map f.hom) :=
  TopCat.Presheaf.mono_iff_stalk_mono f

end Buffalo.Topos.Part01.Boards
