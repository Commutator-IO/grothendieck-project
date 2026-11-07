import Buffalo.Topos.Part02a

/-!
# Buffalo, topos theory, part 2b: infinite products, connectedness, torsors, stacks (18 May 1973)

Entries of `docs/buffalo-topos/index.tex` from « Stalks and infinite products » to « Gluing and
quotient topoi » (video `URU5jgTvjhU`, 6:51:54–7:52:11). The status of each entry is in
`docs/buffalo-topos/lean/Part02.json`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Topology MonoidalCategory

namespace Buffalo.Topos.Part02

noncomputable section

open Buffalo.Topos.Part01

variable {X : TopCat.{u}}

/-! ## Stalks and infinite products -/

/-- URU5jgTvjhU-24714 (6:51:54) [prop] The canonical arrow `(∏ᵢ Fᵢ)_x → ∏ᵢ (Fᵢ)_x`. -/
def stalk_piComparison {ι : Type u} (F : ι → X.Presheaf (Type u)) (x : X) :
    (TopCat.Presheaf.stalkFunctor (Type u) x).obj (∏ᶜ F) ⟶
      ∏ᶜ fun i => (TopCat.Presheaf.stalkFunctor (Type u) x).obj (F i) :=
  piComparison _ F

/-- URU5jgTvjhU-24851 (6:54:11) [rem] and URU5jgTvjhU-24919 (6:55:19) [cex] On `ℝ`, with
`Uₙ = ]-1/(n+1), 1/(n+1)[`, `fₙ = a` and `gₙ = a` on `Uₙ`, `b` elsewhere (maps to
`{a, b} = Bool`), each `fₙ, gₙ` have the same germ at `0`, but they coincide on no common
neighbourhood of `0`: the arrow `(∏ Fᵢ)₀ → ∏ (Fᵢ)₀` is not injective. -/
theorem germ_product_counterexample :
    ∃ f g : ℕ → ℝ → Bool, (∀ n, f n =ᶠ[𝓝 0] g n) ∧ ¬ ∀ᶠ y in 𝓝 (0 : ℝ), ∀ n, f n y = g n y := by
  refine ⟨fun _ _ => true, fun n y => decide (|y| < 1 / ((n : ℝ) + 1)), fun n => ?_, ?_⟩
  · have : Metric.ball (0 : ℝ) (1 / ((n : ℝ) + 1)) ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [this] with y hy
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, one_div] at hy
    simp [hy]
  · intro h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
    have hy : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    have := hball (ε / 2) hy n
    simp only [eq_comm (a := true), decide_eq_true_eq] at this
    rw [abs_of_pos (half_pos hε)] at this
    linarith

/-- URU5jgTvjhU-25045 (6:57:25) [prop] (injectivity half, in germ form) Germs at `x` of families of
maps commute with products iff `x` has a smallest open neighbourhood. -/
theorem germ_product_iff {Z : Type u} [TopologicalSpace Z] (x : Z) :
    (∀ (ι : Type u) (f g : ι → Z → Bool), (∀ i, f i =ᶠ[𝓝 x] g i) →
        ∀ᶠ y in 𝓝 x, ∀ i, f i y = g i y) ↔
      ∃ U : Set Z, IsOpen U ∧ x ∈ U ∧ ∀ V : Set Z, IsOpen V → x ∈ V → U ⊆ V := by
  classical
  constructor
  · intro h
    have := h {V : Set Z // IsOpen V ∧ x ∈ V} (fun _ _ => true) (fun V y => decide (y ∈ V.1))
      (fun V => by
        filter_upwards [V.2.1.mem_nhds V.2.2] with y hy
        simp [hy])
    obtain ⟨U, hU, hUo, hxU⟩ := mem_nhds_iff.1 this
    refine ⟨U, hUo, hxU, fun V hV hxV y hy => ?_⟩
    have := hU hy ⟨V, hV, hxV⟩
    simpa [eq_comm] using this
  · rintro ⟨U, hUo, hxU, hmin⟩ ι f g hfg
    filter_upwards [hUo.mem_nhds hxU] with y hy i
    obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.1 (hfg i)
    exact hW (hmin W hWo hxW hy)

/-- URU5jgTvjhU-25045 (6:57:25) [prop] If points are closed, `x` has a smallest open neighbourhood
iff `x` is isolated. -/
theorem smallest_nhd_iff_isolated {Z : Type u} [TopologicalSpace Z] [T1Space Z] (x : Z) :
    (∃ U : Set Z, IsOpen U ∧ x ∈ U ∧ ∀ V : Set Z, IsOpen V → x ∈ V → U ⊆ V) ↔ IsOpen {x} := by
  constructor
  · rintro ⟨U, hUo, hxU, hmin⟩
    have : U = {x} := by
      ext y
      refine ⟨fun hy => ?_, fun hy => hy ▸ hxU⟩
      by_contra hyx
      exact hmin {y}ᶜ isOpen_compl_singleton (Ne.symm hyx) hy rfl
    exact this ▸ hUo
  · intro h
    exact ⟨{x}, h, rfl, fun V _ hxV => Set.singleton_subset_iff.2 hxV⟩

/-- The sheaf `Fₙ` of sections of `Uₙ ⊔ (ℝ ∖ {0}) → ℝ`, `Uₙ = ]-1/(n+1), 1/(n+1)[`: continuous
`s : U → Bool`, `s = true` only on `Uₙ` and `s = false` only off `0`. -/
def shrinkingPred (n : ℕ) : TopCat.LocalPredicate fun _ : TopCat.of ℝ => Bool where
  pred {U} f := Continuous f ∧
    ∀ y : U, (f y = true → |(y : ℝ)| < 1 / ((n : ℝ) + 1)) ∧ (f y = false → (y : ℝ) ≠ 0)
  res {U V} i f h := ⟨(TopCat.continuousLocal _ Bool).res i f h.1, fun x => h.2 ⟨x.1, i.le x.2⟩⟩
  locality {U} f w := by
    refine ⟨(TopCat.continuousLocal _ Bool).locality f fun x => ?_, fun x => ?_⟩
    · obtain ⟨V, m, i, h⟩ := w x
      exact ⟨V, m, i, h.1⟩
    · obtain ⟨V, m, i, h⟩ := w x
      exact h.2 ⟨x, m⟩

/-- The sheaves `Fₙ`. -/
abbrev shrinkingSheaf (n : ℕ) : TopCat.Sheaf (Type) (TopCat.of ℝ) :=
  TopCat.subsheafToTypes.{0, 0} (shrinkingPred n)

/-- The terminal sheaf on `ℝ` (one section over every open set). -/
abbrev unitSheaf : TopCat.Sheaf (Type) (TopCat.of ℝ) :=
  ⟨(TopCat.of ℝ).presheafToTypes fun _ => PUnit.{1}, TopCat.Presheaf.toTypes_isSheaf _ _⟩

/-- The arrow `Fₙ → e`. -/
def toUnitSheaf (F : TopCat.Sheaf (Type) (TopCat.of ℝ)) : F ⟶ unitSheaf :=
  ObjectProperty.homMk
    { app := fun _ => ↾fun _ _ => PUnit.unit
      naturality := fun _ _ _ => rfl }

/-- No morphism from `∏ₙ Fₙ` to the terminal sheaf is an epimorphism: near `0`, a family of sections
of all the `Fₙ` would force a neighbourhood of `0` inside every `Uₙ`. -/
theorem not_epi_from_prod (ψ : ∏ᶜ shrinkingSheaf ⟶ unitSheaf) : ¬ Epi ψ := by
  intro hψ
  rw [sheaf_epi_iff_local_lift] at hψ
  obtain ⟨V, -, h0V, s, -⟩ := hψ ⊤ (fun _ => PUnit.unit) 0 trivial
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 V.2 0 h0V
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
  let t := (Pi.π shrinkingSheaf n).hom.app (op V) s
  obtain ⟨f, hfc, hf⟩ := t
  have hB : _root_.IsPreconnected (Set.range (Set.inclusion hball)) := by
    rw [← Set.image_univ]
    have : PreconnectedSpace (Metric.ball (0 : ℝ) ε) :=
      isPreconnected_iff_preconnectedSpace.1 (convex_ball (0 : ℝ) ε).isPreconnected
    exact isPreconnected_univ.image _ (continuous_inclusion hball).continuousOn
  have h0 : f ⟨0, h0V⟩ = true := by
    cases h : f ⟨0, h0V⟩
    · exact absurd rfl ((hf ⟨0, h0V⟩).2 h)
    · rfl
  have hyB : (ε / 2 : ℝ) ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hconst := hB.constant hfc.continuousOn (x := Set.inclusion hball ⟨ε / 2, hyB⟩)
    (y := Set.inclusion hball ⟨0, Metric.mem_ball_self hε⟩) ⟨_, rfl⟩ ⟨_, rfl⟩
  have h1 : f (Set.inclusion hball ⟨ε / 2, hyB⟩) = true := hconst.trans h0
  have := (hf _).1 h1
  change |ε / 2| < _ at this
  rw [abs_of_pos (half_pos hε)] at this
  linarith

/-- URU5jgTvjhU-25113 (6:58:33) [cex], URU5jgTvjhU-25307 (7:01:47) [ex] and URU5jgTvjhU-7768
(2:09:28) In `Sh(ℝ)`, with `Fₙ = Uₙ ⊔ (ℝ ∖ {0})`, `Uₙ = ]-1/(n+1), 1/(n+1)[`, each `Fₙ → e` is an
epimorphism but their product `∏ Fₙ → ∏ e = e` is not. -/
theorem product_of_epis_not_epi :
    (∀ n, Epi (toUnitSheaf (shrinkingSheaf n))) ∧
      ¬ Epi (Limits.Pi.map fun n => toUnitSheaf (shrinkingSheaf n)) := by
  refine ⟨fun n => ?_, fun h => ?_⟩
  · rw [sheaf_epi_iff_local_lift]
    intro U t x hx
    by_cases hx1 : |x| < 1 / ((n : ℝ) + 1)
    · refine ⟨U ⊓ ⟨Metric.ball 0 (1 / ((n : ℝ) + 1)), Metric.isOpen_ball⟩, homOfLE inf_le_left,
        ⟨hx, by simpa [Metric.mem_ball, Real.norm_eq_abs] using hx1⟩,
        ⟨fun _ => true, continuous_const, fun y => ⟨fun _ => ?_, fun h => by simp at h⟩⟩, rfl⟩
      have := y.2.2
      simpa [Metric.mem_ball, Real.norm_eq_abs] using this
    · have hx0 : x ≠ 0 := by
        rintro rfl
        exact hx1 (by simp; positivity)
      refine ⟨U ⊓ ⟨{0}ᶜ, isOpen_compl_singleton⟩, homOfLE inf_le_left, ⟨hx, hx0⟩,
        ⟨fun _ => false, continuous_const, fun y => ⟨fun h => by simp at h, fun _ => y.2.2⟩⟩, rfl⟩
  · have hπ : Epi (Pi.π (fun _ : ℕ => unitSheaf) 0) :=
      (IsSplitEpi.mk' ⟨Pi.lift fun _ => 𝟙 _, by simp⟩).epi
    exact not_epi_from_prod _ (epi_comp (Limits.Pi.map fun n => toUnitSheaf (shrinkingSheaf n))
      (Pi.π (fun _ : ℕ => unitSheaf) 0))

/-- Restricting twice is restricting once. -/
theorem map_map_apply (F : TopCat.Sheaf (Type u) X) {U V W : Opens X} (h1 : V ≤ U) (h2 : W ≤ V)
    (h3 : W ≤ U) (x : F.obj.obj (op U)) :
    F.obj.map (homOfLE h2).op (F.obj.map (homOfLE h1).op x) = F.obj.map (homOfLE h3).op x := by
  rw [← Functor.map_comp_apply]
  rfl

/-- Gluing two sections over two disjoint open sets covering `W`. -/
theorem glue_two (F : TopCat.Sheaf (Type u) X) (W A B : Opens X) (hAW : A ≤ W) (hBW : B ≤ W)
    (hWAB : W ≤ A ⊔ B) (hAB : A ⊓ B = ⊥) (a : F.obj.obj (op A)) (b : F.obj.obj (op B)) :
    ∃ s : F.obj.obj (op W), F.obj.map (homOfLE hAW).op s = a ∧
      F.obj.map (homOfLE hBW).op s = b := by
  let V : Bool → Opens X := fun i => if i then A else B
  let sf : ∀ i, F.obj.obj (op (V i)) := fun i => match i with | true => a | false => b
  have hcompat : TopCat.Presheaf.IsCompatible F.obj V sf := by
    intro i j
    have hbot : ∀ i j : Bool, i ≠ j → V i ⊓ V j = ⊥ := by
      intro i j hij
      cases i <;> cases j <;> simp_all [V, inf_comm]
    by_cases hij : i = j
    · subst hij; rfl
    · exact (uniqueOfEqBot F (hbot i j hij)).instSubsingleton.elim _ _
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' V W
    (fun i => homOfLE (by cases i; exacts [hBW, hAW])) (by
      intro y hy
      rcases hWAB hy with h | h
      · exact Opens.mem_iSup.2 ⟨true, h⟩
      · exact Opens.mem_iSup.2 ⟨false, h⟩) sf hcompat
  exact ⟨s, hs true, hs false⟩

section Stone

variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]

/-- On a compact totally disconnected Hausdorff space, an epimorphism of sheaves is surjective on
every open-closed set (the local lifts are glued along a finite clopen partition). -/
theorem stone_epi_surjective {F G : TopCat.Sheaf (Type u) X} (φ : F ⟶ G) [Epi φ] (U : Opens X)
    (hU : IsClopen (U : Set X)) : Function.Surjective (φ.hom.app (op U)) := by
  classical
  intro t
  have hlift := (sheaf_epi_iff_local_lift φ).1 inferInstance U t
  choose V i hxV s hs using hlift
  have hC : ∀ x (hx : x ∈ U), ∃ C : Set X, IsClopen C ∧ x ∈ C ∧ C ⊆ V x hx :=
    fun x hx => exists_isClopen_mem_of_isOpen (V x hx).2 (hxV x hx)
  choose C hCc hxC hCV using hC
  obtain ⟨T, hT⟩ := hU.1.isCompact.elim_finite_subcover (fun x : U => C x x.2)
    (fun x => (hCc x x.2).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxC x hx⟩)
  have key : ∀ (T : Finset U) (W : Opens X), IsClopen (W : Set X) → ∀ hWU : W ≤ U,
      (W : Set X) ⊆ ⋃ x ∈ T, C x x.2 →
      ∃ s' : F.obj.obj (op W), φ.hom.app (op W) s' = G.obj.map (homOfLE hWU).op t := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro W _ hWU hW
      have hW0 : W = ⊥ := by
        ext y
        simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty] at hW
        exact ⟨fun hy => hW hy, fun h => h.elim⟩
      exact ⟨(uniqueOfEqBot F hW0).default, (uniqueOfEqBot G hW0).instSubsingleton.elim _ _⟩
    | insert a T' ha ih =>
      intro W hWc hWU hW
      let A : Opens X := W ⊓ ⟨C a a.2, (hCc a a.2).isOpen⟩
      let B : Opens X := ⟨(W : Set X) \ C a a.2, hWc.isOpen.sdiff (hCc a a.2).isClosed⟩
      have hAW : A ≤ W := inf_le_left
      have hBW : B ≤ W := fun y hy => hy.1
      have hWAB : W ≤ A ⊔ B := fun y hy =>
        (em (y ∈ C a a.2)).elim (fun h => Or.inl ⟨hy, h⟩) (fun h => Or.inr ⟨hy, h⟩)
      have hAB : A ⊓ B = ⊥ := by
        ext y
        simp only [Opens.coe_inf, Set.mem_inter_iff, A, B]
        constructor
        · rintro ⟨⟨-, h⟩, -, h'⟩; exact absurd h h'
        · intro h; exact h.elim
      have hAV : A ≤ V a a.2 := fun y hy => hCV a a.2 hy.2
      have hBU : B ≤ U := hBW.trans hWU
      obtain ⟨b, hb⟩ := ih B (hWc.diff (hCc a a.2)) hBU (by
        intro y ⟨hyW, hya⟩
        obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hW hyW)
        rcases Finset.mem_insert.1 hx with rfl | hx'
        · exact absurd hyx hya
        · exact Set.mem_iUnion₂.2 ⟨x, hx', hyx⟩)
      obtain ⟨g, hgA, hgB⟩ := glue_two F W A B hAW hBW hWAB hAB
        (F.obj.map (homOfLE hAV).op (s a a.2)) b
      refine ⟨g, ?_⟩
      apply G.eq_of_locally_eq' (fun j : Bool => if j then A else B) W
        (fun j => homOfLE (by cases j; exacts [hBW, hAW])) (by
          intro y hy
          rcases hWAB hy with h | h
          · exact Opens.mem_iSup.2 ⟨true, h⟩
          · exact Opens.mem_iSup.2 ⟨false, h⟩)
      intro j
      cases j
      · change G.obj.map (homOfLE hBW).op (φ.hom.app _ g) =
          G.obj.map (homOfLE hBW).op (G.obj.map (homOfLE hWU).op t)
        rw [← NatTrans.naturality_apply φ.hom, hgB, hb, map_map_apply G hWU hBW hBU]
      · change G.obj.map (homOfLE hAW).op (φ.hom.app _ g) =
          G.obj.map (homOfLE hAW).op (G.obj.map (homOfLE hWU).op t)
        rw [← NatTrans.naturality_apply φ.hom, hgA, NatTrans.naturality_apply φ.hom, hs a a.2,
          show i a a.2 = homOfLE (leOfHom (i a a.2)) from rfl,
          map_map_apply G _ hAV (hAW.trans hWU), map_map_apply G hWU hAW (hAW.trans hWU)]
  obtain ⟨s', hs'⟩ := key T U hU le_rfl hT
  exact ⟨s', hs'.trans (by simp)⟩

/-- URU5jgTvjhU-25503 (7:05:03) [prop] (corrected: `X` compact *Hausdorff* totally disconnected)
`F → G` is an epimorphism iff `F(U) → G(U)` is surjective for every open-closed `U`. -/
theorem stone_epi_iff {F G : TopCat.Sheaf (Type u) X} (φ : F ⟶ G) :
    Epi φ ↔ ∀ U : Opens X, IsClopen (U : Set X) → Function.Surjective (φ.hom.app (op U)) := by
  refine ⟨fun _ U hU => stone_epi_surjective φ U hU, fun h => ?_⟩
  rw [sheaf_epi_iff_local_lift]
  intro U t x hx
  obtain ⟨C, hC, hxC, hCU⟩ := exists_isClopen_mem_of_isOpen U.2 hx
  obtain ⟨s, hs⟩ := h ⟨C, hC.isOpen⟩ hC (G.obj.map (homOfLE hCU).op t)
  exact ⟨⟨C, hC.isOpen⟩, homOfLE hCU, hxC, s, hs⟩

/-- URU5jgTvjhU-25503 (7:05:03) [prop] On such a space every product of epimorphisms of sheaves is
an epimorphism. -/
theorem stone_prod_epi {ι : Type u} {F G : ι → Sheaf (Opens.grothendieckTopology X) (Type u)}
    (φ : ∀ i, F i ⟶ G i)
    [hφ : ∀ i, Epi (φ i)] : Epi (Limits.Pi.map φ) := by
  refine (stone_epi_iff (X := X) (F := ∏ᶜ F) (G := ∏ᶜ G) (Limits.Pi.map φ)).2 ?_
  intro U hU t
  let E := sheafToPresheaf (Opens.grothendieckTopology X) (Type u) ⋙
    (evaluation _ (Type u)).obj (op U)
  have : PreservesLimit (Discrete.functor F) E := comp_preservesLimit _ _
  have : PreservesLimit (Discrete.functor G) E := comp_preservesLimit _ _
  let hF := Types.isLimitEquivSections (isLimitOfPreserves E (limit.isLimit (Discrete.functor F)))
  let hG := Types.isLimitEquivSections (isLimitOfPreserves E (limit.isLimit (Discrete.functor G)))
  choose s hs using fun i => @stone_epi_surjective X _ _ _ (F i) (G i) (φ i) (hφ i) U hU
    ((Pi.π G i).hom.app (op U) t)
  let σ : (Discrete.functor F ⋙ E).sections :=
    ⟨fun j => s j.as, fun {j j'} f => by
      rcases j with ⟨j⟩
      rcases j' with ⟨j'⟩
      have h : j = j' := Discrete.eq_of_hom f
      subst h
      simp⟩
  refine ⟨hF.symm σ, hG.injective (Subtype.ext (funext fun ⟨i⟩ => ?_))⟩
  have h1 : (Pi.π F i).hom.app (op U) (hF.symm σ) = s i :=
    congrArg (fun z => z.1 ⟨i⟩) (hF.apply_symm_apply σ)
  have h2 := congrArg (fun f : (∏ᶜ F) ⟶ G i => f.hom.app (op U) (hF.symm σ))
    (Limits.Pi.map_π φ i)
  change (Pi.π G i).hom.app (op U) ((Limits.Pi.map φ).hom.app (op U) (hF.symm σ)) =
    (Pi.π G i).hom.app (op U) t
  rw [← hs i, ← h1]
  exact h2

end Stone

/-! ## Connectedness and cohomology -/

/-- URU5jgTvjhU-26587 (7:23:07) [rem] The lattice of open sets of `X` is that of the subobjects
(subsheaves) of the terminal sheaf `e = 𝒪(-, X)`. -/
def subterminalEquivOpens :
    {S : Subfunctor (yoneda.obj (⊤ : Opens X)) // TopCat.Presheaf.IsSheaf (X := X) S.toFunctor} ≃
      Opens X where
  toFun S := sSup {U | (S.1.obj (op U)).Nonempty}
  invFun W := ⟨{ obj := fun U => {_a | U.unop ≤ W}, map := fun i _ h => (leOfHom i.unop).trans h },
    (subfunctor_isSheaf_iff (yoneda_isSheaf ⊤) _).2 fun _ U _ hs => show iSup U ≤ W from iSup_le hs⟩
  left_inv S := by
    apply Subtype.ext
    apply Subfunctor.ext
    funext U
    ext a
    obtain ⟨U⟩ := U
    change U ≤ sSup _ ↔ _
    constructor
    · intro hU
      let ι := {V : Opens X // (S.1.obj (op V)).Nonempty}
      let cov : ι → Opens X := fun i => U ⊓ i.1
      have heq : iSup cov = U := by
        apply le_antisymm (iSup_le fun _ => inf_le_left)
        intro x hx
        obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.1 (hU hx)
        exact Opens.mem_iSup.2 ⟨⟨V, hV⟩, ⟨hx, hxV⟩⟩
      have key := (subfunctor_isSheaf_iff (yoneda_isSheaf ⊤) S.1).1 S.2 cov
        (homOfLE le_top) (fun i => by
          obtain ⟨b, hb⟩ := i.2
          have := S.1.map (homOfLE (inf_le_right : cov i ≤ i.1)).op hb
          have sub : ∀ (p q : (yoneda.obj (⊤ : Opens X)).obj (op (cov i))), p = q :=
            fun _ _ => Subsingleton.elim (α := cov i ⟶ ⊤) _ _
          rw [sub ((yoneda.obj ⊤).map _ (homOfLE le_top))
            ((yoneda.obj ⊤).map (homOfLE (inf_le_right : cov i ≤ i.1)).op b)]
          exact this)
      rw [heq] at key
      convert key using 1
      exact Subsingleton.elim (α := U ⟶ ⊤) _ _
    · intro ha
      exact le_sSup ⟨a, ha⟩
  right_inv W := le_antisymm (sSup_le fun _ hV => by obtain ⟨_, h⟩ := hV; exact h) (le_sSup (show W ∈ _ from ⟨homOfLE le_top, (le_rfl : W ≤ W)⟩))

/-- URU5jgTvjhU-25977 (7:12:57) [prop] `X` is connected iff `e` is not the sum of two disjoint
non-initial subobjects, i.e. `X` is not the union of two disjoint nonempty open sets. -/
theorem preconnected_iff_opens (Z : Type*) [TopologicalSpace Z] :
    PreconnectedSpace Z ↔
      ∀ U V : Opens Z, U ⊔ V = ⊤ → U ⊓ V = ⊥ → U = ⊥ ∨ V = ⊥ := by
  rw [preconnectedSpace_iff_clopen]
  constructor
  · intro h U V hUV hdisj
    have hU : (U : Set Z) = (V : Set Z)ᶜ := by
      ext x
      have h1 := congrArg (fun W : Opens Z => x ∈ W) hUV
      have h2 := congrArg (fun W : Opens Z => x ∈ W) hdisj
      simp at h1 h2
      constructor
      · exact fun hx hV => h2 hx hV
      · intro hV
        rcases h1 with h | h
        · exact h
        · exact absurd h hV
    rcases h U ⟨hU ▸ V.2.isClosed_compl, U.2⟩ with h' | h'
    · left; ext x; simp [h']
    · right; ext x
      have : x ∈ (U : Set Z) := h' ▸ trivial
      rw [hU] at this
      simpa using this
  · intro h s hs
    rcases h ⟨s, hs.2⟩ ⟨sᶜ, hs.1.isOpen_compl⟩ (by ext x; simp) (by ext x; simp) with h' | h'
    · left; exact congrArg (fun W : Opens Z => (W : Set Z)) h'
    · right
      have := congrArg (fun W : Opens Z => (W : Set Z)) h'
      simpa using this

section Empty

variable {C : Type*} [Category C] [HasInitial C] [HasTerminal C]

/-- In a category with strict initial objects, `∅ → e` is an isomorphism iff every object is
initial. -/
theorem isIso_initial_to_terminal_iff [HasStrictInitialObjects C] :
    IsIso (initial.to (⊤_ C)) ↔ ∀ Z : C, Nonempty (IsInitial Z) := by
  constructor
  · intro _ Z
    have : IsIso (terminal.from Z ≫ inv (initial.to (⊤_ C))) := initialIsInitial.isIso_to _
    exact ⟨IsInitial.ofIso initialIsInitial
      (asIso (terminal.from Z ≫ inv (initial.to (⊤_ C)))).symm⟩
  · intro h
    exact ⟨⟨(h (⊤_ C)).some.to _, initialIsInitial.hom_ext _ _, terminalIsTerminal.hom_ext _ _⟩⟩

omit [HasTerminal C] in
/-- A category in which every object is initial is equivalent to the point (and conversely, for a
category with an initial object). -/
theorem allInitial_iff_equiv_point :
    (∀ Z : C, Nonempty (IsInitial Z)) ↔ Nonempty (C ≌ Discrete PUnit.{1}) := by
  constructor
  · intro h
    have : (Functor.star C).Faithful := ⟨fun {X Y} _ _ _ => (h X).some.hom_ext _ _⟩
    have : (Functor.star C).Full := ⟨fun {X Y} _ => ⟨(h X).some.to Y, Subsingleton.elim _ _⟩⟩
    have : (Functor.star C).EssSurj := ⟨fun Y => ⟨⊥_ C, ⟨eqToIso (Subsingleton.elim _ _)⟩⟩⟩
    have : (Functor.star C).IsEquivalence := {}
    exact ⟨(Functor.star C).asEquivalence⟩
  · rintro ⟨e⟩ Z
    exact ⟨IsInitial.ofUniqueHom
      (fun Y => e.fullyFaithfulFunctor.preimage (eqToHom (Subsingleton.elim _ _)))
      (fun Y f => e.functor.map_injective (Subsingleton.elim _ _))⟩

end Empty

/-- The sheaf with one section over every open set. -/
abbrev unitSheafOn (X : TopCat.{u}) : TopCat.Sheaf (Type u) X :=
  ⟨X.presheafToTypes fun _ => PUnit.{u + 1}, TopCat.Presheaf.toTypes_isSheaf _ _⟩

/-- On the empty space every sheaf is initial. -/
def isInitial_of_isEmpty [IsEmpty X] (F : TopCat.Sheaf (Type u) X) : IsInitial F := by
  have hbot : ∀ U : Opens X, U = ⊥ := fun U => by ext x; exact isEmptyElim x
  exact IsInitial.ofUniqueHom
    (fun G => ObjectProperty.homMk
      { app := fun U => ↾fun _ => (uniqueOfEqBot G (hbot U.unop)).default
        naturality := fun _ V _ => by
          ext; exact (uniqueOfEqBot G (hbot V.unop)).instSubsingleton.elim _ _ })
    (fun G f => by
      apply Sheaf.hom_ext
      ext U s
      exact (uniqueOfEqBot G (hbot U.unop)).instSubsingleton.elim _ _)

/-- URU5jgTvjhU-26075 (7:14:35) [prop] and URU5jgTvjhU-33121 (9:12:01) [prop] `X` is empty iff
`∅ → e` is an isomorphism in `Sh(X)`. -/
theorem sheaf_isIso_initial_iff :
    IsIso (initial.to (⊤_ (Sheaf (Opens.grothendieckTopology X) (Type u)))) ↔ IsEmpty X := by
  rw [isIso_initial_to_terminal_iff]
  constructor
  · intro h
    refine ⟨fun x => ?_⟩
    let f := (h (unitSheafOn X)).some.to (opensSheaf ⊥)
    have : (⊤ : Opens X) ≤ ⊥ := (f.hom.app (op ⊤) fun _ => PUnit.unit).le
    exact (this (show x ∈ (⊤ : Opens X) from trivial) : x ∈ (⊥ : Opens X))
  · intro _ Z
    exact ⟨isInitial_of_isEmpty Z⟩

/-- URU5jgTvjhU-26075 (7:14:35) [prop] and URU5jgTvjhU-32997 (9:09:57) [prop] `X` is empty iff
`Sh(X)` is equivalent to the point category; in particular `Sh(∅)` is the « empty topos ». -/
theorem sheaf_equiv_point_iff :
    Nonempty (Sheaf (Opens.grothendieckTopology X) (Type u) ≌ Discrete PUnit.{1}) ↔ IsEmpty X := by
  rw [← allInitial_iff_equiv_point, ← isIso_initial_to_terminal_iff, sheaf_isIso_initial_iff]

/-- URU5jgTvjhU-26202 (7:16:42) [def] `H^i(X, F)`: Mathlib's sheaf cohomology `Sheaf.H`, the
`Ext` groups from the constant sheaf `ℤ` in the abelian category of abelian sheaves (which has
enough injectives, `Part01.ab_enoughInjectives`). -/
abbrev sheafH (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) : Type _ :=
  Sheaf.H F n

/-- URU5jgTvjhU-26328 (7:18:48) [def] `H^i(X, M) = H^i(X, M_X)` for an abelian group `M`. -/
abbrev sheafHConst (M : AddCommGrpCat.{u}) (n : ℕ) : Type _ :=
  Sheaf.H ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj M) n

/-- URU5jgTvjhU-26392 (7:19:52) [prop] `X` is connected iff `ℤ → H⁰(X, ℤ)` (the locally constant
maps `X → ℤ`) is surjective. -/
theorem preconnected_iff_const_surjective (Z : Type*) [TopologicalSpace Z] :
    PreconnectedSpace Z ↔ Function.Surjective (LocallyConstant.const Z : ℤ → LocallyConstant Z ℤ) := by
  classical
  constructor
  · intro _ f
    rcases isEmpty_or_nonempty Z with hZ | ⟨⟨z⟩⟩
    · exact ⟨0, by ext x; exact isEmptyElim x⟩
    · exact ⟨f z, by ext x; exact (f.isLocallyConstant.apply_eq_of_preconnectedSpace x z).symm⟩
  · intro h
    rw [preconnectedSpace_iff_clopen]
    intro s hs
    obtain ⟨n, hn⟩ := h ((LocallyConstant.ofIsClopen hs).map fun i => (i.val : ℤ))
    by_cases hne : s.Nonempty
    · right
      obtain ⟨z, hz⟩ := hne
      ext x
      simp only [Set.mem_univ, iff_true]
      have h1 := LocallyConstant.congr_fun hn x
      have h2 := LocallyConstant.congr_fun hn z
      simp only [LocallyConstant.coe_const, Function.const_apply, LocallyConstant.map_apply,
        Function.comp_apply] at h1 h2
      by_contra hx
      have e1 : LocallyConstant.ofIsClopen hs z = 0 := by simp [LocallyConstant.ofIsClopen, hz]
      have e2 : LocallyConstant.ofIsClopen hs x = 1 := by simp [LocallyConstant.ofIsClopen, hx]
      rw [e1] at h2; rw [e2] at h1
      rw [h1] at h2
      simp at h2
    · left; exact Set.not_nonempty_iff_eq_empty.1 hne

/-- URU5jgTvjhU-26392 (7:19:52) [prop] `X` is connected and nonempty iff `ℤ → H⁰(X, ℤ)` is
bijective. -/
theorem connected_iff_const_bijective (Z : Type*) [TopologicalSpace Z] :
    ConnectedSpace Z ↔ Function.Bijective (LocallyConstant.const Z : ℤ → LocallyConstant Z ℤ) := by
  rw [connectedSpace_iff_univ, _root_.IsConnected, ← preconnectedSpace_iff_univ,
    preconnected_iff_const_surjective, Function.Bijective, ← Set.nonempty_iff_univ_nonempty]
  constructor
  · rintro ⟨⟨z⟩, hs⟩
    exact ⟨fun a b hab => by simpa using LocallyConstant.congr_fun hab z, hs⟩
  · rintro ⟨hinj, hs⟩
    refine ⟨?_, hs⟩
    by_contra hZ
    rw [not_nonempty_iff] at hZ
    exact absurd (hinj (a₁ := 0) (a₂ := 1) (by ext x; exact isEmptyElim x)) (by simp)

/-! ## Covering spaces and torsors -/

section Torsor

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

open CartesianMonoidalCategory MonObj in
/-- URU5jgTvjhU-26911 (7:28:31) [def] A `G`-torsor is an object `P` with an action of the group
object `G` such that `G × P → P × P`, `(g, p) ↦ (gp, p)`, is an isomorphism and `P → e` an
epimorphism. -/
structure IsTorsorObj (G P : C) [GrpObj G] (act : G ⊗ P ⟶ P) : Prop where
  one_act : (λ_ P).inv ≫ (η[G] ▷ P) ≫ act = 𝟙 P
  mul_act : (μ[G] ▷ P) ≫ act = (α_ G G P).hom ≫ (G ◁ act) ≫ act
  isIso : IsIso (lift act (snd G P))
  epi : Epi (toUnit P)

end Torsor

/-- URU5jgTvjhU-26975 (7:29:35) [prop] `G ↦ G_X = ∐_G e` is left exact. -/
example : PreservesFiniteLimits (constantSheaf (Opens.grothendieckTopology X) (Type u)) :=
  inferInstance

/-! ## Stacks and gerbes -/

/-- URU5jgTvjhU-27104 (7:31:44) [def] A fibred category over `𝒪(X)`: a pseudofunctor
`𝒪(X)ᵒᵖ → Cat` (restriction functors, transitive up to coherent isomorphism). -/
abbrev FibredCategoryOver (X : TopCat.{u}) : Type _ :=
  Pseudofunctor (LocallyDiscrete (Opens X)ᵒᵖ) Cat.{u, u + 1}

/-- URU5jgTvjhU-27291 (7:34:51) [def] A fibred category is a stack if morphisms glue (the presheaves
`𝓗om` are sheaves) and descent data are effective (Mathlib's `Pseudofunctor.IsStack`). -/
abbrev IsStackOver (F : FibredCategoryOver X) : Prop :=
  F.IsStack (Opens.grothendieckTopology X)

/-- URU5jgTvjhU-27167 (7:32:47) [ex] The fibred category `U ↦ Sh(U)` (Mathlib's
`pseudofunctorOver`, with `Sh(𝒪(X)/U) ≃ Sh(U)`). -/
abbrev sheavesFibred (X : TopCat.{u}) :=
  (Opens.grothendieckTopology X).pseudofunctorOver (Type u)

/-- URU5jgTvjhU-27873 (7:44:33) [def] A stack over a category `ℰ`: descent along epimorphic
families, here for the canonical topology of `ℰ`. -/
abbrev IsStackOverCategory {E : Type*} [Category E] (F : Pseudofunctor (LocallyDiscrete Eᵒᵖ) Cat) :
    Prop :=
  F.IsStack (Sheaf.canonicalTopology E)

/-! ## Gluing and quotient topoi -/

/-- URU5jgTvjhU-28139 (7:48:59) [prop] The open sets of a sum `∐ Xᵢ` are the families of open sets
of the `Xᵢ`: `𝒪(∐ Xᵢ) ≃ ∏ 𝒪(Xᵢ)`, the lattice isomorphism underlying `Sh(∐ Xᵢ) ≃ ∏ Sh(Xᵢ)`. -/
def opensSigmaIso {ι : Type*} (Z : ι → Type*) [∀ i, TopologicalSpace (Z i)] :
    Opens (Σ i, Z i) ≃o ∀ i, Opens (Z i) where
  toFun U i := ⟨Sigma.mk i ⁻¹' U, U.2.preimage continuous_sigmaMk⟩
  invFun V := ⟨{p | p.2 ∈ V p.1}, isOpen_sigma_iff.2 fun i => (V i).2⟩
  left_inv U := rfl
  right_inv V := rfl
  map_rel_iff' {U V} := by
    constructor
    · intro h ⟨i, z⟩ hz
      exact h i hz
    · intro h i z hz
      exact h hz

end

end Buffalo.Topos.Part02
