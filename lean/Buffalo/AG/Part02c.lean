import Buffalo.AG.Part02b

/-!
# Buffalo, algebraic geometry, part 02 (c): 11 June 1973 (beginning)

The entries of `docs/buffalo-ag/index.tex` for the session of 11 June 1973 up to 8:34:57 (video
`51wmmpHand0`): group objects in a category embedded in functors, group structures on affine
spaces as Hopf algebras, and complements on the spectrum (noetherian spaces, irreducible
components of open sets, connected components). Notation as in `Buffalo.AG.Part02a`.

Not formalised (no carrier in mathlib): smoothness of reduced affine algebraic groups over an
algebraically closed field and the rationality of connected ones (entry 29738), and the
comparison of Zariski and complex-analytic connectedness of `X(ℂ)` (entry 26013, in `Part02b`).
-/

open CategoryTheory Limits TopologicalSpace PrimeSpectrum

universe u

namespace Buffalo.AG.Part02

open Buffalo.AG.Part01

noncomputable section

section June11

variable (k : Type u) [CommRing k]

/-! ### Group objects and Hopf algebras -/

/-- 51wmmpHand0-29480 (8:11:20) [def] A group in a category `C` embedded in functors: an object
`G` with a group structure on each `G(Z) = Hom(Z, G)`, functorial in `Z` (a lift of `yoneda G` to
groups); no products and no final object are required. -/
structure GroupOnPoints {C : Type*} [Category C] (G : C) where
  /-- The groups `Hom(Z, G)`, functorially in `Z`. -/
  F : Cᵒᵖ ⥤ GrpCat
  /-- Their underlying sets are the `Hom(Z, G)`. -/
  iso : F ⋙ forget GrpCat ≅ yoneda.obj G

/-- 51wmmpHand0-29867 (8:17:47) [ex] `A = K[T_ij][Δ⁻¹]` represents `GL_n`: its points with values
in `K'` are the matrices with invertible determinant (`Buffalo.AG.Part01.prop_17469`). -/
theorem ex_29867 (n : Type u) [Fintype n] [DecidableEq n] (k' : Type u) [CommRing k']
    [Algebra k k'] :
    Function.Injective (fun u : OGL k n →ₐ[k] k' =>
        (Matrix.of fun i j => u (algebraMap (MvPolynomial (n × n) k) (OGL k n)
          (MvPolynomial.X (i, j))) : Matrix n n k')) ∧
      Set.range (fun u : OGL k n →ₐ[k] k' =>
        (Matrix.of fun i j => u (algebraMap (MvPolynomial (n × n) k) (OGL k n)
          (MvPolynomial.X (i, j))) : Matrix n n k')) = {M | IsUnit M.det} :=
  prop_17469 k n k'

/-- 51wmmpHand0-29996 (8:19:56) [prop] A monoid structure on the affine space of `A` is a
comultiplication `A → A ⊗_K A` with counit satisfying the axioms: monoid objects of `𝒞` are the
commutative bialgebras (mathlib: `commBialgCatEquivComonCommAlgCat`). -/
def prop_29996 : CommBialgCat k ≌ (Mon (CommAlgCat k)ᵒᵖ)ᵒᵖ :=
  commBialgCatEquivComonCommAlgCat k

/-- 51wmmpHand0-29996 (8:19:56) [prop] Group objects of `𝒞` are the commutative Hopf algebras
(mathlib: `commHopfAlgCatEquivCogrpCommAlgCat`). -/
def prop_29996_hopf : CommHopfAlgCat k ≌ (CategoryTheory.Grp (CommAlgCat k)ᵒᵖ)ᵒᵖ :=
  commHopfAlgCatEquivCogrpCommAlgCat k

/-- 51wmmpHand0-30063 (8:21:03) [prop] Inversion `g ↦ g⁻¹` corresponds to an automorphism `σ` of
the `K`-algebra `A` (the antipode; mathlib: `CommAlgCat.inv_op_of_unop_hom`,
`HopfAlgebra.antipodeAlgHom`): if `V_A` carries a functorial group structure, then
`g⁻¹ = g ∘ σ` for every point `g`, and `σ ∘ σ = id`. -/
theorem prop_30063 (A : Type u) [CommRing A] [Algebra k A] (G : CommAlgCat.{u} k ⥤ GrpCat.{u})
    (e : G ⋙ forget GrpCat ≅ V k A) :
    ∃ σ : A ≃ₐ[k] A, ∀ (k' : CommAlgCat.{u} k) (x : G.obj k'),
      pt k (e.hom.app k' x⁻¹) = (pt k (e.hom.app k' x)).comp σ.toAlgHom := by
  let ι : ∀ k' : CommAlgCat.{u} k, (V k A).obj k' → (V k A).obj k' := fun k' y =>
    e.hom.app k' ((e.inv.app k' y : G.obj k')⁻¹)
  have hnat : ∀ {k' k'' : CommAlgCat.{u} k} (f : k' ⟶ k'') (y : (V k A).obj k'),
      ι k'' ((V k A).map f y) = (V k A).map f (ι k' y) := by
    intro k' k'' f y
    simp only [ι]
    have h1 := NatTrans.naturality_apply e.inv f y
    have h3 : ((G.map f).hom (e.inv.app k' y : G.obj k'))⁻¹ =
        (G.map f).hom ((e.inv.app k' y : G.obj k')⁻¹) := (map_inv (G.map f).hom _).symm
    have h2 := NatTrans.naturality_apply e.hom f ((e.inv.app k' y : G.obj k')⁻¹)
    rw [h1]
    exact (congrArg (e.hom.app k'') h3).trans h2
  let A' := CommAlgCat.of k A
  let σ₀ : A →ₐ[k] A := pt k (ι A' (AlgHom.id k A))
  have hform : ∀ (k' : CommAlgCat.{u} k) (y : (V k A).obj k'), ι k' y = (pt k y).comp σ₀ := by
    intro k' y
    have := hnat (hm k (A := A') (B := k') (pt k y)) (AlgHom.id k A)
    exact this
  have hinv : ∀ (k' : CommAlgCat.{u} k) (y : (V k A).obj k'), ι k' (ι k' y) = y := by
    intro k' y
    simp only [ι, Iso.hom_inv_id_app_apply, inv_inv]
    exact Iso.inv_hom_id_app_apply e k' y
  have hσσ : σ₀.comp σ₀ = AlgHom.id k A := by
    have h := hinv A' (AlgHom.id k A)
    have h2 : pt k (ι A' (ι A' (AlgHom.id k A))) = (pt k (ι A' (AlgHom.id k A))).comp σ₀ :=
      congrArg (pt k) (hform A' _)
    exact h2.symm.trans h
  refine ⟨AlgEquiv.ofAlgHom σ₀ σ₀ hσσ hσσ, fun k' x => ?_⟩
  have := hform k' (e.hom.app k' x)
  simp only [ι, Iso.hom_inv_id_app_apply] at this
  exact this

/-! ### Complements on the spectrum -/

/-- 51wmmpHand0-30192 (8:23:12) [prop] The `V(J)` are the closed sets of `Spec A`, which is
quasi-compact; the closed sets correspond to the radical ideals (`prop_23031`). -/
theorem prop_30192 (A : Type*) [CommRing A] :
    (∀ Z : Set (PrimeSpectrum A), IsClosed Z ↔ ∃ J : Ideal A, Z = zeroLocus J) ∧
      CompactSpace (PrimeSpectrum A) ∧
      (∀ Z : Set (PrimeSpectrum A), IsClosed Z → zeroLocus (vanishingIdeal Z : Set A) = Z) ∧
      (∀ J : Ideal A, J.IsRadical → vanishingIdeal (zeroLocus (J : Set A)) = J) :=
  ⟨prop_23031.1, inferInstance, prop_23031.2⟩

/-- 51wmmpHand0-30258 (8:24:18) [prop] Primes correspond to irreducible closed sets and to points;
`Spec A` is sober, and empty iff `A = 0` (`prop_25035`, `prop_25167`, `prop_23676`). -/
theorem prop_30258 (A : Type*) [CommRing A] :
    (∀ J : Ideal A, J.IsPrime → IsIrreducible (zeroLocus (J : Set A))) ∧
      (∀ Z : Set (PrimeSpectrum A), IsIrreducible Z → IsClosed Z → ∃! x, closure {x} = Z) ∧
      (IsEmpty (PrimeSpectrum A) ↔ Subsingleton A) :=
  ⟨fun J hJ => (prop_25035 J).1.2 (by rw [hJ.isRadical.radical]; exact hJ), prop_23357.2,
    prop_23676 A⟩

/-- 51wmmpHand0-30323 (8:25:23) [prop] `Spec A` is irreducible iff its radical (the nilradical
`rad A = nil A`) is prime, i.e. `A / rad A` is an integral domain (`prop_23801`). -/
theorem prop_30323 (A : Type*) [CommRing A] :
    (IrreducibleSpace (PrimeSpectrum A) ↔ (nilradical A).IsPrime) ∧
      (IrreducibleSpace (PrimeSpectrum A) ↔ IsDomain (A ⧸ nilradical A)) :=
  ⟨(prop_23801 A).trans (Ideal.Quotient.isDomain_iff_prime _), prop_23801 A⟩

/-- A union of two accessible closed sets is accessible (for `⊂`). -/
theorem acc_sup {X : Type*} [TopologicalSpace X] {a b : Closeds X}
    (ha : Acc (· < ·) a) (hb : Acc (· < ·) b) : Acc (· < ·) (a ⊔ b) := by
  induction ha generalizing b with
  | intro a _ iha =>
    induction hb with
    | intro b hb' ihb =>
      refine Acc.intro _ fun W hW => ?_
      have hWeq : W = (W ⊓ a) ⊔ (W ⊓ b) := by rw [← inf_sup_left, inf_eq_left.2 hW.le]
      by_cases hWa : W ⊓ a < a
      · rw [hWeq]
        apply iha _ hWa
        rcases (inf_le_right : W ⊓ b ≤ b).lt_or_eq with h | h
        · exact hb' _ h
        · rw [h]; exact Acc.intro b hb'
      · have hWa' : W ⊓ a = a := (inf_le_right.lt_or_eq).resolve_left hWa
        have ha' : a ≤ W := hWa' ▸ inf_le_left
        have hWb : W ⊓ b < b := by
          refine lt_of_le_of_ne inf_le_right fun h => ?_
          have : b ≤ W := h ▸ inf_le_left
          exact hW.ne (le_antisymm hW.le (sup_le ha' this))
        have := ihb _ hWb
        have e : a ⊔ W ⊓ b = W := by
          conv_rhs => rw [hWeq]
          rw [hWa']
        rwa [e] at this

/-- A finite union of accessible closed sets is accessible. -/
theorem acc_finsetSup {X : Type*} [TopologicalSpace X] (s : Finset (Closeds X))
    (h : ∀ c ∈ s, Acc (· < ·) c) : Acc (· < ·) (s.sup id) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Acc.intro _ fun y hy => absurd hy not_lt_bot
  | insert a s _ ih =>
    rw [Finset.sup_insert]
    exact acc_sup (h a (Finset.mem_insert_self a s))
      (ih fun c hc => h c (Finset.mem_insert_of_mem hc))

/-- 51wmmpHand0-30451 (8:27:31) [prop] A space is noetherian iff (a) every closed set has finitely
many irreducible components and (b) every decreasing sequence of irreducible closed sets is
stationary (well-foundedness of `⊂` on irreducible closed sets). -/
theorem prop_30451 (X : Type*) [TopologicalSpace X] :
    NoetherianSpace X ↔ (∀ Z : Set X, IsClosed Z → (irreducibleComponents Z).Finite) ∧
      WellFounded (fun s t : {s : Set X // IsIrreducible s ∧ IsClosed s} => s.1 ⊂ t.1) := by
  have h1 : NoetherianSpace X ↔ WellFoundedLT (Closeds X) := (noetherianSpace_TFAE X).out 1 2
  constructor
  · intro hN
    refine ⟨fun Z _ => NoetherianSpace.finite_irreducibleComponents, ?_⟩
    let f : {s : Set X // IsIrreducible s ∧ IsClosed s} → Closeds X := fun s => ⟨s.1, s.2.2⟩
    have hwf : WellFounded ((· < ·) : Closeds X → Closeds X → Prop) := wellFounded_lt
    exact Subrelation.wf (r := InvImage (· < ·) f) (fun {s t} h => h) (InvImage.wf f hwf)
  · rintro ⟨ha, hb⟩
    classical
    have L1 : ∀ Z : Closeds X, (∀ (D : Set X) (hD : IsIrreducible D) (hDc : IsClosed D),
        D ⊆ Z → Acc (· < ·) (⟨D, hDc⟩ : Closeds X)) → Acc (· < ·) Z := by
      intro Z hZ
      let g : Set Z → Closeds X := fun C => ⟨closure (Subtype.val '' C), isClosed_closure⟩
      have hF := ha Z Z.isClosed
      have heq : Z = (hF.toFinset.image g).sup id := by
        apply le_antisymm
        · intro z hz
          obtain ⟨C, hC, hzC⟩ := Set.mem_sUnion.1
            ((sUnion_irreducibleComponents (X := Z)).symm ▸ Set.mem_univ (⟨z, hz⟩ : Z))
          have hle : g C ≤ (hF.toFinset.image g).sup id :=
            Finset.le_sup (f := id) (Finset.mem_image_of_mem g (hF.mem_toFinset.2 hC))
          exact hle (subset_closure ⟨⟨z, hz⟩, hzC, rfl⟩)
        · refine Finset.sup_le fun c hc => ?_
          obtain ⟨C, -, rfl⟩ := Finset.mem_image.1 hc
          exact closure_minimal (by rintro _ ⟨y, -, rfl⟩; exact y.2) Z.isClosed
      rw [heq]
      refine acc_finsetSup _ fun c hc => ?_
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hc
      have hCi : IsIrreducible (closure (Subtype.val '' C)) :=
        ((hF.mem_toFinset.1 hC).1.image _ continuous_subtype_val.continuousOn).closure
      exact hZ _ hCi isClosed_closure
        (closure_minimal (by rintro _ ⟨y, -, rfl⟩; exact y.2) Z.isClosed)
    have L2 : ∀ C : {s : Set X // IsIrreducible s ∧ IsClosed s},
        Acc (· < ·) (⟨C.1, C.2.2⟩ : Closeds X) := by
      intro C
      induction C using hb.induction with
      | _ C ih =>
        refine Acc.intro _ fun W hW => L1 W fun D hD hDc hDW => ?_
        have hlt : (W : Set X) ⊂ C.1 := hW
        exact ih ⟨D, hD, hDc⟩ (Set.ssubset_of_subset_of_ssubset hDW hlt)
    rw [h1]
    exact ⟨fun Z => L1 Z fun D hD hDc _ => L2 ⟨D, hD, hDc⟩⟩

/-- 51wmmpHand0-30645 (8:30:45) [prop] For `A` finitely generated over a field `K`, the set `X₀`
of closed points is very dense in `Spec A` (`prop_28733`: the inclusion is a
quasi-homeomorphism); if `K` is algebraically closed, `X₀ = X(K)` (`prop_29114`). -/
theorem prop_30645 (K A : Type u) [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A] :
    VeryDense (closedPoints (PrimeSpectrum A)) ∧
      ([IsAlgClosed K] → ∀ x : PrimeSpectrum A, x ∈ closedPoints (PrimeSpectrum A) ↔
        ∃ u : A →ₐ[K] K, RingHom.ker u = x.asIdeal) :=
  ⟨prop_28733 K A, fun x => (prop_29114 K A).2.2 x⟩

/-- 51wmmpHand0-30897 (8:34:57) [prop] The irreducible components of an open set `U` are the
traces on `U` of the components of the space that meet `U`. -/
theorem prop_30897 {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsOpen U) :
    irreducibleComponents U =
      {T | ∃ Z ∈ irreducibleComponents X, (Z ∩ U).Nonempty ∧ T = Subtype.val ⁻¹' Z} := by
  have hpre : ∀ Z ∈ irreducibleComponents X, (Z ∩ U).Nonempty →
      Subtype.val ⁻¹' Z ∈ irreducibleComponents U := fun Z hZ hne =>
    preimage_mem_irreducibleComponents hZ hU.isOpenEmbedding_subtypeVal
      (by rwa [Subtype.range_coe])
  ext T
  constructor
  · intro hT
    obtain ⟨Z, hZ, hTZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
      (hT.1.image _ continuous_subtype_val.continuousOn)
    obtain ⟨t, ht⟩ := hT.1.nonempty
    have hne : (Z ∩ U).Nonempty := ⟨t, hTZ ⟨t, ht, rfl⟩, t.2⟩
    refine ⟨Z, hZ, hne, ?_⟩
    have hsub : T ⊆ Subtype.val ⁻¹' Z := Set.image_subset_iff.1 hTZ
    exact le_antisymm hsub (hT.2 (hpre Z hZ hne).1 hsub)
  · rintro ⟨Z, hZ, hne, rfl⟩
    exact hpre Z hZ hne

/-- The trace of a preirreducible set on an open set is preirreducible. -/
theorem preirreducible_inter_isOpen {X : Type*} [TopologicalSpace X] {Z W : Set X}
    (hZ : IsPreirreducible Z) (hW : IsOpen W) : IsPreirreducible (Z ∩ W) := by
  rintro u v hu hv ⟨a, ⟨haZ, haW⟩, hau⟩ ⟨b, ⟨hbZ, hbW⟩, hbv⟩
  obtain ⟨c, hcZ, ⟨hcu, hcW⟩, hcv, -⟩ :=
    hZ (u ∩ W) (v ∩ W) (hu.inter hW) (hv.inter hW) ⟨a, haZ, hau, haW⟩ ⟨b, hbZ, hbv, hbW⟩
  exact ⟨c, ⟨hcZ, hcW⟩, hcu, hcv⟩

/-- 51wmmpHand0-30897 (8:34:57) [prop] If `X` has finitely many irreducible components, `X` is
locally connected, and `x`, `y` lie in the same connected component iff a chain of irreducible
components joins them, two consecutive ones meeting. -/
theorem prop_30897_conn {X : Type*} [TopologicalSpace X] (hfin : (irreducibleComponents X).Finite) :
    LocallyConnectedSpace X ∧ ∀ x y : X, y ∈ connectedComponent x ↔
      Relation.ReflTransGen (fun a b => ∃ Z ∈ irreducibleComponents X, a ∈ Z ∧ b ∈ Z) x y := by
  have hcl : ∀ F ⊆ irreducibleComponents X, IsClosed (⋃₀ F) := fun F hF =>
    (hfin.subset hF).isClosed_sUnion fun Z hZ => isClosed_of_mem_irreducibleComponents Z (hF hZ)
  constructor
  · rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    intro x N hN
    let C := ⋃₀ {Z ∈ irreducibleComponents X | x ∉ Z}
    have hC : IsClosed C := hcl _ (Set.sep_subset _ _)
    let W := interior N ∩ Cᶜ
    have hxW : x ∈ W := ⟨mem_interior_iff_mem_nhds.2 hN, fun hx => by
      obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.1 hx
      exact hZ.2 hxZ⟩
    have hWo : IsOpen W := isOpen_interior.inter hC.isOpen_compl
    refine ⟨W, Set.inter_subset_left.trans interior_subset, hWo, hxW, ⟨x, hxW⟩, ?_⟩
    have hWeq : W = ⋃₀ {S | ∃ Z ∈ irreducibleComponents X, x ∈ Z ∧ S = Z ∩ W} := by
      ext y
      constructor
      · intro hy
        obtain ⟨Z, hZ, hyZ⟩ := Set.mem_sUnion.1
          ((sUnion_irreducibleComponents (X := X)).symm ▸ Set.mem_univ y)
        by_cases hxZ : x ∈ Z
        · exact ⟨Z ∩ W, ⟨Z, hZ, hxZ, rfl⟩, hyZ, hy⟩
        · exact absurd (Set.mem_sUnion_of_mem hyZ
            (show Z ∈ {Z ∈ irreducibleComponents X | x ∉ Z} from ⟨hZ, hxZ⟩)) hy.2
      · rintro ⟨_, ⟨Z, -, -, rfl⟩, hy⟩
        exact hy.2
    rw [hWeq]
    refine isPreconnected_sUnion x _ (by rintro S ⟨Z, -, hxZ, rfl⟩; exact ⟨hxZ, hxW⟩) ?_
    rintro S ⟨Z, hZ, -, rfl⟩
    exact (preirreducible_inter_isOpen hZ.1.isPreirreducible hWo).isPreconnected
  · intro x y
    constructor
    · intro hy
      let R := fun a b : X => ∃ Z ∈ irreducibleComponents X, a ∈ Z ∧ b ∈ Z
      let S := {z | Relation.ReflTransGen R x z}
      have hcomp : ∀ Z ∈ irreducibleComponents X, (Z ∩ S).Nonempty → Z ⊆ S := by
        rintro Z hZ ⟨a, haZ, haS⟩ z hz
        exact Relation.ReflTransGen.tail haS ⟨Z, hZ, haZ, hz⟩
      have hS : S = ⋃₀ {Z ∈ irreducibleComponents X | Z ⊆ S} := by
        ext z
        refine ⟨fun hz => ?_, fun ⟨Z, ⟨_, hZS⟩, hz⟩ => hZS hz⟩
        obtain ⟨Z, hZ, hzZ⟩ := Set.mem_sUnion.1
          ((sUnion_irreducibleComponents (X := X)).symm ▸ Set.mem_univ z)
        exact ⟨Z, ⟨hZ, hcomp Z hZ ⟨z, hzZ, hz⟩⟩, hzZ⟩
      have hSc : Sᶜ = ⋃₀ {Z ∈ irreducibleComponents X | Z ⊆ Sᶜ} := by
        ext z
        refine ⟨fun hz => ?_, fun ⟨Z, ⟨_, hZS⟩, hz⟩ => hZS hz⟩
        obtain ⟨Z, hZ, hzZ⟩ := Set.mem_sUnion.1
          ((sUnion_irreducibleComponents (X := X)).symm ▸ Set.mem_univ z)
        refine ⟨Z, ⟨hZ, fun w hw hwS => hz ?_⟩, hzZ⟩
        exact hcomp Z hZ ⟨w, hw, hwS⟩ hzZ
      have hclo : IsClopen S := by
        refine ⟨?_, ?_⟩
        · rw [hS]; exact hcl _ (Set.sep_subset _ _)
        · rw [← isClosed_compl_iff, hSc]; exact hcl _ (Set.sep_subset _ _)
      exact hclo.connectedComponent_subset Relation.ReflTransGen.refl hy
    · intro h
      induction h with
      | refl => exact mem_connectedComponent
      | tail _ hbc ih =>
        obtain ⟨Z, hZ, hbZ, hcZ⟩ := hbc
        rw [connectedComponent_eq ih]
        exact hZ.1.isPreirreducible.isPreconnected.subset_connectedComponent hbZ hcZ

end June11

end

end Buffalo.AG.Part02
