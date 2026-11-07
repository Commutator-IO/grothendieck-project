import Buffalo.Groupes.Part01

/-!
# Buffalo, algebraic groups, Part 03 (c): group schemes over a field, height one, tori

Entries `3ULFIl_2Wis-14121` to `3ULFIl_2Wis-25487` of `docs/buffalo-groupes/index.tex` (session of
11 July 1973 and tape 3). Statuses in `docs/buffalo-groupes/lean/Part03.json`. The last section
settles the open question of Part 01 on the counit of a bialgebra (entry `_lTf_L0yvrU-10811`).

Conventions. A group scheme over `S` is a group object `G` of `Over S` (Mathlib's `GrpObj`,
`Over S` being cartesian monoidal through fibre products): `G ⊗ G` is `G ×_S G`, `μ`, `η`, `ι`
are the multiplication, unit section and inverse, and morphisms `T ⟶ G` form a group
(`open MonObj`). Affine group schemes over `k` are commutative Hopf algebras, as in Part 01.
-/

namespace Buffalo.Groupes.Part03

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  TensorProduct

universe u

/-! ## Group schemes over a field: separation, openness, torsors -/

section Abstract

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] (G : C) [GrpObj G]

/-- 3ULFIl_2Wis-14186 (3:56:26) [prop] The map `(g, h) ↦ g h⁻¹`. -/
noncomputable def divMap : G ⊗ G ⟶ G := fst G G * (snd G G)⁻¹

/-- 3ULFIl_2Wis-14186 (3:56:26) [prop] The diagonal of a group object is the inverse image of the
unit section under `(g, h) ↦ g h⁻¹`. -/
theorem diag_isPullback :
    IsPullback (lift (𝟙 G) (𝟙 G)) (toUnit G) (divMap G) η := by
  refine IsPullback.of_isLimit' ⟨by
    rw [divMap, comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, mul_inv_cancel, Hom.one_def]⟩ ?_
  refine PullbackCone.IsLimit.mk _ (fun s ↦ s.fst ≫ fst G G) (fun s ↦ ?_) (fun s ↦ ?_)
    (fun s m h₁ _ ↦ ?_)
  · have e : s.fst ≫ fst G G = s.fst ≫ snd G G := by
      have : (s.fst ≫ fst G G) * (s.fst ≫ snd G G)⁻¹ = 1 := by
        have h := s.condition
        simp only [divMap, comp_mul, GrpObj.comp_inv] at h
        rw [h, toUnit_unique s.snd (toUnit _), ← Hom.one_def]
      exact mul_inv_eq_one.mp this
    ext <;> simp [e]
  · exact toUnit_unique _ _
  · simp [← h₁]

/-- 3ULFIl_2Wis-14253 (3:57:33) [prop] The shear `(g, x) ↦ (g x, x)` is an isomorphism. -/
noncomputable def shear : G ⊗ G ≅ G ⊗ G where
  hom := lift (fst G G * snd G G) (snd G G)
  inv := lift (fst G G * (snd G G)⁻¹) (snd G G)
  hom_inv_id := by ext <;> simp [comp_mul, GrpObj.comp_inv]
  inv_hom_id := by ext <;> simp [comp_mul]

/-- 3ULFIl_2Wis-14253 (3:57:33) [prop] The multiplication is the shear followed by the first
projection. -/
theorem mul_eq_shear_fst : μ[G] = (shear G).hom ≫ fst G G := by
  simp [shear, Hom.mul_def]

end Abstract

/-- 3ULFIl_2Wis-14186 (3:56:26) [prop] A group scheme over `S` whose unit section is a closed
immersion is separated. -/
theorem isSeparated_of_unit {S : Scheme} (G : Over S) [GrpObj G] [IsClosedImmersion η[G].left] :
    IsSeparated G.hom := by
  have hpb := (diag_isPullback G).map (Over.forget S)
  constructor
  have : IsClosedImmersion ((Over.forget S).map (lift (𝟙 G) (𝟙 G))) :=
    MorphismProperty.of_isPullback hpb.flip ‹_›
  have e : pullback.diagonal G.hom = (lift (𝟙 G) (𝟙 G)).left := by
    apply pullback.hom_ext <;> simp [Over.lift_left]
  rw [e]; exact this

/-- 3ULFIl_2Wis-14186 (3:56:26) [prop] Conversely the unit section of a separated group scheme is a
closed immersion. -/
theorem unit_of_isSeparated {S : Scheme} (G : Over S) [GrpObj G] [IsSeparated G.hom] :
    IsClosedImmersion η[G].left := by
  have : IsClosedImmersion (η[G].left ≫ G.hom) := by
    rw [Over.w η[G]]; exact (inferInstance : IsClosedImmersion (𝟙 S))
  exact IsClosedImmersion.of_comp _ G.hom

/-- 3ULFIl_2Wis-14121 (3:55:21) [prop] Every group scheme over a field is separated. -/
theorem isSeparated_over_field {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G] :
    IsSeparated G.hom :=
  isSeparated_of_unit G

/-- 3ULFIl_2Wis-14253 (3:57:33) [prop] For a group scheme locally of finite type over a field, the
composition law `G × G → G` is open. -/
theorem mul_isOpenMap {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G]
    [LocallyOfFiniteType G.hom] : IsOpenMap μ[G].left := by
  have : UniversallyOpen G.hom := UniversallyOpen.of_flat G.hom
  rw [mul_eq_shear_fst, Over.comp_left]
  exact (pullback.fst G.hom G.hom).isOpenMap.comp
    (Scheme.Hom.homeomorph ((Over.forget _).mapIso (shear G)).hom).isOpenMap

/-- 3ULFIl_2Wis-14392 (3:59:52) [prop] If `(g, x) ↦ (g x, x)` is an isomorphism `G × X ≅ X × X`
(with `X` locally of finite type over the field), the action `G × X → X` is open and flat. -/
theorem action_open_flat {K : Type u} [Field K] (G X : Over (Spec (.of K)))
    (a : G ⊗ X ⟶ X) [IsIso (lift a (snd G X))] [LocallyOfFiniteType X.hom] :
    IsOpenMap a.left ∧ Flat a.left := by
  have : UniversallyOpen X.hom := UniversallyOpen.of_flat X.hom
  have e : a = lift a (snd G X) ≫ fst X X := by simp
  have : IsIso (lift a (snd G X)).left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of K))).map (lift a (snd G X))))
  rw [e, Over.comp_left]
  refine ⟨(pullback.fst X.hom X.hom).isOpenMap.comp
    (Scheme.Hom.homeomorph (lift a (snd G X)).left).isOpenMap, ?_⟩
  have : Flat (fst X X).left := inferInstanceAs (Flat (pullback.fst X.hom X.hom))
  infer_instance

/-- 3ULFIl_2Wis-14457 (4:00:57) [def] `U V ⊂ X` is the image of `U × V` under the action. -/
def actImage {S : Scheme} {G X : Over S} (a : G ⊗ X ⟶ X) (U : Set G.left) (V : Set X.left) :
    Set X.left :=
  a.left '' ((fst G X).left ⁻¹' U ∩ (snd G X).left ⁻¹' V)

/-- 3ULFIl_2Wis-14457 (4:00:57) [def] If the action is open, `U V` is open. -/
theorem isOpen_actImage {S : Scheme} {G X : Over S} (a : G ⊗ X ⟶ X) (ha : IsOpenMap a.left)
    {U : Set G.left} {V : Set X.left} (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (actImage a U V) :=
  ha _ ((hU.preimage (fst G X).left.continuous).inter (hV.preimage (snd G X).left.continuous))

/-- 3ULFIl_2Wis-17756 (4:55:56) [def] A group scheme is totally disconnected if the connected
component of its neutral element is reduced to a point. -/
def IsTotallyDisconnectedGrp {K : Type u} [Field K] (G : Over (Spec (.of K))) [GrpObj G] : Prop :=
  ∀ s : (𝟙_ (Over (Spec (.of K)))).left, connectedComponent (η[G].left s) = {η[G].left s}

/-! ## Height one and restricted Lie algebras -/

section HeightOne

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- 3ULFIl_2Wis-19065 (5:17:45) [def] An affine group scheme `Spec A` has height one if its
Frobenius is trivial: `a ^ p = ε(a) ^ p` for all `a` (the comorphism of `F_G` is `a ↦ a ^ p`, that
of the trivial map is `a ↦ ε(a) ^ p`). -/
def IsHeightOne (A : Type u) [CommRing A] [Bialgebra k A] : Prop :=
  ∀ a : A, a ^ p = algebraMap k A (Coalgebra.counit a ^ p)

omit [CharP k p] in
/-- 3ULFIl_2Wis-19065 (5:17:45) [def] A group of height one is radicial: its augmentation ideal is
nil and `Spec A` is a single point. -/
theorem heightOne_radicial (A : Type u) [CommRing A] [Bialgebra k A] (h : IsHeightOne k p A) :
    (∀ a : A, Coalgebra.counit (R := k) a = 0 → a ^ p = 0) ∧ Subsingleton (PrimeSpectrum A) := by
  have hnil : ∀ a : A, Coalgebra.counit (R := k) a = 0 → a ^ p = 0 := fun a ha ↦ by
    rw [h a, ha, zero_pow (Fact.out : p.Prime).ne_zero, map_zero]
  refine ⟨hnil, ⟨fun P Q ↦ ?_⟩⟩
  let ε := Bialgebra.counitAlgHom k A
  have hsurj : Function.Surjective ε := fun r ↦ ⟨algebraMap k A r, by simp [ε]⟩
  have hmax : (RingHom.ker ε).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  have key : ∀ P : PrimeSpectrum A, P.asIdeal = RingHom.ker ε := fun P ↦
    (hmax.eq_of_le P.2.ne_top fun a ha ↦ P.2.mem_of_pow_mem p (by
      rw [hnil a (by simpa [ε] using ha)]; exact P.asIdeal.zero_mem)).symm
  exact PrimeSpectrum.ext ((key P).trans (key Q).symm)

attribute [local instance 100] LieRing.ofAssociativeRing in
/-- 3ULFIl_2Wis-19319 (5:21:59) [def] A restricted (`p`-)Lie algebra: a Lie algebra with a map
`x ↦ x^[p]`, here defined through a faithful representation in an associative `k`-algebra
carrying `x^[p]` to `x ^ p` (equivalent, by the restricted Poincaré–Birkhoff–Witt theorem, to the
definition with Jacobson's formula). -/
structure RestrictedLie (L : Type u) [LieRing L] [LieAlgebra k L] where
  /-- The `p`-map. -/
  pmap : L → L
  /-- A faithful representation turning the `p`-map into the `p`-th power. -/
  faithful : ∃ (B : AlgCat.{u} k) (φ : L →ₗ⁅k⁆ B),
    Function.Injective φ ∧ ∀ x, φ (pmap x) = φ x ^ p

omit [Fact p.Prime] [CharP k p] in
attribute [local instance 100] LieRing.ofAssociativeRing in
/-- 3ULFIl_2Wis-19319 (5:21:59) [def] The entry's definition is incomplete: on the abelian Lie
algebra `k`, the identity `x ↦ x` satisfies Jacobson's formula (all brackets vanish, so it reduces
to additivity), but it is not a restricted structure as soon as some `c` has `c ^ p ≠ c`: the
axiom `(c x)^[p] = c ^ p x^[p]` fails. -/
theorem id_not_restricted (hc : ∃ c : k, c ^ p ≠ c) :
    (∀ x y : k, id (x + y) = id x + id y) ∧ ¬ ∃ R : RestrictedLie k p k, R.pmap = id := by
  refine ⟨fun _ _ ↦ rfl, ?_⟩
  rintro ⟨R, hR⟩
  obtain ⟨c, hc⟩ := hc
  obtain ⟨B, φ, hinj, hφ⟩ := R.faithful
  have h1 : φ 1 = φ 1 ^ p := by simpa [hR] using hφ 1
  have hcφ : φ c = c • φ 1 := by rw [← map_smul, smul_eq_mul, _root_.mul_one]
  have h2 : φ c = φ c ^ p := by simpa [hR] using hφ c
  rw [hcφ, smul_pow, ← h1] at h2
  have h3 : (c - c ^ p) • φ 1 = 0 := by rw [sub_smul, ← h2, sub_self]
  have h4 : φ 1 = 0 := (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hc))
  exact one_ne_zero (hinj (h4.trans (map_zero φ).symm))

end HeightOne

section Derivations

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- 3ULFIl_2Wis-19382 (5:23:02) [prop] Leibniz's formula for the iterates of a derivation. -/
theorem derivation_iterate_leibniz (D : Derivation k A A) (n : ℕ) (a b : A) :
    D^[n] (a * b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, n.choose ij.1 • (D^[ij.1] a * D^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul (M := A) (fun i j ↦ D^[i] a * D^[j] b) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, Derivation.leibniz,
      smul_eq_mul, smul_add, Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun ⟨i, j⟩ hij ↦ ?_
      rw [n.choose_symm_of_eq_add (Finset.HasAntidiagonal.mem_antidiagonal.1 hij).symm, mul_comm]

/-- 3ULFIl_2Wis-19382 (5:23:02) [prop] In characteristic `p`, the `p`-th power of a derivation is
a derivation (which makes `Lie(G)` a restricted Lie algebra). -/
theorem derivation_pow_char (p : ℕ) [hp : Fact p.Prime] [CharP k p] (D : Derivation k A A) :
    ∃ Dp : Derivation k A A, ∀ a, Dp a = D^[p] a := by
  have hpA : ∀ x : A, p • x = 0 := fun x ↦ by
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  have key : ∀ a b : A, D^[p] (a * b) = a * D^[p] b + b * D^[p] a := by
    intro a b
    rw [derivation_iterate_leibniz, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ p.choose i • (D^[i] a * D^[j] b)), Finset.sum_range_succ,
      Finset.sum_eq_single 0]
    · simp [mul_comm]
    · intro i hi hi0
      rw [Finset.mem_range] at hi
      obtain ⟨m, hm⟩ := hp.out.dvd_choose_self hi0 hi
      rw [hm, mul_comm, mul_nsmul, hpA]
    · intro h; exact absurd (Finset.mem_range.2 hp.out.pos) h
  let L : A →ₗ[k] A := (D : A →ₗ[k] A) ^ p
  have hL : ∀ a, L a = D^[p] a := fun a ↦ by
    simp [L, Module.End.pow_apply]
  refine ⟨Derivation.mk' L fun a b ↦ ?_, fun a ↦ hL a⟩
  rw [hL, hL, hL, key, smul_eq_mul, smul_eq_mul]

end Derivations

/-- 3ULFIl_2Wis-19444 (5:24:04) [prop] `Lie(G) = Lie(G₁)`: the ideal of `G₁ = ker F` in `A`,
generated by the `a ^ p` with `a` in the augmentation ideal `m`, lies in `m²`, so the cotangent
space `m/m²` at the origin is unchanged. -/
theorem frobenius_ideal_le_sq {A : Type*} [CommRing A] (m : Ideal A) (p : ℕ) (hp : 2 ≤ p) :
    Ideal.span {x | ∃ a ∈ m, a ^ p = x} ≤ m ^ 2 := by
  rw [Ideal.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have : a ^ p = a ^ 2 * a ^ (p - 2) := by rw [← pow_add]; congr 1; omega
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ha 2)

/-- 3ULFIl_2Wis-19511 (5:25:11) [prop] Over an algebraically closed field the one-dimensional
restricted Lie algebras `k x`, `x^[p] = c x`, are, up to rescaling `x`, those with `c = 0`
(`Lie α_p`) and `c = 1` (`Lie μ_p`): for `c ≠ 0` some `l ≠ 0` has `(l x)^[p] = l x`. -/
theorem rank_one_restricted_normalize {k : Type*} [Field k] [IsAlgClosed k] (p : ℕ) (hp : 2 ≤ p)
    {c : k} (hc : c ≠ 0) : ∃ l : k, l ≠ 0 ∧ l ^ p * c = l := by
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ (n := p - 1) (by omega)
  refine ⟨l, fun h ↦ ?_, ?_⟩
  · rw [h, zero_pow (by omega)] at hl; exact inv_ne_zero hc hl.symm
  · have : l ^ p = l ^ (p - 1) * l := by rw [← pow_succ]; congr 1; omega
    rw [this, hl]; field_simp

/-! ## Tori -/

/-- 3ULFIl_2Wis-25487 (7:04:47) [prop] A split torus is determined by its character lattice: the
diagonalizable group `D(M)` of Part 01, with `D(ℤ) = 𝔾_m` and `D(M ⊕ N) = D(M) × D(N)`. -/
noncomputable def splitTorus_rankOne (A : Type*) [CommRing A] : Part01.D ℤ A ≃ Aˣ :=
  Part01.D_int A

/-! ## The counit of a bialgebra (open question of Part 01, entry `_lTf_L0yvrU-10811`)

On the dual numbers `k[ε]`, `ε² = 0`, take both basis vectors `1` and `ε` group-like:
`π(1) = 1 ⊗ 1`, `π(ε) = ε ⊗ ε`, counit `1 ↦ 1`, `ε ↦ 1`. This is a coalgebra, `π` is an algebra
homomorphism, and the counit is not multiplicative (`ε(ε²) = 0 ≠ 1 = ε(ε)²`). So "π is an algebra
homomorphism" does not make `A` a bialgebra; the counit must be required to be an algebra map too
(equivalently, multiplication and unit must be coalgebra morphisms, which includes `ε ∘ m = ε ⊗ ε`).
-/

section DualNumberCounterexample

open TrivSqZeroExt

variable (k : Type) [Field k]

local notation "Dk" => TrivSqZeroExt k k

/-- The basis vector `ε` of `k[ε]`. -/
noncomputable abbrev dnEps : Dk := DualNumber.eps

/-- `π(a + b ε) = a (1 ⊗ 1) + b (ε ⊗ ε)`. -/
noncomputable def dnComul : Dk →ₗ[k] Dk ⊗[k] Dk :=
  (TensorProduct.mk k Dk Dk).flip 1 ∘ₗ Algebra.linearMap k Dk ∘ₗ (fstHom k k k).toLinearMap +
    (TensorProduct.mk k Dk Dk).flip (dnEps k) ∘ₗ inrHom k k ∘ₗ sndHom k k

/-- The counit `a + b ε ↦ a + b`. -/
noncomputable def dnCounit : Dk →ₗ[k] k := (fstHom k k k).toLinearMap + sndHom k k

@[simp] lemma dnComul_apply (x : Dk) :
    dnComul k x = inl x.fst ⊗ₜ (1 : Dk) + inr x.snd ⊗ₜ dnEps k := by
  simp only [dnComul, LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.mk_apply,
    LinearMap.flip_apply, Algebra.linearMap_apply, algebraMap_eq_inl, inrHom_apply, sndHom_apply,
    AlgHom.toLinearMap_apply, fstHom_apply]

@[simp] lemma dnCounit_apply (x : Dk) : dnCounit k x = x.fst + x.snd := by simp [dnCounit]

lemma dn_inl (r : k) : (inl r : Dk) = r • 1 := by ext <;> simp

/-- _lTf_L0yvrU-10811 (3:00:11) [def] (Part 01 question) `π`, `ε` make `k[ε]` a coalgebra. -/
@[instance_reducible] noncomputable def dnCoalgebra : Coalgebra k Dk where
  comul := dnComul k
  counit := dnCounit k
  coassoc := by
    refine linearMap_ext (fun r ↦ ?_) (fun m ↦ ?_)
    · simp [dnEps, dn_inl, smul_tmul']
    · simp [dnEps, smul_tmul']
  rTensor_counit_comp_comul := by
    refine linearMap_ext (fun r ↦ ?_) (fun m ↦ ?_)
    · simp [dnEps, dn_inl, smul_tmul']
    · simp [dnEps, smul_tmul']
  lTensor_counit_comp_comul := by
    refine linearMap_ext (fun r ↦ ?_) (fun m ↦ ?_)
    · simp [dnEps, dn_inl]
    · simp [dnEps]

/-- _lTf_L0yvrU-10811 (3:00:11) [def] (Part 01 question) `π` is multiplicative ... -/
theorem dn_comul_mul (x y : Dk) : dnComul k (x * y) = dnComul k x * dnComul k y := by
  simp only [dnComul_apply, fst_mul, snd_mul, add_mul, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, dnEps, inl_mul_inl, inl_mul_inr, inr_mul_inl, inr_mul_inr,
    _root_.mul_one, _root_.one_mul, zero_tmul, add_zero, smul_eq_mul, op_smul_eq_smul, inr_add,
    add_tmul]
  abel

/-- _lTf_L0yvrU-10811 (3:00:11) [def] (Part 01 question) ... and unital ... -/
theorem dn_comul_one : dnComul k 1 = 1 := by
  simp [Algebra.TensorProduct.one_def]

/-- _lTf_L0yvrU-10811 (3:00:11) [def] (Part 01 question) ... but the counit is not an algebra
homomorphism. -/
theorem dn_counit_not_mul :
    dnCounit k (dnEps k * dnEps k) ≠ dnCounit k (dnEps k) * dnCounit k (dnEps k) := by
  simp [dnEps]

end DualNumberCounterexample

end Buffalo.Groupes.Part03
