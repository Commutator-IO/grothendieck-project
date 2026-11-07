import Mathlib

/-!
# Buffalo, algebraic groups, Part 01 (a): functors of points, first examples, centers

Entries `_lTf_L0yvrU-3` to `_lTf_L0yvrU-2769` of `docs/buffalo-groupes/index.tex` (the undated
side and the first half of 4 June 1973). Statuses in `docs/buffalo-groupes/lean/Part01.json`.

Conventions. The base ring is `k : Type u`, a commutative ring; the category of commutative
`k`-algebras is Mathlib's `CommAlgCat k`, and a "space over `k`" is a functor
`CommAlgCat k ⥤ Type u`. Affine spaces are the corepresentable ones (`Functor.IsCorepresentable`),
and the affine schemes over `k` are `(CommAlgCat k)ᵒᵖ`, a cartesian monoidal category in Mathlib.
Where only the value of a functor at one `k`-algebra `A` matters, the statement is made for an
arbitrary `A`, which is the functor-of-points statement read pointwise.
-/

namespace Buffalo.Groupes.Part01

open CategoryTheory Opposite Limits

universe u

/-! ## Functors of points and affine algebraic groups -/

section GroupObjects

variable {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
  [CartesianMonoidalCategory D]

/-- _lTf_L0yvrU-3 (0:00:03) [prop] A functor commuting with finite products and the final object
takes a group object `X` of `C` to a group object `F(X)` of `C'`. -/
noncomputable def mapGrpOfPreservesFiniteProducts (F : C ⥤ D) [PreservesFiniteProducts F] :
    Grp C ⥤ Grp D :=
  letI := Functor.Monoidal.ofChosenFiniteProducts F
  F.mapGrp

/-- _lTf_L0yvrU-135 (0:02:15) [prop] More generally, such a functor carries other algebraic
structures over: monoids (here) and commutative groups (next). -/
noncomputable def mapMonOfPreservesFiniteProducts (F : C ⥤ D) [PreservesFiniteProducts F] :
    Mon C ⥤ Mon D :=
  letI := Functor.Monoidal.ofChosenFiniteProducts F
  F.mapMon

/-- _lTf_L0yvrU-135 (0:02:15) [prop] Commutative group objects are carried over too. -/
noncomputable def mapCommGrpOfPreservesFiniteProducts [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [PreservesFiniteProducts F] : CommGrp C ⥤ CommGrp D :=
  letI := Functor.Braided.ofChosenFiniteProducts F
  F.mapCommGrp

/-- _lTf_L0yvrU-596 (0:09:56) [prop] A group structure on an object `X` is the same as a lift of
its functor of points to groups: the functors to groups whose underlying functor is
representable are exactly those of group objects (Mathlib `essImage_yonedaGrp`). -/
theorem grp_iff_representable :
    yonedaGrp (C := C).essImage = fun F ↦ (F ⋙ forget _).IsRepresentable :=
  essImage_yonedaGrp

end GroupObjects

section Affine

variable (k : Type u) [CommRing k]

/-- _lTf_L0yvrU-267 (0:04:27) [prop] A functor from `k`-algebras to sets is in the essential image
of the Yoneda embedding of `(k-alg)ᵒᵖ` exactly when it is (co)representable. -/
theorem essImage_coyoneda_iff (F : CommAlgCat.{u} k ⥤ Type u) :
    coyoneda.essImage F ↔ F.IsCorepresentable :=
  ⟨fun ⟨Y, ⟨e⟩⟩ ↦ ⟨Y.unop, ⟨Functor.corepresentableByEquiv.symm e⟩⟩,
    fun ⟨X, ⟨e⟩⟩ ↦ ⟨op X, ⟨Functor.corepresentableByEquiv e⟩⟩⟩

/-- _lTf_L0yvrU-267 (0:04:27) [prop] The affine spaces (representable functors) form a full
subcategory equivalent to the opposite of the category of `k`-algebras (Yoneda). -/
noncomputable def affineSpacesEquiv :
    (CommAlgCat.{u} k)ᵒᵖ ≌ (coyoneda (C := CommAlgCat.{u} k)).EssImageSubcategory :=
  (coyoneda (C := CommAlgCat.{u} k)).toEssImage.asEquivalence

/-- _lTf_L0yvrU-393 (0:06:33) [prop] The space represented by `A` has `X(k') = Hom_{k-alg}(A, k')`. -/
def pointsEquiv (A B : CommAlgCat.{u} k) : (coyoneda.obj (op A)).obj B ≃ (A →ₐ[k] B) where
  toFun f := f.hom
  invFun f := CommAlgCat.ofHom f
  left_inv _ := rfl
  right_inv _ := rfl

/-- _lTf_L0yvrU-660 (0:11:00) [def] An affine algebraic group over `k`: a functor from
`k`-algebras to groups whose underlying set-valued functor is representable. -/
def IsAffineGroup (G : CommAlgCat.{u} k ⥤ GrpCat.{u}) : Prop :=
  (G ⋙ forget GrpCat).IsCorepresentable

/-- _lTf_L0yvrU-660 (0:11:00) [def] Equivalently (Mathlib), a group object in affine schemes. -/
abbrev AffineGroupScheme := Grp (CommAlgCat.{u} k)ᵒᵖ

/-- Building a corepresentation from a family of bijections natural in the algebra. -/
def corepOf (F : CommAlgCat.{u} k ⥤ Type u) (R : Type u) [CommRing R] [Algebra k R]
    (e : ∀ A : CommAlgCat.{u} k, (R →ₐ[k] A) ≃ F.obj A)
    (he : ∀ (A B : CommAlgCat.{u} k) (g : A ⟶ B) (φ : R →ₐ[k] A),
      e B (g.hom.comp φ) = F.map g (e A φ)) :
    F.CorepresentableBy (CommAlgCat.of k R) where
  homEquiv {A} := (pointsEquiv k (CommAlgCat.of k R) A).trans (e A)
  homEquiv_comp g f := he _ _ g f.hom

/-! ## `𝔾_a`, `𝔾_m`, `GL_n` -/

/-- The additive group `𝔾_a : A ↦ (A, +)` (written multiplicatively to land in `CommGrpCat`). -/
def Ga : CommAlgCat.{u} k ⥤ CommGrpCat.{u} where
  obj A := CommGrpCat.of (Multiplicative A)
  map f := CommGrpCat.ofHom (AddMonoidHom.toMultiplicative f.hom.toRingHom.toAddMonoidHom)

/-- The multiplicative group `𝔾_m : A ↦ Aˣ`. -/
def Gm : CommAlgCat.{u} k ⥤ CommGrpCat.{u} where
  obj A := CommGrpCat.of Aˣ
  map f := CommGrpCat.ofHom (Units.map f.hom.toRingHom.toMonoidHom)

/-- Points of the polynomial algebra: `Hom(k[t], A) ≃ A`. -/
noncomputable def polyHomEquiv (A : Type u) [CommRing A] [Algebra k A] :
    (Polynomial k →ₐ[k] A) ≃ A where
  toFun φ := φ Polynomial.X
  invFun a := Polynomial.aeval a
  left_inv φ := Polynomial.algHom_ext (by simp)
  right_inv a := by simp

/-- Points of the Laurent polynomial algebra: `Hom(k[t,t⁻¹], A) ≃ Aˣ`. -/
noncomputable def laurentHomEquiv (A : Type u) [CommRing A] [Algebra k A] :
    (LaurentPolynomial k →ₐ[k] A) ≃ Aˣ :=
  (AddMonoidAlgebra.lift k A ℤ).symm.trans
    { toFun φ := (φ.toHomUnits) (Multiplicative.ofAdd 1)
      invFun u := (Units.coeHom A).comp (zpowersHom Aˣ u)
      left_inv φ := by
        ext
        simp only [MonoidHom.comp_apply, Units.coeHom_apply]
        rw [zpowersHom_apply, ← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
        rfl
      right_inv u := by ext; simp }

/-- _lTf_L0yvrU-722 (0:12:02) [ex] `𝔾_a` is an affine algebraic group (represented by `k[t]`);
its groups of points are commutative. -/
noncomputable def Ga_corep : (Ga k ⋙ forget _).CorepresentableBy (CommAlgCat.of k (Polynomial k)) :=
  corepOf k _ _ (fun A ↦ (polyHomEquiv k A).trans Multiplicative.ofAdd) (fun _ _ _ _ ↦ rfl)

/-- _lTf_L0yvrU-722 (0:12:02) [ex] `𝔾_m` is an affine algebraic group (represented by
`k[t,t⁻¹]`); its groups of points are commutative. -/
noncomputable def Gm_corep :
    (Gm k ⋙ forget _).CorepresentableBy (CommAlgCat.of k (LaurentPolynomial k)) :=
  corepOf k _ _ (fun A ↦ laurentHomEquiv k A) (fun _ _ _ _ ↦ Units.ext rfl)

/-- `GL_n` as a group functor. -/
def GLn (n : Type) [Fintype n] [DecidableEq n] : CommAlgCat.{u} k ⥤ GrpCat.{u} where
  obj A := GrpCat.of (Matrix.GeneralLinearGroup n A)
  map f := GrpCat.ofHom (Units.map f.hom.toRingHom.mapMatrix.toMonoidHom)

/-- The generic matrix `(t_{ij})` over `k[t_{ij}]` and its determinant `Δ`. -/
noncomputable abbrev genDet (n : Type) [Fintype n] [DecidableEq n] : MvPolynomial (n × n) k :=
  (Matrix.of (fun i j ↦ (MvPolynomial.X (i, j) : MvPolynomial (n × n) k))).det

theorem map_genDet (n : Type) [Fintype n] [DecidableEq n] {A : Type u} [CommRing A] [Algebra k A]
    (φ : MvPolynomial (n × n) k →ₐ[k] A) :
    φ (genDet k n) = (Matrix.of fun i j ↦ φ (MvPolynomial.X (i, j))).det := by
  rw [AlgHom.map_det]; congr 1

/-- Points of `k[t_{ij}][1/Δ]` are invertible matrices. -/
noncomputable def glHomEquiv (n : Type) [Fintype n] [DecidableEq n]
    (A : Type u) [CommRing A] [Algebra k A] :
    (Localization.Away (genDet k n) →ₐ[k] A) ≃ Matrix.GeneralLinearGroup n A where
  toFun φ :=
    let ψ := φ.comp (IsScalarTower.toAlgHom k (MvPolynomial (n × n) k) _)
    (show IsUnit (Matrix.of fun i j ↦ ψ (MvPolynomial.X (i, j))) from
      (Matrix.isUnit_iff_isUnit_det _).mpr (by
        rw [← map_genDet]
        exact (IsLocalization.Away.algebraMap_isUnit (genDet k n)).map φ)).unit
  invFun g := IsLocalization.Away.liftAlgHom (A := k) (genDet k n)
      (f := MvPolynomial.aeval (fun p : n × n ↦ (g : Matrix n n A) p.1 p.2))
      (by
        rw [map_genDet]
        convert (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit using 2
        ext i j; simp)
  left_inv φ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (genDet k n))
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, Algebra.algHom, IsLocalization.Away.coe_liftAlgHom]
    erw [IsLocalization.Away.lift_eq]
    simp
  right_inv g := by ext i j; simp

/-- _lTf_L0yvrU-790 (0:13:10) [ex] `GL_n` is an affine algebraic group: its functor of points
is represented by `k[t_{ij}][1/Δ]`. -/
noncomputable def GLn_corep (n : Type) [Fintype n] [DecidableEq n] :
    (GLn k n ⋙ forget _).CorepresentableBy (CommAlgCat.of k (Localization.Away (genDet k n))) :=
  corepOf k _ _ (fun A ↦ glHomEquiv k n A) (fun _ _ _ _ ↦ Units.ext (Matrix.ext fun _ _ ↦ rfl))

/-- _lTf_L0yvrU-790 (0:13:10) [ex] `GL_n` is in general non-commutative: `GL_2(A)` is not
commutative as soon as `A ≠ 0`. -/
theorem GL2_not_comm (A : Type u) [CommRing A] [Nontrivial A] :
    ∃ g h : Matrix.GeneralLinearGroup (Fin 2) A, g * h ≠ h * g := by
  refine ⟨⟨!![1, 1; 0, 1], !![1, -1; 0, 1], ?_, ?_⟩, ⟨!![1, 0; 1, 1], !![1, 0; -1, 1], ?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · intro h
    have := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) A ↦ (g : Matrix (Fin 2) (Fin 2) A) 0 0) h
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this

/-! ## Basic examples -/

/-- _lTf_L0yvrU-932 (0:15:32) [prop] `𝔾_m(A) = Aˣ` is the largest subgroup of the multiplicative
monoid of `𝒪(A) = A`: every submonoid all of whose elements are invertible in it consists of
units. (That `𝒪 : A ↦ A` is a `k`-algebra object and `𝔾_a` its additive group is the
definition of `Ga`.) -/
theorem units_largest {M : Type*} [Monoid M] (H : Submonoid M)
    (h : ∀ x ∈ H, ∃ y ∈ H, x * y = 1 ∧ y * x = 1) : H ≤ IsUnit.submonoid M := by
  intro x hx
  obtain ⟨y, -, h1, h2⟩ := h x hx
  exact ⟨⟨x, y, h1, h2⟩, rfl⟩

/-- _lTf_L0yvrU-995 (0:16:35) [prop] `𝔾_a`, `𝔾_m`, `GL_n` are represented by `k[t]`,
`k[t,t⁻¹]`, `k[t_{ij}][1/Δ]` (the three corepresentations above, collected). -/
theorem Ga_Gm_GLn_representable (n : Type) [Fintype n] [DecidableEq n] :
    (Ga k ⋙ forget _).IsCorepresentable ∧ (Gm k ⋙ forget _).IsCorepresentable ∧
      (GLn k n ⋙ forget _).IsCorepresentable :=
  ⟨⟨_, ⟨Ga_corep k⟩⟩, ⟨_, ⟨Gm_corep k⟩⟩, ⟨_, ⟨GLn_corep k n⟩⟩⟩

/-- _lTf_L0yvrU-1061 (0:17:41) [ex] The orthogonal group of a quadratic form `Q` on `Aⁿ`, the
`g ∈ GL_n(A)` with `Q ∘ g = Q`, is a subgroup: the stabilizer of `Q` for the action of
`GL_n(A)`. -/
def orthogonalGroup {n : Type} [Fintype n] [DecidableEq n] {A : Type u} [CommRing A]
    (Q : QuadraticForm A (n → A)) : Subgroup (Matrix.GeneralLinearGroup n A) where
  carrier := {g | Q.comp (Matrix.toLin' (g : Matrix n n A)) = Q}
  one_mem' := by ext x; simp
  mul_mem' {g h} hg hh := by
    ext x
    have := congrArg (fun Q' : QuadraticForm A (n → A) ↦ Q' (Matrix.mulVec (h : Matrix n n A) x)) hg
    have h2 := congrArg (fun Q' : QuadraticForm A (n → A) ↦ Q' x) hh
    simp only [QuadraticMap.comp_apply, Matrix.toLin'_apply] at this h2 ⊢
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, this, h2]
  inv_mem' {g} hg := by
    ext x
    have := congrArg (fun Q' : QuadraticForm A (n → A) ↦ Q' (Matrix.mulVec ((g⁻¹ : Matrix.GeneralLinearGroup n A) :
      Matrix n n A) x)) hg
    simp only [QuadraticMap.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec] at this ⊢
    rw [← this, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

/-- Points of a localization `R[1/f]`: the points of `R` at which `f` is invertible. -/
noncomputable def awayHomEquiv {R : Type u} [CommRing R] [Algebra k R] (f : R)
    (A : Type u) [CommRing A] [Algebra k A] :
    (Localization.Away f →ₐ[k] A) ≃ {φ : R →ₐ[k] A // IsUnit (φ f)} where
  toFun φ := ⟨φ.comp (IsScalarTower.toAlgHom k R _),
    (IsLocalization.Away.algebraMap_isUnit f).map φ⟩
  invFun φ := IsLocalization.Away.liftAlgHom f φ.2
  left_inv φ := by
    apply IsLocalization.algHom_ext (Submonoid.powers f)
    ext x
    simp only [AlgHom.comp_apply, Algebra.algHom, IsLocalization.Away.coe_liftAlgHom]
    erw [IsLocalization.Away.lift_eq]
    rfl
  right_inv φ := by
    apply Subtype.ext
    ext x
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsLocalization.Away.coe_liftAlgHom]
    erw [IsLocalization.Away.lift_eq]
    rfl

/-- Points of a polynomial algebra `k[t_s]`: families of elements. -/
noncomputable def mvHomEquiv (σ : Type) (A : Type u) [CommRing A] [Algebra k A] :
    (MvPolynomial σ k →ₐ[k] A) ≃ (σ → A) where
  toFun φ s := φ (MvPolynomial.X s)
  invFun x := MvPolynomial.aeval x
  left_inv φ := MvPolynomial.algHom_ext (by simp)
  right_inv x := by ext; simp

/-- The upper triangular generic matrix and the product of its diagonal. -/
noncomputable def triDiag (n : Type) [Fintype n] [LinearOrder n] :
    MvPolynomial {p : n × n // p.1 ≤ p.2} k :=
  ∏ i, MvPolynomial.X ⟨(i, i), le_rfl⟩

/-- _lTf_L0yvrU-1262 (0:21:02) [ex] The upper triangular subgroup `T_n` of `GL_n` is represented by
`k[t_{ij} (i ≤ j)][t_{11}⁻¹, …, t_{nn}⁻¹]`: its points are the invertible upper triangular
matrices. -/
noncomputable def triHomEquiv (n : Type) [Fintype n] [LinearOrder n]
    (A : Type u) [CommRing A] [Algebra k A] :
    (Localization.Away (triDiag k n) →ₐ[k] A) ≃
      {g : Matrix.GeneralLinearGroup n A // (g : Matrix n n A).IsUpperTriangular} :=
  (awayHomEquiv k (triDiag k n) A).trans
  { toFun φ :=
      let M : Matrix n n A := Matrix.of fun i j ↦
        if h : i ≤ j then φ.1 (MvPolynomial.X ⟨(i, j), h⟩) else 0
      have hM : M.IsUpperTriangular := fun i j hij ↦ by
        change j < i at hij
        simp [M, not_le.mpr hij]
      ⟨((Matrix.isUnit_iff_isUnit_det M).mpr (by
        rw [Matrix.det_of_isUpperTriangular hM]
        convert φ.2 using 1
        simp [M, triDiag, map_prod])).unit, hM⟩
    invFun g := ⟨MvPolynomial.aeval (fun p ↦ (g.1 : Matrix n n A) p.1.1 p.1.2), by
      have := (Matrix.isUnit_iff_isUnit_det _).mp g.1.isUnit
      rw [Matrix.det_of_isUpperTriangular g.2] at this
      simpa [triDiag, map_prod] using this⟩
    left_inv φ := by
      apply Subtype.ext
      apply MvPolynomial.algHom_ext
      rintro ⟨⟨i, j⟩, h⟩
      simp [h]
    right_inv g := by
      apply Subtype.ext
      ext i j
      by_cases h : i ≤ j
      · simp [h]
      · simp [h, g.2 (not_le.mp h)] }

/-- The strictly upper triangular (unipotent) matrix with entries `x_{ij}` (`i < j`). -/
def unipotentMatrix {n : Type} [Fintype n] [LinearOrder n] {A : Type u} [CommRing A]
    (x : {p : n × n // p.1 < p.2} → A) : Matrix n n A :=
  Matrix.of fun i j ↦ if h : i < j then x ⟨(i, j), h⟩ else if i = j then 1 else 0

theorem unipotentMatrix_upper {n : Type} [Fintype n] [LinearOrder n] {A : Type u} [CommRing A]
    (x : {p : n × n // p.1 < p.2} → A) : (unipotentMatrix x).IsUpperTriangular :=
  fun i j hij ↦ by
    change j < i at hij
    simp [unipotentMatrix, not_lt.mpr hij.le, hij.ne']

theorem det_unipotentMatrix {n : Type} [Fintype n] [LinearOrder n] {A : Type u} [CommRing A]
    (x : {p : n × n // p.1 < p.2} → A) : (unipotentMatrix x).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (unipotentMatrix_upper x)]
  simp [unipotentMatrix]

/-- _lTf_L0yvrU-1337 (0:22:17) [ex] The strictly triangular subgroup (diagonal `1`) of `GL_n` is
represented by `k[t_{ij} (i < j)]`: its points are the families `(x_{ij})_{i<j}`, every such
matrix being invertible (determinant `1`). -/
noncomputable def unipotentHomEquiv (n : Type) [Fintype n] [LinearOrder n]
    (A : Type u) [CommRing A] [Algebra k A] :
    (MvPolynomial {p : n × n // p.1 < p.2} k →ₐ[k] A) ≃
      {g : Matrix.GeneralLinearGroup n A //
        (g : Matrix n n A).IsUpperTriangular ∧ ∀ i, (g : Matrix n n A) i i = 1} :=
  (mvHomEquiv k _ A).trans
  { toFun x := ⟨((Matrix.isUnit_iff_isUnit_det (unipotentMatrix x)).mpr
        (by rw [det_unipotentMatrix]; exact isUnit_one)).unit,
      unipotentMatrix_upper x, fun i ↦ by simp [unipotentMatrix]⟩
    invFun g p := (g.1 : Matrix n n A) p.1.1 p.1.2
    left_inv x := by ext ⟨⟨i, j⟩, h⟩; simp [unipotentMatrix, h]
    right_inv g := by
      apply Subtype.ext
      ext i j
      simp only [IsUnit.unit_spec, unipotentMatrix, Matrix.of_apply]
      rcases lt_trichotomy i j with h | rfl | h
      · simp [h]
      · simp [g.2.2]
      · simp [not_lt.mpr h.le, h.ne', g.2.1 h] }

/-- Points of a quotient `R/(f)`: the points of `R` killing `f`. -/
noncomputable def quotHomEquiv {R : Type u} [CommRing R] [Algebra k R] (f : R)
    (A : Type u) [CommRing A] [Algebra k A] :
    (R ⧸ Ideal.span {f} →ₐ[k] A) ≃ {φ : R →ₐ[k] A // φ f = 0} where
  toFun φ := ⟨φ.comp (Ideal.Quotient.mkₐ k _), by simp⟩
  invFun φ := Ideal.Quotient.liftₐ _ φ.1 (fun x hx ↦ by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    simp [φ.2])
  left_inv φ := by ext x; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x; rfl
  right_inv φ := rfl

/-- Points of `k[t]/(f)`: the roots of `f`. -/
noncomputable def adjoinRootHomEquiv (f : Polynomial k) (A : Type u) [CommRing A] [Algebra k A] :
    (AdjoinRoot f →ₐ[k] A) ≃ {a : A // Polynomial.aeval a f = 0} :=
  (quotHomEquiv k f A).trans
    ((polyHomEquiv k A).subtypeEquiv fun φ ↦ by
      simp only [polyHomEquiv, Equiv.coe_fn_mk]
      rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_X_left_apply])

/-- _lTf_L0yvrU-1466 (0:24:26) [ex] The group `{(x, y) : xy = 1}` is represented by
`k[x,y]/(xy - 1)`, and it is `𝔾_m`: its points are the units (whence `k[x,y]/(xy-1) ≃ k[x,x⁻¹]`
by Yoneda, both representing `𝔾_m`). -/
noncomputable def xyHomEquiv (A : Type u) [CommRing A] [Algebra k A] :
    (MvPolynomial (Fin 2) k ⧸ Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 - 1 : MvPolynomial (Fin 2) k)} →ₐ[k] A) ≃
      {x : Fin 2 → A // x 0 * x 1 = 1} :=
  (quotHomEquiv k _ A).trans
    ((mvHomEquiv k (Fin 2) A).subtypeEquiv fun φ ↦ by
      simp only [mvHomEquiv, Equiv.coe_fn_mk, map_sub, map_mul, map_one, sub_eq_zero])

/-- _lTf_L0yvrU-1466 (0:24:26) [ex] The pairs with `xy = 1` are the units, with the coordinatewise
law. -/
def xyEquivUnits (A : Type u) [CommRing A] : {x : Fin 2 → A // x 0 * x 1 = 1} ≃ Aˣ where
  toFun x := ⟨x.1 0, x.1 1, x.2, by rw [mul_comm]; exact x.2⟩
  invFun u := ⟨![u, ↑u⁻¹], by simp⟩
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv u := by ext; rfl

/-- _lTf_L0yvrU-1661 (0:27:41) [ex] `λ ↦ λ I_n` is a monomorphism `𝔾_m → GL_n` (injective on
points, `n ≠ 0`); its image is the group of scalar matrices. -/
theorem scalar_units_injective (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Type u) [CommRing A] :
    Function.Injective (Units.map (Matrix.scalar n : A →+* Matrix n n A).toMonoidHom) := by
  intro a b h
  ext
  exact Matrix.scalar_inj.mp (congrArg Units.val h)

/-- _lTf_L0yvrU-1724 (0:28:44) [cex] For `n ≥ 2`, `λ ↦ diag(1, …, λ, …, 1)` is not central: when
`λ ≠ 1` it does not commute with the transvection `1 + E_{ij}` (`j ≠ i`). (For `n = 1` it is
the identity of `𝔾_m`, which is central.) -/
theorem diag_not_central {n : Type} [Fintype n] [DecidableEq n] {A : Type u} [CommRing A]
    {i j : n} (hij : i ≠ j) {c : A} (hc : c ≠ 1) :
    Matrix.diagonal (Function.update 1 i c) * Matrix.transvection i j 1 ≠
      Matrix.transvection i j 1 * Matrix.diagonal (Function.update 1 i c) := by
  intro h
  have := congrFun (congrFun h i) j
  simp [Matrix.transvection, Matrix.diagonal_mul, Matrix.mul_diagonal, hij, Ne.symm hij] at this
  exact hc this

/-! ## Centers and central morphisms -/

/-- _lTf_L0yvrU-2181 (0:36:21) [def] The center is the kernel of `g ↦ (inner automorphism of
`g`)`: pointwise, the kernel of `MulAut.conj` is `Subgroup.center`. -/
theorem ker_conj_eq_center (G : Type*) [Group G] :
    (MulAut.conj : G →* MulAut G).ker = Subgroup.center G := by
  ext g
  simp only [MonoidHom.mem_ker, Subgroup.mem_center_iff, MulEquiv.ext_iff, MulAut.conj_apply,
    MulAut.one_apply]
  exact ⟨fun h x ↦ (mul_inv_eq_iff_eq_mul.mp (h x)).symm,
    fun h x ↦ mul_inv_eq_iff_eq_mul.mpr (h x).symm⟩

variable {k} in
/-- _lTf_L0yvrU-2181 (0:36:21) [def] The center of a group functor `G`, as a subgroup functor:
`g ∈ G(A)` is central when its image in `G(B)` is central for every `A → B` (this is the kernel
of `G → Aut(G)`, the automorphisms of `G` restricted to `A`-algebras). -/
def fCenter (G : CommAlgCat.{u} k ⥤ GrpCat.{u}) (A : CommAlgCat.{u} k) : Subgroup (G.obj A) where
  carrier := {g | ∀ (B : CommAlgCat.{u} k) (f : A ⟶ B), (G.map f).hom g ∈ Subgroup.center (G.obj B)}
  one_mem' B f := by rw [map_one]; exact one_mem _
  mul_mem' ha hb B f := by rw [map_mul]; exact mul_mem (ha B f) (hb B f)
  inv_mem' ha B f := by rw [map_inv]; exact inv_mem (ha B f)

variable {k} in
/-- _lTf_L0yvrU-2376 (0:39:36) [prop] `g ∈ G(Z)` is in the center iff its image in `G(Z')` is
central for every `Z' → Z` (here `A → B` on algebras); the center is a subfunctor, and it is
contained in the center of each `G(A)`. -/
theorem mem_fCenter_iff (G : CommAlgCat.{u} k ⥤ GrpCat.{u}) (A : CommAlgCat.{u} k) (g : G.obj A) :
    g ∈ fCenter G A ↔
      ∀ (B : CommAlgCat.{u} k) (f : A ⟶ B), (G.map f).hom g ∈ Subgroup.center (G.obj B) :=
  Iff.rfl

variable {k} in
/-- _lTf_L0yvrU-2376 (0:39:36) [prop] The center is a subgroup functor. -/
theorem fCenter_map (G : CommAlgCat.{u} k ⥤ GrpCat.{u}) {A B : CommAlgCat.{u} k} (f : A ⟶ B)
    {g : G.obj A} (hg : g ∈ fCenter G A) : (G.map f).hom g ∈ fCenter G B := by
  intro C f'
  have := hg C (f ≫ f')
  rwa [G.map_comp] at this

variable {k} in
/-- _lTf_L0yvrU-2376 (0:39:36) [prop] The functorial center lies in the center of each group of
points. -/
theorem fCenter_le_center (G : CommAlgCat.{u} k ⥤ GrpCat.{u}) (A : CommAlgCat.{u} k) :
    fCenter G A ≤ Subgroup.center (G.obj A) := fun g hg ↦ by
  simpa using hg A (𝟙 A)

/-- _lTf_L0yvrU-2441 (0:40:41) [def] `λ ↦ λ I_n` is central: scalar matrices are in the center
of `GL_n(A)` for every `A`. -/
theorem scalar_mem_center (n : Type) [Fintype n] [DecidableEq n] {A : Type u} [CommRing A]
    (c : Aˣ) : Units.map (Matrix.scalar n : A →+* Matrix n n A).toMonoidHom c ∈
      Subgroup.center (Matrix.GeneralLinearGroup n A) :=
  Subgroup.mem_center_iff.mpr fun g ↦ Units.ext
    (Matrix.scalar_commute (c : A) (fun _ ↦ Commute.all _ _) (g : Matrix n n A)).eq.symm

/-- _lTf_L0yvrU-2639 (0:43:59) [ex] `λ ↦ 1 + λ E_{ij}` (`i ≠ j`; for `n = 2`, `(1 λ; 0 1)`) is a
homomorphism `𝔾_a → GL_n`. -/
def transvectionHom {n : Type} [Fintype n] [DecidableEq n] {A : Type u} [CommRing A] {i j : n}
    (hij : i ≠ j) : Multiplicative A →* Matrix.GeneralLinearGroup n A where
  toFun a := ⟨Matrix.transvection i j a.toAdd, Matrix.transvection i j (-a.toAdd),
    by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp,
    by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by simp [Matrix.transvection_mul_transvection_same _ _ hij])

/-- _lTf_L0yvrU-2639 (0:43:59) [ex] … and it embeds `𝔾_a` in `GL_n` (injective on points). -/
theorem transvectionHom_injective {n : Type} [Fintype n] [DecidableEq n] {A : Type u} [CommRing A]
    {i j : n} (hij : i ≠ j) : Function.Injective (transvectionHom (A := A) hij) := fun a b h ↦ by
  have := congrArg (fun g : Matrix.GeneralLinearGroup n A ↦ (g : Matrix n n A) i j) h
  simpa [transvectionHom, Matrix.transvection, hij] using this

end Affine

end Buffalo.Groupes.Part01
