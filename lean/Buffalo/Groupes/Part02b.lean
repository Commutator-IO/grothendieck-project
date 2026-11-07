import Buffalo.Groupes.Part02a

/-!
# Buffalo, algebraic groups, Part 02 (b): distributions, hyperalgebra, diagonalizable groups

Entries `_lTf_L0yvrU-25719` to `_lTf_L0yvrU-30490` of `docs/buffalo-groupes/index.tex` (19 and
20 June 1973). Statuses in `docs/buffalo-groupes/lean/Part02.json`.

`Dist(X)(k') = V(A)(k') = Hom_k(A, k')` for `X = Spec A` (`Part01.V`). The pairing
`u ⊠ v : A ⊗ B → k'` is `a ⊗ b ↦ u(a) v(b)` (`boxtimes`); the diagonal of `Dist(X)` is the
transpose of the multiplication of `A` (`diag`); the law of `Dist(G)` for a monoid `G = Spec A`
is Mathlib's convolution product on `WithConv (A →ₗ[k] k')`.
-/

namespace Buffalo.Groupes.Part02

open TensorProduct LinearMap WithConv

universe u

variable (k : Type u) [CommRing k]

/-! ## The distribution functor -/

section Dist

variable {k} {A B : Type u} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  (R : Type u) [CommRing R] [Algebra k R]

/-- _lTf_L0yvrU-25719 (7:08:39) [def] `Dist(X)(k') = V(A)(k') = Hom_k(A, k')`, represented by the
symmetric algebra `S_k(A)` (`Part01.V_repr`). -/
noncomputable def distRepr : (SymmetricAlgebra k A →ₐ[k] R) ≃ Part01.V k A R :=
  Part01.V_repr k A R

/-- _lTf_L0yvrU-25918 (7:11:58) [prop] `Dist` is covariant in `X = Spec A`: `B → A` gives
`V(A) → V(B)`, `u ↦ u ∘ f`, functorially. -/
def distMap (f : B →ₗ[k] A) : Part01.V k A R →ₗ[R] Part01.V k B R where
  toFun u := u ∘ₗ f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem distMap_comp {C : Type u} [AddCommGroup C] [Module k C] (f : B →ₗ[k] A) (g : C →ₗ[k] B)
    (u : Part01.V k A R) : distMap R (f ∘ₗ g) u = distMap R g (distMap R f u) := rfl

/-- _lTf_L0yvrU-26050 (7:14:10) [prop] The pairing `Dist(X) × Dist(Y) → Dist(X × Y)`,
`(u ⊠ v)(a ⊗ b) = u(a) v(b)`, through `A ⊗ B → k' ⊗ k' → k'`. -/
noncomputable def boxtimes (u : A →ₗ[k] R) (v : B →ₗ[k] R) : A ⊗[k] B →ₗ[k] R :=
  LinearMap.mul' k R ∘ₗ TensorProduct.map u v

@[simp] theorem boxtimes_tmul (u : A →ₗ[k] R) (v : B →ₗ[k] R) (a : A) (b : B) :
    boxtimes R u v (a ⊗ₜ b) = u a * v b := rfl

/-- `⊠` is `k'`-bilinear, so it induces `V(A) ⊗_𝒪 V(B) → V(A ⊗ B)`. -/
noncomputable def boxtimesBilin : (A →ₗ[k] R) →ₗ[R] (B →ₗ[k] R) →ₗ[R] (A ⊗[k] B →ₗ[k] R) :=
  LinearMap.mk₂ R (boxtimes R)
    (fun u u' v ↦ TensorProduct.ext' fun a b ↦ by simp [add_mul])
    (fun c u v ↦ TensorProduct.ext' fun a b ↦ by simp [mul_assoc])
    (fun u v v' ↦ TensorProduct.ext' fun a b ↦ by simp [mul_add])
    (fun c u v ↦ TensorProduct.ext' fun a b ↦ by simp [mul_left_comm])

/-- The comparison morphism `V(A) ⊗_𝒪 V(B) → V(A ⊗ B)`. -/
noncomputable def cmp : (A →ₗ[k] R) ⊗[R] (B →ₗ[k] R) →ₗ[R] (A ⊗[k] B →ₗ[k] R) :=
  TensorProduct.lift (boxtimesBilin R)

theorem zmod_smul_eq_zero (n : ℕ) (b : ZMod n) : (n : ℤ) • b = 0 := by
  rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

theorem tensor_zero_of_coprime {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]
    (h2 : ∀ a : P, (2 : ℤ) • a = 0) (h3 : ∀ b : Q, (3 : ℤ) • b = 0) (z : P ⊗[ℤ] Q) : z = 0 := by
  have e3 : ∀ z : P ⊗[ℤ] Q, (3 : ℤ) • z = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b => rw [← TensorProduct.tmul_smul, h3, TensorProduct.tmul_zero]
    | add a b ha hb => rw [smul_add, ha, hb, add_zero]
  have e2 : ∀ z : P ⊗[ℤ] Q, (2 : ℤ) • z = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b => rw [TensorProduct.smul_tmul', h2, TensorProduct.zero_tmul]
    | add a b ha hb => rw [smul_add, ha, hb, add_zero]
  calc z = (3 : ℤ) • z - (2 : ℤ) • z := by rw [← sub_smul]; norm_num
    _ = 0 := by rw [e3, e2, sub_zero]

theorem zmod_tensor_subsingleton : Subsingleton (ZMod 2 ⊗[ℤ] ZMod 3) :=
  ⟨fun x y ↦ by
    rw [tensor_zero_of_coprime (zmod_smul_eq_zero 2) (zmod_smul_eq_zero 3) x,
      tensor_zero_of_coprime (zmod_smul_eq_zero 2) (zmod_smul_eq_zero 3) y]⟩

theorem dual_tensor_subsingleton (R : Type) [CommRing R] :
    Subsingleton ((ZMod 2 →ₗ[ℤ] R) ⊗[R] (ZMod 3 →ₗ[ℤ] R)) := by
  have hn : ∀ (n : ℕ) (u : ZMod n →ₗ[ℤ] R), (n : ℤ) • u = 0 := by
    intro n u
    ext x
    rw [LinearMap.smul_apply, ← map_zsmul, zmod_smul_eq_zero, map_zero, LinearMap.zero_apply]
  have e3 : ∀ z : (ZMod 2 →ₗ[ℤ] R) ⊗[R] (ZMod 3 →ₗ[ℤ] R), (3 : ℤ) • z = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b => rw [← TensorProduct.tmul_smul]; erw [hn 3 b]; rw [TensorProduct.tmul_zero]
    | add a b ha hb => rw [smul_add, ha, hb, add_zero]
  have e2 : ∀ z : (ZMod 2 →ₗ[ℤ] R) ⊗[R] (ZMod 3 →ₗ[ℤ] R), (2 : ℤ) • z = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b => rw [TensorProduct.smul_tmul']; erw [hn 2 a]; rw [TensorProduct.zero_tmul]
    | add a b ha hb => rw [smul_add, ha, hb, add_zero]
  have h : ∀ z : (ZMod 2 →ₗ[ℤ] R) ⊗[R] (ZMod 3 →ₗ[ℤ] R), z = 0 := fun z ↦
    calc z = (3 : ℤ) • z - (2 : ℤ) • z := by rw [← sub_smul]; norm_num
      _ = 0 := by rw [e3, e2, sub_zero]
  exact ⟨fun x y ↦ by rw [h x, h y]⟩

theorem zmod_not_projective (n : ℕ) (hn : 2 ≤ n) : ¬ Module.Projective ℤ (ZMod n) := by
  intro _
  have : Module.Flat ℤ (ZMod n) := inferInstance
  have ht := Module.Flat.torsion_eq_bot (R := ℤ) (M := ZMod n)
  have h1 : (1 : ZMod n) ∈ Submodule.torsion ℤ (ZMod n) := by
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by omega)⟩, ?_⟩
    simp
  rw [ht, Submodule.mem_bot] at h1
  have : Fact (1 < n) := ⟨by omega⟩
  exact one_ne_zero h1

/-- _lTf_L0yvrU-26115 (7:15:15) [cex] The entry's "only if" is false: over `k = ℤ`, with
`A = ℤ/2` and `B = ℤ/3` (neither projective), both `V(A) ⊗_𝒪 V(B)` and `V(A ⊗ B)` vanish at every
`k'`, so `V(A) ⊗_𝒪 V(B) → V(A ⊗ B)` is an isomorphism. -/
theorem cmp_bijective_not_projective (R : Type) [CommRing R] :
    Function.Bijective (cmp (k := ℤ) (A := ZMod 2) (B := ZMod 3) R) ∧
      ¬ Module.Projective ℤ (ZMod 2) ∧ ¬ Module.Projective ℤ (ZMod 3) := by
  have := dual_tensor_subsingleton R
  have := zmod_tensor_subsingleton
  have : Subsingleton (ZMod 2 ⊗[ℤ] ZMod 3 →ₗ[ℤ] R) :=
    ⟨fun f g ↦ LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  refine ⟨⟨fun x y _ ↦ Subsingleton.elim x y, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩,
    zmod_not_projective 2 le_rfl, zmod_not_projective 3 (by norm_num)⟩

/-- _lTf_L0yvrU-26180 (7:16:20) [prop] The pairing `V(A) × V(B) → V(N)` attached to `φ : N → A ⊗ B`,
`(u, v) ↦ (u ⊠ v) ∘ φ` (the direction morphism ↦ pairing). -/
noncomputable def pairingOf {N : Type u} [AddCommGroup N] [Module k N] (φ : N →ₗ[k] A ⊗[k] B) :
    (A →ₗ[k] R) →ₗ[R] (B →ₗ[k] R) →ₗ[R] (N →ₗ[k] R) :=
  (boxtimesBilin R).compr₂ (distMap R φ)

end Dist

section DistAlg

variable {k} {A : Type u} [CommRing A] [Algebra k A] (R : Type u) [CommRing R] [Algebra k R]

/-- _lTf_L0yvrU-26307 (7:18:27) [prop] `X ⊆ Dist(X)`: an algebra map `A → k'` is a particular
linear map, injectively. -/
theorem points_sub_dist : Function.Injective (fun φ : A →ₐ[k] R ↦ φ.toLinearMap) :=
  AlgHom.toLinearMap_injective

/-- The diagonal `δ : Dist(X) → Dist(X × X) = Dist(X) ⊠ Dist(X)`, transpose of the
multiplication `A ⊗ A → A`. -/
noncomputable def diag (u : A →ₗ[k] R) : A ⊗[k] A →ₗ[k] R := u ∘ₗ LinearMap.mul' k A

/-- _lTf_L0yvrU-26440 (7:20:40) [prop] The inclusion `X ⊆ Dist(X)` commutes with the diagonals:
`δ(x) = x ⊠ x` for a point `x` of `X` (`X → X × X` is the diagonal). -/
theorem diag_point (φ : A →ₐ[k] R) : diag R φ.toLinearMap = boxtimes R φ.toLinearMap φ.toLinearMap :=
  TensorProduct.ext' fun a b ↦ by simp [diag]

/-- _lTf_L0yvrU-26884 (7:28:04) [prop] A point `x ∈ Dist(X)(k')` lies in `X(k')` iff
`δ(x) = x ⊠ x` and `ε(x) = x(1) = 1`. -/
theorem mem_points_iff (x : A →ₗ[k] R) :
    (∃ φ : A →ₐ[k] R, φ.toLinearMap = x) ↔ diag R x = boxtimes R x x ∧ x 1 = 1 := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨diag_point R φ, map_one φ⟩
  · rintro ⟨h, h1⟩
    refine ⟨AlgHom.ofLinearMap x h1 fun a b ↦ ?_, rfl⟩
    simpa [diag] using LinearMap.congr_fun h (a ⊗ₜ b)

end DistAlg

/-! ## Linear forms with values in commutative algebras separate points -/

section Separate

variable {k} {N P : Type u} [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P]

/-- Two linear maps `N → P` agree as soon as they agree after every linear form `P → k'` with
values in a commutative `k`-algebra (take `k' = k ⊕ P`, the trivial square-zero extension). -/
theorem V_separates {f g : N →ₗ[k] P}
    (h : ∀ (R : Type u) [CommRing R] [Algebra k R] (x : P →ₗ[k] R), x ∘ₗ f = x ∘ₗ g) : f = g := by
  let _ : Module kᵐᵒᵖ P := Module.compHom P ((RingHom.id k).fromOpposite fun _ _ ↦ Commute.all _ _)
  have _ : IsCentralScalar k P := ⟨fun _ _ ↦ rfl⟩
  have := h (TrivSqZeroExt k P) (TrivSqZeroExt.inrHom k P)
  ext n
  exact TrivSqZeroExt.inr_injective (LinearMap.congr_fun this n)

variable (μ : P ⊗[k] P →ₗ[k] P)

/-- _lTf_L0yvrU-26689 (7:24:49) [prop] `A` is commutative iff `δ = x ↦ x ∘ μ` is cocommutative. -/
theorem comm_iff_cocomm :
    μ ∘ₗ (TensorProduct.comm k P P).toLinearMap = μ ↔
      ∀ (R : Type u) [CommRing R] [Algebra k R] (x : P →ₗ[k] R),
        (x ∘ₗ μ) ∘ₗ (TensorProduct.comm k P P).toLinearMap = x ∘ₗ μ := by
  refine ⟨fun h R _ _ x ↦ by rw [LinearMap.comp_assoc, h], fun h ↦ V_separates fun R _ _ x ↦ ?_⟩
  rw [← LinearMap.comp_assoc, h]

/-- _lTf_L0yvrU-26689 (7:24:49) [prop] `A` is associative iff `δ` is coassociative. -/
theorem assoc_iff_coassoc :
    μ ∘ₗ μ.rTensor P = μ ∘ₗ μ.lTensor P ∘ₗ (TensorProduct.assoc k P P P).toLinearMap ↔
      ∀ (R : Type u) [CommRing R] [Algebra k R] (x : P →ₗ[k] R),
        x ∘ₗ μ ∘ₗ μ.rTensor P = x ∘ₗ μ ∘ₗ μ.lTensor P ∘ₗ (TensorProduct.assoc k P P P).toLinearMap :=
  ⟨fun h R _ _ x ↦ by rw [h], fun h ↦ V_separates fun R _ _ x ↦ h R x⟩

/-- _lTf_L0yvrU-26689 (7:24:49) [prop] `1 ∈ A` is a unit for `μ` iff `ε(x) = x(1)` is a counit
for `δ`. -/
theorem unit_iff_counit (e : P) :
    μ ∘ₗ (TensorProduct.mk k P P e) = LinearMap.id ↔
      ∀ (R : Type u) [CommRing R] [Algebra k R] (x : P →ₗ[k] R),
        x ∘ₗ μ ∘ₗ (TensorProduct.mk k P P e) = x :=
  ⟨fun h R _ _ x ↦ by rw [h, LinearMap.comp_id],
    fun h ↦ V_separates fun R _ _ x ↦ by rw [LinearMap.comp_id]; exact h R x⟩

/-- _lTf_L0yvrU-26634 (7:23:54) [prop] The multiplication is recovered from the diagonal `δ`:
`μ ↦ (x ↦ x ∘ μ)` is injective. -/
theorem mul_of_diag {μ μ' : P ⊗[k] P →ₗ[k] P}
    (h : ∀ (R : Type u) [CommRing R] [Algebra k R] (x : P →ₗ[k] R), x ∘ₗ μ = x ∘ₗ μ') : μ = μ' :=
  V_separates h

end Separate

/-! ## Monoids: the convolution algebra of distributions -/

section Conv

variable {k} {A : Type u} [CommRing A] [Bialgebra k A] (R : Type u) [CommRing R] [Algebra k R]

/-- _lTf_L0yvrU-27165 (7:32:45) [prop] The law of `Dist(G)` (convolution) induces the given law
on `G ⊆ Dist(G)` (Mathlib `AlgHom.toLinearMap_convMul`). -/
theorem conv_extends (f g : WithConv (A →ₐ[k] R)) :
    toConv (f * g).ofConv.toLinearMap = toConv f.ofConv.toLinearMap * toConv g.ofConv.toLinearMap :=
  AlgHom.toLinearMap_convMul f g

/-- _lTf_L0yvrU-27502 (7:38:22) [prop] `Dist(G)(k')` is an associative algebra and `G(k')` is a
submonoid of it (injective monoid map). -/
noncomputable def pointsToDist : WithConv (A →ₐ[k] R) →* WithConv (A →ₗ[k] R) where
  toFun f := toConv f.ofConv.toLinearMap
  map_one' := rfl
  map_mul' f g := AlgHom.toLinearMap_convMul f g

noncomputable example : Algebra R (WithConv (A →ₗ[k] R)) := inferInstance

theorem pointsToDist_injective : Function.Injective (pointsToDist (k := k) R (A := A)) := fun f g h ↦ by
  have := congrArg ofConv h
  exact WithConv.ofConv_injective (AlgHom.toLinearMap_injective this)

/-- _lTf_L0yvrU-27502 (7:38:22) [prop] For a group (Hopf algebra), `G(k')` lies in the units of
`Dist(G)(k')`. -/
theorem points_isUnit {H : Type u} [CommRing H] [HopfAlgebra k H] (f : WithConv (H →ₐ[k] R)) :
    IsUnit (pointsToDist R f) := by
  have h1 := LinearMap.algHom_comp_convMul_distrib f.ofConv (toConv LinearMap.id)
    (toConv (HopfAlgebra.antipode k (A := H)))
  have h2 := LinearMap.algHom_comp_convMul_distrib f.ofConv
    (toConv (HopfAlgebra.antipode k (A := H))) (toConv LinearMap.id)
  rw [LinearMap.id_mul_antipode, LinearMap.algHom_comp_convOne] at h1
  rw [LinearMap.antipode_mul_id, LinearMap.algHom_comp_convOne] at h2
  refine ⟨⟨pointsToDist R f, toConv (f.ofConv.toLinearMap ∘ₗ HopfAlgebra.antipode k), ?_, ?_⟩, rfl⟩
  · apply WithConv.ofConv_injective
    rw [h1]; rfl
  · apply WithConv.ofConv_injective
    rw [h2]; rfl

end Conv

/-! ## Hyperalgebra -/

section Hyper

variable {k} (A : Type u) [CommRing A] [Bialgebra k A] (R : Type u) [CommRing R] [Algebra k R]

/-- The augmentation ideal `I = Ker ε`. -/
abbrev augIdeal (k : Type u) [CommRing k] (A : Type u) [CommRing A] [Bialgebra k A] : Ideal A := RingHom.ker (Bialgebra.counitAlgHom k A)

/-- _lTf_L0yvrU-27899 (7:44:59) [def] The distributions concentrated at the origin, vanishing on a
power of `I = Ker ε` (an `𝒪`-submodule; that it is a subalgebra is not formalised). -/
def hyper : Submodule R (A →ₗ[k] R) where
  carrier := {u | ∃ n : ℕ, ∀ a ∈ augIdeal k A ^ n, u a = 0}
  zero_mem' := ⟨0, fun _ _ ↦ rfl⟩
  add_mem' := by
    rintro u v ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨max m n, fun a ha ↦ ?_⟩
    rw [LinearMap.add_apply, hm a (Ideal.pow_le_pow_right (le_max_left m n) ha),
      hn a (Ideal.pow_le_pow_right (le_max_right m n) ha), add_zero]
  smul_mem' := by
    rintro c u ⟨n, hn⟩
    exact ⟨n, fun a ha ↦ by rw [LinearMap.smul_apply, hn a ha, smul_zero]⟩

/-- _lTf_L0yvrU-27965 (7:46:05) [prop] The splitting `Dist(G) = 𝒪 ⊕ Dist⁺(G)`: every `u` is
uniquely `c · 1 + v` with `v(1) = 0` (`1 = ε` the unit of the convolution algebra). -/
theorem dist_split (u : WithConv (A →ₗ[k] R)) :
    ∃! p : R × WithConv (A →ₗ[k] R), p.2.ofConv 1 = 0 ∧ u = p.1 • 1 + p.2 := by
  have h1 : (1 : WithConv (A →ₗ[k] R)).ofConv 1 = 1 := by
    simp [LinearMap.convOne_apply]
  refine ⟨(u.ofConv 1, u - u.ofConv 1 • 1), ⟨?_, (add_sub_cancel _ u).symm⟩, ?_⟩
  · simp [h1]
  · rintro ⟨c, v⟩ ⟨hv, rfl⟩
    have hc : (c • (1 : WithConv (A →ₗ[k] R)) + v).ofConv 1 = c := by
      simp [h1, hv]
    simp only [Prod.mk.injEq]
    refine ⟨hc.symm, ?_⟩
    rw [hc, add_sub_cancel_left]

end Hyper

/-! ## Constant groups -/

section Constant

variable {k} (Γ : Type u) [Group Γ]

/-- The product of `Dist(Γ_k) = (k^Γ)^∨`, transposed from the comultiplication of `k^Γ`,
`(Δ f)(g, h) = f(g h)`. -/
noncomputable def constConv (u v : (Γ → k) →ₗ[k] k) : (Γ → k) →ₗ[k] k where
  toFun f := u (fun g ↦ v (fun h ↦ f (g * h)))
  map_add' f f' := by
    rw [← map_add]; congr 1; ext g; rw [Pi.add_apply, ← map_add]; rfl
  map_smul' c f := by
    rw [← map_smul]; congr 1; ext g; rw [Pi.smul_apply, ← map_smul]; rfl

/-- _lTf_L0yvrU-28231 (7:50:31) [ex] `Dist(Γ_k) = k[Γ]`: the evaluations `e_g` (the dual basis of
the basis of `k^Γ`) multiply like `Γ`: `e_g ⋆ e_h = e_{gh}`. -/
theorem constConv_eval (g h : Γ) :
    constConv Γ (LinearMap.proj g) (LinearMap.proj h) = (LinearMap.proj (g * h) : (Γ → k) →ₗ[k] k) :=
  rfl

theorem dualBasis_eq_eval {Γ : Type u} [Fintype Γ] [DecidableEq Γ] (g : Γ) :
    (Pi.basisFun k Γ).dualBasis g = LinearMap.proj g := by
  ext f; simp

/-- _lTf_L0yvrU-28424 (7:53:44) [prop] Representations of `Γ` on `M` are the `k[Γ]`-module
structures, for any group `Γ` (Mathlib `MonoidAlgebra.lift`). -/
noncomputable def repEquiv (Γ' : Type u) [Group Γ'] (M : Type u) [AddCommGroup M] [Module k M] :
    (Γ' →* Module.End k M) ≃ (MonoidAlgebra k Γ' →ₐ[k] Module.End k M) :=
  MonoidAlgebra.lift k (Module.End k M) Γ'

/-- _lTf_L0yvrU-28489 (7:54:49) [ex] For the constant group, the augmentation ideal `I ⊆ k^Γ`
(functions vanishing at `1`) satisfies `I² = I`; hence `Lie(Γ_k) = (I/I²)^∨ = 0`. -/
theorem aug_sq_eq (Γ' : Type*) [Group Γ'] [DecidableEq Γ'] :
    RingHom.ker (Pi.evalRingHom (fun _ : Γ' ↦ k) (1 : Γ')) ^ 2 =
      RingHom.ker (Pi.evalRingHom (fun _ : Γ' ↦ k) (1 : Γ')) := by
  apply le_antisymm (Ideal.pow_le_self two_ne_zero)
  intro f hf
  have hf' : f 1 = 0 := hf
  have he : (1 - Pi.single 1 1 : Γ' → k) ∈ RingHom.ker (Pi.evalRingHom (fun _ : Γ' ↦ k) (1 : Γ')) := by
    rw [RingHom.mem_ker, Pi.evalRingHom_apply]; simp
  have : f = f * (1 - Pi.single 1 1) := by
    ext g
    by_cases hg : g = 1
    · subst hg; simp [hf']
    · simp [hg]
  rw [this, pow_two]
  exact Ideal.mul_mem_mul hf he

/-- _lTf_L0yvrU-28615 (7:56:55) [ex] `ℤ/2 → μ₂`, `1 ↦ -1`: on points over a domain in which `2 ≠ 0`
it is a bijection `{1, -1} = μ₂(R)` … -/
theorem mu2_points {R : Type*} [CommRing R] [IsDomain R] (x : R) :
    x ^ 2 = 1 ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro h
    have : (x - 1) * (x + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (eq_neg_of_add_eq_zero_left h')
  · rintro (rfl | rfl) <;> ring

theorem one_ne_neg_one_of_two {R : Type*} [CommRing R] (h2 : (2 : R) ≠ 0) : (1 : R) ≠ -1 := by
  intro h
  apply h2
  linear_combination h

/-- _lTf_L0yvrU-28615 (7:56:55) [ex] … trivial on points in characteristic `2` (`-1 = 1`), while
`μ₂` has the non-trivial point `1 + ε` over `k[ε]` (non-zero Lie algebra, `Part01.mu_p_nontrivial`). -/
theorem mu2_char2 {R : Type*} [CommRing R] [CharP R 2] : (-1 : R) = 1 := by
  rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, CharTwo.two_eq_zero]

example [Nontrivial k] [CharP k 2] :
    Part01.onePlusEps k ∈ rootsOfUnity (2 ^ 1) (DualNumber k) ∧ Part01.onePlusEps k ≠ 1 :=
  Part01.mu_p_nontrivial k 2 1 one_ne_zero

end Constant

end Buffalo.Groupes.Part02
