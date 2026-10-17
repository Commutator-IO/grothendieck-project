import Mathlib

/-!
# Folder 115, pages 3–7: Isbell duality from the kernel transform

The modernised reading `transcripts/115/115.modern.tex` (« La dualité d'Isbell, telle que
la cote 115 l'établit ») attaches to a kernel `X ∈ (A × B)^`, a presheaf contravariant in
both variables, two transforms `ˢX : Â^op → B̂` and `ᵈX : B̂^op → Â` with

  `Hom_Â(L, ᵈX(M)) ≅ X(L, M) ≅ Hom_B̂(M, ˢX(L))`,

an adjunction between `Â` and `B̂^op` (pages 3–5). Taking `B = A^op` and the hom of `A` as
kernel (page 7) gives `𝒪 ⊣ Spec : Â ⇄ (A^∨)^op` with `𝒪(Φ)(a) = Hom(Φ, y a)` and
`Spec(Ψ)(a) = Hom(Ψ, Hom_A(a, -))`: Isbell duality. This is the reachable part of finding
`115-isbell-duality-derived-from-kernels` of `src/content/findings.ts` (the finding's
question, whether this derivation is in print, is not a mathematical one).

What is formalised. The kernel is written `K : Aᵒᵖ ⥤ C ⥤ Type u`, `A`, `C` small; the
page's kernel on `A × B` is the case `C = Bᵒᵖ`, and the hom of `A` is `K = coyoneda`
(`C = A`).

* `kernelS K : (Aᵒᵖ ⥤ Type u)ᵒᵖ ⥤ C ⥤ Type u`, `ˢK(L)(c) = Hom(L, K(-, c))`, and
  `kernelD K : (C ⥤ Type u)ᵒᵖ ⥤ Aᵒᵖ ⥤ Type u`, `ᵈK(M)(a) = Hom(M, K(a, -))`.
* `kernelEquiv`: `Hom(M, ˢK(L)) ≃ Hom(L, ᵈK(M))`, both sides being the families
  `L(a) × M(c) → K(a, c)` natural in `a` and `c`; `kernelAdj`: `(ˢK)ʳᵒᵖ ⊣ ᵈK`, the dual
  adjunction of pages 3–5, for every kernel.
* `isbell`: the case `K = coyoneda`, `𝒪 ⊣ Spec`; `isbellO_obj_obj` and
  `isbellSpec_obj_obj` check that the specialised transforms are the reading's `𝒪` and
  `Spec` on the nose (`rfl`).
* `isbellO_yoneda`, `isbellSpec_coyoneda`: on representables, `𝒪(y a) ≅ Hom_A(a, -)` and
  `Spec(Hom_A(a, -)) ≅ y a` (Yoneda); `isbellO_preservesColimits`: `𝒪` sends colimits of
  `Â` to limits of `A^∨`, being a left adjoint into `(A^∨)^op`.

Holds as stated: the duality is literally the kernel adjunction at `K = Hom`. Not
formalised: the eleven-node wheel of page 5, the families `(Aᵢ)` and the uniqueness of
`𝒪` and `Spec` from their restriction along `y`.
-/

namespace Grothendieck.Folder115

open CategoryTheory Opposite Limits

universe u

variable {A : Type u} [SmallCategory A] {C : Type u} [SmallCategory C]

/-- The left transform `ˢK(L)(c) = Hom(L, K(-, c))` of a kernel `K`, contravariant in `L`. -/
abbrev kernelS (K : Aᵒᵖ ⥤ C ⥤ Type u) : (Aᵒᵖ ⥤ Type u)ᵒᵖ ⥤ C ⥤ Type u :=
  (K.flip ⋙ yoneda).flip

/-- The right transform `ᵈK(M)(a) = Hom(M, K(a, -))` of a kernel `K`, contravariant in
`M`. -/
abbrev kernelD (K : Aᵒᵖ ⥤ C ⥤ Type u) : (C ⥤ Type u)ᵒᵖ ⥤ Aᵒᵖ ⥤ Type u :=
  (K ⋙ yoneda).flip

/-- The two transforms are mutually right adjoint: a map `M ⟶ ˢK(L)` and a map
`L ⟶ ᵈK(M)` are the same family `L(a) × M(c) → K(a, c)`. -/
def kernelEquiv (K : Aᵒᵖ ⥤ C ⥤ Type u) (L : Aᵒᵖ ⥤ Type u) (M : C ⥤ Type u) :
    (M ⟶ (kernelS K).obj (op L)) ≃ (L ⟶ (kernelD K).obj (op M)) where
  toFun β :=
    { app := fun a => TypeCat.ofHom fun l =>
        { app := fun c => TypeCat.ofHom fun m => (β.app c m).app a l
          naturality := fun c c' f => ConcreteCategory.hom_ext _ _ fun m => by
            exact (congr_arg (fun φ => φ.app a l) (types_congr_hom (β.naturality f) m) :) }
      naturality := fun a a' g => ConcreteCategory.hom_ext _ _ fun l =>
        NatTrans.ext (funext fun c => ConcreteCategory.hom_ext _ _ fun m => by
          exact (types_congr_hom ((β.app c m).naturality g) l :)) }
  invFun α :=
    { app := fun c => TypeCat.ofHom fun m =>
        { app := fun a => TypeCat.ofHom fun l => (α.app a l).app c m
          naturality := fun a a' g => ConcreteCategory.hom_ext _ _ fun l => by
            exact (congr_arg (fun φ => φ.app c m) (types_congr_hom (α.naturality g) l) :) }
      naturality := fun c c' f => ConcreteCategory.hom_ext _ _ fun m =>
        NatTrans.ext (funext fun a => ConcreteCategory.hom_ext _ _ fun l => by
          exact (types_congr_hom ((α.app a l).naturality f) m :)) }
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The dual adjunction of pages 3–5**, for every kernel: `ˢK` (seen as a functor into
the opposite category) is left adjoint to `ᵈK`. -/
def kernelAdj (K : Aᵒᵖ ⥤ C ⥤ Type u) : (kernelS K).rightOp ⊣ kernelD K :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun L M => (opEquiv _ _).trans (kernelEquiv K L M.unop)
      homEquiv_naturality_left_symm := by intros; rfl
      homEquiv_naturality_right := by intros; rfl }

/-- `𝒪 : Â → (A^∨)^op`, the kernel transform at `K = Hom_A`. -/
abbrev isbellO : (Aᵒᵖ ⥤ Type u) ⥤ (A ⥤ Type u)ᵒᵖ := (kernelS (coyoneda (C := A))).rightOp

/-- `Spec : (A^∨)^op → Â`, the kernel transform at `K = Hom_A`. -/
abbrev isbellSpec : (A ⥤ Type u)ᵒᵖ ⥤ Aᵒᵖ ⥤ Type u := kernelD (coyoneda (C := A))

/-- **Isbell duality (page 7)**: `𝒪 ⊣ Spec`, as the kernel adjunction for the hom. -/
def isbell : (isbellO : (Aᵒᵖ ⥤ Type u) ⥤ _) ⊣ isbellSpec := kernelAdj coyoneda

/-- `𝒪(Φ)(a) = Hom(Φ, y a)`, as in the reading. -/
theorem isbellO_obj_obj (Φ : Aᵒᵖ ⥤ Type u) (a : A) :
    ((isbellO.obj Φ).unop).obj a = (Φ ⟶ yoneda.obj a) := rfl

/-- `Spec(Ψ)(a) = Hom(Ψ, Hom_A(a, -))`, as in the reading. -/
theorem isbellSpec_obj_obj (Ψ : A ⥤ Type u) (a : A) :
    (isbellSpec.obj (op Ψ)).obj (op a) = (Ψ ⟶ coyoneda.obj (op a)) := rfl

/-- On representables, `𝒪(y a) ≅ Hom_A(a, -)`. -/
def isbellO_yoneda (a : A) : (isbellO.obj (yoneda.obj a)).unop ≅ coyoneda.obj (op a) :=
  NatIso.ofComponents (fun _ => Equiv.toIso yonedaEquiv) (fun _ =>
    ConcreteCategory.hom_ext _ _ fun _ => rfl)

/-- On corepresentables, `Spec(Hom_A(a, -)) ≅ y a`. -/
def isbellSpec_coyoneda (a : A) : isbellSpec.obj (op (coyoneda.obj (op a))) ≅ yoneda.obj a :=
  NatIso.ofComponents (fun _ => Equiv.toIso coyonedaEquiv) (fun _ =>
    ConcreteCategory.hom_ext _ _ fun _ => rfl)

/-- `𝒪` sends colimits of presheaves to colimits of `(A^∨)^op`, i.e. limits of
copresheaves; dually `Spec` preserves limits. -/
theorem isbellO_preservesColimits :
    PreservesColimitsOfSize.{u, u} (isbellO : (Aᵒᵖ ⥤ Type u) ⥤ _) :=
  isbell.leftAdjoint_preservesColimits

theorem isbellSpec_preservesLimits :
    PreservesLimitsOfSize.{u, u} (isbellSpec : (A ⥤ Type u)ᵒᵖ ⥤ _) :=
  isbell.rightAdjoint_preservesLimits

end Grothendieck.Folder115
