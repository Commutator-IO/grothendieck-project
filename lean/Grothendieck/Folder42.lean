import Mathlib

/-!
# Folder 42: Lemme 1, the proposition of page 3, Lemme 2, Corollaire 1

The modernised reading `transcripts/42/42.modern.tex` (manuscript pages 3–5)
states:

> **Proposition (page 3).** Let `X` be a locally Noetherian sober space and `F` a
> sheaf on `X` such that (H): for every `x` there is a nonempty open `U` of
> `closure {x}` on which every generization map `F_y → F_x` is injective. Then
> `Γ(X, F) → lim_x F_x` (coherent families of germs) is bijective.
>
> **Lemme 1.** For a coherent family `(ξ_x)` and a section `s ∈ F(U)`, the locus
> `{x ∈ U : s_x = ξ_x}` is open.
>
> **Lemme 2.** Let `A` be a Noetherian ring and `𝔭` a prime ideal of `A`. Then
> 1. there exists `f ∈ A - 𝔭` such that `A_f → A_𝔭` is injective;
> 2. if moreover `A → A_𝔭` is already injective, then `A_𝔮 → A_𝔭` is injective
>    for every prime ideal `𝔮 ⊇ 𝔭`.
>
> **Corollaire 1.** For `X` locally Noetherian, `Γ(X, 𝒪_X) ≅ lim_x 𝒪_{X,x}`.

All are proved here, Corollaire 1 for `X = Spec A` with `A` Noetherian (the
affine case, to which the reading reduces it). What this certifies is that the
reading holds together, not that it is what the page says (issue #26): that is
for a reader with the leaf in front of them.

What the proofs make plain. The step « constructible and stable under
generization, hence open » is used only in the form proved here as
`isOpen_of_stableUnderGeneralization`: a set stable under generization that
contains, with each point `x`, a nonempty open of `closure {x}`, is open in a
Noetherian sober space. Lemme 2 (2) does not use the Noetherian hypothesis.
Lemme 2 (1) uses it only to make the kernel of `A → A_𝔭` finitely generated —
which is where the reading's footnote bears: the kernel is the set of elements
killed by *some* element outside `𝔭`, not by every one. Corollaire 1 needs, from
Lemme 2, only that one `f ∉ 𝔭` kills that kernel.
-/

namespace Grothendieck.Folder42

open IsLocalization TopologicalSpace

variable {A : Type*} [CommRing A]

/-- A map out of a localisation `S = M⁻¹A`, induced by `g : A → P`, is injective
as soon as everything `g` kills is already killed in `S`. -/
theorem lift_injective {M : Submonoid A} {S : Type*} [CommRing S] [Algebra A S]
    [IsLocalization M S] {P : Type*} [CommRing P] {g : A →+* P}
    (hg : ∀ y : M, IsUnit (g y)) (h : ∀ x, g x = 0 → algebraMap A S x = 0) :
    Function.Injective (IsLocalization.lift (S := S) hg) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M z
  have hgx : g x = 0 := by
    have := congrArg (IsLocalization.lift (S := S) hg) e
    rw [map_mul, hz, zero_mul, IsLocalization.lift_eq] at this
    exact this.symm
  rw [h x hgx] at e
  exact (IsLocalization.map_units S s).mul_left_eq_zero.mp e

variable (p : Ideal A) [p.IsPrime]

/-- The map `A_f → A_𝔭`, for `f ∉ 𝔭`. -/
noncomputable def awayToAtPrime (f : A) (hf : f ∉ p) :
    Localization.Away f →+* Localization.AtPrime p :=
  IsLocalization.lift (M := Submonoid.powers f)
    (fun y => IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p)
      ⟨y, (Submonoid.powers_le.2 (show f ∈ p.primeCompl from hf)) y.2⟩)

/-- The map `A_𝔮 → A_𝔭`, for primes `𝔭 ⊆ 𝔮`. -/
noncomputable def atPrimeToAtPrime (q : Ideal A) [q.IsPrime] (hpq : p ≤ q) :
    Localization.AtPrime q →+* Localization.AtPrime p :=
  IsLocalization.lift (M := q.primeCompl)
    (fun y => IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p)
      ⟨y, fun h => y.2 (hpq h)⟩)

/-- The kernel of `A → A_𝔭`, for `A` Noetherian, is killed by one element outside `𝔭`. -/
theorem exists_mul_eq_zero_of_ker [IsNoetherianRing A] :
    ∃ f ∉ p, ∀ y, algebraMap A (Localization.AtPrime p) y = 0 → f * y = 0 := by
  classical
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian
    (RingHom.ker (algebraMap A (Localization.AtPrime p))) : Submodule.FG _)
  have kill : ∀ x ∈ t, ∃ s : p.primeCompl, (s : A) * x = 0 := fun x hx => by
    have : x ∈ RingHom.ker (algebraMap A (Localization.AtPrime p)) :=
      ht ▸ Submodule.subset_span hx
    exact (IsLocalization.map_eq_zero_iff p.primeCompl _ x).1 this
  choose! s hs using kill
  let f : A := ∏ x ∈ t, (s x : A)
  have hf : f ∈ p.primeCompl := Submonoid.prod_mem _ fun x _ => (s x).2
  have hspan : ∀ y ∈ Submodule.span A (t : Set A), f * y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun x => (s x : A)) hx
      show (∏ x ∈ t, (s x : A)) * x = 0
      rw [hc, mul_comm (s x : A) c, mul_assoc, hs x hx, mul_zero]
    | zero => exact mul_zero f
    | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
    | smul c a _ ha => rw [smul_eq_mul, mul_left_comm, ha, mul_zero]
  exact ⟨f, hf, fun y hy => hspan y (ht.symm ▸ hy)⟩

/-- **Lemme 2 (1).** Over a Noetherian ring, some `f ∉ 𝔭` makes `A_f → A_𝔭`
injective. -/
theorem lemme2_1 [IsNoetherianRing A] :
    ∃ (f : A) (hf : f ∉ p), Function.Injective (awayToAtPrime p f hf) := by
  obtain ⟨f, hf, hJ⟩ := exists_mul_eq_zero_of_ker p
  refine ⟨f, hf, lift_injective _ fun y hy => ?_⟩
  exact (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ y).2
    ⟨⟨f, Submonoid.mem_powers f⟩, hJ y hy⟩

/-- **Lemme 2 (2).** If `A → A_𝔭` is injective, so is `A_𝔮 → A_𝔭` for every
prime `𝔮 ⊇ 𝔭`. No Noetherian hypothesis is needed. -/
theorem lemme2_2 (hinj : Function.Injective (algebraMap A (Localization.AtPrime p)))
    (q : Ideal A) [q.IsPrime] (hpq : p ≤ q) :
    Function.Injective (atPrimeToAtPrime p q hpq) :=
  lift_injective _ fun x hx => by
    rw [hinj (hx.trans (map_zero _).symm), map_zero]


section Topology

variable {X : Type*} [TopologicalSpace X]

/-- **The topological step of Lemme 1 (page 3).** In a Noetherian sober space, a set `E` stable
under generization that contains, with each of its points `x`, a nonempty open of `closure {x}`
(equivalently `W ∩ closure {x}` for an open `W ∋ x`), is open. Noetherian induction on the closed
sets in which `Eᶜ` is dense. -/
theorem isOpen_of_stableUnderGeneralization [NoetherianSpace X] [QuasiSober X] {E : Set X}
    (hgen : StableUnderGeneralization E)
    (hloc : ∀ x ∈ E, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ∩ closure {x} ⊆ E) : IsOpen E := by
  have key : ∀ Z : Closeds X, (Z : Set X) ⊆ closure ((Z : Set X) ∩ Eᶜ) →
      (Z : Set X) ∩ E = ∅ := by
    intro Z
    induction Z using WellFoundedLT.induction with
    | _ Z IH =>
    intro hd
    by_cases h₁ : IsPreirreducible (Z : Set X)
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hyZ, hyE⟩
      have hirr : IsIrreducible (Z : Set X) := ⟨⟨y, hyZ⟩, h₁⟩
      have hg := hirr.isGenericPoint_genericPoint Z.isClosed
      have hzE : hirr.genericPoint ∈ E := hgen (hg.specializes hyZ) hyE
      obtain ⟨W, hW, hzW, hWE⟩ := hloc _ hzE
      obtain ⟨w, hwW, ⟨hwZ, hwE⟩⟩ := mem_closure_iff.1 (hd hg.mem) W hW hzW
      exact hwE (hWE ⟨hwW, by rw [hg.def]; exact hwZ⟩)
    · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at h₁
      obtain ⟨z₁, z₂, hz₁, hz₂, h, hz₁', hz₂'⟩ := h₁
      have piece : ∀ z : Set X, IsClosed z → ¬ (Z : Set X) ⊆ z →
          ∃ Z' : Closeds X, Z' < Z ∧ (Z' : Set X) ∩ E = ∅ ∧
            closure ((Z : Set X) ∩ z ∩ Eᶜ) ⊆ Z' := by
        intro z hz hz'
        let Z' : Closeds X := ⟨closure ((Z : Set X) ∩ z ∩ Eᶜ), isClosed_closure⟩
        have sub : (Z' : Set X) ⊆ (Z : Set X) ∩ z :=
          closure_minimal (fun x hx => hx.1) (Z.isClosed.inter hz)
        have lt : Z' < Z := by
          refine lt_of_le_of_ne (fun x hx => (sub hx).1) fun e => hz' fun x hx => ?_
          have : x ∈ (Z' : Set X) := by rw [e]; exact hx
          exact (sub this).2
        refine ⟨Z', lt, IH Z' lt ?_, subset_rfl⟩
        exact closure_mono fun x hx => ⟨subset_closure hx, hx.2⟩
      obtain ⟨Z₁, -, e₁, s₁⟩ := piece z₁ hz₁ hz₁'
      obtain ⟨Z₂, -, e₂, s₂⟩ := piece z₂ hz₂ hz₂'
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hyZ, hyE⟩
      have hy := hd hyZ
      have hsplit : (Z : Set X) ∩ Eᶜ ⊆ ((Z : Set X) ∩ z₁ ∩ Eᶜ) ∪ ((Z : Set X) ∩ z₂ ∩ Eᶜ) := by
        rintro x ⟨hxZ, hxE⟩
        rcases h hxZ with h' | h'
        · exact Or.inl ⟨⟨hxZ, h'⟩, hxE⟩
        · exact Or.inr ⟨⟨hxZ, h'⟩, hxE⟩
      have hy' := closure_mono hsplit hy
      rw [closure_union] at hy'
      rcases hy' with h' | h'
      · exact (Set.eq_empty_iff_forall_notMem.1 e₁) y ⟨s₁ h', hyE⟩
      · exact (Set.eq_empty_iff_forall_notMem.1 e₂) y ⟨s₂ h', hyE⟩
  let T : Closeds X := ⟨closure Eᶜ, isClosed_closure⟩
  have hT := key T (closure_mono fun x hx => ⟨subset_closure hx, hx⟩)
  refine isClosed_compl_iff.1 (closure_subset_iff_isClosed.1 fun x hx hxE => ?_)
  exact (Set.eq_empty_iff_forall_notMem.1 hT) x ⟨hx, hxE⟩

end Topology

/-- `A_𝔮 → A_𝔭` is the identity on `A`. -/
theorem atPrimeToAtPrime_algebraMap (q : Ideal A) [q.IsPrime] (hpq : p ≤ q) (x : A) :
    atPrimeToAtPrime p q hpq (algebraMap A _ x) = algebraMap A _ x :=
  IsLocalization.lift_eq _ x

/-- If `f` kills the kernel of `A → A_𝔭`, then `A_𝔮 → A_𝔭` is injective for every prime
`𝔮 ⊇ 𝔭` with `f ∉ 𝔮`: the injectivity condition (H) on the open `D(f) ∩ V(𝔭)` of `V(𝔭)`. -/
theorem atPrimeToAtPrime_injective_of_mul_eq_zero {f : A}
    (hf : ∀ y, algebraMap A (Localization.AtPrime p) y = 0 → f * y = 0)
    (q : Ideal A) [q.IsPrime] (hpq : p ≤ q) (hfq : f ∉ q) :
    Function.Injective (atPrimeToAtPrime p q hpq) :=
  lift_injective _ fun y hy =>
    (IsLocalization.map_eq_zero_iff q.primeCompl _ y).2 ⟨⟨f, hfq⟩, hf y hy⟩

/-- The map `(A_f)_𝔔 → A_𝔭`, for `f ∉ 𝔭` and a prime `𝔔` of `A_f` whose trace on `A` contains
`𝔭`: the page's form of Lemme 2 (2). -/
noncomputable def awayAtPrimeToAtPrime (f : A) (hf : f ∉ p) (Q : Ideal (Localization.Away f))
    [Q.IsPrime] (hQ : p ≤ Q.comap (algebraMap A _)) :
    Localization.AtPrime Q →+* Localization.AtPrime p :=
  IsLocalization.lift (M := Q.primeCompl) (g := awayToAtPrime p f hf) fun y => by
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, e⟩ :=
      IsLocalization.surj (Submonoid.powers f) (y : Localization.Away f)
    have hfn : IsUnit (algebraMap A (Localization.Away f) (f ^ n)) :=
      IsLocalization.map_units _ (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
    have ha : a ∉ p := fun ha => by
      have h1 : algebraMap A (Localization.Away f) a ∈ Q := hQ ha
      rw [← e] at h1
      rcases Ideal.IsPrime.mem_or_mem inferInstance h1 with h2 | h2
      · exact y.2 h2
      · exact Ideal.IsPrime.ne_top inferInstance (Ideal.eq_top_of_isUnit_mem Q h2 hfn)
    have hu : IsUnit (awayToAtPrime p f hf y *
        awayToAtPrime p f hf (algebraMap A _ (f ^ n))) := by
      rw [← map_mul, e]
      unfold awayToAtPrime
      rw [IsLocalization.lift_eq]
      exact IsLocalization.map_units (Localization.AtPrime p) (⟨a, ha⟩ : p.primeCompl)
    exact isUnit_of_mul_isUnit_left hu

/-- **Lemme 2 (2), in the page's form.** If `A_f → A_𝔭` is injective, so is `(A_f)_𝔔 → A_𝔭`
for every prime `𝔔` of `A_f` above a prime containing `𝔭`. -/
theorem lemme2_2_away (f : A) (hf : f ∉ p) (hinj : Function.Injective (awayToAtPrime p f hf))
    (Q : Ideal (Localization.Away f)) [Q.IsPrime] (hQ : p ≤ Q.comap (algebraMap A _)) :
    Function.Injective (awayAtPrimeToAtPrime p f hf Q hQ) :=
  lift_injective _ fun x hx => by
    rw [hinj (hx.trans (map_zero _).symm), map_zero]

/-- Lemme 2 (1) and (2) together, as page 5 uses them: some `f ∉ 𝔭` makes every
`(A_f)_𝔔 → A_𝔭` injective. -/
theorem lemme2_page [IsNoetherianRing A] :
    ∃ (f : A) (hf : f ∉ p), ∀ (Q : Ideal (Localization.Away f)) [Q.IsPrime]
      (hQ : p ≤ Q.comap (algebraMap A _)),
      Function.Injective (awayAtPrimeToAtPrime p f hf Q hQ) := by
  obtain ⟨f, hf, hinj⟩ := lemme2_1 p
  exact ⟨f, hf, fun Q _ hQ => lemme2_2_away p f hf hinj Q hQ⟩

omit p in
/-- A *coherent family* of germs of the structure sheaf of `Spec A`: one element `ξ 𝔭 ∈ A_𝔭`
for each prime, such that `ξ 𝔮 ↦ ξ 𝔭` under `A_𝔮 → A_𝔭` whenever `𝔭 ⊆ 𝔮`, i.e. whenever `𝔭` is a
generization of `𝔮`. These families form `lim_x 𝒪_{X,x}` along the specialization order. -/
def IsCoherent (ξ : ∀ P : PrimeSpectrum A, Localization.AtPrime P.asIdeal) : Prop :=
  ∀ (P Q : PrimeSpectrum A) (h : P.asIdeal ≤ Q.asIdeal),
    atPrimeToAtPrime P.asIdeal Q.asIdeal h (ξ Q) = ξ P

omit p in
/-- The germs of an element of `A` form a coherent family. -/
theorem isCoherent_algebraMap (a : A) :
    IsCoherent (fun P : PrimeSpectrum A => algebraMap A (Localization.AtPrime P.asIdeal) a) :=
  fun P Q h => atPrimeToAtPrime_algebraMap P.asIdeal Q.asIdeal h a

omit p in
/-- **Lemme 1 (page 3), for the structure sheaf of `Spec A`, `A` Noetherian.** For a coherent
family `ξ` and a fraction `a / s`, the locus `{𝔭 ∈ D(s) : ξ 𝔭 = a / s}` is open. -/
theorem lemme1 [IsNoetherianRing A] {ξ : ∀ P : PrimeSpectrum A, Localization.AtPrime P.asIdeal}
    (hξ : IsCoherent ξ) (a s : A) :
    IsOpen {P : PrimeSpectrum A | s ∉ P.asIdeal ∧
      ξ P * algebraMap A _ s = algebraMap A _ a} := by
  apply isOpen_of_stableUnderGeneralization
  · intro Q P hPQ hQ
    have h : P.asIdeal ≤ Q.asIdeal := (PrimeSpectrum.le_iff_specializes P Q).2 hPQ
    refine ⟨fun hs => hQ.1 (h hs), ?_⟩
    have := congrArg (atPrimeToAtPrime P.asIdeal Q.asIdeal h) hQ.2
    rwa [map_mul, hξ P Q h, atPrimeToAtPrime_algebraMap, atPrimeToAtPrime_algebraMap] at this
  · intro P hP
    obtain ⟨f, hf, hkill⟩ := exists_mul_eq_zero_of_ker P.asIdeal
    refine ⟨(PrimeSpectrum.basicOpen f : Set _) ∩ PrimeSpectrum.basicOpen s,
      (PrimeSpectrum.basicOpen f).isOpen.inter (PrimeSpectrum.basicOpen s).isOpen,
      ⟨hf, hP.1⟩, ?_⟩
    rintro Q ⟨⟨hfQ, hsQ⟩, hQP⟩
    have h : P.asIdeal ≤ Q.asIdeal :=
      (PrimeSpectrum.le_iff_specializes P Q).2 (specializes_iff_mem_closure.2 hQP)
    refine ⟨hsQ, atPrimeToAtPrime_injective_of_mul_eq_zero P.asIdeal hkill Q.asIdeal h hfQ ?_⟩
    rw [map_mul, hξ P Q h, atPrimeToAtPrime_algebraMap, atPrimeToAtPrime_algebraMap]
    exact hP.2

section
open AlgebraicGeometry StructureSheaf

omit p in
/-- **Corollaire 1 (page 4).** For `A` Noetherian, `A = Γ(Spec A, 𝒪)` is the limit of the local
rings `A_𝔭` along specialization: `a ↦ (a/1)_𝔭` is a bijection onto the coherent families.
Injectivity holds for every ring; surjectivity is Lemme 1 plus mathlib's description of the
structure sheaf as the sheaf of locally-fraction families. -/
theorem corollaire1 [IsNoetherianRing A] :
    Function.Bijective (fun a : A =>
      (⟨fun P : PrimeSpectrum A => algebraMap A (Localization.AtPrime P.asIdeal) a,
        isCoherent_algebraMap a⟩ : {ξ // IsCoherent ξ})) := by
  constructor
  · intro a b hab
    have hab' := congrArg Subtype.val hab
    apply (toOpenₗ_top_bijective (R := A) (M := A)).1
    apply Subtype.ext
    funext x
    have h := congrFun hab' x.1
    simp only [← Localization.mk_one_eq_algebraMap] at h
    exact h
  · rintro ⟨ξ, hξ⟩
    obtain ⟨a, ha⟩ := (toOpenₗ_top_bijective (R := A) (M := A)).2 ⟨fun x => ξ x.1, fun x => by
      have : (x.1 : PrimeSpectrum A).asIdeal.IsPrime := (x.1 : PrimeSpectrum A).isPrime
      obtain ⟨⟨a, ⟨s, hs⟩⟩, e⟩ :=
        IsLocalization.surj (x.1 : PrimeSpectrum A).asIdeal.primeCompl (ξ x.1)
      refine ⟨⟨_, lemme1 hξ a s⟩, ⟨hs, e⟩, CategoryTheory.homOfLE le_top, a, s, fun y => ⟨y.2.1, ?_⟩⟩
      show ξ y.1 = Localization.mk a ⟨s, y.2.1⟩
      rw [Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
      exact y.2.2⟩
    refine ⟨a, Subtype.ext (funext fun P => ?_)⟩
    have h := congrArg (fun t => t.1 ⟨P, trivial⟩) ha
    simp only at h
    show algebraMap A _ a = ξ P
    rw [← h, toOpenₗ_eq_const, ← Localization.mk_one_eq_algebraMap]
    rfl

end


section Sheaves

open CategoryTheory Opposite

universe u

variable {X : TopCat.{u}} (F : TopCat.Sheaf (Type u) X)

/-- A *coherent family of germs* of `F`: `ξ x ∈ F_x` for each `x`, with `ρ_{yx} (ξ y) = ξ x`
whenever `x ⤳ y` (`y` a specialization of `x`). -/
def IsCoherentGerms (ξ : ∀ x : X, ToType (F.presheaf.stalk x)) : Prop :=
  ∀ ⦃x y : X⦄ (h : x ⤳ y), F.presheaf.stalkSpecializes h (ξ y) = ξ x

/-- **Condition (H) (page 3).** Every point `x` has an open `W ∋ x` such that the generization
maps `F_y → F_x` are injective for `y ∈ W ∩ closure {x}` — i.e. on a nonempty open of
`closure {x}`. -/
def ConditionH : Prop :=
  ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∀ y ∈ (W : Set X) ∩ closure {x}, ∀ h : x ⤳ y,
    Function.Injective (fun t => F.presheaf.stalkSpecializes h t)

/-- **Lemme 1 (page 3).** Under (H), on a Noetherian sober space, the locus where a section
agrees with a coherent family of germs is open. -/
theorem lemme1_faisceau [NoetherianSpace X] [QuasiSober X] (hH : ConditionH F)
    {ξ : ∀ x : X, ToType (F.presheaf.stalk x)} (hξ : IsCoherentGerms F ξ)
    (U : Opens X) (s : ToType (F.1.obj (op U))) :
    IsOpen {x : X | ∃ hx : x ∈ U, F.presheaf.germ U x hx s = ξ x} := by
  apply isOpen_of_stableUnderGeneralization
  · rintro x y h ⟨hx, e⟩
    refine ⟨h.mem_open U.isOpen hx, ?_⟩
    rw [← hξ h, ← e, TopCat.Presheaf.germ_stalkSpecializes_apply]
  · rintro x ⟨hx, e⟩
    obtain ⟨W, hxW, hinj⟩ := hH x
    refine ⟨(W : Set X) ∩ U, W.isOpen.inter U.isOpen, ⟨hxW, hx⟩, ?_⟩
    rintro y ⟨⟨hyW, hyU⟩, hyx⟩
    have h : x ⤳ y := specializes_iff_mem_closure.2 hyx
    refine ⟨hyU, hinj y ⟨hyW, hyx⟩ h ?_⟩
    simp only
    rw [hξ h, TopCat.Presheaf.germ_stalkSpecializes_apply, e]

/-- **Proposition (page 3).** On a Noetherian sober space, under (H), a global section is the
same thing as a coherent family of germs. -/
theorem proposition [NoetherianSpace X] [QuasiSober X] (hH : ConditionH F) :
    Function.Bijective (fun s : ToType (F.1.obj (op ⊤)) =>
      (⟨fun x => F.presheaf.germ ⊤ x trivial s, fun _ _ h =>
        F.presheaf.germ_stalkSpecializes_apply (U := ⊤) (hy := trivial) h s⟩ :
        {ξ // IsCoherentGerms F ξ})) := by
  constructor
  · intro s t hst
    apply TopCat.Presheaf.section_ext F ⊤ s t
    intro x _
    exact congrFun (congrArg Subtype.val hst) x
  · rintro ⟨ξ, hξ⟩
    choose U hxU s hs using fun x => F.presheaf.exists_germ_eq (ξ x)
    let V : X → Opens X := fun x =>
      ⟨{y | ∃ hy : y ∈ U x, F.presheaf.germ (U x) y hy (s x) = ξ y},
        lemme1_faisceau F hH hξ (U x) (s x)⟩
    have hVU : ∀ x, V x ≤ U x := fun x y hy => hy.1
    let sf : ∀ x, ToType (F.1.obj (op (V x))) := fun x => F.1.map (homOfLE (hVU x)).op (s x)
    have hgerm : ∀ x y (hy : y ∈ V x), F.presheaf.germ (V x) y hy (sf x) = ξ y :=
      fun x y hy => by
        simp only [sf]
        rw [TopCat.Presheaf.germ_res_apply]
        exact hy.2
    have hcompat : TopCat.Presheaf.IsCompatible F.1 V sf := by
      intro x y
      apply TopCat.Presheaf.section_ext F
      intro z hz
      refine ((F.presheaf.germ_res_apply ((V x).infLELeft (V y)) z hz (sf x)).trans ?_).trans
        (F.presheaf.germ_res_apply ((V x).infLERight (V y)) z hz (sf y)).symm
      exact (hgerm x z _).trans (hgerm y z _).symm
    obtain ⟨g, hg, -⟩ := F.existsUnique_gluing' V ⊤ (fun _ => homOfLE le_top)
      (fun z _ => Opens.mem_iSup.2 ⟨z, hxU z, hs z⟩) sf hcompat
    refine ⟨g, Subtype.ext (funext fun x => ?_)⟩
    show F.presheaf.germ ⊤ x trivial g = ξ x
    rw [← hgerm x x ⟨hxU x, hs x⟩, ← hg x, TopCat.Presheaf.germ_res_apply]

end Sheaves
end Grothendieck.Folder42
