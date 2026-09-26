import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

/-!
# Folder 158, Proposition 1 (§5.1)

The modernised reading `transcripts/158/158.modern.tex`, §5.1 (manuscript
pages 44–46), states:

> **Proposition 1.** Soit `M` un monoïde *fini* dont le groupe enveloppant est
> trivial et qui est pseudo-cofiltrant. Alors il existe `p ∈ M` tel que
> `up = p` pour tout `u ∈ M` — en particulier `p² = p` — et `M` est cofiltrant.

It is proved here as the reading states it, with no hypothesis added. The
proof follows the reading's three steps:

1. (`etape1`) pseudo-cofilteringness and finiteness give a `p` lying in every
   principal right ideal `uM`;
2. `M` acts on itself by left multiplication, and `E₀ = pM` is contained in
   `u(E₀) = upM` for every `u`; since `E₀` is finite, the inclusion is an
   equality, so each `u` permutes `E₀`;
3. the resulting monoid morphism `M → Perm(E₀)` lands in a group, hence is
   trivial, which gives `up = p`.

What the formalisation shows. The finiteness the reading's footnote flags —
used silently on the leaf to turn `E₀ ⊆ u(E₀)` into `E₀ = u(E₀)` — is exactly
where the proof needs it: `Set.eq_of_subset_of_ncard_le` requires the finiteness
of `u(E₀)`, and `Finite.surjective_iff_bijective` (a surjection of `E₀` onto
itself is a permutation) requires that of `E₀`. Nothing else in the argument
uses finiteness except step 1, where it turns "any two `uM` meet" into "all
of them meet". No hypothesis turned out to be superfluous: without
pseudo-cofilteringness the monoid `{1, a, b}` with `a, b` left zeros
(`xy = x` for `x ≠ 1`) is finite with trivial group completion but has no such
`p`; without finiteness the reading's own §6 (`Ep(E)`, `E` infinite) is the
counterexample (not formalised here).

Conventions. "Pseudo-cofiltrant" is the reading's footnote definition,
`∀ u v, ∃ u' v', u u' = v v'`; "cofiltrant" adds the equalising clause on the
same side, `∀ u v, ∃ w, u w = v w`, which is the side the proof produces.
"Trivial group completion" is stated as: every monoid morphism from `M` to a
group is trivial. The groups quantified over are those in `M`'s universe; the
group completion of `M` lives there, so this is the same condition, and taking
fewer groups only weakens the hypothesis.

What the formalisation found. The Proposition holds as stated, but the
reading's modern gloss on it does not. The gloss says `p` « engendre un idéal
à gauche minimal réduit à un zéro à gauche : c'est le noyau de Rees du monoïde
fini, dont la trivialité du groupe enveloppant force qu'il soit ponctuel ».
`Mp = {p}` is indeed a minimal left ideal; but the kernel (minimal two-sided
ideal) is `MpM = pM`, which need not be a point, and `p` is neither unique nor
a two-sided zero: `contre_noyau_non_ponctuel` exhibits a three-element monoid
satisfying every hypothesis whose kernel has two elements. (Also, `u p = p` for
all `u` makes `p` what semigroup theory usually calls a *right* zero.) mathlib
has no structure theory of finite semigroups (kernels, completely simple
semigroups), so the proof is self-contained.
-/

namespace Grothendieck.Folder158

universe u

/-- **Pseudo-cofiltrant** (the reading's footnote, from manuscript p. 55):
`∀ u, v`, `∃ u', v'` with `u u' = v v'` — any two principal right ideals meet. -/
def PseudoCofiltrant (M : Type u) [Monoid M] : Prop :=
  ∀ u v : M, ∃ u' v' : M, u * u' = v * v'

/-- **Cofiltrant**: pseudo-cofiltrant, and any two parallel arrows (here, any
two elements) are equalised further on: `∀ u, v`, `∃ w` with `u w = v w`. -/
def Cofiltrant (M : Type u) [Monoid M] : Prop :=
  PseudoCofiltrant M ∧ ∀ u v : M, ∃ w : M, u * w = v * w

/-- **Groupe enveloppant trivial**: every monoid morphism from `M` to a group is
trivial (the universal property of the group completion, for groups in `M`'s
universe, where the group completion lives). -/
def GroupeEnveloppantTrivial (M : Type u) [Monoid M] : Prop :=
  ∀ (G : Type u) [Group G] (f : M →* G), f = 1

variable {M : Type u} [Monoid M]

/-- **Step 1.** In a finite pseudo-cofiltering monoid, some `p` lies in every
principal right ideal: for every `u` there is `v` with `p = u v`. -/
theorem etape1 [Finite M] (h : PseudoCofiltrant M) :
    ∃ p : M, ∀ u : M, ∃ v : M, p = u * v := by
  classical
  have key : ∀ s : Finset M, ∃ p : M, ∀ u ∈ s, ∃ v : M, p = u * v := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp⟩
    | insert a s _ ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨p', v', e⟩ := h p a
      refine ⟨p * p', fun u hu => ?_⟩
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact ⟨v', e⟩
      · obtain ⟨v, hv⟩ := hp u hu
        exact ⟨v * p', by rw [hv, mul_assoc]⟩
  have := Fintype.ofFinite M
  obtain ⟨p, hp⟩ := key Finset.univ
  exact ⟨p, fun u => hp u (Finset.mem_univ u)⟩

/-- **Proposition 1.** Let `M` be a finite pseudo-cofiltering monoid with
trivial group completion. Then there is `p ∈ M` with `u p = p` for every
`u ∈ M`; in particular `p² = p`, and `M` is cofiltering. -/
theorem proposition1 [Finite M] (hpc : PseudoCofiltrant M)
    (hG : GroupeEnveloppantTrivial M) :
    ∃ p : M, (∀ u : M, u * p = p) ∧ p * p = p ∧ Cofiltrant M := by
  obtain ⟨p, hp⟩ := etape1 hpc
  -- `E₀ = pM`, the image of `p` in the regular representation.
  let E₀ : Set M := Set.range (p * ·)
  -- `E₀ ⊆ u(E₀)`, because `p ∈ upM`.
  have hsub : ∀ u : M, E₀ ⊆ (u * ·) '' E₀ := by
    rintro u x ⟨y, rfl⟩
    obtain ⟨v, hv⟩ := hp (u * p)
    refine ⟨p * (v * y), ⟨v * y, rfl⟩, ?_⟩
    change u * (p * (v * y)) = p * y
    conv_rhs => rw [hv]
    simp only [mul_assoc]
  -- Finiteness of `E₀` turns the inclusion into an equality.
  have heq : ∀ u : M, (u * ·) '' E₀ = E₀ := fun u =>
    (Set.eq_of_subset_of_ncard_le (hsub u) (Set.ncard_image_le (Set.toFinite _))
      (Set.toFinite _)).symm
  -- So each `u` maps `E₀` onto itself, bijectively since `E₀` is finite.
  let f : M → E₀ → E₀ := fun u x =>
    ⟨u * x, (heq u).subset ⟨x, x.2, rfl⟩⟩
  have hbij : ∀ u : M, Function.Bijective (f u) := fun u =>
    Finite.surjective_iff_bijective.1 fun y => by
      have hy : (y : M) ∈ (u * ·) '' E₀ := (heq u).symm.subset y.2
      obtain ⟨x, hx, e⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  -- The restriction `u ↦ u|E₀` is a morphism into the group `Perm E₀` …
  let φ : M →* Equiv.Perm E₀ :=
    { toFun := fun u => Equiv.ofBijective (f u) (hbij u)
      map_one' := by ext x; simp [f]
      map_mul' := fun a b => by ext x; simp [f, mul_assoc] }
  -- … hence trivial, which gives `u p = p`.
  have hup : ∀ u : M, u * p = p := fun u => by
    have h1 : φ u = 1 := by rw [hG _ φ]; rfl
    have h2 := congrArg (fun σ : Equiv.Perm E₀ => (σ ⟨p, 1, mul_one p⟩ : M)) h1
    simpa [φ, f] using h2
  exact ⟨p, hup, hup p, hpc, fun u v => ⟨p, by rw [hup u, hup v]⟩⟩

/-! ### The modern gloss: the kernel need not be a point

The reading glosses Proposition 1 as: « `p` est un idempotent qui engendre un
idéal à gauche minimal réduit à un zéro à gauche : c'est le noyau de Rees du
monoïde fini, dont la trivialité du groupe enveloppant force qu'il soit
ponctuel ». The first half is right (`Mp = {p}` is a minimal left ideal, and
`p` absorbs whatever multiplies it on the left, i.e. `p` is what semigroup
theory usually calls a *right* zero). The second half is false: the kernel
(the minimal two-sided ideal) is `MpM = pM`, which need not be a point, and
`p` is neither unique nor a two-sided zero.

The counterexample is the smallest one: two right zeros `a`, `b`
(`xa = a`, `xb = b` for all `x`) with an identity adjoined. -/

/-- The monoid `{1, a, b}` with `x a = a` and `x b = b` for every `x`. -/
inductive Contre
  | un
  | a
  | b
  deriving DecidableEq

instance : Fintype Contre :=
  ⟨{.un, .a, .b}, fun x => by cases x <;> decide⟩

instance : Monoid Contre where
  mul x y := match y with
    | .un => x
    | .a => .a
    | .b => .b
  one := .un
  mul_assoc x y z := by cases x <;> cases y <;> cases z <;> rfl
  one_mul x := by cases x <;> rfl
  mul_one x := by cases x <;> rfl

/-- `{1, a, b}` is pseudo-cofiltering: `u a = v a` for all `u, v`. -/
theorem contre_pseudoCofiltrant : PseudoCofiltrant Contre := fun u v =>
  ⟨.a, .a, by cases u <;> cases v <;> rfl⟩

/-- `{1, a, b}` has trivial group completion: `a = b a` forces `b ↦ 1`, and
`b = a b` forces `a ↦ 1`. -/
theorem contre_groupeEnveloppantTrivial : GroupeEnveloppantTrivial Contre := by
  intro G _ f
  have hb : f .b = 1 := by
    have h := f.map_mul .b .a
    exact mul_right_cancel (h.symm.trans (one_mul (f .a)).symm)
  have ha : f .a = 1 := by
    have h := f.map_mul .a .b
    exact mul_right_cancel (h.symm.trans (one_mul (f .b)).symm)
  ext x
  cases x
  · exact f.map_one
  · exact ha
  · exact hb

/-- The kernel of a monoid: the intersection of its principal two-sided ideals
`MxM` (equivalently of all its non-empty two-sided ideals; for a finite monoid
it is the minimal ideal, the Suschkewitsch–Rees kernel). -/
def noyau (M : Type u) [Monoid M] : Set M :=
  ⋂ x : M, {y | ∃ s t : M, y = s * x * t}

/-- **The gloss fails.** `{1, a, b}` satisfies the hypotheses of Proposition 1,
yet two distinct elements `a ≠ b` both satisfy `u p = p` for all `u`, neither
is a two-sided zero (`a b = b`), and the kernel is `{a, b}`, not a point. -/
theorem contre_noyau_non_ponctuel :
    PseudoCofiltrant Contre ∧ GroupeEnveloppantTrivial Contre ∧
      (∀ u : Contre, u * .a = .a) ∧ (∀ u : Contre, u * .b = .b) ∧
      Contre.a ≠ Contre.b ∧ Contre.a * Contre.b ≠ Contre.a ∧
      noyau Contre = {Contre.a, Contre.b} := by
  refine ⟨contre_pseudoCofiltrant, contre_groupeEnveloppantTrivial,
    fun u => by cases u <;> rfl, fun u => by cases u <;> rfl, by decide, by decide, ?_⟩
  ext y
  simp only [noyau, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  revert y
  decide

end Grothendieck.Folder158
