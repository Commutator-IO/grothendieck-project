import Mathlib.Data.Set.Card
import Mathlib.Data.Multiset.Bind
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Group.Action.Defs

/-!
# Folder 98, pages 10–12: the axioms of a theory of norms in the model of G-sets

The modernised reading `transcripts/98/98.modern.tex` (« Une théorie axiomatique des normes »)
gives, in a category with finite sums, a class `𝒩` of morphisms with (i) identities,
(ii) composition, (iii) base change, (iv) sums, (v) the quotients `(X^n_Y)/H`, `H ⊆ 𝔖_n`; a
degree with (i bis) `deg id = 1`, (ii bis) `deg (vu) = deg v · deg u`, (iii bis) invariance under
base change, (iv bis) additivity, (v bis) `deg ((X^n_Y)/H → Y) = card(E^n/H)` for `deg u = r`,
`E = {1, …, r}`; and canonical sections `Can_{X/Y} : Y → Sym^r_Y(X)` with (i ter)
`Can_{X/X} = id`, (ii ter) the transitivity diagram of page 11, (iii ter) base change,
(iv ter) additivity. Example I: `G`-sets, `u` of degree `r` when all its fibres have `r`
elements, `Can_{X/Y}(y)` the class of the points of the fibre « rangés dans un ordre
quelconque »; the page says the axioms are « immédiats » and « se vérifient aussitôt ».

What is formalised, for maps of types (the action of `G` only has to be respected, `can_smul`):

* `hasDeg_id`, `hasDeg_comp`, `hasDeg_pullback`, `hasDeg_sum`, `hasDeg_quotPow` — (i)–(v) and
  (i bis)–(v bis): maps with fibres of constant finite cardinality form a class closed under
  identities, composition, base change, sums and quotients `(X^n_Y)/H`, with the degree rules;
  the fibre of `(X^n_Y)/H` over `y` is in bijection with `E^n/H`.
* `Can`, with `Sym^r_Y(X)` as pairs `(y, m)`, `m` a multiset of `r` points of `u⁻¹(y)`, and
  `can_id`, `can_comp`, `can_pullback`, `can_sum` — (i ter)–(iv ter), (ii ter) being the
  diagram of page 11 with `can : Sym^s_Z(Sym^r_Y X) → Sym^s_Z(Sym^r_Z X) → Sym^{rs}_Z X`.
* `can_smul` — `Can` is compatible with the action of a group `G` when `u` is equivariant.

Not formalised: Example II (finite locally free morphisms of schemes, with the norm of page 2),
Example III (covering spaces and `Φ(E) = X ×^Γ E`), and the transitivity of norms of pages 6–8.

**What the formalisation finds.** Example I satisfies all the axioms, including (ii ter), which
nothing in the folder verifies for any example: the fibre of `v ∘ u` over `z` is the disjoint
union of the fibres of `u` over the `s` points of the fibre of `v`. The group plays no role
beyond the equivariance of `Can`; (v bis) holds for every `n` and every `H`, with the fibre of
`(X^n_Y)/H` identified with `E^n/H` by any enumeration of the fibre of `u`.

What this certifies is that the reading holds together at this point, not that it is what the
pages say (issue #26).
-/

namespace Grothendieck.Folder98

variable {X Y Z : Type*}

/-- `u` has degree `r`: every fibre of `u` is finite with `r` elements (Example I). -/
def HasDeg (u : X → Y) (r : ℕ) : Prop := ∀ y, (u ⁻¹' {y}).Finite ∧ (u ⁻¹' {y}).ncard = r

/-- The fibre of `u` over `y`, as a finset. -/
noncomputable def fib {u : X → Y} {r : ℕ} (hu : HasDeg u r) (y : Y) : Finset X :=
  (hu y).1.toFinset

@[simp] theorem mem_fib {u : X → Y} {r : ℕ} (hu : HasDeg u r) {y : Y} {x : X} :
    x ∈ fib hu y ↔ u x = y := by simp [fib]

theorem card_fib {u : X → Y} {r : ℕ} (hu : HasDeg u r) (y : Y) : (fib hu y).card = r := by
  rw [fib, ← Set.ncard_eq_toFinset_card _ (hu y).1, (hu y).2]

theorem hasDeg_of_finset {u : X → Y} {r : ℕ} (s : Y → Finset X) (hs : ∀ y x, x ∈ s y ↔ u x = y)
    (hc : ∀ y, (s y).card = r) : HasDeg u r := fun y => by
  have : u ⁻¹' {y} = ↑(s y) := by ext x; simp [hs]
  rw [this]
  exact ⟨Finset.finite_toSet _, by rw [Set.ncard_coe_finset, hc]⟩

/-! ### The class `𝒩` and the degree: (i)–(iv), (i bis)–(iv bis) -/

/-- (i), (i bis) -/
theorem hasDeg_id : HasDeg (id : X → X) 1 :=
  hasDeg_of_finset (fun x => {x}) (fun y x => by simp [eq_comm]) fun _ => rfl

/-- (ii), (ii bis): `deg (v ∘ u) = deg v · deg u`. -/
theorem hasDeg_comp {u : X → Y} {v : Y → Z} {r s : ℕ} (hu : HasDeg u r) (hv : HasDeg v s) :
    HasDeg (v ∘ u) (s * r) := by
  classical
  refine hasDeg_of_finset (fun z => (fib hv z).biUnion (fib hu)) (fun z x => by simp) fun z => ?_
  rw [Finset.card_biUnion]
  · simp [card_fib]
  · intro y _ y' _ hyy'
    exact Finset.disjoint_left.2 fun x hx hx' => hyy' (((mem_fib hu).1 hx).symm.trans
      ((mem_fib hu).1 hx'))

/-- The fibre product `X ×_Y Y'`. -/
def Pullback (u : X → Y) {Y' : Type*} (f : Y' → Y) := {p : X × Y' // u p.1 = f p.2}

/-- (iii), (iii bis): the degree is invariant under base change. -/
theorem hasDeg_pullback {u : X → Y} {r : ℕ} (hu : HasDeg u r) {Y' : Type*} (f : Y' → Y) :
    HasDeg (fun p : Pullback u f => p.1.2) r := by
  classical
  refine hasDeg_of_finset (fun y' => (fib hu (f y')).attach.map
    ⟨fun x => ⟨(x.1, y'), (mem_fib hu).1 x.2⟩, fun a b h => Subtype.ext (by
      simpa using congrArg (fun p : Pullback u f => p.1.1) h)⟩) (fun y' p => ?_) fun y' => ?_
  · constructor
    · simp only [Finset.mem_map, Finset.mem_attach, true_and]
      rintro ⟨x, rfl⟩; rfl
    · rintro rfl
      simp only [Finset.mem_map, Finset.mem_attach, true_and]
      exact ⟨⟨p.1.1, (mem_fib hu).2 p.2⟩, rfl⟩
  · simp [card_fib]

/-- (iv), (iv bis): `deg (u₁, u₂) = deg u₁ + deg u₂`. -/
theorem hasDeg_sum {X₁ X₂ : Type*} {u₁ : X₁ → Y} {u₂ : X₂ → Y} {r₁ r₂ : ℕ}
    (h₁ : HasDeg u₁ r₁) (h₂ : HasDeg u₂ r₂) : HasDeg (Sum.elim u₁ u₂) (r₁ + r₂) := by
  classical
  refine hasDeg_of_finset (fun y => (fib h₁ y).disjSum (fib h₂ y)) (fun y x => ?_) fun y => ?_
  · cases x <;> simp
  · simp [card_fib]


/-! ### (v), (v bis): the quotients `(X^n_Y)/H` -/

/-- The `n`-fold fibre product `X^n_Y`, as pairs `(y, t)` with `t : Fin n → u⁻¹(y)`. -/
def FibPow (u : X → Y) (n : ℕ) := {p : Y × (Fin n → X) // ∀ i, u (p.2 i) = p.1}

/-- `H ⊆ 𝔖_n` permuting the factors. -/
def fibPowSetoid (u : X → Y) {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) :
    Setoid (FibPow u n) where
  r p q := p.1.1 = q.1.1 ∧ ∃ σ ∈ H, q.1.2 = p.1.2 ∘ σ
  iseqv := ⟨fun p => ⟨rfl, 1, H.one_mem, rfl⟩,
    fun ⟨h1, σ, hσ, h⟩ => ⟨h1.symm, σ⁻¹, H.inv_mem hσ, by rw [h]; ext; simp⟩,
    fun ⟨h1, σ, hσ, h⟩ ⟨h1', τ, hτ, h'⟩ => ⟨h1.trans h1', σ * τ, H.mul_mem hσ hτ,
      by rw [h', h]; rfl⟩⟩

/-- `(X^n_Y)/H`. -/
def QuotPow (u : X → Y) {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) :=
  Quotient (fibPowSetoid u H)

/-- Its projection to `Y`. -/
def QuotPow.proj {u : X → Y} {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} :
    QuotPow u H → Y :=
  Quotient.lift (fun p : FibPow u n => p.1.1) fun _ _ h => h.1

/-- `E^n/H` for a set `E`. -/
def powSetoid (E : Type*) {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) : Setoid (Fin n → E) where
  r s t := ∃ σ ∈ H, t = s ∘ σ
  iseqv := ⟨fun _ => ⟨1, H.one_mem, rfl⟩,
    fun ⟨σ, hσ, h⟩ => ⟨σ⁻¹, H.inv_mem hσ, by rw [h]; ext; simp⟩,
    fun ⟨σ, hσ, h⟩ ⟨τ, hτ, h'⟩ => ⟨σ * τ, H.mul_mem hσ hτ, by rw [h', h]; rfl⟩⟩

/-- (v), (v bis): if `u` has degree `r`, the projection `(X^n_Y)/H → Y` has degree
`card(E^n/H)`, `E = {1, …, r}`. -/
theorem hasDeg_quotPow {u : X → Y} {r : ℕ} (hu : HasDeg u r) {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n))) :
    HasDeg (QuotPow.proj : QuotPow u H → Y) (Nat.card (Quotient (powSetoid (Fin r) H))) := by
  classical
  intro y
  -- an enumeration of the fibre
  have hc : Fintype.card (fib hu y) = r := by simp [card_fib]
  let ι : Fin r ≃ fib hu y := (Fintype.equivFinOfCardEq hc).symm
  let g : Quotient (powSetoid (Fin r) H) → (QuotPow.proj : QuotPow u H → Y) ⁻¹' {y} :=
    Quotient.lift (fun s => ⟨Quotient.mk _ ⟨(y, fun i => (ι (s i)).1),
        fun i => (mem_fib hu).1 (ι (s i)).2⟩, rfl⟩)
      (fun s t ⟨σ, hσ, h⟩ => Subtype.ext (Quotient.sound ⟨rfl, σ, hσ, by rw [h]; rfl⟩))
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      induction a using Quotient.inductionOn with | h s => ?_
      induction b using Quotient.inductionOn with | h t => ?_
      obtain ⟨-, σ, hσ, h⟩ := Quotient.exact (congrArg Subtype.val hab)
      refine Quotient.sound ⟨σ, hσ, funext fun i => ι.injective (Subtype.ext ?_)⟩
      exact congrFun h i
    · rintro ⟨q, hq⟩
      induction q using Quotient.inductionOn with | h p => ?_
      have hp : p.1.1 = y := hq
      refine ⟨Quotient.mk _ fun i => ι.symm ⟨p.1.2 i, (mem_fib hu).2 ((p.2 i).trans hp)⟩,
        Subtype.ext (Quotient.sound ⟨hp.symm, 1, H.one_mem, ?_⟩)⟩
      ext i; simp
  have hfin : Finite ((QuotPow.proj : QuotPow u H → Y) ⁻¹' {y}) :=
    Finite.of_surjective g hg.2
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq, Nat.card_congr (Equiv.ofBijective g hg).symm]


/-! ### The canonical sections `Can_{X/Y} : Y → Sym^r_Y(X)`: (i ter)–(iv ter) -/

/-- `Sym^r_Y(X) = (X^r_Y)/𝔖_r`: a point `y` and a multiset of `r` points of `u⁻¹(y)`. -/
def SymY (u : X → Y) (r : ℕ) :=
  Σ y : Y, {m : Multiset X // Multiset.card m = r ∧ ∀ x ∈ m, u x = y}

/-- `Can_{X/Y}(y)`: the class of the `r` points of the fibre, in any order (page 11). -/
noncomputable def Can {u : X → Y} {r : ℕ} (hu : HasDeg u r) (y : Y) : SymY u r :=
  ⟨y, (fib hu y).val, by simp [card_fib], fun x hx => (mem_fib hu).1 hx⟩

theorem SymY.ext {u : X → Y} {r : ℕ} {p q : SymY u r} (h1 : p.1 = q.1) (h2 : p.2.1 = q.2.1) :
    p = q := by
  obtain ⟨y, m, hm⟩ := p
  obtain ⟨y', m', hm'⟩ := q
  simp only at h1 h2
  subst h1 h2
  rfl

/-- `Sym^s` of a morphism over `Z`. -/
def SymY.map {A B : Type*} {a : A → Z} {b : B → Z} {s : ℕ} (f : A → B)
    (hf : ∀ x, b (f x) = a x) (p : SymY a s) : SymY b s :=
  ⟨p.1, p.2.1.map f, by simp [p.2.2.1], fun x hx => by
    obtain ⟨x', hx', rfl⟩ := Multiset.mem_map.1 hx
    rw [hf]; exact p.2.2.2 x' hx'⟩

/-- `can : Sym^r_Y(X) → Sym^r_Z(X)` for `X → Y → Z`. -/
def SymY.push {u : X → Y} (v : Y → Z) {r : ℕ} (p : SymY u r) : SymY (v ∘ u) r :=
  ⟨v p.1, p.2.1, p.2.2.1, fun x hx => by simp [p.2.2.2 x hx]⟩

/-- `can : Sym^s_Z(Sym^r_Z(X)) → Sym^{rs}_Z(X)`, the union of the multisets. -/
def SymY.flatten {w : X → Z} {r s : ℕ} (p : SymY (fun q : SymY w r => q.1) s) :
    SymY w (s * r) :=
  ⟨p.1, p.2.1.bind fun q => q.2.1, by
    rw [Multiset.card_bind, Multiset.map_congr rfl fun q _ => q.2.2.1, Multiset.map_const',
      Multiset.sum_replicate, p.2.2.1, smul_eq_mul],
    fun x hx => by
      obtain ⟨q, hq, hxq⟩ := Multiset.mem_bind.1 hx
      rw [q.2.2.2 x hxq]; exact p.2.2.2 q hq⟩

/-- (i ter): `Can_{X/X} = id`, the fibre of `id` over `x` being `{x}`. -/
theorem can_id (x : X) : (Can hasDeg_id x).2.1 = {x} := by
  change (fib hasDeg_id x).val = {x}
  rw [← Finset.singleton_val]
  congr 1
  ext; simp

/-- (ii ter), the transitivity diagram of page 11: for `X → Y → Z` of degrees `r`, `s`,
`can ∘ can ∘ Sym^s(Can_{X/Y}) ∘ Can_{Y/Z} = Can_{X/Z}`. -/
theorem can_comp {u : X → Y} {v : Y → Z} {r s : ℕ} (hu : HasDeg u r) (hv : HasDeg v s) (z : Z) :
    SymY.flatten (SymY.map (SymY.push v) (fun _ => rfl)
      (SymY.map (Can hu) (fun _ => rfl) (Can hv z))) = Can (hasDeg_comp hu hv) z := by
  refine SymY.ext rfl ?_
  change Multiset.bind (((fib hv z).val.map (Can hu)).map (SymY.push v)) (fun q => q.2.1) =
    (fib (hasDeg_comp hu hv) z).val
  rw [Multiset.map_map, Multiset.bind_map]
  change (fib hv z).val.bind (fun y => (fib hu y).val) = _
  have hnd : ((fib hv z).val.bind fun y => (fib hu y).val).Nodup := by
    refine Multiset.nodup_bind.2 ⟨fun y _ => (fib hu y).nodup, ?_⟩
    refine (fib hv z).nodup.pairwise fun y _ y' _ hyy' => ?_
    exact Multiset.disjoint_left.2 fun hx hx' => hyy' (((mem_fib hu).1 hx).symm.trans
      ((mem_fib hu).1 hx'))
  refine (Multiset.Nodup.ext hnd (fib _ z).nodup).2 fun x => ?_
  · simp only [Multiset.mem_bind, Finset.mem_val, mem_fib, Function.comp_apply]
    exact ⟨fun ⟨y, hy, hxy⟩ => hxy ▸ hy, fun h => ⟨u x, h, rfl⟩⟩

/-- (iii ter): `Can` commutes with base change along `f : Y' → Y`. -/
theorem can_pullback {u : X → Y} {r : ℕ} (hu : HasDeg u r) {Y' : Type*} (f : Y' → Y) (y' : Y') :
    (Can (hasDeg_pullback hu f) y').2.1.map (fun p => p.1.1) = (Can hu (f y')).2.1 := by
  change (fib (hasDeg_pullback hu f) y').val.map _ = (fib hu (f y')).val
  have hnd : ((fib (hasDeg_pullback hu f) y').val.map fun p => p.1.1).Nodup := by
    refine (fib _ y').nodup.map_on fun p hp q hq h => Subtype.ext (Prod.ext h ?_)
    exact ((mem_fib _).1 hp).trans ((mem_fib _).1 hq).symm
  refine (Multiset.Nodup.ext hnd (fib _ _).nodup).2 fun x => ?_
  · simp only [Multiset.mem_map, Finset.mem_val, mem_fib]
    exact ⟨fun ⟨p, hp, hx⟩ => hx ▸ p.2.trans (congrArg f hp),
      fun hx => ⟨⟨(x, y'), hx⟩, rfl, rfl⟩⟩

/-- (iv ter): for `X = X₁ ⊔ X₂`, `Can_{X/Y}` is the sum of `Can_{X₁/Y}` and `Can_{X₂/Y}`. -/
theorem can_sum {X₁ X₂ : Type*} {u₁ : X₁ → Y} {u₂ : X₂ → Y} {r₁ r₂ : ℕ}
    (h₁ : HasDeg u₁ r₁) (h₂ : HasDeg u₂ r₂) (y : Y) :
    (Can (hasDeg_sum h₁ h₂) y).2.1 =
      (Can h₁ y).2.1.map Sum.inl + (Can h₂ y).2.1.map Sum.inr := by
  change (fib (hasDeg_sum h₁ h₂) y).val =
    (fib h₁ y).val.map Sum.inl + (fib h₂ y).val.map Sum.inr
  have hnd : ((fib h₁ y).val.map Sum.inl + (fib h₂ y).val.map Sum.inr).Nodup := by
    rw [Multiset.nodup_add]
    refine ⟨(fib h₁ y).nodup.map Sum.inl_injective, (fib h₂ y).nodup.map Sum.inr_injective,
      Multiset.disjoint_left.2 fun ha hb => ?_⟩
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 ha
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.1 hb
    exact Sum.inr_ne_inl hb
  refine (Multiset.Nodup.ext (fib _ y).nodup hnd).2 fun x => ?_
  cases x <;> simp

/-- `Can` is compatible with the action of `G` (page 11): for `u` equivariant,
`Can(g y) = g · Can(y)`. -/
theorem can_smul {G : Type*} [Group G] [MulAction G X] [MulAction G Y] {u : X → Y} {r : ℕ}
    (hu : HasDeg u r) (hequiv : ∀ (g : G) x, u (g • x) = g • u x) (g : G) (y : Y) :
    (Can hu (g • y)).2.1 = (Can hu y).2.1.map (g • ·) := by
  change (fib hu (g • y)).val = (fib hu y).val.map (g • ·)
  have hinj : Function.Injective (g • · : X → X) := fun a b h => by
    simpa using congrArg (g⁻¹ • ·) h
  refine (Multiset.Nodup.ext (fib _ _).nodup ((fib hu y).nodup.map hinj)).2 fun x => ?_
  simp only [Finset.mem_val, mem_fib, Multiset.mem_map]
  constructor
  · intro hx
    refine ⟨g⁻¹ • x, ?_, by simp⟩
    rw [hequiv, hx, inv_smul_smul]
  · rintro ⟨x', hx', rfl⟩
    rw [hequiv, hx']

end Grothendieck.Folder98
