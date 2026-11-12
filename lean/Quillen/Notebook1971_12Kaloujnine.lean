import Mathlib

/-!
# Quillen, notebook 1971-12, pp. 21, 34: Kaloujnine's theorem `[A_r, A_s] ≤ A_{r+s}`

Daniel Quillen's research notebook 1971-12 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201971/1971-12.pdf>), p. 34:
for a sequence of normal subgroups `G_i` of a group `G`, let `A_r` be the group of
automorphisms `θ` with `θ(G_i) = G_i` and `θ` trivial on each `G_i / G_{i+r}`, that is
`θ(x)x⁻¹ ∈ G_{i+r}` for `x ∈ G_i`. Then `[A_r, A_s] ≤ A_{r+s}` (Kaloujnine; the page proves
it by the three-subgroup lemma in the semidirect product `G ⋊ Aut G`).

The proof here runs in `Equiv.Perm G`, where the holomorph lives: left translations `L_g` and
automorphisms `θ` satisfy `θ L_g θ⁻¹ = L_{θ g}` (`toPerm_mul_L_mul_inv`), so
`[L_x, θ] = L_{x θ(x)⁻¹}` (`commutatorElement_L_toPerm`), and the Hall–Witt identity gives
the three-subgroup lemma elementwise.

* `A r`: the subgroup `A_r` of `MulAut G`;
* `commutator_le`: **the statement**, `⁅A r, A s⁆ ≤ A (r + s)`.

No monotonicity of the `G_i` is needed, only their normality.
-/

namespace Quillen.Notebook1971_12Kaloujnine

open scoped commutatorElement

variable {G : Type*} [Group G] (F : ℕ → Subgroup G)

/-- Automorphisms as permutations. -/
abbrev T : MulAut G →* Equiv.Perm G := MulAut.toPerm G

/-- Left translation, as a homomorphism `G →* Perm G`. -/
def L : G →* Equiv.Perm G where
  toFun g := Equiv.mulLeft g
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

@[simp] theorem L_apply (g x : G) : L g x = g * x := rfl

@[simp] theorem L_symm_apply (g x : G) : (L g).symm x = g⁻¹ * x := rfl

@[simp] theorem T_apply (θ : MulAut G) (x : G) : T θ x = θ x := rfl

@[simp] theorem T_symm_apply (θ : MulAut G) (x : G) : (T θ).symm x = θ.symm x := rfl

theorem L_injective : Function.Injective (L : G → Equiv.Perm G) := fun a b h => by
  simpa using congrArg (fun f : Equiv.Perm G => f 1) h

theorem toPerm_mul_L_mul_inv (θ : MulAut G) (g : G) :
    T θ * L g * (T θ)⁻¹ = L (θ g) := by
  ext x
  change θ (g * θ.symm x) = θ g * x
  simp

theorem commutatorElement_L_toPerm (θ : MulAut G) (x : G) :
    ⁅L x, T θ⁆ = L (x * (θ x)⁻¹) := by
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc (T θ),
    ← map_inv, toPerm_mul_L_mul_inv, ← map_mul, map_inv]

/-- `A_r`: automorphisms preserving every `G_i` and trivial on every `G_i / G_{i+r}`. -/
def A (r : ℕ) : Subgroup (MulAut G) where
  carrier := {θ | (∀ i x, x ∈ F i ↔ θ x ∈ F i) ∧ ∀ i, ∀ x ∈ F i, θ x * x⁻¹ ∈ F (i + r)}
  one_mem' := ⟨fun _ _ => Iff.rfl, fun i x _ => by simp⟩
  mul_mem' := by
    rintro θ φ ⟨hθ1, hθ2⟩ ⟨hφ1, hφ2⟩
    refine ⟨fun i x => (hφ1 i x).trans (hθ1 i _), fun i x hx => ?_⟩
    have h1 := hθ2 i (φ x) ((hφ1 i x).mp hx)
    have h2 := hφ2 i x hx
    have : (θ * φ) x * x⁻¹ = (θ (φ x) * (φ x)⁻¹) * (φ x * x⁻¹) := by
      simp [mul_assoc]
    rw [this]
    exact (F (i + r)).mul_mem h1 h2
  inv_mem' := by
    rintro θ ⟨hθ1, hθ2⟩
    refine ⟨fun i x => ?_, fun i x hx => ?_⟩
    · rw [hθ1 i ((θ⁻¹) x)]; simp
    · have hy : θ⁻¹ x ∈ F i := by rw [hθ1 i]; simpa using hx
      have := hθ2 i (θ⁻¹ x) hy
      have hx' : θ (θ⁻¹ x) = x := by simp
      rw [hx'] at this
      have := (F (i + r)).inv_mem this
      simpa using this

variable {F}

theorem A_inv_apply {r : ℕ} {θ : MulAut G} (hθ : θ ∈ A F r) {i : ℕ} {x : G} (hx : x ∈ F i) :
    x * (θ x)⁻¹ ∈ F (i + r) := by
  have := (F (i + r)).inv_mem (hθ.2 i x hx)
  simpa using this

/-- `[L_x, θ] = L_y` with `y ∈ G_{i+r}` for `x ∈ G_i`, `θ ∈ A_r`. -/
theorem commutator_L_mem {r : ℕ} {θ : MulAut G} (hθ : θ ∈ A F r) {i : ℕ} {x : G}
    (hx : x ∈ F i) : ∃ y ∈ F (i + r), ⁅L x, T θ⁆ = L y :=
  ⟨_, A_inv_apply hθ hx, commutatorElement_L_toPerm θ x⟩

/-- **Notebook 1971-12, p. 34** (Kaloujnine): `⁅A_r, A_s⁆ ≤ A_{r+s}`. -/
theorem commutator_le [hF : ∀ i, (F i).Normal] (r s : ℕ) : ⁅A F r, A F s⁆ ≤ A F (r + s) := by
  rw [Subgroup.commutator_le]
  intro θ hθ φ hφ
  have hθi : θ⁻¹ ∈ A F r := (A F r).inv_mem hθ
  have hφi : φ⁻¹ ∈ A F s := (A F s).inv_mem hφ
  refine ⟨fun i x => ?_, fun i g hg => ?_⟩
  · simp only [commutatorElement_def, MulAut.mul_apply]
    rw [← hθ.1 i, ← hφ.1 i, ← hθi.1 i, ← hφi.1 i]
  · -- the three-subgroup lemma, elementwise, in `Perm G`
    -- `W₁ = ⁅φ, ⁅L g⁻¹, θ⁻¹⁆⁆` is a translation by an element of `G_{i+r+s}`
    obtain ⟨u, hu, hu'⟩ := commutator_L_mem hθi ((F i).inv_mem hg)
    obtain ⟨n₁, hn₁, hn₁'⟩ := commutator_L_mem hφ hu
    have hW₁ : ⁅T φ, ⁅(L g)⁻¹, (T θ)⁻¹⁆⁆ = L n₁⁻¹ := by
      rw [← map_inv, ← map_inv, hu', ← commutatorElement_inv, hn₁', map_inv]
    -- `W₂ = ⁅θ⁻¹, ⁅φ⁻¹, L g⁆⁆` is a translation by an element of `G_{i+s+r}`
    obtain ⟨v, hv, hv'⟩ := commutator_L_mem hφi hg
    obtain ⟨n₂, hn₂, hn₂'⟩ := commutator_L_mem hθi ((F (i + s)).inv_mem hv)
    have hW₂ : ⁅(T θ)⁻¹, ⁅(T φ)⁻¹, L g⁆⁆ = L n₂⁻¹ := by
      rw [← map_inv, ← map_inv, ← commutatorElement_inv (L g), hv', ← map_inv,
        ← commutatorElement_inv, hn₂', map_inv]
    -- the Hall–Witt identity
    have HW : ∀ x y z : Equiv.Perm G, ⁅z, ⁅x, y⁆⁆ =
        x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * z⁻¹ * y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆⁻¹ * y⁻¹ * x⁻¹ := by
      intro x y z; simp only [commutatorElement_def]; group
    have key := HW (T θ) (T φ) (L g)
    rw [hW₁, hW₂, ← map_commutatorElement, commutatorElement_L_toPerm] at key
    have hR : T θ * L g * (L n₁⁻¹)⁻¹ * (L g)⁻¹ * T φ * (L n₂⁻¹)⁻¹ *
        (T φ)⁻¹ * (T θ)⁻¹ = L (θ (g * n₁ * g⁻¹) * θ (φ n₂)) := by
      ext x; simp [mul_assoc]
    rw [hR] at key
    have key' := L_injective key
    have h1 : θ (g * n₁ * g⁻¹) ∈ F (i + (r + s)) := by
      rw [← hθ.1]
      exact (hF _).conj_mem n₁ (by rwa [← add_assoc]) g
    have h2 : θ (φ n₂) ∈ F (i + (r + s)) := by
      rw [← hθ.1, ← hφ.1]
      rwa [show i + (r + s) = i + s + r by omega]
    have := (F (i + (r + s))).mul_mem h1 h2
    rw [← key'] at this
    simpa using (F (i + (r + s))).inv_mem this

end Quillen.Notebook1971_12Kaloujnine
