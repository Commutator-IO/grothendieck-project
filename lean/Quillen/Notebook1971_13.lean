import Mathlib

/-!
# Quillen, notebook 1971-13, p. 13: good submodules pass to quotients

Daniel Quillen's research notebook 1971-13 (Clay Mathematics Institute,
<https://www.claymath.org/library/Quillen/Working_papers/quillen%201971/1971-13.pdf>) works in
November 1971 towards the homotopy property `K(A) ≅ K(A[z])` of the `K`-theory of coherent
modules. For a finitely generated `A[z]`-module `E` he calls a finitely generated `A`-submodule
`L ⊂ E` *good* when `L` generates `E` over `A[z]` and `z⁻¹L ⊂ L`, where `z⁻¹L` is the set of
`e` with `z e ∈ L`; such an `L` gives a two-term resolution of `E` by the induced modules
`A[z] ⊗ L` and `A[z] ⊗ z⁻¹L` (p. 15). The lemma of p. 13 (entry of November 10, 1971), in our
words: if `E' ⊂ E` is an `A[z]`-submodule and `L ∩ E'` generates `E'`, then `L ∩ E'` is good for
`E'` and the image of `L` is good for `E / E'`. His proof is the one formalised here.

We write `z` for an `A`-linear endomorphism of an `A`-module `E` (an `A[z]`-module structure),
and drop finiteness, which plays no role.

* `GeneratesUnder z L E'`: the submodules `zⁿ L` span a submodule containing `E'`;
* `le_sup_map_of_generates`: if `L' ⊂ E'` generates the `z`-stable submodule `E'`, then
  `E' ⊂ L' + z E'` (the step `e' = l' + z e'₁`);
* `mem_sup_of_smul_mem_sup`: **the lemma**: if `z⁻¹L ⊂ L`, `E'` is `z`-stable and `L ∩ E'`
  generates `E'`, then `z e ∈ L + E'` implies `e ∈ L + E'`;
* `comap_map_mkQ_le`: the same in the quotient: `z⁻¹L'' ⊂ L''` for the image `L''` of `L` in
  `E ⧸ E'` and the endomorphism induced by `z`;
* `comap_inf_le`: the easy half, `z⁻¹(L ∩ E') ∩ E' ⊂ L ∩ E'`.
-/

namespace Quillen.Notebook1971_13

open Submodule

variable {A E : Type*} [CommRing A] [AddCommGroup E] [Module A E]

/-- `L` generates the submodule `E'` under `z`: `E'` lies in the span of the `zⁿ L`, `n ≥ 0`. -/
def GeneratesUnder (z : Module.End A E) (L E' : Submodule A E) : Prop :=
  E' ≤ ⨆ n : ℕ, L.map (z ^ n)

/-- If `L' ⊂ E'` generates the `z`-stable submodule `E'`, then every element of `E'` is of the
form `l' + z e'₁` with `l' ∈ L'` and `e'₁ ∈ E'`. -/
theorem le_sup_map_of_generates {z : Module.End A E} {L' E' : Submodule A E}
    (hL' : L' ≤ E') (hE' : E'.map z ≤ E') (hgen : GeneratesUnder z L' E') :
    E' ≤ L' ⊔ E'.map z := by
  refine hgen.trans (iSup_le fun n => ?_)
  cases n with
  | zero => rw [pow_zero, Module.End.one_eq_id, map_id]; exact le_sup_left
  | succ k =>
    refine le_sup_of_le_right ?_
    rw [pow_succ', Module.End.mul_eq_comp, map_comp]
    refine map_mono ?_
    -- `z ^ k` maps `L'` into `E'`, since `L' ⊂ E'` and `E'` is `z`-stable.
    induction k with
    | zero => simpa [Module.End.one_eq_id] using hL'
    | succ j ih =>
      rw [pow_succ', Module.End.mul_eq_comp, map_comp]
      exact (map_mono ih).trans hE'

/-- **Quillen, notebook 1971-13, p. 13.** Let `z` be an endomorphism of `E`, `L` a submodule with
`z⁻¹L ⊂ L`, and `E'` a `z`-stable submodule generated under `z` by `L ∩ E'`. If `z e ∈ L + E'`,
then `e ∈ L + E'`. -/
theorem mem_sup_of_smul_mem_sup {z : Module.End A E} {L E' : Submodule A E}
    (hL : L.comap z ≤ L) (hE' : E'.map z ≤ E') (hgen : GeneratesUnder z (L ⊓ E') E')
    {e : E} (he : z e ∈ L ⊔ E') : e ∈ L ⊔ E' := by
  obtain ⟨l, hl, e', he', hze⟩ := mem_sup.1 he
  -- Write `e' = l' + z e'₁`.
  have h := le_sup_map_of_generates inf_le_right hE' hgen he'
  obtain ⟨l', hl', y, hy, hy'⟩ := mem_sup.1 h
  obtain ⟨e₁, he₁, rfl⟩ := mem_map.1 hy
  -- Then `z (e - e'₁) = l + l' ∈ L`, hence `e - e'₁ ∈ L`.
  have hz : z (e - e₁) ∈ L := by
    rw [map_sub, ← hze, ← hy']
    convert L.add_mem hl (mem_inf.1 hl').1 using 1
    abel
  simpa using add_mem_sup (hL hz) he₁

/-- **Quillen, notebook 1971-13, p. 13**, in the quotient: the image `L''` of `L` in `E ⧸ E'`
satisfies `z⁻¹L'' ⊂ L''` for the endomorphism of `E ⧸ E'` induced by `z`. -/
theorem comap_map_mkQ_le {z : Module.End A E} {L E' : Submodule A E}
    (hL : L.comap z ≤ L) (hE' : E' ≤ E'.comap z) (hgen : GeneratesUnder z (L ⊓ E') E') :
    (L.map E'.mkQ).comap (E'.mapQ E' z hE') ≤ L.map E'.mkQ := by
  intro x hx
  obtain ⟨e, rfl⟩ := E'.mkQ_surjective x
  have hE'map : E'.map z ≤ E' := map_le_iff_le_comap.2 hE'
  rw [mem_comap, mkQ_apply, mapQ_apply, ← mkQ_apply, ← mem_comap, comap_map_mkQ,
    sup_comm] at hx
  rw [← mem_comap, comap_map_mkQ, sup_comm]
  exact mem_sup_of_smul_mem_sup hL hE'map hgen hx

/-- The easy half of the lemma: `z⁻¹(L ∩ E') ∩ E' ⊂ L ∩ E'` when `z⁻¹L ⊂ L`. -/
theorem comap_inf_le {z : Module.End A E} {L E' : Submodule A E} (hL : L.comap z ≤ L) :
    (L ⊓ E').comap z ⊓ E' ≤ L ⊓ E' :=
  fun _ ⟨h1, h2⟩ => ⟨hL (mem_comap.2 (mem_comap.1 h1).1), h2⟩

end Quillen.Notebook1971_13
