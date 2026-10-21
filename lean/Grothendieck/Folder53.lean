import Mathlib

/-!
# Folder 53, page 21: a cancellative algebraic monoid is a group

Page 21 of folder 53 opens with a « Rectification »: an affine monoid of finite type over a
field embeds as a closed submonoid of `M_n`, not of `GL_n`, « car on peut montrer que si `G`
est un monoïde de prés. finie sur un anneau `k`, tel que les translations à g (à dr.) sont
[illisible] [illisible] — p.ex. s'il ∃ mon. `G → G'`, `G'` un groupe — alors `G` est un objet
gr.-pr. » (transcription `transcripts/53/batch-02.fr.tex`, with « sont », « mon. » and
« gr.-pr. » uncertain). The modernised reading `transcripts/53/53.modern.tex` supplies
« monomorphismes » for the illegible words and the proof by Ax–Grothendieck; both are the
edition's reconstruction, not the page's. The statement over an algebraically closed field is
classical (Putcha, *Linear algebraic monoids*, 1988; Brion's survey, 2014).

This file proves the case of `K`-points, `K` algebraically closed, by the route the reading
proposes: a left translation is an injective polynomial self-map of a Zariski-closed set,
hence surjective by Ax–Grothendieck (`MvPolynomial.ax_grothendieck_zeroLocus`).

What is modelled. A *monoid of `K`-points with a polynomial law* is a monoid `M` with an
injective map `φ : M → (ι → K)` (`ι` finite) whose image is the zero locus of an ideal of
`K[X_i]`, and polynomials `m i` in two sets of variables with `φ (x * y) = law m (φ x) (φ y)`.
* `law`, `translation`, `eval_translation`: the law and its left translations as polynomials;
* `isUnit_of_isLeftCancelMul`: in such a monoid, if left multiplications are injective, every
  element is a unit (only left cancellation is used);
* `inv_mem_of_isClosed`: a submonoid of `GL_n(K)` which is closed in `GL_n` — cut out by
  polynomials in the entries and in `det⁻¹` — is a subgroup (the special case on page 21:
  a closed submonoid of `GL_n` is a group, the reason for `M_n`).

Not formalised: monoid schemes over a ring, scheme-theoretic monomorphisms, finite
presentation (the page's generality), and the embedding into `M_n` of page 30.
-/

open MvPolynomial

namespace Grothendieck.Folder53

variable {K ι : Type*} [Field K]

/-- The polynomial law: `law m a v i = m i (a, v)`, the variables `inl j` for `a`, `inr j`
for `v`. -/
noncomputable def law (m : ι → MvPolynomial (ι ⊕ ι) K) (a v : ι → K) : ι → K :=
  fun i => eval (Sum.elim a v) (m i)

/-- The left translation `v ↦ law m a v`, as polynomials in `v`. -/
noncomputable def translation (m : ι → MvPolynomial (ι ⊕ ι) K) (a : ι → K) :
    ι → MvPolynomial ι K :=
  fun i => bind₁ (Sum.elim (fun j => C (a j)) X) (m i)

theorem eval_translation (m : ι → MvPolynomial (ι ⊕ ι) K) (a : ι → K) :
    (fun v i => eval v (translation m a i)) = law m a := by
  funext v i
  simp only [translation, law, eval, eval₂Hom_bind₁]
  congr 2
  funext j
  cases j <;> simp

variable [IsAlgClosed K] [Finite ι]

/-- A monoid of `K`-points of an affine variety with a polynomial law, whose left translations
are injective, is a group (the reading of folder 53, page 21, over an algebraically closed
field). -/
theorem isUnit_of_isLeftCancelMul {M : Type*} [Monoid M] [IsLeftCancelMul M]
    (φ : M → ι → K) (hφ : Function.Injective φ) (I : Ideal (MvPolynomial ι K))
    (hI : Set.range φ = zeroLocus K I) (m : ι → MvPolynomial (ι ⊕ ι) K)
    (hm : ∀ x y, φ (x * y) = law m (φ x) (φ y)) (x : M) : IsUnit x := by
  have key := ax_grothendieck_zeroLocus I (translation m (φ x))
  rw [eval_translation, ← hI] at key
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := key (by rintro _ ⟨y, rfl⟩; exact ⟨x * y, hm x y⟩)
    (by rintro _ ⟨y, rfl⟩ _ ⟨z, rfl⟩ h; rw [← hm, ← hm] at h; rw [mul_left_cancel (hφ h)])
    ⟨1, rfl⟩
  have hxy : x * y = 1 := hφ (by rw [hm, hy])
  exact ⟨⟨x, y, hxy, mul_left_cancel (a := x) (by rw [← mul_assoc, hxy, one_mul, mul_one])⟩, rfl⟩

/-- The determinant of the generic matrix `(X (some (i, j)))`. -/
noncomputable def detPoly (n : ℕ) : MvPolynomial (Option (Fin n × Fin n)) K :=
  (Matrix.of fun i j => X (some (i, j))).det

/-- Coordinates on `GL_n(K)`: the entries and `det⁻¹`. -/
def glCoords {n : ℕ} (g : GL (Fin n) K) : Option (Fin n × Fin n) → K
  | none => (g⁻¹ : GL (Fin n) K).val.det
  | some ij => g.val ij.1 ij.2

/-- The matrix with entries `v (some (i, j))`. -/
def entries {n : ℕ} (v : Option (Fin n × Fin n) → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => v (some (i, j))

omit [IsAlgClosed K] in
theorem eval_detPoly {n : ℕ} (v : Option (Fin n × Fin n) → K) :
    eval v (detPoly n) = (entries v).det := by
  rw [detPoly, RingHom.map_det]
  congr 1
  ext i j
  simp [entries]

/-- Matrix multiplication on the coordinates `(A, t)`, `t = det A⁻¹`: `(A, t)(B, s) = (AB, ts)`. -/
noncomputable def glLaw (n : ℕ) :
    Option (Fin n × Fin n) → MvPolynomial (Option (Fin n × Fin n) ⊕ Option (Fin n × Fin n)) K
  | none => X (Sum.inl none) * X (Sum.inr none)
  | some (i, j) => ∑ k, X (Sum.inl (some (i, k))) * X (Sum.inr (some (k, j)))

/-- A submonoid of `GL_n(K)`, `K` algebraically closed, which is Zariski-closed in `GL_n`
(cut out by polynomials in the entries and `det⁻¹`) is a subgroup: the special case of
page 21 of folder 53 behind the rectification `GL_n ↦ M_n`. -/
theorem inv_mem_of_isClosed {n : ℕ} (S : Submonoid (GL (Fin n) K))
    (J : Ideal (MvPolynomial (Option (Fin n × Fin n)) K))
    (hS : ∀ g, g ∈ S ↔ glCoords g ∈ zeroLocus K J) {g : GL (Fin n) K} (hg : g ∈ S) :
    g⁻¹ ∈ S := by
  have hinj : Function.Injective fun x : S => glCoords x.1 := by
    intro x y h
    ext i j
    exact congrFun h (some (i, j))
  have hrange : Set.range (fun x : S => glCoords x.1) =
      zeroLocus K (J ⊔ Ideal.span {X none * detPoly n - 1}) := by
    ext v
    simp only [Set.mem_range, mem_zeroLocus_iff, Submodule.mem_sup, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨x, rfl⟩ p ⟨a, ha, _, ⟨c, rfl⟩, rfl⟩
      have h1 := (mem_zeroLocus_iff.1 ((hS x).1 x.2)) a ha
      replace h1 : eval (glCoords x.1) a = 0 := by simpa using h1
      simp only [aeval_eq_eval, map_add, h1, map_mul, map_sub, eval_X, glCoords,
        Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', eval_detPoly, entries,
        map_one, zero_add, mul_eq_zero]
      exact .inl (sub_eq_zero.2 (inv_mul_cancel₀ (Matrix.isUnits_det_units x.1).ne_zero))
    · intro hv
      have hdet : v none * (entries v).det = 1 := by
        have := hv (X none * detPoly n - 1) ⟨0, zero_mem _, _, dvd_rfl, zero_add _⟩
        simpa [eval_detPoly, sub_eq_zero] using this
      let g : GL (Fin n) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (entries v)
        (right_ne_zero_of_mul_eq_one hdet)
      have hc : glCoords g = v := by
        funext o
        rcases o with _ | ⟨i, j⟩
        · simp [glCoords, g, Matrix.coe_units_inv, eq_inv_of_mul_eq_one_left hdet]
        · rfl
      exact ⟨⟨g, (hS g).2 (hc ▸ fun p hp => hv p ⟨p, hp, 0, dvd_zero _, add_zero p⟩)⟩, hc⟩
  have hm : ∀ x y : S, glCoords (x * y).1 = law (glLaw n) (glCoords x.1) (glCoords y.1) := by
    intro x y
    funext o
    rcases o with _ | ⟨i, j⟩
    · simp [glCoords, law, glLaw, mul_comm]
    · simp [glCoords, law, glLaw, Matrix.mul_apply]
  obtain ⟨u, hu⟩ := isUnit_of_isLeftCancelMul _ hinj _ hrange _ hm ⟨g, hg⟩
  have h1 := congrArg Subtype.val u.mul_inv
  simp only [Submonoid.coe_mul, hu, Submonoid.coe_one] at h1
  rw [inv_eq_of_mul_eq_one_right h1]
  exact (↑u⁻¹ : S).2

end Grothendieck.Folder53
