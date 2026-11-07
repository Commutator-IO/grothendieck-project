# The eight « hypothesis » items: mathematical side settled (2026-11-07)

Scope: the items of `src/content/review-queue.json` with `kind: "hypothesis"`. For each one: whether
the statement as read holds, which hypothesis it needs, what the facsimile reader has to look at, what
to write in the reading for each answer, and the closest published statement. References marked
"opened" were read in the PDF at the place cited (copies in the session scratchpad). References marked
"not opened" could not be fetched and are given only as pointers. Nothing here says what the page has.

---

## hypothesis-57-p45: Théorème de rigidité, 57 p. 45

**Verdict.** As read, without « commutatif » on the ambient G, the theorem is **false**, and the
claim's counterexample holds. Over S = 𝔸¹_t (noetherian, connected), let G = GL₂, G₁ = T the diagonal
torus, and G₂ = gTg⁻¹ with g = (1 t ; 0 1). Both are closed, flat, commutative subgroups with dense
prime-to-p torsion, so they are « rigides » in the sense of the p. 42 definition. That definition is
stated only for a commutative group: « Un préschéma en groupes commutatif G … est dit rigide ». The
fibres agree at t = 0. At t ≠ 0, g is not monomial and so does not normalise T. **Needed:** G
commutative. With that hypothesis the ℓ^k-torsion of G is unramified when ℓ is invertible, and the
argument of pp. 44–45 (finite étale subschemes that agree at one point of a connected S agree
everywhere) goes through. Corollaire 1 of p. 46 does write « comm. ». A weaker hypothesis would also do,
for instance that G₁ is central in G, as in SGA 3.

**On the page.** Read the word added between « schéma en groupes » and « de type fini ». If it reads
« comm. » or « commutatif », the statement is right, and the reading can drop the counterexample to a
footnote that explains why the word is needed. If it reads anything else (« lisse », « affine »,
« séparé »), the reading keeps the counterexample and says that the hypothesis is missing on the page.
Corollaire 1 carries the right one.

**Reference (opened).** SGA 3, Exp. IX, Théorème 5.1 (new edition by Gille–Polo, pp. 48–49; original
p. 59). It is the rigidity of homomorphisms u, v : H → G with H of multiplicative type, under the
explicit hypothesis « supposons u_s central ». Corollaire 5.4 (p. 50) is the descent analogue of 57's
Corollaire 2, with the same « fibres géométriquement connexes ».

---

## hypothesis-114-p3: Proposition 4, 114 p. 3

**Verdict.** As read, (iii) ⇒ (i) is **false**, and the edition's counterexample is right. Take the
cube category □ without connections. Every product □ᵐ × □ⁿ is 0-connected, so □ satisfies (iii). But
□¹ × □¹ is not W∞-aspherical. Opened: Cisinski, *Les préfaisceaux comme modèles des types
d'homotopie*, Astérisque 308 (2006), Remarque 8.4.33, p. 348: its homotopy type « n'est même pas
simplement connexe ». The chain (i) ⇒ (ii) ⇒ (iii) holds.

Hypotheses one might expect, checked:
- « W ⊆ W₀ » adds nothing. PS p. 349 itself says « The condition Loc 4) on W, i.e., W ⊂ W₀ ».
- « A test category » does not help, since □ is a test category.
- Stability of A under finite products, or « strictly totally W-aspheric », would make (iii) ⇒ (i)
  trivial or would assume it.

**Bibliographical finding (opened).** Pursuing Stacks, §95, typescript pp. 348–351 (arXiv:2111.01000v2,
Carmona–Buchholtz edition, pp. 321–323). The published page 350 does **not** contain this
Proposition 4. Its « Proposition 4 » is about contractibility structures and *assumes* « A strictly
totally W-aspheric », and the text says the localiser-dependence is real (« this depends a priori on
the choice of W, as it has to »). The folder's sheet, numbered 350, is therefore an abandoned version
of that page. The text Grothendieck kept replaced the independence claim with an assumption.

**On the page.** Check that the typed statement has no hypothesis between « Let A be any small category »
and the list (i)–(iii). The words « strictly », « with finite products » or « contractor » would be the
ones that matter. Check also whether a hand addition qualifies (iii). If nothing is added, the reading
keeps the refutation and adds that the published p. 350 differs. If « strictly totally » or « stable
under products » appears, the proposition is true as written and the counterexample goes.

---

## hypothesis-18-p35: f_∞ = 1, 18 pp. 35 and 37

**Verdict.** As read, the chain is **false** in its third term, and so is the Remarque of p. 37.

Complex conjugation acts on the Betti realisation of ℚ(1) (the period 2πi) by −1, and on the sign
Artin motive ε (from h⁰(Spec ℂ/ℝ), period i) by −1. So L = ℚ(1) ⊗ ε has f_∞ = +1 and a real period
(2πi · i = −2π). It is not a sum of ℚ(2n), yet ⟨L⟩ has group G_m.

**Correct statement:**
- f_∞ = 1 ⟺ all periods are real ⟺ M ∈ ⟨ℚ(1) ⊗ ε⟩, that is, M is a sum of ℚ(n) ⊗ ε^{⊗n}.
- Under these conditions G ≃ G_m or {e}. This last part stays right.
- « directe » on p. 37 is harmless, since the categories are semisimple. The error lies in
  « puissances tensorielles de ℚ(2) ».

**On the page.** Read the margin of p. 35, « engendré par ℚ tordu et par ℚ(2) ».
- If « ℚ tordu » is ℚ(±1) twisted by the sign (ε, « signe », « tordu par ε »), the page has the right
  answer, because ⟨ℚ(1)⊗ε, ℚ(2)⟩ = ⟨ℚ(1)⊗ε⟩. The reading should credit the margin and correct the box.
- If it is only a Tate twist ℚ(n), the margin is wrong as well, since it would contain ℚ(1), which has
  f_∞ = −1. The reading keeps the correction as the edition's own.

**References (not opened).** Deligne, « Valeurs de fonctions L et périodes d'intégrales », PSPUM 33
(1979). The AMS and IAS copies refused automated access, and Fontaine's Bourbaki exposé 751 (numdam)
has unusable OCR at the relevant lines. The computation above is elementary and self-contained.

---

## hypothesis-42-p1: réseaux d'anneaux locaux, 42 pp. 1, 2 and 6

**Verdict.**
- **The theorem of p. 2 as read** (S_{0/S} = *loc.* de type fini, no separation) is **false**, by the
  edition's Y = 𝔸¹ with infinitely many doubled points. I re-checked the gluing and the cocycle
  condition: the lattice homomorphism is well defined, and any realising morphism would have a
  quasi-compact image.
- **Corollaire 3 of p. 6 as transcribed** says « Y [struck word] *de type fini* ». Finite type
  includes quasi-compactness, so that counterexample does **not** touch Corollaire 3. For curves
  X, a quasi-compact non-separated Y gives no counterexample either: the exceptional points are finite
  and the germs glue. Whether a counterexample exists in higher dimension is still open.
- **Sufficient:** Y separated (the edition, checked in Lean).
- **The germ step:** EGA IV₃, Prop. 8.13.1, p. 49 (opened). It needs Y locally of finite
  presentation over S and uses no separation, so the failure is only in the gluing.

**On the page.**
- Read the struck word before « de type fini » in Corollaire 3. If it is « loc. », then Grothendieck
  deliberately strengthened to finite type, and the reading should say that Corollaire 3 is not
  refuted by our example. Only p. 2 is.
- Check that p. 2 really says « loc. de type fini » for S₀.
- Check that « séparé » is nowhere on pp. 1–2 or 6, including under the crosses.

---

## hypothesis-151-p62: théorème de recollement des tubes, 151 p. 68

**Verdict.** False at depth 2 in **every** reading of the operation, not only the topological one. The
claim's own counterexample is ℝ² ⊃ x-axis ⊃ {0}.

- **Topological colimit.** False, as the edition's Lean check shows. Grothendieck says it himself on
  p. 62, before the theorem: such a limit, taken as a topological space, « a peu de chances d'être
  homéo. à X ».
- **Homotopy colimit, my own count.** With V_{1,2} the tube of the open axis in ℝ² ∖ {0}, the diagram
  X₀* ← V*₀₁ → X₁* ← V*₁₂ → X₂* has 1, 2, 2, 4 and 2 contractible pieces. Its homotopy colimit is a
  graph with 5 vertices and 6 edges, ≃ S¹ ∨ S¹. If instead V_{1,2} is taken around the closed axis,
  one gets a graph with 6 vertices and 6 edges, ≃ S¹. Neither is contractible, while ℝ² is.
- **What is missing.** In both cases it is the link of {0} in the open stratum, that is, the
  non-adjacent pair 0 < 2.
- **Correct form (opened).** The diagram must run over **all flags** of strata, with their homotopy
  links. See Douteau–Waas, *From homotopy links to stratified homotopy theories*, arXiv:2112.02394v2,
  §6.2, pp. 70–71: X ≃ hocolim over the regular flags I of HoLink_I, proved there for vertically
  stratified CW complexes.
- **Depth 1 (two strata)** is right. It is the « somme amalgamée » of section 1.

**On the page.** Read the illegible word after the struck « au topos ». Also look for a hypothesis
limiting I to two elements, or for diagonal arrows between non-successive indices (the « trait plein »
arrows of (17)). If « deux strates » or diagonal arrows are there, the theorem stands. Otherwise the
reading should state the flag version and say that the theorem, in whatever category, needs the
non-adjacent links.

---

## hypothesis-94-p7: Remarque 5 bis, 94 p. 7

**Verdict.**
- **The local form is false.** Under (iv) as read (F(M) finitely generated for M of finite length
  over A_𝔭), the converse fails. I re-checked the telescope F(M) = colim(M →h₂ M →h₃ …) on k[x, y]
  with h_j = x − a_j. At each 𝔭 at most one h_j lies in 𝔭, so the tail of the colimit is a chain of
  isomorphisms and F_𝔭 ≅ id. All fibres have rank 1. F(A_g) is not finite for g ≠ 0. Note that F(A)
  is the submodule ⋃ A/(h₂⋯h_n), not the localisation.
- **The page's own sketch** uses « F(N) est de type fini » for a finitely generated N that is not of
  finite length. This is a **global** finiteness.
- **Bibliographical point.** On p. 5, (iv) is written « \struck{type fini} longueur finie ».
  Grothendieck weakened the global hypothesis to the local one there, and the sketch of p. 7 still
  uses the global one.

**On the page.** On p. 7, check that the module whose F is said to be « de type fini » is the
finitely generated N, and that no hypothesis is added in the interline. On p. 5, check the strike
« type fini → longueur finie » in (iv).
- If both are confirmed, the reading should say that 5 bis needs (iv) in its original, global form.
- If p. 7 adds « F(M) de type fini pour M de type fini », the remark is right.

The readings « Nor(B) » (normal locus), « codimension » and « normal » are consistent with the Hartogs
step and need no change. With the global hypothesis, the edition says the normal-locus condition
becomes unnecessary. I did not verify that.

**Reference (opened).** EGA III₂, Théorème 7.7.6, p. 69 (Publ. IHÉS 17): M ↦ Γ(X, F ⊗ M) is
represented by a coherent Q. This is the global finite-type model of the representability that
Lemme 5 is after.

---

## hypothesis-7-p16: the big site, 7 pp. 16–18

**Verdict.**
- **As read, test a) fails.** The objects are p-adic formal affines B → A₀ with B/pB → A₀ of nilpotent
  kernel, which are Ogus's « enlargements ». The cohomology of this site computes the de Rham
  cohomology of the p-adic completion, and on 𝔸¹ that is huge. For example, ω = Σ pⁿ x^{pⁿ−1} dx lies
  in ℤ_p⟨x⟩ dx, but its only primitive Σ x^{pⁿ} is not in ℚ_p⟨x⟩. Monsky–Washnitzer cohomology of 𝔸¹
  has H¹ = 0.
- **Test b)** (proper smooth) is the case where such a cohomology agrees with crystalline cohomology.
- **Needed for a):** B weakly complete (dagger), not « formel complet ».

**Reference (opened).** Berthelot, « Géométrie rigide et cohomologie des variétés algébriques de
caractéristique p », Mém. SMF 23 (1986), Remarque after Prop. 2, p. 14: the naive cohomology of affine
space is the de Rham cohomology of the closed polydisc, « qui n'est pas de dimension finie sur K ». It
keeps the good properties only when X is proper. Section 2 (p. 14) adds that overconvergence is
needed in the non-proper case.

**On the page.**
- Read « formel » and the illegible word after « complet ». If it is « faiblement » or « f.c. », the
  site is Monsky–Washnitzer style and test a) passes. If « formel complet » stands, a) fails as
  above, and the reading should say so, citing Berthelot.
- « isomorphisme nilpotent » and its parenthesis can stand either way.

---

## hypothesis-43-p70: local cohomology with values in G, 43 pp. 70–74

**Verdict.** **True**, if k is algebraically closed (Grothendieck, p. 70: A regular). The case d = 1
holds for any separated G over any k: H⁰_A = 0, and H¹_A = G(K)/G(A) because H¹_Zar(Spec A) = 0. The
proof for d ≥ 2 goes in four steps:
1. Dévissage by Chevalley's structure theorem, which needs k perfect. Torsors under the linear part
   are Zariski-locally trivial when the torus is split.
2. H^{≥1}_Zar(U, G_m) = 0: H¹ = Pic U = Cl A = 0 by factoriality, and H^{≥2} = 0 by the
   divisor resolution 0 → O* → K* → ⊕ℤ → 0.
3. H^j(U, G_a) = H^{j+1}_𝔪(A), which is concentrated in j = d − 1 because A is Cohen–Macaulay. Opened:
   SGA 2, Exp. III, Prop. 3.3, arXiv:math/0511279, p. 27.
4. The abelian part needs every map U → B to extend, which uses the regularity of A. I did not find
   this in a source I could open. It is the point to cite, or to check with a specialist.

« Algebraically closed » is sufficient. Whether « perfect » alone suffices, with non-split tori, is not
settled here.

**On the page.** Read the field hypothesis on pp. 70 and 74. If the page reads « k alg. clos » or
« parfait », record it and drop the edition's addition. If it has nothing, keep the addition and
footnote it as the edition's own. Also check « régulier » (p. 70), « factoriel » (pp. 72–73), and
« G_a » versus « G_m » (pp. 72–73). These are what the proof rests on.
