# Review queue, the nine « argument » items: mathematical check (2026-11-07)

Checked against the footnotes of `transcripts/<cote>/<cote>.modern.tex`. Every argument below is the edition's own unless it says otherwise. Not committed.

## argument-107-p20: path fibration over S¹. It holds (high confidence)
**Claim.** In the square with p : PS¹ → S¹ (paths starting at *), i : {0,1} → [0,1], g ≡ c_*, g′ a degree-1 loop and φ ≡ c_*, both triangles commute up to homotopy, but no φ̄ makes them commute strictly. The p. 20 criterion (k, h compatible rel endpoints) also fails.
**Check.** pg = g′i holds. φi = g. pφ ≃ g′ because [0,1] is contractible. Take a lift φ̄ of g′ starting at c_*. It is a family α_t of paths from * to g′(t). The square (s,t) ↦ α_t(s) has a boundary of degree 0, so deg α₁ = deg g′ = 1 and α₁ ≠ c_*. For the criterion: the boundary of h : [0,1]×J → S¹ forces deg h(1,·) − deg h(0,·) = 1. Meanwhile p∘k factors through the contractible PS¹, so it has degree 0 at both ends. Necessity and sufficiency are standard lifting and extension arguments (Top is a model category in which every object is fibrant).
**Refs.** Hatcher, *Algebraic Topology*, Thm 1.7 (π₁S¹ = ℤ) and §4.3 (path fibration). Quillen, *Homotopical Algebra*, LNM 43, ch. II §2.

## argument-109-p14: groupoids are not a topos, and (Ord) is a modelizer. It holds (high)
**Check.** In Gpd the monomorphisms are the functors that are injective on objects and on arrows. So Sub(1) has 2 elements and Ω has exactly 2 objects. Sub(Bℤ/3) has 3 elements, because ℤ/3 has only two subgroups. Hom(Bℤ/3, Ω) = Σ_x #{h ∈ Aut x : h³ = 1}. Each term is odd or infinite, since the non-trivial solutions pair off as {h, h²}. Two odd terms cannot add up to 3. For (Ord): Raptis gives a model structure on posets whose weak equivalences are detected by the nerve, Quillen equivalent to Thomason's structure on Cat. Its homotopy category is therefore Hot.
**Refs.** Mac Lane–Moerdijk IV.1 (definition of a topos). G. Raptis, HHA 12(2) (2010) 211–230, doi:10.4310/HHA.2010.v12.n2.a7, checked on Crossref. The publisher's page could not be opened.

## argument-118-p32: the lemma restated. It holds (high)
**Check.** (ii) ⇔ (ii bis): f×g = (f×id)(id×g). (i) ⇒ (ii bis): the projections X×a → X lie in W_A by locality, since their fibres b×a are aspherical. (iv) ⇔ the a×b are aspherical: the comma category of A/(X×Y) → A/X × A/Y over α is A/(a×b), then Quillen's Theorem A. For A non-empty, (iv) ⇒ A aspherical: apply Theorem A to A/a → A, whose comma categories are the A/(a×b). For A = A₁ ⊔ A₂, a×b = ∅, so (iv) is not stable under sums. The two conditions differ only for A = ∅, as the footnote says. Counterexample A = BG with G ≠ 1: a map of G-sets that is bijective on orbits and an isomorphism on stabilisers is an isomorphism. So W_A consists of the isomorphisms and is stable under products, while BG is not contractible. This agrees with the footnote's comparison with Cisinski's Prop. 4.3.2(g). Cisinski's MathOverflow answer could not be opened here.
**Refs.** Cisinski, Astérisque 308 (2006), 4.3.1–4.3.2. Maltsiniotis, Astérisque 301 (2005). Quillen, LNM 341, Theorem A.

## argument-118-p22: the counterexample needs more than π₁ ≠ 1. It holds (high)
**Check.** In Σ(Z), no chain of arrows passes through both apexes. So N Σ(Z) = cone ∪_{BG} cone, the unreduced suspension of BG. That suspension is simply connected (van Kampen), so by Hurewicz–Whitehead it is contractible ⇔ H̃_*(BG) = 0 ⇔ G is acyclic. For Higman's acyclic group, ΣBG ≃ *, which refutes the page's "π₁ ≠ 1 suffices". The queue's wording "needs non-zero abelianisation" is too strong. H₁(G) ≠ 0 is sufficient but not necessary: the binary icosahedral group is perfect but not acyclic (H₃ = ℤ/120). The footnote itself states the exact condition, "G not acyclic", correctly.
**Refs.** Baumslag–Dyer–Heller, JPAA 16 (1980) 1–47, doi:10.1016/0022-4049(80)90040-7. Hatcher, Cor. 4.33.

## argument-103-p5: Picard envelope, and the functorial cone. It holds (high)
**Check.** Strictness is invariant under equivalence, so the envelope is strict ⇔ s = 0. The swap on P⊕P equals (id ⊕ −id) times an elementary automorphism (Whitehead lemma), so s[P] = [−id_P]. If 2 = 0 in A, this is 0. For A = ℤ, K₁ = {±1} and s(n) = (−1)ⁿ ≠ 0. On p. 13: the functorial K-injective resolution C makes F ↦ Cone(C(F) → q_*C(q^*C(F))) a functor on complexes. It preserves quasi-isomorphisms (q^* is exact, q_* preserves homotopy equivalences between K-injectives, then the five lemma), so it descends to D.
**Refs.** Stacks 079H (functorial injective embeddings) and 079P (functorial K-injective resolutions). SGA 4 XVIII §1.4.

## argument-105-p26: saturation, and the converses of W7 bis / W8 bis. It holds (high)
**Check.** Free category on f : A → B and g : B → A, with W the words of even length. W contains the identities, which are the only isomorphisms. It has 2-out-of-3 because length is additive. It is closed under retracts, because rs = id forces r = s = id, so a retract of v is v itself. Yet gf and fg lie in W while f does not. For the converses: take X₀ acyclic but not contractible (the Poincaré sphere minus a point), X_a = e, and X_b = X₀ with a final object added. By Thomason, 𝒳 ≃ ΣX₀, which is simply connected and acyclic, hence contractible. So i′_b ∈ W∞ while i_b ∉ W∞. Similarly a) + c) hold without b). For homology equivalences the converses do hold (Mayer–Vietoris and the five lemma).
**Refs.** Thomason, Math. Proc. Camb. 85 (1979) 91–109, doi:10.1017/S0305004100055535. Dwyer–Hirschhorn–Kan–Smith, AMS Surveys 113 (2004), 2-out-of-6.

## argument-111-p3: four counterexamples. It holds (high, the fourth conditional)
**Check.**
- K(ℤ/p,2): its reduced homology is p-torsion (Serre classes). Over ℚ or 𝔽_ℓ, ℓ ≠ p, the local systems are constant and H^{>0} = 0, so u^* is an equivalence on D^b_lc, yet u is not a weak equivalence.
- Higman's group G: BG → pt is an isomorphism on all abelian cohomology, but H¹(BG, G) = Hom(G, G)/conj is not a single point.
- The loop functor is not faithful: ab ∈ H⁴(S²×S²) is non-zero, while σ*(ab) = 0 because cohomology suspension factors through ΣΩX, where cup products vanish.
- RP¹ ⊂ RP²: Sq¹a = a² ≠ 0. This refutes the statement only if S(X) means classes dual to submanifolds, which the footnote already says.

**Refs.** Serre, Ann. Math. 58 (1953). Hatcher §4.L (Steenrod squares). BDH 1980.

## argument-43-p0: the corrections in the header. They hold (high, except p. 79 medium)
I checked each of the corrections listed in the header:
- **p. 3:** O_p^* is needed, otherwise weak approximation makes the quotient 0. On signs, "finite" would be wrong; the reason is Chevalley's theorem (JMSJ 3 (1951), doi:10.2969/jmsj/00310036, title checked).
- **p. 8:** the sign comes out as (a)^{-1}.
- **p. 14:** Serre's local symbol satisfies (f,g)_x = v_x(g)f(x) when f is regular at x, so it vanishes on U_G×U, not on U_G×V (GACC III).
- **p. 25:** finiteness follows from properness and quasi-finiteness. Flatness is a genuine hypothesis.
- **p. 28:** the right construction is the pushout.
- **p. 41:** H²(Ẑ, ℤ) = ℚ/ℤ.
- **p. 42:** H¹(Ẑ, M) = M/(F−1)M. Kernel and cokernel of F − 1 need not be isomorphic; for example, on ℤ/2×ℤ/4 with F(a,b) = (a, b+2a), F − 1 has kernel ℤ/4 but cokernel (ℤ/2)².
- **p. 51:** q^{(n)}A_q = q^nA_q.
- **p. 66:** the Koszul sign.
- **p. 76:** vanishing needs a strictly henselian ring. For a local field L, Br(L) ≠ 0. Zariski–Nagata purity is SGA 1 X 3.4.
- **p. 111:** H¹(α_p) = K/K^p.
- **p. 132:** the shift through ℤ → ℚ → ℚ/ℤ, with cd = 2.
- **p. 145:** the nine-term Poitou–Tate sequence (Milne, ADT I.4.10).
- **p. 148:** the arrow's direction, and the functor is faithful but not full.
- **p. 172:** V = p on ℤ.
- **p. 198:** F and p are nilpotent only locally on 𝒰.
- **p. 205:** the tame symbol lands in k^*.
- **p. 206:** Θ lives on A×Â.

For p. 79, the objection with G_a holds in genus ≥ 1. The claim that the pro-object makes the formula correct in degree 1 is cited and was not re-proved.

## argument-150-p19: strict compatibility, and the p. 68 dimension argument. It holds (high)
**Check.** On X = [0,1], Y = {0}, T = [0,½], the closed sets X₁ = {0} and X₁ = ∅ are both compatible with T and have the same data on the right. Under X_i∩Y = f(Ẋ_i), each X_i is determined by its data. On p. 68: D²×{0} in D²×({0}∪{1/n}) is a nowhere-dense closed set of full dimension. In an n-manifold, an n-dimensional subset has non-empty interior.
**Refs.** Hurewicz–Wallman, *Dimension Theory* (1941), Thm IV.3.
