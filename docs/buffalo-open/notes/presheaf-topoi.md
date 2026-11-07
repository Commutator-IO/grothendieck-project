# Grothendieck's question on presheaf topoi (Buffalo 1973, entries 5182 and 27083)

## 0. The question and where it comes from

Index `docs/buffalo-topos/index.tex`:

* **5182** (q, line 475, 30 May 1973): *"Are the topoi of the form Ĉ exactly those that are locally connected and, in a suitable sense, totally disconnected, i.e. those sharing all exactness properties of Set, including those involving infinite limits?"* It follows **5053**: *"The inverse image Set → E commutes with infinite products iff E is locally connected; this expresses that products distribute over arbitrary sums in E."*
* **27083** (q, line 644, 27 June 1973): *"Are the essential topoi, i.e. topoi in which arbitrary products of epimorphisms are epimorphisms and arbitrary products commute with sums, exactly the presheaf topoi Ĉ (when they have generators)?"* It sits among the examples of `Cat_D` (26963: topoi; 27254: frames, "distributivity of products over sums").

Notes in `docs/buffalo-topos/lean/*.json`: Part03.json marks 5182 "Question", status n/a. Part03-boards.json, at board PqCQM3Pcl6Q-2947, t = 5182, says "Presheaf topoi are locally connected and have the exactness of Set; the converse is the open question of the index". At board URU5jgTvjhU-34123, t = 36565, it says "Asserted here; the lecture of 30 May asks it as a question (PqCQM3Pcl6Q-5182)". Part04.json marks 27083 "Question. The name 'essential topos' is used here in a sense different from the current one (f_! exists)". Part04-boards.json corrects the board formula "essential topos with generators = Ĉ" to "≟ Ĉ".

Throughout, E is a Grothendieck topos and the metatheory is ZFC (we use the axiom of choice freely). The two conditions are:

* **(A)** For every small family of epimorphisms f_i : X_i → Y_i, the product ∏f_i : ∏X_i → ∏Y_i is an epimorphism.
* **(B)** For every small family of small families (X_ij), i ∈ I, j ∈ J_i, the canonical map ∐_{φ∈∏J_i} ∏_i X_{iφ(i)} → ∏_i ∐_{j∈J_i} X_ij is an isomorphism.

## Summary of answers

1. **Grothendieck's conjecture is false.** Take X = [0,1) with the opens [0,a), 0 ≤ a ≤ 1 (the lower topology). Equivalently, take the locale whose frame is the complete chain [0,1]. Then Sh(X) satisfies (A) and (B), but it is not equivalent to any presheaf topos. It even has no projective objects other than 0. Proved in §3.
2. **The class defined by (A)+(B) is exactly the class of totally distributive Grothendieck topoi, which is the class of essential subtopoi of presheaf topoi.** For a Grothendieck topos E the following are equivalent:
   * (i) E satisfies (A)+(B);
   * (ii) some (equivalently every) small generating full subcategory C, with its induced topology J, has J-covering sieves closed under arbitrary intersections;
   * (iii) E is an essential subtopos of a presheaf topos Ĉ;
   * (iv) E is totally distributive in the sense of Rosebrugh–Wood, i.e. colim : Ê → E has a left adjoint.

   The equivalences (i)⇔(ii)⇔(iii) are proved here, along with a direct proof of (iv)⇒(i). The equivalence (iii)⇔(iv) is Lucyshyn-Wright's Theorem 1.5.5, which I read. Proved in §2.
3. **Localic case.** Sh(L) satisfies (A)+(B) ⇔ L is completely distributive ⇔ Sh(L) is totally distributive ⇔ Sh(L) ↪ PSh(L) is an essential inclusion. Separately, (B) alone holds for Sh(L) iff L is locally connected. Proved in §2.6.
4. **(A) and (B) are independent.** Sh(Cantor space) satisfies (A) but not (B). Sh(ℝ) and the topos of continuous ℤ_p-sets satisfy (B) but not (A). Proved in §4.
5. Inside the class, the presheaf topoi are the members with enough projectives. This rests on a standard characterisation that I recalled but did not re-check (§3.4).

Grothendieck named the (A)+(B) topoi "essential topoi". By (iii), that class is exactly the class of essential subtopoi of presheaf topoi in today's sense. This looks like a coincidence of vocabulary.

---

## 1. Literature: what was actually read

**Read.** R. B. B. Lucyshyn-Wright, *Totally distributive toposes*, J. Pure Appl. Algebra 216 (2012) 2425–2431, arXiv:1108.4032. I read the full text of §1 and §5 from the arXiv PDF.

* §1.1 recalls a definition from Fawcett–Wood: a poset E is ccd (constructively completely distributive) if ∨ : Dn(E) → E has a left adjoint. It states: "In the presence of the axiom of choice, a poset is a ccd lattice iff it is a completely distributive lattice in the usual sense [2]."
* It recalls the Rosebrugh–Wood definition: a locally small category E is *totally distributive* if there is a chain t ⊣ c ⊣ y : E → Ê = [E^op, Set], with y the Yoneda embedding. In other words, c = colim has a left adjoint.
* Definition before Thm 1.5.5: "An essential subtopos of a topos F is a topos E for which there is a geometric inclusion i : E → F whose inverse image functor i* has a left adjoint."
* **Theorem 1.5.5**: "Those totally distributive categories having a small dense generator are exactly the essential subtoposes of presheaf toposes Ĉ = [C^op, Set] (with C a small category)."
  * Every Grothendieck topos has a small dense generator, as the paper notes. So Thm 1.5.5 applies to Grothendieck topoi without the foundational caveat that Remark 1.5.8 attaches to the variant Thm 1.5.9.
  * The two directions are Prop. 5.1(2) and Prop. 5.3. Prop. 5.3 uses that s_! ⊣ s* ⊣ s_* with s_!, s_* fully faithful gives total distributivity (its Lemma 2.3).
* **Theorem 1.5.3**: lex totally distributive with a small dense generator ⇔ injective topos.
* **Prop. 1.5.4**: every quasi-injective topos is totally distributive.
* **Remark 1.5.6** (attributed to Kelly–Lawvere): the essential subtopoi of Ĉ correspond to the idempotent ideals of arrows of C.

The paper says nothing about locales, Sh(L), products of epimorphisms, or products and sums.

**Not read** (only seen through Lucyshyn-Wright's citations or search snippets, so not used as sources): Street–Walters *Yoneda structures* (1978); Street *Notions of topos* (1981); Fawcett–Wood and Rosebrugh–Wood *Constructive complete distributivity* I–IV; Rosebrugh–Wood *Totally distributive categories*; Marmolejo–Rosebrugh–Wood *Completely and totally distributive categories I* (JPAA 2012); Kelly–Lawvere; Hoffmann. I found no text stating "Sh(L) is totally distributive iff L is (c)cd". §2.6 proves it under AC.

**Answers to the literature questions:**

* *Is a Grothendieck topos totally distributive iff it is a presheaf topos?* No. By Lucyshyn-Wright 1.5.5 the totally distributive Grothendieck topoi are the essential subtopoi of presheaf topoi. The example of §3 is one of these that is not a presheaf topos. This is also visible from Kelly–Lawvere: Sh([0,1]) is the essential subtopos of presheaves on (0,1] attached to the idempotent ideal "<".
* *Is Sh(L) totally distributive iff L is completely distributive?* Yes under AC. This is proved here in Cor. 2.7 and was not found in the literature I read.

---

## 2. The class defined by (A)+(B)

### 2.1 Proposition. (B) ⇔ E is locally connected.

*Proof.*

(⇒) Apply (B) with all X_ij = 1. This says that the constant-sheaf functor Δ : Set → E preserves small products. Δ is left exact, so it preserves all small limits. Δ also preserves all colimits, so it is accessible. Set and E are locally presentable, so the adjoint functor theorem (Adámek–Rosický 1.66) gives a left adjoint π₀ ⊣ Δ. Over Set, such a left adjoint is automatically Set-indexed: X × ΔI = ∐_I X, so π₀(X × ΔI) = π₀X × I. Hence E is locally connected. This is entry 5053.

(⇐) A locally connected topos has a generating set of connected objects (the components of the objects in a generating set; standard). For a connected object Q:

* Hom(Q, −) preserves products.
* Hom(Q, −) preserves coproducts. A map Q → ∐X_j pulls the summands back to a decomposition Q = ∐Q_j. Exactly one Q_j is nonzero, because Q ≠ 0 and Q = Q_{j0} ⊔ ∐_{j≠j0} Q_j.

So Hom(Q, −) sends the canonical map of (B) to the canonical bijection of Set: ⊔_φ ∏_i Hom(Q, X_{iφ(i)}) ≅ ∏_i ⊔_j Hom(Q, X_ij), using AC. A map f in E that is bijective on Hom(Q, −) for every Q in a generating set is an isomorphism: f is mono because the generators separate maps, and epi because every Q → target lifts. ∎

### 2.2 Proposition. An essential subtopos of a presheaf topos satisfies (A) and (B).

*Proof.* Let i : E ↪ Ĉ be the inclusion, with i_! ⊣ i* ⊣ i_*. Since i_* is fully faithful, i_! is also fully faithful, so id ≅ i* i_!.

* (A): i_! f_i is epi, being the image of an epi under a left adjoint. ∏ i_! f_i is epi in Ĉ, since products are computed pointwise and AC holds in Set. i* preserves products and epis, so ∏f_i ≅ i*(∏ i_! f_i) is epi.
* (B): ∏_i ∐_j X_ij ≅ i*(∏_i ∐_j i_! X_ij) ≅ i*(∐_φ ∏_i i_! X_{iφ(i)}) ≅ ∐_φ ∏_i X_{iφ(i)}, naturally, compatible with the canonical maps. ∎

**Direct proof that totally distributive ⇒ (A)+(B)** (independent of Lucyshyn-Wright). Suppose c = colim : Ê → E has a left adjoint, so c preserves all limits that exist in Ê. Products in Ê are pointwise.

* (B): In Ê, ∏_i ∐_j y X_ij ≅ ∐_φ ∏_i y X_{iφ(i)} = ∐_φ y(∏_i X_{iφ(i)}), by pointwise distributivity and because y preserves limits. Apply c, which preserves products, coproducts and c∘y ≅ id. This gives (B).
* (A): Let P_i ⊆ yY_i be the sieve generated by f_i. In a topos, the colimit of a sieve on Y is the union of the images of its members: the equivalence relation generated by the diagram contains the kernel pair, because sieves are closed under precomposition. So c(P_i) = im f_i = Y_i.
  * By AC, ∏P_i ⊆ y(∏Y_i) is the sieve generated by ∏f_i.
  * Hence im(∏f_i) = c(∏P_i) = ∏c(P_i) = ∏Y_i.

### 2.3 Lemma (essentiality from intersections of covers)

Let (C, J) be a small site with associated sheaf functor a : Ĉ → Sh(C,J).

* If each J(c) is closed under arbitrary small intersections, then a preserves all small limits. Hence it has a left adjoint, and Sh(C,J) ↪ Ĉ is an essential subtopos.
* Conversely, if the inclusion is essential, then each J(c) is closed under arbitrary intersections.

*Proof.* Write F⁺(c) = colim_{S∈J(c)} Match(S,F). The colimit is directed, since J(c) is closed under finite intersections. Since Match(S, −) = Hom(S, −) preserves products, there is a canonical map (∏F_i)⁺(c) = colim_S ∏_i Match(S,F_i) → ∏_i colim_S Match(S,F_i).

* *Surjective:* represent ξ_i on S_i and restrict all of them to T = ⋂S_i ∈ J(c). This uses AC to choose the representatives.
* *Injective:* if two families agree in each factor, they agree on some S_i for each i, hence on ⋂S_i ∈ J(c).

So (−)⁺ preserves products, and so does a = (−)⁺⁺. a is left exact, so it preserves all small limits. a is a left adjoint between locally presentable categories, hence accessible, so the adjoint functor theorem gives a left adjoint.

Conversely, suppose a preserves limits and S_i are covering sieves, i.e. a(S_i) → a(yc) is an iso. Then a(⋂S_i), which is the wide pullback of the a(S_i), maps isomorphically to a(yc). ∎

### 2.4 Lemma. (A)+(B) ⇒ (ii)

Let C ⊆ E be a small generating full subcategory with its induced topology: a sieve S on c is covering iff the family of its members is jointly epimorphic in E. Assume (A)+(B). Then each J(c) is closed under arbitrary intersections.

*Proof.* Let (S_i)_{i∈I} be covering sieves on c, so each e_i : ∐_{(d,s)∈S_i} d → c is epi.

1. By (A), ∏_i e_i is epi onto c^I.
2. By (B), its domain is ∐_{φ∈∏S_i} ∏_i d_{φ(i)}, and on the φ-summand the map is ∏_i s_{φ(i)}.
3. Pull back along the diagonal c → c^I. Epis and coproducts are pullback-stable in a topos, so ∐_φ P_φ → c is epi. Here P_φ is the wide pullback over c of the maps s_{φ(i)} : d_{φ(i)} → c.
4. For each i, P_φ → c factors through s_{φ(i)} ∈ S_i.
5. Cover each P_φ by objects of C. The composites e → P_φ → c lie in every S_i, so they lie in ⋂S_i, and they are jointly epimorphic. Hence ⋂S_i is covering. ∎

### 2.5 Theorem

For a Grothendieck topos E the following are equivalent:

* (i) E satisfies (A) and (B).
* (ii) For some (equivalently every) small generating full subcategory C, the induced topology has J(c) closed under arbitrary intersections.
* (iii) E is an essential subtopos of a presheaf topos.
* (iv) E is totally distributive.

*Proof.*

* (i)⇒(ii): Lemma 2.4, for every C.
* (ii)⇒(iii): By the comparison lemma, E ≃ Sh(C,J); then apply Lemma 2.3.
* (iii)⇒(i): Proposition 2.2.
* (iii)⇔(iv): Lucyshyn-Wright Thm 1.5.5. The implication (iv)⇒(i) is also proved directly in §2.2. ∎

**Status:** (i)⇔(ii)⇔(iii) is proved here, assuming AC and the standard facts cited (comparison lemma, a = (−)⁺⁺, the adjoint functor theorem for locally presentable categories). (iii)⇔(iv) rests on Lucyshyn-Wright. I have not seen (i)⇔(iii) or (i)⇔(iv) stated anywhere. It is plausible that it is known folklore: Lemma 2.3 in particular is the kind of fact Kelly–Lawvere may contain, but I did not read Kelly–Lawvere. Novelty is not claimed.

### 2.6 The localic case

L is a frame; covers are joins. The checks marked "Lean" are in §5.

(a) **L completely distributive (CD) ⇔ covering down-sets of every u are closed under arbitrary intersections.**

* ⇒: Lean `cover_iInter`.
* ⇐: Lean `cd_of_cover_iInter`. Take u = ⋀_i ⋁_j f_ij. Then u = ⋁_j (u ∧ f_ij) for each i, by frame distributivity. Each w in the intersection of the down-sets generated by these covers lies below some ⋀_i f_{iφ(i)}.

By Lemma 2.3 and Theorem 2.5, applied to the site L with its canonical topology, this gives Corollary 2.7 below.

(b) **Direct checks, without the theorem:**

* CD ⇒ (A): given s_i liftable on covers {u_ik}_k of u, the meets ⋀_i u_{iφ(i)} cover u by CD, and on each of them the whole family lifts.
* (A)+(B) ⇒ CD: apply (A) to the epis ∐_k y(u_ik) → y(u). Then u is covered by v's that, for each i, decompose disjointly as v = ⨆_k v_ik with v_ik ≤ u_ik. (B) applied to the subterminals y(v_ik) gives v = ⋁_φ ⋀_i v_{iφ(i)} ≤ ⋁_φ ⋀_i u_{iφ(i)}.
* Exact content of (A) for Sh(L): u is covered by elements v such that, for each i, v has a disjoint decomposition subordinate to the i-th cover. Both directions are checked by the gluing argument above.

(c) **(B) for Sh(L) ⇔ L is locally connected ⇔ L is "disjointly CD"** (CD for families of disjoint decompositions).

* Locally connected ⇒ (B): Proposition 2.1.
* (B) ⇒ disjointly CD: apply (B) to subterminals.
* Disjointly CD ⇒ locally connected. Fix b and index all disjoint decompositions D of b. Disjoint CD gives b = ⨆_φ e_φ with e_φ = ⋀_D φ(D). This is again a disjoint decomposition, the common refinement. Each nonzero e_φ is connected: if e_φ = c₁ ⊔ c₂, then {c₁, c₂, e_ψ (ψ ≠ φ)} is a decomposition D′, so e_φ ≤ φ(D′), which forces c₁ or c₂ to be 0.
* Consequence: **every CD frame is locally connected.**

### 2.7 Corollary

Under AC, the following are equivalent for a locale L:

* Sh(L) satisfies (A)+(B);
* L is completely distributive, which equals ccd under AC (Fawcett–Wood, as quoted by Lucyshyn-Wright);
* Sh(L) ↪ PSh(L) is essential;
* Sh(L) is totally distributive.

Sh(L) is a presheaf topos iff L is the frame of down-sets of a poset, i.e. iff L is join-generated by completely join-prime elements. *Proof of ⇒:* representables are connected projectives, so each is a retract of a subterminal, hence subterminal and completely join-prime, and every subterminal is a join of representables. So every CD frame that is not Alexandrov gives a counterexample to the conjecture.

---

## 3. The counterexample: X = [0,1) with opens [0,a)

O(X) = {[0,a) : a ∈ [0,1]} ≅ [0,1], a complete chain. The same works for ℝ with the opens (a,∞), whose frame is the chain [−∞,∞].

### 3.1 Sheaves

A sheaf is a functor F : ((0,1], ≤)^op → Set with F(a) ≅ lim_{0<b<a} F(b) for every a, together with F(0) = 1.

*Reason:* a cover of [0,a) not containing it is cofinal in [0,a), and pairwise intersections of members of a chain are the smaller member.

**Coproducts are pointwise on (0,1].** A compatible family over a cofinal chain in a pointwise coproduct stays in a single summand, since restriction preserves the summand index. So the pointwise coproduct, with value 1 at 0, is already a sheaf. Products are pointwise.

### 3.2 (B) holds

At a > 0 both sides of (B) are ⊔_φ ∏_i X_{iφ(i)}(a), by distributivity in Set. At 0 both sides are 1. The cases where some J_i = ∅, or I = ∅, are fine: 0 is strict and empty products are 1. Equivalently, every nonzero element of a chain is connected (Lean `chain_connected`), so Sh(X) is locally connected, and Proposition 2.1 applies.

### 3.3 (A) holds

A complete chain is CD (Mathlib instance `CompleteLinearOrder.toCompletelyDistribLattice`; Lean, for [0,1] ⊆ ℝ). Then §2.6(b) applies. The underlying argument: given d < c = ⋀_i ⋁_k a_ik, choose for each i an index φ(i) with a_{iφ(i)} > d.

By §2.6 and Lemma 2.3, Sh(X) is therefore also an essential subtopos of a presheaf topos, and totally distributive. A direct description: Sh(X) ⊆ PSh((0,1]) is the subcategory of functors that are continuous from below. The sheafification aF(a) = lim_{b<a} F(b) is itself a limit, so it visibly preserves limits. In Kelly–Lawvere terms (Remark 1.5.6 as quoted), the idempotent ideal is "<".

### 3.4 Not a presheaf topos

**First argument: no join-primes.** The frame [0,1] has no completely join-prime element, since x = sup [0,x) (Lean `no_completely_join_prime`). By §2.7 it is not Alexandrov.

**Second argument: no nonzero projective.** Suppose P is projective. Let

e : E = ∐_{(c, z ∈ P(c), c′ < c)} y(c′) → P

be the epimorphism given by z|_{c′}. It is epi because sup{c′ < c} = c. Choose a section σ of e. Suppose x ∈ P(v) with v > 0.

1. v is connected, so σ(x) lies in a single summand (c, z, c′) with v ≤ c′ < c, and e∘σ = id gives x = z|_v.
2. By naturality, σ(z)|_v = σ(z|_v) = σ(x). Since v ≠ 0 is connected, σ(z) and σ(x) lie in the same summand (c, z, c′).
3. But σ(z) is a section over c, so the summand's c′ satisfies c′ ≥ c > c′, a contradiction.

So P(v) = ∅ for all v > 0, i.e. P = 0.

Every nondegenerate presheaf topos has nonzero projectives, the representables. More precisely, a Grothendieck topos is a presheaf topos iff it has a generating set of indecomposable projectives. This is a standard characterisation, which I recalled (I believe it is due to Bunge, 1966) but **did not re-check**. With it, Theorem 2.5 shows that **presheaf topoi are exactly the (A)+(B) topoi with enough projectives**. The "if" direction: components of projectives are connected projectives, and these are tiny, because Hom(P, −) then preserves coproducts and coequalizers (sketch).

**Conclusion.** The answer to 27083 is no. For 5182: the example is locally connected and satisfies (A)+(B), so it has the infinitary exactness of Set listed there. What fails is projectivity of 1, Γ = Hom(1, −) not preserving epis, which is not a limit/colimit commutation. Whether Sh(X) satisfies *every* "exactness property of Set" in Grothendieck's informal sense is not settled here, because that notion is not defined precisely.

---

## 4. Independence of (A) and (B)

* **(A) without (B): Sh(K), K a Stone space (e.g. the Cantor set).**
  * (A): every clopen v, given any cover, has a finite clopen refinement, which can be disjointified. So the criterion of §2.6(b) holds with the clopens v.
  * (B) fails: Sh(K) is not locally connected. Explicitly, ∏_n Δ2 has the identity K → 2^ℕ as a global section, but ∐_{2^ℕ} 1 has only the locally constant ones.
* **(B) without (A): Sh(ℝ).** It is locally connected, so (B) holds.
  * (A) fails. Let U_{n,k} = (k/2n, k/2n + 1/n). Then f_n : ∐_k y(U_{n,k}) → 1 is epi for every n.
  * A section of ∏_n ∐_k y(U_{n,k}) over a connected interval w forces w ⊆ some U_{n,k} for every n. So w is empty, ∏f_n has empty domain, and it is not epi.
* **(B) without (A): continuous ℤ_p-sets, a non-localic example.**
  * Orbits are connected, so (B) holds.
  * (A) fails. Let f_n : ℤ_p/p^nℤ_p → 1. The product of the f_n is computed as the smooth part of the set product. Its domain has no smooth points, because the stabiliser of every point is ⋂ p^nℤ_p = 0, which is not open. So the domain is empty.

---

## 5. Lean checks

The Lean file was written in another session's scratch directory and is not in the repository; it would have to be redone to be checked again. It was compiled with `lake env lean` against the project's Mathlib (Lean v4.35.0-rc4). It compiles with no errors and no `sorry`. Nothing was added to any repository.

* An `example` checks that `CompletelyDistribLattice (Set.Icc (0:ℝ) 1)` holds: the chain [0,1] is CD.
* `sSup_Iio_dense`: in a dense complete chain, sSup (Iio x) = x.
* `no_completely_join_prime`: in a dense complete chain, every x lies below the join of a set none of whose members lies above x. It is specialised to [0,1]. This is the failure of the Alexandrov property.
* `chain_connected`: b ⊓ c = ⊥ in a chain implies b = ⊥ or c = ⊥. Every nonzero element is connected, so the frame is locally connected.
* `cover_iInter`: in a CD lattice, if u ≤ sSup S_i for lower sets S_i, then u ≤ sSup (⋂ S_i). This is the localic hypothesis of Lemma 2.3.
* `cd_of_cover_iInter`: in a frame, if intersections of covering lower sets cover, then ⋀_i ⋁_j f_ij ≤ ⋁_φ ⋀_i f_{iφ(i)}.

The topos-level statements (§2–§4) are not formalised; Mathlib has no Grothendieck topoi in this generality.

## 6. What is proved, what is sketched, what is open

| Claim | Status |
|---|---|
| Sh([0,1) lower topology) satisfies (A), (B) and is not a presheaf topos, so the conjecture is false | **Proved** (§3), AC |
| (A)+(B) ⇔ essential subtopos of Ĉ ⇔ intersections of induced covers are covers | **Proved** (§2), AC + standard facts |
| totally distributive ⇒ (A)+(B) | **Proved** directly (§2.2) |
| (A)+(B) ⇒ totally distributive | Via Lucyshyn-Wright Thm 1.5.5 (read) |
| Sh(L): (A)+(B) ⇔ L CD ⇔ totally distributive; (B) ⇔ L locally connected; CD ⇒ locally connected | **Proved** (§2.6–2.7); order-level parts checked in Lean |
| (A), (B) independent | **Proved** (§4) |
| presheaf topoi = (A)+(B) topoi with enough projectives | Relies on a recalled characterisation of presheaf topoi (not re-checked); tininess step sketched |
| Constructive versions without AC; whether (B) with an abstract (non-canonical) iso suffices; the precise meaning of "all exactness properties of Set" in 5182 | **Open / not addressed** |
| Priority: whether (i)⇔(iii) appears in the literature (Kelly–Lawvere, Street, Rosebrugh–Wood) | **Unknown**; those papers were not read |
