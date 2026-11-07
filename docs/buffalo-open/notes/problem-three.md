# Grothendieck's « Problem three » (Buffalo, 2 July 1973, 4gynb9uTEE4-7434/7564)

Scratch write-up for Michel. Status labels: **[proved]** means a complete argument is given here; **[proved mod (H)]** means complete once the standing hypothesis (H) below holds; **[sketch]** means the structure is given but some coherence or bookkeeping is only indicated; **[cited]** means it rests on a result I checked in the literature, with its locator; **[open]** means open. Lean check: `ProblemThree.lean`, written in another session's scratch directory, is not in the repository.

## 0. Sources read

- `docs/buffalo-topos/index.tex`, lines 596–830: entries 19319 (Cat_D), 28756 (base objects), 29464–30037 (rules 1–3), 33138–33898 (rule 4, algebraic theories), 34019, 34771, 35544–36019, 258–2813, 7050–7823, 12928–13448. Also lines 979–1000 (the topos case, video ORG14LNb5gE).
- Board reconstruction `public/buffalo-boards/4gynb9uTEE4-6842.json`, items t = 7240–7629. It confirms the meaning of « basic »: « Algebraic $R$: a discrete category $I$ and $I\to R$ with $R$ reached by a transfinite sequence $R_0=\widetilde I^{\Delta}$, $R_{\alpha+1}=B(R_\alpha)$ or $C(R_\alpha)$, $R_\alpha=\varinjlim_{\beta<\alpha}R_\beta$ ». Here B means making arrows invertible or equalising pairs (axioms) and C means adding arrows (data), with $R_\alpha=R$ for $\alpha\gg0$. The board then says: « Problem 3: given problems 1 and 2 solved, R is reached transfinitely from I ⟺ (R′ ⊂ R full, stable under Δ, I → R factors through R′ ⇒ R′ = R) ». And at t = 7629: « One implication not proved; the other perhaps easy. »
- Lean: `Buffalo/Topos/Part04b.lean` (`DSpec`, `HasD`, `IsDFunctor`, `SatisfiesExactness`, `IsTwoSumFor`, `IsDEnvelopeFor`, localizations tested against one target) and `Part05*.lean`. Notes: `docs/buffalo-topos/lean/Part04.json`, `Part05.json`, `Part07.json`.

## 1. Definitions

Fix $D=(D',D'')$, two sets of small diagram shapes. $\Delta=\mathrm{Cat}_D$ has as objects the locally small categories with limits of type $D'$ and colimits of type $D''$. Its 1-cells are the $D$-functors, which preserve both; its 2-cells are all natural transformations. Write $\mathrm{Hom}_D(R,C)$ for the category of $D$-functors $R\to C$.

**Standing hypothesis (H)** (Grothendieck's « problems one and two solved », board item t = 7470). The following constructions exist in $\Delta$, each defined by its 2-universal property against every $C\in\Delta$:

1. the envelope $j\colon I\to\widetilde I$ of a small category $I$: restriction $\mathrm{Hom}_D(\widetilde I,C)\to\mathrm{Hom}(I,C)$ is an equivalence;
2. the localization $R\to R[\Sigma^{-1}]$ at a small set $\Sigma$ of arrows: $\mathrm{Hom}_D(R[\Sigma^{-1}],C)\to\mathrm{Hom}_D(R,C)$ is fully faithful, with essential image the functors that invert $\Sigma$;
3. equalizing a small set of parallel pairs, defined in the same way;
4. adjoining a small set $H$ of arrows $h\colon a_h\to b_h$ between objects of $R$ (rule 3, 30037). This gives $R\to R\langle H\rangle$ with $\mathrm{Hom}_D(R\langle H\rangle,C)\simeq\{(\psi,\beta):\psi\in\mathrm{Hom}_D(R,C),\ \beta_h\colon\psi a_h\to\psi b_h\}$, whose morphisms are the transformations $\psi\to\psi'$ compatible with the $\beta$'s;
5. 2-colimits of small chains, and 2-pushouts (needed only in §4).

**Definition (basic; 4gynb9uTEE4-7240).** Let $I$ be a small discrete category and $i\colon I\to R$ a functor, with $R\in\Delta$. Then $i$ is *basic* if there is a sequence $(R_\alpha)_{\alpha\le\gamma}$ indexed by a small ordinal $\gamma$ with the following properties:
- $R_0=\widetilde I$;
- each $R_\alpha\to R_{\alpha+1}$ is one of the steps 2, 3 or 4, with small data;
- at a limit ordinal $\lambda$, $R_\lambda$ is the 2-colimit in $\Delta$ of the $R_\beta$, $\beta<\lambda$;
- there is an equivalence $R_\gamma\simeq R$ in $\Delta$ whose composite with $I\to\widetilde I\to R_\gamma$ is isomorphic to $i$.

$R$ is *algebraic* if some small discrete $I'\to R$ is basic.

**Condition (G) (7434).** Every strictly full subcategory $R'\subset R$ that contains $i(I)$ and is closed under the $D'$-limits and the $D''$-colimits of $R$ is all of $R$.

**Saturation (7564).** Let $I_0$ be the repletion of $i(I)$. Let $I_{\alpha+1}$ be the repletion of $I_\alpha$ together with the limits of the $D'$-diagrams in $I_\alpha$ and the colimits of the $D''$-diagrams in $I_\alpha$. At limit ordinals, take unions.

## 2. Saturation and the number of steps (entry 7564) [proved]

**Prop 2.1.** (G) holds if and only if $\bigcup_{\alpha\in\mathrm{Ord}}I_\alpha=R$. If every shape in $D$ has fewer than $\rho$ arrows, for a regular cardinal $\rho$, then (G) holds if and only if $I_\rho=R$. This is the bound given in Kelly, *Basic Concepts*, §3.5, p. 45 (checked).

*Proof.* The union $\bigcup_\alpha I_\alpha$ is replete and contains $i(I)$. It is closed under $D$-limits: a diagram has a set of vertices, so it lands in some $I_\alpha$. It is also contained in every $R'$ as in (G). For $\rho$: a diagram with fewer than $\rho$ vertices in $I_\rho$ lands in some $I_\alpha$ with $\alpha<\rho$, by regularity. ∎

Consequences and examples:
- For finitary $D$, at most $\omega$ steps are needed.
- $R=\mathbf{Set}$, $I=\{2\}$, $D$ = all small limits: **exactly 2 steps**. $I_2=\mathbf{Set}$ by Prop 5.1 below. But $I_1\ne\mathbf{Set}$, because no limit of a diagram of copies of $2$ has 3 elements; this is `Buffalo.Topos.Part05.no_limit_of_bools`, already in the project.
- Kelly, §5.7 end (p. 100, checked): $\mathbf{Cat}_0$ is the colimit-closure of $\{2\}$, but the idempotent category is not a colimit of a diagram of copies of $2$. So one step is not enough there either.
- For $D$ with shapes of unbounded size, I know no bound by a small ordinal. Grothendieck expected one (29294, « expected, not proved »). **[open]**

**Remark 2.2 [proved].** (G) implies that $\mathrm{Hom}_D(R,C)\to C^I$ is faithful. The objects $X$ on which two transformations agree form a replete class closed under $D$-limits: arrows into a preserved limit, or out of a preserved colimit, are determined by their components. So (G) lies strictly between « basic » (§3) and the faithfulness condition, which 7434 [cex] and 35722 show is too weak.

## 3. The direction that holds: basic ⇒ (G), for every $D$ [proved mod (H)]

**Lemma 3.1.** $i\colon I\to R$ satisfies (G) if and only if the following holds. For every fully faithful $D$-functor $u\colon B'\to R$ with $B'\in\Delta$, and every $i'\colon I\to B'$ with $u i'\cong i$, the functor $u$ is an equivalence.

*Proof.* (⇐) Take $B'=R'$ and $u$ the inclusion. $R'$ has $D$-limits computed in $R$, so $R'\in\Delta$ and $u$ is a $D$-functor; an equivalence onto a replete full subcategory forces $R'=R$. (⇒) The essential image of $u$ is replete and contains $i(I)$. It is closed under $D$-limits: a $D'$-diagram on objects $u(b_k)$ lifts to $B'$ because $u$ is fully faithful, and $u$ preserves its limit. So by (G) the essential image is all of $R$. ∎

**Theorem 3.2.** If $i$ is basic, (G) holds. This works for any $D$, small or not, and even for a non-discrete small $I$.

*Proof.* By transfinite induction, (G) holds for $I\to R_\alpha$. At each stage, let $u\colon B'\to R_{\alpha}$ be as in Lemma 3.1, taken without loss of generality to be the inclusion of a replete full subcategory.

- *$\alpha=0$.* There is $i'\colon I\to B'$ with $u i'\cong j$. Extend $i'$ to a $D$-functor $r\colon\widetilde I\to B'$ with $rj\cong i'$. Then $urj\cong j=\mathrm{id}\circ j$, and full faithfulness of restriction to $I$ gives $ur\cong\mathrm{id}$. So $u$ is essentially surjective.
- *Successor.* Let $F\colon R_\alpha\to R_{\alpha+1}$ be the step. $F^{-1}(B')$ is replete, contains $I$ and is closed under $D$-limits, because $F$ preserves them. By induction $F^{-1}(B')=R_\alpha$, so $F=uF'$ with $F'$ a $D$-functor.
  - Localization: $F'$ inverts $\Sigma$, because $u$ is fully faithful and so reflects isomorphisms. So $F'\cong rF$ for some $r\colon R_{\alpha+1}\to B'$. Then $urF\cong F$, hence $ur\cong\mathrm{id}$.
  - Equalizing: the same, since $u$ is faithful.
  - Adding arrows: the universal arrows $\gamma_h\colon Fa_h\to Fb_h$ are $u(\beta'_h)$ for unique $\beta'_h$, because $u$ is full. So $(F',\beta')$ gives $r$ with $(urF,ur\gamma)\cong(F,\gamma)$, and therefore $ur\cong\mathrm{id}$, by the equivalence $\mathrm{Hom}_D(R_{\alpha+1},C)\simeq\{(\psi,\beta)\}$ with $C=R_{\alpha+1}$.
- *Limit ordinal.* Each $F_\beta\colon R_\beta\to R_\lambda$ factors as $uF'_\beta$ by induction. The coherence isomorphisms lift uniquely through the fully faithful $u$, so the $F'_\beta$ form a pseudo-cocone and induce $r\colon R_\lambda\to B'$. As before, $ur\cong\mathrm{id}$.
- *End.* (G) is invariant under an equivalence compatible with $I$.

In every case the universal property is applied with target $B'$, which lies in $\Delta$. ∎

## 4. Reduction of the converse to algebraicity, for every $D$ [proved mod (H); sketch for the coherence bookkeeping]

**Lemma 4.1.** Assume (H). Let $x$ lie in the $D$-closure of $i(I)$ in $R$. Then there are a basic $I\to S$, a $D$-functor $\Phi\colon S\to R$ with $\Phi|_I\cong i$, and an object $s\in S$ with $\Phi s\cong x$.

*Proof.* Induction on the saturation stage of $x$. Let $x\cong\lim d$ with $d\colon J\to I_\beta$ a $D'$-diagram; the colimit case is dual.
1. For each vertex $d_k$, choose a triple $(S_k,\Phi_k,s_k)$ by induction.
2. Form the amalgamated 2-sum of the $S_k$ over $\widetilde I$ (33666). It is basic over $I$: the steps of each $S_k$, pushed out along $\widetilde I\to$ the sum, are again steps of the same kind.
3. Adjoin the arrows of $d$, transported along $\Phi_k s_k\cong d_k$. These form a small set, because $J$ is small.
4. Equalize the composition and identity relations. They hold in $R$, so $\Phi$ extends to each new stage.
5. Now there is a diagram $\tilde d$ in the last stage $S$ with $\Phi\tilde d\cong d$. Put $s=\lim\tilde d$; then $\Phi s\cong x$, since $\Phi$ preserves the limit. ∎

**Theorem 4.2.** Assume (H). For $i\colon I\to R$:
$$i\ \text{basic}\iff \text{(G) holds and } R \text{ is algebraic}.$$

*Proof.* (⇒) Theorem 3.2.

(⇐) Let $I'\to R$ be basic, through a sequence $(R_\alpha)$ from $\widetilde{I'}$. By (G), every $x\in I'$ lies in the closure of $I$. Lemma 4.1, applied once to the small family $(x)_{x\in I'}$ and amalgamating over $\widetilde I$ as in step 2, gives $(S,\Phi)$ basic over $I$ and objects $s_x\in S$ with isomorphisms $c_x\colon x\cong\Phi s_x$. Then build:

1. $P=R\sqcup_{\widetilde{I'}}S$, the pseudo-pushout along $x\mapsto s_x$. It is basic over $I$: set $P_\alpha=R_\alpha\sqcup_{\widetilde{I'}}S$. Then $P_0\simeq S$, and the pushout of a localization, equalization or adjunction of arrows is a step of the same kind, as one checks on the $\mathrm{Hom}_D(-,C)$ descriptions. Pushouts commute with chain colimits.
2. Adjoin arrows $e_i\colon i_S\to i_R$ and their inverses, and equalize the inverse relations ($|I|$ data). The isomorphism $e$ between the two $D$-functors $\widetilde I\to S\rightrightarrows P$ (directly, and through $\Phi$ and the $R$-leg) then extends uniquely, by the envelope property.
3. Follow $S$'s own basic sequence. At each arrow-adding step, equalize the naturality squares of $e$ for the added arrows (small data). Localization steps need nothing, because their restriction maps are fully faithful. At the end the two composites $S\rightrightarrows P'$ are isomorphic through $e$.
4. For each $x\in I'$, equalize $e_{s_x}\circ\theta_x$ with the image of $c_x$, where $\theta$ is the pushout isomorphism. This involves $|I'|$ data. Call the result $P^\ast$.

A $D$-functor $P^\ast\to C$ is a tuple $(\psi\colon R\to C,\ \varphi\colon S\to C,\ \theta,\ e)$ satisfying these equations. Such a tuple is determined, up to unique isomorphism, by $\psi$: one gets $\varphi\cong\psi\Phi$ through $e$, and $\theta$ is then forced. So restriction along the $R$-leg, $\mathrm{Hom}_D(P^\ast,C)\to\mathrm{Hom}_D(R,C)$, is an equivalence for every $C$. By 2-Yoneda (take $C=R$ and $C=P^\ast$), the $R$-leg $R\to P^\ast$ is an equivalence, compatible with $I$ via $e_i$. Every step used small data and the sequence has small length, so $i$ is basic. ∎

The coherence checks in step 3 (that the extension of $e$ survives the limit stages) are routine, but I only indicate them. Hence **[sketch]** for those details.

**Corollary 4.3.** For a given $\Delta$ satisfying (H), Problem three has a positive answer if and only if every $R\in\Delta$ satisfying (G) for some small $I$ is algebraic.

## 5. $D$ = all small limits (or all small colimits): the converse fails

**Prop 5.1 [proved; Lean].** Every set $X$ is an equalizer of two maps between powers of $2$:
$$X\cong\mathrm{Eq}\Big(2^{P(X)}\rightrightarrows 2^{P(P(X))\sqcup P(X)}\Big),\qquad f(u)=\big(S\mapsto u(\textstyle\bigcap S),\ A\mapsto u(A^c)\big),\quad g(u)=\big(S\mapsto\bigwedge_{A\in S}u(A),\ A\mapsto\neg u(A)\big).$$
The equalizer consists of the complete Boolean homomorphisms $P(X)\to 2$, which are exactly the principal ultrafilters.

This is `ProblemThree.equivEqualizer : X ≃ {u : Set X → Bool // f u = g u}`, with `range_e` and `e_injective`. Hence, in $\Delta=$ complete categories, $\{2\}\to\mathbf{Set}$ satisfies (G), in 2 steps (§2). Dually, in $\Delta=$ cocomplete categories, $\{2\}\to\mathbf{Set}^{op}$ satisfies (G).

**Prop 5.2 [proved].** In $\mathbf{Set}^{op}$ the object $2$ is not $\lambda$-presentable for any regular cardinal $\lambda$.

*Proof.* $\mathbf{Set}^{op}(2,-)$ preserves $\lambda$-filtered colimits exactly when $P=\mathbf{Set}(-,2)$ sends $\lambda$-cofiltered limits of $\mathbf{Set}$ to colimits. Take the chain $A_\alpha=[\alpha,\lambda)$, $\alpha<\lambda$, with limit $\bigcap_\alpha A_\alpha=\varnothing$. Then $P(\varnothing)=1$, while $\varinjlim_\alpha P(A_\alpha)$ has at least two elements: the germs of $\varnothing$ and of $A_\alpha$ differ, since every $A_\beta$ is non-empty. ∎

**Prop 5.3 [proved mod details marked sketch; cited].** Let $\Delta=$ cocomplete categories with cocontinuous functors. If $S$ is algebraic, every object of $S$ is $\mu$-presentable for some $\mu$. Hence $\mathbf{Set}^{op}$ is not algebraic, and $\{2\}\to\mathbf{Set}^{op}$ satisfies (G) without being basic. Dually, $\{2\}\to\mathbf{Set}$ is a counterexample for $D$ = all small limits. This is the counterexample Grothendieck pointed to (13448, 13380).

*Proof.* By induction along a basic sequence, $S\simeq\Phi\text{-Alg}$ for a small sketch $(A,\Phi)$, with $\mathrm{Cocts}[\Phi\text{-Alg},B]\simeq\Phi\text{-Com}[A,B]$ for every cocomplete $B$. This is Kelly, Thm 6.11 ($\Phi$-Alg is the reflective orthogonality class of a regulus in $[A^{op},\mathbf{Set}]$, by Thm 6.5) together with Thm 5.56 (with $C$ cocomplete and $A$ small, left adjoints may be replaced by cocontinuous functors); checked. The steps:
- *Envelope:* $(I,\varnothing)$, which is $\mathbf{Set}^I$.
- *Enlarging the sketch:* given a small set of objects, pass to the closure $D$ of $K(A)$ under $\lambda$-small colimits for $\lambda$ large. It is small (Kelly §3.5), and $\Phi\text{-Alg}\simeq(D,\lambda\text{-colimits})\text{-Alg}$ with the same comodels in every cocomplete $B$ (Kelly Prop 6.21, Cor 6.22, Thm 6.23; checked).
- *Inverting $\sigma\colon X\to Y$:* enlarge so that $\sigma$ lies in $D$, then add the cylinder « $Y$ with leg $\sigma$ is the colimit of the one-object diagram $X$ ».
- *Equalizing:* invert $Y\to\mathrm{coeq}$ (cf. 11824).
- *Adding arrows:* freely adjoin the arrow to $D$, keeping the same cylinders.
- *Chains:* choose the sketches recursively, so that $D_\beta$ maps into $D_\gamma$. Take the pseudo-colimit of the $D_\beta$ in $\mathbf{Cat}$ and the union of the cylinders. Comodels form the pseudo-limit. This coherence is the **[sketch]** part.

Finally, in $\Phi\text{-Alg}$ the cylinders are cones over diagrams of presheaves of size $<\lambda$, so the orthogonality class is closed in $[A^{op},\mathbf{Set}]$ under $\lambda$-filtered colimits. Every presheaf on a small $A$ is a small colimit of finitely presentable representables, hence $\mu$-presentable for some $\mu\ge\lambda$. So every object of $\Phi\text{-Alg}$ is $\mu$-presentable there. Prop 5.2 concludes. ∎

(The literature fact behind this is that the algebraic $S$ are exactly the locally presentable categories: Gabriel–Ulmer, and Adámek–Rosický ch. 1. I did **not** check exact locators there; the web search did not reach the book's text. The argument above uses only Kelly's checked results.)

## 6. Small $D$: the equivalence holds, with the base fixed [proved mod (H)]

**Theorem 6.1.** Let $D$ be a small set of shapes, each with fewer than $\rho$ arrows, $\rho$ regular. Assume (H), with the constructions applied to small categories and small data giving small categories (the hypothesis of 7694). Then for every small discrete $I$ and every $i\colon I\to R$: $i$ is basic if and only if (G) holds. The base is fixed: we do not enlarge $I$ to $\mathrm{Ob}\,R$.

*Proof 1, via Theorem 4.2.* By §2, $R=I_\rho$. Each $I_\alpha$ has a small set of isomorphism classes: there are only a small set of diagrams of each of the small set of shapes (Kelly §3.5). So $R$ is essentially small. Its skeleton $R_s$ is algebraic over $\mathrm{Ob}\,R_s$ (34019): from $\widetilde{\mathrm{Ob}R_s}$, adjoin the arrows of $R_s$, equalize the composition relations, and invert the comparison maps for the small set of $D$-diagrams. By 2-Yoneda the result is $\simeq R$. Theorem 4.2 then finishes.

*Proof 2, direct.* Build a chain $S_\beta$ for $\beta\le\rho$ with $D$-functors $\Phi_\beta\colon S_\beta\to R$ extending $i$. Each successor step does two things: (a) adjoin a formal arrow $a\to b$ for every arrow $\Phi a\to\Phi b$ of $R$; (b) equalize every pair that $\Phi$ identifies. Both are small, because $S_\beta$ is small. Since $\rho$ is regular and the shapes are $\rho$-small, the 2-colimit $S_\rho$ can be computed in $\mathbf{Cat}$: diagrams and parallel pairs come from earlier stages, and a functor out of it is a $D$-functor exactly when all its restrictions are. So $\Phi_\rho$ is fully faithful. Its essential image is closed under $D$-limits, since diagrams lift along a fully faithful functor. By (G) it is everything. A fully faithful, essentially surjective $D$-functor is an equivalence in $\Delta$. ∎

Where (H) is available for small $D$: when $D'=\varnothing$ (or dually $D''=\varnothing$), Kelly Thm 5.35 (the free $\mathcal F$-cocompletion is small) and Thms 6.21–6.23 provide envelopes and localizations as small categories (checked). For mixed small $D$ ($D'$ and $D''$ both non-empty) I have not checked a reference. Grothendieck's own remark 20613 asserts it without proof.

The candidates suggested for the fixed-base case all fall under Theorem 6.1, and the equivalence **holds** for them: $D$ = finite limits with $I$ infinite (but small), and $\kappa$-small limits. There is no counterexample with small $D$.

## 7. Side finding: the topos case (ORG14LNb5gE-6683, -7147, -3843)

For topoi ($D'$ = finite limits, $D''$ = all colimits, plus Giraud's exactness and the generator condition), entry 6683 says: « every object of $R_{\alpha+1}$ is covered by images of objects of $R_\alpha$ ». Entry 7147 (necessity) says that basic implies the finite products of $I$ generate $R$. Both are **false as stated** **[proved]**:

- $R_\alpha=\mathbf{Set}$. Adjoin one arrow $1\to1\sqcup1$; this gives the classifier of clopen decompositions, $R_{\alpha+1}=\mathbf{Set}\times\mathbf{Set}$, and the image of $\mathbf{Set}$ is the diagonal $\{(n,n)\}$. The object $(1,0)$ receives a map from $(n,n)$ only when $n=0$, so it is not covered.
- $I=\{x\}$. Start from the object classifier, invert $x\to1$ (giving $\mathbf{Set}$), then adjoin $1\to1\sqcup1$. This makes $\{(1,1)\}\to\mathbf{Set}\times\mathbf{Set}$ basic, but the finite products of $(1,1)$ are just $(1,1)$, which does not generate.
- (G) does hold here, as Theorem 3.2 requires: pull back $(\mathrm{inl},\mathrm{inr})\colon(1,1)\to(2,2)$ along $\mathrm{inl}$ to get $(1,0)$.
- A $\mathbf{Z}/2$-set example of the same kind: $Y=\mathbf{Z}/2\sqcup1$ in $\mathbf{Z}/2$-Set. No map $Y^n\to\mathbf{Z}/2$ exists, yet $\mathbf{Z}/2=Y\times_{Y/\tau}1$, and the theory of torsors makes $\{Y\}$ basic.

The sufficiency half (7213) is untouched. The repaired statement is « basic ⟺ (G) »: every topos is algebraic (4018), so Theorem 4.2 gives (G) ⇒ basic, since its proof uses only constructions available in topoi (classifying topoi, 2-pushouts 5022, subtopoi). For basic ⇒ (G) in the topos $\Delta$, the proof of Theorem 3.2 needs the closure $B'$ to lie in $\Delta$. Closure under finite limits and colimits gives Giraud's exactness, but I have not proved that $B'$ has a small generating set. **[expected, not checked]** This would be the first correction of these entries; `Part07.json` currently records them only as « not-formalised ».

## 8. Summary: what is proved, what is open

- **basic ⇒ (G):** proved for every $D$ (§3), with $I$ discrete or small, assuming (H).
- **(G) ⟺ saturation reaches $R$:** proved (§2). For $\rho$-bounded $D$, $\rho$ steps suffice; in the $\mathbf{Set}/\{2\}$ example, exactly 2.
- **Reduction:** basic ⟺ (G) + algebraic, for every $D$ under (H) (§4; the coherence bookkeeping is sketched).
- **Small $D$:** the fixed-base equivalence holds (§6), under (H). For one-sided small $D$, (H) is supplied by Kelly; mixed small $D$ is not checked.
- **$D$ = all small limits / all small colimits:** the converse fails, with $\{2\}\to\mathbf{Set}$ (respectively $\mathbf{Set}^{op}$). (G) is proved and checked in Lean; non-algebraicity is proved via presentability, with one coherence step sketched (§5).
- **Topoi:** the fixed-base equivalence holds in the direction (G) ⇒ basic. The converse needs one unchecked point. Entries 6683 and 7147 are false as stated (§7).
- **Open [open]:**
  - Large $D$ beyond these cases, for example plain $\mathrm{Cat}_D$ with $D'$ finite and $D''$ all colimits but no exactness. There $\mathbf{Set}^{op}$ with $\{2\}$ satisfies (G), and I do not know whether it is algebraic.
  - Mixed large $D$, where problem one itself may fail.
  - Whether the number of saturation steps is bounded by a small ordinal for unbounded $D$ (29294).
  - By Corollary 4.3, the question for each $\Delta$ is exactly whether « (G) for some small $I$ ⇒ algebraic ».

## 9. Literature actually checked

G. M. Kelly, *Basic Concepts of Enriched Category Theory*, TAC Reprints 10 (2005), read in the TAC PDF:
- §3.5 (pp. 44–45): transfinite closure, the bound $A=A_\rho$, smallness of the closure;
- Prop 3.40 (pp. 46–47): the colimit-closure of $A$ is everything iff $A$ is strongly generating, given cocompleteness, finite completeness and weak cowellpoweredness. This is the « strong generator » form of (G);
- §5.7 (pp. 98–100), Thm 5.35, and the closing remark on $\mathbf{Cat}_0$ and $\{2\}$;
- Thm 5.56 (p. 96 ff.);
- §6.2–6.4: Thm 6.5, Thm 6.11, Prop 6.21, Cor 6.22, Thm 6.23.

Not checked (cited from memory only): Gabriel–Ulmer, *Lokal präsentierbare Kategorien*, LNM 221 (1971); Adámek–Rosický, LMS LN 189 (1994), ch. 1 (orthogonality classes, sketches, $\mathbf{Set}^{op}$ not locally presentable).
