# Buffalo 1973, algebraic groups: an internal check of our transcripts and boards

**Reference.** None. No written notes of the course « Theory of algebraic groups » exist, so this check is internal. It is the counterpart of `docs/buffalo-funcalg-check.md`, where the algebraic geometry course was checked against Gaeta's notes.

**Our side.** The local transcripts `transcripts-buffalo/<video>-<start>.en.md` (git-ignored, rights #31) and the published boards `public/buffalo-boards/<video>-<start>.json`. Each verdict rests on one or more of four kinds of evidence:
- *Captions*: the raw automatic captions in `transcripts-buffalo/captions/`.
- *Whisper*: the second-pass hearings recorded in the transcripts and in the review tab (`public/transcripts-bourbaki/review.json`). The sides of 27 June – 11 July have no Whisper variant recorded.
- *Board*: the board items. The boards are reconstructions from the transcript, so they test consistency and are not independent witnesses.
- *Mathematics*: internal consistency, and the standard theory of affine group schemes.

The board corrections already made by the Lean pass (`docs/buffalo-corrections.md`) were taken into account. No audio was listened to again, and « to listen » marks the items that only the audio can decide. No exposé of SGA 3 or section of Demazure–Gabriel was checked for this note, so none is cited; the arguments are the mathematics itself.

**Status.** Applied on 7 November 2026 with Michel's approval; see « Status (7 November 2026) » below. Times are video times (h:mm:ss). Quotations are limited to a few words, and everything else is described.

## Summary

- **Sides checked:** 21 group-scheme sides, 4 June – 11 July 1973, plus one undated side (list in section 1).
- **Proposed items: 53.** Of these, 27 are settled and 26 are to listen.
  - misheard term: 13;
  - garbled statement: 13;
  - missing statement or word: 8;
  - symbol: 5;
  - formula, variance or index: 3;
  - the lecturer's own slip or outdated claim, needing an editorial note only: 2;
  - board items to amend: 9. None is mislabelled in the strict sense. One (23851, t = 25330) states an example the lecture does not give, and one (23263) has its « resp. » reversed.
- **Doubtful [?] marks:** about 830 in the bodies of the 21 sides. **70 are settled** (dropped or replaced), and 6 more are replaced by a proposal that is still to listen. Nearly all of the rest are in room exchanges, fillers or the noise-damaged stretches of 19 and 27 June, and none of them carries a statement.
- **Formulas, variances and indices:** almost everything agrees in transcript, board and mathematics. The exceptions are three items: a right action written as a left one (10808), δ(u) written with u ⊗ u (26681), and I² = 0 for I² = I in a header (26681).
- **Sides with nothing to correct:** none is entirely clean. Four are close: 18200, 31596, 13088 and 03729 (section 3).

### Corrections that change the mathematics

1. **_lTf_L0yvrU-07948, 2:33:35–2:34:42.** The biduality D(D(M)) ≅ M_k holds only after M_k is **sheafified for the Zariski topology**. Settled for 2:33:35, with the exact words at 2:34:42 to listen. Board 9282 needs the same note.
2. **_lTf_L0yvrU-26681, 7:31:42.** δ(u) is u ∘ μ, not (u ⊗ u) ∘ μ; as we have it, the sentence equates the two sides of what is being proved. Settled.
3. **_lTf_L0yvrU-26681, header.** For a constant finite group, I² = I, not I² = 0. Settled.
4. **_lTf_L0yvrU-28721, 8:29:19.** Affine commutative groups are not reflexive for G_m in general; the right word is diagonalisable. The board is already corrected. To listen.
5. **_lTf_L0yvrU-10808, 3:33:56.** As written, the associativity axiom for A ⊗ M is that of a **right** action. He redoes it correctly on 13 June. Editorial note, plus board 12836.
6. **_lTf_L0yvrU-00000, 0:05:30.** The supplied « not necessarily [commutative] » is wrong: the k-algebras are commutative. To listen.
7. **_lTf_L0yvrU-00858, 0:25:31.** SL_n is divided by the **scalar** matrices (μ_n), not by the diagonal ones. Probably his slip. To listen.
8. **_lTf_L0yvrU-21165, 6:33:01 and 6:36:13.** For monoids the targets are End(M) = M_n, not Aut or GL_n. No non-trivial monoid map (A¹, ·) → GL_n exists.
9. **_lTf_L0yvrU-23851, 6:59:54.** M₁ is O under multiplication, not M_n. Settled. Also **7:05:27**: the hypothesis is « injective on points », not « monomorphism on points ». To listen.
10. **3ULFIl_2Wis-05301, 2:09:20.** « A complete field » cannot be right. The fields with 1 < [k_s : k] < ∞ are the real closed ones (Artin–Schreier). To listen.
11. **3ULFIl_2Wis-14051, 3:54:14.** Separable ⇔ **geometrically** normal; « normal » alone is false over imperfect fields. To listen. Also **4:30:32**: drop the supplied « [faithfully flat] ». To listen.
12. **3ULFIl_2Wis-10195, 3:29:10.** « over k′ / of k′ » should be « over K / of K ». Settled.
13. **3ULFIl_2Wis-16934, 5:25:11 and 5:26:15.** Two editorial notes on the lecturer's own statements: the p-Lie algebra determines G₁ (not a neighbourhood « of order p² »), and the simple restricted Lie algebras include the Cartan-type ones.
14. **Board 4896 (03729).** Reflexivity of modules does not require projective of finite type (ℤ^ℕ is reflexive over ℤ). Settled.

### For a human to listen to (the ones that matter)

- **_lTf_L0yvrU:**
  - 00000: 0:05:30.
  - 00858: 0:25:31, 0:34:14 (ring), 0:39:36 (free or projective), 0:55:52 (pro-representable).
  - 07948: 2:28:19 (Cartier), 2:34:42.
  - 21165: 6:33:01 (End or Aut).
  - 23851: 6:44:17, 7:05:27 (two items), and board item t = 25330.
  - 26681: 7:58:00.
  - 28721: 8:29:19 (affine), 8:31:29 (India or Canada).
- **3ULFIl_2Wis:**
  - 00000: 0:35:41.
  - 02838: 0:47:24.
  - 05301: 1:45:58, 2:09:20.
  - 08161: 2:16–2:23 (pro-étale or profinite), 2:37:59.
  - 10195: 3:19:27 (κ(y) or κ(x)).
  - 14051: 3:54:14, 4:30:32.
  - 16934: 4:53:49 (geodesics), 5:28:26 (Shafarevich?).
  - 25298: 7:05:51 (ℤ/p or ℤ/ℓ).

## Status (7 November 2026)

Michel approved the corrections on 7 November 2026, and they were applied to the 21 local transcripts of section 1 (110 edits) and to 10 board items in 6 published boards. Each changed transcript has a « Third pass, 2026-11-07 » line in its header comment. Every passage was found at its timestamp; the one exception is 26681 7:31:42, whose phrase « the composition of u ⊗ u and [μ] » ends the 7:30:36 paragraph and was corrected there. Each edit touches only the words its item names, and Whisper comments were kept.

- **Settled corrections, applied without [?] (14 edits):**
  - _lTf_L0yvrU: 00858 0:23:21 (a quotient); 05096 2:09:35 (quotients); 07948 2:33:35 (sheafify); 23851 6:58:46 (the two premises), 6:59:54 (O under multiplication; M_n for n = 1); 26681 7:31:42 (u and μ), header (I² = I).
  - 3ULFIl_2Wis: 00000 0:23:13 (0-connected); 05301 1:43:44 (0-connected, both places); 08161 2:28:18 (compact, both places, with « [in Bourbaki's sense] » once); 10195 3:29:10 (over K, and « of K » at 3:30:14).
- **Editorial notes on the lecturer's own slips (7):** _lTf_L0yvrU 07948 2:56:14 (antipode); 10808 3:37:09 (« [as written, the axiom for a right action; see 13 June, 5:13:35] », where the passage 3:33:56–3:37:09 ends); 21165 6:36:13 (« [read: into End(kⁿ) = M_n] »); 26681 7:54:49 (« [read: the sum of the coefficients] »); 3ULFIl_2Wis 00000 0:24:18 (see 2 July, 1:28:22); 16934 5:25:11 (« [read: the Frobenius neighbourhood G₁] ») and 5:26:15 (the Cartan-type algebras).
- **Doubtful marks dropped: 71.** 62 come from plain drops and 9 from inside the settled corrections. The report counts 70; the extra one is at 23851 6:59:54, where both marks of « M₁ [?] … M_n [?] » were dropped along with the mark on « [O¹] [?] ».
- **Proposed readings put in, still to listen, with [?] kept or added (29 edits; net +8 [?] in the bodies):**
  - _lTf_L0yvrU: 00000 0:05:30; 00858 0:25:31 (« diagonal [?] [read: scalar] »), 0:34:14, 0:39:36, 0:55:52; 07948 2:28:19, 2:34:42; 10808 3:10:01; 21165 6:33:01 (the captions' Aut/GL_n in a comment); 23851 6:44:17, 6:57:42 (twice), 6:58:46 (G_k′), 7:05:27 (both items); 28721 8:29:19.
  - 3ULFIl_2Wis: 00000 0:35:41; 02838 0:47:24; 05301 1:45:58, 2:09:20 (the captions' « complete » in a comment); 08161 2:37:59; 10195 3:19:27 (the captions' κ(x) in a comment); 14051 3:54:14, 4:11:05, 4:30:32; 16934 4:53:49, 5:28:26; 25298 7:05:51, 7:08:11 (the captions' variant in a comment).
- **Still for the audio, nothing changed because no reading is proposed:**
  - _lTf_L0yvrU: 05096 2:00:27; 10808 3:06:44, 3:25:16, 3:43:46; 21165 5:59:15, 6:09:11, the name « [O¹] » at 6:36:13; 26681 7:58:00; 28721 8:31:29; 31596 8:56:25.
  - 3ULFIl_2Wis: 00000 0:05:13, and the clause after 0:23:13; 02838 0:54:09 (separability); 08161 2:16–2:23 (pro-étale or profinite); 13088 3:46:46; 16934 4:51:40.
- **Skipped:**
  - Board 8163 and the header of 08161 stay « pro-étale » until the audio is heard, since the item makes the change conditional on it. The header of 13088 likewise waits for 3:46:46.
  - The optional « [π] » for δ at 23851 6:44:17 was not added.
  - Board item 25330 was reworded but not moved to about 7:03:16, because moving it would change its timing field.
  - The items marked « note, no change » were left alone: 05096 1:25:01, 18200 5:07:16, 28721 8:13:10.
- **Boards changed** (in `public/buffalo-boards/` and in their local sources in `transcripts-buffalo/`, so that a full `npm run buffalo-boards` keeps them; timing fields untouched):
  - _lTf_L0yvrU-3729 t = 4896: the biduality M ≃ M^∨∨ « fails in general (holds for M projective of finite type) ».
  - _lTf_L0yvrU-7948 t = 9282: « M_k replaced by the associated Zariski sheaf »; t = 10309: « the antipode » added.
  - _lTf_L0yvrU-10808 t = 10811: π and ε both algebra homomorphisms; t = 11541: Aut(X) for a group, End(X) for a monoid; t = 12836 (text and diagram): marked uncertain, with the right-action note.
  - _lTf_L0yvrU-21165 t = 23263: the « resp. » put right (closed submonoid of End(M), resp. closed subgroup of GL_n).
  - _lTf_L0yvrU-23851 t = 25330: the Frobenius example, which the lecture never gives, is replaced by the lecture's examples (x ↦ x² on G_m, t ↦ sⁿ) and « a radicial endomorphism is surjective ». It stays marked uncertain (to listen).
  - 3ULFIl_2Wis-16934 t = 19382: « determines only G₁ = Ker F »; t = 19575: the correction is now marked as editorial, with what he said.
- **Index:** `docs/buffalo-groupes/index.tex` entry 12836 (3:33:56) gives the associativity axiom in the form he wrote, which is the axiom of a right action. The report does not cover the index entry, so it was not changed. The other index entries near the corrected passages agree with the corrections (10811 was already corrected, and 11541, 23263, 25194 and 28489 are right). `npm run buffalo-index` was not rerun.
- **Derived files:** `npm run buffalo-review` was rerun. It writes only the git-ignored review file, and `git status` shows no public change besides the six boards.

## 1. Sides checked

| File key | Date | Tape, side | Video time | Subject (from the header) |
|---|---|---|---|---|
| _lTf_L0yvrU-00000 | undated | unlabelled tape 1, A | 0:00:00–0:14:18 | group objects, affine spaces, G_a, G_m, GL_n |
| _lTf_L0yvrU-00858 | 4 June | tape 1, A | 0:14:18–1:02:09 | examples, triangular groups, centre, W(M), flatness |
| _lTf_L0yvrU-03729 | 4 June | tape 1, B | 1:02:09–1:24:56 | W(M), V(M), finite presentation, biduality |
| _lTf_L0yvrU-05096 | 6 June | tape 1, A | 1:24:56–2:12:28 | Hom(M, N), R*, μ_n, Frobenius, PGL_n, α_{p^i} |
| _lTf_L0yvrU-07948 | 11 June (opens on 6 June) | tape 1 | 2:12:28–3:00:08 | Frobenius kernel, D(M), Hopf algebras |
| _lTf_L0yvrU-10808 | 11 June | tape 2 | 3:00:08–3:45:53 only | bialgebras, actions, comodules |
| _lTf_L0yvrU-18200 | 13 June | tape 2, A | 5:03:20–5:52:45 | comodules, V(A), H = A^∨ |
| _lTf_L0yvrU-21165 | 13 June | tape 2, B | 5:52:45–6:37:31 | subcomodules, local finiteness, closed in GL_n |
| _lTf_L0yvrU-23851 | 19 June | tape 1, A (bad) | 6:37:31–7:24:41 | embedding in M_n, monomorphisms, Dist(X) |
| _lTf_L0yvrU-26681 | 19 June | tape 1, B (bad) | 7:24:41–7:58:41 | distributions, hyperalgebra, Lie algebra |
| _lTf_L0yvrU-28721 | 20 June | tape 1, A | 7:58:41–8:46:36 | Dist(D(M)), constant schemes, Cartier duality |
| _lTf_L0yvrU-31596 | 20 June | tape 1, B | 8:46:36–8:59:13 | D(G) = Spec A^∨, μ_p, α_p |
| 3ULFIl_2Wis-00000 | 27 June | tape 1, A (bad) | 0:00:00–0:47:18 | geometric connectedness, G⁰ |
| 3ULFIl_2Wis-02838 | 27 June | tape 1, B (bad) | 0:47:18–1:28:21 | étale schemes, Π-sets, π₀(X/k) |
| 3ULFIl_2Wis-05301 | 2 July | tape 1, A | 1:28:21–2:16:01 | geometric irreducibility, torsors, π₀ |
| 3ULFIl_2Wis-08161 | 2 July | tape 1, B | 2:16:01–2:49:55 | pro-étale schemes, geometric regularity |
| 3ULFIl_2Wis-10195 | 10 July | tape 1, A | 2:49:55–3:38:08 | smoothness, Jacobian criterion, normality |
| 3ULFIl_2Wis-13088 | 10 July | tape 1, B | 3:38:08–3:54:11 | homogeneity: separable ⇔ smooth |
| 3ULFIl_2Wis-14051 | 11 July | tape 1, A | 3:54:11–4:42:14 | separatedness, UV, homogeneous spaces |
| 3ULFIl_2Wis-16934 | 11 July | tape 1, B | 4:42:14–5:30:34 | images, dévissage, Chevalley, p-Lie algebras |
| 3ULFIl_2Wis-25298 | 11 July | tape 3 | 7:01:38–7:11:20 | structure of algebraic groups, simple pieces |

**Not checked here, because they are AG sessions already checked in `docs/buffalo-funcalg-check.md`:** _lTf_L0yvrU-10808 from 3:45:53, _lTf_L0yvrU-13644 and -16477 (11 June), and 3ULFIl_2Wis-19834 and -22716 (11 July).

## 2. Discrepancies, by side

Each item gives the time, the kind, our reading, the evidence, the proposed correction, and its verdict (« settled » or « to listen »).

### _lTf_L0yvrU-00000 (undated, unlabelled tape 1, side A)

- **0:05:30**, garbled statement (changes the mathematics as it stands).
  - Ours: the opposite of the k-algebras, « not necessarily [commutative] [?] ».
  - Evidence: the algebras must be commutative. X(k′) = Hom(A, k′) is taken over commutative k′, and at 0:14:26 he says the groups are representable by commutative algebras. Nothing in the captions sounds like « commutative »; « not necessarily » probably qualified something else, such as « of finite type ».
  - Correction: drop « [commutative] », keep « not necessarily [?] », and add an editorial note « [the algebras are commutative] ». **To listen.**
- **0:09:56**, doubtful mark settled.
  - Ours: « every [homomorphism] [?] » from k′ to k″. Whisper hears something like « of algebras ».
  - Evidence: functoriality of the group structure requires exactly this; board 596.
  - Correction: « [homomorphism of algebras] », drop the [?]. **Settled.**
- **0:02:15**, doubtful mark settled. « structures on the X(Z) [?] » is the definition he recalls (board 459). Drop the [?]. **Settled.**
- Marks: 5 [?], 2 settled, 3 left. Agrees: group objects carried by functors that commute with finite products and the final object; the full faithfulness of the embedding into functors; G_a, G_m, GL_n (boards 3–778).

### _lTf_L0yvrU-00858 (4 June, tape 1, side A)

- **0:23:21**, missing word.
  - Ours: « represent in terms of [?] ». The captions have « a coent of », that is « a quotient of ».
  - Evidence: the next sentence describes the algebra as k[x, y]/(xy − 1); board 1401.
  - Correction: « in terms of [a quotient] ». **Settled.**
- **0:24:26**, doubtful mark settled. « PGL₂ [?] » in the room's question: Whisper hears GL2, and the answer (a quotient group, the projective group) confirms the reading. Drop the [?]. **Settled.**
- **0:25:31**, garbled statement (probably his own wording; changes the mathematics).
  - Ours, with the captions: SL modulo « the diagonal matrices » of determinant 1.
  - Evidence: the kernel of SL_n → PGL_n is the group of **scalar** matrices in SL_n, that is μ_n, as he says himself in the same sentence and at 1:59:24. The diagonal matrices of determinant 1 form a torus of rank n − 1.
  - Correction: an editorial « [read: scalar] » after « diagonal ». **To listen**, to confirm that the slip is his.
- **0:34:14**, misheard term.
  - Ours: « change our rank [?] ». The captions have « rank », Whisper « way ».
  - Evidence: he is replacing the base ring k by k′ at this point.
  - Correction: « change our [ring] [?] ». **To listen.**
- **0:39:36**, misheard term.
  - Ours: the algebra of G « [projective] [?] » as a module, for the centre over a base that is not a field. The captions have « the al G3 module », which reads « the algebra of G free [as a] module ».
  - Correction: « [free] [?] ». **To listen.** Both hypotheses are reasonable, and the captions favour « free ».
- **0:41:50**, doubtful mark settled. « [functor of automorphisms] [?] » of G_a: the room's question is about Aut G, and board 2510 agrees. Drop the [?]. **Settled.**
  - The statement holds as transcribed. In characteristic p, Aut(G_a)(k′) is the set of the Σ aᵢ x^{p^i} with a₀ invertible and aᵢ nilpotent for i ≥ 1, an ind-scheme and not representable.
- **0:45:06**, doubtful mark settled. « additive structure [of] k′ [?] »: the unipotent 2 × 2 matrices form a group isomorphic to (k′, +) (board 2639). Drop the [?]. **Settled.**
- **0:55:52**, misheard term.
  - Ours: representable functors commute with all inverse limits, « not only finite ones, as any other [?] does ». The captions have « program », Whisper « present ».
  - Evidence: the contrast he draws is with pro-representable functors, which commute with finite inverse limits but not, in general, with infinite products.
  - Correction: « as any [pro-representable] [?] [functor] does ». **To listen.**
- Marks: 21 [?], 4 settled, 17 left. Agrees:
  - the algebras of G_a, G_m and GL_n;
  - T_n ≃ A^{n(n−1)/2} × G_m^n, which fits the n(n+1)/2 pairs i ≤ j counted with the diagonal (boards 1196, 1262);
  - the centre as Ker(G → Aut G), stable under base change;
  - W(M) as Ker(1 − p) for M projective of finite type;
  - flatness tested through k ⊕ N′ → k ⊕ N;
  - M ⊗ k^I ≅ M^I (boards 1596–3692).

### _lTf_L0yvrU-03729 (4 June, tape 1, side B)

- **1:17:21**, doubtful mark settled. « [bilinear] [?] » for the pairing (M ⊗ k′) × Hom(M, k′) → k′: Whisper hears « pairing », and the mathematics and board 4641 fix the sense. Drop the [?] and keep the supplied word. **Settled.**
- **1:20:31**, two doubtful marks settled. « [dual] [?] » and « [fully faithful] [?] »: both are what the biduality argument needs (boards 4767, 4896). Drop both. **Settled.**
- **1:21:36**, board item to amend (board 4896).
  - He says biduality for modules works only for projective modules of finite type. That is fine as an oral simplification.
  - The board states it as a fact, which is false in general: ℤ^ℕ is reflexive over ℤ (Specker).
  - Correction to the board: « fails in general (holds for M projective of finite type) ». **Settled.**
- Marks: 10 [?], 3 settled, 7 left, all filler. Agrees:
  - finite type and flat ⇒ finite presentation, through the five-lemma diagram (boards 3799–3925);
  - V(M) represented by S_k(M);
  - the variances: W covariant, V contravariant (board 4324);
  - W(M) ≅ V(M^∨) (boards 4960, 5023).

### _lTf_L0yvrU-05096 (6 June, tape 1, side A)

- **2:09:35**, misheard term.
  - Ours: in the room's question, « by taking portions [?] »; Whisper has « potions ».
  - Evidence: the exchange is about groups obtained as quotients, and on side -00858 (0:25:31) the captions write « portions » for « quotients ».
  - Correction: « [quotients] ». **Settled.**
- **1:32:36**, doubtful mark settled. « a [ring] [?] object »: the lemma is about ring objects (board 5620). Drop the [?]. **Settled.**
- **1:40:03**, doubtful mark settled. « an epimorphism [?] of rings »: A → A[Δ⁻¹] is a localisation, hence an epimorphism (board 6070). Drop the [?]. **Settled.**
- **2:00:27**, doubtful mark left. SL_p → PGL_p is « purely inseparable [?] »; Whisper hears « purely infinitesimal ». Both are true (board 7227). **To listen**; the mathematics is unaffected.
- Notation, no correction: at 1:25:01–1:30:21 he calls k′ ↦ M ⊗ k′ « V(M) » and notices the slip himself. The header and the board use the right letters.
- Marks: 15 [?], 3 settled, 12 left. Agrees:
  - Hom(M, N) = V(M ⊗ N^∨) and End(N), the latter non-commutative;
  - R* as a fibre product (boards 5812–5876);
  - μ_n free of rank n, and its points in characteristic p;
  - λ ↦ λᵖ bijective on points over perfect fields but not an isomorphism;
  - GL_n(k′) spanning M_n(k′);
  - SL_n ∩ G_m = μ_n, and PGL_n = GL_n/G_m = SL_n/μ_n;
  - End(G_a) = the p-polynomials;
  - α_{p^i};
  - the Frobenius kernel of GL_n (boards 5101–7907).

### _lTf_L0yvrU-07948 (11 June, tape 1; opens on 6 June material)

- **2:33:35 and 2:34:42**, missing statement (changes the mathematics).
  - Ours: the biduality between D(M) and the constant group M_k holds « except [?] … to [?] it a little », and M_k must be taken « a little bit [?] [more] [?] [carefully] [?] ».
  - Evidence:
    - The captions have « to shify it a little », that is, sheafify.
    - At the second place Whisper hears « that's good technology », that is, Zariski topology.
    - The mathematics requires exactly this. Hom_gr(D(M)_{k′}, G_m) is the set of group-like elements of k′[M], which are the locally constant M-valued functions on Spec k′. So biduality holds for the constant Zariski sheaf, and fails for the constant functor as soon as k′ has non-trivial idempotents.
  - Correction: at 2:33:35, « to [sheafify] it a little » (**settled**). At 2:34:42, « [one has to sheafify it] … [with respect to the Zariski topology] [?] » (**to listen** for the exact words).
  - Board 9282 (« essentially an isomorphism »): add « (M_k replaced by the associated Zariski sheaf) ». **Settled.**
- **2:28:19**, misheard term.
  - Ours: in characteristic 0 a radicial group is trivial, « that's [a theorem] [?] ». The captions have « That's uh tell ».
  - Evidence: this is Cartier's theorem (group schemes over a field of characteristic 0 are reduced).
  - Correction: « that's [Cartier's theorem] [?] ». **To listen.**
- **2:56:14**, missing term (his own lapse). He cannot recall the name of σ and calls it a « contraposition ». The standard name is **antipode**, as the header already says.
  - Correction: an editorial note « [the standard name is antipode] ». Board 10309: add « (the antipode) ». **Settled.**
- **2:57:21**, doubtful mark settled. « Hopf algebras [?] »: the captions have « hope also », and the graded algebras of the next sentence confirm the reading. Drop the [?]. **Settled.**
- **2:35:46**, doubtful mark settled. « [group laws] [?] », translated on X = Spec A next (board 9346). Drop the [?]. **Settled.**
- Marks: 43 [?], 3 settled, 40 left, none in a formula. Agrees:
  - the Frobenius kernel ideal and (λ_ii − 1)ᵖ = 0;
  - D(M) contravariant, D(ℤ) = G_m, D(ℤ/n) = μ_n;
  - k[M] with e^m e^{m′} = e^{m+m′};
  - diagonalisable groups as closed subgroups of G_m^r;
  - radicial = infinitesimal, his definition;
  - the Hopf diagrams (associativity, unit, commutativity, inverse), all with the right variance (boards 8101–10641).

### _lTf_L0yvrU-10808 (11 June, tape 2; the groups part, 3:00:11–3:45:53)

- **3:33:56–3:37:09**, variance (the lecturer's own slip, faithfully transcribed).
  - He puts A on the left (3:31:46) and states associativity for u₀ : M → A ⊗ M as (π ⊗ 1)u₀ = (1 ⊗ u₀)u₀, saying that it expresses that G operates on M.
  - Evidence: with his own definition of the action through the universal point (3:29:36), this diagram gives (gg′)x = g′(gx), a **right** action. A direct check on u₀(m) = Σ aᵢ ⊗ mᵢ confirms it.
  - He redoes it correctly with M ⊗ A on 13 June (18200, 5:11:29–5:13:35).
  - The slip is harmless for groups, as he says at 3:44:50, but not for the monoids he claims at 3:40:18. The same diagram for B (board 11141) is right, since functions are contravariant.
  - Correction: keep his words, and add an editorial note « [as written, the axiom for a right action; see 13 June, 5:13:35] ». Mark board 12836 u, with the same note. **Settled.**
- **3:12:21**, board item to amend. Board 11541 has G → Aut(X) for a monoid; it should be End(X), the point of the question at 3:23:08. Correction: « (Aut(X) for a group, End(X) for a monoid) ». **Settled.**
- **3:00:11**, board item to amend. Board 10811 makes only π an algebra homomorphism, but ε must be one too.
  - The index entry was already corrected (docs/buffalo-corrections.md, _lTf_L0yvrU-10811), but the board item was not.
  - Correction: the same wording on the board. **Settled.**
- **3:23:08, 3:27:29, 3:11:06**, doubtful marks settled: « End [?] » (the captions have « nomisms »), « u₀ [?] » (« you not », board 12449) and « ε, ω [?] » (« epsilon omega »). Drop the three [?]. **Settled.**
- Minor items, **to listen**; the sense is unaffected in each case:
  - 3:25:16, « associative [?] way »: the captions and Whisper both hear « constant ».
  - 3:10:01, « [form] [?] »: probably « formulate ».
  - 3:43:46, « [duality] [?] »: the captions have « polarity ».
  - 3:06:44, « [associativity] [?] »: the captions have « transitivity ». The statement is true either way, since the zero action is associative.
- Marks: 19 [?] in the groups part, 3 settled, 16 left. Agrees:
  - the bialgebra axioms;
  - ω : B → A ⊗ B (boards 11007–11270);
  - π(t) = t′ + t″ for G_a and π(t) = t′t″ for G_m (boards 11735–11993);
  - the universal point (boards 12382–12640);
  - comodules (boards 13029–13155);
  - left on X = right on B (board 13362).

### _lTf_L0yvrU-18200 (13 June, tape 2, side A)

- **5:38:55**, doubtful mark settled. « End(M) [?] »: M ⊗ A = Hom_k(H, M), so maps M → M ⊗ A are maps H → End_k(M). Drop the [?]. **Settled.**
- **5:31:06**, doubtful mark settled (filler). The captions give « it's a ». **Settled.**
- **5:07:16**, note, no change. « The axioms are the same » for ω and δ_M holds only up to the side swap that he states at once. The transcript is faithful.
- Marks: 5 [?], 2 settled, 3 left. Agrees:
  - δ_M : M → M ⊗ A;
  - the left action (1 ⊗ π)δ = (δ ⊗ 1)δ, checked directly, and the right action through the symmetry (boards 18304–18815);
  - left comodule = right V(A)-module;
  - Hom_k(R, P ⊗ Q) ≅ bilinear maps V(P) × V(Q) → V(R), true in general, since V(R) is represented by Sym R;
  - H = A^∨;
  - the direct-sum case, with H an inverse limit and continuous actions;
  - coalgebras as topological algebras (boards 19072–21055).

### _lTf_L0yvrU-21165 (13 June, tape 2, side B)

- **6:33:01**, wording against the mathematics.
  - Ours: into the « [End] [?] » of M, « [M_n] [?] », and for a group GL_n. The captions sound like Aut(M) and GL_n.
  - Evidence: for a monoid only End(M) ≅ M_n is right, and he says so a moment later (board 23581).
  - Correction: keep End and M_n, and note what the captions hear. **To listen.**
- **6:36:13**, garbled statement (probably his own; changes the mathematics).
  - The exercise asks how the multiplicative monoid can be embedded « into GL_n » (the captions also have « gln »).
  - Evidence: no non-trivial monoid homomorphism (A¹, ·) → GL_n exists. 0 is idempotent and must go to 1, and then everything goes to 1. His point, that the image is not stable under inverses, concerns M_n.
  - Correction: an editorial note « [read: into End(kⁿ) = M_n] ». **Settled** as a note. The name « [O¹] [?] » is to listen.
- **6:26:36–6:27:43**, board item to amend (board 23263). The « resp. » is reversed.
  - Correction: « a closed submonoid of End(M) (resp. a closed subgroup of GL_n) ». **Settled.**
- **6:18:59**, doubtful mark settled: « tricky », from the captions' « trigger ». **Settled.**
- **5:59:15**, to listen (minor). « [equivalence relation] [?] »: the captions have « constellation », probably « congruence relation », which also fits.
- **6:09:11**, note for the listener. The room's remark as supplied (a projective module is a direct sum of countably generated ones) is Kaplansky's theorem. It is sound but unheard, since the captions have nothing usable. **To listen.**
- Marks: 18 [?], 1 settled, 17 left. Agrees:
  - quotient comodules;
  - induced structures on submodules, unique under flatness or a direct-factor hypothesis;
  - subcomodules = H-submodules, the smallest one H·M′;
  - local finiteness, and coalgebras over a field as unions of finite-dimensional subcoalgebras;
  - G = lim Gᵢ of finite type, and G of finite type closed in GL_n (in End for monoids);
  - the antipode argument M + σ(M) (boards 21168–23708).

### _lTf_L0yvrU-23851 (19 June, tape 1, side A; catalogued bad)

- **6:44:17**, symbol.
  - Ours: δ(M) contained in « M ⊗ [A] ». The captions sound like M ⊗ M.
  - Evidence: the subcoalgebra condition π(M′) ⊂ M′ ⊗ M′ stated just before. With [A], the sentence repeats the weaker condition that comes next. In this course the comultiplication is π, and δ is kept for comodules.
  - Correction: « M ⊗ [M] [?] », optionally « [π] » for δ. **To listen.**
- **6:57:42–6:58:46**, symbol.
  - Ours supplies « [M(k′)] » and « [M_k′] » for the monoid. On this side M is the module of finite type, and the monoid is G throughout (6:40:59, 6:43:12, 6:45:20).
  - Correction: « [G(k′)] », « [G_k′] ». **To listen.** The mathematics does not depend on the letter.
- **6:58:46**, garbled statement (in our supplied words). The argument needs two different premises, but ours supplies « [monomorphism] » twice.
  - Correction: « we know that [G_k′ is of finite presentation], and … [the translation] is a [monomorphism] ». **Settled**, since the words are ours.
- **6:59:54**, symbol (doubtful mark replaced). « [O¹] [?] » has no support in the captions. The functor is O under multiplication (O^• on the board), which is M₁. Correction: « [O under multiplication] », drop the [?]. **Settled.**
- **6:59:54**, garbled statement (doubtful marks replaced).
  - Ours: M₁, « which [is the monoid] M_n [?] ». M₁ is M_n for n = 1, not M_n in general.
  - Correction: « which [is] M_n [for n = 1] », drop both [?]. **Settled.**
- **7:05:27**, garbled statement (changes the mathematics).
  - Ours: if a « monomorphism on [?] points », then « surjective ».
  - Evidence: the sentence before defines radicial as injective on field-valued points, « less strong than a monomorphism ». A monomorphic endomorphism of finite presentation is already an isomorphism (6:56:38), so the statement has content only under the weaker hypothesis: a radicial endomorphism is surjective, a statement of Ax–Grothendieck type.
  - Correction: « if [it is injective] on points, then [it] must be surjective ». **To listen.**
- **7:05:27**, missing word. « start [with a finiteness] type property … [an] [?] type conclusion »: the pattern is injectivity giving surjectivity, and the captions do not support « finiteness ».
  - Correction: « [an injectivity] type … [a surjectivity] type conclusion [?] ». **To listen.**
- **Board item t = 25330 (7:02:10, marked uncertain)**, not supported by the lecture.
  - The item gives t ↦ t^p on G_m and says the statement fails for radicial morphisms. The example was put in by the Lean pass (docs/buffalo-corrections.md, Part02).
  - The lecture (7:03:16–7:05:27) gives x ↦ x² on G_m and k[t] → k[s], t ↦ sⁿ, then says that radicial endomorphisms are surjective. It never mentions Frobenius.
  - Proposal: restate the item as the lecture's examples (surjective endomorphisms that are not isomorphisms) plus « a radicial endomorphism is surjective », and move it to about 7:03:16. **To listen.**
- **Doubtful marks settled, to drop (7):** 6:48:40 (twice; board: End(M) ≃ M_n), 6:49:47 (the unit), 6:50:55, 6:52:03 (g′ ↦ x(g′g), evaluated at 1), 7:20:40 (diagonal), 7:21:43 (the symmetry s). **Settled.**
- Marks: 172 [?], 9 settled, 163 left, almost all in noise-damaged sentences. Agrees:
  - the closed embedding into M_n (into GL_n for a group);
  - monomorphic endomorphisms of finite presentation are isomorphisms;
  - Dist(X) = V(A), represented by Sym A, and covariant in X;
  - V(A) × V(B) → V(A ⊗ B), and the universal property of ⊠;
  - X ⊂ Dist(X);
  - algebra on A = coalgebra on V(A).

### _lTf_L0yvrU-26681 (19 June, tape 1, side B; catalogued bad)

- **7:31:42**, formula (changes the mathematics).
  - Ours: « the composition of u ⊗ u and [μ] … is δ of [u] ». The captions have « the composition of u and delta ».
  - Evidence: δ is the transpose of μ (7:30:36), so δ(u) = u ∘ μ, while u ⊠ u is u ⊗ u followed by the multiplication of k′. As we have it, the sentence equates the two sides of the identity being proved.
  - Correction: « the composition of u and [μ] ». **Settled.** Board 7:29:23 is right.
- **Header comment**, formula. The header gives « I² = 0 » for a constant finite group Γ.
  - Evidence: the body (7:54:49, 7:55:53) and the board have I² = I, which is right. k^Γ is a product of copies of k, so the augmentation ideal is generated by an idempotent, and Lie = (I/I²)^∨ = 0.
  - Correction: « I² = I » in the header. **Settled.**
- **7:54:49**, the lecturer's slip, corrected by him. The augmentation of Σ a_γ γ is Σ a_γ, not « the coefficient of the one ». He catches it at once.
  - Correction: none needed; optionally an editorial « [read: the sum of the coefficients] ». **Settled.**
- **7:58:00**, doubtful mark left. « [étale] [?] … [no] internal [infinitesimal structure] »: the captions have « no longer apps ». The bracketed mathematics is right. **To listen.**
- **7:25:53, 7:26:58**, doubtful marks settled: ε : V(A) → O, and the diagonal δ (board 7:24:49). **Settled.**
- Marks: 62 [?], 2 settled, 60 left. Agrees:
  - coassociativity, cocommutativity and counit;
  - X = {x : δ(x) = x ⊠ x, ε(x) = 1};
  - convolution and its unit;
  - G-modules = Dist(G)-modules;
  - the hyperalgebra, Dist = O ⊕ Dist⁺, the bracket and the p-th power map;
  - Dist(Γ_k) = k[Γ];
  - ℤ/2 → μ₂;
  - x^[p] = x for the generator of Lie μ_p.

### _lTf_L0yvrU-28721 (20 June, tape 1, side A)

- **8:29:19**, garbled statement (his slip or a mishearing; changes the mathematics).
  - Ours, with the captions (« aline »): group objects « that are affine, or close to affine ones like constant ones », are reflexive.
  - Evidence: as stated this is false. Over a field of characteristic 0, Hom(G_a, G_m) = 0. Board 30559 was already corrected to diagonalisable and constant ones (docs/buffalo-corrections.md).
  - Correction: an editorial note « [read: diagonalisable (of multiplicative type)] ». **To listen** whether he said « affine ».
- **8:31:29**, bibliography. Mumford's book « published in [India] [?] »; the captions have « Canada ».
  - *Abelian Varieties* appeared in Bombay (Tata Institute and Oxford University Press, 1970), so the supplied word is right in fact.
  - **To listen**; drop the [?] if the audio has India.
- **8:39:02**, doubtful mark settled. « O^× [?] »: O with its multiplication (board 31080). Drop the [?]; a footnote could explain that his × means « times ». **Settled.**
- **8:45:25**, doubtful mark settled. « [closed] [?] subfunctor »: polynomial equations in the coordinates of W(A) define a closed subscheme (board 31525). **Settled.**
- **8:13:10**, note, no change. « If S is affine, it would never be affine » is corrected in the same breath to « affine iff M is finite or S is empty ». The transcript is faithful, and board 29527 is right.
- Marks: 24 [?], 2 settled, 22 left. Agrees:
  - Dist(D(M)) = k^M with the pointwise product;
  - representations = M-graded modules;
  - the constant scheme M_S;
  - D(M) = Hom(M_S, G_m);
  - biduality through open partitions of S;
  - Ext¹(A, G_m) = the dual abelian variety;
  - finite and finite locally free morphisms;
  - D(G) inside W(A), cut out by ε(u) = 1 and π(u) = u ⊗ u (boards 28722–31525).

### _lTf_L0yvrU-31596 (20 June, tape 1, side B)

- **8:47:44**, doubtful mark settled. « by definition [?] »: the captions have it. **Settled.**
- **8:56:25**, to listen (minor). « the unit group, [one] [?], ℤ/p [?] »: the sense is clear. Neglecting nilpotents makes μ_p trivial while ℤ/p stays, so the duality would break.
- Marks: 18 [?], 1 settled, 17 left. Agrees:
  - D(G) = Spec A^∨;
  - Spec H^ab in the non-commutative case;
  - self-duality of the axioms and biduality;
  - μ_n not constant over Spec ℤ;
  - D(μ_p) = ℤ/p;
  - D(α_p) = α_p, while α_{pⁿ} is not self-dual for n > 1 (boards 31598–32249).

### 3ULFIl_2Wis-00000 (27 June, tape 1, side A; catalogued bad)

- **0:23:13**, misheard term. « geometrically [?] connected »: the captions have « geometrically zero connected ». This is his « 0-connected » (connected and non-empty), as in the AG course (51wmmpHand0, 5:43:10) and on 2 July.
  - Correction: « geometrically [0-]connected ». **Settled**; the clause that follows is to listen.
- **0:24:18**, the lecturer's slip, which he corrects himself on 2 July.
  - He says the irreducible analogue goes « exactly the same way ». That is false: Spec ℝ[x, y]/(x² + y²) is irreducible with a rational point but not geometrically irreducible. He notes that a hypothesis is missing (0:31:00–0:33:19) and corrects himself at 05301, 1:28:22. Board 1393 already carries the warning.
  - Correction: at most an editorial « [see the correction of 2 July, 1:28:22] ». **Settled.**
- **0:35:41**, missing word. « locally [noetherian, and] the connected components are all open »: the captions have « locally connected ». The step is locally noetherian ⇒ locally connected ⇒ components open.
  - Correction: « locally [noetherian, hence locally] connected ». **To listen.**
- **0:05:13**, doubtful mark left. « going-up [?] »: plausible from the mathematics, but the captions do not support it. **To listen.**
- **Doubtful marks settled by the mathematics (17 dropped):** 0:14:02 (four marks: A ⊗ B, the projection, flat and of finite presentation, finitely generated subalgebras), 0:15:10 (direct limit), 0:16:16 (inverse limit), 0:17:23, 0:18:30, 0:22:09 (dominating), 0:19:58 (U = p_i⁻¹(U_i)), 0:25:27 (finite Galois), 0:28:46 (quotient), 0:29:50 (stable under Π), 0:41:00, 0:43:18 (twice) and 0:44:23 (set-theoretically). **Settled.**
- Marks: 150 [?], 18 settled, 132 left, most in the lost stretches 0:09:35–0:22:09 and 0:31:00–0:33:19. Agrees:
  - the criteria for geometric connectedness, with the reduction to finite Galois extensions;
  - integral ⇒ universally closed, and flat ⇒ generalisations lift;
  - flat and locally of finite presentation ⇒ open;
  - the limit lemma;
  - Galois descent of open-closed sets;
  - G⁰ open when G is locally of finite type;
  - G⁰_red and G_red subgroups over a perfect field (boards 54–2791).

### 3ULFIl_2Wis-02838 (27 June, tape 1, side B; catalogued bad)

- **0:47:24**, missing word. « just one ideal [?] » for the local ring of a discrete scheme: such a ring has one **prime** ideal.
  - Correction: « one [prime] ideal [?] ». **To listen.**
- **0:54:09**, doubtful mark settled. « finite [étale] [?] over k′ »: A_k′ is a product of finite separable extensions. **Settled.** « [separability] [?] », where the captions have « descendability », stays to listen.
- Marks: 35 [?], 1 settled, 34 left. Agrees:
  - étale over k = sum of spectra of finite separable extensions;
  - X ↦ X(k̄) as an equivalence with continuous Π-sets, and its exactness;
  - étale groups = groups with continuous Π-action;
  - π₀(X/k) and its three characterisations (boards 2844–5148).
- The board writes Π where the transcript writes π, a difference of notation only.

### 3ULFIl_2Wis-05301 (2 July, tape 1, side A)

- **2:08:14–2:09:20**, garbled statement (changes the mathematics).
  - Ours: besides separably closed fields, « maybe the only other example is [the reals] [?], [?] a complete field like this ». The captions have « it is a complete field like this », with no word heard for « the reals ».
  - Evidence: complete fields in general are wrong, since ℚ_p and ℂ((t)) have infinite separable closures. By Artin–Schreier, the fields with 1 < [k_s : k] < ∞ are exactly the real closed ones, of degree 2.
  - Correction: « [a real closed] field like this ». **To listen.** If the audio does have « complete », he means ℝ, and the note should say that the class is real closed fields.
- **1:43:44**, misheard term. « [non-empty] connected », twice: the captions have « zero connected », his « 0-connected ». Correction: « 0-connected » at both places. **Settled.**
- **1:45:58**, missing word. For infinite inverse limits of étale schemes, « not necessarily [the] same [?] ». The point, and the reason he takes only finite limits, is that an infinite limit of étale schemes need not be étale (Spec k_s, 2:08:14).
  - Correction: « not necessarily [étale] [?] ». **To listen.**
- **1:31:42**, doubtful mark settled. « a separable [?] closure ». **Settled.**
- Marks: 19 [?], 1 settled, 18 left. Agrees:
  - the counterexample x² + y² over ℝ;
  - the closed nowhere-dense set Σ, and the corrected theorem with its Galois proof;
  - the dictionary between schemes étale over k and Π-sets;
  - torsors with a geometric point = continuous Π → G;
  - κ(t) as the largest étale subalgebra;
  - π₀ commuting with products, and π₀(G/k) = G/G⁰ (boards 5302–8019).

### 3ULFIl_2Wis-08161 (2 July, tape 1, side B)

- **2:28:18**, misheard term. « not [Hausdorff] [?] » and « very far from [Hausdorff] [?] »: the captions hear « compact » both times. He contrasts quasi-compact schemes with compact spaces in Bourbaki's sense.
  - Correction: « compact » at both places, drop the [?]; optionally add « [in Bourbaki's sense] ». **Settled.**
- **2:16:03–2:22:36**, term to confirm. « [pro-étale] » is supplied every time it occurs. The captions do not give it, and he hesitates over « profinite » (2:17:12) before saying « locally profinite » (2:23:42). Board heading 8163 rests on the supplied word alone.
  - **To listen.** If he says « profinite », board 8163 and the header should follow.
- **2:37:59**, term to confirm. « finite [purely inseparable] [?] extension »: the captions suggest his « radicial ». Both are right mathematically.
  - Correction: « [radicial] [?] ». **To listen.**
- **2:18:18, 2:41:09, 2:34:44**, doubtful marks settled: étale, noetherian, and « over k′ ». **Settled.**
- Marks: 29 [?], 5 settled, 24 left. Agrees:
  - pro-étale affine schemes = Spec of ind-(finite étale) algebras;
  - over a separably closed field, the equivalence with profinite spaces;
  - π₀(X/k) for quasi-compact X;
  - essentially of finite type;
  - the equivalence (a)–(d) for geometric regularity and its proof;
  - smooth = locally of finite type and geometrically regular (boards 8163–10118).

### 3ULFIl_2Wis-10195 (10 July, tape 1, side A)

- **3:29:10**, garbled statement (changes the mathematics).
  - Ours: K ⊗ k′ is a product of fields because it is separable « over k′ », a product of finite extensions « [of] k′ ». The captions have « over K » and « of K ».
  - Evidence: K ⊗_k k′ is finite and reduced over K, hence a product of finite extensions of K. It is not finite over k′ in general.
  - Correction: « over K », « of K ». **Settled.**
- **3:19:27**, symbol. « κ(y) [?] is the ground field »: the captions have « kapa x ». κ(y) is mathematically right, since it is the coefficient field of Â, with κ(x) finite over it.
  - Correction: keep κ(y), and note that the captions hear κ(x). **To listen.**
- **3:18:21, 3:20:33**, doubtful marks settled: Cohen (the coefficient field), and quasi-finite (stated at 3:21:37; board 11710). **Settled.**
- Marks: 50 [?], 2 settled, 1 replaced by a proposal, 47 left. Agrees:
  - geometric regularity and smoothness;
  - the Jacobian criterion and its proof for k perfect;
  - X_sm open, and dense iff reduced with separable residue fields at the generic points;
  - geometric normality;
  - Serre's criterion (boards 10200–13077).

### 3ULFIl_2Wis-13088 (10 July, tape 1, side B)

- **3:53:20**, doubtful mark settled. « theses [?] » (the captions have « Caesars »). **Settled.**
- **3:46:46**, to listen (minor). He calls 0 on the half-line « not singular », faithful to the captions, while the header says the unit « may be singular ». Confirm the wording before keeping the header.
- Marks: 3 [?], 1 settled, 2 left. Agrees: separable ⇔ geometrically normal ⇔ smooth by homogeneity, with the translation in the right direction; G_red a smooth subgroup over a perfect field; connected components = irreducible components. Every board item agrees.

### 3ULFIl_2Wis-14051 (11 July, tape 1, side A)

- **3:54:14**, garbled statement (his abbreviation; changes the mathematics).
  - Ours, with the captions: a group over a field is separable « if and only if it's normal ».
  - Evidence: over an imperfect field this is false, since there are regular, non-smooth forms of G_a. The right condition is geometrically normal, and board 14054 was corrected to it on 7 November.
  - Correction: « [geometrically] normal », or an editorial note. **To listen.**
- **4:30:32**, garbled statement (in our supplied words).
  - Ours: an fpqc epimorphism implies « [faithfully flat] [?], and hence surjective ». The captions have only « surjective », twice.
  - Evidence: he proves flatness right afterwards (4:31:35–4:34:47), which makes sense only if it was not given.
  - Correction: « implies [for one thing] that it's surjective », dropping « [faithfully flat] ». **To listen.**
- **4:29:28, 4:20:49**, doubtful marks settled: « [fpqc] [?] [topology] [?] » (the captions have « Ph compact topology » at 4:30:32), and « g u₀ » (board 15585). **Settled.**
- **4:11:05**, misheard term. « [topological] groups »: the captions have « loops ».
  - Correction: « [Lie] groups [?] », as compared on the next side (4:53:49). **To listen.**
- Marks: 46 [?], 3 settled, 1 replaced, 42 left. Agrees:
  - separatedness, through the inverse image of e under (g, h) ↦ gh⁻¹;
  - π open and faithfully flat for a pseudo-torsor;
  - the properties of UV, and the proof of (b);
  - W stable under G⁰ ⇔ stable under specialisation and generalisation;
  - homogeneous spaces;
  - the lemma on equivariant maps (boards 14054–16871).

### 3ULFIl_2Wis-16934 (11 July, tape 1, side B)

- **4:53:49**, misheard term. « the [one-parameter subgroups] of a torus »: the captions have « jurisics », that is, geodesics. The sense is the same.
  - Correction: « [geodesics] [?] ». **To listen.**
- **5:28:26**, misheard term. « Jacobson or [?] and a few [others] [?] »: the captions have « a few chefs », which may be Shafarevich (Kostrikin–Shafarevich, Cartan-type algebras).
  - Correction: « [Kostrikin] and [Shafarevich] [?] ». **To listen.**
- **5:25:11**, the lecturer's slip, faithfully transcribed.
  - He says the p-Lie algebra determines the infinitesimal neighbourhood « of order p² ».
  - Evidence: G₁ = Ker F is cut out by the p-th powers of the augmentation ideal. It lies between the neighbourhoods of order p − 1 and n(p − 1), so neither p nor p² is right. He settles on « height one », which is correct.
  - Correction: an editorial « [read: the Frobenius neighbourhood G₁] ». Board 19382 (« only the first-order neighbourhood ») understates the point; suggested wording: « determines only G₁ = Ker F ». **Settled.**
- **5:26:15**, the lecturer's statement, outdated in 1973.
  - He says that apart from α_p, μ_p and some small-characteristic exceptions, the simple restricted Lie algebras come from simple algebraic groups. The Witt algebra (Zassenhaus) and the Cartan-type families already contradicted this.
  - Board 19575 was corrected on 7 November to the modern list, so it no longer records what he said.
  - Correction: an editorial note in the transcript. On the board, mark the correction as editorial. **Settled.**
- **5:26:15, 4:53:49, 5:24:04**, doubtful marks settled (four): unipotent (the answer about α_p and μ_p fixes it), quasi-compact (twice), and « in an associative » ring (Jacobson's formula). **Settled.**
- **4:51:40**, doubtful mark left. « in the [fpqc] [?] sense »: the captions have « low », which does not support fpqc. **To listen.**
- Marks: 52 [?], 4 settled, 2 replaced by proposals, 46 left. Agrees:
  - f(G⁰) = H⁰ for f generalising;
  - monomorphisms of groups of finite type are closed immersions;
  - the dévissage (étale, pro-étale, radicial);
  - Chevalley's theorem, with the affine kernel the largest smooth connected affine subgroup;
  - Frobenius kernels of height one ↔ restricted p-Lie algebras, and Jacobson's formula;
  - α_p unipotent, μ_p not (boards 16947–19768).

### 3ULFIl_2Wis-25298 (11 July, tape 3)

- **7:05:51**, symbol. « the [ℤ/p]'s [?] » (the captions have « the zc »). The simple étale commutative pieces are ℤ/ℓ for every prime ℓ, while p is the characteristic on this side. Board 7:06:56 already has ℤ/ℓ.
  - Correction: « [ℤ/ℓ]'s [?], [ℓ prime] ». **To listen.**
- **7:08:11**, missing word (not mathematical). The captions have « top algebra » where ours has « [?] algebra [?] ». Add the variant to the comment. **To listen.**
- Marks: 33 [?], 0 settled, 33 left, 25 of them in the closing exchange (7:07:56–7:11:20). Agrees:
  - complex abelian varieties as ℂⁿ/lattice;
  - smooth connected affine groups as extensions of semisimple groups by the radical;
  - the root-system classification;
  - the radical as torus by unipotent, with unipotent groups successive extensions of G_a over a perfect field;
  - the six commutative simple pieces.

## 3. Sides with nothing to correct

No side is entirely clean. Four come close:

- **_lTf_L0yvrU-18200:** only two [?] to drop. The comodule formulas, and the left action in its corrected form, all check.
- **_lTf_L0yvrU-31596:** one [?] to drop and one minor hearing.
- **3ULFIl_2Wis-13088:** one [?] to drop and one wording to confirm.
- **_lTf_L0yvrU-03729:** three [?] to drop and one board item worded too strongly. The transcript's wording needs no change.

## 4. Counts by kind

| Kind | Items | Settled | To listen |
|---|---|---|---|
| misheard term | 13 | 4 | 9 |
| garbled statement | 13 | 6 | 7 |
| missing statement or word | 8 | 3 | 5 |
| symbol | 5 | 1 | 4 |
| formula, variance or index | 3 | 3 | 0 |
| the lecturer's slip or outdated claim (editorial note) | 2 | 2 | 0 |
| board item to amend | 9 | 8 | 1 |
| **total** | **53** | **27** | **26** |
| doubtful [?] marks settled | 70 (of about 830) | 70 | — |

The settled/to-listen split counts an item as settled only when every part of it is settled. 07948 2:33:35 and 3ULFIl_2Wis-00000 0:23:13 have a settled part and a part still to listen, and are counted as settled. The [?] marks settled by these items (for example 0:23:21, 2:09:35, 2:33:35, 1:43:44, 2:28:18) are included in the 70. A further 6 marks are replaced by proposals that are still to listen (10195 3:19:27, 14051 4:11:05 and 4:30:32, 16934 4:53:49 and 5:28:26, 23851 7:05:27).

When the corrections are applied, the derived files should be refreshed as after the AG check. `npm run buffalo-review` rewrites the git-ignored review file. The boards in `public/buffalo-boards/` change only for the 9 board items, and only with Michel's approval.
