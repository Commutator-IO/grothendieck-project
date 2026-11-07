# Buffalo 1973, algebraic geometry: our transcripts and boards against Gaeta's written notes

**Reference.** *Introduction to Functorial Algebraic Geometry, after a summer course by A. Grothendieck. Vol. I: Affine algebraic geometry*, notes written by Federico Gaeta (SUNY at Buffalo, Department of Mathematics; foreword dated June 1974). The scan is from the Grothendieck Circle (`FuncAlg.pdf`, 168 pages, no text layer). It is kept locally in `archives/funcalg/`, which is git-ignored and never served. Printed page = PDF page − 4. Gaeta says he wrote the notes from tape recordings of the lectures. His own additions are in square brackets, and outside them he often follows the tape sentence by sentence, so the notes serve as an independent hearing of our audio. Vol. II (schemes) was announced but never appeared, so the notes stop at affine schemes.

**Our side.** The local transcripts `transcripts-buffalo/<video>-<start>.en.md` and the published boards `public/buffalo-boards/<video>-<start>.json`. The evidence for each verdict is one of three. *Re-hearing* means the raw captions (`transcripts-buffalo/captions/`) and the Whisper second pass noted in the transcripts. *Board* means the board items (the boards are reconstructions from the transcript, so they are a check on consistency, not an independent witness). *Mathematics* means internal consistency. No audio was listened to again for this check. « To listen » marks the items where only the audio would decide.

**Status.** Applied on 7 November 2026 with Michel's approval; see « Status (7 November 2026) » below. Times are video times (h:mm:ss). Quotations are limited to a few words, and everything else is described.

## Summary

- **Our transcripts, 20 proposed corrections and 3 doubtful marks the notes settle:**
  - misheard term: 10;
  - symbol: 2;
  - missing statement or word: 3;
  - garbled statement: 5;
  - doubtful [?] marks to drop: 3.
- **Our formulas, indices and variances: no disagreement found.** Every formula the lectures state that the notes also give agrees in transcript, board and notes.
- **Boards: no mislabelled item.** Several board items confirm the right form where the notes are wrong.
- **The notes wrong and the recording right: 21 places.**
  - 9 are in passages that follow the lectures.
  - 12 are slips in Gaeta's own interpolations, or in passages the lecture does not cover.
  - They are listed so that nobody corrects our text towards them.
- **Sessions with no counterpart in the notes:** everything from 13 June 1973, 3:30:02 (thSz9ZHDK9o) onwards. That is 18, 19, 20, 25 and 26 June and 2, 3, 9, 10 and 11 July: schemes in general, projective space, morphisms, descent, topologies. Several affine-level stretches of the recorded sessions are also absent from the notes (see the last section).
- **Notes with no AG recording:**
  - Ch. 0 (Gaeta's introduction).
  - The Ch. I §0 « survival talk » exchange.
  - Ch. I §1–§2, §12 and §14.
  - Ch. II §2–§3 (from SGA 4).
  - Ch. III §7 (FAC sheaves) and §12 (examples).
  - The §14 appendix, which is from the **topos** course (4 April 1973), not from this one.

## Status (7 November 2026)

Michel approved the corrections of section 2 on 7 November 2026, and all 23 items were applied to the local transcripts (20 corrections and 3 doubtful marks dropped, 26 edits in 10 files). Each changed file has a « Third pass, 2026-11-07 » line in its header comment. Nothing was skipped: every passage was found at its timestamp. The « notes error » items needed no change, and the Whisper comments were kept except where the item says to drop them (6:44:16).

- **Applied as settled, no [?]:** 51wmmpHand0 0:20:45 (cube), 1:40:03 (imaginary quadric), 1:46:34 (« [here: surjective] » added after the word, rather than a footnote), 2:12:08 and 2:13:13 (V″_J at all three places), 2:29:35 (Dieudonné), 5:27:00 (« [not] too reasonable »), 6:48:38 (editorial note); _lTf_L0yvrU 4:20:41 (the data Ã and M̃); thSz9ZHDK9o 2:33:14 (« for the presheaves »).
- **Doubtful marks dropped:** 51wmmpHand0 6:44:16 (union, with the Whisper variant); _lTf_L0yvrU 4:20:41 (the book with Dieudonné); thSz9ZHDK9o 2:15:59 (finite presentation).
- **Applied but still to listen (the [?] kept or added):**
  - 51wmmpHand0: 0:22:51 (ordinary integers), 2:07:43 (Zorn's lemma), 2:31:41 (the ring A), 3:11:46 (tensor product; the captions' « direct » noted in the comment), 3:49:41 (closed embedding), 6:16:15 (result of Krull), 6:26:07 (Krull's theorem), 6:31:25 (editorial note on « empty »), 6:34:36 (« [union] » after « sum », both places);
  - _lTf_L0yvrU: 4:14:30 (unit element to unit element), 4:20:41 (associated sheaf).
- **Boards:** none flagged; no file in `public/buffalo-boards/` was changed.
- **Derived files:** `npm run buffalo-index` reads the `.tex` indexes, not the transcripts, so it was not rerun. `npm run buffalo-review` was rerun; it writes only the git-ignored review file, and `git status` shows no public change.

## 1. Mapping: notes → recordings

| Notes (printed pp.) | Content | Recording (file key) | Video time | Date |
|---|---|---|---|---|
| Ch. 0 §0, §2 (4–11) | Propaganda for applied mathematicians; summary of vol. I (Gaeta's) | none | — | — |
| Ch. 0 §1 (6) | Prerequisites | 51wmmpHand0-00000 | 0:02:23–0:10:57 | 29 May |
| Ch. I §0 (11–12) | Summary, « survival talk » exchange | none | — | — |
| Ch. I §1 (12–19) | Representable functors, S/C, C/S (recall from the topos and group courses) | only a reminder at 51wmmpHand0-02680 | 1:09:48 | 29 May |
| Ch. I §2 (19–21) | The category of k-algebras | 51wmmpHand0-00000 (convention only) | 0:10:57–0:12:01 | 29 May |
| Ch. I §3–§4 (21–25) | Points of k′^I = homomorphisms P_I → k′; solution sets | 51wmmpHand0-00000 | 0:12:01–0:25:00 | 29 May |
| Ch. I §5–§6 (25–29) | The functor V_S, E^I; intrinsic study, embedding | 51wmmpHand0-00000; recap 51wmmpHand0-05671 | 0:25:00–0:33:56; 1:34:36–1:41:05 | 29–30 May |
| Ch. I §7 (30–33) | Reduction to an ideal, J ↔ V_J | 51wmmpHand0-00000, -02680; -05671 | 0:33:56–0:48:09; 1:47:38–1:54:06 | 29–30 May |
| Ch. I §8 (33–37) | The category Aff_k | 51wmmpHand0-02680; -05671 | 0:48:09–1:33:36; 1:42:09–1:56:14 | 29–30 May |
| Ch. I §9–§10 (37–40) | Field-valued points, radicals | 51wmmpHand0-05671, -07660 | 1:56:14–2:09:50 | 30 May |
| Ch. I §11 (41–44) | Classical case, Nullstellensatz | 51wmmpHand0-07660 | 2:09:50–2:26:23 | 30 May |
| Ch. I §12 (44–45) | Equivalence classes of points, geometric points | none on 29–30 May; nearest is 51wmmpHand0-20588 | 6:02:03–6:08:43 | 5 June |
| Ch. I §13 (45–47) | Criticisms of nilpotent elements | 51wmmpHand0-07660 | 2:26:23–2:32:54 | 30 May |
| Ch. I §14 (47–48) | Classical Zariski topology on k^n | none (the lecture's Zariski topology is on Spec, 5 June) | — | — |
| Ch. II §0 (49–50) | Summary: two directions | 51wmmpHand0-09650 | 2:50:14–2:55:36 | 30 May |
| Ch. II §1 (50–61) | Products, kernels, fibre products | 51wmmpHand0-09650; -11235 | 2:56:43–2:59:58; 3:16:18–3:44:19 | 30 May, 4 June |
| Ch. II §2 (61–67) | Reduction of inverse limits (from SGA 4) | one sentence at 51wmmpHand0-11235 | 3:09:31–3:10:36, 3:16:18 | 4 June |
| Ch. II §3 (67–69) | Direct limits, amalgamated sums | 51wmmpHand0-09650; -14177 | 2:58:52–2:59:58; 4:37:38–4:38:43 | 30 May, 4 June |
| Ch. II §4 (70–73) | Categorical generalities on Aff | 51wmmpHand0-09650; -11235 | 2:52:25; 3:07:21–3:10:36 | 30 May, 4 June |
| Ch. II §5 (73–74) | Recovery of A as Hom(X, E¹) | 51wmmpHand0-07660, -09650; recap -17719 | 2:33:56–2:49:03; 5:15:01–5:17:11 | 30 May, 5 June |
| Ch. II §6 (74–78) | Fibre products and kernels in Aff_k | 51wmmpHand0-09650; -11235; recap -17719 | 3:00:04–3:06:22; 3:11:46–3:52:03; 5:24:51–5:25:57 | 30 May–5 June |
| Ch. II §7 (78–80) | Filtered inverse limits, Noetherian rings | 51wmmpHand0-14177 | 3:58:28–4:11:21 | 4 June |
| Ch. II §8 (80–85) | Direct limits in Aff, finite sums, connectedness | 51wmmpHand0-14177; -17719; -20588 | 4:33:21–4:36:34; 5:27:00–5:56:40 | 4–5 June |
| Ch. III §0 (85–87) | Summary: the sheaf is needed to recover A | 51wmmpHand0-29285; _lTf_L0yvrU-10808 | 8:08:07–8:09:12; 3:45:53–3:47:24 | 6, 11 June |
| Ch. III §1 (88–89) | Loci, the spectrum | 51wmmpHand0-20588; recaps -23482, -29285 | 6:00:59–6:11:57; 6:39:56–6:48:38; 8:22:06–8:23:12 | 5, 6, 11 June |
| Ch. III §2 (89–95) | Spectral topology | 51wmmpHand0-20588; -23482; -29285 | 6:11:57–6:30:22; 6:42:06–6:56:12; 8:23:12–8:25:23 | 5, 6, 11 June |
| Ch. III §3 (95–101) | Canonical basis X_f; sheaves given on the basis | 51wmmpHand0-32167; _lTf_L0yvrU-13644 | 8:54:32–8:58:26; 3:47:26–4:00:27 | 11 June |
| Ch. III §4 (101–103) | The functor Spec | 51wmmpHand0-29285, -32167 | 8:40:28–8:49:15; 8:59:31–9:00:35 | 11 June |
| Ch. III §5 (103–112) | Irreducibility, generic points, sober spaces, components, noetherian spaces | 51wmmpHand0-20588, -23482, -26373; recap -29285 | 6:29:17–6:37:44; 6:48:38–7:45:56; 8:24:18–8:29:40 | 5, 6, 11 June |
| Ch. III §6 (112–114) | Introduction to Part II | 51wmmpHand0-29285; _lTf_L0yvrU-10808 | 8:08:07–8:09:12; 3:45:53–3:47:24 | 6, 11 June |
| Ch. III §7 (115–121) | Sheaves after FAC; ringed and locally ringed spaces | FAC part none; thSz9ZHDK9o-05786, -08735 | 2:07:11; 2:48:18–2:59:33 | 12, 13 June |
| Ch. III §8 (122–133) | M_f, A_f, fractions, local rings | _lTf_L0yvrU-13644; thSz9ZHDK9o-05786 | 4:00:27–4:20:41; 1:41:57–2:07:11, recap 2:17:07–2:19:20 | 11–13 June |
| Ch. III §9 (133–137) | The presheaves Ã, M̃ are sheaves | _lTf_L0yvrU-13644 → -16477 | 4:20:41–4:44:12 | 11 June |
| Ch. III §10 (137–142) | Spec A as a locally ringed space; Hom(A,B) = Hom_loc | thSz9ZHDK9o-02870; -08735; -11692 | 0:55:41–1:01:00; 2:27:54–2:59:33; 3:14:56–3:30:02 | 12–13 June |
| Ch. III §11 (142–144) | Recovery of the ground ring k | thSz9ZHDK9o-11692 | 3:30:02–3:34:15 | 13 June |
| Ch. III §12 (144–145) | Examples; nilpotents again | none | — | — |
| Ch. III §13 (145–147) | Quasi-coherent sheaves, M ↦ M̃ | thSz9ZHDK9o-02870; -05786 | 1:01:00–1:20:41; 2:09:32–2:16:00 | 12–13 June |
| Ch. III §14 (147–162) | Appendix: sheaves of sets, étale spaces | **topos course**, URU5jgTvjhU-0000 → -02951 | 0:00:11–c. 1:12:00 | 4 April |

Recorded AG sides with no counterpart in the notes: 51wmmpHand0-29399 (11 June, group objects and Hopf algebras; the notes refer to the algebraic-groups course), 51wmmpHand0-35114 (11 June, descent and Čech cohomology), and every side from thSz9ZHDK9o-11692 3:34:15 onwards. That last group includes the AG sides filed on 3ULFIl_2Wis (-19834, -22716, 11 July).

## 2. Discrepancies, by session

Each item gives the kind, what our side has against what the notes have, which is likelier right and why, and the proposed correction. « Notes error » items need no change on our side.

### 51wmmpHand0-00000 (29 May, tape 1, side A)

- **0:20:45**, misheard term. Ours counts solutions in a « ball of size [R] » as [R] grows, with [?]. The notes (p. 24) count solutions in a cube centred at the origin as its side grows. The captions and Whisper both hear « cube » and « sides ». **Notes right.** Correction: « a big cube, as the sides are going to increase », and drop [R] and [?].
- **0:22:51**, misheard term. Ours has « [p-adic] integers [?] ». The notes have only the ring of integers, the captions « ordinal integers » and Whisper « ordinary integers ». No source has p-adic. Correction: « [ordinary] integers [?] » (to listen).

### 51wmmpHand0-02680 (29 May, tape 1, side B)

- **1:22:50–1:33:36**, notes error. The notes (p. 36) state that a morphism of affine algebraic spaces, drawn as an inclusion, is injective if and only if the ring map A → A′ is surjective. The lecture says injectivity on points for every k′ is a ring epimorphism, and that surjectivity suffices but is not necessary. It gives K[T] → K[T,T⁻¹] as the counterexample, and boards 4970, 5033, 5353 and 5486 have this correctly. The notes leave out the counterexample. Their statement is true only for closed embeddings. **Recording right.**

### 51wmmpHand0-05671 (30 May, tape 1, side A)

- **1:40:03**, misheard term. Ours has « a quadric [?] ». The notes (p. 28) have an imaginary quadric, the sum of squares plus one, and the captions « an i quad ». **Notes right.** Correction: « an imaginary quadric ».
- **1:40:03**, notes error. The notes (p. 26) give x² + y² = 0 as a real curve with no real point, but (0,0) is one. Ours, the captions and board 5943 have x² + y² + 1 = 0, as do the notes themselves on p. 28. **Recording right.**
- **1:46:34**, garbled statement (terminology). Ours says P_I → A is an « epi[morphism] », meaning A is a quotient of P_I. The notes (p. 35) have the same wording. For ring epimorphisms this is false, and it contradicts the lecture at 1:22:50, so he says « epi » here for a surjection. Board 6331 already has « surjective ». Correction: add « [here: surjective] » after the word, or a footnote pointing to 1:22:50.

### 51wmmpHand0-07660 (30 May, tape 1, side B)

- **2:07:43**, missing statement. Ours says Krull's theorem follows immediately from something inaudible in the captions. The notes (p. 40) say it needs Zorn's lemma (the axiom of choice), and the mathematics agrees. Correction: « [of Zorn's lemma] [?] » (to listen). The notes also add a proof by localisation that the lecture explicitly declines to give.
- **2:12:08, 2:13:13**, symbol. Ours writes V^c_J three times, where at 2:11:01 it has V″_J. The captions read « VC lower J » and « my second lower J ». The notes ((11.1)–(11.2)) and board 7861 have V″_J. « V second » was misread as « V c ». Correction: V″_J at all three places.
- **2:29:35**, missing statement. Ours says Kähler was the first, then that someone inaudible in the captions started writing « our treatise » in this spirit. The captions have « you don't I ». The notes (p. 45, quoting him) have Dieudonné and himself. **Notes right**, and the captions are a mishearing of « Dieudonné and I ». Correction: « and Dieudonné and I started writing our treatise ».
- **2:31:41**, missing word. Ours has valuable information concerning something inaudible in the captions, and the captions have « the name ». The notes (p. 45) have the ring A. Correction: « the [ring A] [?] » (to listen).

### 51wmmpHand0-09650 (30 May, tape 2)

- **2:52:25**, notes error. The lecturer first says « isomorphic », then corrects himself to « equivalent » (Aff ≃ opposite of k-algebras). The notes (p. 71) state a bijection on objects and an isomorphism. Aff is the category of representable functors, so A ↦ h^A is essentially surjective, not bijective on objects. **Recording right.** Board 10345 has ≃. The notes repeat « isomorphic » on p. 113.

### 51wmmpHand0-11235 (4 June, tape 1, side A)

- **3:11:46**, misheard term or oral slip, wrong mathematics as it stands. Ours calls the sum of the algebras Aᵢ « the direct product [?] ». The captions have « direct » and Whisper « light ». The notes ((6.1)) and our own next sentence say tensor product. The coproduct of commutative k-algebras is ⊗_k Aᵢ, while the direct product represents the *sum* of the affine spaces (Ch. II §8). Correction: « the [tensor] product [?] », with a note that the captions hear « direct » (to listen: possibly his slip). Board 11506 already has ⊗.
- **3:49:41**, garbled statement (minor). Ours has a « nice [?] embedding » for the kernel. The construction gives K = V_{A/I}, a closed embedding, as in the notes (pp. 77–78). Correction: « a [closed] embedding [?] » (to listen).

### 51wmmpHand0-14177 (4 June, tape 1, side B)

- **4:01:40**, notes error. The lecture says that two finitely generated subalgebras generate together a finitely generated subalgebra. The notes (p. 78) say their « union » is finitely generated, but a union of two subalgebras is in general not a subalgebra. **Recording right**, as is board 14500.

### 51wmmpHand0-17719 (5 June, tape 1, side A)

- **5:27:00**, misheard term (sense unchanged). Ours says direct limits in Aff are « [un]reasonable [?] ». The captions and Whisper hear « too reasonable », and the notes (pp. 70, 80–81) have « not too reasonable ». **Notes right.** Correction: « [not] too reasonable », and drop [?].
- **5:35:44–5:55:37**, notes error. The notes (p. 83) say the map from the disjoint union of the Xᵢ(Z) to X(Z) is bijective if and only if Z is connected. That is false for Z empty (K′ = 0), and the converse needs the Xᵢ non-empty and at least two of them. The lecturer sharpens it to 0-connected (connected and not initial) and gives the K′ = 0 counterexample. **Recording right**, as are boards 20850, 20914 and 21173.

### 51wmmpHand0-20588 (5 June, tape 1, side B)

- **6:16:15**, misheard term. Ours invokes the fact that a radical is the intersection of the primes containing it « by the [rule] [?] » recalled earlier. The captions have « by the pool », Whisper « sum of cool ». The notes ((2.7)) state the same fact, and elsewhere the lecturer names Krull for these results (6:34:36, 7:26:02). Correction: « by the [result of Krull] [?] » (to listen).
- **6:26:07**, misheard term. In the quasi-compactness proof, ours has « by rule seven », a theorem that every non-zero ring has a maximal ideal. The notes call it Krull's theorem, and the lecturer names Krull for it at 6:34:36, 6:49:42 and 7:26:02. Correction: « by [Krull's theorem] [?] » (to listen). Board 23167 names no one.

### 51wmmpHand0-23482 (5 June, tape 2; 6 June from 6:38:20)

- **6:31:25**, garbled statement (probable slip, to listen). The side opens mid-sentence on irreducibility: of two closed sets covering X, one should be « empty ». For closed sets this is false (X = X ∪ X). The notes ((5.1)) and board 23485 say one of them equals X, so it is probably the same slip as at 6:48:38. Correction: an editorial note « [read: one of them equals X; « empty » holds for the open complements] ».
- **6:34:36**, wrong word that changes the mathematics. Twice in this paragraph ours says X is written as a « sum » of two closed subspaces, with the sum corresponding to the product J′J″. In this course « sum » is the disjoint sum, and a decomposition into a sum of two closed sets is the connectedness criterion of 5:36:48. The notes (p. 106, X = X′ ∪ X″ and V(J′J″)), board 23738 and the mathematics all require union. Correction: « [union] » in both places, kept after « sum » if the audio has « sum » (to listen).
- **6:44:16**, doubtful mark settled. Ours has « union [?] », while Whisper has « intersection ». The notes ((2.9)), board 24256 and the mathematics (∪ V(Jᵢ) = V(∏ Jᵢ)) give union. Correction: drop the [?] and the Whisper variant.
- **6:48:38**, garbled statement (the lecturer's slip, half-corrected). Ours, faithful to the captions, says one of X′, X″ should be « empty », or « what is the same », equal to X. The two are not the same for closed sets. The second form is the definition (notes (5.1), board 23485). Correction: after « empty », add « [read: the complement of X′ or of X″ should be empty] ».

### _lTf_L0yvrU-13644 (11 June, filed with the group-scheme videos)

- **4:14:30**, garbled statement (minor). Ours says ring homomorphisms are supposed to take « [units into units] [?] ». The convention he recalls is that the unit element goes to the unit element. Taking units to units holds for every homomorphism and is no convention. Correction: « [the unit element into the unit element] [?] » (to listen).
- **4:20:41**, misheard term, the most serious item in this side. Ours says he could take the « same sheaf » and be happy, as in the book with Dieudonné. The notes (p. 133, outside brackets, near-verbatim from the tape) say the **associated** sheaf: one could sheafify, but he wants to prove directly that the presheaf is a sheaf. Only that reading makes sense. Correction: « take the associated sheaf and be happy » (to listen, to confirm).
- **4:20:41**, symbol. Ours has « the data A and B ». No ring B exists at that point: the data are the presheaves just built on the X_f, as in the notes (p. 133). Correction: « the data Ã and M̃ ».
- **4:20:41**, doubtful mark settled. The notes name Dieudonné (EGA I) for « the book with Dieudonné [?] ». Correction: drop the [?].
- **3:52:56**, notes error ((3.8), p. 97). The notes say X_f ⊂ X_g gives gⁿ = hf. The divisibility is reversed: X_f ⊂ X_g means V(g) ⊂ V(f), so f ∈ √(gA) and fⁿ = gh. Take f = 0, g = 1: X_f = ∅ ⊂ X_g, yet no power of 1 is a multiple of 0. The equality criterion also prints « A_g » for gA. Ours (« fⁿ is equal to gh »), board 13910 and index 13976 are **right**. The notes' own (3.14) uses the correct form.

### _lTf_L0yvrU-16477 (11 June)

- **4:37:51**, notes error. The notes ((9.6)′) say the proof reduces to the case m = 1. The reduction is to m = 0, as ours and board items 16609–16925 have it. **Recording right.**

### thSz9ZHDK9o-05786 (12 June; 13 June from 2:09:32)

- **2:14:53**, notes error. The notes (p. 147) build the counterexample to Hom commuting with ~ on the product A^I. They also print the arrow without the tilde on the left, which contradicts the full faithfulness stated a page earlier. Ours uses the direct sum A^(I), so that Hom(A^(I), N) = N^I reduces to the failure for products. **Recording right.** Board 7837 needs nothing.
- **2:15:59**, doubtful mark settled. The notes (p. 147) have finite presentation as the right assumption. Correction: drop the [?] after « [finite presentation] ».

### thSz9ZHDK9o-08735 (13 June)

- **2:33:14**, misheard term. Ours: to define O_Y → φ_*O_X, he needs to define it only on « the [basic open sets] [?] ». Whisper and the notes (p. 139) independently have « only for the presheaves » (f ↦ A_f on the basis). The sense is the same, but the wording is settled. Correction: « only for the presheaves ». Board 9194 is unaffected.
- **2:31:07**, notes error. The notes ((10.8)) place u⁻¹(𝔭) in X, but it lies in Y = Spec A, as ours has it. **Recording right.**

### Other sides with shared material and no disagreement

- 51wmmpHand0-26373, -29285 and -32167: minimal closed irreducible sets, noetherian induction, Spec u and its continuity, φ⁻¹(Y_f) = X_{u(f)} (board 32371 = notes (4.5)–(4.6)).
- thSz9ZHDK9o-02870: boards 3728–4903 = notes (13.1)–(13.3).
- thSz9ZHDK9o-11692: the notes state (10.16) without proof.

## 3. Errors in the notes, with no counterpart on our side

These are slips in Gaeta's bracketed interpolations or in passages the lecture does not cover. They are listed so that nobody corrects our text towards them.

- **p. 59:** the fibre product is written as a kernel over S × S with (f×f)∘p, (g×g)∘q. It should be the kernel of f∘p, g∘q into S. The same page has « finite products and finite products » for « and fibre products ».
- **p. 61, footnote 4:** left and right adjoint are swapped. The text above it, and board 12487, are right.
- **p. 69:** the union of two subsets of S is called a sum in S/C. It is the amalgamated sum over their intersection.
- **p. 82:** Xᵢ(k′) → X(k) is printed for X(k′).
- **p. 103, (4.4):** the preimage of the canonical basis is stated to be the canonical basis. Only inclusion holds (for k → k[T], the basis {∅, Y} pulls back to {∅, X}). The lecture states only φ⁻¹(Y_f) = X_{u(f)}.
- **p. 105:** « sober » is defined with irreducible subsets, not closed irreducible ones. Under that definition no spectrum is sober: the closed points of Spec ℤ form an irreducible set with no generic point. The lecture says « closed » each time (6:29:17, 7:00:33, 8:24:18; boards 23357 and 25035).
- **p. 107:** every space is called the irredundant union of its components, uniquely. This holds for sober spaces such as Spec A; the lecture (7:04:58) claims only the union.
- **p. 113:** A_f is called the largest homomorphic image of A in which f is invertible. It is the universal A-algebra inverting f, not a quotient (ℤ → ℤ[1/2]). The lecture states this correctly at _lTf_L0yvrU 4:13:26.
- **§8, pp. 127–131:** S₀ = {0} should be {0, 1}, and the double saturation should equal S̄, not S.
- **§13:** the references (12.2) and (12.4) mean (13.2) and (13.4).

## 4. Content on one side only

**In the notes, not in our AG recordings:**
- Ch. 0 §0 and §2: applied mathematics, Klein, manifolds as locally ringed spaces, and a summary of vol. I. All of this is Gaeta's.
- Ch. I §0: the « survival talk » question-and-answer (Enriques' title, whether a high-school graduate could understand an affine scheme). It is not on our tapes.
- Ch. I §1–§2: representable functors, Yoneda, S/C and C/S, and k-algebras as ℤ-algebras. Gaeta recalls these from the topos and group courses.
- Ch. I §12: equivalence classes of points with values in arbitrary k′. This is compatible with the field-valued version of 5 June.
- Ch. I §14: the classical Zariski topology on kⁿ.
- Ch. II:
  - the §1 set-theoretic review;
  - §2, abstract diagrams and the reduction theorem (2.10), taken from SGA 4 I;
  - §3, amalgamated sums.
- Ch. III:
  - Max A not functorial (ℤ ⊂ ℚ);
  - the T₀/T₁/T₂ footnotes;
  - the §5 examples (complex curves and surfaces, the local ring, generic points in history);
  - all of §7 after FAC (étalé spaces, the canonical presheaf, the sheafification adjunction);
  - the §8 fraction calculus for arbitrary multiplicative sets;
  - most of §11 (Sch, Sch*);
  - all of §12 (stalks of Spec ℤ, the nilpotent « paradox »).
- The §14 appendix belongs to the topos course (URU5jgTvjhU, 4 April 1973). No gross disagreement was found there. The notes (pp. 161–162) contain what our captions lose at URU5jgTvjhU-02951 1:05:06–1:12:14: the n sheets of x ↦ xⁿ away from 0, 0 as a ramification point, dominant morphisms of curves, and the universal covering. That gap could be filled in summary from them, or by listening.

**In our recordings, not in the notes (affine-level material):**
- 29–30 May:
  - the opening on the order of the two courses;
  - the monomorphism V_A → E^I that is not a closed embedding, and the epimorphism K[T] → K[T,T⁻¹] (1:20:37–1:33:36);
  - the questions at 1:00:53 and 1:21:44;
  - the choice offered at 1:33:36;
  - the meaning of « Nullstellensatz » (2:32:54).
- 4 June:
  - the Nullstellensatz question (3:53:03);
  - coarse and fine aspects of the functorial view (3:56:19);
  - kernels of homomorphisms of affine groups, A/B⁺A, stabilisers, intersections of subobjects (4:12:35–4:32:17);
  - the cokernel as an equaliser subalgebra, H × G ⇉ G, GL_n/B collapsing to a point in Aff (4:36:34 to the end of 51wmmpHand0-17078).
- 5 June:
  - questions from the room (4:56:31–5:24:51), including closed subspaces ↔ all ideals, and the flatness test through the dual numbers D_K(N) with Nagata's idealisation, which is nowhere in the notes;
  - 0-connectedness and the bijectivity theorem (5:43:10–5:56:40).
- 6 June:
  - the old use of « minimal prime » (7:09:13);
  - comparison with X(ℂ) and its connectedness (7:11:23);
  - minimal closed irreducible sets = closed points (7:19:36);
  - noetherian ⇔ every open set quasi-compact (7:27:06);
  - a non-noetherian ring with noetherian spectrum (7:42:27);
  - very dense subsets and the recovery of X from its closed points (7:45:56–8:08:07).
- 11 June:
  - questions on group objects, Hopf algebras and the antipode (8:10:17–8:22:06);
  - the criterion for noetherian spaces (8:27:31);
  - connected components through chains of irreducible components (8:32:52);
  - Spec A_f → Spec A an open embedding, and A → A_f an epimorphism (8:49:15, 9:00:35);
  - Spec of a finite product is a topological sum (9:04:59);
  - Spec(A ⊗_K B) against the fibre product of spectra, with the plane example (9:10:51–9:45:14);
  - faithfully flat descent, the Čech complex, acyclicity of M̃, flat and finitely presented = locally free (51wmmpHand0-35114; _lTf_L0yvrU-16477 4:45:15–5:03:20);
  - Spec turning tensor products into fibre products of locally ringed spaces (_lTf_L0yvrU 3:45:53).
- 12 June:
  - ~ commuting with direct limits (1:02:08);
  - M̃ = M ⊗_A O_X as an inverse image (1:11:48);
  - the proof of full faithfulness (1:13:56);
  - quasi-coherent ⇔ ≃ M̃, proved by descent, with the vocabulary of descent (1:17:15–1:36:26).
- 13 June:
  - (A^I)_f against (A_f)^I (2:13:48);
  - descent along A → Â (2:19:20);
  - O_X local through Σfᵢ = 1 (2:27:54);
  - direct image = restriction of scalars, inverse image = extension of scalars (2:37:29);
  - φ⁻¹(Y_f) = X_{φ*f} characterising local morphisms (2:56:11);
  - the mistaken first proof, the counterexample Spec K → Spec V for a DVR V, and the repaired proof that local morphisms between spectra come from ring homomorphisms (3:14:56–3:30:02);
  - schemes and k-schemes as functors (from 3:30:02).

**Sessions with no counterpart at all.** The notes stop at affine schemes, so none of the following has a counterpart. The topics are from the index.
- 18 June: morphisms into an affine scheme, schemes as Zariski sheaves, epimorphisms and open immersions of sheaves, representability, gluing, projective space, invertible modules and P(V).
- 19 June: limits of Zariski sheaves, projective bundles, the universal quotient, P as a quotient by G_m.
- 20 June: base change, relative Spec and affine morphisms, fibre products of schemes, Grassmannians, flags.
- 25 June: local, noetherian and artinian schemes; finiteness conditions; immersions; DVRs; reduced, integral, normal and regular schemes.
- 26 June: separated, quasi-separated and coherent morphisms; geometric properties; subschemes.
- 2 July: finite presentation and limits; projective, ample, quasi-projective and proper morphisms; valuative criteria; integral and finite morphisms.
- 3 July: ample sheaves; quasi-affine, radicial, open and flat morphisms.
- 9–10 July: flatness criteria; faithfully flat descent of properties, modules, subobjects, morphisms and affine schemes; Chevalley's theorem; effective descent; group actions.
- 11 July (3ULFIl_2Wis-19834, -22716): descent for families, the fpqc, fppf and étale topologies, quotients and algebraic spaces.
