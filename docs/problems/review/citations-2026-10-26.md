# Open-problems paper — citation verification (2026-10-26)

Scope: `docs/problems/article.tex` at HEAD `42f4c72`, 30 bibliography items plus the names cited without an item. Read-only review; nothing in the article was edited.

Method (skill `citation-verification`): metadata against Crossref, arXiv API, zbMATH API, numdam, SMF and publisher pages; claims checked in the full texts where open (arXiv PDFs, numdam scans, Milne's ADT PDF, Orgogozo's retyped SGA 4 X, Illusie's homepage, MPG PuRe preprint of Pop). Three checking passes in parallel; web search was not available to them, so a « not found » below means not found in the sources opened. ScienceDirect, Project Euclid and the Oxford books were closed to them.

## 1. Totals

| Status | Count |
|---|---|
| Metadata confirmed, entry complete | 9 |
| Metadata confirmed, entry incomplete (pages, volume, issue, subtitle, journal version) | 15 |
| Metadata wrong | 2 (`friedmanlaza` no title; `pop2019` no volume, short title) |
| Not a publication as cited | 1 (`illusie2023`: talk notes) |
| SGA 4 authors are editors | 1 |
| Claim confirmed | 15 |
| Claim wrong or misattributed | 10 (§ 3) |
| Claim not checkable (no access) | 6 (Kleiman Th. 2.13; Durfee's E₁ formula and scope; Kock–Moerdijk 1992 and 1996; Baues Rem. 1.5.5; Bose–Everett–Wismath; Grünbaum ch. 3) |

## 2. Findings that change a problem

1. **Problem 4 is answered, in part, by Breen 1975.** L. Breen, « Un théorème d'annulation pour certains Ext^i de faisceaux abéliens », Ann. Sci. ÉNS (4) 8 (1975), 339–352, doi:10.24033/asens.1291. For $G$ finite flat commutative and $H$ smooth commutative quasi-projective, with residue characteristics $\ge p$ and multiplication by every prime $q < p$ an automorphism of $G$, $\mathcal Ext^i(G, H) = 0$ for $1 < i < 2p-2$ (étale-sheafified); Remarque 3°: $\mathcal Ext^{2p-2}(\alpha_p, H) \ne 0$ in characteristic $p$ for $H = \mathbb G_a, \mathbb G_m$. With $p = 3$ (2 invertible) this gives $\mathcal Ext^2(G, H) = 0$ for smooth $H$, hence for vector bundles, and $\mathcal Ext^2(\alpha_2, \mathbb G_a) \ne 0$, which supports the reading « si 2 inv. ». The paper's « first test » ($\alpha_p$, $\mathbb G_a$, $p$ odd) is settled: zero. What stays open is arbitrary quasi-coherent $M$ and the fppf (not étale-sheafified) version. Breen 1978, cited now, is the wrong paper: it computes Ext of $\mathbb G_a$ in sheaves of $\mathbb F_p$-vector spaces and does not treat $\alpha_p$.
2. **Problem 12: Pop's tripod variants need dimension > 1.** Pop, Invent. Math. 216 (2019): the categories $\mathcal V_X$ are built from varieties $X$ with finitely many dominant rational maps to the tripod, and Hypothesis (H) requires $\dim X > 1$. So « tripod variants for finite étale covers of $\mathbb P^1 \smallsetminus \{0,1,\infty\}$ » is wrong, and Pop does not by himself cover the covers of one curve, which makes the single-curve question more clearly open. The preprint is public (MPG PuRe), so « could not be read » should go.
3. **§ 7 (pseudoline proof): Melchior and Grünbaum do not support « valid for pseudolines ».** Melchior treats lines; Felsner–Goodman cite him only for simplicial arrangements; Kelly–Rottenberg's introduction says Grünbaum *asked* whether pseudoline arrangements have a simple point. Cite instead: L. M. Kelly, R. Rottenberg, « Simple points in pseudoline arrangements », Pacific J. Math. 40 (1972), 617–622, doi:10.2140/pjm.1972.40.617, Th. 3.6 (at least $3n/7$ simple points if not a near-pencil); and J. Bokowski, P. Pokora, « On the Sylvester–Gallai and the orchard problem for pseudoline arrangements », Period. Math. Hungar. 77 (2018), 164–174, doi:10.1007/s10998-017-0224-x, Th. 1.3 ($t_2 \ge 3$). Step 1 needs one simple point. A bigon-free arrangement is not a near-pencil (each pencil line of a near-pencil carries only the centre and its point on the transversal), so Kelly–Rottenberg applies.
4. **Problem 1: global bounds are printed in SGA 4.** X 6.2: $\cd_\ell X \le 2\dim X + 1$ for $X$ of finite type over $\mathbb Z$; X 4.4 for $\ell$ invertible; X 6.1: $\cd_\ell \le 3$ for $X$ quasi-finite over $\mathbb Z$, with equality for $X \to \Spec \mathbb Z$ proper surjective, so $\cd_\ell(\Spec \mathbb Z) = 3$ is printed there. « Globally we found only [CM] » must be corrected; « our observation » should be kept only for « the constant cannot be lowered to 2 ».
5. **Problem 10: the classification credited to Breen 1999 is not in it.** The arXiv text classifies Gr-stacks by $H^3$ and strict Picard stacks by $\Ext^2(B, A)$, citing Deligne, SGA 4 XVIII 1.4; no $\mathrm{RHom}(\mathbb Z(M), N)$ statement, no *Pursuing Stacks*. Cite SGA 4 XVIII 1.4.

## 3. Other wrong or misattributed claims

- **Mathew, Prop. 4.5** bounds $\cd_\ell \kappa(\mathfrak q) \le d+1$ for residue fields; the bound on affine opens $\Spec R[1/f]$ is proved inside the proof. $R$ is a normal *domain*; the condition is for $\mathfrak p \supseteq I$. Mathew's proof is the paper's « natural route » (Gabber's affine proper base change, then G–O Th. 6.1): say so.
- **SGA 4 X 2.3 / 2.4.** The $\mathbb R[X,Y]/(X^2+Y^2)$ example is the Exemple after X 2.3, not X 2.4. Artin's induction on $\dim A$ is in the proof of X 2.4, with 2.3 and 2.2 for dimension one.
- **SGA 4 X 5.1** is for *noetherian* $X$; Problem 1's step « $V(\ell)$ affine of characteristic $\ell$, so $\cd \le 1$ » needs $X$ noetherian or a limit argument.
- **$\dim_\ell(k) \le \nu(k) + \cd_\ell(k)$** is correct but unsourced: immediate from Gabber–Orgogozo, Déf. 1.1.
- **Caramello 2009** is about De Morgan classifying toposes, with rings only as examples (§5); « work on theories of rings » overstates it.
- **Rosenthal 1984, Th. 3.9** states that $\mathrm{sh}(X; r)$ is a topos for strictly open $r$ without proof (proof in his 1979 thesis); what the paper proves is the étendue property for strictly regular $r$.
- **Kock–Moerdijk.** « Characterise étendues as $\mathrm{sh}(M, r)$ » is the 1992 paper's title result, not the 1996 paper's; the 1992 Lemma 5.1 / § 6 claims are unchecked (ScienceDirect closed).
- **Felsner–Goodman** contains none of Bose–Everett–Wismath, Robertson–Vitray, Mohar, or « local sequences determine a Euclidean arrangement »; closest are Th. 5.2.2 (Goodman–Pollack, lines) and Th. 5.5.1 (4-connectivity of the graph of a simple projective arrangement). Cite primary sources: Mohar, Combinatorica 15 (1995) 541–556; Vitray, JCTB 54 (1992) 1–12 (face-width 2 and 3 in the projective plane, directly relevant); Mohar–Robertson–Vitray, Discrete Math. 149 (1996) 141–157. Bose–Everett–Wismath, IJCGA 13 (2003) 447–462 exists but its abstract says nothing of unique embeddings: unverified for this claim.
- **Durfee 1983** (from the zbMATH review) treats $T \smallsetminus Z$ for a neighbourhood $T$ of a closed $Z$ in a projective $Y$. $X \cap B_y = B_y \smallsetminus (Y \smallsetminus X)$ is of that form only when $(Y \smallsetminus X) \cap B_y = \{y\}$; the general case may need Durfee–Saito (1990) or Saito's mixed Hodge modules. The $E_1$ formula was not checked.
- **Collas 2026**: the abstract claims a combinatorial reconstruction of $G_{\mathbb Q}$ already; what is left to forthcoming work is the model $GT^{NF}$ (§4.3.3). Reword.

## 4. Bibliography corrections (metadata)

| Key | Correction |
|---|---|
| andre | subtitle « (motifs purs, motifs mixtes, périodes) »; ch. 5 « Les conjectures standard », pp. 47–60, § 5.2 Lefschetz |
| breen1978 | pp. 39–125; replace by, or add, Breen 1975 (above) |
| breen1999 | no. 3, pp. 295–335, doi:10.1023/A:1000928915124 |
| caramello | Adv. Math. 222 (2009), 2117–2144, doi:10.1016/j.aim.2009.07.009 |
| clausenmathew | no. 3, pp. 981–1076, doi:10.1007/s00222-021-01043-3 |
| elephant | 2 vols, Oxford Logic Guides 43–44 |
| friedmanlaza | « The higher Du Bois and higher rational properties for isolated singularities », J. Algebraic Geom. 33 (2024), 493–520, doi:10.1090/jag/824; cite Th. 2.6 and Def. 2.7 rather than § 2 |
| gabberorgogozo | pp. 47–80, doi:10.1007/s00222-008-0133-y |
| gabberzavyalov | 59 (2026), no. 2, 387–436, doi:10.24033/asens.002641 |
| illusie2023 | talk notes, Chicago, 6 March 2023, https://www.imo.universite-paris-saclay.fr/~luc.illusie/Illusie-Chicago-2023-1.pdf (claim confirmed, p. 2) |
| kleiman1968 | Adv. Stud. Pure Math. 3, North-Holland/Masson; Th. 2.13 unchecked (no open copy) |
| mathew | no. 5, pp. 1079–1119, doi:10.1112/S0010437X21007144 |
| pop2019 | « Finite tripod variants of I/OM: On Ihara's question/Oda–Matsumoto conjecture », Invent. Math. 216 (2019), no. 3, 745–797, doi:10.1007/s00222-019-00855-8 |
| sga4 | Artin, Grothendieck, Verdier are editors (« dirigé par »); Exposé X is LNM 305, pp. 43–63 |
| melchior, grunbaum | keep, but add Kelly–Rottenberg 1972 and Bokowski–Pokora 2018 for pseudolines |
| order | the list is no longer alphabetical (grunbaum, melchior before felsnergoodman) |

Confirmed as they stand: hodge3 (8.2.4 (i), (ii) exactly as stated, p. 38), poonenstoll (§ 4, $2c_\lambda = 0$ p. 1119, no $\chi$ criterion), milneadt (II.3.2, 3.3, 3.12 support $\cd_\ell \Spec \mathbb Z = 3$), clausenmathew Cor. 3.29, gabberzavyalov Th. 1.7, gabberorgogozo Th. 6.1 and § 3, SGA 4 X 3.0 and its quotation, hls, collas (exists), durfee (metadata), illusie2023 (claim), Tonini's two arXiv papers (exist).

## 5. Items to add

Kostant, Amer. J. Math. 81 (1959), 973–1032, doi:10.2307/2372999; Springer, Invent. Math. 25 (1974), 159–198, doi:10.1007/BF01390173; Breen 1975 (above); Kelly–Rottenberg 1972; Bokowski–Pokora 2018; Deligne's theorem, SGA 4 VI 9.0 (LNM 270, p. 336), stated for locally coherent toposes; SGA 4 XVIII 1.4; SGA 4 X 4.4, 6.1, 6.2; Tonini, « Stacks of ramified Galois covers » (PhD thesis, 2013, arXiv:1307.1116) and « Ramified Galois covers via monoidal functors », Transform. Groups 22 (2017), 845–868, doi:10.1007/s00031-016-9395-4; Moerdijk, « Foliations, groupoids and Grothendieck étendues », Rev. Acad. Cienc. Zaragoza (2) 48 (1993), 5–33 (seen on nLab only); Vitray 1992 and Mohar 1995 (above).
