# Citation verification: Lean appendix (`docs/lean/article.tex`)

Read-only review, 2026-10-24/25. Nothing in the article was edited.

**Line numbers** refer to a snapshot of the working tree taken on 2026-10-24 at 18:40. Another agent was revising the prose during the review, so lines may have moved. Keys and quoted phrases identify each item.

**Method.**
- Metadata: one Crossref query per `\bibitem` (`query.bibliographic`, plus a DOI lookup when the item gives a DOI). arXiv IDs checked with the arXiv API (`export.arxiv.org`). Script and raw JSON are in the session scratchpad, not in the repo.
- Claims: read each attributing sentence, then the source's arXiv full text or abstract, the Stacks Project tags, Cisinski's and Maltsiniotis's own PDFs, and GitHub.
- Links: HTTP checks (status after redirects).
- Theorem numbers were checked against the **arXiv** versions only, not the published numbering.

## 1. Summary

| | Count |
|---|---|
| `\bibitem`s | 99 |
| Cited keys | 98 |
| Uncited bibitems | 1 (`riehlverity2022`) |
| Cited but missing keys | 0 |
| Duplicate keys | 0 |
| Confirmed in Crossref (title, authors, venue, year match) | 79 |
| Confirmed by arXiv only (preprints) | 4 (`henry2016`, `maltsiniotis2010`, `kreutzshenvial`, `singermanstrudwick2020` (venue not confirmed)) |
| URL-only items, URL alive | 2 (`stacks`, `formalconjectures`) |
| Personal communication | 1 (`cisinskimo2026`) |
| Not findable with the allowed APIs | 13 (see §3). All but `ferrand1966` match records I know. |
| DOIs given in the bibliography | 8. All resolve to the right record. |
| DOIs available in Crossref but not given | 65 (list in §4) |
| arXiv IDs given | 22. All match title and authors. |

**Problems by kind**

| Kind | Count | Items |
|---|---|---|
| Wrong metadata | 2 | `ega4-1` (pages), `friedmanlaza` (says « à paraître », already published) |
| Incomplete metadata | 3 | `mathew2021` (no issue or pages), `pernice2022` (no pages), `gabberzavyalov2026` (no volume or pages; two DOIs registered) |
| Title to check | 1 | `ara2013` (Crossref's TAC record has the French title) |
| Unverifiable | 1 | `ferrand1966` |
| Uncited bibitem | 1 | `riehlverity2022` |
| Source type | 1 | `cisinskimo2026` (public MathOverflow answer cited as a personal communication) |
| Claim not supported by the cited place | 1 | `mackall2020` at 2.tex:71 |
| Claim partly supported | 9 | hypotheses dropped or credit loose, see §2 |
| Claim to check | 1 | `cisinski2006` at 118.tex:70 |
| Dead links | 0 | 0 of 7 bibliography/footnote URLs; 0 of 96 GitHub Lean targets |
| Bibliography order and format | 6 order inversions; inconsistent venue capitalisation | §5 |

## 2. In-text claims: does the source say what the text attributes?

33 citation loci were checked: 22 supported, 9 partly supported, 1 not supported, 1 to check. About 11 more could not be read (books, Numdam/IHÉS scans) and are listed at the end of this section.

### Problems, most important first

| Key | Location | What the text attributes | Verdict | Evidence | Suggested fix |
|---|---|---|---|---|---|
| `gabberorgogozo2008` | vide/cohomologie-etale-et-l-adique.tex:23 | Th. 6.1: cd_ℓ(U) = dim A + dim_ℓ(k) « pour A excellent », U an open affine of Spec A[1/ℓ] | **partly: hypotheses dropped** | Th. 6.1 needs A **henselian, excellent, integral**, residue characteristic ℓ and fraction field of characteristic 0 | Add « hensélien intègre, de corps résiduel de caractéristique ℓ et de corps des fractions de caractéristique nulle ». The same paragraph's later remark on Spec **Z** falls outside the theorem without « hensélien ». |
| `mackall2020` | 2.tex:71 | The non-injectivity example in degree 3 for BO⁺(2n+1), « en renvoyant à l'exposé XIV de SGA 6 » | **not supported (wrong pointer)** | The example is Remark 4.3 and rests on Karpenko–Merkurjev [KM19, Th. 5.5]. Mackall cites SGA 6 XIV for a different example (flag varieties of O⁺(n)). | « (remarque 4.3), en s'appuyant sur Karpenko–Merkurjev ». Drop the SGA 6 XIV pointer. |
| `edidinhu2025` (+ `pernice2022`) | 146.tex:266 | Th. 1.3: A*([M_{0,2g+2}/S_{2g+1}]) = **Z**[l]/(2g(2g+1)l), g ≥ 2; « L_n l'engendre »; « partant de la présentation de Pernice par un sous-groupe de Borel » | **partly** | Formula, g ≥ 2 and theorem number match. (1) The paper also assumes an algebraically closed field of characteristic not dividing 2g+2. (2) The generator l is a torus-character class; the paper never identifies L_n as the generator. (3) Pernice gives a stack description (Prop. 1.3); the Borel-quotient presentation is Edidin–Hu's own §3. | Add the field hypothesis. Mark « L_n l'engendre » as the edition's deduction. Rephrase: « partant de la description de Pernice, qu'ils présentent par un sous-groupe de Borel ». |
| `arsievistoli2004` | 146.tex:180 | « voir aussi Arsie–Vistoli th. 5.1 » for Pic[M_{0,n}/S_n] cyclic of order 2(n−1) | **partly** | Th. 5.1 computes Pic of the stacks of uniform cyclic covers H_sm(n,r,d). For hyperelliptic curves that is Pic(H_g), not Pic(D_{2g+2}). | « (pour Pic(H_g), dont Pic(D_{2g+2}) est un sous-groupe d'indice 1 ou 2, GV th. 3.6) ». |
| `voight2016` | 84.tex:35 | The classification by (δ, b mod 2) when 2 is regular is in « prop. 3.11 et th. 4.3 » | **partly** | Prop. 3.11 gives existence and uniqueness of the discriminant. Th. 4.3 gives an AS(R)-action on the fibres of disc. The classification follows (R[4] = 0 when 2 is regular) but is not stated. | « découle de la proposition 3.11 et du théorème 4.3 ». |
| `voight2016` | 84.tex:96 | The fixed-subring identification « est due à C. Small (1972), que cite Voight (théorème 3.24) » | **partly** | Th. 3.24(iii) states the property without crediting anyone. Small appears only in the introduction, next to Kanzaki, as a general reference on quadratic algebras. | « Voight (th. 3.24 (iii)) ; voir aussi Kanzaki et Small (1972), qu'il cite ». |
| `formalconjectures` | autres/cycles-algebriques-et-conjectures-standa.tex:16 | Resolution in dim ≤ 3 « en toute caractéristique (Cossart–Piltant) »; « ces trois énoncés sont formalisés » | **partly** | File exists (HTTP 200). The positive-characteristic statements are over a **perfect** field. All three are statements closed by `sorry`, not proofs. | « sur un corps parfait » ; « énoncés (sans démonstration) dans le dépôt ». |
| `mathew2021` | vide/cohomologie-etale-et-l-adique.tex:23 | Prop. 4.5: cd_ℓ ≤ d+1 on affine opens of Spec R[1/ℓ], R henselian along ℓ | **partly** | Prop. 4.5 assumes R an **excellent normal domain**, henselian along an ideal containing (p). Its conclusion concerns the residue fields κ(q); the vanishing on affine opens is in the proof. | Add the hypotheses; « (démonstration de la prop. 4.5) ». |
| `topaz2018` | autres/groupes-fondamentaux-et-theorie-de-galoi.tex:39 | Strengthened mod-ℓ I/OM over a perfect field of characteristic ≠ ℓ | **partly** | The Main Theorem and Th. B assume an **infinite** perfect field. §1.7 is cited correctly. | « corps parfait infini ». |
| `cisinski2006` | 114.tex:70 | The cube category refutes (iii) ⇒ (i) (Maltsiniotis 2005, Cisinski 2006) | **partly** | Maltsiniotis 2005, introduction: the cube category is not a strict test category (supported). In Cisinski 2006 only the positive result was found (cubes form a W∞-test category, 8.4.13, 8.4.27), not this counterexample. | Cite the Maltsiniotis passage precisely. Give a numbered place in Cisinski or drop that citation. |
| `cisinski2006` | 118.tex:70 | « the last sentence of 4.3.2 » derives asphericity of A from connectedness (iv) | **to check** | That sentence says: for A non-empty, *each of conditions (a)–(g)* implies A aspherical. It does not start from connectedness. | Check that (iv) is one of (a)–(g); otherwise rephrase. |
| `cisinskimo2026` | bib (article.tex:342); 118.tex:16 « Interrogé directement » | « communication personnelle, 21 octobre 2026 » | **source type** | The `Folder118.lean` docstring says Cisinski answered publicly on MathOverflow (question 516223, 21 Oct 2026). | Cite the MathOverflow answer (public, checkable), or bring the docstring in line with the article. |
| `brion2014` | 53.tex:38 | §2.2 Prop. 3: left-invertible ⇒ invertible, and 1 the only idempotent ⇒ group, « par le même argument » (Ax Th. C) | supported, one nuance | Prop. 3 (i) and (iii), §2.2, match. The Ax argument proves (i) only; (iii) uses Th. 1 and Prop. 1. | Optional: « (i) par le théorème C d'Ax ». |
| `gorchinskiyviviani2008` | 146.tex:180 | Th. 3.6: Pic[M_{0,n}/S_n] cyclic of order 2(n−1), n even | supported | Th. 3.6 (arXiv math/0609705): Pic(D_{2g+2}) = **Z**/(4g+2), char ∤ 2g+2 | Optional: add « car. ∤ n ». |
| `beauville2010` | 64.tex:45; 85.tex:159 | Criterion for A₅ ⊂ PGL₂(K) | supported | Prop. 1.1(3), arXiv 0909.3942 | Optional: cite « prop. 1.1 ». |

### Supported (no change needed)

- `fultonolsson2010` / `mumford1965` (146.tex:266): Pic(M_{1,1}) = **Z**/12. The μ₂-gerbe remark is the edition's and is not attributed to them.
- `stacks` [07EL, 07EM] (22.tex:128): 07EL = Th. 15.41.1, formal smoothness for the 𝔪-adic topology; 07EM = Ex. 15.41.2, K[[x]] with the (x)-adic topology. Both tags return HTTP 200.
- `henrylanari2023`, `henry2016`, `ara2013`, `maltsiniotis2010` (article.tex:274–275): the homotopy-hypothesis paragraph matches. Henry–Lanari: semi-model structure ⇒ hypothesis, n = 3 proved. Henry: Conj. 5.3.3 is the pushout lemma. Ara: simply connected types modelled are exactly products of Eilenberg–Mac Lane spaces.
- `maltsiniotis2005` (114.tex:66): 1.1.32 defines W₀.
- `cisinski2006` (114.tex:62): 9.3.1 and 9.3.2.
- `cisinski2006` / `cisinskimo2026` (118.tex:16): 4.3.2 includes (g) among the equivalent conditions.
- `lorenz1999` (46.tex:40): §3.6, Lemma.
- `courcelle2020` (156-3.tex:58): Th. 7.
- `singermanstrudwick2020` (79.tex:103, 147): Th. 11 (diameter 3 for n ≥ 5) and Th. 9 (distance between poles is 3).
- `antieaumeier2020` (64.tex:52): Def. 4.4, Prop. 4.5, Lemma 4.7.
- `gabberzavyalov2026` (Th. 1.7), `clausenmathew2021` (Cor. 3.29), `gabberorgogozo2008` (Prop. 5.4.5) in vide/cohomologie-etale-et-l-adique.tex:23.
- `bostcharles2016` (Def. 2.3, Lemma 2.5, §2.2) and `kreutzshenvial` (Prop. 3.1, Rem. 3.2, Th. 5.4, Conj. 4.1; v3 dated 2026-01-21) in vide/theorie-de-hodge.tex:22, 26.
- `elliott2010` (153.tex:150): title level.
- OpenAI footnote (article.tex:115, 142, 274): repository, `lean/docs/008.md` and `312.md` return HTTP 200. The README gives 719 manuscripts, and the described scope matches both pages. `history.md` records the 7 Oct 2026 withdrawal of three manuscripts.

### Not checked (sources not accessible)

`milne2006` II.3; `sga4-3` X 4.1, 2.4, §3.0; `durfee1983`; `deligne1974` 8.2.4; `friedmanlaza` §2; `bienborel1992`; `serre1964`; `polya1919`; `bass1964`; `rees1956`; `baer1940`. These are books, Numdam or IHÉS scans, or classical results. None carries a theorem number that could be tested.

## 3. Metadata, item by item (problems only)

| Key | Line | Problem | Evidence | Fix |
|---|---|---|---|---|
| `ega4-1` | 365 | **Pages wrong**: the bib says 101–355 | Crossref 10.1007/BF02684747: Publ. IHÉS 20 (1964), **5–259** | « 20 (1964), 5--259 » |
| `friedmanlaza` | 358 | « à paraître » is outdated | Crossref and arXiv v4 journal-ref: J. Algebraic Geom. **33 (2024), no. 3, 493–520**, doi:10.1090/jag/824 | Give the published reference |
| `mathew2021` | 397 | No issue or pages | Compositio 157 (2021), **no. 5, 1079–1119**, doi:10.1112/S0010437X21007144 | Complete |
| `pernice2022` | 402 | No pages | IMRN 2022, no. 15, **11539–11574**, doi:10.1093/imrn/rnab072 | Complete |
| `gabberzavyalov2026` | 362 | No volume or pages; Crossref has **two** DOIs for the same article (10.24033/asens.1641 and 10.24033/asens.002641) | Crossref | Add the DOI the SMF page displays once the issue is out |
| `edidinhu2025` | 354 | Online-first (Crossref volume −1, pp. 1–23) | Crossref | Fine for now; update when the issue appears |
| `ara2013` | 318 | Crossref's TAC record (10.70930/tac/50iqmupv) gives the title « Sur les types d'homotopie modélisés par les ∞-groupoïdes stricts ». arXiv 1206.2945 has the English title used in the bib. | Crossref; arXiv | Check the TAC page. If the published title is French, cite it. |
| `ferrand1966` | 357 | Not in Crossref (CRAS 1966 is not deposited), and I could not corroborate it from another source | — | Check against Gallica or zbMATH before release |
| `riehlverity2022` | 407 | Never cited | — | Cite it where ∞-categories are mentioned, or delete it |
| `cisinskimo2026` | 342 | See §2 | — | — |
| `gorchinskiyviviani2008`, `bostcharles2016` | — | Crossref "issued" is 2007/2014 (online first); print volume 2008/2016 | — | Fine as is |
| `cahen1997` | — | Crossref chapter records say 1996; the AMS book is 1997 | — | Fine as is |

**Not findable through Crossref, arXiv or Semantic Scholar** (classical; metadata consistent with standard catalogues, except where noted): `belyi1979`, `coxetermoser1957` (Crossref has reviews confirming the book), `conrad2014`, `cori1975`, `drinfeld1990`, `ferrand1966` (unconfirmed), `ihara1991`, `jacques1968`, `milne2006`, `morita1958`, `mumford1965` (a review confirms the volume), `popescugabriel1964`, `pursuingstacks2022`.

## 4. Missing DOIs (available in Crossref)

The bibliography gives a DOI for 8 items only: `arsievistoli2004`, `ax1968`, `borel1969`, `brion2014`, `edidinhu2025`, `gorchinskiyviviani2008`, `lorenz1999`, `putcha1988`. Either give DOIs throughout or for none. If throughout, these are the Crossref DOIs:

`antieaumeier2020` 10.2140/ant.2020.14.2295 · `adamekrosicky1994` 10.1017/CBO9780511600579 · `andre2004` 10.1515/9783110198133.1.55 · `ara2013` 10.70930/tac/50iqmupv · `sga4-1` 10.1007/BFb0081551 · `sga4-3` 10.1007/BFb0070714 · `baer1940` 10.1090/S0002-9904-1940-07306-9 · `bass1964` 10.1007/BF02684689 · `baues1989` 10.1017/CBO9780511662522 · `beauville2010` 10.1090/conm/522/10289 · `bhatia1997` 10.1007/978-1-4612-0653-8 · `borceux1994` 10.1017/CBO9780511525858 · `borgerwieland2005` 10.1016/j.aim.2004.06.006 · `bost2001` 10.1007/s10240-001-8191-3 · `bostcharles2016` 10.1515/crelle-2014-0025 · `brown1973` 10.1090/S0002-9947-1973-0341469-9 · `cadman2007` 10.1353/ajm.2007.0007 · `chase1960` 10.1090/S0002-9947-1960-0120260-3 · `chudnovsky1985` 10.1007/BFb0074601 · `cisinski2006` 10.24033/ast.715 · `clausenmathew2021` 10.1007/s00222-021-01043-3 · `courcelle2020` 10.1051/ita/2020007 · `lean4` 10.1007/978-3-030-79876-5_37 · `deligne1974` 10.1007/BF02685881 · `deligne1989` 10.1007/978-1-4613-9649-9_3 · `deningermurre1991` 10.1515/crll.1991.422.201 · `durfee1983` 10.1215/S0012-7094-83-05043-3 · `elliott2010` 10.5802/acirm.34 · `fan1951` 10.1073/pnas.37.11.760 · `friedmanlaza` 10.1090/jag/824 · `fultonolsson2010` 10.2140/ant.2010.4.87 · `furusho2010` 10.4007/annals.2010.171.545 · `gabberorgogozo2008` 10.1007/s00222-008-0133-y · `gabberzavyalov2026` 10.24033/asens.1641 (see §3) · `gabrielzisman1967` 10.1007/978-3-642-85844-4 · `ega4-1` 10.1007/BF02684747 · `ega4-3` 10.1007/BF02684343 · `hartshorne1970` 10.1007/BFb0067839 · `hasseschmidt1937` 10.1515/crll.1937.177.215 · `hatcherlochakschneps2000` 10.1515/crll.2000.028 · `henrylanari2023` 10.70930/tac/897kfv5y · `jacobson1941` 10.1090/S0002-9947-1941-0005118-0 · `jonessingerman1978` 10.1112/plms/s3-37.2.273 · `karoubi1968` 10.24033/asens.1163 · `katz1970` 10.1007/BF02684688 · `katz1972` 10.1007/BF01389714 · `katzoda1968` 10.1215/kjm/1250524135 · `kisin2000` 10.5802/aif.1786 · `kockmoerdijk1992` 10.1016/0022-4049(92)90118-Y · `kockmoerdijk1996` 10.1016/0166-8641(95)00101-8 · `lenzing1969` 10.1007/BF01899297 · `lucas1878` 10.2307/2369308 and 10.2307/2369373 · `mackall2020` 10.1016/j.jalgebra.2020.06.018 · `maclane1998` 10.1007/978-1-4757-4721-8 · `maltsiniotis2005` 10.24033/ast.689 · `mathlib2020` 10.1145/3372885.3373824 · `mathew2021` 10.1112/S0010437X21007144 · `mukai1987` 10.2969/aspm/01010515 · `pernice2022` 10.1093/imrn/rnab072 · `polya1919` 10.1515/crll.1919.149.97 · `rees1956` 10.1017/S0305004100031091 · `riehlverity2022` 10.1017/9781108936880 · `tallwraith1970` 10.1112/plms/s3-20.4.619 · `topaz2018` 10.1007/s00222-018-0792-2 · `voight2016` 10.2140/pjm.2016.283.483

## 5. Format and order

- **Alphabetical order broken in 6 places.**
  - `antieaumeier2020` precedes `adamekrosicky1994`.
  - `bienborel1992` precedes `beauville2010`.
  - `henrylanari2023` precedes `henry2016`; a single author should come first.
  - `ega4-1` and `ega4-3` (Grothendieck) precede `formalconjectures` (Google) and `gorchinskiyviviani2008`.
  - `mathlib2020` precedes `mathew2021`.
  - `mumford1965` precedes `mukai1987`.
- **Venue names are capitalised inconsistently.**
  - « Publications mathématiques de l'IHÉS » (`bass1964`, `deligne1974`, `ega4-*`) vs « Publications Mathématiques de l'IHÉS » (`bost2001`, `katz1970`).
  - « Inventiones mathematicae » vs « Inventiones Mathematicae » (`katz1972`).
- **Volume and issue style varies**: « (2) 171 », « (3) 37 » and « (4) 1 » sit next to plain volume numbers, and « n\textsuperscript{o} » is used only sometimes. This is minor.
- **The `formalconjectures` and OpenAI web sources** carry an access date, as they should. `stacks` has none.

## 6. Links

- The bibliography and footnote URLs all return HTTP 200: stacks.math.columbia.edu, tags 07EL and 07EM, github.com/google-deepmind/formal-conjectures (and the cited file), github.com/openai/math (and `lean/docs/008.md`, `312.md`).
- The 96 distinct GitHub Lean targets of `\verifie`, `\general` and the summary table, at their linked refs (`article-lean-2026-10` or `main`), all return HTTP 200. The peer-review report covers the files that changed after the tag.
