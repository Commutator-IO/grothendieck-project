# Citation check: docs/problem-three/article.tex, 8 November 2026

Each `\bibitem` was compared with canonical metadata from Crossref (`api.crossref.org/works/<doi>`), zbMATH Open (`api.zbmath.org`), the publisher's or host's page, or the GitHub API. Where the article cites a numbered result, that result was read in the source when an open copy exists (Kelly's book in the TAC reprint; MathOverflow through the Stack Exchange API). Only bibliographic metadata and public URLs were sent to these services. No manuscript text was sent.

| Key | Source checked | Metadata | In-text use | Result / action |
|---|---|---|---|---|
| ar | Crossref 10.1017/CBO9780511600579; zbMATH 0795.18007 (review read) | Adámek, Rosický, LMS LNS 189, CUP, 1994: matches | ch. 1 (locally presentable categories, Gabriel–Ulmer duality); **Example 6.38** (a colimit closure needing a proper class of steps) | **Book not opened** (no open copy; Google Books blocked). Example 6.38 is used as Rosický describes it in his MathOverflow answer 243945 and as Campion spells it out in answer 243949. The article says so in « What is not done ». To read in a library copy |
| gu | Crossref 10.1007/BFb0059396; zbMATH 0225.18004 | LNM 221, Springer, 1971: matches | Set^op not locally presentable; Gabriel–Ulmer duality; second question of 2 July (only axioms remain) | **Book not opened**. Satz 7.13 (a locally presentable category whose dual is locally presentable is a preorder) agrees with the nLab page *locally presentable category*. The article cites the book without a number |
| sga4 | Crossref 10.1007/BFb0081551; zbMATH 0234.00007 | SGA 4, tome 1 (exp. I–IV), LNM 269, Springer, 1972: matches. Editors Artin, Grothendieck, Verdier (Crossref lists Grothendieck, Verdier) | Giraud's theorem, exp. IV | Not opened. Cited by exposé only, without a theorem number, which we could not check |
| isbell | Crossref 10.1215/ijm/1255456274; zbMATH 0104.01704 | Illinois J. Math. 4 (1960), no. 4, 541–552: matches (pages from zbMATH and from Kelly's bibliography, item [35]) | definition of (left/right) adequate = dense/codense | Project Euclid did not serve the text. The terminology was checked in Kelly §5.1 (« Isbell's right adequate » = codense) |
| kellybook | zbMATH 0478.18005 (1982), 1086.18001 (TAC reprint 2005); TAC reprint PDF read | LMS LNS 64, CUP 1982; Repr. Theory Appl. Categ. 10 (2005): matches | §3.5 (transfinite closure, bound ρ, smallness), §5.1 (dense, Isbell's terminology), Thm 5.35 (free F-cocompletion = closure), Thm 5.56, Thm 6.5, Thm 6.11, Prop 6.21, Cor 6.22, Thm 6.23, **end of §5.9** (Cat₀ is the colimit closure of {2}; the idempotent is not a one-step colimit) | All read in the reprint and they match. **Correction**: the Buffalo article cites the Cat₀ remark as « §5.7, p. 100 ». It is at the end of §5.9, between the running heads p. 101 and p. 103 of the reprint. The new article cites « end of §5.9 » |
| mo | Stack Exchange API, question 243931 and its answers | Question by Tim Campion, 8 July 2016. Answers by J. Rosický (243945), T. Campion (243949) and M. Barr (243960) | Rosický: Example 6.38 needs a proper class of steps; under Vopěnka's principle the colimit closure of a small subcategory of a locally presentable category is locally presentable (6.28, 6.29). Barr: Isbell's unpublished 1965 claim about Z/2 | Matches. « a comment by M. Barr » corrected to « an answer by M. Barr » |
| pare | Crossref 10.1090/S0002-9904-1974-13497-X; zbMATH 0288.18002 | Bull. AMS 80 (1974), no. 3, 556–562 | monadicity of the power-object functor (Paré's theorem) | **Pages corrected** from 556–561 to 556–562 (Crossref). The paper itself could not be opened (AMS returned 403). The citation gives credit only; Prop. 7.1 has its own proof |
| repo | GitHub API (`gh repo view`): public. `git ls-files` | `lean/Buffalo/ProblemThree.lean` and `docs/buffalo-topos/index.tex` are tracked; commit 23657b5d exists | Lean file, index | none |
| open | local `docs/buffalo-open/article.tex` | title matches. Served at `/article/grothendieck-buffalo-open.pdf` (copy line in `docs/study/tei.mjs`) | companion survey | none |

## Searched, not cited

These were searched (zbMATH API, arXiv API, Crossref, MathOverflow through the Stack Exchange API) and found not to state any of the article's results:

- Isbell, *Small adequate subcategories* (J. London Math. Soc. 43, 1968, doi 10.1112/jlms/s1-43.1.242) and *Small subcategories and completeness* (Math. Systems Theory 2, 1968, doi 10.1007/BF01691344). Both are about density and codensity. Not opened.
- Freyd–Kelly, *Categories of continuous functors I* (JPAA 2, 1972, doi 10.1016/0022-4049(72)90001-1).
- Kelly, *Structures defined by finite limits in the enriched context I* (Cahiers 23, 1982, zbMATH 0538.18006).
- Bastiani–Ehresmann, *Categories of sketched structures* (Cahiers 13, 1972, zbMATH 0263.18009). Lair, *Étude générale de la catégorie des esquisses* (1975) and *Elements of the theory of sketches* I–III. Guitart–Lair, *Calcul syntaxique des modèles* (Diagrammes, 1980) and *Limites et colimites pour représenter les formules* (1982).
- Diers, *Catégories multialgébriques* (Arch. Math. 1980).
- Kelly–Lawvere, essential localizations (on a different subject).
- Adámek–Rosický–Vitale, *Algebraic Theories*: sifted colimits and one-sorted theories, not the closure question.
- Brandenburg, arXiv:2106.11115, and MathOverflow 349409: universal property of Mod(S) for limit sketches. This is related to Prop. 7.4, which uses Kelly instead.
- MathOverflow searches on closure under limits/colimits, Set^op and codensity: only 243931 is relevant, and it is cited.

## Not verified in the source

AR Example 6.38 (book), GU Satz 7.13, SGA 4 exp. IV theorem number, Paré's paper, and Isbell 1960 (text).

The Kassis et al. citation suggested by the review skill was not added.
