# Citation check: docs/bigon/article.tex, 7 November 2026

Each `\bibitem` was compared with canonical metadata from Crossref (`api.crossref.org/works/<doi>`), zbMATH Open (`api.zbmath.org/v1/document/_search`), the arXiv abstract page, or the publisher's page. Where the article cites a numbered result, the result was read in the source when an open copy was available. Only bibliographic metadata was sent to these services; no manuscript text was.

| Key | Source checked | Metadata | In-text use | Action |
|---|---|---|---|---|
| bjorner1999 | Crossref 10.1017/CBO9780511586507; zbMATH 0944.52006 | Björner, Las Vergnas, Sturmfels, White, Ziegler, *Oriented Matroids*, 2nd ed., Encycl. Math. Appl. 46, CUP, 1999: matches | Arrangements as rank-3 oriented matroids (standard; Folkman–Lawrence topological representation, treated in the book). New use: the Fano matroid is not orientable (standard, in the book) | none |
| bokowskipokora2017 | Crossref 10.1007/s10998-017-0224-x; zbMATH 1413.52029; arXiv:1607.05864 | Period. Math. Hungar. 77 (2018), no. 2, 164–174 (online 2017): matches | **Th. 1.3** read in the arXiv text (v4): it is Melchior's equality Σ_{r≥2}(3−r)t_r = 3 + Σ_j (j−3)p_j for pseudoline arrangements, attributed to Melchior. It gives a simple crossing, but it is not a Sylvester–Gallai theorem in Kelly–Rottenberg's form | the "see also" moved from Theorem 1 to a sentence on Melchior's equality, and added to the Melchior paragraph of §6. Theorem numbering in the published version not checked (no open copy) |
| felsnergoodman2017 | Handbook site (csun.edu/~ctoth/Handbook/HDCG3.html); zbMATH 1375.52001 (the book) | Ch. 5 "Pseudoline arrangements", S. Felsner and J. E. Goodman, in Goodman, O'Rourke, Tóth (eds.), 3rd ed., CRC Press, Boca Raton, 2017: matches | General reference; the claim that the dichotomy is not stated there was not re-checked (no open copy) | place of publication added. No chapter DOI found in Crossref |
| finschifukuda2003 | Crossref 10.1007/978-3-642-55566-4_19; zbMATH 1077.52519 | Title is "Combinatorial generation of small point configurations and hyperplane arrangements" (the article had "Complete combinatorial generation…", which is the title of the authors' CCCG 2001 abstract); Aronov et al. (eds.), Algorithms Combin. 25, Springer, 2003, 425–440 | Counts 1, 2, 4, 17, 143, 4890, 461053 (n = 3…9) and uniform 4382 (n = 9). These agree with the values asserted by `computations/bigon/run.py`. The table in the paper was not read (no open copy) | **title corrected**, editors added |
| grunbaum1972 | zbMATH 0249.50011 | *Arrangements and Spreads*, CBMS Regional Conf. Ser. Math. 10, AMS, 1972: matches | General reference | none |
| kellyrottenberg1972 | Crossref 10.2140/pjm.1972.40.617; zbMATH 0251.50010; published PDF (msp.org, pjm-v40-n3-p10) | Pacific J. Math. 40 (1972), no. 3, 617–622: matches | **Th. 3.6** read: the number λ of simple points satisfies λ ≥ 3n/7, and the remark after it shows the bound is sharp (complete quadrilateral with its diagonal triangle). The article's Theorem 1 said only "not a near-pencil ⇒ a simple crossing" | Theorem 1 restated as the source's bound and its consequence (see the peer-review report, M1) |
| lienhardt1994 | Crossref 10.1142/S0218195994000173; zbMATH 0821.57016 | Int. J. Comput. Geom. Appl. 4 (1994), no. 3, 275–324: matches | Definition of generalised maps (involutions α_0, α_1, α_2, α_0α_2 an involution): consistent with the paper's subject | none |
| melchior1941 | zbMATH 0025.09105 (also JFM 67.0733.04) | Deutsche Math. 5 (1941), 461–475: matches | Melchior's inequality: standard | none |

## Not verified

- Felsner–Goodman: the statement that the dichotomy does not appear in the chapter (no open copy).
- Finschi–Fukuda: that the counts appear in that paper. The values themselves match the enumeration, which asserts them in `run.py`.

## No references added

No new references were added. The Kassis et al. citation suggested by the peer-review skill's instructions was not added either: the skill helped with a local review of this text and did not contribute to the mathematics.
