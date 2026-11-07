# Citation verification, 2026-11-07

Article: docs/polytopes/article.tex. Metadata checked against Crossref (api.crossref.org), zbMATH Open API and arXiv abstract pages (the arXiv export API was rate-limited). Claims checked in the full texts where accessible.

| Key | Metadata check | Change |
|---|---|---|
| coxeter1973 | Coxeter, Regular Polytopes; zbMATH lists the 1948 and 1963 editions; the 3rd ed. (Dover, 1973) is standard but was not found by the zbMATH query | none; manual verification only |
| dgklm2021 | arXiv:2102.02757 (v1 2021-02-04, v3 2024-09-09), five authors as cited; published J. Eur. Math. Soc. 27 (2025), no. 1, 119-181, doi:10.4171/jems/1539 (Crossref) | bibitem updated to the JEMS version |
| esquisse | Crossref: "Esquisse d'un Programme", Geometric Galois Actions (Schneps, Lochak eds.), CUP 1997, pp. 7-48, doi:10.1017/CBO9780511758874.003; English translation in the same volume, pp. 243-283 (Crossref 243-284), doi:10.1017/CBO9780511758874.017 | translation added to the bibitem |
| fisherjamison1998 | Crossref and zbMATH 0904.51010: Fisher, Jamison, Properties of affinely regular polygons, Geom. Dedicata 69 (1998), 241-259, doi:10.1023/A:1004903818702 | new reference |
| ji2023 | arXiv:2304.03345, Caleb Ji, "A note on regular polyhedra over finite fields", single version v1, 2023-04-06, no journal ref | none |
| korchmarosszonyi2008 | Crossref and zbMATH 1193.51011: Contrib. Discrete Math. 3 (2008), no. 1, 20-38, doi:10.55016/ojs/cdm.v3i1.62767 | issue and pages added |
| lucas1878 | Crossref: Amer. J. Math. 1 (1878), no. 2, 184-196 (doi:10.2307/2369308); no. 3, 197-240 (10.2307/2369311); no. 4, 289-321 (10.2307/2369373) | issues and the two other DOIs added |
| mcmullenschulte2002 | Crossref: Abstract Regular Polytopes, McMullen, Schulte, CUP 2002, doi:10.1017/CBO9780511546686 | none |
| monsonschulte2004 | Crossref and zbMATH 1065.20051: Adv. Appl. Math. 33 (2004), no. 2, 290-317, doi:10.1016/j.aam.2003.11.002 | none |

## Claims attributed to sources

1. Ji 2023 (full text read). Formulae over Z[cos theta, cos gamma] whose reduction is "well-defined ... except p = 2, 5 for the icosahedron": supported (section 3.1). Automorphism group stays A_5 at the other primes: supported (Prop. 3.1 and following lines). Quotation "seems to claim this in all cases": verbatim (remark after Prop. 3.1). Added: Ji's remark that his formulae use the cosines, not their doubles, and that he could not resolve the discrepancy (section 2): supported.
2. Korchmaros-Szonyi (full text read). (3.4): the circular system v_0 + c v_1 + v_2 = 0, ... has a nontrivial solution iff c = +-2 or (x^2 - cx + 1) | (x^n - 1). The article had dropped "c = +-2"; corrected. "Every affinely regular polygon lies on an irreducible conic" is Lemma 2.2 (non-degenerate polygons), not Th. 2.1-2.3; corrected. Th. 2.1 (classification: ellipse, hyperbola, parabola examples) and Th. 2.3 (finite fields; n = p on a parabola): supported. The case c = -2 (n even: even-index vertices coincide, odd ones too) is in section 3, which assumes n prime to the characteristic: supported. No two-line 2p-gon found in the survey; the article now says "we have not found ... in that survey" and explains that these polygons are degenerate in the survey's sense.
3. Danciger-Gueritaud-Kassel-Lee-Marquis (arXiv v3 read). The statement that the reflections determine the Cartan matrix only up to diagonal conjugation is in section 3.2 (and section 1.2), not section 3.1 (which defines Coxeter groups); citation changed to section 3.2. Section numbers verified only in arXiv v3, as the bibitem now says.
4. Monson-Schulte 2004 (publisher page 403; zbMATH review read). The former "study reflection groups of polytopes over finite fields through a similar Gram matrix" could not be verified. Replaced by what the review supports: they reduce the root-lattice representation of a crystallographic Coxeter group modulo an odd prime and ask when the image is a string C-group (the group of an abstract regular polytope).
5. Esquisse section 4 (French and English texts from the Grothendieck Circle copies, same as the GGA 1 volume). Supported: written January 1984; work "in 1977 and 1978" (late 1970s); realisation over any field and any base ring; pinned polyhedra; universal formulae in n parameters, "the doubles of the cosines of the 'fundamental angles'" (English translation wording); the icosahedron specialised to finite fields "remains an icosahedron", with the simple group of order 60; characteristics 2 and 5 "the most singular" for the icosahedron; the centre sent off to infinity in characteristic 2; footnote on pseudo-polyhedra with n + (n+1) variables; existence and uniqueness of a circumscribed hyperquadric, and the footnote linking exceptional characteristics to a degenerate hyperquadric or one tangent to the hyperplane at infinity. The last three were added to the article with \cite[\S4]{esquisse}.
6. Fisher-Jamison: cited only for the link between diagonals of affinely regular polygons and Chebyshev polynomials of the second kind, as stated in the zbMATH review and in Korchmaros-Szonyi section 3.

## Unresolved

- Coxeter 1973: edition data not confirmed by an API (zbMATH has the 1948 and 1963 editions only).
- Monson-Schulte: body not read.
- No search was made for prior descriptions of the icosahedron modulo 5 as a conic of PG(2,5); the article's sentence is phrased as "we do not know a printed source".
