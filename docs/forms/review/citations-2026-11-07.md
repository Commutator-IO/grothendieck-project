# Citation check — docs/forms/article.tex, 7 November 2026

Method: the Crossref REST API for each DOI; the zbMATH Open API for series data; the HAL deposit of Courcelle's paper (full text read); a public copy of the French *Esquisse* for its table of contents; Crossref chapter DOIs for the chapter titles of van den Dries. The RAIRO site answered with a bot challenge, which was not bypassed; the HAL deposit is the published version (it carries the RAIRO citation and DOI).

## 1. Courcelle 2020

- Crossref `10.1051/ita/2020007`: "Betweenness of partial orders", B. Courcelle, *RAIRO - Theoretical Informatics and Applications* 54, article 7, 2020, EDP Sciences. The bibitem matches.
- Full text: HAL `hal-03078856` (https://hal.science/hal-03078856v1). Received 20 April 2020, accepted 19 November 2020.
- In-text claim, before: "studied by Courcelle [§1, Th. 7]". **Wrong locator.** There is no Theorem 7. Section 1 is the introduction and only announces the result. The reconstruction theorem is **Theorem 3.5** in §3: (1) two B-minimal connected posets with the same betweenness are equal or mutually reverse; (2) a poset with at least 3 elements is reconstructible up to reversal iff it is connected and strongly B-minimal, or has one isolated point and one other component with no extremal elements. Definitions 3.1(c)–(d): B-minimal means every comparable pair lies in a 3-chain; strongly B-minimal means every minimal x and maximal y with x < y have some z strictly between them. A dense poset is strongly B-minimal.
- The axiomatisation is credited by Courcelle to J. Lihová, *Strict-order betweenness*, Acta Univ. M. Belii Ser. Math. 8 (2000) 27–33 (his ref. [10]).
- Fix applied: cite `[Th. 3.5]`. The article now says what the theorem gives here: a dense poset with at least three elements and connected comparability graph, for example a dense poset directed both ways, is determined up to reversal by its strict betweenness alone. Lihová is named as Courcelle's source, with no separate bibitem because her paper was not checked.

## 2. Grothendieck, *Esquisse d'un programme*

- Crossref `10.1017/CBO9780511758874.003`: "Esquisse d'un Programme", A. Grothendieck, in *Geometric Galois Actions*, Cambridge University Press, pp. 7–48, issued 1997. The bibitem matches. zbMATH (API, document search) gives the series, *London Math. Soc. Lecture Note Ser.* 242, with the editors Schneps and Lochak, and the English translation on pp. 243–283 of the same volume. zbMATH gives the French text's pages as 5–48 where Crossref (publisher metadata) gives 7–48; the article keeps the publisher's 7–48.
- Claim that the Esquisse discusses tame topology. Confirmed: §5 is titled « Haro sur la topologie dite "générale", et réflexions heuristiques vers une topologie dite "modérée" », and §6 « "Théories différentiables" (à la Nash) et "théories modérées" ». Source: the French text at webusers.imj-prg.fr/~leila.schneps/grothendieckcircle/EsquisseFr.pdf, table of contents.
- Fix applied: the introduction now says "Section 5 of the *Esquisse*".

## 3. van den Dries 1998

- Crossref `10.1017/CBO9780511525919`: *Tame Topology and O-minimal Structures*, L. van den Dries, Cambridge University Press, 1998. *London Math. Soc. Lecture Note Ser.* 248, confirmed by zbMATH (ISBN 0-521-59838-9, x+180 pp.). The bibitem matches.
- Chapter titles (Crossref chapter DOIs `.005`–`.008`): Ch. 1 Some elementary results (pp. 11–30); Ch. 2 Semialgebraic sets (31–42); Ch. 3 Cell decomposition (43–62); Ch. 4 Definable invariants: dimension and Euler characteristic (63–78).
- New in-text uses (added for the semialgebraic example in Section 6): closure and finiteness of connected components → Ch. 2 and 3; dim(cl S \ S) < dim S → Ch. 4. The chapter locators were checked against the chapter titles. The theorem numbers inside the chapters were not checked, so none are given.
- The introduction's claim, "O-minimal structures have since given one answer", is general and fits the book's subject; it is kept.

## Not added

The peer-review skill asks for a citation of its own source paper when it "materially contributed". It is not a mathematical source for this article, so it was not added to the bibliography; the AI statement already discloses the use of language models.
