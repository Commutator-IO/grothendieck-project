# Bourbaki rédactions: facts for the RHM article

Sources: local transcriptions transcripts-bourbaki/*/batch-*.fr.tex (git-ignored, rights pending with AHP/ACNB, #50). All are first machine passes (Opus 5.5, 2026-10-10/18), none checked against the facsimile. Pages are PDF pages (the transcription's `\page{}`). Dates are the AHP notice's unless stated. Congress presence comes from src/content/bourbaki-skim.json (AHP item numbers in brackets). Article read at HEAD 415d974 (it already includes the absence from Sept 1960 to July 1962 and from 1966 to 1970).

Quotations are kept to a few words because of the rights question.

**Status labels.** NEW: the article does not say it. EXTENDS: the article touches the topic, and this adds a document, date or page. **Strength.** DIRECT: read on the typed page. INFERENCE: depends on a comparison or a date.

Corpus size: 15 documents, 485 typed pages. 457 has 142 pages, 262 has 100, 245 has 50, 243 has 41, 288 has 38, 346 has 31, 222 has 16, 417 has 18, 307 and 327 have 12 each, 455 has 8, 433 has 6, 443 has 5, 383 bis and item 999 have 3 each.

---

## A. The best facts, ranked

### 1. Stacks in 1956: the « catégorie locale » of 243. NEW, DIRECT
- **Where:** n° 243, « Esquisse du chapitre I du Livre de Topologie Élémentaire », July 1956. The archival hand on p. 1 reads « Grothendieck juillet 1956 ».
- **Pages 11–12, the « catégorie pré-locale ».** Over the opens of a space X he defines a system of categories with restriction functors, transitivity isomorphisms and a commuting square of coherence. In current terms this is a pseudo-functor, i.e. a prestack.
- **Pages 15–16, the « catégorie locale ».** He adds two axioms: « recollement des morphismes » and « recollement des morceaux ». The second carries the cocycle condition on triple overlaps. This is the definition of a stack over a topological space.
- **Same document:** on p. 2 the « mécanisme algébrique essentiel des fibrés » is H¹(X, G) for a sheaf of groups, abelian or not. § 14, « Où on tord les faisceaux structuraux » (p. 37), twists F by a class c ∈ H¹(X, H) to define the second coboundary into H², and refers to « le rapport Kansas ».
- **Later in the fonds:** the same word « catégorie locale » appears in cote 45 (lot 1, p. 11–12; inventory 1961–[vers 1970]), on noyaux and H² with values in Nor(φ), i.e. Giraud-type nonabelian H².
- **Serves:** 6.1 De l'objet à la catégorie des objets; 6.3 L'homotopie (champs); 7.1 (champs de Picard, 1974).
- **Claim it supports:** the stack notion that the article meets in 1974–1975 (Breen letters) and 1983 is already defined, with gluing axioms, in a 1956 Bourbaki rédaction.
- **Caution:** do not assert priority. The 1955 Kansas report and its reception would have to be checked first.

### 2. « Algèbre homologique non commutative » already in 1956. NEW, DIRECT for the wording, INFERENCE for the continuity
- **1956:** n° 243, p. 3 (July 1956). Having noted that H⁰ and H¹ of a group with coefficients in a nonabelian group run parallel to the sheaf case, he suggests « un paragraphe d'algèbre homologique non commutative, dans des classes plus … ». He offers to write « un petit rapport ».
- **What the article has:** it quotes the same phrase only from cote 135, c. 1974 (§ 6.6, lot 135/3/44).
- **1975 in the fonds:** the phrase also occurs in 134-2, lot 3, p. 42 and p. 46 (letter to Breen, 1975). There he wants a theory linking topos, semi-simplicial sets and n-categories. He doubts the name will last and suggests « algèbre topologique ». It also occurs in lot 7, p. 126.
- **What changes:** the name lasts twenty years. In 1956 it meant nonabelian H¹ and exact sequences. In 1975 it means n-stacks.
- **Serves:** 6.6 De petits invariants, and 6.1.

### 3. A species of structure is a functor on bijections (1956). EXTENDS, DIRECT
- **Where:** n° 243, § 2 « Digression sur les structures », pp. 7–11. Note also p. 4: the notion of functor « me semble donner une façon très maniable de définir les structures ».
- **The definition (pp. 7–9):** a species of structure T is a covariant functor from sets-with-bijections to sets. Subordination of species is a morphism of functors, and equivalence of species is an isomorphism. He criticises Bourbaki's échelle de construction (the published Ensembles IV) as « péniblement explicité » and says it takes great pains « rien que pour avoir le droit de parler de transport de structure ».
- **Generalisation (pp. 9–11):** species of structure on any category, the category C_T of structured objects, and a classification. The indecomposable species on C(A) correspond to subgroups of Aut A up to conjugacy. This is a Galois-type correspondence.
- **Same idea in 262:** n° 262 (April 1957), p. 4, calls a topological category's functor a « espèce de structure » (Ens. IV).
- **Link to the fonds:** 161-2 (the article: « une espèce de structure est une recette, et son topos … »).
- **Serves:** 6.1. The article says the « object → category of objects » move is a commonplace that the drafts let one date. This dates the structure-as-functor version to July 1956, against Bourbaki's own text.
- **Caution:** do not attach Joyal's later « espèces » to it as an attribution. If mentioned at all, mention it as a resemblance only.

### 4. The fundamental group of a field and the anti-equivalence Et(k) ≃ Ensf(G)° (Oct. 1965). EXTENDS, DIRECT
- **Where:** n° 457, « Projet de réédition d'Algèbre, chap. V », October 1965 (AHP). It sits in § 8, n° 7, set between asterisks (pp. 76–86).
- **p. 76:** Définition 6 defines π₁(k, Ω) as the topological Galois group of the separable closure.
- **p. 78:** the category Ensf(G) of finite admissible G-sets.
- **pp. 78–81:** quasi-inverse functors φ, ψ, then Théorème 5, the anti-equivalence between étale k-algebras and Ensf(G).
- **pp. 82–83:** galoisian algebras correspond to principal homogeneous spaces (with his aside « (brrr) », p. 82). Pointed galoisian algebras give H¹(k, Ω; Γ) ≅ Hom cont(G, Γ) (cor. 5–7).
- **p. 84:** π₁ « proreprésentant » the functor H¹(k, Ω; Γ). An exercise on axiomatic Galois theory in categories, « cf. SGA V et SGAD X 7.5 ».
- **p. 86:** functoriality of π₁ and the « Autocritique du rédacteur » (fact 5).
- **p. 4:** the notion « dont l'importance n'est apparue que dans les dernières années, ce … ».
- **Links to the fonds:** pointed torsors in the 1959 letter to Serre (29/7/124–130, « fibrés principaux pointés »). Pro-representability of π¹(S, ξ; π) and descent data in 29, lot 9, pp. 169–179 (cote 1959–1969, undated leaves).
- **Serves:** 6.4 Le groupe fondamental, between 1959 (letter) and 1967 (SGA 1/Murre).
- **Check before use:** whether the printed Algèbre V (1981) keeps étale algebras and their Galois classification. That would make 457 the origin of a printed section; it has not been checked here.

### 5. « Autocritique du rédacteur »: arguing against his own text (457, p. 86). NEW, DIRECT
- **The passage:** he admits one understands less well than if one could « renverser les flèches et parler de schémas étales ». Galois theory would then be the theory of coverings, and the H¹ « petits bouts » would fit into general cohomology.
- **The objection he raises himself:** one could « vider purement et simplement » the fundamental group and wait for a geometric language.
- **His conclusion:** fields deserve a separate treatment, the only work being to line up the functorial sorites « dans un ordre pigeable ».
- **p. 86, same page:** he stops short of the full functoriality sorite, trusting that « Bourbaki peut se faire une idée suffisamment nette ».
- **Serves:** 5.3 L'erreur sur la page and 5.6 (how he defends a plan). This is self-criticism addressed to a collective.

### 6. A plan revised inside the same typescript (457). NEW, DIRECT
- **First plan, pp. 3–6:** « Commentaires sur le plan », a 13-paragraph plan with Leitfaden (§ 9 norms and traces; § 11 radicial; § 12 Mac Lane; § 13 differentials).
- **Revised plan, p. 87:** headed « (suite et fin) ». « Contrairement à son intention première », he dropped the paragraph on radicial algebras after « une rédaction au brouillon », judging it better placed in algebraic geometry. The plan becomes §§ 7–11.
- **What he left undone:** he did not redo § 9 (the § 9 of this plan, roots of unity and Kummer), and gave only a plan for § 11 « au Maître », « inspiré par EGA 0_IV par. 18 à 21 ». This explains the « § 9 absent » noted in PROGRESS-long.md.
- **What survives:** both plans stay in the document, as the restarts in the fonds stay beside what replaces them.
- **Serves:** 5.2 Recommencer sans effacer, in collective work.

### 7. The reader of 457: verdicts and their placement. EXTENDS, DIRECT for the readings, INFERENCE for the dating
- **The hand:** one unidentified ink hand on the ENS copy, dense on pp. 3–44 and sparse after.
- **Approvals:** about twenty, such as « Oui », « Vrai », « TB » (p. 4), « Ce serait fort bien » (p. 5), « bonne remarque » (p. 43).
- **Objections:** about ten. « Bien long ! » (p. 8). « Non » and « Contradictoire ! » against calling a polynomial « étale » (pp. 23–24). « On garde « séparable » pour les corps » (p. 26). « Non !! » (Prop. 12, p. 27). « faux en dim. ∞ » (p. 33). « Non ! » (p. 136). « Idiot | la dém. Bbki est meilleure » (p. 138), against his alternative proof of Dedekind–Artin independence.
- **An exchange:** he writes he has never used the theorem of algebraic independence (p. 14). The reader answers « CC s'en est servi », probably Chevalley.
- **Other people named:** Bruhat in the third person (p. 7, « Bruhat ne veut pas confuser le lecteur », reading doubtful). « le soutien à Cartier ne se dérobe point » (p. 43, doubtful).
- **Placing the reading:** on p. 10 the reader writes « La majorité est d'accord mais moi je m'en fiche » (end doubtful). This records a group vote, so the annotations were most likely made at or after a congress discussion. Congress n° 66 of 27 Sept. 1965 [831], where he was absent, set the reading of his recast of Algèbre V and VIII for March 1966, « avec un certain effroi ». The next congress is n° 67, Cargèse, 13–20 March 1966 [832]; he is not on its list, and the body of that report has not been skimmed.
- **Hypothesis to check:** these notes come from the Cargèse reading, in his absence. Reading the body of report 832 would settle it.
- **Serves:** 5.6 (reception), and a counterweight to « effroi ». The group reads him closely, approves most detail changes, and resists his terminology (étale, séparable) and some of his proofs.

### 8. 455: the « effroi » project, and the archive's date. EXTENDS, DIRECT for the text, INFERENCE for the identification
- **The date:** the ink mention on p. 1 reads « Archives Grothendieck – sept. 1965 ». The AHP notice gives octobre 1965.
- **The proposal (p. 3):** to « interchanger purement et simplement » Chap. V (Corps) and Chap. VIII (semi-simple modules and rings). The latter should come right after Chap. IV, against « le peu d'intérêt pour le « non commutatif » ».
- **Tone:** p. 1, « Par un reste de fidélité à sa vocation première » and « malgré la résistance de certains ». p. 4, the change is no more « sacrilège » than those already made in Chap. II–IV.
- **The identification:** this is plausibly the « projet de refonte d'Algèbre V et VIII » that report 831 (27 Sept. 1965) expects « avec un certain effroi ». It is a recast of both chapters, sent in September.
- **A link to the fonds:** the same weeks give the letter to Dieudonné of 29.9.1965 with the plan of EGA IV §§ 20–27 (25/7/134, in the article). That makes two plans for two treatises in September 1965, then 142 typed pages (457) in October, and the Alger letter to Mumford on 1.11.1965.
- **Serves:** 5.6, 5.9 Rythmes, and 4 Dater (the notice vs page discrepancy).

### 9. 222 (July 1955): his doubt about higher Zariski cohomology, and an uncorrected slip. NEW, DIRECT
- **The doubt (p. 15):** for the « bons » Hᵖ on any space, « notamment une variété algébrique avec la topologie (non séparée) de Zariski », « il n'est pas sûr qu'ils offrent le moindre intérêt » outside p = 0, 1, 2. Serre's results show only that the coherent class has a remarkable cohomological functor.
- **His uncertainty about the axioms (p. 7):** he is « pas absolument certain » that C₁–C₃ are the best axioms.
- **A joke (p. 14):** Čech cohomology is Hᵖ_m, « m, initiale de m…auvaise ».
- **The slip (p. 12):** the Corollary swaps the conditions of the Theorem of p. 11. It asks effaçable for i < 0 and coeffaçable for i > 0, the reverse of the theorem. No hand corrects it on the ENS copy.
- **Placement:** the archival hand reads « Juillet 1955 Grothendieck ». Congress n° 36 (27 June–9 July 1955) [1193] read it « avec enthousiasme » with him absent: his first listed attendance as a member is Oct. 1955 [801]. 243, p. 2 says his fibre-space report was written at the University of Kansas.
- **Serves:** 5.3 L'erreur sur la page (a doubt later refuted by his own work), and 5.6 (the article does not say the 1955 reading happened in his absence).

### 10. The rédacteur's voice, and how long the texts are. EXTENDS, DIRECT
- **The third-person « le rédacteur »** confesses, refuses and delegates:
  - 262, p. 2: « le rédacteur a fini par se dégonfler », and no effort « en direction d'un style canonique ».
  - 262, p. 56: « qui en a marre de faire le travail des autres, … ».
  - 262, p. 83: he has not copied the proof he wrote « pour lui-même par acquit de conscience ».
  - 262, p. 46: he leaves a notion « à son successeur » while using it.
  - 288, p. 35 (May 1958, counter-draft): he will not copy a theorem that « sera probablement vidé ». The remarks after it are made to impress « un lecteur sans malice », and remark 3 is « sans doute fausse ».
  - 288, p. 33: « Je suspecte qu'il est faux si E n'est pas séparé, Dieudonné exercicera ».
  - 245, p. 2 (June 1956): « Le rédacteur est convaincu » that the Krull–Remak–Schmidt theorem must be kept, with numbered reasons.
  - 417, p. 2 (June 1964): « Conformément aux instructions reçues ».
  - 307, p. 8 (Nov. 1958): he will take the Kuratowski pair « pour éculé et pisseux que ce soit ».
- **Omissions he admits inline:** 346, p. 8 and p. 25 (Sept. 1960), « [J'ai oublié de préciser …] » twice. 262, p. 32: « On a oublié … de préciser ».
- **Length:** 457 gives 142 typed pages to one chapter and 262 gives 100 pages to « Préliminaires » alone. Report 806 (June 1957) found 262/270 « too much algebraic geometry » (skim).
- **Serves:** 5.2, 5.3, 5.6.

### 11. Universes: 307 (Nov. 1958), then the Galaxies letter (433, Jan. 1965). EXTENDS, DIRECT
- **307 (Nov. 1958).** Axioms for Universes. p. 9: U₁ contains every object defined so far, « le rédacteur étant le premier » to define one not in it (U₁ itself). p. 10: the axiom (A 6), « l'axiome gratuit » or « l'axiome d'épuration », says every object lies in some U_n. p. 7: he would rather do without Hilbert's τ. On the Cartier copy, « par Alexander Groth. » is in an unidentified hand.
- **433 (21 Jan. 1965), to Samuel:**
  - Samuel's « Galaxies » might do for ordinary mathematics, but would force big categories to carry antifilters of subcategories.
  - Universes stay « plus proche de l'intuition naïve ».
  - He proposes test texts: « Tohoku, SGAD I et IV, SGAA I, II, III (les … ».
  - He urges deciding before Chevalley and Gabriel finish their book on categories. « si j'étais Bourbaki », he would free Samuel for the Galaxies « à temps complet ».
- **Sequence in the skim:** report 826 (March 1964) cites the « vieux papiers Grothendieck et Samuel », probably 307 and 307 bis. Report 829 (March 1965) does not adopt the axiom. N° 453 (Sept. 1965): Sabbay shows it implies well-foundedness. Report 831: to be rediscussed « en présence de Grothendieck ».
- **Links to the fonds:** the sigla SGAA and SGAD are those of the fonds. SGAA occurs in 23/4/79 and 33/4/75; SGAD in 6, 10, 16, 26, 48 and 102.
- **Serves:** 5.7 Écrire à quelqu'un (a letter that argues against his own axiom's rival without dismissing it). It gives substance to the article's single line « son axiome des univers n'est pas adopté ».

### 12. Fredholm: cote 1 (1953) → his paper (1956) → n° 417 (June 1964). NEW, DIRECT for each piece, INFERENCE for the thread
- **417 (June 1964), « Déterminant de Fredholm »,** a plan for a Bourbaki chapter.
  - He refers to his own Bull. SMF paper as « l'article de Grothendieck » and « T. F. ».
  - He also writes « Dans T. F. le rédacteur a donné… » (p. 6) and « que je me dispense de recopier » (p. 14).
  - The most interesting Fredholm operators are « probablement » those in nuclear spaces. « Dieudonné s'en fera sans doute un plaisir » (p. 2).
- **Cote 1 (1953) in the fonds:** already has « Caractérisation des op. de Fredholm » (1/2/39 and lot 3) and « Produits extérieurs hilbertiens » (lot 3, pp. 58–60). These are the Λⁿ and trace-class tools of 417.
- **The 417 annotations:** in the hand of the Cartier copy (initials « PC », p. 2). « Catégorie Fred et foncteur dans la catégorie des Banach » (p. 9). A doubtful « Congrès » (p. 10) suggests a congress reading; 417 is dated June 1964 and he attended n° 62 (25 June–8 July 1964) [827].
- **Serves:** 6 (a subject kept for eleven years), 5.6, and 6.8 (self-citation in the 1960s).

---

## B. Further facts

13. **327 (Sept. 1959), « Extrait du multiplodoque Grothendieck. § 4. Anneaux adiques ».** In the same month the letter to Serre (29/7/129, Aug. 1959) says « le multiplodoque devrait être fini d'ici 3 ans, ou 4 au maximum ». Report 824 (June 1963) speaks of « chap. IV du Multiplodoque » (skim, doubtful). The Bourbaki nickname for EGA is shared between the group and his private letter. The content matches EGA 0_I § 7 « Anneaux adiques » (1960), which is an inference not checked here. NEW, DIRECT. Serves 6.8 and 5.6.

14. **346 (Sept. 1960), Pic(A).** p. 14: Pic(A), « groupe de Picard de A (ou groupe des classes de … ». A starred remark then gives the sheaf reading: M̃ is locally free on Spec(A), and Pic(A) is the set of classes of invertible sheaves, i.e. H¹(X, O_X^*) (the report-815 annex). Placement: report 815 (June 1960; present) read his § 5 « Modules projectifs » and printed it in annex. 346 is the rédaction that follows, written as his absence from the congresses begins (Sept. 1960). Whether the printed Alg. Comm. II § 5 (1961) kept « Pic » and the name should be checked. NEW, DIRECT. Serves 5.6 and 6.1.

15. **Rédactions sent while absent (Sept. 1960–July 1962):** 346 (Sept. 1960). 383 bis (undated, comments on n° 383 of May 1962) asks for a table of automorphisms of Dynkin diagrams, « constamment » needed « dans les questions de H¹ des groupes semi-simples ». On the definition of root systems he writes « je préfère une rédaction antérieure ». NEW, DIRECT for the texts, INFERENCE for the date of 383 bis. It adds to the article's sentence on the six congresses missed: written contributions continue.

16. **262 (April 1957).** The archival hand reads « Archives. Grothendieck. Avril 57 ». p. 57 foresees building « des catégories de variétés arithmétiques (tels les schémas de Chevalley) » from small pieces. pp. 16–17: Chevalley's quotient variety, whose condition is « assez canularesque ». Placement: commissioned at the congress of March 1957 [805] as the « Diplodocus des variétés » for June 1957, and discussed in June 1957 [806], so April falls between. NEW, DIRECT. Serves 4 (archival date consistent with the congress sequence) and 6.1.

17. **The archival hand.** Undated ink mentions in one unidentified hand, top left of the ENS copies: 222 « Juillet 1955 Grothendieck », 243 « Grothendieck juillet 1956 », 262 « Archives. Grothendieck. Avril 57 », 455 « Archives Grothendieck – sept. 1965 ». The AHP notices take their dates from them, and in 455 misread « sept. » as octobre. 457 (ENS copy) has no such mention: its date « octobre 1965 » is the notice's. The 455/457 sequence holds: 455 says he is « en train de préparer » the Chap. V project. DIRECT, except that whether it is one hand is an INFERENCE to check on the facsimiles. Serves 4 (inventories as layers of dating, here the AHP's own), as a parallel to Montpellier.

18. **443 (June 1965).** p. 2: « Je propose de vider la terminologie » of separable algebras, keeping the name for « universellement réduit ». p. 3: refers to his own talk, « Grothendieck, Le Groupe de Brauer, Séminaire Bourbaki Mai 1965 », in the third person. p. 4: the definition of similarity « qui se globalise bien ». p. 5: « Consulter Serre sur un programme raisonnable ». The article already says the 1972 plan starts from 443. EXTENDS, DIRECT. Serves 5.6 and 6.8.

19. **245 (June 1956).** « Aux commentaires de la Tribu, le rédacteur ajoute… » (p. 1). He defends the Krull–Remak–Schmidt theorem: if Bourbaki leaves it out here, « il n'en parlera pas non plus ailleurs » (pp. 2–3). He calls a numéro « demandé par Borel » foreign to the chapter's spirit (p. 29). On p. 36 he admits he does not know whether an inclusion is an equality. Link to the fonds: 10/9/180, « groupe ordonné des classes indécomposables… d'après Krull–Schmidt », in a « classe abélienne ». NEW, DIRECT. Serves 5.6 and 5.3.

20. **The vocabulary of 1955–1956 in the fonds (a dating hint).** « classe abélienne » is the term of 222 (1955) and 243 (1956), where Tôhoku (1957) says « catégorie abélienne ». Cote 10, dated [à partir de 1958] by the inventory, uses « classe abélienne » on 10/8/156 (« Classes abéliennes de k-modules et algèbres topologiques ») and 10/9/180. This suggests, without proving, that these leaves may predate the inventory's bound. He could also have kept the old word. INFERENCE, weak; check the handwritten reading on the facsimile first. Serves 4.2–4.4.

21. **Item 999, « La condition de Mittag-Leffler »** (undated, Cartier papers). Report 811 (March 1959) refers to « un bout du Mittag-Leffler de Grothendieck » for n° 314 (projective limits). So item 999 probably dates from c. 1958–1959. Mittag-Leffler conditions recur in the fonds (7, 31, 43, 57, 62, 128). INFERENCE. Serves 4.

22. **Cross-references to EGA and SGA.** Only 457 cites EGA (11 times, all EGA 0_IV §§ 19–21, e.g. 20.5.7, 21.2.3, 21.4.5, pp. 111–120) and SGA (« SGA V », « SGAD X 7.5 », p. 84). It says the differential sorite cannot be given « dans Bourbaki faute de disposer de la notion voulue » (p. 111). 433 cites SGAD and SGAA. No rédaction before 1965 cites his own treatises except 417 (T. F., 1956 paper). DIRECT. Serves 6.8: in 1965 the printed EGA 0_IV (1964) becomes, for Bourbaki too, a store of lemmas and exercises.

23. **Names cited in the rédactions,** as persons and not eponyms:
   - Serre: 222, theorems on coherent sheaves and « classes » of abelian groups; 443, « Consulter Serre ».
   - Cartan: 222, « séminaire Cartan »; 262, « Cartan-Sammy ».
   - Chevalley: 243 and 262, « rapport Chevalley », « séminaire », « schémas de Chevalley »; 433.
   - Dieudonné: 288 and 417.
   - Samuel: 433, and « Sammy » in 262.
   - Others named once: Borel (245), Gabriel and Verdier (433), E. Artin's referee report on the Algebra book (455, p. 2), Koszul (245, « la jolie démonstration de Koszul »), Weil (243, « th. de Weil » joke; 457, « extension régulière »), Cartier (457, « égalité de Cartier »), Buchsbaum (262, p. 14).
   - The reader of 457 adds Bruhat and « CC ».
   - EXTENDS. Serves 6.9: the Bourbaki milieu of 1955–1965 is the same as the fonds' 1960s interlocutors (Serre, Dieudonné, Verdier).

24. **Comparison with the printed Bourbaki.** He measures his text against it explicitly:
   - 457, p. 4: the essential change is the emphasis on algebras rather than extensions, made necessary by change of base field. Separable and perfect closures « ne figuraient pas dans Bourbaki ».
   - 457, p. 5: tensor products of fields are treated « très imparfaitement par Bourbaki ».
   - 457, p. 88: « Critères de séparabilité de Mr. N. Bourbaki et de Mac-Lane ».
   - 455, p. 2: a proof in the printed text « semble bien abracadabrant ».
   - 288, p. 2: the separation condition in precompactness is « un carcan inutile ».
   - DIRECT. Serves 5.6.

---

## C. Readings to check on the facsimile before use

- 457 marginals: « vivable » (p. 3), « confuser » (p. 7), « moi je m'en fiche » (p. 10), « soutien » and « dérobe » (p. 43), « Bonne raison » (p. 16), « certain » (p. 42). 17 \uncertain in batch 1, 5 in batch 2.
- 417 marginals: « Alfred » (p. 8), « Congrès » (p. 10). The struck 1/n! in (15) (p. 6). 13 \uncertain and 7 \ill in all.
- 455 p. 1: « sept. » against the notice's « octobre ».
- 222 p. 12: the swapped effaçable/coeffaçable is typed. Check that no faint correction exists.
- 243 pp. 11–16: typed and clear, but the copy is « faint, blurred ». Check the gluing axioms (ii) and the triple-overlap condition word by word before building fact 1 on them.
- 10/8/156 and 10/9/180: « classe abélienne » (handwritten, fonds).
- 346 p. 14: « vomi par Bourbaki » (typed). The starred remark carries an \add of uncertain origin (p. 31 note).
- Whether the archival mentions on 222, 243, 262 and 455 are in one hand.
- Not verified here: whether the printed Bourbaki Algèbre V (1981) has étale algebras and their Galois classification, and whether Alg. Comm. II (1961) uses « Pic ».
