# Readings of folder 12 to check on the facsimile (2026-11-10)

Issue #66, last item. Each bullet is one place of folder 12 (*Motifs*, pp. 22–94, batches 2 to 5) where our
transcription has one reading and another reading is possible. Nothing here has been checked by a person and
nothing has been changed in `transcripts/`: each alternative is another possible reading, to check on the
facsimile (https://grothendieck.umontpellier.fr/12.pdf, PDF page = archive page + 1).

`scripts/review-queue.mjs` reads this file, one item per open box, as kind `uncertain` (« Doubtful reading »),
with the id `reading-12-<batch>-<line>`. The bullet's format is:

`- [ ] <cote> p<pages> batch-<NN>:<line> | reading | <where on the page, what to look at> | <our reading> | <alternative reading>`

`<pages>` is an archive page, a range (`p43–50`) or a list (`p56,58,70`); `batch-<NN>:<line>` is the line of
`transcripts/<cote>/batch-<NN>.fr.tex` where the place stands on 10 November 2026 (a letter after the line
number tells apart several questions on one line). The review page offers four answers: our reading is right,
the alternative is right, neither (with what the page has), cannot tell. Tick a box when its answer is applied;
the transcription then gains a `% Revised` line naming the issue that carried the answer.

162 questions: 5, 13, 144 in the three sections below.

On 10 November the readings that a second look at the page found sure were applied in `transcripts/12` (#66) and
their boxes ticked; where a question named a sure place together with likely ones, the applied place is ticked
and the rest stays open in a box of its own, so section 2 now has 20 boxes.

## 1. A letter or a word written the same way over several pages

Each of these is one question for all the pages it names: the answer is applied at every place.

- [ ] 12 p43–50 batch-03:134 | reading | the hooked letter multiplying M^+_{(i−1)}(K) etc. : is it the ξ defined on p. 36 ? | ζ | ξ
- [ ] 12 p47–49 batch-03:191 | reading | the invariant of pp. 47–49 : capital Γ or the γ of p. 46 ? | Γ^i, Γ_i | γ^i, γ_i (underlined)
- [ ] 12 p56,58,70 batch-03:355 | reading | the gothic letter for the Lie algebra | capital 𝔊 (and 𝔍 on p. 70) | lower-case 𝔤
- [ ] 12 p75,76,78 batch-04:439 | reading | exponent of A, and the words under the brace | « A^{tr} » ; « [illisible] de la V.A. A sur S » | « A^{fixe} » ; « partie fixe (points fixes) de la V.A. A sur S »
- [x] 12 p85–88,92 batch-05:188 | reading | the letter of the weight in § 17 and § 18 | p | ρ

## 2. Places where the alternative looked clear on the page

A first look at the page images found the alternative clear here, in whole or for one of the signs the question names.

- [x] 12 p22 batch-02:122 | reading | derived tensor product : an L above the ⊗, or strokes under it ? | « M ⊗^L N » | « M ⊗ N (⊗ underlined) »
- [ ] 12 p22 batch-02:122b | reading | the words after « M ⊗ N » | « pour M, N ∈ D^b » | « en M, N ∈ Ob D^b »
- [x] 12 p24 batch-02:176 | reading | target of T_ℓ in the displayed formula | « M_ℓ(X) » | « M_ℓ^+(X) »
- [x] 12 p24 batch-02:180 | reading | is « projectifs » on the page ? | « systèmes projectifs ℓ-adiques » | « systèmes ℓ-adiques »
- [ ] 12 p29 batch-02:306 | reading | parenthesis after « spectre d'un corps » | « (qu'on peut supposer si on veut, alg. clos) » | « (fini si on veut, ou clôture alg. d'un tel) »
- [x] 12 p34 batch-02:485 | reading | parenthesis after « on prend » | ([illisible]) | « (du moins pour X = Spec K d'un corps) »
- [ ] 12 p34 batch-02:485b | reading | the words around « X = Spec K » in the parenthesis, and the word after « filtration » | « (du moins pour … d'un corps) », words doubtful ; « minimale » | the same words, certain ; « minimum »
- [x] 12 p37 batch-02:609 | reading | sign after « on aura » | [illisible] | « = », i.e. « même »
- [x] 12 p42 batch-03:110 | reading | § 12, the letter after « groupe » | [ill.] | « K »
- [ ] 12 p42 batch-03:110b | reading | § 12, first lines | « le groupe … décomposition … par × » | « le gpe … découpage … pour ⊗ »
- [x] 12 p56 batch-03:362 | reading | word before « dans H^{2n−i} ⊗ H^i(n) » | « prolongée » | « Plongée »
- [x] 12 p58 batch-03:397 | reading | the adjective after « ses structures » | « structures habituelles » | « structures tensorielles »
- [ ] 12 p58 batch-03:397b | reading | the first sentence | « On peut par l'image provenir » | « On pense que l'image provient »
- [x] 12 p63 batch-04:184 | reading | NB, line 1 : the sign in the parenthesis | « (ou projectif lisse) » | « (= projectif lisse) »
- [ ] 12 p63 batch-04:185 | reading | NB, lines 2–3 | « [four words unread] telles relations précises » | « on n'a plus de telles relations précises »
- [ ] 12 p70 batch-04:294 | reading | the verb after « coeff. finis, on » | « on a » | « on trouve »
- [x] 12 p70 batch-04:319 | reading | the words before the last display | « Donc on a » | « De =, on trouve »
- [x] 12 p88 batch-05:296 | reading | is « d'ailleurs » on the page ? | « qui sont de la forme » | « qui sont d'ailleurs de la forme »
- [x] 12 p93 batch-05:449 | reading | first paragraph, after « cl H^{2n−1}_!(X, F) » | « [ill.] la [ill.] chose » | « mod la = chose »
- [ ] 12 p93 batch-05:449b | reading | two places in the first paragraph | « connexe de dim n » ; « donc [ill.] des données [ill.] » | « variété de dim n » ; « donc (purement ?) de poids 2n »

## 3. The remaining places, page by page

A first look at the page images found the alternative likely here; these are fast cursive, and the facsimile decides.

- [ ] 12 p22 batch-02:117 | reading | margin, top left : third line | « en tirer [illisible] les constructions des foncteurs » | « en termes des données construire des foncteurs »
- [ ] 12 p22 batch-02:133 | reading | words after « compatible avec ⊗ » : in the margin or in the line ? | « (Cond. de transitivité.) » in the margin | « [On a transitivité. » in the line
- [ ] 12 p23 batch-02:142 | reading | margin, first line | « le formulaire de dualité » | « la formule de dualité »
- [ ] 12 p23 batch-02:144 | reading | margin, last lines | « les formules d'Alexander reliant tous ces foncteurs » | « le formulaire standard reliant tous ces foncteurs »
- [ ] 12 p23 batch-02:151 | reading | two words after « filtrant » (twice) | « à morph. affines » | « ess. affine »
- [ ] 12 p23 batch-02:162 | reading | last two lines of the page | « X, Y [ill.] de t.f. sur S, [ill.] définis par … de la façon habituelle, si » | « X, Y de t.f. sur S sont définis par (X_i), (Y_i), si on prend des »
- [ ] 12 p24 batch-02:167 | reading | indices of f, X, Y on line 2 | « on a pour f_i : X_i → Y_i » | « on aura pour f_{i₀} : X_{i₀} → Y_{i₀} »
- [ ] 12 p24 batch-02:178 | reading | word between « catégorie » and « des » | (nothing) | « formée »
- [ ] 12 p24 batch-02:181 | reading | word after « négligeant » | [illisible] | « précisément »
- [ ] 12 p25 batch-02:186 | reading | margin top left, last line | « avec [illisible] etc. » | « avec résidu etc. » (and a short word, « hom » ?, after « f^! »)
- [ ] 12 p25 batch-02:202 | reading | margin, third line | « la chose triviale » | « le choix trivial » (or « le choix limite »)
- [ ] 12 p25 batch-02:203 | reading | margin : word before R^*f_* ; anything unread after « ℓ, » ? | « que R^*f_*… pour f, ℓ, [ill.] ce qui » | « qu'on ait R^*f_*… pour f, ℓ, ce qui »
- [ ] 12 p26 batch-02:222 | reading | is there a word between « échéant » and « (X sur Q) » ? | [illisible] | nothing
- [ ] 12 p26 batch-02:227 | reading | « connexes … » | « connexes et non vides » | « connexes non vides »
- [ ] 12 p26 batch-02:232 | reading | verb before « l'hyp « projectif » » | « oublie » | « enlève »
- [ ] 12 p27 batch-02:252 | reading | anything between « inductive » and « des » ? | « de [illisible] des » | « des »
- [ ] 12 p27 batch-02:255 | reading | end of the chain of M^+ | « → ⋯ » | a full stop
- [ ] 12 p27 batch-02:257 | reading | after « inversible, » | « d'inverse Q(1) [illisible] » | « soit Q(1) son inverse » ; and « pour » after « s'écrire, »
- [ ] 12 p27 batch-02:260 | reading | margin bottom left | « sous-catégorie pleine épaisse abélienne de M(X) ; [illisible] » | « une sous-catégorie abélienne épaisse de M(X) ; l'appartenance à M^+(X) se vérifie fibre par fibre … »
- [ ] 12 p28 batch-02:268 | reading | word before lim→ | [illisible] | « Pseudo »
- [ ] 12 p28 batch-02:269 | reading | sentence squeezed after the closing bracket | « T_ℓ s'étend à M(X), de façon unique à isom unique près, compatible avec ⊗. Les foncteurs [ill.] » | « Les foncteurs T_ℓ s'étendent à M(X), de façon unique, de façon à rester compatibles avec ⊗. »
- [ ] 12 p29 batch-02:313 | reading | words before the first boxed formula | « et on désire que » | « et je dis que l'on a »
- [ ] 12 p29 batch-02:317 | reading | exponent of Λ and the last word of the line | « Λ^n u, la formule » | « Λ^i u, le fait »
- [ ] 12 p30 batch-02:354 | reading | where does the small « sur Z » belong ? | « fibre sur Z par fibre » | « X de t.f. sur Z »
- [ ] 12 p30 batch-02:356 | reading | word after « (Pour » | [illisible] | « ceux-ci »
- [ ] 12 p31 batch-02:364 | reading | after the struck lines | « [ill.] compatible [ill.] f^* » | « Compatible avec f^* »
- [ ] 12 p31 batch-02:373 | reading | « sous-… » (twice) | « sous-quotients » | « sous-espaces »
- [ ] 12 p31 batch-02:375 | reading | is the Z before 1_X struck ? and the exponent of R | « R^i f_!(Z·1_X) » | « R^j f_!(1_X) », Z struck
- [ ] 12 p31 batch-02:379 | reading | opening of the bracket | « on sait que tout » | « au sens que tout »
- [ ] 12 p32 batch-02:405 | reading | verb | « permet de prolonger » | « peut se prolonger »
- [ ] 12 p32 batch-02:407 | reading | two words before « la filtration déjà » | « on ait » | « ce soit »
- [ ] 12 p32 batch-02:413 | reading | « … on prend j assez grand … que » | « si … tel que » | « où … pour que »
- [ ] 12 p33 batch-02:437 | reading | first line | « mais [illisible] par l'inclusion » | « mais on fera (fait) attention que l'inclusion »
- [ ] 12 p33 batch-02:455 | reading | sign before M_i(X)/M_{i−1}(X) | « = » | « ≃ »
- [ ] 12 p33 batch-02:458 | reading | word after « sont » | [illisible] | « tous »
- [ ] 12 p33 batch-02:463 | reading | words before « équiv. can. … à G_0(X) » | « on [illisible] » | « en particulier tous »
- [ ] 12 p34 batch-02:480 | reading | line 3 | « qui se loc. étale [(dans …, … fibre par fibre)] [ill.] objets » | « qui se dévissent loc. étale (du moins fibre par fibre) en objets »
- [ ] 12 p34 batch-02:501 | reading | left margin, first words | [illisible] | « cela distingue »
- [ ] 12 p35 batch-02:521 | reading | first word(s) of the page | « en utilisant » | « induisant »
- [ ] 12 p35 batch-02:526 | reading | after « pour j » | « qui [illisible] » | « grand »
- [ ] 12 p35 batch-02:540 | reading | opening of the parenthesis : the sense is reversed | « par une formule aussi simple » | « pas de formule aussi simple »
- [ ] 12 p35 batch-02:551 | reading | two letters before « tordu » (twice) | « est tordu » | « ct tordu » (constant tordu)
- [ ] 12 p36 batch-02:558 | reading | word before « cette catégorie » | [illisible] | « sur »
- [ ] 12 p36 batch-02:561 | reading | two short words before « une « catégorie tensorielle » | « C'est » | « On a »
- [ ] 12 p36 batch-02:572 | reading | is « libre » on the page ? | « est un Z-module libre admettant comme base » | « comme Z-module admet comme base »
- [ ] 12 p36 batch-02:575 | reading | after « injective » | « [illisible] des objets simples » | « sur l'ens. de ces objets simples »
- [ ] 12 p36 batch-02:578 | reading | after « résulte » | [illisible] | « du fait »
- [ ] 12 p37 batch-02:587 | reading | « on a(ura) … un diagramme … » | « on a … [illisible] » | « on aura … comm. »
- [ ] 12 p37 batch-02:594 | reading | sentence around Σ^+_{(i)}(X) | « M_i(X) se définit en termes [ill.] Σ^+_{(i)}(X) et Σ_i(X), d'une partie [ill.], d'où » | « M_i^+(X) se définit en termes d'une partie Σ^+_{(i)}(X) de Σ_i(X), d'où »
- [ ] 12 p38 batch-02:629 | reading | small words under M_0(X)[ξ] and over the ⊗ below | « (ξ de degré 1) », the rest unread | « de d° 0 » under M_0(X), « de degré 1 » under ξ
- [ ] 12 p38 batch-02:641 | reading | small formula at the right edge after « défini par » | [illisible] | « u, v ↦ ξ^{-1}uv »
- [ ] 12 p38 batch-02:644 | reading | anything between « classe » and « dans » ? | [illisible] | nothing
- [ ] 12 p39 batch-02:667 | reading | first word under the formula | « (donc on a » | « alors on a »
- [ ] 12 p39 batch-02:699 | reading | N.B., first line | « [ill.] on voit [ill.] la structure additive » | « Du pt de vue de la structure additive, »
- [ ] 12 p39 batch-02:701 | reading | word after « connaissance » | [illisible] | « de »
- [ ] 12 p39 batch-02:709 | reading | small note right of « les applications » | « x, y ↦ [ill.] définies par [ill.] » | « u, v ↦ uv, défini par »
- [ ] 12 p40 batch-02:721 | reading | two gaps in the sentence on the involution | [illisible], [illisible] | « de proche en proche » ; « sur σ_i »
- [ ] 12 p40 batch-02:722 | reading | verb, and the word after « théorie » | « résulterait de la théorie [illisible] » | « résultera de la théorie projective »
- [ ] 12 p41 batch-03:78 | reading | title, word before « géométriques » | « ou » | « Cas »
- [ ] 12 p41 batch-03:82 | reading | first line after the struck word | « une variété lisse sur le corps alg. clos » | « non singulière sur k alg. clos »
- [ ] 12 p41 batch-03:86 | reading | margin note, first word | « utilisation du » | « attention »
- [ ] 12 p41 batch-03:94 | reading | under the inductive limit | « U ouvert dense de x̄ » | « U ouvert ≠ ∅ de x̄ »
- [ ] 12 p41 batch-03:96 | reading | « On … que cette suite spectrale provien… » : known or wanted ? | « On sait que … provient » | « On veut que … provienne »
- [ ] 12 p41 batch-03:96b | reading | end of the parenthesis and the small insertion | « passer aux filtrations finies convenables … [en dehors de …] » | « prendre une filtration finie convenable … » ; insertion « en dim n » after « Le morceau »
- [ ] 12 p41 batch-03:96c | reading | margin right : « essentielle … si X de dim 1 » | « ! ou si » | « , même si » ; is « projectif » struck or underlined, and is « lisse » there ?
- [ ] 12 p41 batch-03:96d | reading | last sentence | « On voit que [ill.] [ill.] exactement » | « On veut que ce soit exactement »
- [ ] 12 p43 batch-03:120 | reading | after « σ cl(X), on » | « [illisible] les » | « a des »
- [ ] 12 p44 batch-03:152 | reading | « on trouve un(e) … dans Z^(…) … un invariant » | « un « type » » ; « i.e. » | « une image » ; « donc »
- [ ] 12 p45 batch-03:159 | reading | first words of the page | « i.e. des » | « où chaque »
- [ ] 12 p45 batch-03:163 | reading | underlined word after « la composante » | « primitive » | « bipure »
- [ ] 12 p45 batch-03:167 | reading | two places in the last paragraph | « le dual des H^j » ; « la composante primitive des H^j » | « la classe dans H^j » ; « la composante j-bipure dans H^j »
- [ ] 12 p46 batch-03:183 | reading | sign between the two terms of the bracket | « + » | a comma (the + is struck)
- [ ] 12 p47 batch-03:193 | reading | four places in the definition of the invariant | « on peut le supposer » ; « morphisme » ; « ([ill.] surjectif) » ; « comme on le sait bien » | « ce qu'on peut supposer » ; « hom. » ; « (donc surjectif) » under « propre » ; « comme il est bien connu »
- [ ] 12 p47–48 batch-03:196 | reading | the « Question » sentence | « On aimerait, pour deux … extensions de type …, … provenant d'un K-homom. » | « On aimerait que tout système d'homs … provienne d'un K-homom. »
- [ ] 12 p48 batch-03:199 | reading | first sentence | « R'[t_1, …, t_N] » ; « à des systèmes » ; « s'immerge » | « R'[δ_1, …, δ_N] » ; « et des (du) système(s) » ; « s'envoie »
- [ ] 12 p48 batch-03:201 | reading | words in the loop under « sur K alg. clos » | « ([ill.] [ill.]) telles que » | « (supposons que »
- [ ] 12 p48 batch-03:208 | reading | last bracket of the page | « Cast. ok ! » | « coh. alg ! »
- [ ] 12 p49 batch-03:212 | reading | verb | « Trouve-t-on » | « Trouvons-nous »
- [ ] 12 p52 batch-03:274 | reading | second paragraph | « voir » (twice) ; « permettent de décrire » | « via » (twice) ; « peuvent se décrire »
- [ ] 12 p53 batch-03:316 | reading | small N.B. between cases 1) and 2) | « des variantes de l'unité [… I 1 !] » | « des racines de l'unité [leur produit étant ±1 !] »
- [ ] 12 p54 batch-03:323 | reading | word before « caractériser » | « pouvons-nous » | « comment »
- [ ] 12 p54 batch-03:327 | reading | last two lines of the page ; are they struck ? | « Le cas général [ill.] [ill.], si on connaît tous les Frobenius [ill.] » | « Le cas général s'en déduit par image inverse, si on connaît tous les Frobenius ∈ π_1 »
- [ ] 12 p58 batch-03:399 | reading | the bracket on the « partie algébrique » ; is its last clause struck or underlined ? | « ce pro-motif n'étant lui-même autre … en tout autre cas, on … que Z(0) ! ; [struck] il paraît qu'il est une … » | « c'est tout – le pro-motif n'étant lui-même autre que Z(0) ! ; en tout autre cas, je pense qu'il est nul … »
- [ ] 12 p59 batch-03:406 | reading | exponents on lines 1, 4 and after the triangulated functor | R^i f_*, H^i(X,M) | R^* f_*, H^*(X,M)
- [ ] 12 p59 batch-03:418 | reading | 1°) | « lim essentielles filtrantes de préschémas à pr. quasi proj. affines » | « lim essentiellement affines de préschémas q.c. q.s. »
- [ ] 12 p59 batch-03:421 | reading | last word of the page | « est » | « de » (type fini, next page)
- [ ] 12 p61 batch-04:118 | reading | 3°), three lines | « on a [ill.] … et H^0 est exact [ill.] en M. De plus, dans fonctoriel » | « on veut que … donc H^0(X,M) est exact à g. De plus, isom fonctoriel »
- [ ] 12 p62 batch-04:140 | reading | the doubt on the Ext^i | « doutes pour les Ext^i (i>0) [ill.] pour être dans la catégorie des Ind-motifs ???] Possibles » | « doute que les Ext^i (i>0) soient [peut-être dans la catégorie des Ind-motifs ???] effaçables »
- [ ] 12 p62 batch-04:154 | reading | words above the struck line of 4°) | « bien le ℓ-foncteur » | « des hom de ∂-foncteurs »
- [ ] 12 p63 batch-04:179 | reading | verb | « on aurait » | « on aura »
- [ ] 12 p63 batch-04:189 | reading | « Le th. de Tate … en énonçant » | « peut se reformuler de façon précise » | « peut se reformuler et se préciser »
- [ ] 12 p63 batch-04:191 | reading | last formula : the small words by the arrow, and the twist of Q_X | label « ét. pr. Q_ℓ » on the arrow ; Q_X(i) | « pas Q_ℓ » pointing at Q ; Q_X(0)
- [ ] 12 p64 batch-04:196 | reading | lines 2–3 | « simplifiant les notations (f : …). Une autre façon de l'écrire » | « morphisme structural f : X → Spec k. Une autre façon est celle-ci »
- [ ] 12 p64 batch-04:220 | reading | last paragraph | « dans (X projectif …) » ; « c'est les cycles » | « alors (si X projectif …) » ; « ce sont les cycles algébriques à coeff. rationnels »
- [ ] 12 p66 batch-04:233 | reading | lines 2 and 4 | « (constructibles) » ; « par le couplage de motifs dualisants » | « (complexes de) » ; « pour le complexe de motifs dualisants »
- [ ] 12 p66 batch-04:236 | reading | the NB in brackets ; the circled word above the line | « est régulier de dim n, dans Q(n)[2n+1], c'est le dualisant à valeurs dans » ; circled « foncteur » | « est régulier partout de dim n, alors c'est la dualité à valeurs dans Q(n)[2n+1] » ; circled « partout »
- [ ] 12 p66 batch-04:245 | reading | phrase in quotation marks under R_!Γ_X(M^*) | « supposer qu'on sait que Z » | « support propre (compact) sur Spec Z »
- [ ] 12 p68 batch-04:264 | reading | first line | « cas choisi pour X = Spec Z, et lui-même le cas géométrique » | « = (même) énoncé pour X = Spec Z, et dans le cas géométrique »
- [ ] 12 p68 batch-04:277 | reading | two verbs | « en utilisant le foncteur » ; « Cela revient à » | « en appliquant » ; « Cela ramène à »
- [ ] 12 p68 batch-04:279 | reading | slanted margin note, left | « à développer au sujet des cup-produits à coeff. « abstraits » » | « à développer sans doute pour le cup-produit en cohomologie « absolue » »
- [ ] 12 p68 batch-04:283 | reading | the bracket | « pour un vectoriel [ill.] … sur lequel » | « pour des vectoriels … sur lesquels » ; hat on the Z ?
- [ ] 12 p70 batch-04:325 | reading | third case of the last formula | « [struck] si i = 2j+1, mais pas canoniquement isomorphe à … X/F̄ ! » | « id. si i = 2j+1, mais pas canoniquement en termes de X̄/F̄ ! » (or « X̄, K̄ »)
- [ ] 12 p70 batch-04:330 | reading | small N.B. bottom left | « Remplaçons k par [three words unread] l'isom. obtenu par lim » | « Remplacer k par k_n revient à multiplier l'isom obtenu par 1/n »
- [ ] 12 p72,73 batch-04:335 | reading | the same two short words after « motif » on both pages | [illisible] | « ct tordu » (constant tordu)
- [ ] 12 p73 batch-04:379 | reading | index of Q in R^1 f_* | « Q_A(1) » | « Q_{A^*}(1) »
- [ ] 12 p74 batch-04:390 | reading | is « pour » struck ? | « pour nous suggèrent » | « nous suggèrent »
- [ ] 12 p74 batch-04:396 | reading | line above the Kummer sequence | « Considérons [ill.] [ill.] (aux [three words unread] ×) » | « Considérons (pour ℓ premier aux car. résiduelles de X) »
- [ ] 12 p74 batch-04:403 | reading | place of ℓ^ν on the third term | after the parenthesis (cokernel) | under the left of H^1 (kernel)
- [ ] 12 p74 batch-04:412 | reading | adverb | « vraisemblablement » | « moralement »
- [ ] 12 p75 batch-04:419 | reading | first lines | « on a » ; sequence ending on a struck term | « on aura » ; « → 0 » before the struck term
- [ ] 12 p75 batch-04:443 | reading | letter in the middle term of the last sequence | « f_*(M) » | « f_*(A) »
- [ ] 12 p77 batch-04:482 | reading | parenthesis on line 1 | « donc le T_ℓ ou H^2 » | « dont le T_ℓ est H^2 »
- [ ] 12 p77 batch-04:491 | reading | two places | « sur S × S » ; « qui n'est pas nul » | « sur C × C » ; « qui est non nul »
- [ ] 12 p78 batch-04:504 | reading | underlined words right of the isomorphism | « sauf à noyau fini » | « surj. à noyau fini »
- [ ] 12 p78 batch-04:526 | reading | slanted note bottom left | « les seuls cas qui restent » | « les seuls invariants qui restent »
- [ ] 12 p81 batch-05:114 | reading | before the exact sequence | « alors » | « alors on a : »
- [ ] 12 p81 batch-05:132 | reading | the two lines under the Tate duality : is the second one struck, or underlined twice ? | both struck, fragments | first struck ; second « c'est donc essentiellement un p-groupe, … groupe fini ! OK. »
- [ ] 12 p81 batch-05:137 | reading | last sentence : a question or a statement ? | « Peut-on généraliser au cas d'une variété X régulière dont on enlève » | « Peut se généraliser au cas où on prend X régulier dont (auquel) on enlève »
- [ ] 12 p83 batch-05:141 | reading | word after « Calculs » | « sur » | « pour »
- [ ] 12 p83 batch-05:162 | reading | two places | « modèle [illisible] » ; « = fini » | « modèle can. » ; « = gpe fini »
- [ ] 12 p85 batch-05:187 | reading | first words | « Le théorème » | « La théorie »
- [ ] 12 p85 batch-05:205 | reading | sentence before « L^s(M). Noter » | « Soit ce que nous notons » | « Cet espace sera noté »
- [ ] 12 p86 batch-05:227 | reading | words above the struck ones ; is « fermé » struck ? | « on [illisible] L^s(M) un cône convexe [struck : fermé] » | « on a dans L^s(M) un cône convexe fermé »
- [ ] 12 p86 batch-05:234 | reading | slanted margin note | « sont dites positives » | « sont dites pseudo-amples »
- [ ] 12 p88 batch-05:289 | reading | first words of the paragraph | « En décomposant » | « Si on décompose »
- [ ] 12 p88 batch-05:298 | reading | heavy letter after ⊗_A and before « un vectoriel » | M | V (written over an M)
- [ ] 12 p89 batch-05:312 | reading | small word above the second struck word of line 3 | (nothing) | « rang » : « proj. de rang fini sur k »
- [ ] 12 p89 batch-05:321 | reading | head of line 7 | « Z-libre » | « gpe libre »
- [ ] 12 p89 batch-05:324 | reading | where does « k[t]/P k[t] » belong, and what is associated to P ? | « P en [ill.] [ill.]. À tout tel P, on associe : k[t]/P k[t]. (V, f), dont … » | « P en module k[t]/P k[t]. À tout tel P est associé un (V, f), dont … »
- [ ] 12 p89 batch-05:328 | reading | two short lines in the left margin | [illisible] | « k un corps ou non »
- [ ] 12 p90 batch-05:341 | reading | first line | « via la fonction car. modifiée » | « via le pol. car. modifié »
- [ ] 12 p90 batch-05:348 | reading | the looped insertion under R(N,k) → 1 + k[[t]]^+ : first word, and a minus sign in the denominator ? | « compatible avec … l'anti-« additif » φ(t) ↦ 1/φ(t) » | « composé avec l'aut. « additif » φ(t) ↦ 1/φ(−t) »
- [ ] 12 p90 batch-05:351 | reading | boxed margin note, lines 1–2 | « en fait, [illisible] les fonctions rationnelles » | « en fait, à valeur(s) dans les fonctions rationnelles »
- [ ] 12 p90 batch-05:357 | reading | the sentence after « En effet » | « la connaissance de la fonction rationnelle à numérateur 1 dans k[t] [ill.] facilement [ill.] » | « la connaissance de la série formelle permet de reconstituer la fonction rationnelle L, donc »
- [ ] 12 p90 batch-05:381 | reading | last lines | « on trouve inversement L par exp(…). D… » | « on peut inverser cet homomorphisme par exp(…). Donc »
- [ ] 12 p91 batch-05:397 | reading | after « la fonction L de » : is the long word struck ? | « (X, F) [struck word] à coeff. dans F, sur F_p » | « X, compactifiable sur F_p, à coeff. dans F »
- [ ] 12 p91 batch-05:402 | reading | three places in the lower half | « on considère cette fonction L comme l'image » ; « F vient d'un motif » ; « suivant les poids en » | « car essentiellement cette fonction L est l'image » ; « F est un motif » ; « suivant des poids en des »
- [ ] 12 p92 batch-05:415 | reading | the first words of the insertion above line 2 (its « de poids ρ » is settled), and the exponent of H (twice) | « F localement constant » ; H^i | « F constant tordu » ; H^{i−ρ}
- [ ] 12 p92 batch-05:420 | reading | two places | « donc on a la connaissance » ; « Frobenius dans ceux-ci » | « dans ce cas la connaissance » ; « Frobenius dedans »
- [ ] 12 p92 batch-05:444 | reading | slanted margin bottom left | « le poids [ill.] filtration [ill.] cf. N° 12 » | « le poids ici n'est pas la bonne filtration cf N° 12 »
- [ ] 12 p93 batch-05:463 | reading | slanted margin, top left | fragments « filtration … poids … niveau » | « peut se raffiner, en regardant une autre filtration que par le poids, savoir le niveau … »
- [ ] 12 p93 batch-05:466 | reading | the paragraph « Si F = Q_ℓ(0) » | « … [ill.] des fonctions ζ … est [ill.] équivalente : celle de π_0(X̄) comme [ill.] fondamentale » | « donc si on s'occupe des fonctions ζ … est essentiellement équivalente : celle de π_0(X̄) comme Frob-ensemble »
- [ ] 12 p93 batch-05:477 | reading | last lines : the short word, and is the F struck ? | « plus [illisible] la connaissance de ζ(X, F) » | « plus par la connaissance de ζ(X) »
- [ ] 12 p94 batch-05:487 | reading | condition on F (twice) | « lct. constant » | « ct tordu » (constant tordu)
