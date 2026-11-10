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

## 1. A letter or a word written the same way over several pages

Each of these is one question for all the pages it names: the answer is applied at every place.

- [ ] 12 p43–50 batch-03:133 | reading | the hooked letter multiplying M^+_{(i−1)}(K) etc. : is it the ξ defined on p. 36 ? | ζ | ξ
- [ ] 12 p47–49 batch-03:190 | reading | the invariant of pp. 47–49 : capital Γ or the γ of p. 46 ? | Γ^i, Γ_i | γ^i, γ_i (underlined)
- [ ] 12 p56,58,70 batch-03:354 | reading | the gothic letter for the Lie algebra | capital 𝔊 (and 𝔍 on p. 70) | lower-case 𝔤
- [ ] 12 p75,76,78 batch-04:438 | reading | exponent of A, and the words under the brace | « A^{tr} » ; « [illisible] de la V.A. A sur S » | « A^{fixe} » ; « partie fixe (points fixes) de la V.A. A sur S »
- [ ] 12 p85–88,92 batch-05:187 | reading | the letter of the weight in § 17 and § 18 | p | ρ

## 2. Places where the alternative looked clear on the page

A first look at the page images found the alternative clear here, in whole or for one of the signs the question names.

- [ ] 12 p22 batch-02:121 | reading | derived tensor product : an L above the ⊗, or strokes under it ? | « M ⊗^L N pour M, N ∈ D^b » | « M ⊗ N (⊗ underlined) en M, N ∈ Ob D^b »
- [ ] 12 p24 batch-02:175 | reading | target of T_ℓ in the displayed formula | « M_ℓ(X) » | « M_ℓ^+(X) »
- [ ] 12 p24 batch-02:179 | reading | is « projectifs » on the page ? | « systèmes projectifs ℓ-adiques » | « systèmes ℓ-adiques »
- [ ] 12 p29 batch-02:305 | reading | parenthesis after « spectre d'un corps » | « (qu'on peut supposer si on veut, alg. clos) » | « (fini si on veut, ou clôture alg. d'un tel) »
- [ ] 12 p34 batch-02:484 | reading | parenthesis after « on prend » | ([illisible]) | « (du moins pour X = Spec K d'un corps) » ; then « minimum »
- [ ] 12 p37 batch-02:608 | reading | sign after « on aura » | [illisible] | « = », i.e. « même »
- [ ] 12 p42 batch-03:109 | reading | § 12, first lines | « le groupe [ill.] engendré … décomposition … par × » | « le gpe K engendré … découpage … pour ⊗ »
- [ ] 12 p56 batch-03:361 | reading | word before « dans H^{2n−i} ⊗ H^i(n) » | « prolongée » | « Plongée »
- [ ] 12 p58 batch-03:396 | reading | two places | « On peut par l'image provenir » ; « structures habituelles » | « On pense que l'image provient » ; « structures tensorielles »
- [ ] 12 p63 batch-04:183 | reading | NB, lines 1–3 | « (ou projectif lisse) … [four words unread] telles relations précises » | « (= projectif lisse) … on n'a plus de telles relations précises »
- [ ] 12 p70 batch-04:293 | reading | two places | « on a » ; « Donc on a » | « on trouve » ; « De =, on trouve »
- [ ] 12 p88 batch-05:295 | reading | is « d'ailleurs » on the page ? | « qui sont de la forme » | « qui sont d'ailleurs de la forme »
- [ ] 12 p93 batch-05:448 | reading | three places in the first paragraph | « [ill.] la [ill.] chose » ; « connexe de dim n » ; « donc [ill.] des données [ill.] » | « mod la = chose » ; « variété de dim n » ; « donc (purement ?) de poids 2n »

## 3. The remaining places, page by page

A first look at the page images found the alternative likely here; these are fast cursive, and the facsimile decides.

- [ ] 12 p22 batch-02:116 | reading | margin, top left : third line | « en tirer [illisible] les constructions des foncteurs » | « en termes des données construire des foncteurs »
- [ ] 12 p22 batch-02:132 | reading | words after « compatible avec ⊗ » : in the margin or in the line ? | « (Cond. de transitivité.) » in the margin | « [On a transitivité. » in the line
- [ ] 12 p23 batch-02:141 | reading | margin, first line | « le formulaire de dualité » | « la formule de dualité »
- [ ] 12 p23 batch-02:143 | reading | margin, last lines | « les formules d'Alexander reliant tous ces foncteurs » | « le formulaire standard reliant tous ces foncteurs »
- [ ] 12 p23 batch-02:150 | reading | two words after « filtrant » (twice) | « à morph. affines » | « ess. affine »
- [ ] 12 p23 batch-02:161 | reading | last two lines of the page | « X, Y [ill.] de t.f. sur S, [ill.] définis par … de la façon habituelle, si » | « X, Y de t.f. sur S sont définis par (X_i), (Y_i), si on prend des »
- [ ] 12 p24 batch-02:166 | reading | indices of f, X, Y on line 2 | « on a pour f_i : X_i → Y_i » | « on aura pour f_{i₀} : X_{i₀} → Y_{i₀} »
- [ ] 12 p24 batch-02:177 | reading | word between « catégorie » and « des » | (nothing) | « formée »
- [ ] 12 p24 batch-02:180 | reading | word after « négligeant » | [illisible] | « précisément »
- [ ] 12 p25 batch-02:185 | reading | margin top left, last line | « avec [illisible] etc. » | « avec résidu etc. » (and a short word, « hom » ?, after « f^! »)
- [ ] 12 p25 batch-02:201 | reading | margin, third line | « la chose triviale » | « le choix trivial » (or « le choix limite »)
- [ ] 12 p25 batch-02:202 | reading | margin : word before R^*f_* ; anything unread after « ℓ, » ? | « que R^*f_*… pour f, ℓ, [ill.] ce qui » | « qu'on ait R^*f_*… pour f, ℓ, ce qui »
- [ ] 12 p26 batch-02:221 | reading | is there a word between « échéant » and « (X sur Q) » ? | [illisible] | nothing
- [ ] 12 p26 batch-02:226 | reading | « connexes … » | « connexes et non vides » | « connexes non vides »
- [ ] 12 p26 batch-02:231 | reading | verb before « l'hyp « projectif » » | « oublie » | « enlève »
- [ ] 12 p27 batch-02:251 | reading | anything between « inductive » and « des » ? | « de [illisible] des » | « des »
- [ ] 12 p27 batch-02:254 | reading | end of the chain of M^+ | « → ⋯ » | a full stop
- [ ] 12 p27 batch-02:256 | reading | after « inversible, » | « d'inverse Q(1) [illisible] » | « soit Q(1) son inverse » ; and « pour » after « s'écrire, »
- [ ] 12 p27 batch-02:259 | reading | margin bottom left | « sous-catégorie pleine épaisse abélienne de M(X) ; [illisible] » | « une sous-catégorie abélienne épaisse de M(X) ; l'appartenance à M^+(X) se vérifie fibre par fibre … »
- [ ] 12 p28 batch-02:267 | reading | word before lim→ | [illisible] | « Pseudo »
- [ ] 12 p28 batch-02:268 | reading | sentence squeezed after the closing bracket | « T_ℓ s'étend à M(X), de façon unique à isom unique près, compatible avec ⊗. Les foncteurs [ill.] » | « Les foncteurs T_ℓ s'étendent à M(X), de façon unique, de façon à rester compatibles avec ⊗. »
- [ ] 12 p29 batch-02:312 | reading | words before the first boxed formula | « et on désire que » | « et je dis que l'on a »
- [ ] 12 p29 batch-02:316 | reading | exponent of Λ and the last word of the line | « Λ^n u, la formule » | « Λ^i u, le fait »
- [ ] 12 p30 batch-02:353 | reading | where does the small « sur Z » belong ? | « fibre sur Z par fibre » | « X de t.f. sur Z »
- [ ] 12 p30 batch-02:355 | reading | word after « (Pour » | [illisible] | « ceux-ci »
- [ ] 12 p31 batch-02:363 | reading | after the struck lines | « [ill.] compatible [ill.] f^* » | « Compatible avec f^* »
- [ ] 12 p31 batch-02:372 | reading | « sous-… » (twice) | « sous-quotients » | « sous-espaces »
- [ ] 12 p31 batch-02:374 | reading | is the Z before 1_X struck ? and the exponent of R | « R^i f_!(Z·1_X) » | « R^j f_!(1_X) », Z struck
- [ ] 12 p31 batch-02:378 | reading | opening of the bracket | « on sait que tout » | « au sens que tout »
- [ ] 12 p32 batch-02:404 | reading | verb | « permet de prolonger » | « peut se prolonger »
- [ ] 12 p32 batch-02:406 | reading | two words before « la filtration déjà » | « on ait » | « ce soit »
- [ ] 12 p32 batch-02:412 | reading | « … on prend j assez grand … que » | « si … tel que » | « où … pour que »
- [ ] 12 p33 batch-02:436 | reading | first line | « mais [illisible] par l'inclusion » | « mais on fera (fait) attention que l'inclusion »
- [ ] 12 p33 batch-02:454 | reading | sign before M_i(X)/M_{i−1}(X) | « = » | « ≃ »
- [ ] 12 p33 batch-02:457 | reading | word after « sont » | [illisible] | « tous »
- [ ] 12 p33 batch-02:462 | reading | words before « équiv. can. … à G_0(X) » | « on [illisible] » | « en particulier tous »
- [ ] 12 p34 batch-02:479 | reading | line 3 | « qui se loc. étale [(dans …, … fibre par fibre)] [ill.] objets » | « qui se dévissent loc. étale (du moins fibre par fibre) en objets »
- [ ] 12 p34 batch-02:500 | reading | left margin, first words | [illisible] | « cela distingue »
- [ ] 12 p35 batch-02:520 | reading | first word(s) of the page | « en utilisant » | « induisant »
- [ ] 12 p35 batch-02:525 | reading | after « pour j » | « qui [illisible] » | « grand »
- [ ] 12 p35 batch-02:539 | reading | opening of the parenthesis : the sense is reversed | « par une formule aussi simple » | « pas de formule aussi simple »
- [ ] 12 p35 batch-02:550 | reading | two letters before « tordu » (twice) | « est tordu » | « ct tordu » (constant tordu)
- [ ] 12 p36 batch-02:557 | reading | word before « cette catégorie » | [illisible] | « sur »
- [ ] 12 p36 batch-02:560 | reading | two short words before « une « catégorie tensorielle » | « C'est » | « On a »
- [ ] 12 p36 batch-02:571 | reading | is « libre » on the page ? | « est un Z-module libre admettant comme base » | « comme Z-module admet comme base »
- [ ] 12 p36 batch-02:574 | reading | after « injective » | « [illisible] des objets simples » | « sur l'ens. de ces objets simples »
- [ ] 12 p36 batch-02:577 | reading | after « résulte » | [illisible] | « du fait »
- [ ] 12 p37 batch-02:586 | reading | « on a(ura) … un diagramme … » | « on a … [illisible] » | « on aura … comm. »
- [ ] 12 p37 batch-02:593 | reading | sentence around Σ^+_{(i)}(X) | « M_i(X) se définit en termes [ill.] Σ^+_{(i)}(X) et Σ_i(X), d'une partie [ill.], d'où » | « M_i^+(X) se définit en termes d'une partie Σ^+_{(i)}(X) de Σ_i(X), d'où »
- [ ] 12 p38 batch-02:628 | reading | small words under M_0(X)[ξ] and over the ⊗ below | « (ξ de degré 1) », the rest unread | « de d° 0 » under M_0(X), « de degré 1 » under ξ
- [ ] 12 p38 batch-02:640 | reading | small formula at the right edge after « défini par » | [illisible] | « u, v ↦ ξ^{-1}uv »
- [ ] 12 p38 batch-02:643 | reading | anything between « classe » and « dans » ? | [illisible] | nothing
- [ ] 12 p39 batch-02:666 | reading | first word under the formula | « (donc on a » | « alors on a »
- [ ] 12 p39 batch-02:698 | reading | N.B., first line | « [ill.] on voit [ill.] la structure additive » | « Du pt de vue de la structure additive, »
- [ ] 12 p39 batch-02:700 | reading | word after « connaissance » | [illisible] | « de »
- [ ] 12 p39 batch-02:708 | reading | small note right of « les applications » | « x, y ↦ [ill.] définies par [ill.] » | « u, v ↦ uv, défini par »
- [ ] 12 p40 batch-02:720 | reading | two gaps in the sentence on the involution | [illisible], [illisible] | « de proche en proche » ; « sur σ_i »
- [ ] 12 p40 batch-02:721 | reading | verb, and the word after « théorie » | « résulterait de la théorie [illisible] » | « résultera de la théorie projective »
- [ ] 12 p41 batch-03:77 | reading | title, word before « géométriques » | « ou » | « Cas »
- [ ] 12 p41 batch-03:81 | reading | first line after the struck word | « une variété lisse sur le corps alg. clos » | « non singulière sur k alg. clos »
- [ ] 12 p41 batch-03:85 | reading | margin note, first word | « utilisation du » | « attention »
- [ ] 12 p41 batch-03:93 | reading | under the inductive limit | « U ouvert dense de x̄ » | « U ouvert ≠ ∅ de x̄ »
- [ ] 12 p41 batch-03:95 | reading | « On … que cette suite spectrale provien… » : known or wanted ? | « On sait que … provient » | « On veut que … provienne »
- [ ] 12 p41 batch-03:95b | reading | end of the parenthesis and the small insertion | « passer aux filtrations finies convenables … [en dehors de …] » | « prendre une filtration finie convenable … » ; insertion « en dim n » after « Le morceau »
- [ ] 12 p41 batch-03:95c | reading | margin right : « essentielle … si X de dim 1 » | « ! ou si » | « , même si » ; is « projectif » struck or underlined, and is « lisse » there ?
- [ ] 12 p41 batch-03:95d | reading | last sentence | « On voit que [ill.] [ill.] exactement » | « On veut que ce soit exactement »
- [ ] 12 p43 batch-03:119 | reading | after « σ cl(X), on » | « [illisible] les » | « a des »
- [ ] 12 p44 batch-03:151 | reading | « on trouve un(e) … dans Z^(…) … un invariant » | « un « type » » ; « i.e. » | « une image » ; « donc »
- [ ] 12 p45 batch-03:158 | reading | first words of the page | « i.e. des » | « où chaque »
- [ ] 12 p45 batch-03:162 | reading | underlined word after « la composante » | « primitive » | « bipure »
- [ ] 12 p45 batch-03:166 | reading | two places in the last paragraph | « le dual des H^j » ; « la composante primitive des H^j » | « la classe dans H^j » ; « la composante j-bipure dans H^j »
- [ ] 12 p46 batch-03:182 | reading | sign between the two terms of the bracket | « + » | a comma (the + is struck)
- [ ] 12 p47 batch-03:192 | reading | four places in the definition of the invariant | « on peut le supposer » ; « morphisme » ; « ([ill.] surjectif) » ; « comme on le sait bien » | « ce qu'on peut supposer » ; « hom. » ; « (donc surjectif) » under « propre » ; « comme il est bien connu »
- [ ] 12 p47–48 batch-03:195 | reading | the « Question » sentence | « On aimerait, pour deux … extensions de type …, … provenant d'un K-homom. » | « On aimerait que tout système d'homs … provienne d'un K-homom. »
- [ ] 12 p48 batch-03:198 | reading | first sentence | « R'[t_1, …, t_N] » ; « à des systèmes » ; « s'immerge » | « R'[δ_1, …, δ_N] » ; « et des (du) système(s) » ; « s'envoie »
- [ ] 12 p48 batch-03:200 | reading | words in the loop under « sur K alg. clos » | « ([ill.] [ill.]) telles que » | « (supposons que »
- [ ] 12 p48 batch-03:207 | reading | last bracket of the page | « Cast. ok ! » | « coh. alg ! »
- [ ] 12 p49 batch-03:211 | reading | verb | « Trouve-t-on » | « Trouvons-nous »
- [ ] 12 p52 batch-03:273 | reading | second paragraph | « voir » (twice) ; « permettent de décrire » | « via » (twice) ; « peuvent se décrire »
- [ ] 12 p53 batch-03:315 | reading | small N.B. between cases 1) and 2) | « des variantes de l'unité [… I 1 !] » | « des racines de l'unité [leur produit étant ±1 !] »
- [ ] 12 p54 batch-03:322 | reading | word before « caractériser » | « pouvons-nous » | « comment »
- [ ] 12 p54 batch-03:326 | reading | last two lines of the page ; are they struck ? | « Le cas général [ill.] [ill.], si on connaît tous les Frobenius [ill.] » | « Le cas général s'en déduit par image inverse, si on connaît tous les Frobenius ∈ π_1 »
- [ ] 12 p58 batch-03:398 | reading | the bracket on the « partie algébrique » ; is its last clause struck or underlined ? | « ce pro-motif n'étant lui-même autre … en tout autre cas, on … que Z(0) ! ; [struck] il paraît qu'il est une … » | « c'est tout – le pro-motif n'étant lui-même autre que Z(0) ! ; en tout autre cas, je pense qu'il est nul … »
- [ ] 12 p59 batch-03:405 | reading | exponents on lines 1, 4 and after the triangulated functor | R^i f_*, H^i(X,M) | R^* f_*, H^*(X,M)
- [ ] 12 p59 batch-03:417 | reading | 1°) | « lim essentielles filtrantes de préschémas à pr. quasi proj. affines » | « lim essentiellement affines de préschémas q.c. q.s. »
- [ ] 12 p59 batch-03:420 | reading | last word of the page | « est » | « de » (type fini, next page)
- [ ] 12 p61 batch-04:117 | reading | 3°), three lines | « on a [ill.] … et H^0 est exact [ill.] en M. De plus, dans fonctoriel » | « on veut que … donc H^0(X,M) est exact à g. De plus, isom fonctoriel »
- [ ] 12 p62 batch-04:139 | reading | the doubt on the Ext^i | « doutes pour les Ext^i (i>0) [ill.] pour être dans la catégorie des Ind-motifs ???] Possibles » | « doute que les Ext^i (i>0) soient [peut-être dans la catégorie des Ind-motifs ???] effaçables »
- [ ] 12 p62 batch-04:153 | reading | words above the struck line of 4°) | « bien le ℓ-foncteur » | « des hom de ∂-foncteurs »
- [ ] 12 p63 batch-04:178 | reading | verb | « on aurait » | « on aura »
- [ ] 12 p63 batch-04:188 | reading | « Le th. de Tate … en énonçant » | « peut se reformuler de façon précise » | « peut se reformuler et se préciser »
- [ ] 12 p63 batch-04:190 | reading | last formula : the small words by the arrow, and the twist of Q_X | label « ét. pr. Q_ℓ » on the arrow ; Q_X(i) | « pas Q_ℓ » pointing at Q ; Q_X(0)
- [ ] 12 p64 batch-04:195 | reading | lines 2–3 | « simplifiant les notations (f : …). Une autre façon de l'écrire » | « morphisme structural f : X → Spec k. Une autre façon est celle-ci »
- [ ] 12 p64 batch-04:219 | reading | last paragraph | « dans (X projectif …) » ; « c'est les cycles » | « alors (si X projectif …) » ; « ce sont les cycles algébriques à coeff. rationnels »
- [ ] 12 p66 batch-04:232 | reading | lines 2 and 4 | « (constructibles) » ; « par le couplage de motifs dualisants » | « (complexes de) » ; « pour le complexe de motifs dualisants »
- [ ] 12 p66 batch-04:235 | reading | the NB in brackets ; the circled word above the line | « est régulier de dim n, dans Q(n)[2n+1], c'est le dualisant à valeurs dans » ; circled « foncteur » | « est régulier partout de dim n, alors c'est la dualité à valeurs dans Q(n)[2n+1] » ; circled « partout »
- [ ] 12 p66 batch-04:244 | reading | phrase in quotation marks under R_!Γ_X(M^*) | « supposer qu'on sait que Z » | « support propre (compact) sur Spec Z »
- [ ] 12 p68 batch-04:263 | reading | first line | « cas choisi pour X = Spec Z, et lui-même le cas géométrique » | « = (même) énoncé pour X = Spec Z, et dans le cas géométrique »
- [ ] 12 p68 batch-04:276 | reading | two verbs | « en utilisant le foncteur » ; « Cela revient à » | « en appliquant » ; « Cela ramène à »
- [ ] 12 p68 batch-04:278 | reading | slanted margin note, left | « à développer au sujet des cup-produits à coeff. « abstraits » » | « à développer sans doute pour le cup-produit en cohomologie « absolue » »
- [ ] 12 p68 batch-04:282 | reading | the bracket | « pour un vectoriel [ill.] … sur lequel » | « pour des vectoriels … sur lesquels » ; hat on the Z ?
- [ ] 12 p70 batch-04:324 | reading | third case of the last formula | « [struck] si i = 2j+1, mais pas canoniquement isomorphe à … X/F̄ ! » | « id. si i = 2j+1, mais pas canoniquement en termes de X̄/F̄ ! » (or « X̄, K̄ »)
- [ ] 12 p70 batch-04:329 | reading | small N.B. bottom left | « Remplaçons k par [three words unread] l'isom. obtenu par lim » | « Remplacer k par k_n revient à multiplier l'isom obtenu par 1/n »
- [ ] 12 p72,73 batch-04:334 | reading | the same two short words after « motif » on both pages | [illisible] | « ct tordu » (constant tordu)
- [ ] 12 p73 batch-04:378 | reading | index of Q in R^1 f_* | « Q_A(1) » | « Q_{A^*}(1) »
- [ ] 12 p74 batch-04:389 | reading | is « pour » struck ? | « pour nous suggèrent » | « nous suggèrent »
- [ ] 12 p74 batch-04:395 | reading | line above the Kummer sequence | « Considérons [ill.] [ill.] (aux [three words unread] ×) » | « Considérons (pour ℓ premier aux car. résiduelles de X) »
- [ ] 12 p74 batch-04:402 | reading | place of ℓ^ν on the third term | after the parenthesis (cokernel) | under the left of H^1 (kernel)
- [ ] 12 p74 batch-04:411 | reading | adverb | « vraisemblablement » | « moralement »
- [ ] 12 p75 batch-04:418 | reading | first lines | « on a » ; sequence ending on a struck term | « on aura » ; « → 0 » before the struck term
- [ ] 12 p75 batch-04:442 | reading | letter in the middle term of the last sequence | « f_*(M) » | « f_*(A) »
- [ ] 12 p77 batch-04:481 | reading | parenthesis on line 1 | « donc le T_ℓ ou H^2 » | « dont le T_ℓ est H^2 »
- [ ] 12 p77 batch-04:490 | reading | two places | « sur S × S » ; « qui n'est pas nul » | « sur C × C » ; « qui est non nul »
- [ ] 12 p78 batch-04:503 | reading | underlined words right of the isomorphism | « sauf à noyau fini » | « surj. à noyau fini »
- [ ] 12 p78 batch-04:525 | reading | slanted note bottom left | « les seuls cas qui restent » | « les seuls invariants qui restent »
- [ ] 12 p81 batch-05:113 | reading | before the exact sequence | « alors » | « alors on a : »
- [ ] 12 p81 batch-05:131 | reading | the two lines under the Tate duality : is the second one struck, or underlined twice ? | both struck, fragments | first struck ; second « c'est donc essentiellement un p-groupe, … groupe fini ! OK. »
- [ ] 12 p81 batch-05:136 | reading | last sentence : a question or a statement ? | « Peut-on généraliser au cas d'une variété X régulière dont on enlève » | « Peut se généraliser au cas où on prend X régulier dont (auquel) on enlève »
- [ ] 12 p83 batch-05:140 | reading | word after « Calculs » | « sur » | « pour »
- [ ] 12 p83 batch-05:161 | reading | two places | « modèle [illisible] » ; « = fini » | « modèle can. » ; « = gpe fini »
- [ ] 12 p85 batch-05:186 | reading | first words | « Le théorème » | « La théorie »
- [ ] 12 p85 batch-05:204 | reading | sentence before « L^s(M). Noter » | « Soit ce que nous notons » | « Cet espace sera noté »
- [ ] 12 p86 batch-05:226 | reading | words above the struck ones ; is « fermé » struck ? | « on [illisible] L^s(M) un cône convexe [struck : fermé] » | « on a dans L^s(M) un cône convexe fermé »
- [ ] 12 p86 batch-05:233 | reading | slanted margin note | « sont dites positives » | « sont dites pseudo-amples »
- [ ] 12 p88 batch-05:288 | reading | first words of the paragraph | « En décomposant » | « Si on décompose »
- [ ] 12 p88 batch-05:297 | reading | heavy letter after ⊗_A and before « un vectoriel » | M | V (written over an M)
- [ ] 12 p89 batch-05:311 | reading | small word above the second struck word of line 3 | (nothing) | « rang » : « proj. de rang fini sur k »
- [ ] 12 p89 batch-05:320 | reading | head of line 7 | « Z-libre » | « gpe libre »
- [ ] 12 p89 batch-05:323 | reading | where does « k[t]/P k[t] » belong, and what is associated to P ? | « P en [ill.] [ill.]. À tout tel P, on associe : k[t]/P k[t]. (V, f), dont … » | « P en module k[t]/P k[t]. À tout tel P est associé un (V, f), dont … »
- [ ] 12 p89 batch-05:327 | reading | two short lines in the left margin | [illisible] | « k un corps ou non »
- [ ] 12 p90 batch-05:340 | reading | first line | « via la fonction car. modifiée » | « via le pol. car. modifié »
- [ ] 12 p90 batch-05:347 | reading | the looped insertion under R(N,k) → 1 + k[[t]]^+ : first word, and a minus sign in the denominator ? | « compatible avec … l'anti-« additif » φ(t) ↦ 1/φ(t) » | « composé avec l'aut. « additif » φ(t) ↦ 1/φ(−t) »
- [ ] 12 p90 batch-05:350 | reading | boxed margin note, lines 1–2 | « en fait, [illisible] les fonctions rationnelles » | « en fait, à valeur(s) dans les fonctions rationnelles »
- [ ] 12 p90 batch-05:356 | reading | the sentence after « En effet » | « la connaissance de la fonction rationnelle à numérateur 1 dans k[t] [ill.] facilement [ill.] » | « la connaissance de la série formelle permet de reconstituer la fonction rationnelle L, donc »
- [ ] 12 p90 batch-05:380 | reading | last lines | « on trouve inversement L par exp(…). D… » | « on peut inverser cet homomorphisme par exp(…). Donc »
- [ ] 12 p91 batch-05:396 | reading | after « la fonction L de » : is the long word struck ? | « (X, F) [struck word] à coeff. dans F, sur F_p » | « X, compactifiable sur F_p, à coeff. dans F »
- [ ] 12 p91 batch-05:401 | reading | three places in the lower half | « on considère cette fonction L comme l'image » ; « F vient d'un motif » ; « suivant les poids en » | « car essentiellement cette fonction L est l'image » ; « F est un motif » ; « suivant des poids en des »
- [ ] 12 p92 batch-05:414 | reading | the insertion above line 2, and the exponent of H (twice) | « F localement constant, de poids p » ; H^i | « F constant tordu, de poids ρ » ; H^{i−ρ}
- [ ] 12 p92 batch-05:419 | reading | two places | « donc on a la connaissance » ; « Frobenius dans ceux-ci » | « dans ce cas la connaissance » ; « Frobenius dedans »
- [ ] 12 p92 batch-05:443 | reading | slanted margin bottom left | « le poids [ill.] filtration [ill.] cf. N° 12 » | « le poids ici n'est pas la bonne filtration cf N° 12 »
- [ ] 12 p93 batch-05:462 | reading | slanted margin, top left | fragments « filtration … poids … niveau » | « peut se raffiner, en regardant une autre filtration que par le poids, savoir le niveau … »
- [ ] 12 p93 batch-05:465 | reading | the paragraph « Si F = Q_ℓ(0) » | « … [ill.] des fonctions ζ … est [ill.] équivalente : celle de π_0(X̄) comme [ill.] fondamentale » | « donc si on s'occupe des fonctions ζ … est essentiellement équivalente : celle de π_0(X̄) comme Frob-ensemble »
- [ ] 12 p93 batch-05:476 | reading | last lines : the short word, and is the F struck ? | « plus [illisible] la connaissance de ζ(X, F) » | « plus par la connaissance de ζ(X) »
- [ ] 12 p94 batch-05:486 | reading | condition on F (twice) | « lct. constant » | « ct tordu » (constant tordu)
