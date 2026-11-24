# Tri de l'annexe Lean — proposition de simplification

Fichier de travail non suivi (docs/lean/tri.md), préparé le 17 octobre 2026 sur le commit `d3dd4de`. Il ne modifie ni docs/lean ni aucun fichier suivi. Le tri des 40 sections a été fait section par section, d'après la section, son fichier Lean, `found` et `verdict` de src/content/proofs.ts et les champs `lean.found` de src/content/findings.ts. Les cas douteux sont relevés au § 7.

## 1. Résumé

**544 environnements** au total : 406 dans les 40 sections démontrées, et 138 encadrés dans les parties vides et les blocs « autres pistes » (sections/vide, sections/autres).

| classe | sections démontrées | parties vides / autres pistes | total | mots actuels* |
|---|---|---|---|---|
| A — preuve rédigée | 164 | — | 164 | 35161 |
| B — ligne + lien | 112 | — | 112 | 16366 |
| C — retirer | 101 | — | 101 | 19706 |
| D — garder (partie finale, énoncé ouvert) | 29 | 64 | 93 | 8331 |
| D — retirer | 0 | 74 | 74 | 6373 |

\* Mots comptés par environnement, preuve comprise, avec le même compteur sur tout l'article : 123 600 mots pour 197 pages, soit environ 628 mots par page. Le texte de contexte entre les environnements n'est pas compté dans les lignes.

Parmi les A, il y a 67 remarques (8 400 mots) qui portent la trouvaille : elles se fondent dans l'énoncé ou dans sa ligne de verdict. Il y a aussi 58 énoncés (14 300 mots), et 35 théorèmes et contre-exemples (12 400 mots).

**Estimation des pages**
- *Tri appliqué tel quel* : A en entier, une ligne de 40 mots par B, les D gardés, 150 mots de contexte par section, 4 000 mots d'introduction, de tableau et de bilan, soit environ 58 k mots et **92 pages**. C'est au-dessus de la cible.
- *Tri resserré* (proposé) : preuve entière pour les théorèmes et les contre-exemples A ; énoncés A avec une preuve réduite d'environ 40 % ; remarques A fondues en une ou deux phrases ; B seulement dans le tableau d'ouverture, sans ligne dans les sections ; énoncés D sans commentaire ; 80 mots de contexte par section. On obtient environ 38 k mots, soit **60 pages**, dans la cible de 50 à 70 pages.
- Leviers supplémentaires, si besoin : passer en B les A douteux du § 7 (environ 20 items), et ramener la partie finale aux D marqués « candidate » dans findings.ts.

**Parties proposées** : six thèmes, puis une partie finale d'énoncés ouverts. Le détail est au § 2.

- I. Analyse, cycles et dualité : cotes 1, 16, 125
- II. Algèbre commutative et géométrie formelle : cotes 21, 22, 39, 41, 42, 37, 67, 153
- III. Catégories, topos et algèbre universelle : cotes 19, 161-2, 133, 113, 161-1
- IV. Groupes algébriques, variétés abéliennes et courbes : cotes 44, 40, 93, 78, 84
- V. Surfaces, cartes, polyèdres et ordres : cotes 70, 73, 74, 76, 77, 86, 79, 68, 152, 156-1, 156-3, 88, 85
- VI. Homotopie et espaces stratifiés : cotes 136, 120, 106, 114, 158, 104
- VII. Énoncés ouverts : les D gardés, classés selon les thèmes I à VI.

## 2. Regroupement des 29 parties en thèmes

Les cotes restent rangées comme dans la carte. On fusionne seulement les parties. Dans chaque thème, l'ordre suit la datation de l'inventaire (milieu de l'intervalle), et les cotes non datées viennent en dernier. Les titres ne portent pas « (vers année) ».

| thème | anciennes parties fusionnées | cotes, dans l'ordre (datation de l'inventaire) |
|---|---|---|
| I. Analyse, cycles et dualité | Cycles algébriques et conjectures standard ; Motifs ; Théorie de Hodge ; Cohomologie étale et ℓ-adique ; Groupes p-divisibles et groupes formels ; Analyse fonctionnelle (cote 1) ; Théorie de la dualité ; Cohomologie cristalline et de de Rham | 1 (1953) ; 16 (1966-1967) ; 125 ([avant 1970]) |
| II. Algèbre commutative et géométrie formelle | Descente ; Topos et sites (cote 37) ; Algèbre commutative ; Géométrie formelle, modules et représentabilité ; K-théorie, classes de Chern et Riemann–Roch | 21 ([vers 1960-1967]) ; 22 (1963-[vers 1967]) ; 39 ([vers 1960-1970]) ; 41 ([années 1960-1970]) ; 42 ([années 1960-1970]) ; 37 (1967-1971) ; 67 ([à partir de 1977]-1984) ; 153 ([à partir de 1982]) |
| III. Catégories, topos et algèbre universelle | Algèbre universelle et théories ; Analyse fonctionnelle (cote 113) ; Catégories tensorielles et dualité tannakienne ; Catégories et foncteurs ; Champs, gerbes et catégories fibrées | 19 ([à partir de 1958-1973]) ; 161-2 ([vers 1963-1973]) ; 133 (1974-[à partir de 1975]) ; 113 ([à partir de 1982]) ; 161-1 (s.d.) |
| IV. Groupes algébriques, variétés abéliennes et courbes | Variétés abéliennes et schémas de Picard ; Schémas en groupes et groupes algébriques ; Surfaces de Riemann, uniformisation et modules des courbes ; Groupes fondamentaux et théorie de Galois ; Géométrie anabélienne et dessins | 44 (1964) ; 40 ([années 1960-1970]) ; 93 ([1972]-1981) ; 78 ([à partir de 1977]) ; 84 ([à partir de 1982-vers 1986]) |
| V. Surfaces, cartes, polyèdres et ordres | Topologie combinatoire, surfaces et cartes ; Jeux et combinatoire ; Polyèdres et géométrie convexe ; Ordres et géométrie des formes | 70 ([à partir de 1976]) ; 73 ([à partir de 1976]) ; 74 ([à partir de 1976]) ; 76 ([vers 1977]) ; 77 ([à partir de 1977]) ; 86 ([à partir de 1977]) ; 79 ([à partir de 1980]) ; 68 ([à partir de 1978-à partir de 1983]) ; 152 ([à partir de 1982]) ; 156-1 (1986) ; 156-3 (1986) ; 88 (s.d.) ; 85 (s.d.) |
| VI. Homotopie et espaces stratifiés | Théorie de l'homotopie et catégories tests ; Topologie modérée et espaces stratifiés | 136 ([à partir de 1975-1976]) ; 120 ([à partir de 1973-à partir de 1978]) ; 106 ([à partir de 1982]) ; 114 ([1983]) ; 158 ([vers 1990-1991]) ; 104 (s.d.) |
| VII. Énoncés ouverts | les encadrés non vérifiés des parties vides et des blocs « autres pistes », et les D des sections | par thème I à VI, puis par cote |

Les dix parties vides disparaissent comme parties. Leurs D gardés passent en VII, et la phrase « ce qui manque à mathlib » de chaque thème vide devient une ligne de VII. Le paragraphe \lettres d'une ancienne partie passe sous le thème qui la reçoit.

## 3. Tableau d'ouverture de l'article

Colonnes : **Cote** | **Énoncé** (quelques mots) | **Verdict** (tient tel qu'énoncé / tient, plus généralement / faux sur la page / la lecture omettait une hypothèse / en partie) | **Théorème Lean** (le nom, lié au fichier) | **§** (renvoi à la section, si la preuve est rédigée). On peut ajouter une colonne étroite de marques : ♦ piste, ■ PR mathlib. Le tableau donne une ligne par cote. Les B de la cote y figurent dans une seconde sous-table, plus serrée (cote, énoncé, théorème).

Projet de lignes, tiré des verdicts du tri (à relire) :

| Cote | Énoncé | Verdict | Théorème Lean |
|---|---|---|---|
| **I. Analyse, cycles et dualité** | | | |
| 1 | Système (16) des valeurs singulières, cas m ≤ 2 | en partie | `sigma_two_add_le` |
| 16 | Pseudo-inverse de Lefschetz, normalisation sl₂, algèbres de Hodge d'ordre 2 | en partie | `DonneesHodge.assoc_iff` |
| 125 | Trois étages de la carte de dualité ; lemme III-18 | tient tel qu'énoncé | `etage1_iff_etage2` |
| **II. Algèbre commutative et géométrie formelle** | | | |
| 21 | Modules de I-torsion injectifs et Γ_I sur anneau noethérien | tient, lecture corrigée | `proposition2_15` |
| 22 | Produits de plats ; k[[t]] non formellement lisse, topologie discrète | tient, plus généralement | `not_formallySmooth_of_field` |
| 39 | Préparation formelle : division par F, cas adique et discret | en partie | `preparation_discrete` |
| 41 | Section générique continue ssi f ouvert, relèvement des générisations | tient, plus généralement | `proposition1` |
| 42 | Sections d'un faisceau = familles cohérentes de germes ; lemme 2 | tient, plus généralement | `proposition` |
| 37 | Contre-exemple à EGA I 10.10.5 (lettre à Dieudonné) | tient, plus généralement | `no_finitePresentation_inducing` |
| 67 | Involutions des modules et triplets (P, Q, m) | tient, plus généralement | `equivalence` |
| 153 | Polynômes à valeurs entières : lemme, co-opérations, Pólya, Ω = Ω₀ ⊕ Ω⁰ | tient, plus généralement | `coaddition_existsUnique_of_injective` |
| **III. Catégories, topos et algèbre universelle** | | | |
| 19 | Théorème 1.12 de comonadicité ; comonade sur une base produit | faux sur la page | `theoreme_b_necessite_fausse` |
| 161-2 | Monadicité de Beck et caractérisation de Gabriel–Ulmer | tient tel qu'énoncé | `caracterisation_gabriel_ulmer` |
| 133 | Centre et groupe dérivé par deux modules croisés | tient, hypothèses plus faibles | `injective_Psi_iff` |
| 113 | Invariance des modules par enveloppe de Karoubi | tient, plus généralement | `morita` |
| 161-1 | Adjonctions idempotentes : conditions équivalentes, parties fixes, descente d'adjoints | tient, plus généralement | `idempotent_tfae` |
| **IV. Groupes algébriques, variétés abéliennes et courbes** | | | |
| 44 | Intégralité des nombres de Cartan depuis les axiomes | en partie : axiomes seuls insuffisants | `cartan_int_of_indivisible` |
| 40 | La régularité des torseurs sous α_p ne passe pas à la somme | tient, plus généralement | `fibre_nilpotent` |
| 93 | Différence schwarzienne en dérivées divisées : cocycle, fonctions tuées, rigidité | en partie | `rigidity_of_gt` |
| 78 | Critère u_α^n = id ⇔ F_n(α) = 0 sur un anneau ; 2p-gones | tient, plus généralement | `zpow_eq_one_iff` |
| 84 | Produit des algèbres quadratiques, triplets, extensions χ-scindées, en coordonnées | en partie | `coinvariants_bijective_iff` |
| **V. Surfaces, cartes, polyèdres et ordres** | | | |
| 70 | Icosaèdre sur Z[α] fidèle en toute caractéristique, conique mod 5 | en partie | `not_collinear_any` |
| 73 | Aires des oreilles : plan projectif des quadrilatères, critère multiplicateur nul | tient, sur tout corps | `zero_multiplier_criterion` |
| 74 | Réduction des graphes à triangles à un carré latin et revêtements | tient sous (Ka) restituée | `Scholie.axiom1_iff_ka` |
| 76 | Surjectivité des drapeaux de type H, transitivité de ≺ | tient, plus généralement | `flag_lemma` |
| 77 | Discriminant universel modulo 2 et 4, symétrie canonique | tient, plus généralement | `disc_even_rank` |
| 86 | Cinq trièdres de l'icosaèdre, action par Alt_T, hémi-icosaèdre | tient tel qu'énoncé | `permT_surjective` |
| 79 | Commutant de SL₂, homothéties et distances dans les graphes | tient, plus généralement | `commutant` |
| 68 | Théories de l'orientation : morphisme unique, isomorphisme, action sg∘det | tient tel qu'énoncé | `exists_unique_hom` |
| 152 | Dictionnaire entre graphes circularisés et contours | en partie ; tête de page fausse | `formules` |
| 156-1 | Le modèle-segment est un biordre, et réciproquement | tient, plus généralement | `biorder` |
| 156-3 | Bijection respectant les découpages : isomorphisme ou anti-isomorphisme | tient, plus généralement | `order_of_cuts` |
| 88 | Ordre 2ν de σ_{ℓ−2}σ_{ℓ−1} ; trichotomie des types (p,q) | tient, plus généralement ; (c₂) corrigée | `proposition_ordre` |
| 85 | Représentations de G₂ dans PGL₂, rotations d'ordre 5 | en partie | `discr_isUnit_of_star` |
| **VI. Homotopie et espaces stratifiés** | | | |
| 136 | Lemme binomial des ombres, forme en degré i | tient, plus généralement | `binomial_shadow_existsUnique` |
| 120 | Écrasement d'une partie modérée : séparation des points hors de Y | tient, plus généralement | `collapse_separation` |
| 106 | Doute de la page 11 levé ; critère (⋆⋆) toujours vérifié | tient, plus généralement | `qFunctor_iso` |
| 114 | Proposition 4 : asphéricité totale indépendante du localisateur | la lecture omettait une hypothèse | `proposition4_ii_iii` |
| 158 | Monoïde fini pseudo-cofiltrant à groupe enveloppant trivial : zéro à droite | tient ; la glose était fausse | `proposition1` |
| 104 | Catégories de modèles : sous-objets, exemples, structure de Reedy directe | en partie démontré | `reedyDirecte` |

## 4. Format des liens

Permalien GitHub figé sur un SHA de commit ; le nom du théorème est dans le texte, sans numéro de ligne. Une macro dans le préambule :

```latex
\newcommand{\leansha}{d3dd4de0a022d948528f56f1a3dc9a33fa60db9c}% à figer au commit de publication
\newcommand{\leanthm}[2]{\href{https://github.com/Commutator-IO/grothendieck-project/blob/\leansha/lean/Grothendieck/#1.lean}{\texttt{\detokenize{#2}}}}
% usage : \leanthm{Folder77}{disc_even_rank}
```

Exemple de rendu : [`disc_even_rank`](https://github.com/Commutator-IO/grothendieck-project/blob/d3dd4de0a022d948528f56f1a3dc9a33fa60db9c/lean/Grothendieck/Folder77.lean). La macro \verifie (lien sur `main`, dans la note du titre de section) passe au même SHA. Le golf en cours déplace les lignes, mais un SHA figé et un nom de théorème restent stables. Les noms viennent de `theorem` et `lemma`. `morita` et `restriction_isEquivalence` (113) sont des `instance` : on les lie quand même par leur nom. Les cotes à tiret donnent `Folder156_1`, `Folder161_2`, etc.

## 5. Énoncés non démontrés : étiquettes et partie finale

Règle appliquée (17 oct.) : « Conjecture (Grothendieck, p. N) » seulement quand la page pose elle-même l'énoncé comme conjecture, affirmation ou question, c'est-à-dire quand le titre de l'encadré porte « Grothendieck, page(s) N ». Sinon, « Énoncé non démontré » : titre « D'après… », forme reconstituée, corrigée ou complétée par l'édition, ou question de l'édition. **À vérifier sur les pages** : les agents ont appliqué la règle au titre et n'ont pas relu les fac-similés. Plusieurs « Grothendieck, pages… » sont des théorèmes que la page affirme, des exemples (133 n° 9, 70 n° 5) ou des contre-exemples (22 n° 15).

Bilan : 29 D à garder dans les sections démontrées, et 64 à garder contre 74 à retirer dans les parties vides et les blocs « autres pistes » (tables au § 6).

**Pistes du tier 3 (#54) sans encadré dans l'article.** Les 147 pistes du tier 3 sont toutes citées dans l'article. 140 y ont un encadré. Les 7 autres ne figurent que dans une liste \item (« Cote N : … ») :

| piste | cote, pages | énoncé | important | étiquette proposée | raison |
|---|---|---|---|---|---|
| `2-trivial-total-chern-class` | Cote 2, pp. 9, 11 et 13 | Classe non nulle de K(X × P^r) à classe de Chern totale 1 | oui | Conjecture (Grothendieck, pp. 9, 11 et 13) | Exemple explicite frappant : Chern ne détecte pas la K-théorie |
| `8-lubin-tate-via-hodge-filtration` | Cote 8, pp. 43 à 49 | Relèvement de Lubin–Tate obtenu par la seule théorie des déformations cristallines | non | Conjecture (Grothendieck, pp. 43 à 49) | Nouvelle voie vers un résultat connu ; lecture à vérifier |
| `8-dim-one-A-module-homs` | Cote 8, pp. 39 à 41 | BT de dimension un à action de A isogènes ssi ϖ = ϖ′, Hom explicite | non | Conjecture (Grothendieck, pp. 39 à 41) | Classification probablement chez Hazewinkel ; signe taché à relire |
| `18-archimedean-lattice-cocycle` | Cote 18, pp. 46 à 61 | Réseaux de Betti aux places archimédiennes : 1-cocycle galoisien, classe indépendante de la place | oui | Conjecture (Grothendieck, pp. 46 à 61) | Énoncé neuf sur variétés conjuguées et torseur sur k₀ |
| `53-cancellative-monoid-is-group` | Cote 53, p. 21 | Schéma en monoïdes de présentation finie à translations monomorphes : schéma en groupes | non | Conjecture (Grothendieck, p. 21) | Net mais sans doute connu (Brion) ; mots illisibles |
| `62-triples-rigidified-moduli` | Cote 62, pp. 41 à 53 | Triplets (courbe de genre 0, trisection, section) : trois descriptions, invariant j | non | Conjecture (Grothendieck, pp. 41 à 53) | Candidate mais correspondance attendue avec Katz–Mazur, Deligne–Rapoport |
| `94-rank-constructibility` | Cote 94, p. 7 | Représentabilité générique de F équivaut à constructibilité du rang des fibres | non | Énoncé non démontré (p. 7) | Critère technique ; réciproque non lisible sur la page |

À ajouter en VII : 2-trivial-total-chern-class et 18-archimedean-lattice-cocycle. Les cinq autres restent hors de l'article, ou en une ligne.

## 6. Tables par section

Ordre des \input d'article.tex. Colonnes : n° (rang dans la section) | environnement | titre ou label tel qu'écrit (♦ = piste, ■ = PR mathlib, ◇ = non vérifié) | théorème(s) Lean | classe | raison.

### Cote 16 — Pseudo-inverse de Lefschetz, normalisation sl₂, algèbres de Hodge d'ordre 2

Verdict : *en partie* · théorème principal `DonneesHodge.assoc_iff` · 4746 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Page 9, la comparaison de la lecture  | `identification_seulement_si` | B | Comparaison de la lecture confirmée : ΛLx = (n−i)x, pas x. |
| 2 | énoncé | Page 16, le commutateur  | `commutateur_pseudo_inverse` | B | Calcul direct du commutateur avec le pseudo-inverse. |
| 3 | énoncé | Page 13, le modèle extérieur  | `lambda0_L0_un`, `lambda0_L0_un_ne_un` | A | Page 13 fausse telle qu'écrite : Λ₀L₀(1) = n, identification seulement si n = 1. |
| 4 | lemme | `lem:16-sl2`  | `sl2_normalisation` | C | Calcul sl₂ standard servant seulement à l'énoncé 1. |
| 5 | remarque | —  | — | C | Reformule la comparaison des deux normalisations. |
| 6 | remarque | —  | — | B | Confirme la correction de la page 13 ; se condense dans le verdict de 3. |
| 7 | énoncé | Pages 6 à 8, les projecteurs de la graduation ♦ | `projecteurs_mem`, `projecteurs_mem_lefschetz` | A | Tranche la première partie de la piste : projecteurs dans ℰ, sur ℤ, sans module. |
| 8 | lemme | `lem:16-homogene`  | `Graduation.mul_proj`, `sandwich` | C | Lemme auxiliaire de la preuve des projecteurs. |
| 9 | remarque | —  | — | A | Hypothèse de réalisation superflue ; piste démontrée en partie seulement. |
| 10 | encadré/contre-ex. | Page 13, sur $\mathbb Z$ ♦ | `not_exists_xi₀_pow_mul_eq_vol`, `L₀_pow_ne_vol` | A | Contre-exemple : le Λ₀ de (6.15) n'existe pas sur ℤ pour n ≥ 2. |
| 11 | remarque | —  | — | A | Porte la trouvaille : Φ₀ = ℤ[L₀, Λ₀] impossible sur ℤ, possible sur ℚ. |
| 12 | lemme | Pages 14 et 15, l'étape algébrique de l'unicité `lem:16-pseudo`  | `pseudo_inverse_unique` | B | Étape algébrique de l'unicité confirmée, une ligne. |
| 13 | encadré/théorème | Grothendieck, pages 24 à 28, algèbres de Hodge d'ordre 2 `thm:16-hodge` ♦ | `DonneesHodge.produit_force`, `DonneesHodge.mul_anticomm_of_impair`, `DonneesHodge.assoc_iff`, `DonneesHodge.lefschetz_iff`, `DonneesHodge.poincare_iff` | A | Tranche la piste des algèbres de Hodge d'ordre 2, sur tout anneau commutatif. |
| 14 | énoncé | Page 26, la forme $\chi$ et la reformulation  | `DonneesHodge.chi_eq`, `DonneesHodge.identite_iff_chi`, `reformulation_spec` | B | Forme χ et reformulation confirmées telles qu'énoncées. |
| 15 | remarque | —  | — | A | Généralité : tout anneau commutatif ; finitude seulement pour Lefschetz. |
| 16 | encadré/théorème | Grothendieck, pages 47 et 48, \emph{proposition}, b) $\Rightarrow$ $C$ ♦■44708 | `inverse_Lefschetz_algebrique` | A | Piste tranchée, tient tel qu'énoncé ; PR mathlib ouverte #44708. |
| 17 | lemme | Cayley--Hamilton `lem:16-ch`  | `inverse_mem_of_charpoly` | C | Lemme de Cayley–Hamilton auxiliaire de la preuve du théorème 16. |
| 18 | remarque | —  | — | B | Cayley–Hamilton écrit en w = uv comme la lecture ; condensable au verdict. |
| 19 | remarque | —  | — | C | Décrit la PR mathlib. |
| 20 | encadré/théorème | Grothendieck, pages 4 à 17, critère de Lefschetz dans un anneau gradué ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 4–17) : Λ et projecteurs primitifs dans ℰ, sur ℤ. |
| 21 | encadré/theoreme* | Grothendieck, page 49, variantes en dimension critique ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 49) : variantes A'⁰, A''⁰ entraînent A⁰. |

### Cote 161-2 — Monadicité de Beck et caractérisation de Gabriel–Ulmer

Verdict : *tient tel qu'énoncé* · théorème principal `caracterisation_gabriel_ulmer` · 1566 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Théorème de monadicité, page 33 ; théorème de Beck  | `monadicite` | B | Théorème de Beck, page confirmée telle qu'énoncée. |
| 2 | lemme | `lem:161-2-grossier`  | — | C | Lemme auxiliaire (monadicité grossière duale) servant seulement à la preuve. |
| 3 | définition | —  | — | B | Définition utile au lecteur du corollaire de Gabriel–Ulmer. |
| 4 | énoncé | Corollaire, pages 60 et 61 ; théorème de Gabriel--Ulmer  | `caracterisation_gabriel_ulmer` | B | Corollaire confirmé : théorème de Gabriel–Ulmer, notion moderne. |
| 5 | énoncé | Lemme, page 77  | `lemme_ind` | B | Lemme de la page 77 confirmé : Ind(Σ) ≃ préfaisceaux exacts à gauche. |
| 6 | remarque | —  | — | B | Situation bibliographique ; se condense dans le verdict. |
| 7 | encadré/theoreme* | Grothendieck, pages 39, 41 et 42, deux topos classifiants non cohérents ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 39, 41–42) : deux topos classifiants non cohérents. |
| 8 | encadré/theoreme* | Grothendieck, pages 47 à 49, anneaux de caractéristique définie ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 47–49) : caractéristique définie, réunion de sous-topos. |
| 9 | encadré/theoreme* | D'après les pages 92 à 95, le corps universel, forme complétée par l'édition ♦◇ | — | D-garder | Énoncé non démontré : corps universel, site des anneaux absolument plats. |

### Cote 1 — Système (16) des valeurs singulières, cas m ≤ 2

Verdict : *en partie* · théorème principal `sigma_two_add_le` · 3865 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Pages 71 et 72, le système (16) pour $m \leq 1$ ♦ | `sum_singularValues_add_le`, `sigma_system_of_le_one` | A | Piste : système (16) pour m ≤ 1, inégalité de Ky Fan absente de mathlib. |
| 2 | énoncé | Page 71, du système (16) à la forme produit (15)  | `prod_le_of_sigma_system`, `one_add_singularValues_zero_le` | B | Implication (16) ⇒ (15) confirmée, coefficient par coefficient. |
| 3 | lemme | `lem:1-bessel`  | `sum_norm_inner_sq_le` | C | Lemme auxiliaire (Bessel) de la preuve de Ky Fan. |
| 4 | lemme | `lem:1-poids`  | `sum_mul_le_sum_range` | C | Lemme auxiliaire de poids pour Ky Fan. |
| 5 | lemme | `lem:1-schmidt`  | `inner_apply_ebasis`, `norm_apply_ebasis`, `apply_ebasis_eq` | C | Lemme auxiliaire (décomposition de Schmidt). |
| 6 | lemme | principe de Ky Fan, majoration `lem:1-kyfan`  | `norm_sum_inner_le` | C | Principe de Ky Fan, lemme auxiliaire de la preuve. |
| 7 | remarque | —  | — | B | Ky Fan publié 1951, preuve classique ; condensable au verdict. |
| 8 | remarque | —  | — | B | Réciproque non vérifiée ; se condense dans le verdict de 2. |
| 9 | encadré/théorème | Grothendieck, pages 71 et 72, le système (16) pour $m = 2$ ♦■44757,44759 | `sigma_two_add_le`, `sigma_system_of_le_two` | A | Piste : cas m = 2 tient tel qu'énoncé ; PR mathlib #44757, #44759. |
| 10 | lemme | Lagrange `lem:1-lagrange`  | `sum_sum_norm_sub_sq_le` | C | Inégalité de Lagrange, lemme auxiliaire du cas m = 2. |
| 11 | lemme | poids pour $\sigma^2$ `lem:1-poids2`  | `sum_sum_mul_le_of_weights` | C | Lemme de poids auxiliaire du cas m = 2. |
| 12 | lemme | Cauchy--Binet pour les mineurs d'ordre $2$ `lem:1-binet`  | `two_mul_sum_minor` | C | Cauchy–Binet pour mineurs d'ordre 2, auxiliaire. |
| 13 | remarque | —  | — | B | Voie Λ² par mineurs, constante 1/2 de la page ; condensable au verdict. |
| 14 | encadré/théorème | Grothendieck, pages 71 à 73, le système (16) ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 71–73) : système (16) complet, opérateurs compacts. |
| 15 | remarque | —  | — | C | Redit l'absence de Ky Fan dans mathlib. |
| 16 | remarque | —  | — | C | Décrit les PR mathlib. |

### Cote 113 — Invariance des modules par enveloppe de Karoubi

Verdict : *tient, plus généralement* · théorème principal `morita` · 1245 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | définition | —  | — | B | Définition de l'enveloppe de Karoubi, utile au lecteur de l'énoncé. |
| 2 | énoncé | Page 3, la note marginale ■44726 | `morita`, `morita_module` | A | PR mathlib ouverte #44726 ; tient sans petitesse ni but abélien. |
| 3 | lemme | `lem:113-univ`  | `enveloppe_libre` | C | Propriété universelle classique, auxiliaire de la preuve. |
| 4 | lemme | `lem:113-op`  | `toKaroubi_op_eq` | C | Lemme auxiliaire : enveloppe de l'opposée. |
| 5 | lemme | `lem:113-restr`  | `restriction_isEquivalence` | C | Lemme auxiliaire : restriction côté opposé. |
| 6 | lemme | `lem:113-decomp`  | `decomp` | C | Lemme auxiliaire : décomposition des flèches de Kar P. |
| 7 | lemme | `lem:113-add`  | `additive_of_toKaroubi_op` | C | Lemme auxiliaire : additivité du prolongement. |
| 8 | remarque | —  | — | A | Hypothèses plus faibles que la lecture : ni petitesse, ni but abélien. |
| 9 | remarque | —  | — | B | Attribution Karoubi, nom de Morita ; condensable au verdict. |
| 10 | remarque | —  | — | C | Décrit la PR mathlib. |

### Cote 125 — Trois étages de la carte de dualité ; lemme III-18

Verdict : *tient tel qu'énoncé* · théorème principal `etage1_iff_etage2` · 1759 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Feuillet 2, trois premiers étages  | `etage1_iff_etage2`, `etage2_iff_etage3`, `bornes` | B | Carte confirmée : trois étages équivalents, dualité admise. |
| 2 | lemme | `lem:125-etage12`  | `etage1_iff_etage2` | C | Lemme auxiliaire : premier étage lu dans la suite exacte. |
| 3 | lemme | `lem:125-etage23`  | `etage2_iff_etage3` | C | Lemme auxiliaire : passage au troisième étage par transposition. |
| 4 | énoncé | Feuillet 3, III-18, forme affine  | `lemme_III18`, `lemme_III18_general` | B | Lemme III-18 confirmé, fait classique. |
| 5 | remarque | —  | — | B | Vaut pour toute suite exacte longue ; renvoi à Hartshorne 1970. |
| 6 | remarque | —  | — | A | Corrige la lecture : q ≤ r − m, non q < r − m. |
| 7 | remarque | —  | — | B | Hypothèses de la marge servent à la présentation finie ; condensable. |
| 8 | encadré/theoreme* | Grothendieck, pages 2, 4 et 7, dimension cohomologique du complémentaire ; voir aussi Har… ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 2, 4, 7) : dimension cohomologique du complémentaire, comparaison formelle. |

### Cote 37 — Contre-exemple à EGA I 10.10.5 (lettre à Dieudonné)

Verdict : *tient, plus généralement* · théorème principal `no_finitePresentation_inducing` · 1294 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | lemme | `lem:37-lambda`  | `lam_mul_gen`, `lam_mul_Xpow` | C | Lemme auxiliaire sur les formes λᵢ, sert à la minimalité. |
| 2 | théorème | Grothendieck, page 92, minimalité des générateurs `thm:37-minimal` ♦ | `Jn_spanRank`, `Jn_not_generated`, `le_of_lifts` | A | Piste : J_n exige n + 1 générateurs ; indépendance de la lettre fausse. |
| 3 | énoncé | Page 92, compatibilité `prop:37-compat`  | `Mn_finitePresentation`, `Jn_map_succ` | B | Compatibilité du système M_n confirmée, vérification directe. |
| 4 | lemme | l'étape de Schanuel `lem:37-schanuel`  | `ideal_spanRank_le_of_presentation` | C | Étape de Schanuel, lemme auxiliaire de la preuve du contre-exemple. |
| 5 | théorème | D'après la page 92, contre-exemple à EGA I 10.10.5, sous une forme plus générale `thm:37-contre` ♦ | `no_finitePresentation_inducing` | A | Contre-exemple à EGA I 10.10.5, sous une forme plus générale. |
| 6 | remarque | —  | — | A | Hypothèses superflues ; borne p + 1 au lieu de p + q ; corrige la lettre. |

### Cote 44 — Intégralité des nombres de Cartan depuis les axiomes

Verdict : *en partie : axiomes seuls insuffisants* · théorème principal `cartan_int_of_indivisible` · 1187 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Page 4, de l'indivisibilité à l'intégralité ♦■44971 | `cartan_int_of_indivisible`, `int_of_smul_mem` | A | PR mathlib ouverte ; l'indivisibilité donne l'intégralité dans tout sous-groupe |
| 2 | remarque | —  | — | A | Hypothèses superflues (liberté, finitude, forme) ; à fondre dans l'énoncé 1 |
| 3 | contre-ex. | Page 4, les trois axiomes seuls ♦ | `axioms_not_integral`, `generates`, `reduced_rat`, `symmetries`, `cartan_exists`, `cartan_eq_two_thirds`, `not_integral_base` | A | Contre-exemple : les trois axiomes seuls ne donnent pas l'intégralité |
| 4 | remarque | —  | `cartan_not_int`, `divisible`, `not_integral_base` | A | Corrige la fiche sur le système simple ; crochet non réfuté, à fondre |

### Cote 21 — Modules de I-torsion injectifs et Γ_I sur anneau noethérien

Verdict : *tient, lecture corrigée* · théorème principal `proposition2_15` · 1324 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | définition | —  | — | B | Définitions de I-torsion et d'exactitude sur C, utiles au lecteur de 2.15 |
| 2 | énoncé | Proposition 2.15 ■44724 | `proposition2_15` | A | PR mathlib ouverte (#44724) ; critère d'injectivité confirmé |
| 3 | énoncé | Corollaire 2.16  | `corollaire2_16` | A | Énoncé de la PR #44724 (composante I-primaire d'un injectif) |
| 4 | lemme | `lem:21-puissance`  | `tue_de_type_fini` | C | Lemme auxiliaire de la preuve de 2.15 |
| 5 | remarque | —  | — | A | Correction de la page : Artin–Rees avec le module ambiant, à fondre |
| 6 | remarque | —  | — | B | Finitude utilisée seulement via les A/I^m ; se condense en verdict |
| 7 | remarque | —  | — | B | Aucune finitude de M dans 2.16 ; se condense en verdict |
| 8 | remarque | —  | — | C | Décrit la tenue de la PR mathlib |
| 9 | encadré/théorème | Grothendieck, pages 21 à 26, critère ponctuel pour une catégorie fibrée ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 21–26) ; critère ponctuel, piste ouverte |

### Cote 22 — Produits de plats ; k[[t]] non formellement lisse, topologie discrète

Verdict : *tient, plus généralement* · théorème principal `not_formallySmooth_of_field` · 2616 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Lemme 3.3 ■44715 | `lemme3_3` | A | PR mathlib ouverte (#44715) ; vaut sur tout anneau commutatif |
| 2 | énoncé | Corollaire 3.4 ; cas noethérien du théorème de Chase ■44716 | `corollaire3_4`, `corollaire3_4_coherent` | A | PR mathlib ouverte ; la preuve ne demande qu'un anneau cohérent |
| 3 | énoncé | Corollaire 3.5 ■44714 | `corollaire3_5` | A | PR mathlib ouverte ; démontré pour systèmes indexés par ℕ |
| 4 | lemme | `lem:22-libre`  | `can_bijective_fin` | C | Lemme auxiliaire de la preuve de 3.3 |
| 5 | lemme | `lem:22-hyp`  | `hypothese_iff_noetherien` | A | L'hypothèse de 3.4 équivaut à noethérien ; énoncé de PR |
| 6 | lemme | `lem:22-prod2`  | `flat_prod` | C | Lemme auxiliaire de la preuve de 3.5 |
| 7 | remarque | —  | — | B | Généralité et réciproque de Lenzing ; se condense en verdict |
| 8 | remarque | —  | — | A | « Par exemple noethérien » trompeur : équivalence ; à fondre dans 3.4 |
| 9 | remarque | —  | `corollaire3_4_coherent` | A | Cas du théorème de Chase, cohérent suffit ; à fondre dans 3.4 |
| 10 | remarque | —  | — | C | Décrit la tenue des PR mathlib |
| 11 | lemme | `lem:22-obstruction`  | `no_derivation`, `coordProj_eventually_zero` | C | Lemme auxiliaire de l'obstruction, servant aux énoncés 12 et 13 |
| 12 | théorème | D'après les pages 22 et 24, obstruction différentielle sur {$k[[t]]$}, topologie discrète… ♦ | `no_derivation_extending_d`, `not_formallySmooth_discrete`, `basisDx_apply` | A | Tranche la piste : obstruction discrète tient sans réduction à D(t)=0 |
| 13 | corollaire | `prop:22-corps`  | `not_formallySmooth_of_field`, `not_formallySmooth_of_basis` | A | Généralisation : tout corps avec Ω infini, toute base, toute caractéristique |
| 14 | remarque | —  | — | A | Réduction à D(t)=0 inutile ; à fondre dans l'énoncé 12 |
| 15 | encadré/théorème | Grothendieck, pages 26 et 28, noyau des différentielles ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 26 et 28) ; contre-exemple sur le noyau des différentielles |

### Cote 67 — Involutions des modules et triplets (P, Q, m)

Verdict : *tient, plus généralement* · théorème principal `equivalence` · 1607 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | encadré/théorème | Grothendieck, page 90, \emph{proposition} ♦ | `equivalence`, `inverse_obj_iso`, `essSurj_witness`, `inf_eigen_eq_bot`, `mem_two_of_plus`, `mem_two_of_minus` | A | Tranche la piste : équivalence involutions–triplets, anneau quelconque |
| 2 | remarque | —  | — | A | Seule la 2-régularité sert, sans finitude ; à fondre dans l'énoncé |
| 3 | remarque | —  | — | C | Décrit le sens de la vérification et les choix de formalisation |

### Cote 19 — Théorème 1.12 de comonadicité ; comonade sur une base produit

Verdict : *faux sur la page* · théorème principal `theoreme_b_necessite_fausse` · 3545 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | définition | —  | `ConditionC` | B | Définition de la condition C, utile au lecteur de 1.12 |
| 2 | énoncé | Théorème 1.12, page 4  | `theoreme_a`, `theoreme_a'`, `theoreme_b_suffisance`, `theoreme_b_necessite_fausse`, `comonadique`, `non_conditionC` | A | Faux sur la page : la nécessité de b) a un contre-exemple |
| 3 | lemme | `lem:19-scinde`  | — | C | Lemme auxiliaire de la preuve de Beck |
| 4 | lemme | `lem:19-paire`  | — | C | Lemme auxiliaire de la preuve de Beck |
| 5 | lemme | `lem:19-comp`  | — | C | Lemme auxiliaire de la preuve de Beck |
| 6 | énoncé | Théorème de Beck, forme exacte ■44727 | `beck_iff` | A | PR mathlib ouverte (#44727) : Beck sous forme d'équivalence |
| 7 | énoncé | Pages 7 et 8, la matrice de la comonade ♦ | `adjPi_counit`, `matrice`, `counit_matrice`, `comult_matrice`, `comult_unique` | A | Piste : la comonade sur base produit est une matrice |
| 8 | énoncé | Pages 7 à 9, les cas dégénérés et les deux facteurs ♦ | `lam_diag`, `lam_isIso_left`, `lam_isIso_right`, `lam_eq_counit_comp_lamUnit`, `deuxFacteurs_left`, `deuxFacteurs_right` | A | Piste : cas dégénérés et réduction à deux facteurs confirmés |
| 9 | encadré/contre-ex. | Page 7, « ou $I$ fini » ♦ | `matrice_fini_fausse` | A | Contre-exemple : « ou I fini » faux sur la page |
| 10 | remarque | —  | — | A | L'hypothèse de commutation aux produits suffit, second exemple faux ; à fondre |
| 11 | remarque | —  | — | A | (3.9) sans hypothèse ; à fondre dans l'énoncé 7 |
| 12 | énoncé | Pages 14 et 15 ; théorème de Gabriel--Popescu  | `gabriel_popescu` | B | Classique, confirmé sous la forme de la lecture |
| 13 | remarque | —  | — | A | a) sous la seule condition C ; à fondre dans 1.12 |
| 14 | remarque | —  | — | A | La nécessité de b) est fausse, l'erreur est sur la page |
| 15 | remarque | —  | — | A | Correction de la lecture : condition C plus forte que Beck |
| 16 | remarque | —  | — | B | Seul le plongement pleinement fidèle est acquis ; se condense en verdict |
| 17 | remarque | —  | — | C | Décrit la tenue de la PR mathlib |
| 18 | encadré/théorème | Grothendieck, pages 7 à 11, comonade sur une base produit ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 7–11) ; coünité, coassociativité et quadruplets non démontrés |
| 19 | encadré/theoreme* | Grothendieck, pages 79 et 80, chaînes d'adjoints ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 79–80) ; chaînes de n adjoints, question ouverte |

### Cote 133 — Centre et groupe dérivé par deux modules croisés

Verdict : *tient, hypothèses plus faibles* · théorème principal `injective_Psi_iff` · 2050 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | lemme | `lem:133-central`  | `comm_mul_central`, `comm_mul_central_left` | C | Lemme auxiliaire de la preuve de l'injectivité de Ψ_G |
| 2 | encadré/théorème | Grothendieck, page 46, l'injectivité de $\Psi_G$ ♦ | `injective_Psi_iff`, `Psi_mul`, `phi_eq_of_rel` | A | Piste : tient sous la seule hypothèse N′ ⊂ Cent(G) |
| 3 | remarque | —  | — | A | Hypothèses superflues ([N, N′] = 1, N ⊃ D(G)) ; à fondre |
| 4 | lemme | `lem:133-D`  | `Dcal_comm`, `pi0_comm` | C | Lemme auxiliaire servant à l'énoncé de λ_G |
| 5 | énoncé | Pages 51 et 52, la surjectivité de $\lambda_G$ ♦ | `eq_commutator_iff_lam_surjective`, `lam_swap`, `lam_self` | A | Piste : N = D(G) ssi λ_G engendre, confirmé |
| 6 | remarque | —  | — | A | Nécessité de N′ central (exemple Q8), commutativité de π₀ déduite ; à fondre |
| 7 | énoncé | Pages 48 et 52, le changement de $G$ en $G_1$ ♦ | `cE_spec`, `cE_well_defined`, `commutator_G1`, `Psi_G1`, `lam_G1` | A | Piste : changement de G en G₁, prouvé comme identité de commutateurs |
| 8 | remarque | —  | — | A | Fixe le signe laissé ouvert par la page ; à fondre |
| 9 | encadré/exemple | Grothendieck, pages 42 et 43, quotient affine non constructible ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 42–43) ; quotient affine non constructible, piste |

### Cote 161-1 — Adjonctions idempotentes : conditions équivalentes, parties fixes, descente d'adjoints

Verdict : *tient, plus généralement* · théorème principal `idempotent_tfae` · 3285 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | (1), page 3  | `condition1`, `condition1_non_surabondante` | B | page confirmée ; l'exemple de la marge montre la seconde condition nécessaire |
| 2 | énoncé | Adjonctions idempotentes, page 5 ■44723 | `idempotent_tfae` | A | PR mathlib ouverte #44723 ; deux conditions du manuscrit redondantes |
| 3 | énoncé | Objets locaux, pages 6 et 7  | `sigma_iff`, `local_mem_essImage`, `local_iff_mem_essImage` | B | fait classique des sous-catégories réflexives, « Or c'est vrai » confirmé |
| 4 | lemme | `lem:161-1-hom`  | `map_bijective_iff` | C | lemme auxiliaire servant seulement à la preuve de (1) et (2) |
| 5 | énoncé | (2), page 3  | `condition2` | B | dual de (1), confirmé tel qu'énoncé |
| 6 | énoncé | Les cinq conditions, page 3  | `five_conditions_tfae`, `corresp_of` | B | confirmé ; la cinquième condition répète la deuxième |
| 7 | énoncé | Les points fixes, page 4 ■44723 | `fixedEquiv`, `condition1_iff_le_E0`, `condition2_iff_le_F0` | A | PR mathlib ouverte #44723 : parties fixes équivalentes, maximales |
| 8 | énoncé | Conditions 1), 3) et 4), page 5 ; la préservation des colimites  | `condition1_p5_iff`, `reflectorAdj`, `reflector0_preservesColimits`, `condition4`, `coreflectorAdj` | B | confirmé ; préservation des colimites déjà connue pour tout adjoint |
| 9 | énoncé | La descente d'adjoints, page 6  | `descent`, `descent_isLeftAdjoint` | A | tient sans β pleinement fidèle, hypothèse de la page superflue |
| 10 | remarque | —  | — | C | redit la réponse à la marge, déjà dans l'énoncé (1) |
| 11 | remarque | —  | — | B | référence Gabriel–Zisman, se condense dans la ligne de verdict |
| 12 | remarque | —  | — | B | cinquième condition redondante, à fondre dans le verdict des cinq conditions |
| 13 | remarque | —  | `descent` | A | porte la trouvaille : β pleinement fidèle inutile ; à fondre |
| 14 | remarque | —  | — | C | reformule l'équivalence des deux hypothèses déjà établie |
| 15 | remarque | —  | — | B | référence Borceux, se condense dans la ligne de verdict |
| 16 | remarque | —  | — | C | décrit la tenue de la PR mathlib |
| 17 | encadré/définition | Grothendieck, pages 11 et 12, contractions ♦ | — | C | définition encadrée sans énoncé gardé qu'elle serve ; pages 11–12 non traitées |

### Cote 39 — Préparation formelle : division par F, cas adique et discret

Verdict : *en partie* · théorème principal `preparation_discrete` · 1269 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Théorème de préparation « formel » ■44725 | `preparation_adique`, `preparation_discrete` | A | PR mathlib ouverte #44725 ; seuls cas adique et discret démontrés |
| 2 | lemme | `lem:39-adique`  | `preparation_adique` | B | cas adique, conséquence directe de la division de Weierstrass |
| 3 | lemme | `lem:39-nilp`  | `isAdicComplete_of_nilpotent`, `ideal_nilpotent` | C | lemme auxiliaire du cas discret ; contenu de la PR, porté par l'énoncé 1 |
| 4 | remarque | —  | `preparation_adique` | A | idéal non nécessairement de type fini : hypothèse de la lecture superflue |
| 5 | remarque | —  | — | B | division de Weierstrass admise, se condense dans le verdict |
| 6 | remarque | —  | — | B | précise ce qui reste non démontré (a_i ∈ √I) |
| 7 | remarque | —  | — | C | décrit la tenue de la PR mathlib |
| 8 | encadré/theoreme* | D'après les pages 9 à 14, axiomatique des fonctions implicites, forme corrigée par l'édit… ♦◇ | — | D-garder | Énoncé non démontré ; axiomatique des fonctions implicites, piste candidate |

### Cote 41 — Section générique continue ssi f ouvert, relèvement des générisations

Verdict : *tient, plus généralement* · théorème principal `proposition1` · 1175 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Proposition 1  | `proposition1`, `i_iff_ii`, `iii_iff_iiibis` | A | tient plus généralement ; finitude requise seulement pour (iii bis) ⇒ (ii) |
| 2 | définition | —  | — | B | définition de la section générique, utile au lecteur de l'énoncé |
| 3 | lemme | `lem:41-formule`  | `preimage_eq_image` | C | lemme auxiliaire, formule φ⁻¹(U) = f(U) de la page |
| 4 | lemme | `lem:41-top`  | `i_iff_ii`, `i_imp_iii`, `iii_iff_iiibis` | C | implications topologiques, déjà portées par l'énoncé et sa remarque |
| 5 | remarque | —  | `iiibis_not_imp_ii` | A | contre-exemple : l'hypothèse de finitude ne peut être retirée |
| 6 | remarque | —  | `i_iff_ii`, `i_imp_iii`, `iii_iff_iiibis` | A | généralisation : sans type fini ni continuité ; à fondre dans l'énoncé |
| 7 | remarque | —  | — | B | EGA IV 1.10.4 admis, se condense dans le verdict |
| 8 | encadré/theoreme* | D'après les pages 3 et 8 à 10, composantes irréductibles des fibres, forme reconstituée p… ♦◇ | — | D-garder | Énoncé non démontré ; critère des composantes irréductibles des fibres, piste |

### Cote 42 — Sections d'un faisceau = familles cohérentes de germes ; lemme 2

Verdict : *tient, plus généralement* · théorème principal `proposition` · 2780 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Proposition et lemme 1, page 3 ■44707 | `lemme1_faisceau`, `proposition` | A | PR mathlib ouverte #44707 ; (H) employée sous forme plus faible |
| 2 | énoncé | Lemme 2, pages 4 et 5  | `lemme2_1`, `lemme2_2`, `lemme2_page` | A | (2) vaut pour tout anneau commutatif ; glose « annulateur » de la lecture corrigée |
| 3 | énoncé | Lemme 1 et corollaire 1, pages 3 et 4, cas affine  | `lemme1`, `corollaire1` | B | cas affine confirmé ; résultat connu (Ferrand) |
| 4 | lemme | `lem:42-ouvert`  | `isOpen_of_stableUnderGeneralization` | A | constructibilité inutile au « donc » de la page ; contenu de la PR #44707 |
| 5 | lemme | `lem:42-lift`  | `lift_injective` | C | lemme auxiliaire de localisation servant seulement aux preuves |
| 6 | lemme | `lem:42-tue`  | `exists_mul_eq_zero_of_ker` | C | lemme auxiliaire, déjà dans mathlib |
| 7 | remarque | —  | — | B | référence Ferrand, se condense dans la ligne de verdict |
| 8 | remarque | —  | `isOpen_of_stableUnderGeneralization` | A | porte la trouvaille : constructibilité non employée ; à fondre |
| 9 | remarque | —  | `proposition` | A | (H) faible suffit ; injectivité sans (H) ni noethérianité |
| 10 | remarque | —  | `lemme2_2` | A | noethérien inutile dans (2) ; « annulateur de A − p » ne convient pas |
| 11 | remarque | —  | — | C | décrit la tenue de la PR mathlib |
| 12 | remarque | —  | `lemme2_page` | B | détails de la forme (3) et coquille s_x, condensables dans le verdict |
| 13 | encadré/theoreme* | D'après les pages 1 à 6, réseaux d'anneaux locaux, forme corrigée par l'édition ♦◇ | — | D-garder | Énoncé non démontré ; pleine fidélité des réseaux d'anneaux locaux, piste |

### Cote 153 — Polynômes à valeurs entières : lemme, co-opérations, Pólya, Ω = Ω₀ ⊕ Ω⁰

Verdict : *tient, plus généralement* · théorème principal `coaddition_existsUnique_of_injective` · 4413 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | définition | —  | — | B | définition de Ω, sert au lecteur des énoncés gardés |
| 2 | énoncé | Lemme, page 3 ■44717 | `lemme_coordonnees`, `lemme_injective`, `lemme_range` | A | PR mathlib ouverte #44717 ; inclusion k₀ ⊂ K₀ superflue |
| 3 | lemme | `lem:153-nat`  | `coords_rTensor` | C | lemme auxiliaire de naturalité des coordonnées |
| 4 | lemme | `lem:153-image`  | `mem_range_rTensor` | C | lemme auxiliaire, porté par l'énoncé du lemme de la page 3 |
| 5 | lemme | `lem:153-un`  | `range_mk_one` | C | lemme auxiliaire servant seulement à la preuve |
| 6 | remarque | —  | — | A | porte la trouvaille : l'inclusion k₀ → K₀ ne sert pas ; à fondre |
| 7 | énoncé | Page 3, stabilité  | `comp_mem_Omega` | B | stabilité par composition, calcul direct |
| 8 | énoncé | Page 3, les co-opérations  | `Phi_injective`, `mem_range_Phi_iff`, `coaddition_existsUnique`, `comultiplication_existsUnique`, `comp_add_eq`, `comp_mul_eq` | B | cas localisé confirmé ; englobé par l'énoncé sans localisation |
| 9 | lemme | `lem:153-indep`  | `sum_smul_basis_eq_zero` | C | lemme auxiliaire de la preuve des co-opérations |
| 10 | lemme | `lem:153-engendre`  | `exists_sum_smul_basis` | C | lemme auxiliaire de la preuve des co-opérations |
| 11 | remarque | —  | — | C | reformule l'hypothèse employée, redit par l'énoncé suivant |
| 12 | énoncé | Page 3, les co-opérations sans localisation ♦ | `omegaBaseChange_surjective`, `coaddition_existsUnique_of_injective`, `comultiplication_existsUnique_of_injective`, `omegaBaseChange_injective_of_flat` | A | piste 153-relative-int-coproducts tranchée en partie : cas plat |
| 13 | remarque | —  | — | A | question ouverte sans platitude ; à fondre dans le verdict de la piste |
| 14 | énoncé | Page 2, théorème de Pólya ■44722 | `polya`, `binom_linearIndependent` | A | PR mathlib ouverte #44722 (base de Pólya) |
| 15 | énoncé | Page 2, Vandermonde, et les co-opérations de $\mathrm{Int}(\mathbf Z)$  | `vandermonde`, `coaddition_binom`, `comultiplication_binom` | B | Chu–Vandermonde, calcul direct des γ de la page |
| 16 | remarque | —  | — | C | conséquences sans énoncé Lean et attribution, reformulation |
| 17 | énoncé | Page 5, $\Omega = \Omega_0 \oplus \Omega^0$  | `isCompl_constants_zeroPart` | A | décomposition sans axiome 3) ni unité T, hypothèses plus faibles |
| 18 | remarque | —  | `isCompl_constants_zeroPart` | A | porte la généralisation (ni 3) ni T) ; à fondre dans l'énoncé |
| 19 | énoncé | Page 7, l'exemple $\mathrm{Appl}(A, A)$  | `appl_not_coaddition`, `mem_constants_appl` | B | contre-exemple de 3a) pour A infini, confirme la lecture |
| 20 | énoncé | Page 7, l'analyseur des polynômes et l'application $\Omega \to \Omega_{\Omega_0}$  | `mem_constants_poly`, `poly_toAppl_not_injective`, `poly_toAppl_injective` | B | exemples de la page 7 confirmés, calcul direct |
| 21 | énoncé | {Page 7, $k[[T]]^+$ ne vérifie pas 3a)}  | `geom_not_finite_coaddition`, `pascal_det` | A | corrige la note de la lecture : Pascal sans le coefficient (0,0) |
| 22 | remarque | —  | `geom_not_finite_coaddition` | A | correction de la lecture (matrice, hypothèses de 3a)) ; à fondre |
| 23 | remarque | —  | — | C | décrit la tenue des PR mathlib |
| 24 | encadré/théorème | Pages 3 et 9, co-opérations de $\mathrm{Int}$ relatif, forme corrigée par l'édition ♦◇ | — | D-garder | Énoncé non démontré ; co-opérations sous K₀ ⊗ K₀ = K₀ seul, piste |

### Cote 40 — La régularité des torseurs sous α_p ne passe pas à la somme

Verdict : *tient, plus généralement* · théorème principal `fibre_nilpotent` · 1577 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | lemme | `lem:40-dvr`  | `isDVR_adjoinRoot`, `irreducible_radical`, `isDomain_radical` | A | Porte la généralisation : tout anneau de valuation discrète, tout n, sans complétude |
| 2 | énoncé | Page 26, le cusp $T^n = X^2$ `prop:40-cusp`  | `cusp_not_valuation`, `not_isDVR_cusp_odd`, `not_isDomain_cusp_even`, `cusp_two_nilpotent` | B | Non-régularité du cusp, calcul direct servant au point 2 du théorème |
| 3 | théorème | Grothendieck, pages 26 et 27, la régularité ne passe pas à la somme des torseurs sous $\a… ♦ | `isDVR_root_X`, `isDVR_root_neg_X_add_X_sq`, `neg_X_add_X_sq_eq_pow`, `fibre_ne_zero`, `fibre_nilpotent` | A | Énoncé de la piste, confirmé et tranché |
| 4 | remarque | —  | — | A | Porte la trouvaille « plus généralement » ; à fondre dans le verdict |

### Cote 78 — Critère u_α^n = id ⇔ F_n(α) = 0 sur un anneau ; 2p-gones

Verdict : *tient, plus généralement* · théorème principal `zpow_eq_one_iff` · 2340 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Page 109, les polynômes $F_n$  | `F_neg`, `F_even_closed`, `F_odd_closed` | B | Formules de la page pour F_n, calcul direct |
| 2 | théorème | Grothendieck, pages 109 à 113, le critère de fermeture sur un anneau ♦ | `F_identity`, `F_bezout`, `u_zpow_apply`, `vertex`, `zpow_eq_one_iff`, `vertex_eq_iff`, `zpow_fix_iff` | A | Énoncé de la piste : critère de fermeture sur tout anneau |
| 3 | remarque | —  | `inv_eq_conj`, `swap_vertex`, `conic_invariant`, `affine_eq_of_frame` | B | Confirme tel qu'énoncé ; matrice barrée, faits annexes condensables |
| 4 | contre-ex. | Page 113, le coefficient de la page  | `page_A_four_fails` | A | Correction : le coefficient de Bézout de la page échoue pour n = 4 |
| 5 | énoncé | Pages 84, 85 et 94 à 99, existence des $2p$-gones en bande ♦ | `strip_vertex`, `strip_lines`, `strip_conic`, `strip_orderOf`, `strip_vertex_eq_iff`, `strip_noncollinear`, `linPart_det`, `imp_zpow_apply`, `imp_vertex`, `imp_orderOf`, `imp_vertex_eq_iff`, `imp_noncollinear`, `imp_inv_eq_conj`, `imp_linPart_det` | A | Énoncé de la piste des 2p-gones en bande, existence démontrée |
| 6 | remarque | —  | — | A | Généralisation : toute caractéristique, p non premier, p = 2 et p = 0 |

### Cote 84 — Produit des algèbres quadratiques, triplets, extensions χ-scindées, en coordonnées

Verdict : *en partie* · théorème principal `coinvariants_bijective_iff` · 4634 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Pages 47 à 53, \emph{le théorème des triplets, cas libre} ♦ | `qalg_iso_iff_moves`, `qalg_iso_iff_disc`, `translates_iff`, `translates_unique`, `exists_of_congr`, `int_disc_iff`, `int_qalg_iso_iff`, `two_regular_needed` | A | Piste, cas libre ; « 2 régulier » nécessaire (contre-exemple sur F₂) |
| 2 | remarque | —  | — | B | Littérature (Voight) et portée, condensables dans le verdict |
| 3 | énoncé | Pages 63, 64, 89 et 102, \emph{la formule du produit} ♦ | `identity_page64`, `tensor_root`, `disc_mul`, `c_two_forms` | A | Piste ; formule du produit, lecture 4c₁c₂ corrigeant la page |
| 4 | remarque | —  | — | B | Littérature et confirmation de 4c₁c₂, condensables dans le verdict |
| 5 | encadré/théorème | Grothendieck, pages 84 et 85, \emph{proposition} ♦ | `coinvariants_bijective_iff` | A | Piste ; proposition tient sur tout anneau, dans les deux sens |
| 6 | énoncé | Page 86, \emph{corollaire} ♦ | `invariants_of_span_eq_top`, `invariants_universally_iff`, `invariants_not_iff` | A | « Universellement » nécessaire : contre-exemple sur Z[X] |
| 7 | remarque | —  | — | A | Porte la trouvaille : sans changement de base ni réduction à 2 = 0 |
| 8 | énoncé | Pages 77--79 et 123--131, extensions $\chi$-scindées ♦ | `isChiSplitting_of`, `chiSplitting_eq`, `iso_iff`, `transv_comp`, `transv_comp_varpiOf`, `prod_change`, `uProd_cocycle`, `prod_assoc`, `prod_comm`, `prod_unit`, `chiRel_mul`, `invertible_iff` | A | Piste ; produit des extensions χ-scindées en coordonnées, cocycle achevé |
| 9 | remarque | —  | — | B | Portée et cocycle de la page 131, condensables dans le verdict |
| 10 | énoncé | Pages 125, 127 et 169, \emph{produit poussé et produit tiré} ♦ | `push_pull`, `push_pull_square`, `push_pull_unit_iff`, `no_gamma_four` | A | Piste ; hypothèse γχ = 2 nécessaire dès les objets unités |
| 11 | remarque | —  | — | B | Redit la nécessité de γχ = 2 déjà énoncée |
| 12 | encadré/théorème | Grothendieck, pages 45 à 53, classification par triplets ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 45–53) : équivalence avec les triplets, L non trivial |
| 13 | encadré/théorème | Grothendieck, pages 65 à 79, produit des extensions $\chi$-scindées ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 65–79) : produit intrinsèque des extensions χ-scindées |

### Cote 93 — Différence schwarzienne en dérivées divisées : cocycle, fonctions tuées, rigidité

Verdict : *en partie* · théorème principal `rigidity_of_gt` · 4367 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Page 120, le facteur $12$ ♦ | `Ncl_eq`, `G_eq` | B | Identité G = 12 G₀ confirmée telle qu'énoncée |
| 2 | lemme | `lem:93-chaine`  | `chain` | C | Lemme auxiliaire de la relation de cocycle |
| 3 | énoncé | Pages 115 à 117, la relation de cocycle ♦ | `N_comp`, `G0_comp`, `N_X`, `G0_X` | A | Cocycle sans hypothèse ni dénominateur, caractéristiques 2 et 3 comprises |
| 4 | remarque | —  | — | B | Cadre classique et absence d'hypothèse, condensables dans le verdict |
| 5 | énoncé | Page 115, invariance par les homographies ♦ | `N_homography`, `G0_homography`, `G0_homography_const` | B | Invariance par les homographies, confirmée, calcul direct |
| 6 | énoncé | Page 72, les valeurs tests  | `N_X_sq`, `N_X_cube` | B | Valeurs tests ; confirme la correction 1/(4t²) de la lecture |
| 7 | énoncé | Marge de la page 121, les fonctions tuées ♦■44735,44736 | `killed_iff_of_gt`, `killed_iff_two`, `killed_iff_three`, `Killed.comp`, `char_two`, `char_three` | A | PR mathlib ouvertes ; niveau p² nécessaire pour p = 2, 3 |
| 8 | remarque | —  | — | A | Porte la trouvaille : niveau p² nécessaire, correction de la page 72 |
| 9 | lemme | `lem:93-tronque`  | `hasseDeriv_X_pow_mul`, `N_add_X_pow_mul` | C | Lemme auxiliaire de la rigidité dans le modèle tronqué |
| 10 | énoncé | Page 122, le premier terme non affine ♦ | `N_mul_lin`, `step` | C | Étape auxiliaire de la preuve de rigidité |
| 11 | énoncé | Pages 121 à 123, la rigidité ♦■44755,44756 | `rigidity`, `rigidity_of_gt`, `rigidity_iff_of_gt`, `rigidity_four`, `rigidity_nine`, `rigidity_char_zero`, `N_of_homography_trunc` | A | PR mathlib ; rigidité sans hypothèse Pic(A) = 0, pour α = 0 |
| 12 | encadré/contre-ex. | Page 121, le déterminant ♦ | `det_one_square`, `det_one_counterexample` | A | Contre-exemple : la normalisation ad − bc = 1 de la page est fausse |
| 13 | remarque | —  | — | A | Porte la trouvaille : Pic(A) superflu, déterminant unité seulement |
| 14 | encadré/définition | Grothendieck, pages 233 à 235, morphisme dérivé défini par un torseur ♦ | — | C | Définition sans lien avec l'énoncé gardé ni preuve Lean |
| 15 | encadré/théorème | Grothendieck, pages 71 à 73 et 120 à 123, schwarzien à dérivées divisées ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 71–73, 120–123) : schwarzien, cas α ≠ 0 et Pic |
| 16 | remarque | —  | — | C | Décrit les PR mathlib |
| 17 | remarque | —  | — | C | Décrit les PR mathlib |

### Cote 152 — Dictionnaire entre graphes circularisés et contours

Verdict : *en partie ; tête de page fausse* · théorème principal `formules` · 772 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | définition | —  | — | B | Définition des graphes circularisés et contours, nécessaire au lecteur |
| 2 | énoncé | Équivalence, pages 7 et 9, sur les objets  | `formules`, `sommets` | B | Dictionnaire confirmé selon la convention du tableau de la page 9 |
| 3 | énoncé | Connexité, dans la démonstration du critère de la page 9  | `connexe_of_une_face` | B | Connexité par récurrence directe, cas d'un seul cycle |
| 4 | remarque | —  | `tete_page9_incompatible` | A | La tête de la page 9 contredit son tableau : forcerait σ = id |
| 5 | remarque | —  | — | B | Seule σ² = id sert ; dictionnaire classique (Edmonds, Jacques, Cori), condensable |
| 6 | remarque | —  | — | C | Précise seulement la portée : objets, pas morphismes |

### Cote 88 — Ordre 2ν de σ_{ℓ−2}σ_{ℓ−1} ; trichotomie des types (p,q)

Verdict : *tient, plus généralement ; (c₂) corrigée* · théorème principal `proposition_ordre` · 1743 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | définition | —  | — | B | Cadre minimal (torseur, φ, ordre généralisé) nécessaire à l'énoncé |
| 2 | énoncé | Proposition, page 8  | `proposition_ordre` | A | Ordre 2ν sous hypothèses bien plus faibles que la page |
| 3 | énoncé | Article (6), page 14 : l'arithmétique  | `spherique_iff`, `euclidien_iff`, `hyperbolique_iff` | A | Trichotomie (6) démontrée avec la condition (c₂) corrigée |
| 4 | lemme | `lem:88-invol`  | `sigmaDernier_involutive`, `sigmaAvant_mul_self`, `sigmaAvant_mul_sigmaDernier` | C | Lemme auxiliaire de la proposition |
| 5 | lemme | `lem:88-carre`  | `pi_apply`, `pi_sq`, `pi_pow_pair`, `pi_pow_impair` | C | Lemme auxiliaire de la proposition |
| 6 | lemme | `lem:88-fixe`  | `pi_pow_fixe` | C | Lemme auxiliaire de la proposition |
| 7 | lemme | `lem:88-indep`  | `orderOf_indep`, `existe_rep` | C | Lemme auxiliaire de la proposition |
| 8 | remarque | —  | `proposition_ordre` | A | Hypothèses superflues : Weyl, b), c), d) inutiles ; à fondre |
| 9 | remarque | —  | `proposition_ordre` | A | Finitude de W superflue, 2ν vaut avec ordres infinis |
| 10 | remarque | —  | `hyperbolique_iff` | A | Correction de (c₂) : « ≥ 9 et », non « ≥ 10 ou » |
| 11 | remarque | —  | — | B | Sources (Coxeter–Moser, Jones–Singerman), condensable dans le verdict |
| 12 | remarque | —  | — | C | Simple définition reprise de l'Esquisse, sans démonstration |

### Cote 73 — Aires des oreilles : plan projectif des quadrilatères, critère multiplicateur nul

Verdict : *tient, sur tout corps* · théorème principal `zero_multiplier_criterion` · 2552 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | théorème | D'après les pages 5 et 6, forme complétée par l'édition, les quadrilatères forment un pla… `thm:73-quadrilatere` ♦ | `mu_relation`, `quad_moduli`, `exists_quad_of_mu`, `side_eq_zero_iff`, `mu_eq_smul_framePt`, `framePt_three_indep`, `frame_canonical` | A | Piste tranchée : plan projectif, « épi ? » oui, signe ajouté |
| 2 | remarque | —  | `not_wedge13_eq` | A | Ligne 2 du tableau page 5 fausse, contre-exemple ; signe du repère |
| 3 | lemme | paire de directions `lem:73-paire`  | `symProd_proportional_iff` | C | Lemme auxiliaire du critère (paire de directions) |
| 4 | théorème | Grothendieck, pages 15, 18 et 28, critère du cas spécial II `thm:73-critere` ♦ | `zero_multiplier_criterion`, `symProd_formula`, `mult_unique`, `mult_eq_zero_iff`, `eq_zero_of_consecutive` | A | Piste tranchée : critère juste, sur tout corps, multiplicateur unique |
| 5 | remarque | —  | `zero_multiplier_criterion` | A | « Il faut et il suffit » confirmé ; « k infini » superflu ; à fondre |

### Cote 74 — Réduction des graphes à triangles à un carré latin et revêtements

Verdict : *tient sous (Ka) restituée* · théorème principal `Scholie.axiom1_iff_ka` · 4079 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Pages 92 à 99, autour d'un triangle ♦ | `Config.off_unique`, `Config.off_exists`, `Config.sig_sig`, `Config.sig_ne`, `Config.prop2`, `Config.prop5`, `Config.prop3`, `Config.ut_exists`, `Config.ut_unique`, `Config.adj_sig_sig` | B | Propositions 1 à 5 confirmées, étapes vers la Scholie |
| 2 | énoncé | Pages 99, 101 et 102, le carré latin et les revêtements doubles ♦ | `Config.latin`, `Config.transition_trans`, `Config.transition_self`, `Config.card_Et`, `Config.card_UT`, `Config.card_Gam`, `Config.E_equiv` | A | Piste : réduction au carré latin et revêtements doubles |
| 3 | encadré/théorème | Pages 96--100 corrigées par l'édition, Scholie et réciproque ♦ | `Config.scholie_forward`, `Scholie.scholie_converse`, `Scholie.axiom1_iff_ka`, `Scholie.ka_iff` | A | Piste tranchée : Scholie juste seulement avec (Ka) restituée |
| 4 | énoncé | Pages 101 à 103, problèmes I et II ♦ | `LatinCover.star`, `LatinCover.beta`, `LatinCover.converse`, `LatinCover.axiom1_iff_ka` | B | Réciproque reformulée en carré latin, découle de la Scholie |
| 5 | contre-ex. | Pages 96 et 97, contre-exemple de l'édition : la condition (Ka) est nécessaire  | `ka_needed` | A | Contre-exemple : page 97 fausse sans (Ka) |
| 6 | énoncé | Page 116 ♦ | `p116`, `p116_comm` | B | Page 116 confirmée, cas d'une table de groupe |
| 7 | lemme | `lem:74-revetement`  | `card_eq_two_mul` | C | Lemme auxiliaire de dénombrement |
| 8 | lemme | `lem:74-ligne`  | `row_bijective` | C | Lemme auxiliaire de dénombrement |
| 9 | remarque | —  | — | A | Axiome 3 superflu pour la réduction ; à fondre |
| 10 | remarque | —  | `Scholie.axiom1_iff_ka`, `ka_needed` | A | Page 97 demande la condition de marge ; à fondre au contre-exemple |
| 11 | remarque | —  | — | C | Détail de démonstration (proposition 6 remplacée par (Ka)) |
| 12 | remarque | —  | — | B | Portée plus étroite que la lecture, condensable dans le verdict |
| 13 | remarque | —  | `autotopism_iff`, `card_klein_autotopisms` | B | 96 autotopies de la table de Klein, calcul direct |

### Cote 76 — Surjectivité des drapeaux de type H, transitivité de ≺

Verdict : *tient, plus généralement* · théorème principal `flag_lemma` · 1259 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | lemme | `lem:76-produit`  | `mem_mul_of_split` | C | Lemme auxiliaire de la preuve du lemme de surjectivité |
| 2 | théorème | Grothendieck, pages 27 et 28, lemme `thm:76-lemme` ♦ | `flag_lemma` | A | Piste : surjectivité sous hypothèses plus faibles que la page 27 |
| 3 | corollaire | page 27 `cor:76-transitif`  | `prec_trans`, `prec_iff_pair`, `prec_of_mem`, `not_prec_self` | B | Transitivité de ≺, cas particulier H={i,j}, H'={j,k} |
| 4 | remarque | —  | `flag_lemma` | A | Segment final et non-vacuité superflus, σᵢ quelconques ; à fondre |

### Cote 77 — Discriminant universel modulo 2 et 4, symétrie canonique

Verdict : *tient, plus généralement* · théorème principal `disc_even_rank` · 3366 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Page 68, rang impair ♦ | `two_dvd_det_polar`, `det_polar_eq`, `halfDisc_unique`, `det_polarOf_eq` | A | Piste : tient pour tout rang impair, par la matrice antisymétrique, sans graphes. |
| 2 | remarque | —  | — | B | Rattachement à Conrad (Kneser, Grothendieck) ; se condense dans le verdict. |
| 3 | énoncé | Pages 68 à 71 et 87, rangs $2$ et $4$ ♦ | `disc_rank_two`, `disc_rank_four`, `not_dvd_rank_two`, `not_dvd_rank_four` | A | Piste : C explicite en rangs 2 et 4, signe opposé réfuté. |
| 4 | remarque | —  | — | C | Redit l'énoncé précédent et annonce le suivant. |
| 5 | encadré/théorème | Grothendieck, pages 68 à 71, rang pair quelconque ♦ | `four_dvd_disc_sub_hafnian_sq`, `disc_even_rank` | A | Piste tranchée : congruence en tout rang pair, sans pfaffien. |
| 6 | remarque | —  | — | C | Décrit la démonstration et l'absence du pfaffien dans mathlib. |
| 7 | énoncé | Pages 117 à 124, la symétrie canonique ♦ | `canSym_isometry`, `canSym_canSym`, `isometry_of_idem`, `eq_of_isometry_fix`, `eq_id_or_canSym`, `canSym_center`, `canSym_char_two`, `det_polar_one` | A | Correction : π(a) = 2 ; unicité seulement sur base connexe (idempotents). |
| 8 | remarque | —  | — | A | Porte la correction π(a) = 1 → 2 et l'hypothèse de connexité ; à fondre. |
| 9 | encadré/contre-ex. | page 85, extension à travers $2$ ♦◇ | — | D-garder | Énoncé non démontré : contre-exemple Z, Δ = 3 à c) sans « étale ». |

### Cote 79 — Commutant de SL₂, homothéties et distances dans les graphes

Verdict : *tient, plus généralement* · théorème principal `commutant` · 5236 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Pages 242 à 247, (88) et (89) ♦ | `isTorus_torusOf`, `isHomothetyGroup_homothetiesOf`, `homothetiesOf_torusOf`, `torusOf_homothetiesOf`, `IsHomothetyGroup.comm` | A | Piste : équivalence dans les deux sens, commutativité sans simple transitivité. |
| 2 | remarque | —  | — | A | Commutativité de Z déduite, (77) superflue ; à fondre dans l'énoncé. |
| 3 | encadré/théorème | Grothendieck, pages 92 à 95, le commutant ♦ | `commutant`, `commutant_converse`, `sigma_ne_scal`, `scal_eq_scal_iff`, `sigma_sigma`, `sigma_scal`, `exceptional_zmod_iff`, `commutant_zmod`, `zmod4_non_neighbours` | A | Piste : commutant sur tout anneau, exception exactement n = 4. |
| 4 | remarque | —  | — | A | Hypothèses 2 ≠ 0 et bijectivité superflues ; à fondre dans l'énoncé. |
| 5 | énoncé | Pages 275 à 279, un sommet et son étoile ♦ | `same_star_iff`, `matA_mulVec`, `matA_det`, `matA_sq` | A | Piste : sommet déterminé par son étoile, au signe et à σ près. |
| 6 | remarque | —  | — | A | Hypothèse semi-locale superflue ; question ouverte de la page tranchée. |
| 7 | énoncé | Pages 19 et 20, distance au plus $3$ ♦■44734 | `exists_isUnit_mul_add`, `semilocal_dist_three`, `local_dist_three`, `zmod_dist_three` | A | PR mathlib ouverte (#44734) ; distance au plus 3 sur anneau semi-local. |
| 8 | remarque | —  | — | B | Littérature (Singerman–Strudwick, Bass) et borne atteinte ; se condense dans le verdict. |
| 9 | énoncé | Pages 96 à 101 et 136 à 140, la torsion dans le modèle ♦ | `twist_edge`, `twist_star`, `star_line`, `triangle_face`, `link_polygon`, `twist_index` | B | Calcul dans le modèle seulement ; l'énoncé abstrait de la piste reste ouvert. |
| 10 | remarque | —  | — | C | Redit le calcul et liste le non-formalisé. |
| 11 | encadré/théorème | Page 188, forme de l'édition, distance à l'image ♦ | `homothety_fixed`, `homothety_adj`, `homothety_common_nbr`, `homothety_dist_ge_three`, `commutant_dist`, `sigma_common_nbr`, `commutant_dist_three`, `zmod_scal_dist_three` | A | Piste : distance exactement 3 dans le modèle, seule exception σ. |
| 12 | remarque | —  | — | A | σ seule exception à distance 2 ; exemple Z/4 × F2 ; deux voisins requis. |
| 13 | encadré/théorème | Grothendieck, pages 187 et 188, homothéties à distance trois ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 187-188) : double cône, homothéties à distance trois. |
| 14 | encadré/théorème | Grothendieck, pages 136 à 140 et 184 à 187, polygones étoilés ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 136-140, 184-187) : polygones étoilés, injection Z → Z'_n. |
| 15 | remarque | —  | — | C | Décrit la PR mathlib ; déjà marquée sur l'énoncé des pages 19-20. |

### Cote 85 — Représentations de G₂ dans PGL₂, rotations d'ordre 5

Verdict : *en partie* · théorème principal `discr_isUnit_of_star` · 4924 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | lemme | `lem:85-traces`  | `trace_triple_sq`, `commutator_eq`, `invA_add_invA`, `isUnit_discr_iff` | C | Lemme auxiliaire d'identités de traces, sert aux énoncés suivants. |
| 2 | énoncé | Page 4, partie 1), les invariants ♦ | `discr_isUnit_of_star`, `star_of_discr_isUnit` | A | Piste : (*) en tout point équivaut à Δ inversible, sur tout anneau. |
| 3 | remarque | —  | — | A | Chaque facteur de Δ correspond à une condition ; aucune hypothèse sur 2. |
| 4 | lemme | `lem:85-commutant`  | `commutant_eq` | C | Lemme auxiliaire de commutant, sert seulement à la rigidité. |
| 5 | énoncé | Page 4, partie 2), rigidité  | `rigid` | B | Rigidité confirmée sur tout anneau. |
| 6 | énoncé | Page 4, partie 3), une forme normale  | `normalForm`, `exists_normalForm_adjoinRoot` | B | Forme normale explicite sur R[T]/(T² − α₀T + 1), calcul direct. |
| 7 | remarque | —  | — | B | Pourquoi des formes de PGL₂ : pas de A5 dans PGL₂(R) ; condensable. |
| 8 | énoncé | Page 4, partie 2), conjugaison sur un corps  | `conj_normalForm`, `conj_of_same_invariants` | B | Conjugaison sur un corps contenant ℓ, cas particulier de la page. |
| 9 | remarque | —  | — | C | Liste ce qui n'est pas formalisé (descente). |
| 10 | énoncé | Pages 6 et 7, 29 à 31, les ordres  | `pow_succ_eq`, `isScalar_pow_iff`, `powCoeff_eq_chebP`, `chebP_five`, `isScalar_pow_three_iff`, `order_four_iff`, `order_six_iff` | B | Ordres 3, 4, 6 confirmés ; ordre 6 demande 6 inversible. |
| 11 | remarque | —  | — | B | Confirme la condition c) pour ν = 4, 6 ; se condense dans le verdict. |
| 12 | énoncé | Pages 10, 30 et 40, l'invariant d'une rotation d'ordre $5$ ♦ | `invA_smul`, `sq_add_sub_of_pow_five`, `pow_five_of_sq_add_sub`, `invA_sq`, `invA_sq_of_root` | A | Piste : ordre 5 ssi A² + A − 1 = 0, en toute caractéristique. |
| 13 | lemme | `lem:85-puissance`  | `pow_five_eq`, `coeff_eq` | C | Lemme auxiliaire de calcul de g⁵. |
| 14 | énoncé | Page 40, un modèle des relations de l'icosaèdre  | `exists_model_adjoinRoot`, `sModel_sq`, `sp_cube`, `pModel_pow_five`, `invA_pModel_root` | B | Modèle explicite des relations (2,3,5) sur Z[ζ₅], calcul direct. |
| 15 | remarque | —  | — | A | Exclusion de la caractéristique 5 superflue pour le sens direct ; à fondre. |
| 16 | remarque | —  | — | C | Groupe triangulaire, critère de Beauville, passages non formalisés. |
| 17 | encadré/théorème | Grothendieck, pages 4 à 7, modules des représentations de $G_2$ ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 4-7) : modules représentables, complément de trois droites. |
| 18 | encadré/corollaire | Grothendieck, pages 10 et 40, sous-groupes icosaédraux ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 10 et 40) : sous-groupes icosaédraux, Spec Z[T]/(T² + T − 1). |

### Cote 68 — Théories de l'orientation : morphisme unique, isomorphisme, action sg∘det

Verdict : *tient tel qu'énoncé* · théorème principal `exists_unique_hom` · 1958 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | lemme | `lem:68-deux`  | `two_elem`, `eq_of_inj_of_eq`, `fix_all_or_none` | C | Lemme auxiliaire sur les ensembles à deux éléments, sert seulement aux preuves. |
| 2 | énoncé | Page 51, l'action de $\mathrm{GL}(n, \mathbf R)$ ♦ | `Theory.fixes_iff_det_pos`, `Theory.map_ne_iff_det_neg`, `Theory.fixes_iff_det_pos'` | A | Piste : action par sg∘det ; « de proche en proche » comblé par transvections. |
| 3 | encadré/théorème | Grothendieck, page 49, théorème, a) et unicité dans b) ♦ | `Hom.bijective`, `Hom.ext_app`, `Hom.isIso` | A | Théorème encadré de la page 49, piste ; n'utilise que la bijectivité de Stokes. |
| 4 | énoncé | Page 49, théorème, existence dans b) ♦ | `exists_unique_hom` | A | Piste : existence dans b), l'axiome de l'opposé ne sert qu'ici. |
| 5 | remarque | —  | — | A | Porte la trouvaille : bijectivité axiome, opposé seulement pour l'existence ; fondre au verdict. |

### Cote 70 — Icosaèdre sur Z[α] fidèle en toute caractéristique, conique mod 5

Verdict : *en partie* · théorème principal `not_collinear_any` · 2266 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Pages 74, 75, 91, 94 et 101, sur un anneau quelconque  | `q_vert`, `sigma0_vert`, `sigma1_vert`, `sigma2_vert`, `q0_edge`, `isUnit_z`, `iota_char_two` | A | Calculs directs, mais le point 5 corrige la translation lue p. 91. |
| 2 | énoncé | Pages 93 et 94, fidélité en toute caractéristique ♦ | `vert_injective_any`, `not_collinear_any`, `not_in_face_plane_any` | A | Piste : incidences sur tout anneau non nul, caractéristiques 2 et 5 comprises. |
| 3 | encadré/théorème | D'après la page 78, forme complétée par l'édition, la conique de $\mathbf P^2(\mathbf F_5… ♦ | `conic_iff`, `point_bijective`, `card_proj`, `isotropic_iff`, `isotropic_card`, `face_orth`, `edge_tangents`, `face_tangents` | A | Piste : conique de P²(F₅) confirmée, points extérieurs/intérieurs démontrés. |
| 4 | remarque | —  | — | A | Trouvailles : marge « faux en car. 2 » hors sujet, correction p. 91. |
| 5 | encadré/exemple | Grothendieck, pages 101, 102 et 106, la quadrique de l'icosaèdre ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 101–106) : quadrique invariante unique, discriminant −α−3, lisse hors 5. |
| 6 | encadré/conjecture | D'après les pages 9 à 25 et 64 à 69, forme générale de l'édition, formules universelles ♦ | — | D-garder | Énoncé non démontré : formules universelles des réalisations régulières, piste ouverte. |

### Cote 86 — Cinq trièdres de l'icosaèdre, action par Alt_T, hémi-icosaèdre

Verdict : *tient tel qu'énoncé* · théorème principal `permT_surjective` · 2454 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Pages 18 à 20 et 23, les trièdres distingués ♦ | `rho0_choice`, `rho0_swap`, `rho_cube`, `rho_sq`, `col_eq_iff`, `orthogonal_disjoint`, `face_triedres`, `face_triedre_page_reading` | A | Piste : ρ bien défini, ρ³ = id ; corrige {u, v} en {u, v₁}. |
| 2 | encadré/théorème | Grothendieck, pages 20 à 25, l'action sur les trièdres ♦ | `card_aut`, `permT_mem_alternating`, `permT_surjective`, `permT_eq_one_iff` | A | Théorème encadré, piste : image Alt_T, noyau {1, ι}. |
| 3 | remarque | —  | — | B | Autre chemin que la page ; la correction p. 23 se condense au verdict. |
| 4 | encadré/théorème | D'après les pages 21 et 26 à 32, forme complétée par l'édition, l'icosaèdre gauche par l'… ♦ | `numb_map`, `numb_even`, `numb_surjective`, `numb_eq_iff`, `numb_sigma`, `numb_sigma_page`, `page32`, `incidence_dictionary`, `vertex_pentagons`, `counts` | A | Piste : hémi-icosaèdre par numérotations paires ; corrige σ₁ et l'étiquette σ₀σ₁. |
| 5 | remarque | —  | `tau1'_eq`, `page32` | A | Porte les corrections : σ₁ conjugué par σ₂, « σ₀σ₁ » vaut σ₀σ₂. |

### Cote 136 — Lemme binomial des ombres, forme en degré i

Verdict : *tient, plus généralement* · théorème principal `binomial_shadow_existsUnique` · 1364 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | théorème | Grothendieck, page 22, théorème 1 `thm:136-1` ♦ | `binomial_constant`, `hom_family_constant` | A | Théorème 1 de la page 22, piste ; cas i = 0 du suivant. |
| 2 | théorème | D'après les pages 26 à 31, la forme en degré $i$, sous une forme plus générale `thm:136-i` ♦ | `binomial_shadow_existsUnique`, `span_choose_eq_top` | A | Piste : forme en degré i, vraie sans l'hypothèse i ≤ N. |
| 3 | lemme | `lem:136-retenue`  | `choose_pow_sub_one_zmod`, `not_dvd_choose_pow_sub_one` | C | Lemme auxiliaire (« pas de retenue », p. 31), sert seulement à la preuve. |
| 4 | lemme | `lem:136-identite`  | `choose_add_mul_choose` | C | Identité binomiale auxiliaire, sert seulement dans la preuve. |
| 5 | lemme | `lem:136-ordre`  | `eq_zero_of_forall_prime_smul` | C | Lemme auxiliaire sur l'ordre, remplace la localisation dans la preuve. |
| 6 | lemme | `lem:136-croise`  | `cross_relation` | C | Lemme auxiliaire de la preuve du théorème en degré i. |
| 7 | remarque | —  | — | A | Porte la trouvaille : i ≤ N superflu, preuve sans localisation ; fondre au verdict. |

### Cote 106 — Doute de la page 11 levé ; critère (⋆⋆) toujours vérifié

Verdict : *tient, plus généralement* · théorème principal `qFunctor_iso` · 3039 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | définition | —  | — | B | Définition des catégories à cofibrations, nécessaire au lecteur des énoncés gardés. |
| 2 | énoncé | Remplacement cofibrant et relèvement faible, page 1  | `remplacementCofibrant`, `relevementFaible`, `relevementFaible_general` | B | Page 1 confirmée ; construction directe par C3. |
| 3 | énoncé | Factorisation, page 9  | `factorisationDeBrown`, `factorisationDeBrown_general` | B | Factorisation de Brown (publiée en 1973), confirmée telle qu'énoncée. |
| 4 | énoncé | Le doute levé, page 11  | `localisation_W₀_iso_localisation_W`, `inverse_W_of_inverse_W₀` | A | Tranche le doute de la page 11 : W₀⁻¹C ≅ W⁻¹C. |
| 5 | lemme | `lem:106-cof`  | `cofibrant_of_cof` | C | Lemme auxiliaire, sert seulement dans les preuves. |
| 6 | lemme | `lem:106-somme`  | `factorisation_somme` | C | Lemme auxiliaire commun au relèvement et à la factorisation. |
| 7 | remarque | —  | — | B | Hypothèse α_x ∈ W superflue ; se condense dans le verdict du relèvement. |
| 8 | remarque | —  | — | B | f ∈ W superflue sauf pour i ; résultat connu de Brown, verdict. |
| 9 | remarque | —  | — | B | Clauses inutilisées de C1–C2 ; se condense dans une ligne de verdict. |
| 10 | remarque | —  | — | B | Redit que le doute est levé ; se condense dans le verdict de 4. |
| 11 | définition | —  | — | B | Définition de Ch'₀, C̃' et (⋆⋆), nécessaire au théorème gardé. |
| 12 | encadré/théorème | D'après les pages 11 à 15, le critère $(\star\star)$, forme complétée par l'édition ♦ | `qFunctor_iso`, `fidele`, `plein`, `critere_of_fidele`, `fidele_iff_critere`, `critere` | A | Piste : q' isomorphisme sans hypothèse, (⋆⋆) toujours vérifiée. |
| 13 | lemme | `lem:106-cat`  | `Span.frac_eq_of_arrow`, `Span.arrow_comp_left`, `Span.arrow_comp_right`, `Span.arrow_assoc`, `Span.arrow_id_comp`, `Span.arrow_comp_id` | C | Lemme auxiliaire : C̃' est une catégorie, q' un foncteur. |
| 14 | lemme | `lem:106-composante`  | `arrow_brown`, `mk_eq_brown` | C | Lemme auxiliaire de la preuve du critère. |
| 15 | lemme | `lem:106-phi`  | `phi_inverts`, `phi_map_cof`, `back_comp_phi` | C | Lemme auxiliaire de la preuve du critère. |
| 16 | remarque | —  | — | A | Porte la trouvaille : les deux membres vrais, isomorphisme de l'édition ; fondre. |
| 17 | remarque | —  | — | B | Usage des axiomes C1–C2 dans la composition ; se condense en verdict. |

### Cote 114 — Proposition 4 : asphéricité totale indépendante du localisateur

Verdict : *la lecture omettait une hypothèse* · théorème principal `proposition4_ii_iii` · 1735 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | définition | —  | — | B | Définitions des localisateurs fondamentaux, nécessaires au lecteur de la proposition |
| 2 | énoncé | Proposition 4, page 3  | `proposition4_i_ii`, `proposition4_ii_iii`, `contreExemple_proposition4` | A | La lecture omettait « satisfying Loc 4) » ; (ii)⇒(iii) faux sans elle |
| 3 | lemme | `lem:114-W0`  | `W₀_localisateurFondamental` | B | W₀ est un localisateur fondamental : vérification directe des axiomes |
| 4 | lemme | `lem:114-asph`  | `aspherique_W₀_iff`, `totalementAspherique_W₀_iff` | B | Asphéricité totale pour W₀ équivaut à (iii) : calcul direct |
| 5 | lemme | `lem:114-min`  | `Wmin_localisateurFondamental`, `Wmin_inclus` | B | Existence du localisateur minimal W∞, routine |
| 6 | remarque | —  | `Wmoins1_not_inclus_W₀`, `Wtrivial_not_inclus_W₀`, `contreExemple_proposition4` | A | Contre-exemples sans Loc 4) : W ⊆ W₀ et (ii)⇒(iii) tombent |
| 7 | remarque | —  | — | C | Redit le lemme sur W₀ et renvoie à Maltsiniotis |
| 8 | remarque | —  | — | B | (iii)⇒(i) réfuté dans la littérature ; se condense dans le verdict |

### Cote 158 — Monoïde fini pseudo-cofiltrant à groupe enveloppant trivial : zéro à droite

Verdict : *tient ; la glose était fausse* · théorème principal `proposition1` · 1303 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | définition | —  | — | B | Définitions de pseudo-cofiltrant et groupe enveloppant trivial, utiles au lecteur |
| 2 | encadré/théorème | Grothendieck, Proposition 1, pages 44 à 46 ♦■44702 | `proposition1` | A | Piste et PR mathlib #44702 ; tient tel qu'énoncé |
| 3 | lemme | `lem:158-etape1`  | `etape1` | C | Lemme auxiliaire de la preuve de la proposition 1 |
| 4 | remarque | —  | — | B | La finitude sert là où la page le dit ; ligne de verdict |
| 5 | remarque | —  | — | B | Hypothèses nécessaires ; aucun théorème Lean ne porte ce contre-exemple |
| 6 | remarque | —  | `contre_noyau_non_ponctuel`, `contre_pseudoCofiltrant`, `contre_groupeEnveloppantTrivial` | A | p non unique, noyau non ponctuel : corrige la glose de la lecture |
| 7 | remarque | —  | `contre_noyau_non_ponctuel` | A | p zéro à droite ; glose fausse et unicité barrée réfutées |
| 8 | remarque | —  | — | C | Décrit la PR mathlib, déjà dans le titre de l'énoncé |
| 9 | encadré/theoreme* | Grothendieck, pages 21 à 41, monoïdes à élément minimal ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 21–41) ; piste, démonstration esquissée incomplète |
| 10 | encadré/theoreme* | Grothendieck, pages 50 à 53, catégories finies cofiltrantes ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 50–53) ; piste, question centrale de la cote |

### Cote 104 — Catégories de modèles : sous-objets, exemples, structure de Reedy directe

Verdict : *en partie démontré* · théorème principal `reedyDirecte` · 2656 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | définition | —  | — | B | Définition des catégories de modèles et sous-objets, utile au lecteur |
| 2 | énoncé | Pages 6 et 7  | `etoile_injective`, `isIso_of_aller_retour`, `sousObjet_eq_of_meme_type` | B | Pages 6–7 confirmées telles qu'énoncées |
| 3 | énoncé | Page 10, la réciproque : un pas  | `id_of_idempotent_bijective` | B | Bijection idempotente égale l'identité : calcul direct |
| 4 | énoncé | Page 10, les trois exemples ■44732 | `card_I_simplexe`, `card_I_cube`, `somme_faces_cube`, `card_I_hemi`, `card_type_hemi`, `chaotique_non_antisymetrique` | A | Marque PR mathlib #44732 ; exemple 3 corrigé par la lecture |
| 5 | énoncé | Page 4, le complexe globulaire  | `globulaire_complexe` | B | Complexe globulaire : calcul direct |
| 6 | remarque | —  | `chaotique_non_antisymetrique` | A | Exemple 3 faux tel que sur la page (2n+3, préordre non antisymétrique) |
| 7 | remarque | —  | — | B | Hypothèse (i) inutile, (ii) suffit ; se condense dans le verdict |
| 8 | remarque | —  | — | C | Décrit ce qui est démontré ou non pour les exemples |
| 9 | énoncé | Page 6, note de la lecture : la bonne fondation ■44731 | `strict_of_not_isIso`, `strict_of_not_identities`, `reedyDirecte`, `wf_of_degre`, `entiers_relatifs_non_directe` | A | PR mathlib #44731 : catégories directes caractérisées par bonne fondation |
| 10 | remarque | —  | `entiers_relatifs_non_directe` | A | ℤ : la bonne fondation est une hypothèse supplémentaire, non conséquence |
| 11 | énoncé | Page 10, exemple 1 : les identités simpliciales  | `DeltaInj.δ_comp_δ`, `DeltaInj.factorise_face`, `deltaInj_skeletal`, `deltaInj_lt`, `deltaInjReedy` | A | Énoncé de la PR mathlib #44732 (Reedy directe semi-simpliciale) |
| 12 | remarque | —  | — | C | Décrit ce qui est formalisé et l'identification semi-simpliciale |
| 13 | remarque | —  | — | C | Décrit les PR mathlib |
| 14 | encadré/theoreme* | Grothendieck, pages 12 à 16, ensembles ordonnés épinglés ♦◇ | — | D-garder | Conjecture (Grothendieck, p. 12–16) ; piste, équivalence avec ensembles ordonnés épinglés |

### Cote 120 — Écrasement d'une partie modérée : séparation des points hors de Y

Verdict : *tient, plus généralement* · théorème principal `collapse_separation` · 1421 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | lemme | pages 5 et 20 `lem:120-anneau`  | `graphOn_pair_mem`, `image_mem`, `isTameFun_comp`, `isTameFun_mul`, `isTameFun_sub`, `isTameFun_const`, `isTameFun_coord` | B | Fonctions modérées forment un anneau ; seuls (M′1), (M′2), (M′4), (M11) b) |
| 2 | lemme | pages 22 et 23, l'argument `lem:120-separation`  | `separates_off_zeroSet`, `collapseFamily_eq_zero_iff` | C | Lemme auxiliaire de séparation, sert seulement au théorème |
| 3 | théorème | Pages 22 et 23, écrasement sur un corps, forme corrigée par l'édition `thm:120-ecrasement` ♦ | `collapse_separation`, `exists_separating_family`, `exists_separating_family_of_field` | A | Piste ; tient plus généralement, forme corrigée par l'édition |
| 4 | remarque | —  | `not_separates_zmod4`, `not_separates_on_zeroSet` | A | Hypothèses superflues, intégrité nécessaire (ℤ/4), deux corrections nécessaires |

### Cote 156-1 — Le modèle-segment est un biordre, et réciproquement

Verdict : *tient, plus généralement* · théorème principal `biorder` · 2328 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | encadré/théorème | Grothendieck, pages 10 à 13, \emph{le modèle-segment est un biordre} ♦ | `biorder`, `le_swap`, `intervals_axioms`, `intervals_segModel`, `intervals_le_iff` | A | Piste ; tient dans les deux sens, sous moins d'axiomes |
| 2 | remarque | —  | `biorder`, `intervals_axioms` | A | F3, F5 inutiles ; F4 sans régularité dans la réciproque |
| 3 | remarque | —  | `not_total`, `example_segModel` | B | Exemple non total dans ℚ², confirme la lecture |

### Cote 156-3 — Bijection respectant les découpages : isomorphisme ou anti-isomorphisme

Verdict : *tient, plus généralement* · théorème principal `order_of_cuts` · 1609 mots actuels

| n° | env. | titre / label | Lean | classe | raison |
|---|---|---|---|---|---|
| 1 | énoncé | Page 15  | `piece_above`, `piece_below`, `piece_between`, `middle_iff` | B | Page 15 confirmée : calcul direct des morceaux |
| 2 | énoncé | Pages 11 à 13  | `btwLe_iff`, `le_iff_readLe`, `iso_of_lt`, `order_eq_or_dual` | B | Reconstruction de l'ordre par l'intermédiarité, résultat connu (Courcelle) |
| 3 | encadré/théorème | D'après les pages 11 à 15, \emph{l'ordre se lit sur les découpages}, forme complétée par … ♦ | `order_of_cuts`, `cmp_alone_insufficient` | A | Piste ; forme complétée par l'édition, comparabilité seule insuffisante |
| 4 | remarque | —  | `order_of_cuts` | A | Seules densité et filtration servent : vaut plus généralement |
| 5 | remarque | —  | `btwLe_reading_fails` | A | Note de la lecture p. 11 fausse pour extrémités incomparables |
| 6 | remarque | —  | — | B | Renvoi à Courcelle et Lihová ; se condense dans le verdict |

## 6 bis. Parties vides et blocs « autres pistes » (classe D)

### autres/cycles-algebriques-et-conjectures-standa

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `11-simplicial-bivariant-poincare-equivalence` | D-retirer | Conjecture (Grothendieck, pp. 37 et 41) | Mal posé : axiomes laissés à énoncer ; reformulation probable de Frobenius |
| 2 | `36-griffiths-conditional-l-adic` | D-garder | Énoncé non démontré (d'après pp. 9 à 16) | Groupe de Griffiths en toute caractéristique, énoncé fort même conditionnel |
| 3 | `36-h1-invariant-cycle-defect` | D-retirer | Conjecture (Grothendieck, pp. 60 à 70) | Probablement chez Raynaud 1970 et SGA 7 IX |
| 4 | `36-orthogonality-regular-adic-base` | D-garder | Conjecture (Grothendieck, pp. 73 à 76) | Orthogonalité SGA 7 étendue à une base adique régulière |

### vide/motifs

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `12-immersion-level-bound` | D-garder | Conjecture (Grothendieck, pp. 115 à 119) | Borne nette poids/niveau, meilleure d'un cran que l'attendu |

### vide/theorie-de-hodge

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `13-double-lattice-invariants` | D-garder | Conjecture (Grothendieck, pp. 33 et 34) | Piste candidate ; forme k-rationnelle absente des sources consultées |

### vide/cohomologie-etale-et-l-adique

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `60-inertia-average-duality` | D-retirer | Conjecture (Grothendieck, pp. 38 à 58) | Construction et calcul local, question finale seulement esquissée |
| 2 | `31-phi-specialisation-criterion` | D-retirer | Conjecture (Grothendieck, pp. 64 à 70) | Déjà dans SGA 4 X 4.1 (matched) |
| 3 | `31-imperfection-bound-conjectures` | D-garder | Conjecture (Grothendieck, p. 84) | Conjecture de la page, candidate, partiellement confirmée par Gabber–Orgogozo |
| 4 | `31-local-ring-cd-lower-bound` | D-garder | Conjecture (Grothendieck, p. 22) | Candidate : exceptions exactes plus fines que SGA 4 X 2.4 |

### vide/groupes-p-divisibles-et-groupes-formels

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `129-ext2-vanishing-p-odd` | D-garder | Conjecture (Grothendieck, p. 95) | Annulation nette et forte, utile aux déformations de groupes BT |

### autres/theorie-de-la-dualite

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `101-sheaf-duality-dim-one` | D-garder | Conjecture (Grothendieck, pp. 10 et 11) | Dualité locale pour tous les modules, énoncé net |
| 2 | `101-sheaf-duality-dim-two-fails` | D-garder | Énoncé non démontré (pp. 10, 14 et 15) | Contre-exemple à la dualité en dimension deux |
| 3 | `32-pullback-kernel-index` | D-garder | Conjecture (Grothendieck, pp. 10 et 11) | Noyau de f* tué par l'indice, sans hypothèse de dimension |
| 4 | `43-ext-ga-zp-perfection` | D-retirer | Conjecture (Grothendieck, pp. 165 à 169) | Calcul d'Ext probablement classique (Breen, Demazure–Gabriel) |
| 5 | `43-local-cohomology-concentration` | D-retirer | Énoncé non démontré (d'après pp. 70 à 74) | Forme corrigée par l'édition, étape technique vers la jacobienne locale |
| 6 | `58-lef-permanence-projective-flat` | D-garder | Conjecture (Grothendieck, pp. 40 à 43) | Candidate : permanence de Lef sans hypothèse sur les fibres |
| 7 | `58-local-hom-comparison-depth-off-y` | D-retirer | Conjecture (Grothendieck, pp. 45 à 51) | Variante d'hypothèse de SGA 2 X, étape laissée à « ? » |

### vide/descente

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `126-radicial-etale-factorisation` | D-retirer | Conjecture (Grothendieck, pp. 17 à 23) | Repose sur une lecture incertaine « univ. ouvert » |
| 2 | `126-nilpotent-deformation-quotient` | D-retirer | Énoncé non démontré (d'après pp. 4 à 7) | Hypothèses largement reconstituées par l'édition |
| 3 | `126-generic-descent` | D-garder | Conjecture (Grothendieck, pp. 26 à 29) | Descente générique d'une donnée rationnelle, énoncé général et net |
| 4 | `128-nilpotent-conductor-flat-descent` | D-retirer | Conjecture (Grothendieck, pp. 4 à 9) | Suit sans doute formellement de Ferrand 2003 |
| 5 | `128-colength-one-equivalence-criterion` | D-retirer | Conjecture (Grothendieck, pp. 12 à 18) | Lemme technique sur les extensions minimales |
| 6 | `128-infinitesimal-descent-theorem` | D-garder | Conjecture (Grothendieck, pp. 19 à 29) | Théorème central du dossier, énoncé non établi par la page |

### autres/topos-et-sites

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `161-3-locale-spatiality-suprema-proof` | D-retirer | Conjecture (Grothendieck, pp. 9 à 14) | Méthode de preuve, sans énoncé nouveau |
| 2 | `90-equivariant-resolution-general-base` | D-retirer | Conjecture (Grothendieck, pp. 13 à 23) | Probablement couvert par Thomason 1987 |
| 3 | `23-finite-normalisation-quotient-of-regular` | D-garder | Conjecture (Grothendieck, pp. 86 à 88) | Critère net de finitude de la normalisation |
| 4 | `161-3-product-converse` | D-garder | Conjecture (Grothendieck, pp. 10 et 11) | Hypothèse plus faible que la compacité locale, énoncé net |
| 5 | `161-3-infinite-product-criterion` | D-retirer | Conjecture (Grothendieck, pp. 11 et 12) | Variante du critère pour un produit fini |
| 6 | `161-3-two-product-by-intersection` | D-retirer | Conjecture (Grothendieck, pp. 3 à 8) | Théorème connu (SGA 4) ; seule la voie diffère |
| 7 | `37-ind-topos-exercise` | D-garder | Conjecture (Grothendieck, p. 22) | Caractérisation nette des Ind(C) qui sont des topos |
| 8 | `112-linearization-beyond-the-simplex` | D-retirer | Conjecture (Grothendieck, pp. 1 à 4) | Question imprécise, dossier mal lu |
| 9 | `116-presheaf-gluing-continuous-gluing-functor` | D-retirer | Conjecture (Grothendieck, pp. 6 et 7) | Probablement folklore : recollements comme collages de profoncteurs |

### autres/varietes-abeliennes-et-schemas-de-picard

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `14-nakai-euler-characteristic-criterion` | D-garder | Conjecture (Grothendieck, pp. 93 et 94) | Critère d'amplitude par croissance de χ, plus fort que Nakai |
| 2 | `59-determinant-canonical-section` | D-garder | Énoncé non démontré (d'après pp. 1 à 22) | Trivialisation canonique, résultat structurant du dossier 59 |
| 3 | `100-full-faithfulness-connected-components` | D-garder | Conjecture (Grothendieck, pp. 2, 3 et 20) | Pleine fidélité sans normalité ni densité, énoncé fort |
| 4 | `100-proper-epimorphism-hom-descent` | D-retirer | Conjecture (Grothendieck, pp. 22 à 24) | Lemme de descente intermédiaire vers la pleine fidélité |
| 5 | `100-formal-abelian-curve-criterion` | D-garder | Conjecture (Grothendieck, pp. 30 à 38) | Critère d'algébrisation par les courbes, énoncé fort |
| 6 | `130-quasi-function-sheaf` | D-retirer | Conjecture (Grothendieck, pp. 39 à 48) | Organisation des fonctions de Weil, plutôt construction qu'énoncé |
| 7 | `9-det-etale-tate-iso` | D-retirer | Conjecture (Grothendieck, pp. 22 à 28) | Énoncé technique sur le lieu ordinaire, portée limitée |
| 8 | `9-symmetric-positive-det-sqrt-degree` | D-retirer | Conjecture (Grothendieck, pp. 24 et 26) | Cas particulier du précédent |
| 9 | `14-albanese-equivalence-ring` | D-retirer | Conjecture (Grothendieck, pp. 23 à 29 et 33) | Définition et propriétés attendues d'une équivalence adéquate |
| 10 | `47-chow-fourier-todd-over-base` | D-retirer | Conjecture (Grothendieck, pp. 9 et 10) | Calcul Riemann–Roch, sans doute chez Deninger–Murre |
| 11 | `51-albanese-good-reduction-codim-two` | D-garder | Conjecture (Grothendieck, pp. 16, 17 et 20) | Bonne réduction malgré des singularités en codimension deux |
| 12 | `57-generic-hyperplane-h1-injective` | D-garder | Conjecture (Grothendieck, pp. 98 et 99) | Injectivité forte en caractéristique p, à confronter à Raynaud |
| 13 | `57-analytic-pic-completion-criterion` | D-garder | Conjecture (Grothendieck, pp. 226 à 228 et 247 à 271) | Critère « si et seulement si » net, avec corollaire de projectivité |
| 14 | `59-surface-even-chi-torsor` | D-garder | Conjecture (Grothendieck, pp. 11 à 13) | Candidate : nullité de la classe de Poonen–Stoll |
| 15 | `100-baire-dimension-one-points` | D-retirer | Énoncé non démontré (pp. 36 à 38) | Forme corrigée, sans doute Sharp–Vámos |
| 16 | `100-neron-extension-p-divisible` | D-retirer | Conjecture (Grothendieck, pp. 47 à 52) | Conséquence probable de Tate et SGA 7 IX |
| 17 | `47-dual-polarisation-divisibility` | D-garder | Conjecture (Grothendieck, pp. 7 et 8) | Conjecture d'intégralité posée par la page |
| 18 | `49-flatness-lemma-pushforward` | D-retirer | Énoncé non démontré (d'après p. 3) | Forme reconstituée, variante du critère local de platitude |
| 19 | `50-axiomatic-trace-formula` | D-retirer | Conjecture (Grothendieck, pp. 6 à 10) | Cadre axiomatique ; la formule elle-même est connue |
| 20 | `57-rigid-subgroups-one-fibre` | D-garder | Conjecture (Grothendieck, pp. 42 à 49) | Rigidité générale englobant tores et schémas abéliens |
| 21 | `130-neron-symbol-component-correction` | D-garder | Conjecture (Grothendieck, pp. 3 à 5) | Décomposition du symbole de Néron, accouplement sur les composantes |

### vide/categories-tensorielles-et-dualite-tanna

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `155-takeuchi-idealiser` | D-retirer | Conjecture (Grothendieck, p. 1) | Définition, présentation du produit de Takeuchi sans théorème |

### autres/categories-et-foncteurs

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `162-5-bordism-correspondences-universal` | D-garder | Énoncé non démontré (Quillen, d'après pp. 43 à 45) | Propriété universelle nette des correspondances de bordisme |
| 2 | `162-5-de-rham-hochschild-flat-formal-category` | D-retirer | Conjecture (Grothendieck, pp. 27 à 30) | Corollaire de l'équivalence de Quillen qui suit |
| 3 | `162-5-formal-categories-flat-conormal-de-rham` | D-garder | Énoncé non démontré (Quillen, d'après pp. 21 à 26) | Équivalence sans finitude ni lissité, énoncé structurant |

### autres/geometrie-formelle-modules-et-representa

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `102-open-immersion-criterion` | D-retirer | Conjecture (Grothendieck, p. 12) | Critère de type Artin, sans doute dans la littérature |
| 2 | `127-closure-flatness-artinian-or-trait` | D-garder | Conjecture (Grothendieck, pp. 2 à 4, 15 et 19) | Critère valuatif de platitude d'une adhérence schématique |
| 3 | `127-hironaka-reduced-base-openness` | D-retirer | Conjecture (Grothendieck, pp. 7, 9, 10 et 12) | Variante d'un énoncé attribué à Hironaka (Kollár 2011) |
| 4 | `127-non-flat-descent-artinian-epimorphism` | D-retirer | Conjecture (Grothendieck, pp. 2 et 3) | Vérité de l'énoncé non décidée, aucune preuve |
| 5 | `131-locally-quasi-finite-representability` | D-garder | Conjecture (Grothendieck, pp. 1 à 5, 13 et 15) | Candidate : critère de représentabilité explicite |
| 6 | `94-generic-tor-regular-sequences` | D-garder | Conjecture (Grothendieck, pp. 8, 9 et 19) | Substitut de la platitude générique sur base non réduite |
| 7 | `94-representability-criterion` | D-garder | Conjecture (Grothendieck, pp. 15 et 16) | Candidate : représentabilité sur Mod(A) sans condition de produits |

### vide/cohomologie-cristalline-et-de-de-rham

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `4-vanishing-unit-root-bound` | D-retirer | Conjecture (Grothendieck, pp. 1 et 4 à 7) | Conditionnel au Lefschetz faible cristallin avec torsion |
| 2 | `5-universal-artinian-pd-normal-form` | D-retirer | Conjecture (Grothendieck, pp. 4 à 8) | Calcul explicite, nécessité non démontrée |
| 3 | `6-ordinary-moduli-complete-intersection` | D-garder | Conjecture (Grothendieck, pp. 52 à 56) | Cas p divisant le degré ouvert, énoncé net |
| 4 | `6-formal-group-not-in-abelian-variety` | D-garder | Conjecture (Grothendieck, pp. 49 et 50) | Groupe formel hors des variétés abéliennes, énoncé frappant |
| 5 | `6-same-formal-group-not-isogenous` | D-retirer | Conjecture (Grothendieck, pp. 47 et 48) | Probablement connu : argument de dénombrabilité des classes d'isogénie |
| 6 | `137-perfect-complexes-universal-sigma-exact` | D-garder | Conjecture (Grothendieck, pp. 39 à 44 et 48 à 56) | Propriété universelle nette des complexes de modules libres |
| 7 | `5-deligne-letter-ringed-duality` | D-retirer | Conjecture (Grothendieck, pp. 49 et 50) | Variante de la dualité de SGA 4 XVIII |
| 8 | `7-noninfinitesimal-site` | D-garder | Conjecture (Grothendieck, pp. 16 à 18) | Conjecture candidate : site p-adique sans puissances divisées |
| 9 | `137-polynomial-categories-pd-tensor-categories` | D-retirer | Conjecture (Grothendieck, pp. 74 à 83) | Axiomatique lourde, équivalence affirmée sans contrôle |

### autres/schemas-en-groupes-et-groupes-algebrique

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `10-hodgian-polarisations-torsor` | D-retirer | Conjecture (Grothendieck, pp. 11 à 16) | Énoncé de torseur secondaire, lien polarisation-Cartan connu |
| 2 | `10-numerical-character-rank-one-torus` | D-retirer | Conjecture (Grothendieck, pp. 62 à 65) | Conséquence de Hilbert 90 et de Giraud |
| 3 | `123-grothendieck-springer-pic-twisted-torus` | D-garder | Conjecture (Grothendieck, pp. 10 à 12) | Picard de l'espace de Grothendieck–Springer, tore non déployé |
| 4 | `123-kostant-rigidifications-count` | D-retirer | Conjecture (Grothendieck, pp. 21, 28, 30 et 34) | Comptage non vérifié, à prouver ou réfuter |
| 5 | `123-steinberg-no-resolution-picard` | D-retirer | Conjecture (Grothendieck, pp. 10 à 13) | Énoncé classique (Brieskorn, Slodowy) ; seule la voie diffère |
| 6 | `15-brandt-picard-category` | D-retirer | Conjecture (Grothendieck, pp. 71 à 77) | Structure technique sur un 2-groupe |
| 7 | `15-real-fibre-functor-criterion` | D-garder | Conjecture (Grothendieck, pp. 116 à 118) | Critère net d'existence d'un foncteur fibre réel |
| 8 | `27-semicontinuity-proof` | D-garder | Conjecture (Grothendieck, pp. 27 à 36) | Candidate : preuve de SGA 3 X 8.7 |
| 9 | `45-bands-tsen-field` | D-garder | Conjecture (Grothendieck, pp. 10 à 14) | Tout lien sur un corps C1 est réalisé, énoncé fort |
| 10 | `45-h1-surjectivity-dim-one` | D-garder | Énoncé non démontré (d'après pp. 3 à 10) | Surjectivité en H1 sans lissité, énoncé fort |
| 11 | `46-semilocal-hilbert90-inertia` | D-garder | Conjecture (Grothendieck, pp. 84 à 89) | Candidate : injectivité, non seulement noyau trivial |
| 12 | `46-sylow-reduction-criterion` | D-retirer | Conjecture (Grothendieck, pp. 90 à 92) | Argument de restriction à un Sylow, standard |
| 13 | `53-geometric-irreducibility-criterion` | D-retirer | Énoncé non démontré (p. 9) | Forme corrigée, analogue d'EGA IV 4.5.13 |
| 14 | `55-lemma-b-identity-principle` | D-retirer | Conjecture (Grothendieck, p. 13) | Vérité non décidée pour un espace annelé abstrait |
| 15 | `64-legendre-pinning-moduli` | D-garder | Conjecture (Grothendieck, pp. 74 à 79 et 84 à 91) | Candidate : rigidification de Legendre représentée par U_{0,3} |
| 16 | `64-octahedral-configurations-relative` | D-garder | Conjecture (Grothendieck, pp. 44 à 52) | Candidate : bijections relatives et revêtements quartiques |
| 17 | `80-bigon-free-five-line-dichotomy` | D-retirer | Conjecture (Grothendieck, pp. 20, 24 et 28) | Étape combinatoire vers le théorème du squelette |
| 18 | `80-lattice-criterion` | D-retirer | Conjecture (Grothendieck, pp. 24 et 26) | Critère auxiliaire, suffisance non contrôlée |
| 19 | `80-skeleton-full-faithfulness` | D-garder | Conjecture (Grothendieck, pp. 39 à 54) | Candidate : arrangement déterminé par son 1-squelette |
| 20 | `82-char2-conic-frobenius` | D-retirer | Conjecture (Grothendieck, pp. 77 et 78) | Calcul local en caractéristique deux |

### autres/surfaces-de-riemann-uniformisation-et-mo

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `148-m05-special-structures-chart` | D-retirer | Conjecture (Grothendieck, pp. 30 à 32 et 35) | Exemple, décompte de flèches à revoir |
| 2 | `148-multimarked-teichmuller-groupoid` | D-retirer | Conjecture (Grothendieck, pp. 40 et 49 à 60) | Définition sans énoncé |

### vide/champs-gerbes-et-categories-fibrees

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `103-gr-stacks-relative-cohomology-BG` | D-garder | Conjecture (Grothendieck, pp. 14 et 15) | Classification des Gr-champs épinglés, cas non commutatif |
| 2 | `134-1-picard-sign-sequence` | D-garder | Conjecture (Grothendieck, pp. 3 à 5) | Suite exacte nette des champs de Picard épinglés |
| 3 | `134-1-sign-realisation-universal-argument` | D-retirer | Conjecture (Grothendieck, p. 5) | Complément « sauf erreur » de la suite exacte précédente |

### autres/topologie-combinatoire-surfaces-et-carte

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `132-fibre-product-pi2-defect` | D-retirer | Conjecture (Grothendieck, pp. 1 à 3) | Bas degrés de Mayer–Vietoris, presque sûrement connu |
| 2 | `132-nonconnected-extension-classification` | D-garder | Conjecture (Grothendieck, pp. 16 à 20) | Candidate : classification des extensions d'un groupe non connexe |
| 3 | `132-peripheral-gr-category` | D-retirer | Énoncé non démontré (d'après pp. 5 à 8) | Exemple complété par l'édition |
| 4 | `147-deleted-neighbourhood-codim-two` | D-retirer | Conjecture (Grothendieck, pp. 148 à 151) | Sans doute connu (espace de Kato–Nakayama) |
| 5 | `147-m11-stratified-class-over-z` | D-retirer | Énoncé non démontré (d'après pp. 62 à 64) | Exemple de calcul, invariant complété par l'édition |
| 6 | `154-cyclic-order-determines-position` | D-retirer | Conjecture (Grothendieck, p. 18) | Suit sans doute de la théorie des matroïdes orientés |
| 7 | `154-dihedral-monodromy-half-turn` | D-garder | Conjecture (Grothendieck, pp. 55 à 63, 85 et 86) | Monodromie diédrale surjective, énoncé net |
| 8 | `154-generisation-cube` | D-retirer | Conjecture (Grothendieck, p. 153) | Énoncé combinatoire local, cas particulier |
| 9 | `77-arf-cover-stein-factorisation` | D-garder | Conjecture (Grothendieck, pp. 132 à 143 et 155 à 157) | Candidate : revêtement d'Arf sans algèbres de Clifford |

### vide/groupes-fondamentaux-et-theorie-de-galoi

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `142-teichmuller-galois-category-etale` | D-retirer | Conjecture (Grothendieck, pp. 2 à 16) | Définition d'une catégorie, sans énoncé |
| 2 | `34-multiparameter-tame-monodromy` | D-garder | Conjecture (Grothendieck, pp. 167 et 175 à 180) | Monodromie modérée abélienne sur base de dimension quelconque |
| 3 | `149-dominant-faithfulness-curves` | D-garder | Énoncé non démontré (pp. 36 à 39) | Contre-exemple au lemme de la page 36 |
| 4 | `29-ramification-domain-axioms` | D-retirer | Conjecture (Grothendieck, pp. 190 à 193) | Axiome R4 illisible, page barrée |
| 5 | `29-domram-morphisms-fully-faithful` | D-retirer | Conjecture (Grothendieck, p. 197) | Énoncé de rigidité dans un cadre mal fixé |
| 6 | `29-degree-n-as-primitive` | D-retirer | Conjecture (Grothendieck, pp. 212 et 214) | Conditions en partie illisibles |
| 7 | `29-formal-tame-pi1-self-intersection` | D-garder | Conjecture (Grothendieck, pp. 87 à 97) | Candidate : classe d'extension égale à l'auto-intersection |
| 8 | `34-lci-local-1-asphericity` | D-garder | Conjecture (Grothendieck, pp. 153 à 155, 1) | Candidate : 1-asphéricité locale pour fibre d'intersection complète |
| 9 | `29-h1-five-classes-infinite-group` | D-retirer | Conjecture (Grothendieck, pp. 170 et 171) | Comparaisons techniques entre classes de recouvrements |
| 10 | `29-inertia-matrix-determinant` | D-retirer | Conjecture (Grothendieck, p. 120) | Candidate mais folklore probable, à un pas de SGA 1 |
| 11 | `142-galois-image-conditions-single-curve` | D-garder | Énoncé non démontré (d'après pp. 94, 95 et 98 à 101) | Candidate : image de Galois sur une seule courbe |
| 12 | `145-unit-exponent-exercise` | D-retirer | Conjecture (Grothendieck, pp. 34 et 35) | Fait connu sur GT chapeau (Drinfeld, Ihara) |
| 13 | `149-cusp-specialisation-index` | D-garder | Conjecture (Grothendieck, pp. 72 à 77 et 84 à 93) | Spécialisation des sections vers une pointe, indice n |

### autres/theorie-de-l-homotopie-et-categories-tes

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `105-derivator-crible-excision` | D-retirer | Conjecture (Grothendieck, pp. 42 à 45) | Mise en place illisible ; moitié d'un axiome seulement |
| 2 | `107-relative-square-rectification` | D-retirer | Conjecture (Grothendieck, pp. 20 et 22) | Probablement chez Quillen, Homotopical Algebra II §2 |
| 3 | `108-delta-op-not-test` | D-retirer | Conjecture (Grothendieck, p. 2) | Simple « non » sans argument ni définition sur la page |
| 4 | `118-pushout-along-cofibrations-in-cat` | D-garder | Énoncé non démontré (d'après pp. 18 à 20) | Candidate : critère de sommes amalgamées homotopiques dans Cat |
| 5 | `136-automorphism-group-scheme` | D-retirer | Conjecture (Grothendieck, pp. 161 à 179 et 189 à 199) | Classification technique des automorphismes |
| 6 | `136-pd-de-rham-shadows` | D-garder | Conjecture (Grothendieck, pp. 5 à 10 et 226 à 232) | Candidate : cohomologie entière vue par ses ombres |
| 7 | `150-flag-fibration-smoothness` | D-retirer | Conjecture (Grothendieck, pp. 1 et 45 à 47) | Combinatoire de bord, étape vers le déploiement |
| 8 | `150-unfolding-as-ordered-space` | D-garder | Conjecture (Grothendieck, pp. 47 à 66 et 70) | Déploiement comme espace ordonné, énoncé structurant |
| 9 | `151-hypercovering-any-index-category` | D-garder | Conjecture (Grothendieck, pp. 10 à 14 et 17) | Hyperrecouvrements indexés par une catégorie quelconque, un axiome |
| 10 | `151-mixed-tubes` | D-retirer | Énoncé non démontré (pp. 59, 60 et 74) | Définition sans énoncé |
| 11 | `151-pi1-too-coarse-for-the-sphere` | D-retirer | Conjecture (Grothendieck, pp. 61 à 63) | Exemple motivant, sans énoncé général |
| 12 | `151-tube-gluing-covering-pairs` | D-retirer | Conjecture (Grothendieck, pp. 62 à 68) | Variante de reconstruction, sans doute standard |

### autres/topologie-moderee-et-espaces-stratifies

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `121-coarsest-cell-decomposition` | D-garder | Conjecture (Grothendieck, pp. 3 à 16) | Existence d'une partition la plus grossière, énoncé net |
| 2 | `119-foliation-quotient-topos-equivalence` | D-retirer | Conjecture (Grothendieck, pp. 144 et 145) | Équivalence affirmée sans preuve, proche de Kock–Moerdijk |

### vide/geometrie-anabelienne-et-dessins

| n° | piste | classe | étiquette | raison |
|---|---|---|---|---|
| 1 | `140-1-equivariant-pic-u03` | D-garder | Conjecture (Grothendieck, pp. 22, 24 et 29) | Calcul net : Z/6, ou Z/3 en caractéristique 2 |
| 2 | `138-operations-belyi-extending` | D-garder | Conjecture (Grothendieck, pp. 122 à 124 et 127) | Candidate : réciproque de la construction des opérations |
| 3 | `146-equivariant-trivialising-exponents` | D-retirer | Conjecture (Grothendieck, pp. 70, 72 et 73) | Valeurs seulement interrogées au-delà de n = 4 |

## 7. Cas douteux à trancher

**Les A qu'on pourrait descendre en B**, premier levier pour gagner des pages :
- 16 n° 6, 18 (corrections mineures, en B ; A défendable). 19 n° 8, 10, 11, 13, 15 (piste et remarques ; plusieurs se condensent). 136 n° 1 (cas i = 0 du n° 2, à fondre dedans). 153 n° 17, 18, 21, 22 (gains mineurs). 70 n° 1 (A seulement par la correction de la p. 91). 42 n° 2, 10 (la généralisation est déjà dans mathlib). 44 n° 4 (remarque longue, à fondre). 104 n° 4 (A seulement par la marque ■44732, qui porterait plutôt sur le n° 11). 79 n° 12.
- Marques mal placées : ■44724 est sur 21 n° 2 alors que la PR porte le n° 3 (corollaire 2.16) ; ■44732 est sur 104 n° 4 alors que la PR porte le n° 11. Le contenu des PR #44716 (22 n° 5), #44725 (39 n° 3), #44708 (16 n° 17), #44755 (93 n° 9) et #44723 (161-1 n° 8) est dans des lemmes classés C ou B qui ne portent pas la marque.

**Les B ou C qu'on pourrait monter en A** :
- 106 n° 2, 3, 7, 8, 9 (hypothèses superflues, mais ce que la généralisation donne est le lemme de Brown, publié en 1973). 125 n° 5, 7. 21 n° 6, 7. 74 n° 1, 4 (piste dans le titre). 85 n° 5, 6, 8 (relèvent de la piste 85-g2-pgl2-moduli-over-z). 42 n° 3 (finding apparié). 93 n° 6 (correction de la lecture, jugée mineure). 37 n° 4 (étape de Schanuel, borne p + 1 ; la remarque n° 6 en A la reprend). 22 n° 11 (cœur de l'obstruction).

**Correspondance avec le Lean** :
- 158 n° 5 : aucun théorème ne démontre le contre-exemple {1, a, b}. `contre_pseudoCofiltrant` et `contre_groupeEnveloppantTrivial` portent sur l'exemple du n° 6, et la table l'a corrigé.
- 161-2 n° 2 : aucun théorème n'y correspond exactement ; `descente` est voisin.
- 113 : `morita` et `restriction_isEquivalence` sont des `instance`.

**D** :
- Les étiquettes « Conjecture (Grothendieck, p. N) » suivent le titre. Pour 22 n° 15 (contre-exemple), 133 n° 9 et 70 n° 5 (exemples), et 84 n° 12, 13, 158 n° 9, 10, 104 n° 14, 93 n° 15, il faut vérifier sur la page si elle conjecture, affirme ou demande.
- Contre-exemples non démontrés gardés en VII : 77 n° 9, 101-sheaf-duality-dim-two-fails, 149-dominant-faithfulness-curves. Ce sont des réfutations, pas des énoncés ouverts. La sous-rubrique « contre-exemples non vérifiés » de VII leur conviendrait.
- Énoncés de Quillen (162-5-bordism-correspondences-universal, 162-5-formal-categories-flat-conormal-de-rham) : gardés avec l'étiquette « Énoncé non démontré (Quillen, d'après …) ». Leur place dans l'annexe Grothendieck est à décider.
- Retirés sur l'hypothèse « probablement connu », sans recherche : 36-h1-invariant-cycle-defect, 6-same-formal-group-not-isogenous, 100-neron-extension-p-divisible, 116, 90, 119. Candidates retirées : 58-local-hom-comparison-depth-off-y, 29-inertia-matrix-determinant, 155-takeuchi-idealiser (une définition).
- Gardés malgré une lecture fragile : 129-ext2-vanishing-p-odd (le mot « inv. » de la p. 95), 45-h1-surjectivity-dim-one, 128-infinitesimal-descent-theorem, 18-archimedean-lattice-cocycle.
- 161-1 n° 17 et 93 n° 14 : définitions encadrées avec piste, sans ◇, classées C. Elles pourraient passer en D.
