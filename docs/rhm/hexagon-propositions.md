# Article RHM vers Hexagon : propositions en attente de décision (#120)

Préparé le 10 novembre 2026, pour l'issue
[#120](https://github.com/Commutator-IO/grothendieck-project/issues/120).
Les numéros de ligne renvoient à `docs/rhm/article.tex` au commit `a8b797b`.
Chaque proposition donne le texte exact, l'endroit où il irait, les sources
lues et une case à cocher. Rien de ce qui suit n'est dans l'article tant que la
case n'est pas cochée par Michel.

**Rien n'a été compilé.** La session n'avait aucun moteur TeX (ni `tectonic`,
ni `pdflatex`). `article.pdf` n'a pas été régénéré : il ne reflète donc pas les
trois commits ci-dessous. La variante `article-hexagon.tex` n'a jamais été
compilée.

## Ce qui est déjà fait dans `docs/rhm/`

| Commit | Objet |
|---|---|
| `9d6171e` | Collations : résumés français et anglais, « Limites », déclaration IA |
| `a6cf3d0` | Cadrage, formulation seule : le projet ne s'appelle plus « l'édition » (4 endroits) ; « Limites » renvoie à « L'erreur sur la page » |
| `a8b797b` | Forme Hexagon : `article-hexagon.tex`, liens vers les PDF de Montpellier, liens Lean et entrée Palomar, `npm run rhm:hexagon` |

L'introduction, la discussion et la conclusion n'ont pas été touchées.

---

## 1. Collations

**Fait (`9d6171e`).** La formulation de l'issue est appliquée, restreinte à ce
qu'elle couvre de façon sûre, le fonds de Montpellier :

> Toutes les citations que l'article tire du fonds de Montpellier ont été
> collationnées sur le fac-similé par l'auteur ; le reste de la transcription,
> qui sert au comptage et au repérage, ne l'est pas.

Elle est dans le résumé, dans l'*abstract* (« Every quotation the article takes
from the Montpellier fonds has been collated against the facsimile by the
author; the rest of the transcription, which serves for counting and locating,
has not. »), dans « Limites » et dans la déclaration IA. « Limites » garde les
décomptes antérieurs (135 lectures dans 54 cotes, 31 lettres, 57 dates) comme
vérifications ponctuelles.

### Ce que le dépôt enregistre, et ce qu'il n'enregistre pas

- **Montpellier.** La seule source de « toutes les citations ont été
  collationnées » est l'issue #120 elle-même (6 novembre). Le dépôt ne
  l'enregistre pas : sur les 62 adresses « cote, lot, page » distinctes que
  l'article cite par `\lot`, 3 seulement portent, à la page citée du fichier de
  transcription, une note de vérification sur le fac-similé (comptage par
  script le 10 novembre, sur les `\note{}` qui nomment la vérification). La
  phrase de « Limites » ne dit donc plus que ces collations « sont notées dans
  les fichiers de transcription » ; elle le dit seulement des 135 lectures.
- **IHÉS.** L'article donne de courtes citations de 15 passages environ des
  pièces de l'IHÉS (lignes 221, 319, 321, 331, 341, 351, 369). « Limites »
  disait, et dit toujours, qu'elles viennent « d'une transcription non
  collationnée sur les numérisations ». Rien dans le dépôt n'enregistre une
  collation depuis. La phrase a été gardée et précisée : ces pièces « ne
  comptent ni parmi les citations collationnées ni parmi ces 135 lectures ».
- **BnF.** Les citations de la section « Après Montpellier » ne viennent
  d'aucune transcription par machine : les papiers ne sont pas en ligne, et
  l'article dit que l'auteur les a consultés. Aucune phrase de « Limites » ne
  dit comment elles ont été relevées.
- **Bourbaki.** Les lectures de la rédaction n° 457 ont été vérifiées sur le
  fac-similé le 30 octobre (commit `0cc3a5b`, clôture de #50) ; la section
  paraphrase depuis le 6 novembre.

### Propositions

- [ ] **1.a — Enregistrer la collation.** Ajouter au dépôt la liste des
  citations collationnées (cote, lot, page, date), ou une `\note{}` par page
  dans les transcriptions, pour que la phrase du résumé ait une trace
  vérifiable. Sans cela, un relecteur qui ouvre les fichiers n'y trouve que 3
  pages notées.
- [ ] **1.b — IHÉS.** Si les citations de l'IHÉS ont elles aussi été
  collationnées sur les numérisations, remplacer dans « Limites » (ligne 409)
  la phrase « Les pièces de l'IHÉS sont citées d'après une transcription non
  collationnée sur les numérisations ; elles ne comptent ni parmi les citations
  collationnées ni parmi ces 135 lectures. » par :
  > Les citations des pièces de l'IHÉS ont été collationnées de même sur les
  > numérisations de l'Institut.

  Sinon, ne rien changer.
- [ ] **1.c — BnF.** Ajouter dans « Limites », après la phrase sur l'IHÉS :
  > Les citations des papiers de la BnF ont été relevées par l'auteur à la
  > consultation, sans transcription par machine.

  À confirmer par Michel : c'est ce que disent la section de l'article et le
  livre *Archives outillées* (chap. « Deux sources à la marge »), mais aucun
  fichier du dépôt ne dit comment chaque citation a été notée en salle.
- [ ] **1.d — Phrases devenues inexactes dans les parties réservées à
  Michel** (non modifiées) :
  - Introduction, ligne 132 : « Cette transcription n'a pas d'autorité :
    l'auteur n'en a vérifié sur le fac-similé que des lectures ponctuelles
    (section Limites). »
  - Introduction, ligne 134 : « Sauf mention contraire, l'auteur ne les a pas
    collationnées sur le fac-similé ; chacune renvoie à la page où le lecteur
    peut le faire. » Cette phrase contredit maintenant le résumé.
  - Conclusion, ligne 415 : « Ces constats reposent sur une transcription faite
    par machine, dont l'auteur n'a vérifié que des lectures ponctuelles, et la
    vérification des passages cités reste la condition de leur publication. »
  - Hors article : `docs/rhm/README.md`, « Avant soumission », premier point
    (« Collationner chaque citation et chaque date sur le fac-similé ») ;
    `docs/livre-archives/chapitres/03-montpellier.tex`, bilan (« 125 lectures
    dans 54 dossiers »).

---

## 2. Déclaration sur l'usage de l'intelligence artificielle

**Fait (`9d6171e`) :** seule la proposition sur les collations a changé.
**Non fait :** la réécriture complète. La déclaration actuelle contient une
phrase à la première personne de l'auteur, que la nouvelle rédaction
supprimerait : « Le texte de l'article a été rédigé avec l'aide de ces modèles
sous la direction de l'auteur, qui en a relu et corrigé le contenu et en assume
l'entière responsabilité. » Tant que l'introduction, la discussion et la
conclusion ne sont pas réécrites par Michel, dire que les modèles ne sont que
des outils de transcription et d'indexation serait faux.

- [ ] **2.a — Texte proposé, à mettre à la place de la déclaration (ligne 421)
  une fois les trois parties réécrites :**

  > Les modèles de langage ont servi ici d'outils de transcription et
  > d'indexation. Les transcriptions et les lectures modernisées des cotes de
  > Montpellier ont été produites par des modèles d'Anthropic (Claude Opus 5,
  > Opus 5.5, Fable 5 et Fable 5.1), sous des règles éditoriales écrites par
  > l'auteur. Les mêmes modèles ont établi, sous sa direction, les registres
  > dont l'article est tiré ; chaque entrée renvoie au fichier et à la ligne
  > qui la fondent. L'auteur a collationné sur les fac-similés toutes les
  > citations que l'article tire du fonds de Montpellier ; dans le reste de la
  > transcription, il n'a vérifié que des lectures ponctuelles, signalées dans
  > les fichiers. Les pièces de l'IHÉS et les documents des archives de
  > Bourbaki ont été lus de la même façon ; la section « Sources, droits et
  > éthique » dit ce qu'il en a été fait. Les preuves formelles de l'annexe
  > [Hua 2026b] ont été écrites en Lean 4 par ces modèles, sous la direction de
  > l'auteur ; Lean vérifie mécaniquement leur correction, et les
  > démonstrations rédigées de l'annexe en sont tirées. L'introduction, la
  > discussion et la conclusion sont de l'auteur. Les autres sections ont été
  > rédigées avec l'aide de ces modèles, puis relues et corrigées par l'auteur,
  > qui assume l'entière responsabilité de l'ensemble.

  Trois points à trancher avant de l'adopter :
  1. **La dernière phrase.** L'issue demande que la déclaration décrive les
     modèles comme des outils de transcription et d'indexation. Les sections 2
     à 8 ont pourtant été rédigées avec leur aide (c'est ce que dit la
     déclaration actuelle). La phrase « Les autres sections ont été rédigées
     avec l'aide de ces modèles » le maintient. La supprimer n'est exact que si
     Michel réécrit aussi ces sections.
  2. **La liste des modèles.** L'article a aussi été modifié par Sonnet 5.5
     (commit `894ee77`, 4 novembre) et par Fable 5.2 (les trois commits de ce
     jour). L'article sur le coût carbone nomme Opus 5.5, Sonnet 5.5 et
     Haiku 5.5. La liste est à compléter ou à restreindre explicitement aux
     transcriptions.
  3. **Bourbaki et IHÉS.** La phrase qui les nomme est nouvelle. Elle repose
     sur `docs/bourbaki/rhm-facts.md` (« first machine passes (Opus 5.5) ») et
     sur l'issue #86 pour l'IHÉS.

---

## 3. Section « Sources, droits et éthique » (brouillon)

**Où :** une section non numérotée, entre « Limites » et « Conclusion », ou à
la place d'une partie de « Sources et données » (ligne 423), qui dit déjà une
partie de ces choses.

**Pourquoi elle n'est pas dans l'article :** elle rapporte les réponses de
tiers. Chaque paragraphe porte sa case : Michel confirme la date, la teneur et
le droit de la rapporter.

### 3.1 Montpellier

- [ ] Texte proposé :

  > Le fonds de Montpellier est sous droits. Grothendieck est mort le
  > 13 novembre 2014 : ses droits patrimoniaux appartiennent à ses héritiers
  > jusqu'à la fin de 2084, et son droit moral, dont le droit de divulgation,
  > est perpétuel. L'université diffuse les images des cotes en libre accès. En
  > septembre 2026, l'auteur a demandé par écrit au service des archives si des
  > transcriptions de ces cotes, présentées comme une édition de démonstration,
  > restaient dans le cadre de cette mise à disposition, et qui pouvait en
  > autoriser ou en refuser la publication. Le service a répondu que la
  > question était juridique et qu'il la transmettait aux services juridiques
  > de l'université, qui examinent la convention signée avec la famille ; que
  > l'université détient le droit de diffuser les images numérisées, ce qui ne
  > l'autorise pas pour autant à permettre que leur contenu soit mis à
  > disposition sous une autre forme ; et qu'il faudrait peut-être s'adresser
  > directement aux enfants de Grothendieck. L'avis des services juridiques
  > n'est pas parvenu à la date de cet article. En attendant, les
  > transcriptions restent des documents de travail : chaque page porte la
  > mention « Édition de démonstration », le projet n'en revendique aucun droit
  > et n'accorde aucune licence, aucun dépôt à identifiant pérenne n'en est
  > fait, et elles seront retirées à la demande de l'université ou des ayants
  > droit. Un réglage du déploiement retire du site tout le texte des
  > transcriptions sans rien effacer du dépôt. Aucun fac-similé n'est conservé
  > ni redistribué : le site affiche les pages servies par l'université.

  Sources : issue #23 (corps, et commentaires des 23 et 24 septembre 2026 :
  premier courriel, relance, réponse de l'université rapportée le 24) ; issue
  #31 et son commentaire du 27 septembre (l'interrupteur `RENDER_TRANSCRIPTS`,
  commit `f1971f9`) ; `RIGHTS.md` ; `README.md`, « The rights switch » ;
  `docs/livre-archives/chapitres/03-montpellier.tex`.

  À confirmer :
  - la date du premier courriel (le dépôt dit seulement « avant le
    23 septembre ») et celle de la réponse (rapportée le 24 septembre) ;
  - si les services juridiques ont répondu depuis. `RIGHTS.md` et le livre
    disent encore que la question « n'a pas reçu de réponse », alors que
    l'issue #23 rapporte une première réponse : les deux textes sont à
    accorder ;
  - si les héritiers ont été contactés ;
  - l'état actuel de l'interrupteur (transcriptions affichées ou non sur le
    site le jour du dépôt). Le dépôt ne l'enregistre pas : c'est une variable
    du dépôt GitHub ;
  - le sens de la mention « the transcriptions are not published (BnF,
    2026-09-29) » dans `scripts/bundle-tex.mjs` et `scripts/bundle-tei.mjs` :
    aucun autre fichier ne dit ce que la BnF a répondu ce jour-là.

### 3.2 BnF

- [ ] Texte proposé :

  > Les papiers de Lasserre sont entrés à la Bibliothèque nationale de France
  > en 2023 (NAF 29093). Contactée en septembre 2026 au sujet des droits, la
  > Bibliothèque a orienté l'auteur vers son département des Manuscrits. Ces
  > papiers se consultent sur place, après inscription, sur déclaration d'un
  > objectif de recherche et signature d'un engagement de confidentialité ;
  > rien n'en est publié sans l'accord de la Bibliothèque et des cinq
  > héritiers, qui détiennent les droits d'auteur. L'auteur a consulté les
  > boîtes 3, 14, 34, 35, 39, 40 et 43 en octobre et novembre 2026. La section
  > « Après Montpellier » les décrit dans ses propres mots et n'en donne que de
  > brefs extraits. Aucune image de ces papiers n'a été soumise à un modèle de
  > langage.

  Sources : issue #23 (commentaire du 24 septembre : contact BnF) ; issue #37 ;
  `docs/bnf/fiche.tex`, ligne 167 ; `docs/livre-archives/chapitres/06-autres.tex` ;
  commits `8d54311` (4 novembre) et `c062f13` (29 octobre : « quotation allowed
  by the BnF » pour le f. 378).

  À confirmer, et c'est le point le plus sérieux de ce fichier :
  - **l'autorisation de citer.** Le dépôt n'enregistre une autorisation de la
    BnF que pour une citation (f. 378). La section en compte une trentaine (39 passages entre guillemets, dont
    quelques-uns viennent de la notice et du communiqué de la BnF). La
    règle écrite du projet est « rien de publié sans l'accord de la BnF et des
    cinq héritiers ». Si la phrase « n'en donne que de brefs extraits » doit
    rester, il faut pouvoir écrire qui les a autorisés ;
  - **l'engagement de confidentialité** : ce qu'il permet de publier ;
  - la dernière phrase (« aucune image… ») : elle est déduite de ce que les
    papiers ne sont pas en ligne. À confirmer, ou à supprimer ;
  - le commit `be44955` a retiré le jour exact de la consultation : le
    brouillon ne donne donc que les mois.

### 3.3 Archives de Bourbaki (AHP, ACNB)

- [ ] Texte proposé :

  > Les archives de l'Association des collaborateurs de Nicolas Bourbaki sont
  > mises en ligne par les Archives Henri Poincaré. En octobre 2026, les
  > rédactions de Grothendieck ont été transcrites par un modèle de langage, et
  > les comptes rendus de congrès qui le nomment parcourus de la même façon.
  > Ces transcriptions n'ont jamais été versées au dépôt public. L'autorisation
  > de les publier a été demandée le 5 octobre 2026 aux responsables du projet
  > BANANA. La réponse est venue le 4 novembre 2026 : l'Association s'oppose à
  > l'utilisation de ses archives par des outils d'intelligence artificielle.
  > Le projet a suspendu ce travail : il ne lit plus de nouvelle
  > rédaction, ne publie rien de plus, et les transcriptions restent privées.
  > La section « Le travail collectif : Bourbaki » ne cite plus ces documents :
  > elle dit dans ses propres mots ce que montrent les rédactions et la
  > *Tribu*, avec leurs références dans le fonds. L'annexe Lean ne compte plus
  > les deux rédactions de Bourbaki.

  Sources : issue #50 (commentaires des 10, 18, 23, 27 et 30 octobre) ;
  `docs/livre-archives/chapitres/04-bourbaki.tex`, « Les droits, et ce qu'on a
  décidé » ; commits `f337852`, `aa49b1e` (6 novembre) ; issue #120, rubrique
  « Bourbaki » ; `README.md`, « The rights switch » (dossiers
  `transcripts-bourbaki/` ignorés par git).

  À confirmer :
  - qui a répondu le 4 novembre, et au nom de qui (ACNB, AHP, ou les deux) ; le
    dépôt ne garde pas le texte de la réponse, seulement sa teneur en une
    phrase ;
  - la relance annoncée le 23 octobre (« whom to ask, ACNB or AHP ») : a-t-elle
    été envoyée ?
  - **le maintien de la section.** Ce qu'elle rapporte vient d'une lecture par
    machine faite avant la réponse. L'issue juge la paraphrase « in line with
    the 4 November reply » : c'est la décision de Michel, et le brouillon la
    rapporte sans la juger. Un historien demandera si l'Association a été
    informée de ce maintien ;
  - `docs/bourbaki/rhm-facts.md` et `docs/bourbaki/findings.md`, dans le dépôt
    public, citent encore de courts passages des rédactions. Ce n'est pas
    l'article, mais c'est le même engagement.

### 3.4 Carnets de Quillen

- [ ] Texte proposé :

  > Les carnets de recherche de Daniel Quillen, mort en 2011, sont mis en ligne
  > par le Clay Mathematics Institute et restent sous droits. Leurs
  > transcriptions n'ont jamais été versées au dépôt public ni affichées sur le
  > site, et le projet a cessé d'en transcrire à la fin de septembre 2026.
  > L'article n'en donne que des citations de quelques mots, avec le carnet et
  > la page, que le lecteur peut ouvrir sur le site du Clay Institute.

  Sources : `docs/livre-archives/chapitres/05-quillen.tex` ; `README.md`
  (« Quillen and Bourbaki go further ») ; issue #36 (titre : « never committed
  or pushed »).

  À confirmer :
  - le dépôt n'enregistre aucune demande adressée au Clay Institute ni à la
    famille. Le brouillon ne dit donc pas qu'on leur a écrit ;
  - **l'article cite les carnets mot pour mot** (ligne 319, plusieurs passages
    courts en anglais, dont ceux ajoutés le 7 novembre par le commit
    `ff9e716`). Le livre *Archives outillées*
    (chap. « Les carnets de Daniel Quillen ») dit pourtant que le projet
    « énonce tout dans ses propres mots et ne cite que le carnet et la
    date », et l'issue range Quillen parmi ce qui est « kept private ». Soit
    ces passages sont paraphrasés, comme ceux de Bourbaki l'ont été le
    6 novembre, soit la règle est écrite autrement. Avant un dépôt
    irrévocable (§ 3.7), la première voie est la plus sûre.

### 3.5 IHÉS (non demandé par l'issue, mais un lecteur le demandera)

- [ ] Texte proposé :

  > Les pièces du fonds Grothendieck--Illusie sont lues sur le serveur de
  > numérisations que l'Institut rend accessible en ligne. La correspondance
  > reste sous le droit de ses auteurs. L'article n'en donne que de courtes
  > citations, au titre du droit de courte citation, et les conditions de cet
  > usage restent à confirmer avec les archives de l'Institut.

  Source : `docs/livre-archives/chapitres/06-autres.tex` (« toutes deux sont à
  confirmer auprès des archives de l'IHÉS ») ; « Sources et données » de
  l'article. À confirmer : si l'IHÉS a été contacté.

### 3.6 Le traitement des images par un prestataire commercial

Le dépôt établit ceci : les modèles sont ceux d'Anthropic, utilisés « au moyen
de l'outil Claude Code » (`docs/carbon/article.tex`, ligne 294), sous un
« abonnement » à quota hebdomadaire (*ibid.*, ligne 276 ;
`docs/livre-methodes/chapitres/09b-sobriete.tex`, ligne 145). **Le dépôt ne dit
pas de quel abonnement il s'agit**, et les conditions diffèrent du tout au tout
selon le cas. Les pages lues le 10 novembre 2026 disent :

| Page (date portée par la page) | Ce qu'elle dit |
|---|---|
| *Commercial Terms of Service*, anthropic.com/legal/commercial-terms (« Effective Jun 17, 2025 ») | Préambule : ces conditions régissent l'usage des clés d'API et des offres qui s'y réfèrent ; « Our consumer offerings (e.g., Claude.ai) are governed by our Consumer Terms of Service instead ». Section B : « Anthropic may not train models on Customer Content from Services. » Le client « retains all rights to its Inputs » et « owns its Outputs ». |
| *Consumer Terms of Service*, anthropic.com/legal/consumer-terms (« Effective Oct 8, 2025 ») | « We may use Materials to provide, maintain, and improve the Services and to develop other products and services, including training our models, unless you opt out of training through your account settings. Even if you opt out, we will use Materials for model training when: (1) you provide Feedback to us regarding any Materials, or (2) your Materials are flagged for safety review […]. » |
| *Data usage*, code.claude.com/docs/en/data-usage (sans date ; lue le 10 novembre 2026) | Abonnements Free, Pro, Max et Ultra : « We will train new models using data from Free, Pro, Max, and Ultra accounts when this setting is on (including when you use Claude Code from these accounts). » Conservation : cinq ans si le réglage est activé, trente jours sinon. Comptes Team, Enterprise et API : « Anthropic does not train generative models using code or prompts sent to Claude Code under commercial terms, unless the customer has chosen to provide their data to us for model improvement » ; conservation standard de trente jours. Sessions dans le nuage : « Anthropic stores the session transcript so you can return to the session later. » |
| *How long do you store my organization's data?*, privacy.claude.com (« Last updated: July 1, 2026 ») | Produits commerciaux et API : « we automatically delete inputs and outputs on our backend within 30 days of receipt or generation », sauf accord contraire, obligation légale ou application de la politique d'usage ; dans ce dernier cas, « We retain inputs and outputs for up to 2 years and trust and safety classification scores for up to 7 years ». Les retours envoyés (pouce, rapport de bogue) sont gardés cinq ans. |

- [ ] **3.6.a — Si l'abonnement est un compte Team, Enterprise ou une clé
  d'API** (conditions commerciales) :

  > Les images des pages ont été lues par les modèles d'un prestataire
  > commercial, Anthropic, au moyen de son outil Claude Code. Le projet ne
  > conserve aucune de ces images : il les lit sur le serveur de l'université.
  > Les conditions commerciales du prestataire (version en vigueur depuis le
  > 17 juin 2025, lue le 10 novembre 2026) lui interdisent d'entraîner ses
  > modèles sur les contenus soumis par ses clients. Sa documentation indique
  > qu'il conserve ces contenus trente jours, et plus longtemps, jusqu'à deux
  > ans, lorsqu'un échange est signalé au titre de sa politique d'usage.

- [ ] **3.6.b — Si l'abonnement est un compte Pro ou Max** (conditions des
  particuliers) :

  > Les images des pages ont été lues par les modèles d'un prestataire
  > commercial, Anthropic, au moyen de son outil Claude Code, sous un
  > abonnement individuel. Le projet ne conserve aucune de ces images : il les
  > lit sur le serveur de l'université. Les conditions de cet abonnement
  > (version en vigueur depuis le 8 octobre 2025, lue le 10 novembre 2026)
  > permettent au prestataire d'entraîner ses modèles sur les contenus soumis,
  > sauf si l'abonné s'y oppose dans les réglages de son compte. L'auteur
  > [avait / n'avait pas] désactivé ce réglage [depuis le … ]. Réglage
  > désactivé, la documentation indique une conservation de trente jours ;
  > activé, de cinq ans. Dans les deux cas, les contenus signalés pour examen
  > de sécurité peuvent servir à l'entraînement.

  À confirmer, par Michel seul :
  - le type d'abonnement, et s'il a changé depuis août 2026 ;
  - l'état du réglage « aider à améliorer Claude » pendant toute la durée du
    projet (claude.ai/settings/data-privacy-controls). **S'il a été activé à un
    moment où des pages de Montpellier, de l'IHÉS, de Quillen ou de Bourbaki
    étaient lues, la section doit le dire** : c'est précisément ce que
    l'opposition du 4 novembre vise ;
  - si des retours (`/feedback`, pouce) ont été envoyés depuis des sessions qui
    contenaient des pages ;
  - « le projet ne conserve aucune de ces images » : vrai du dépôt
    (`archives/` est ignoré par git, `RIGHTS.md`), mais une copie locale existe
    pour la lecture par lots (`npm run archive`). Formulation plus exacte
    possible : « ne publie ni ne redistribue aucune de ces images » ;
  - les sessions dans le nuage (Claude Code sur le web) clonent le dépôt et
    gardent la transcription de la session ; celle du 10 novembre en est une.

  Non vérifié : l'addendum de traitement des données (DPA) auquel renvoient les
  conditions commerciales, et la politique de confidentialité (« Effective
  Sep 10, 2026 »), parcourue seulement.

### 3.7 Une conséquence du dépôt sur Hexagon

- [ ] **À décider avant de déposer.** La page « About » de Hexagon (lue le
  10 novembre 2026) dit que le dépôt accorde à Hexagon une licence « worldwide,
  non-exclusive, perpetual, irrevocable, royalty-free », et qu'un article
  retiré « remains available but will be marked with a notice of the
  withdrawal ». L'engagement de `RIGHTS.md` (« aucun dépôt à identifiant
  pérenne », retrait « sans discussion ni délai ») porte sur `transcripts/`,
  pas sur les articles ; mais l'article cite des inédits de Montpellier, de
  l'IHÉS et de la BnF. Une fois sur Hexagon, ces citations ne se retirent plus.
  L'article Lean y est déjà (2611.00125), sans citation longue. Pour celui-ci,
  la question se pose citation par citation, d'abord pour la BnF (§ 3.2).
  Il faut aussi choisir la licence de diffusion au moment du dépôt.

---

## 4. Cadrage : la lecture par machine comme complément, les erreurs comme fait d'écriture

**Fait (`a6cf3d0`), formulation seule, hors introduction, discussion et
conclusion :**

| Ligne | Avant | Après |
|---|---|---|
| 239 | « contre-exemple de l'édition vérifié en Lean » | « contre-exemple dû au présent projet et vérifié en Lean » |
| 313 | « que l'édition a transcrite par reconnaissance vocale » | « que le projet a transcrite par reconnaissance vocale » |
| 411 | « ainsi que des erreurs sur les pages elles-mêmes, et l'annexe les détaille » | « ainsi que des erreurs sur les pages elles-mêmes, de celles que décrit la section « L'erreur sur la page », et l'annexe les détaille » |
| annexe B | « Les démonstrations sont celles de l'édition » ; « Le contre-exemple est de l'édition » | « celles du projet » ; « est dû au projet » |

Raison : « Sources et données » dit que les transcriptions sont « sans valeur
d'édition » ; le projet ne peut pas s'appeler « l'édition » à côté des éditions
établies par des mathématiciens, que l'introduction énumère.

**Propositions (non appliquées : elles changent ce qui est affirmé, ou sont
dans une partie réservée) :**

- [ ] **4.a — Ligne 128 (introduction).** « Les 158 autres cotes (10 945 pages)
  n'avaient été transcrites par personne. » La phrase oppose la machine à
  l'absence d'édition. Proposition :
  > Les 158 autres cotes (10 945 pages) n'ont pas d'édition ; la transcription
  > par machine utilisée ici n'en est pas une, et ne dispense pas d'en faire.
- [ ] **4.b — Ligne 132 (introduction).** « Cet article en fait l'expérience
  sur le fonds de Montpellier […] » après l'échange Connes--Serre. Lue seule,
  la phrase donne raison à l'un contre l'autre. Proposition :
  > Cet article en fait l'expérience sur le fonds de Montpellier, à côté des
  > éditions établies par des mathématiciens et sans prétendre les remplacer :
  > la transcription de 164 cotes (9 414 pages) par un modèle de langage sert à
  > compter, à dater et à repérer.
- [ ] **4.c — Ligne 160 (« Les possibilités de la méthode »).** « Sur
  l'ensemble des cotes, ils font voir des régularités qu'une lecture cote par
  cote ne montre pas. » Proposition :
  > Sur l'ensemble des cotes, ils font voir des régularités qu'une lecture cote
  > par cote montre moins aisément, et que cette lecture seule peut confirmer.
- [ ] **4.d — Ligne 239 (« L'erreur sur la page »).** « Il ne voit pas toutes
  ses erreurs. Dans ses notes sur les pseudo-droites (n° 80), un « Théorème »
  affirme […] ; il est faux tel qu'il est écrit […]. » La phrase présente
  l'erreur comme une trouvaille du projet. Proposition :
  > Toutes ne sont pas reprises sur la page, comme il arrive dans des notes
  > écrites pour soi. Dans ses notes sur les pseudo-droites (n° 80), un
  > « Théorème » affirme que, sous deux hypothèses, un arrangement est de l'un
  > de deux types ; tel qu'il est écrit, l'énoncé ne tient pas pour six droites
  > […].
- [ ] **4.e — Ligne 239, même paragraphe.** « Il arrive enfin que la page voie
  juste là où un texte imprimé plus tard demandait une hypothèse de plus. […]
  le même exemple montre que, dans une proposition publiée en 2006 […], l'une
  des conditions n'entraîne pas les autres, ce que Cisinski a confirmé. » C'est
  l'énoncé le plus proche d'une « découverte » sur la littérature. Deux voies :
  le garder ici, ramené à un fait d'écriture (« La page de 1983 contient déjà
  l'exemple qui sépare ces conditions »), et laisser la remarque sur la
  proposition de 2006 à l'annexe ; ou le déplacer en entier dans l'annexe. La
  référence qui appuie la confirmation (`\moanswer`, entrée `cisinski2026mo`)
  est à relire au moment de trancher : un historien attend une source
  publiée ou une communication personnelle datée.
- [ ] **4.f — Ligne 156 (« Le protocole »).** « Elle signale aussi deux cent
  trente et une pistes : des énoncés qui pourraient manquer à la littérature
  […]. » Le conditionnel est déjà là. Proposition, pour le fermer :
  > Elle signale aussi deux cent trente et une pistes, des énoncés dont la
  > recherche bibliographique n'a pas trouvé d'équivalent publié, ce qui ne
  > prouve pas qu'il n'en existe pas ; […]
- [ ] **4.g — Ligne 415 (conclusion).** « […] les seconds y trouveront des
  questions qu'aucun texte imprimé n'a reprises et des énoncés restés sans
  démonstration […]. » Affirmation de nouveauté que « Trois interdits »
  (ligne 164) interdit. À reprendre par Michel.
- [ ] **4.h — Discussion, dernier paragraphe (ligne 405, dépôt d'OpenAI).**
  « […] ils indiquent où ces énoncés apparaissent d'abord, comme questions,
  dans le fonds. » « D'abord » dit une antériorité que les feuillets non datés
  (n° 149) ne permettent pas. À reprendre par Michel.

---

## 5. Forme Hexagon

### 5.0 Ce que le lieu demande : ce qui a pu être lu, et ce qui ne l'a pas été

Hexagon est le site hexagonmath.org (identifié par
`docs/livre-methodes/chapitres/10-publier.tex`, § « Hexagon, à côté d'arXiv »,
et par les dépôts 2611.00125, 2611.00188, 2611.00189 du projet). La page
« About » a été lue le 10 novembre 2026 (elle porte « © 2026 Hexagon
Mathematics Foundation », « public beta », sans date de version) :

- on dépose les **sources TeX** ; un ZIP fait au plus 100 Mio, 250 Mio une fois
  décompressé ;
- « Code such as Lean formalizations is not accepted as part of a Hexagon
  submission » ; on peut lier « formalizations in mathlib, Palomar, prove2.me,
  or TauCeti » ;
- les contrôles automatiques vérifient que le texte **compile** ; un modérateur
  humain relit pendant la bêta ; un dépôt par jour et par compte ;
- les contributeurs sont liés par leur ORCID ; « Artificial-intelligence
  systems cannot be contributors » ; ils doivent « reasonably believe that the
  work is correct » et avoir fait « a good faith effort to ensure that it
  accurately cites prior work » ;
- licence et retrait : voir § 3.7.

**Non vérifié à la source :** l'exigence de pdfLaTeX, celle d'une page de titre
et le champ MSC. La page de dépôt (hexagonmath.org/submit) demande une
connexion ORCID et n'a pas pu être lue. Ces trois points viennent de l'issue
#120 et de la pratique du dépôt (`docs/bigon/README.md` : « pdfLaTeX, a single
file with its bibliography inline »).

### 5.a pdfLaTeX : inventaire et variante

**Fait (`a8b797b`).** Sur le modèle de `article-hal.tex` et `article-ams.tex`,
`article-hexagon.tex` définit `\hexagon` et `\ams` puis lit `article.tex`.

Ce qui bloquait pdfLaTeX :

| Obstacle | Où | Traitement |
|---|---|---|
| `fontspec` | préambule | sous `\hexagon` : `fontenc` T1, `inputenc` utf8, `lmodern` |
| ponctuation active de `babel-french` sous pdfTeX, incompatible avec TikZ | `fig-carte.tex`, figure de l'annexe B | sous `\hexagon` : `\usetikzlibrary{babel}` |
| classe `smfart` et `rhm.sty` | préambule | branche `\ams` existante : `amsart` + `halbib.sty` |
| caractères hors ASCII | `article.tex`, `article.bib`, `fig-carte.tex` | aucun obstacle : lettres latines accentuées, « », œ, Œ, °, º, ‘ ’, …, — ; tous couverts par utf8 + T1 (relevé par script) |
| `unicode-math`, `polyglossia`, `minted`, polices système | — | absents de l'article |

- [ ] **5.a.1 — Compiler.** `cd docs/rhm && pdflatex article-hexagon && bibtex
  article-hexagon && pdflatex article-hexagon && pdflatex article-hexagon`.
  Points à regarder à la première compilation, parce que rien n'a été
  essayé : le titre en capitales d'`amsart` avec les accents ; les liens
  `\lot` (le numéro de page calculé par `\numexpr` dans l'URL) ; les deux
  figures TikZ ; la bibliographie `rhmunsrtnat` hors de la classe SMF (elle
  fonctionne déjà pour `article-ams.tex` sous tectonic) ; `caption` avec
  `amsart`.
- [ ] **5.a.2 — Régénérer `article.pdf`** (`tectonic -X compile article.tex`)
  pour qu'il porte les changements des commits `9d6171e` et `a6cf3d0`.

### 5.b Un seul ZIP, sans code Lean

**Fait (`a8b797b`).** `npm run rhm:hexagon` (`scripts/rhm-hexagon.mjs`) écrit
`exports/rhm-hexagon-<date>-<commit>.zip` avec, à plat :
`article-hexagon.tex`, `article.tex`, `article.bib`, `fig-carte.tex`,
`halbib.sty`, `rhmunsrtnat.bst`, et `article-hexagon.bbl` s'il existe. Le
script refuse de construire si un fichier `.lean` ou un listing de code
entrerait dans l'archive, si un fichier lu par `\input` manque, ou si un
fichier Lean est nommé sans lien. Le script a été exécuté (6 fichiers,
238 ko) ; l'archive n'a pas été compilée.

L'article ne contenait déjà aucun code Lean : l'annexe B donne des énoncés et
des démonstrations rédigées, et nomme trois fichiers.

- [ ] **5.b.1 — Joindre le `.bbl`.** Compiler avant de lancer le script, pour
  que le dépôt ne dépende pas d'un passage de BibTeX côté Hexagon (les
  articles déjà déposés ont leur bibliographie dans le fichier).

### 5.c Liens

**Fait (`a8b797b`), dans la variante Hexagon seulement** (les autres variantes
gardent les liens vers le site) :

- `\lot{cote}{lot}{page}` ouvre
  `https://grothendieck.umontpellier.fr/<cote>.pdf#page=<page + 1>` ; pour une
  étendue (« 124--129 »), la première page. Le décalage d'une page est celui
  que dit l'article (« celle du fichier numérique, décalée d'une unité par une
  page de garde »). Les adresses répondent (essai le 10 novembre sur les cotes
  1, 134-2, 156-2 et 161-3). L'ancre `#page=` dépend du lecteur PDF du
  navigateur.
- Les trois fichiers Lean de l'annexe B sont des liens vers
  `github.com/Commutator-IO/grothendieck-project/blob/main/lean/Grothendieck/`.
- « Sources et données » cite l'entrée
  [PALOMAR-2026-11-07-000003](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-07-000003)
  (source : `README.md`, lignes 427--430) et dit comment s'ouvrent les
  renvois.

- [ ] **5.c.1 — Lien figé.** Les liens Lean pointent vers `main`. L'article
  Lean lie une étiquette git (`article-lean-2026-10b`) « parce que le code
  continue d'évoluer ». Proposition : poser une étiquette au moment du dépôt
  et remplacer `blob/main` par `blob/<étiquette>` dans `\leanfile` (une ligne
  du préambule). Les trois fichiers sont-ils dans le dépôt Palomar
  `grothendieck-project-palomar` ? Non vérifié ici.
- [ ] **5.c.2 — Les renvois sans lien.** L'article cite aussi des pages sous
  la forme « n° 119, pp. 141--142 », sans lien. Les convertir en `\lot`
  demande de connaître le lot : à faire à la main si on le souhaite.
- [ ] **5.c.3 — Bibliographie.** L'entrée `banana` pointe vers
  `https://www.item.ens.fr/banana`, qui répond 404 le 10 novembre 2026.
  Remplacer par la page de l'ANR, qui répond :
  `https://anr.fr/Projet-ANR-23-CE27-0001`.

### 5.d Page de titre sans RHM

**Fait (`a8b797b`).** La variante est en `amsart` : ni `smfart`, ni `rhm.sty`,
ni le format 155 × 240 mm, ni mention de la revue. Le nom de la revue ne
subsiste que dans des entrées de bibliographie.

- [ ] **5.d.1 — ORCID.** Les articles déjà déposés portent
  `\thanks{ORCID 0009-0002-8304-0683.}` (`docs/bigon/article.tex`). À ajouter
  à l'en-tête sous `\hexagon`, avec l'adresse « Commutator, Paris, France »
  qu'ils utilisent, au lieu de « Chercheur indépendant, Paris » ?
- [ ] **5.d.2 — Date.** `\date{Octobre 2026}` (ligne 101) : à mettre à la date
  du dépôt.
- [ ] **5.d.3 — Langue.** Les dépôts précédents sont en anglais. Rien, sur la
  page « About », n'impose une langue ; l'article reste en français avec son
  *abstract*.

### 5.e Classification MSC 2020

**Fait (`a8b797b`) :** la variante porte `\subjclass[2020]{01A60; 01A70,
14-03, 18-03}`, c'est-à-dire les codes que l'article avait déjà, 01A60 en
tête. Tous les libellés ci-dessous ont été lus dans la classification de
zbMATH (api.zbmath.org, 10 novembre 2026).

| Code | Libellé MSC 2020 | Pourquoi |
|---|---|---|
| **01A60** | History of mathematics in the 20th century | principal (issue) |
| 01A70 | Biographies, obituaries, personalia, bibliographies | déjà présent |
| 14-03 | History of algebraic geometry | déjà présent |
| 18-03 | History of category theory | déjà présent |
| 55-03 | History of algebraic topology | « L'homotopie, de 1968 à 1991 » |
| 01A85 | Historiography | chronologie reconstruite, méthode |
| 18M05 | Monoidal categories, symmetric monoidal categories | lettres de 1974, thèse de Sính (Gr-catégories, catégories de Picard) |
| 18G45 | 2-groups, crossed modules, crossed complexes | *idem* |
| 14L15 | Group schemes | cote 27, SGA 3 |
| 17B45 | Lie algebras of linear algebraic groups | cote 27, exposé XIII (éléments réguliers) |
| 14F35 | Homotopy theory and fundamental groups in algebraic geometry | cote 29, SGA 1 en 1967 |
| 14E20 | Coverings in algebraic geometry | cote 29, ramification modérée |
| 18F10 | Grothendieck topologies and Grothendieck topoi | « Le topos change de fonction » |
| 18N40 | Homotopical algebra, Quillen model categories, derivators | cote 118, annexe B |
| 52C30 | Planar arrangements of lines and pseudolines | cote 80, annexe B |
| 14A15 | Schemes and morphisms | cote 37, EGA I 10.10.5, annexe B |
| 68V20 | Formalization of mathematics in connection with theorem provers | annexe Lean |

- [ ] **5.e.1 — Proposition courte** (les trois études de cas, un code
  chacune) :
  `\subjclass[2020]{01A60; 01A70, 14-03, 18-03, 55-03, 18M05, 14L15, 14F35}`
- [ ] **5.e.2 — Proposition longue** (avec l'annexe B) : ajouter `18N40,
  52C30, 14A15, 68V20`.

---

## 6. Historiographie : les travaux publiés du projet BANANA

**Ce qu'est BANANA.** « Bourbaki, nouvelles archives, nouvelles approches
(1934-1935 - 1970) », projet ANR-23-CE27-0001, 48 mois à partir de septembre
2023, porté par les Archives Henri Poincaré avec l'ITEM (page de l'ANR, lue le
10 novembre 2026). L'article le cite déjà en conclusion (ligne 417, entrée
`banana`), comme projet, sans aucun de ses travaux. Le 4 novembre, le commit
`894ee77` a retiré de l'article toute citation d'un des deux coordinateurs et
leurs noms de l'entrée `banana` ; le 5 octobre, la demande d'autorisation
avait été adressée à ce projet (#50). Citer leurs travaux est donc une
décision de Michel, pas une simple mise à jour de la bibliographie.

**Ce qui est publié et vérifié.** Le portail HAL de l'ANR ne rattache au projet
qu'une communication (halshs-05434791, 2025). Une publication est sûre :

```bibtex
@article{eckes2025,
  author  = {Eckes, Christophe},
  title   = {Les archives {Bourbaki} sous l'angle de la critique génétique. {L}'exemple des premières rédactions {Bourbaki} sur les algèbres de {Lie}},
  journal = {Genesis},
  volume  = {60},
  pages   = {31--43},
  year    = {2025},
  doi     = {10.4000/13xlu},
}
```

Vérifié le 10 novembre 2026 : Crossref (titre, sous-titre, volume 60, pages
31-43, 2025) ; le DOI se résout vers journals.openedition.org/genesis/10581
(mis en ligne le 13 mai 2026) ; la notice de l'auteur y nomme le projet
BANANA. L'article reconstitue la genèse du premier chapitre du livre sur les
groupes et algèbres de Lie à partir de huit rédactions (n° 125 à 316), de la
*Tribu* et des comptes rendus de congrès : c'est, sur un autre chapitre, la
méthode que la section « Le travail collectif : Bourbaki » applique aux
rédactions de Grothendieck.

Deux références voisines, vérifiées par leur DOI dans Crossref mais dont le
rattachement au projet n'est pas établi :

- Paola Cantù et Frédéric Patras, « Les structures bourbakistes : objets ou
  concepts épistémiques ? », *Philosophia Scientiæ* 27 (2), 2023, p. 233-259,
  doi:10.4000/philosophiascientiae.4014. (Le titre est celui de Crossref ;
  l'appel de la revue le cite avec une variante.)
- Ralf Krömer, « Duality à la Bourbaki », dans R. Krömer et E. Haffner (dir.),
  *Duality in 19th and 20th Century Mathematical Thinking*, Birkhäuser, 2024,
  p. 659-716, doi:10.1007/978-3-031-59797-8_14.

À paraître, donc non citable aujourd'hui : le cahier thématique « Approches
génétiques des *Éléments de mathématique* de Bourbaki », *Philosophia
Scientiæ* 31 (2), annoncé pour juin 2027 (appel lu le 10 novembre 2026).

- [ ] **6.a — Citer Eckes 2025 dans « Le travail collectif : Bourbaki »**
  (ligne 253), à la fin de la phrase d'historiographie, après « […] et Krömer
  la place des catégories dans les débats du groupe au cours des années 1950
  [Krömer 2006] » :
  > ; Eckes a reconstitué, à partir des rédactions successives et de la
  > *Tribu*, la genèse du premier chapitre sur les algèbres de Lie
  > [`\citealp{eckes2025}`].

  L'entrée est à ajouter à `article.bib` et la clé à la liste `\nocite`
  (ligne 92).
- [ ] **6.b — Dans la conclusion** (ligne 417, réservée à Michel), la phrase
  sur BANANA pourrait renvoyer au même article plutôt qu'à la seule page du
  projet.
- [ ] **6.c — Krömer 2024 et Cantù--Patras 2023 :** à lire avant de les citer
  (non lus ici ; seules leurs notices ont été vérifiées).

---

## 7. Lecteur humain

Rien n'a été fait : c'est à Michel.

---

## Ce que seul Michel peut faire

1. Réécrire l'introduction, la discussion et la conclusion ; les phrases que
   les autres changements rendent inexactes sont listées en 1.d, 4.a, 4.b,
   4.g et 4.h.
2. Confirmer chaque réponse de tiers de la section 3, et dire le type
   d'abonnement et l'état du réglage d'entraînement (3.6).
3. Décider du sort des citations de la BnF et de Quillen avant un dépôt
   irrévocable (3.2, 3.4, 3.7).
4. Compiler (5.a), choisir les codes MSC (5.e), la date, l'ORCID, la licence.
5. Décider de citer ou non les travaux du projet BANANA (6).
6. Trouver le lecteur (7).
