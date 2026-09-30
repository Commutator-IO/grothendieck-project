# Dater, reprendre, déplacer

Un article en français pour la *Revue d'histoire des mathématiques* (SMF) :
une lecture historique et conceptuelle des notes de travail du fonds
Grothendieck, fondée sur les transcriptions du dépôt. Suivi dans #34.

- `article.tex` — l'article, composé avec la classe de la SMF `smfart` et le
  complément `rhm.sty` de la revue, sur la page de la revue imprimée
  (155 × 240 mm, mesurée sur un article publié), la colonne de 11,2 × 17,7 cm
  que fixe `rhm.sty` centrée dessus. `article.bib` est sa bibliographie, pour
  `rhmunsrtnat.bst` ; les citations sont entre crochets, comme dans la revue,
  et chacune est un lien vers son entrée. Les fichiers de la SMF
  (`smfart.cls`, `rhm.sty`, `smfthm.sty`, `smfhyperref.sty`, `smfenum.sty`,
  `rhmunsrtnat.bst`) sont copiés ici tels qu'elle les distribue.
  `article.pdf` est compilé et versionné
  (`cd docs/rhm && tectonic -X compile article.tex`, qui lance BibTeX).

## Les consignes de la revue

Lues le 26 septembre 2026 sur
[smf.emath.fr](https://smf.emath.fr/publications/instructions-pour-les-auteurs) :
article en français ou en anglais, composé en LaTeX avec la classe `smfart`
(et le complément RHM) ou toute classe standard ; à l'acceptation, les sources,
un fichier BibTeX, les titres, résumés et mots-clés en français et en anglais,
les classifications MSC 2010. Soumission par
[EditFlow](https://ef.msp.org/submit_new.php?j=rhm). La revue publie aussi des
« documents inédits commentés ». Sa politique sur l'usage de l'IA reste à
vérifier ; l'article porte une déclaration.

## Avant soumission

- Collationner chaque citation et chaque date sur le fac-similé (annexe B de
  l'article ; les vérifications qui ne demandent qu'un lecteur de l'écriture
  sont dans #35).
- Refaire à la main les comparaisons avec l'imprimé que l'article signale
  comme faites par machine (cote 27 et SGA 3 XIII ; cote 29 et Grothendieck–Murre 1971).
- Vérifier les références marquées comme telles dans l'annexe B, et le style
  bibliographique de la revue (`rhmunsrtnat`).
- Corriger dans le dépôt les deux lectures modernisées que l'article écarte
  (114 : proposition 4 réfutée présentée comme vraie ; 47 : antériorité sur
  Mukai que la datation ne permet pas) et celle de 27, qui dit encore son
  tapuscrit publié.
