#!/usr/bin/env node
/**
 * La figure de l'article pour la RHM : la carte des mathématiques du fonds.
 *
 *   node docs/rhm/figures.mjs
 *
 * Redessine en TikZ la carte que le site montre sous « Maps »
 * (src/content/math-map.json, `npm run fonds-maps`) : trente sujets, placés
 * une fois pour toutes par une disposition de forces à graine fixe, reliés
 * quand ils partagent des dossiers plus souvent que le hasard ne le voudrait
 * (force d'association ≥ 1). Pour un article d'histoire, la couleur dit la
 * datation moyenne des dossiers d'un sujet — milieux de fourchettes
 * d'inventaire, donc un ordre de grandeur — et non la communauté.
 */
import { readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';

const here = import.meta.dirname;
const root = resolve(here, '../..');
const map = JSON.parse(readFileSync(resolve(root, 'src/content/math-map.json'), 'utf8'));

const FR = {
  'Topoi and sites': 'Topos et sites',
  'Stacks, gerbes and fibred categories': 'Champs et gerbes',
  'Homotopy theory and test categories': 'Homotopie',
  'Categories and functors': 'Catégories',
  'Tensor categories and Tannakian duality': 'Catégories tannakiennes',
  Motives: 'Motifs',
  'Algebraic cycles and standard conjectures': 'Cycles algébriques',
  'Hodge theory': 'Théorie de Hodge',
  'Weil conjectures and zeta functions': 'Conjectures de Weil',
  'Étale and ℓ-adic cohomology': 'Cohomologie étale',
  'Crystalline and de Rham cohomology': 'Cohomologie cristalline',
  'p-divisible groups and formal groups': 'Groupes $p$-divisibles',
  'Abelian varieties and Picard schemes': 'Variétés abéliennes',
  'Group schemes and algebraic groups': 'Schémas en groupes',
  Descent: 'Descente',
  'Fundamental groups and Galois theory': 'Groupe fondamental',
  'Anabelian geometry and dessins': 'Géométrie anabélienne',
  'Duality theory': 'Dualité',
  'K-theory, Chern classes and Riemann–Roch': 'K-théorie, Riemann--Roch',
  'Commutative algebra': 'Algèbre commutative',
  'Functional analysis': 'Analyse fonctionnelle',
  'Combinatorial topology, surfaces and maps': 'Surfaces et cartes',
  'Polyhedra and convex geometry': 'Polyèdres',
  'Tame topology and stratified spaces': 'Topologie modérée',
  'Number theory and arithmetic': 'Arithmétique',
  'Complex and analytic geometry': 'Géométrie analytique',
  'Universal algebra and theories': 'Algèbre universelle',
  'Formal geometry, moduli and representability': 'Géométrie formelle, modules',
  'Riemann surfaces, uniformisation and moduli of curves': 'Surfaces de Riemann',
  'Games and combinatorics': 'Jeux',
};

// Rampe ordinale d'une seule teinte, du clair (tôt) au foncé (tard) — la
// même que la vue « dating » de la carte sur le site.
const BINS = [
  { max: 1967, label: '1966--1967', rgb: '151,175,225' },
  { max: 1969, label: '1968--1969', rgb: '107,138,208' },
  { max: 1971, label: '1970--1971', rgb: '74,107,189' },
  { max: 1974, label: '1972--1974', rgb: '46,68,127' },
  { max: 9999, label: '1975 et après', rgb: '34,49,84' },
];
const bin = (y) => BINS.findIndex((b) => y <= b.max);

const W = 14; // cm
const s = W / map.width;
const X = (x) => (x * s).toFixed(2);
const Y = (y) => ((map.height - y) * s).toFixed(2);
const maxW = Math.max(...map.links.map((l) => l.w));

const colours = BINS.map((b, i) => `\\definecolor{dat${i}}{RGB}{${b.rgb}}`).join('\n');
const links = map.links
  .map((l) => {
    const a = map.nodes[l.s];
    const b = map.nodes[l.t];
    return `\\draw[black!18,line width=${(0.25 + (1.4 * l.w) / maxW).toFixed(2)}pt] (${X(a.x)},${Y(a.y)}) -- (${X(b.x)},${Y(b.y)});`;
  })
  .join('\n');
const nodes = map.nodes
  .map((n) => {
    const r = (0.07 + 0.028 * Math.sqrt(n.folders.length)).toFixed(3);
    return `\\fill[dat${bin(n.year)},draw=white,line width=0.6pt] (${X(n.x)},${Y(n.y)}) circle (${r});`;
  })
  .join('\n');
// Étiquette au-dessus du disque par défaut, sur le bord droit à gauche ; les
// autres placements défont les chevauchements que la disposition laisse.
const PLACE = {
  'Commutative algebra': 'below',
  'Functional analysis': 'below',
  'Topoi and sites': 'left',
  'Group schemes and algebraic groups': 'right',
  'Weil conjectures and zeta functions': 'below',
  'Abelian varieties and Picard schemes': 'left',
  'Homotopy theory and test categories': 'left',
  'Categories and functors': 'left',
};
const labels = map.nodes
  .map((n) => {
    const r = 0.07 + 0.028 * Math.sqrt(n.folders.length);
    const where = PLACE[n.term] ?? (n.x > 860 ? 'left' : 'above');
    const x = n.x * s;
    const y = (map.height - n.y) * s;
    const [anchor, lx, ly] = {
      above: ['south', x, y + r + 0.02],
      below: ['north', x, y - r - 0.02],
      left: ['east', x - r - 0.05, y],
      right: ['west', x + r + 0.05, y],
    }[where];
    return `\\node[font=\\tiny,text=black!80,anchor=${anchor},inner sep=1pt,fill=white,fill opacity=0.75,text opacity=1] at (${lx.toFixed(2)},${ly.toFixed(2)}) {${FR[n.term] ?? n.short}};`;
  })
  .join('\n');
const legend = BINS.map(
  (b, i) => `\\fill[dat${i}] (${(i * 2.5).toFixed(2)},-0.55) circle (0.09); \\node[font=\\scriptsize,anchor=west] at (${(i * 2.5 + 0.15).toFixed(2)},-0.55) {${b.label}};`,
).join('\n');

writeFileSync(
  resolve(here, 'fig-carte.tex'),
  `% Générée par docs/rhm/figures.mjs à partir de src/content/math-map.json (${map.built}) — ne pas éditer à la main.
\\begin{figure}[htbp]\\centering
${colours}
\\begin{tikzpicture}
${links}
${nodes}
${labels}
${legend}
\\end{tikzpicture}
\\caption{Carte des mathématiques du fonds : les trente sujets sous lesquels se rangent les mots-clés des ${map.coverage.folders} lectures modernisées (${map.coverage.mapped} des ${map.coverage.keywords} mots-clés sont rattachés). Deux sujets sont proches quand ils partagent des cotes, et reliés quand ils en partagent plus que ne le voudrait le hasard (force d'association au moins égale à 1) ; un disque plus grand, plus de cotes. La couleur donne la datation moyenne des cotes du sujet, calculée sur les milieux des fourchettes de l'inventaire : un ordre de grandeur, non une date. Les mots-clés sont ceux des lectures modernisées, une interprétation, et la disposition est calculée une fois, à graine fixe. D'après \\texttt{src/content/math-map.json} (${map.built}), comme la carte du site, onglet « Maps ».}\\label{fig:carte}
\\end{figure}
`,
);
process.stdout.write(`fig-carte.tex: ${map.nodes.length} sujets, ${map.links.length} liens\n`);
