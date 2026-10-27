// The 43 boxes of the BnF's Grothendieck fonds (NAF 29093), with the number of leaves each notice
// gives (« 1 boîte : N feuillets »). Read from https://archivesetmanuscrits.bnf.fr/ark:/12148/cc126317b on 2026-10-27.
// `maths`: box (3) is a mathematical text; (40), (42), (43) hold some mathematics among other notes.

export interface BnfBox {
  box: number;
  title: string;
  years: string;
  leaves: number;
  maths?: 'whole' | 'part';
}

export const BNF_BOXES: BnfBox[] = [
  { box: 1, title: 'La Clef des Songes, ch. I–VI', years: '1987', leaves: 532 },
  { box: 2, title: 'La Clef des Songes, ch. VII « Mutants »', years: '1987–1988', leaves: 515 },
  { box: 3, title: 'Géométrie élémentaire schématique', years: '1992', leaves: 581, maths: 'whole' },
  { box: 4, title: 'Structures de la Psyché, livre I, sections 1–6', years: '1992', leaves: 672 },
  { box: 5, title: 'Structures de la Psyché, sections 7.1–7.4', years: '1992–1993', leaves: 578 },
  { box: 6, title: 'Structures de la Psyché, 7.5–7.6 et livre II', years: '1993', leaves: 619 },
  { box: 7, title: 'Psyché et Structure', years: '1992–1993', leaves: 361 },
  { box: 8, title: 'Le Problème du Mal I', years: '1993', leaves: 562 },
  { box: 9, title: 'Le Problème du Mal II, ch. VIII–XII', years: '1993', leaves: 419 },
  { box: 10, title: 'Le Problème du Mal II, ch. XIII–XVI', years: '1993', leaves: 364 },
  { box: 11, title: 'Le Problème du Mal III (1)', years: '1993', leaves: 413 },
  { box: 12, title: 'Le Problème du Mal III (2)', years: '1993', leaves: 451 },
  { box: 13, title: 'Le Problème du Mal IV, ch. I–V', years: '1993', leaves: 361 },
  { box: 14, title: 'Esprit et Matière, sections A–C', years: '1992–1993', leaves: 424 },
  { box: 15, title: 'Esprit et Matière, section D', years: '1993–1994', leaves: 678 },
  { box: 16, title: 'Le Problème du Mal V, ch. VI–X', years: '1993–1994', leaves: 420 },
  { box: 17, title: 'Le Problème du Mal V, ch. XI–XV', years: '1994', leaves: 485 },
  { box: 18, title: 'Le Problème du Mal V, ch. XVI–XX', years: '1994', leaves: 380 },
  { box: 19, title: 'Le Problème du Mal VI, ch. I–VII', years: '1994', leaves: 559 },
  { box: 20, title: 'Le Problème du Mal VI, ch. VIII–XIV', years: '1994', leaves: 649 },
  { box: 21, title: 'Le Problème du Mal VI, ch. XV–XX', years: '1994', leaves: 668 },
  { box: 22, title: 'Le Problème du Mal VI, ch. XXI–XXVII', years: '1994', leaves: 550 },
  { box: 23, title: 'Le Problème du Mal VI, ch. XXVIII–XXXII', years: '1994', leaves: 637 },
  { box: 24, title: 'Le Problème du Mal VI, ch. XXXIII–XXXVI', years: '1994', leaves: 417 },
  { box: 25, title: 'Le Problème du Mal VII, ch. I–VI', years: '1994–1995', leaves: 628 },
  { box: 26, title: 'Le Problème du Mal VII, ch. VII–XI', years: '1995', leaves: 611 },
  { box: 27, title: 'Le Problème du Mal VII, ch. XII–XVII', years: '1995', leaves: 761 },
  { box: 28, title: 'Le Problème du Mal VII, ch. XVIII–XXIV', years: '1995', leaves: 657 },
  { box: 29, title: 'Le Problème du Mal VII, ch. XXV–XXXI', years: '1995', leaves: 617 },
  { box: 30, title: 'Le Problème du Mal VIII, ch. I–VIII', years: '1995–1996', leaves: 691 },
  { box: 31, title: 'Le Problème du Mal VIII, ch. IX–XV', years: '1996', leaves: 599 },
  { box: 32, title: 'Le Problème du Mal IX, ch. I–VI', years: '1996', leaves: 428 },
  { box: 33, title: 'Le Problème du Mal IX, ch. VII–XIII', years: '1996', leaves: 650 },
  { box: 34, title: 'Esprit et Matière, section E', years: '1996', leaves: 523 },
  { box: 35, title: 'Le Problème du Mal X, ch. IX–XIII', years: '1996–1997', leaves: 427 },
  { box: 36, title: 'Le Problème du Mal X, ch. XIV–XX', years: '1997', leaves: 395 },
  { box: 37, title: 'Le Problème du Mal XI–XII, textes préparatoires', years: '1997–1998', leaves: 360 },
  { box: 38, title: 'Le Problème du Mal, tables des matières I–IX', years: '', leaves: 493 },
  { box: 39, title: 'Le Problème du Mal, tables X–XI, notes-résumés XI–XII', years: '', leaves: 622 },
  { box: 40, title: 'Gribouillis I', years: '1997–1998', leaves: 438, maths: 'part' },
  { box: 41, title: 'Réflexions sur la Création, I', years: '1998–1999', leaves: 490 },
  { box: 42, title: 'Gribouillis II', years: '1998–1999', leaves: 527, maths: 'part' },
  {
    box: 43,
    title: 'Notes et gribouillis, Trialité, Géographie combinatoire',
    years: '1991–1997',
    leaves: 283,
    maths: 'part',
  },
];
