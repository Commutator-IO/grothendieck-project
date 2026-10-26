/**
 * The 71 mathematical findings that were found in print (FindingsChart,
 * « Found in the literature »): the folder's dating against the year of the
 * printed source that matches it. Built by hand on 2026-10-26 from the
 * `settle` and `literature` fields of src/content/findings.ts and the
 * inventory's datings (src/content/catalogue.ts).
 *
 * `kind` says how the two dates stand: `later`, the source was printed after
 * the end of the folder's dating; `earlier`, before its start; `own`, the
 * source is his own printed work or written from his unpublished results
 * (SGA, the Montréal notes, Murre 1965); `circle`, a student's or close
 * colleague's text (a thesis he directed, an exposé of his seminars);
 * `concurrent`, printed within the folder's dating; `unclear`, a textbook
 * statement with no single source. None of this is a claim of priority: the
 * datings are the inventory's, often inferred, and `from`/`to` are the bounds
 * of that dating (`open` when the inventory gives only a lower bound).
 */
export type RediscoveryKind = 'later' | 'earlier' | 'own' | 'circle' | 'concurrent' | 'unclear';

export interface Rediscovery {
  id: string;
  cote: string;
  from: number;
  to: number;
  open?: boolean;
  pub: number;
  source: string;
  kind: RediscoveryKind;
}

export const REDISCOVERIES: Rediscovery[] = [
  { id: '161-3-fields-partition', cote: '161-3', from: 1963, to: 1973, pub: 1972, source: 'Hakim, Topos annelés et schémas relatifs', kind: 'circle' },
  { id: '151-hypercovering-any-index-category', cote: '151', from: 1982, to: 1991, open: true, pub: 2012, source: 'Shulman, Exact completions and small sheaves', kind: 'later' },
  { id: '115-wheel-eleven-curryings', cote: '115', from: 1982, to: 1991, open: true, pub: 1973, source: 'Bénabou, Les distributeurs', kind: 'earlier' },
  { id: '115-isbell-reflexivity-left-open', cote: '115', from: 1982, to: 1991, open: true, pub: 1966, source: 'Isbell, Structure of categories', kind: 'earlier' },
  { id: '115-isbell-envelope-self-dual', cote: '115', from: 1982, to: 1991, open: true, pub: 1966, source: 'Isbell envelope', kind: 'earlier' },
  { id: '19-faithful-transportable-is-forgetful', cote: '19', from: 1958, to: 1973, pub: 1961, source: 'SGA 1, VI (fibred categories)', kind: 'own' },
  { id: '135-sinh-theorem-classification', cote: '135', from: 1974, to: 1975, pub: 1975, source: 'Sinh, Gr-catégories (thesis)', kind: 'circle' },
  { id: '161-1-giraud-recognition-half-page', cote: '161-1', from: 1963, to: 1973, pub: 1963, source: 'Giraud, Analysis situs (Bourbaki 256)', kind: 'circle' },
  { id: '161-1-epsilon-sign-obstruction', cote: '161-1', from: 1963, to: 1973, pub: 1973, source: 'Deligne, SGA 4 XVIII (Picard categories)', kind: 'circle' },
  { id: '161-1-idempotent-adjunction-decomposition', cote: '161-1', from: 1963, to: 1973, pub: 1994, source: 'Borceux, Handbook (standard)', kind: 'unclear' },
  { id: '29-fundamental-group-scheme-via-torsors', cote: '29', from: 1959, to: 1969, pub: 1976, source: 'Nori, fundamental group scheme', kind: 'later' },
  { id: '29-kummer-gerbe-root-stack', cote: '29', from: 1959, to: 1969, pub: 2007, source: 'Cadman; Abramovich–Graber–Vistoli, root stacks', kind: 'later' },
  { id: '54-universal-extension-de-rham-dual', cote: '54', from: 1971, to: 1975, open: true, pub: 1974, source: 'Mazur–Messing, Universal extensions', kind: 'concurrent' },
  { id: '54-frobenius-kernels-orthogonal', cote: '54', from: 1971, to: 1975, open: true, pub: 1969, source: 'Oda; Mumford, Abelian varieties', kind: 'earlier' },
  { id: '161-2-vn-regular-cartesian-presheaf-classifier', cote: '161-2', from: 1963, to: 1973, pub: 2018, source: 'Berni–Mariano (C∞ case)', kind: 'later' },
  { id: '31-phi-specialisation-criterion', cote: '31', from: 1963, to: 1973, pub: 1973, source: 'Artin, SGA 4 X, Th. 4.1', kind: 'circle' },
  { id: '16-page-21-not-gorenstein', cote: '16', from: 1966, to: 1967, pub: 1980, source: 'Stanley; Artinian Gorenstein, strong Lefschetz', kind: 'later' },
  { id: '14-nakai-euler-characteristic-criterion', cote: '14', from: 1965, to: 1971, pub: 1974, source: 'Elkik on Nakai (after Nakai 1963, Kleiman)', kind: 'concurrent' },
  { id: '116-presheaf-gluing-continuous-gluing-functor', cote: '116', from: 1981, to: 1991, open: true, pub: 1972, source: 'SGA 4 IV, Ex. 9.5.9', kind: 'own' },
  { id: '125-cd-complement-formal-comparison', cote: '125', from: 1960, to: 1970, pub: 1970, source: 'Hartshorne, Ample subvarieties', kind: 'concurrent' },
  { id: '121-cell-decomposition-open-quotient', cote: '121', from: 1974, to: 1974, pub: 2017, source: 'Tamaki; Waas–Woolf–Yokura 2024', kind: 'later' },
  { id: '34-wild-inertia-outer-pi1', cote: '34', from: 1967, to: 1973, pub: 2000, source: 'Kisin, Prime to p fundamental groups', kind: 'later' },
  { id: '57-conic-nonseparated-pic', cote: '57', from: 1962, to: 1968, pub: 2005, source: 'Kleiman, The Picard scheme (FGA explained)', kind: 'later' },
  { id: '57-cone-completion-class-group', cote: '57', from: 1962, to: 1968, pub: 1968, source: 'Danilov, class group of a completed ring', kind: 'concurrent' },
  { id: '57-ns-p-divisibility-generization', cote: '57', from: 1962, to: 1968, pub: 2012, source: 'Maulik–Poonen, Néron–Severi under specialization', kind: 'later' },
  { id: '7-strat-invariance-problem', cote: '7', from: 1967, to: 1971, pub: 1968, source: 'Grothendieck, Crystals (Dix exposés)', kind: 'own' },
  { id: '7-noninfinitesimal-site', cote: '7', from: 1967, to: 1971, pub: 1984, source: 'Ogus, convergent site', kind: 'later' },
  { id: '37-smooth-base-change-stacks', cote: '37', from: 1967, to: 1971, pub: 1971, source: 'Giraud, Cohomologie non abélienne', kind: 'circle' },
  { id: '126-fpqc-generated-topology', cote: '126', from: 1960, to: 1970, pub: 1964, source: 'fpqc topology (SGA 3; Stacks)', kind: 'own' },
  { id: '40-operator-criterion', cote: '40', from: 1960, to: 1970, pub: 1969, source: 'Chase–Sweedler, Hopf–Galois', kind: 'concurrent' },
  { id: '64-gl2-z4-combinatorial-model', cote: '64', from: 1980, to: 1982, pub: 1980, source: 'GL₂(ℤ/4) (group tables)', kind: 'unclear' },
  { id: '129-tate-object-one-index', cote: '129', from: 1970, to: 1970, pub: 1974, source: 'Grothendieck, Groupes de Barsotti–Tate (Montréal)', kind: 'own' },
  { id: '129-colie-truncated-bt-package', cote: '129', from: 1970, to: 1970, pub: 1974, source: 'Montréal notes; Illusie 1985', kind: 'own' },
  { id: '132-taylor-obstruction', cote: '132', from: 1974, to: 1974, pub: 1954, source: 'Taylor’s obstruction (Brown–Mucuk 1994)', kind: 'earlier' },
  { id: '132-teichmuller-boundary-sequence', cote: '132', from: 1974, to: 1974, pub: 1974, source: 'capping sequence (Birman; Farb–Margalit)', kind: 'concurrent' },
  { id: '132-fibre-product-pi2-defect', cote: '132', from: 1974, to: 1974, pub: 1983, source: 'Brown–Heath–Kamps, Mayer–Vietoris', kind: 'later' },
  { id: '156-1-branching-without-branch-point', cote: '156-1', from: 1986, to: 1986, pub: 1957, source: 'Haefliger–Reeb, non-Hausdorff 1-manifolds', kind: 'earlier' },
  { id: '156-3-order-from-betweenness', cote: '156-3', from: 1986, to: 1986, pub: 2020, source: 'Courcelle, Betweenness of partial orders', kind: 'later' },
  { id: '156-4-figures-as-configurations', cote: '156-4', from: 1986, to: 1986, pub: 1981, source: 'Nielsen–Plotkin–Winskel, event structures', kind: 'earlier' },
  { id: '156-9-disposition-correspondences', cote: '156-9', from: 1986, to: 1986, pub: 1999, source: 'bonds of formal concept analysis (Ganter–Wille)', kind: 'later' },
  { id: '144-triangulation-weighting-obstruction', cote: '144', from: 1981, to: 1983, pub: 1977, source: 'Fisk, Geometric coloring theory', kind: 'earlier' },
  { id: '146-variant-pi1-trinion', cote: '146', from: 1978, to: 1988, open: true, pub: 2000, source: 'Bakalov–Kirillov, Lego–Teichmüller game', kind: 'later' },
  { id: '159-no-reduction-monodromy-dense', cote: '159', from: 1990, to: 1991, pub: 1967, source: 'Gunning; Hejhal (projective structures)', kind: 'earlier' },
  { id: '159-formal-rigidity-quadratic-torsor', cote: '159', from: 1990, to: 1991, pub: 1967, source: 'Gunning, projective structures', kind: 'earlier' },
  { id: '159-monodromy-injectivity-question', cote: '159', from: 1990, to: 1991, pub: 1975, source: 'Hejhal; Kra (holonomy injective)', kind: 'earlier' },
  { id: '160-ga-subgroups-additive-kernels', cote: '160', from: 1990, to: 1991, pub: 2021, source: 'Brion, Lemma 4.2', kind: 'later' },
  { id: '160-dickson-geometric-route', cote: '160', from: 1990, to: 1991, pub: 1911, source: 'Dickson invariants (Wilkerson 1983)', kind: 'earlier' },
  { id: '2-chern-ring-gamma-comparison', cote: '2', from: 1957, to: 1957, pub: 2020, source: 'Mackall, universal additive Chern classes', kind: 'later' },
  { id: '28-enriques-systems-classification', cote: '28', from: 1970, to: 1970, pub: 1970, source: 'Demazure, sous-groupes du groupe de Cremona', kind: 'circle' },
  { id: '28-torus-extension-stable-rationality', cote: '28', from: 1970, to: 1970, pub: 1970, source: 'Demazure 1970', kind: 'circle' },
  { id: '105-interval-anodyne-generators', cote: '105', from: 1982, to: 1991, open: true, pub: 2002, source: 'Cisinski, anodyne extensions', kind: 'later' },
  { id: '117-adjunction-equivalence-criterion', cote: '117', from: 1983, to: 1983, pub: 2015, source: 'Gurski–Johnson–Osorno, Th. 1.11', kind: 'later' },
  { id: '13-double-niveau-de-rham-betti', cote: '13', from: 1965, to: 1965, pub: 1966, source: 'Grothendieck, period conjecture', kind: 'own' },
  { id: '21-depth-sheaves-of-sets-pointwise', cote: '21', from: 1963, to: 1967, pub: 1962, source: 'SGA 2, XIV', kind: 'own' },
  { id: '42-sections-limit-of-local-rings', cote: '42', from: 1960, to: 1970, pub: 1966, source: 'Ferrand, CRAS 262', kind: 'concurrent' },
  { id: '46-homeomorphism-affine', cote: '46', from: 1961, to: 1973, pub: 2010, source: 'Stacks 04DE (standard)', kind: 'unclear' },
  { id: '52-hyperelliptic-unique-isomorphism', cote: '52', from: 1973, to: 1973, pub: 2021, source: 'Landesman, Torelli on the hyperelliptic locus', kind: 'later' },
  { id: '88-standard-maps-quotients', cote: '88', from: 1976, to: 1986, open: true, pub: 1978, source: 'Jones–Singerman, maps on surfaces', kind: 'concurrent' },
  { id: '107-hot-sequential-colimits', cote: '107', from: 1973, to: 1983, open: true, pub: 1962, source: 'Milnor, lim¹ sequence', kind: 'earlier' },
  { id: '118-strong-saturation', cote: '118', from: 1983, to: 1991, open: true, pub: 2006, source: 'Cisinski, Astérisque 308', kind: 'later' },
  { id: '131-unramified-and-etale-corollaries', cote: '131', from: 1971, to: 1971, pub: 1965, source: 'Murre, after Grothendieck’s unpublished results', kind: 'own' },
  { id: '90-saturated-subcoalgebras', cote: '90', from: 1964, to: 1974, open: true, pub: 1968, source: 'Serre, groupes de Grothendieck des schémas en groupes', kind: 'concurrent' },
  { id: '97-borel-cartan-simplicial-forms', cote: '97', from: 1966, to: 1966, pub: 1972, source: 'Shulman; Bott 1973', kind: 'later' },
  { id: '78-parabola-p-gon', cote: '78', from: 1977, to: 1987, open: true, pub: 1974, source: 'Korchmáros', kind: 'earlier' },
  { id: '47-relative-fourier-inversion', cote: '47', from: 1961, to: 1973, pub: 1987, source: 'Mukai, Fourier functor', kind: 'later' },
  { id: '47-cup-to-pontrjagin-sign-kleiman', cote: '47', from: 1961, to: 1973, pub: 1983, source: 'Beauville, transformation de Fourier', kind: 'later' },
  { id: '77-two-regular-classification-matched', cote: '77', from: 1977, to: 1987, open: true, pub: 2016, source: 'Voight, quadratic rings', kind: 'later' },
  { id: '77-so-even-rank-smooth-connected-matched', cote: '77', from: 1977, to: 1987, open: true, pub: 2014, source: 'Conrad, Reductive group schemes, App. C', kind: 'later' },
  { id: '83-two-generator-azumaya-criterion', cote: '83', from: 1982, to: 1986, pub: 2011, source: 'Voight, quaternion rings', kind: 'later' },
  { id: '91-local-functor-right-adjoint', cote: '91', from: 1964, to: 1970, pub: 2018, source: 'Bertapelle–González-Avilés, Greenberg functor', kind: 'later' },
  { id: '91-constructible-ring-Acons', cote: '91', from: 1964, to: 1970, pub: 2015, source: 'Bhatt–Scholze, w-localisation', kind: 'later' },
];
