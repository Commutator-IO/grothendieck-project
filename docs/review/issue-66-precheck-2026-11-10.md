# Issue 66 — machine pre-check on the facsimile (10 November 2026)

Issue #66 asks for a reader with the facsimile open. This file is not that check: it is a pre-check
made on the Montpellier facsimiles to narrow what the reader has to look at. Nothing here was applied
to `src/content/dated-leaves.json` or to a transcription, and no page is marked « checked on the
facsimile ». Each verdict says what was seen on the page and how sure it is.

- **The « hand » field of the dated-leaf records**: 242 of 243 records looked at (9 of kind « paper »
  are not dates on a leaf; 157-5 p. 2 not done, its PDF is 272 MB). 223 agree, 14 disagree with a
  proposed value, 4 cannot tell, 1 date not found on its page. Parts A (folders 5 to 144) and B
  (folders 134-1 to 162-5) below.
- **Spot checks of the skipped pages**: 61 pages in 36 folders, from a population of 1,928 pages without
  a `\page` marker in 140 folders (listed in `issue-66-skipped-population-2026-11-10.md`). 51 agree,
  6 carry something of his that the transcription does not, 4 cannot tell. Part C below.
- **Folder 12 against the other transcription**: in progress, reported separately.

Two rules of the `hand` field have to be settled before the disagreements are applied: whether it
records the means by which the date stands on the leaf (a typed date on his own typed letter is then
`typed`, as in 134-4 and 134-8, not `his`, as in 5 p. 49), and whether a correspondent's typed date
is `typed` (37 p. 95, 78 p. 93, 100 p. 29, 119 p. 282) or `other` (29 pp. 2 and 78).

## Part A — « hand », folders 5 to 144


A machine pre-check on the Montpellier facsimiles (`https://grothendieck.umontpellier.fr/<cote>.pdf`, PDF page = archive page + 1), not a human reading. Pages were rendered at 100 dpi, with a 200–250 dpi crop of the date where the first look was not enough. Nothing in `src/content/dated-leaves.json` or in the transcriptions was changed.

How the values are understood here (from `$why`, the records and `src/TimelinePage.tsx`): `his` — the date is written by Grothendieck's hand (also when the leaf itself is typed and only the date is handwritten); `typed` — the date is struck on a typewriter, whoever typed; `machine` — the date was put on the paper by a device or a press: the banner of a computer listing, a rubber date stamp, a postmark, print (the timeline draws these hollow: they date the paper, not the writing); `other` — the date is in another person's hand; `unknown` — not settled. The nine records of kind « paper » (Bourbaki rédactions on the backs) are not dates on a leaf and were skipped.

Confidence: sure / likely / cannot tell.

### Folder 5
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 49 | 10.12.1965 | his | ink, by hand, top right of a typed carbon « Cher Deligne » | agree | likely | numerals of the same build as his dated leaves of 1966 (folder 7); the letter itself is typed |

### Folder 6
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | Pise, Mai 1966 | his | ink, by hand, top right of the typed « Cher John », same ink as the hand corrections in the text | agree | likely | |

### Folder 7
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 2 (two records) | Juillet-Août 1967 | his | pencil, by hand, top right, above a leaf in his ink | agree | likely | lighter instrument than the text; letter forms are his |
| 20 (two records) | Nov. Déc. 1966 | his | pencil, large upright letters, top right; last digit overwritten in red | agree | likely | larger and more upright than the text below, so probably added later; nothing points to another person |
| 35 | 15.11.66 | his | ink, top right, same blue ink as the text; first digit overwritten | agree | sure | |
| 56 | 6.12.1966 | his | ink, top right, set off by a corner stroke, same ink as the text | agree | sure | |

### Folder 12
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 116 | 27 March 1968 | typed | typewriter: « Le 27 Mars 1968 / 17H 45 », note to « Monsieur GROTHENDIECK », signed by hand in blue by someone else | agree | sure | the leaf has « Le 27 Mars 1968 » in French; `written` gives it in English |
| 118 | 20.3.68 | machine | rubber stamp « 20. 3. 68  1. Korrektur » top right of the printed LNM 41 cover | agree | sure | |

### Folder 13
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 13 | Algiers Nov. 1, 1965 | unknown | pencil, by hand, top right, same pencil and same hand as the letter « Dear Mumford » below it and as the P.S. on p. 15 | disagree → his | likely | the hand of pp. 13–15 is his (compare the cover p. 1 « Groupes de Hodge / Lettre à Mumford » and the P.S. p. 15); this is his own draft or copy of the letter |

### Folder 14
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 43 | 27.8.65 | typed | typewriter, top right of « Mon Cher Serre » | agree | sure | |

### Folder 15
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 135 | 1.4.68 | typed | typewriter, top right of « DIVERS / CANDIDATS » | agree | sure | |

### Folder 16
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 43 | 4.1.67 | his | ink, by hand, top right of the typed carbon « Dear Coates » | agree | likely | only five characters; consistent with his numerals |
| 47 | 6.1.1966 | his | ink, by hand, top right of the second typed carbon | agree | likely | « 1966 » in the same build as on 5 p. 49 and 7 p. 56 |

### Folder 23
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 43 | Paris le 11/01/68 | other | by hand, the correspondent's (Lê Dũng Tráng, name and address top left), same hand as the letter | agree | sure | |
| 55 | Bruxelles 5, le 15 décembre 1966 | other | by hand, Deligne's, same blue ink as the letter he signs | agree | sure | |
| 57 | Rösrath, le 29 octobre 1966 | other | by hand, Deligne's, same ink as the letter | agree | sure | pencil marginalia (« ? », « Err ») are a reader's, not the date |
| 59 | Bruxelles 5, le 17 octobre 1966 | other | by hand, Deligne's, same ink as the letter | agree | sure | |

### Folder 25
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 134 | 29.9.1965 | his | ink, by hand, top right of the typed carbon « Cher Dieudonné » | agree | likely | same build of « 1965 » as on 5 p. 49 |

### Folder 28
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | Demazure 5.1.1970 | his | ink, underlined heading top left, same ink and hand as the leaf | agree | sure | |
| 6 | Demazure 12.2.70 | his | ink, underlined heading top left, same ink and hand as the leaf | agree | sure | |

### Folder 29
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 2 | Voorschoten, May 16 1967 | other | typewriter: « Voorschoten, May 16 1967. / Palestrinalaan 11. » heads Murre's typed letter | disagree → typed | sure | the whole letter is typed; only small ink corrections and a blue marginal note are by hand. By the file's own usage (37 p. 95, 78 p. 93) a correspondent's typed date is `typed` |
| 4 | Voorschoten, March 29 1967 | other | by hand, Murre's, same ink as his handwritten letter | agree | sure | pencil marginalia (« SGA 1 », « O.K. ») are a reader's |
| 9 | 29.4.67 | unknown | ink, by hand, top right of the typed carbon « Dear Murre » | disagree → his | likely | same situation as 16 pp. 43/47 and 25 p. 134: his typed carbon, dated by hand; seven characters only |
| 78 | Voorschoten, 30-4-69 | other | typewriter: « Voorschoten, 30-4-69. / Palestrinalaan 11. »; only the signature is by hand | disagree → typed | sure | |
| 124 | Vallouise, 18.8.1959 | typed | black ink, by hand: « Vallouise 18.8.1959 », above the typed « Mon cher Serre » (250 dpi crop) | disagree → his | sure that it is handwritten, likely that it is his | the letter is typed, the place and date are not |
| 143 | Compléments SGA / 1960 | his | pencil, by hand, top right of an otherwise blank wrapper | agree | likely | |
| 149 | 23 mai 1961 | unknown | rubber date stamp « 23. MAI. 1961 », condensed sans-serif figures unlike the typewriter face of the form letter below it (Secrétariat mathématique, to « Monsieur A. GROTHENDIECK »); the leaf is upside down under his sketch (250 dpi crop) | disagree → machine | likely | the same leaf also has a typed « Mai 1961 » in its reply slip; the day comes from the stamp only |

### Folder 37
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 3 | Massy le 3.11.1970 | typed | typewriter, heads the carbon « Chère Madame Michon » | agree | sure | |
| 4 | Massy le 3.11.1970 | typed | typewriter, heads the carbon « Cher Deligne » | agree | sure | |
| 6 | Massy, Août 1970 | typed | typewriter (IBM-type face), at the foot of leaf « (ix) » | agree | sure | |
| 12 | Massy le 23.6.1971 | typed | typewriter, on a blue photocopy « Cher Verdier » | agree | sure | |
| 14 | Massy le 18.5.1971 | typed | typewriter, heads the carbon « Cher Verdier » | agree | sure | |
| 15 | Massy le 3.11.1970 | typed | typewriter, heads « Cher Verdier » | agree | sure | |
| 53 | Aug 4, 1969 | other | blue ink, by hand, Hartshorne's, under the printed Harvard letterhead, same ink and hand as the letter | agree | sure | the pencilled box top right (« Faire copie pour Jouanolou ») is a different hand from the date, and looks like his |
| 73 | Massy le 3.11.1970 | typed | typewriter, heads « Cher Ferrand » | agree | sure | |
| 74 | Bures sur Yvette, le 21 octobre 1968 | other | blue ink, by hand, Deligne's, same as the letter | agree | sure | pencil note top left is a reader's |
| 92 | 27.8.1967 | his | ink, by hand, top right of the typed « Cher Dieudonné » | agree | likely | |
| 95 | Nice , 11 Septembre 1967 | typed | typewriter, heads Dieudonné's typed « Mon cher Grothendieck » | agree | sure | |
| 96 | 15.9.67. | his | ink, by hand, top right of the typed « Cher Dieudonné » | agree | likely | |

### Folder 43
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 117 | September 1963 | unknown | blue ink, by hand, upside down at the foot, twice: « James  September 1963 » (struck) and « Bott  September 1963 ? », heading an English to-do list (« Zariski for Dieudonné: give a talk at the Colloquium of Harvard », « Hilton on the mailing list », « copy of my talks to Baltimore »), all crossed out (170 dpi crop, turned) | disagree → his | likely | same blue ink and same letter forms as the list of fifteen headings on the upright half of the leaf, which is his; the items are in the first person (« my talks », « for myself ») |

### Folder 44
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 7 | Bures le 12.8.1964 | typed | typewriter, heads « Mon cher Serre » | agree | sure | a pencilled « 4 » top right is a leaf number, not the date |

### Folder 45
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 71 | 22.7.961 | his | ink, by hand, top right of the typed « Commentaires sur l'article de A. Delzant… » | agree | likely | |

### Folder 53
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 16 | June 15, 1973 | other | pencil, by hand, the correspondent's (« Prof Grothendieck, The last proposition stated in the course… »), same pencil and hand as the letter, on yellow ruled paper | agree | sure | |

### Folder 57
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 72 | July 18, 1962 | typed | typewriter, heads « My dear Murre » | agree | sure | |
| 226 | Neuilly July 6 1962 | typed | typewriter, heads « Dear Hironaka » | agree | sure | |

### Folder 63
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 40 | (1968) | unknown | ink, by hand, four figures in a ring to the right of the typed title; beside « atkin 1 » a separate ink paraph (250 dpi crop) | cannot tell | cannot tell | four figures are too little to name a hand; the 1 with a flag and the 9 with a long tail do not exclude his; keep `unknown` |
| 96 | Wattignies 9/III/68 | other | pencil or soft ink, by hand, the correspondent's (signed « Carlos Ruiz S. »), same as the letter; leaf upside down and struck with three long strokes | agree | sure | |

### Folder 66
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | 1964 | his | brown ink, by hand, in a box top left, same ink as « Travaux de thèses » below (250 dpi crop) | agree | likely | |

### Folder 67
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | (1976 ou 77 ?) | other | pencil, top right of the cover: two faint cursive lines (the title), then the year line in a darker, firmer pencil, sevens crossed | agree | likely | the year line does look written apart from the title above it; at 100 dpi I can go no further than the human check already recorded |
| 13 | 20.12.77 | machine | red meter franking « 20.12.77 / NAGOYA DAIGAKUNAI / JAPAN / 0,340 » on an air-mail envelope addressed to him | agree | sure | a franking-machine impression rather than a hand-struck postmark; `machine` either way |
| 15 | Les Aumettes 15.4.1984 | typed | typewriter, heads « Dear Lipman Bers » | agree | sure | |
| 47-50 | 11-08-82 | machine | line-printer text « DERNIERE MISE A JOUR DE JOURNAL : 11-08-82 » on the printed side of p. 50; nothing of the kind is visible on pp. 47–49, whose only print is two or three JCL lines at the head (pp. 47, 48) | agree | sure | the printed date is on p. 50 only, as far as the scans show. p. 47 has, by hand beside the struck job number, « 15.1. » in his ink — a date in his hand that has no record of its own |
| 50 | 16 AUG 82 | machine | line-printer banner « … 3.45.56 PM 16 AUG 82 … » repeated six times under the block letters | agree | sure | |
| 53 | 11.1.84 | his | ink, underlined, top left, same ink and hand as the leaf | agree | sure | |
| 69 | 12.1. | his | ink, underlined, left margin beside « 5. Retour sur le principe… », same ink and hand | agree | sure | |
| 73 | 13.1. | his | ink, underlined, left margin beside the ringed « 6 », same ink and hand | agree | sure | |
| 90 | Déc 83 | his | ink, slanted, in the top left corner of a listing leaf, same ink as the notes | agree | likely | |
| 91 | 19 AUG 82 | machine | line-printer banner « 3.08.27 PM 19 AUG 82 » repeated six times; the same sheet also prints « 11-08-82 » | agree | sure | |

Aside, not about the hand: the pencilled foliation in the corner of these leaves runs three ahead of the PDF's page label here (« 50 » on p. 47, « 53 » on p. 50, « 72 » on p. 69, « 76 » on p. 73, « 94 » on p. 91).

### Folder 69
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 83 | 1976 | typed | typewriter (italic face), centred under « D.E.U.G. A Première Année / Option Mathématique » | agree | sure | |

### Folder 71
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 3 | Montpellier, 19 avril 1977 | typed | typewriter (sans-serif face, duplicated notice): « MONTPELLIER, le 19 AVRIL 1977 » | agree | sure | |
| 8 | Janvier 1978 | machine | print: « Janvier 1978 » on a Crédit Lyonnais / EDF-GDF leaflet, leaf upside down | agree | sure | |
| 14 | Montpellier, 19 avril 1977 | typed | typewriter, same notice form as p. 3 | agree | sure | |
| 47 | le 15 juillet 1976, Montpellier | other | blue ink, by hand, at the foot above a signature, same round upright hand as the whole mémoire — not his | agree | sure | the small slanted marginal notes on the left are in a different hand from the date |

### Folder 75
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 28 | Villecun 30.01.78 | typed | very faint typed line under the letterhead's « Montpellier, le », legible only after forcing the contrast of a 200 dpi render; same layout as p. 29 | agree | likely | the faint leaf also shows the letterhead and the oval stain of p. 29, so it may be a pale photocopy rather than a carbon — not a question of hand |
| 29 | Villecun 30.01.78 | typed | typewriter: « Villecun le 30.01.78 » under the printed « Montpellier, le » | agree | sure | |
| 30 | COURS C4 1977-78 | typed | typewriter, underlined title; the letterhead's « Montpellier, le » is left blank | agree | sure | |
| 32 | Cours DEA 1977/78 | typed | typewriter, title line | agree | sure | |

### Folder 78
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 93 | Paris, 10 novembre 1977 | typed | typewriter: « Paris le 10 novembre 1977 » under the CEREMADE letterhead; « A. GROTHENDIECK » added by hand below it | agree | sure | |

### Folder 80
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 27 | Montpellier, le 13 mai 1981 | typed | typewriter (italic face), duplicated notice | agree | sure | |

### Folder 91
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 30 | 11.9.1967 | his | ink, by hand, top right of the typed « Dear Anantharaman » | agree | likely | same build as 37 pp. 92 and 96 of the same weeks |

### Folder 97
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | Paris, le 4 Nov. 66 | other | « Paris, le » is printed (Collège de France letterhead); « 4 Nov . 66 » is by hand in red, the same red and hand as the letter (Serre) | agree | sure | half print, half hand; the date proper is the correspondent's |

### Folder 100
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 19 | 14 MARS 1967 | machine | rubber date stamp « 1 4 MARS 1967 », blue-black, top right of the printed proof cover « Publications mathématiques N° 32 » (which also carries the printed stamp « Bon à tirer ») | agree | sure | the ringed pencil numbers below it (« 17.1.6 », « 19.1.8 », « 19.4.11 ») are paragraph references, not dates |
| 29 | Paris, le 24 Février 1968 | typed | typewriter, heads « Cher Grothendieck » | agree | sure | |
| 37 | Harvard University, Oct. 27, 1963 | typed | **date not found on p. 37**: p. 37 is the first leaf of the preface (« Preface », no date, no signature). The typed « Harvard University / Oct. 27, 1963 » closes leaf « iv », which is **p. 25** | date not found on the page (hand agrees: typed; page → 25) | sure | order of the typed leaves as scanned: 23 (upside down), 25 = « iv », 27 = « -0.4- », 31 = « -0.2- », 33 = « iii », 35 = « ii », 37 = « Preface ». The leaf is not signed by hand; « signed » can only mean the typed place and date. p. 33 (« iii »), which the transcription's list of absent pages does not name, has a blue-ink marginal note |
| 39 | 7.4.1967 | typed | typewriter, top right of « Cher Dieudonné » | agree | sure | |

### Folder 101
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 16 | Notes antiques 1958 | his | ink, by hand, top right of a wrapper, with three more lines in the same hand under it | agree | likely | |

### Folder 103
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 8 | Lodève le 27.8.74 | his | by hand, top right of a photocopied handwritten « Cher Deligne », same hand as the letter; « Lodève le » and the first figure are very pale, « 7.8.74 » is dark (220 dpi crop) | agree | sure for the hand | on the hand nothing to add; the first figure stays as faint on the scan as the record says |
| 16 | Villecun le 23.6.1974 | typed | typewriter, heads « Chers Deligne, Giraud, Verdier » | agree | sure | |

### Folder 105
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 27 | 06/09/82-09:14:22 | machine | line-printer text running up the left margin of the listing sheet: « 06/09/82-09:14:22 » and « CFT 1.09 (05/10/82) », under his notes « 10 bis » | agree | sure | |

### Folder 106
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 12 | 24 AUG 82 | machine | line-printer banner « 2.28.52 PM 24 AUG 82 » repeated six times | agree | sure | |
| 14 | 25 AUG 82 | machine | line-printer banner « 3.04.20 PM 25 AUG 82 » repeated six times | agree | sure | |

### Folder 107
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | 06/04/82 | machine | line-printer header « ASM 0201 15.27 06/04/82 », struck by his pen strokes under his heading | agree | sure | |
| 4 | 04 JUN 82 | machine | line-printer banner « 3.31.25 PM 04 JUN 82 » repeated | agree | sure | |
| 19 | VENDR. 04 JUIN 82 | machine | line-printer text in the cost table of the « JES2 JOB LOG » | agree | sure | |
| 23 | 82155 | machine | line-printer text « START 82155.1527 » / « STOP 82155.1527 » in the JCL messages, beside his pencil diagrams | agree | sure | |
| 25 | 06/04/82 | machine | line-printer header « ASM 0201 15.27 06/04/82 » | agree | sure | |

### Folder 108
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 3 | 4 janvier 1973 | unknown | typewriter, upside down under his items 13)–14): a sender's block « Nikias Stavroulakis / 99, rue de Sèvres / 92100 Boulogne / 4 janvier 1973 », the same typewriter face as the typed text (a leaf numbered « - 18 - ») that fills the lower half | disagree → typed | sure | he boxed the block off with a pen line and wrote around it; the name on the leaf is worth adding to `context` |

### Folder 109
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 20 | Sent 19/12/83 | other | by hand, small, at the right above a ruled line, in the same English hand as the whole list of corrections (« p. 87 line 8 … ») — not his | agree | sure | |
| 28 | Sent 6/2/84 | other | by hand, centred above a ruled line, same English hand as the list of corrections — not his | agree | sure | |

### Folder 111
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | notes du 10.9.68 | his | ink, by hand, small, top right of the typed « Tapis de Quillen », the figures underlined | agree | likely | a few words and six figures; the figures are of his build |

### Folder 113
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 4 | 16 SEP 82 | machine | line-printer banner « 11.07.13 AM 16 SEP 82 » repeated | agree | sure | |
| 12 | 16 SEP 82 | machine | line-printer banner « 11.06.53 AM 16 SEP 82 » repeated, under his notes | agree | sure | |

### Folder 115
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 4 | 02 JUN 82 | machine | line-printer banner « 11.24.23 AM 02 JUN 82 » repeated | agree | sure | |
| 6 | 02 JUN 82 | machine | line-printer banner « 11.23.37 AM 02 JUN 82 » repeated; the sheet also prints « …JOURNAL : 24-05-82 » | agree | sure | |
| 12 | 02 JUN 82 | machine | a JCL message listing; I did not find the string « 02 JUN 82 » on it — what it prints is the day number « 82153 » (« START 82153.1117 », « STOP 82153.1117 »), which is 2 June 1982 | agree (hand); the literal string not found | sure for machine | `written` would be « 82153 » here, as 107 p. 23 has « 82155 » |

### Folder 116
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 10 | 19 June 1981 | typed | typewriter (sans-serif face, duplicated notice): « MONTPELLIER, le 19 JUIN 1981 » | agree | sure | the leaf has it in French |

### Folder 117
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | déc. 83 | his | ink, underlined, top right of a listing leaf, same ink and hand as the notes | agree | sure | |
| 4 | 24.11.83 | his | ink, in brackets « (24.11.83) », slanting in the left margin at the head of a marginal note, same ink and hand | agree | sure | |

### Folder 118
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 12 | 1976 | unknown | pencil, by hand, top right, after a word struck out; under it, fainter, « Poèmes / et Chants » (250 dpi crop) | cannot tell | cannot tell | four pencilled figures, darker than the two lines under them; too little to name a hand. The second line reads « et Chants » |
| 17 | Montpellier, le 29 avril 1985 | typed | typewriter: « Montpellier, le **28 avril 1983** » (250 dpi crop, unambiguous); the notice announces a defence on « 13 MAI 1983 » | agree (hand); **the date itself is misread in the record** | sure | `written` and `iso` should be 28 avril 1983 / 1983-04-28; the transcription's header (batch-01, line 26) has the same misreading |

### Folder 119
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 144 | Mars 1986 | his | ink, in a box top right, above « "Feuilletages" », same ink and hand as the slip | agree | sure | |
| 251 | Massy, le 4 Juin 1968 | typed | typewriter, right, under his typed address | agree | sure | |
| 282 | 16.04.91 | typed | printed text of a word-processed letter (proportional face, justified), « Dear Alexander, / 16.04.91 »; the address above it is added by hand | agree | sure | not a typewriter but a printer; `typed` is still the nearest of the five values (it is the letter's own text, not a stamp on the paper) |
| 308 | le 4/7/72 | other | ink, by hand, a clerk's, on a duplicated CNRS form, in the same hand as the address « Mr Grothendieck. A / 2 Avenue de Verrières / 91 Massy » and « Maths » | agree | sure | the form's own typed reference « AV- 20.I.7I » is not the date of the letter |

### Folder 120
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | 1978 | unknown | very faint pencil, left of the ink title « Topologie modérée », with a faint pencilled « (Autour de l'Éloge) » under it (250 dpi crop) | cannot tell | cannot tell | the figures are barely above the paper tone, and something faint follows them; the ink title beside it is his, which says nothing about the pencil |

### Folder 122
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 17 | 25 April 1968 | typed | typewriter: « Première conférence : jeudi 25 Avril 1968 » | agree | sure | the leaf has it in French |

### Folder 123
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 21 | Massy 22.10.1969 | his | ink, by hand, top right of the typed « Dear Kostant » | agree | likely | |

### Folder 133
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 47 | Montpellier, le 19 juin 1975 | typed | typewriter, duplicated notice | agree | sure | |
| 49 | le 5 Juin 1975 | typed | typewriter: « Montpellier, le 5 Juin 1975 » | agree | sure | |

### Folder 138
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 105 | 11.1.1977 | typed | typewriter: « Montpellier le 11.1.1977 », struck through with the three typed lines under it, his computations below | agree | sure | |
| 109 | 12.12.1977 | typed | typewriter: « Montpellier, le 12 Décembre 1977 », notice under his pencil drawings | agree | sure | the leaf spells the month out |

### Folder 141
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 2 | Montpellier, le 12 Novembre 1980 | typed | typewriter, notice n° 5982 | agree | sure | |
| 4 | Montpellier, le 12 Novembre 1980 | typed | typewriter, notice n° 5890: « Montpellier, le **7 Novembre 1980** » (250 dpi crop, unambiguous) | agree (hand); **the day is not the one recorded** | sure | pp. 2 and 6 are of the 12th, p. 4 is of the 7th; the record is marked checked for all three |
| 6 | Montpellier, le 12 Novembre 1980 | typed | typewriter, notice n° 5983 | agree | sure | |

### Folder 144
| page | written | current | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 103, 113, 115 | 16 June 1978 | other | blue ink, by hand, the student's, heading each sheet with his name: « 16 juin 1978 » on p. 103 (sheet I), « 16/06/78 » on p. 115 (sheet V) and p. 113 (sheet VI); same hand as the copy, signed on p. 113 | agree | sure | three dates in two spellings, none in English |
| 117 | 27/3/81 | other | ink, by hand, Deligne's, top right above « Cher Schurik », same hand as the letter | agree | sure | |
| 183 | juin 1981 | typed | typewriter (duplicated examination paper): « SESSION DE JUIN 1981 » | agree | sure | |

Aside: in this folder the pencilled foliation is one ahead of the PDF's page label from somewhere between pp. 115 and 117 (« 118 » on p. 117, « 184 » on p. 183).

---

## Summary

119 records looked at (the 128 records of folders 5 to 144, less the 9 of kind « paper »). Not done: none.

| verdict | records |
|---|---|
| agree | 107 |
| disagree → proposed value | 8 |
| cannot tell | 3 |
| date not found on the page | 1 |

### Disagreements

| folder | page | written | current | proposed | confidence | why |
|---|---|---|---|---|---|---|
| 13 | 13 | Algiers Nov. 1, 1965 | unknown | his | likely | pencil, same hand as the letter and its P.S. (p. 15), which is his |
| 29 | 2 | Voorschoten, May 16 1967 | other | typed | sure | Murre's letter is typed, date included |
| 29 | 9 | 29.4.67 | unknown | his | likely | handwritten in ink on his own typed carbon |
| 29 | 78 | Voorschoten, 30-4-69 | other | typed | sure | Murre's letter is typed, date included |
| 29 | 124 | Vallouise, 18.8.1959 | typed | his | sure handwritten / likely his | place and date are in ink by hand above the typed letter |
| 29 | 149 | 23 mai 1961 | unknown | machine | likely | rubber date stamp on a form letter of the Secrétariat mathématique |
| 43 | 117 | September 1963 | unknown | his | likely | his ink and letter forms; first-person to-do list |
| 108 | 3 | 4 janvier 1973 | unknown | typed | sure | typed sender's block of the reused leaf |

On 29 pp. 2 and 78: if `other` is meant to cover « a date that is someone else's, by whatever means », these two would stand and 37 p. 95, 78 p. 93, 100 p. 29 and 119 p. 282 (correspondents' typed dates, now `typed`) would be the ones out of line. Either way the six are not treated alike at present.

### Records whose current value is `unknown` (8 in this range)

| folder | page | written | proposal | confidence |
|---|---|---|---|---|
| 13 | 13 | Algiers Nov. 1, 1965 | his | likely |
| 29 | 9 | 29.4.67 | his | likely |
| 29 | 149 | 23 mai 1961 | machine | likely |
| 43 | 117 | September 1963 | his | likely |
| 63 | 40 | (1968) | keep `unknown` — four ringed ink figures | cannot tell |
| 108 | 3 | 4 janvier 1973 | typed | sure |
| 118 | 12 | 1976 | keep `unknown` — four pencilled figures | cannot tell |
| 120 | 1 | 1978 | keep `unknown` — very faint pencil | cannot tell |

### Found on the way, outside the « hand » field

These are not what was asked, but a reader of the pages would trip on them:

1. **118 p. 17** — the leaf reads « Montpellier, le 28 avril 1983 », not « 29 avril 1985 » (`written`, `iso`, and the transcription header).
2. **141 p. 4** — the leaf reads « Montpellier, le 7 Novembre 1980 », not « 12 Novembre » (pp. 2 and 6 are of the 12th).
3. **100 p. 37** — « Harvard University / Oct. 27, 1963 » is on p. 25 (leaf « iv »), not on p. 37 (leaf « Preface »).
4. **67 pp. 47-50** — the printed « 11-08-82 » is on p. 50 only; p. 47 carries « 15.1. » in his hand, which has no record.
5. **115 p. 12** — no « 02 JUN 82 » string seen; the leaf prints the day number « 82153 » (the same day).
6. `written` gives in English what the leaf has in French at 12 p. 116 (« Le 27 Mars 1968 »), 116 p. 10 (« le 19 JUIN 1981 »), 122 p. 17 (« jeudi 25 Avril 1968 »), 144 pp. 103/113/115 (« 16 juin 1978 », « 16/06/78 »).
7. Pencilled foliation and PDF page label disagree in 67 (three ahead around pp. 47–91) and in 144 (one ahead from about p. 117).

### Limits of this pass

- A hand was named from letter forms at 100 dpi (250 dpi for the doubtful ones), against pages of the same folder or of neighbouring folders that are plainly his. Where a date is a handful of figures on an otherwise typed leaf (5 p. 49, 16 pp. 43/47, 25 p. 134, 29 p. 9, 37 pp. 92/96, 45 p. 71, 91 p. 30, 111 p. 1, 123 p. 21) the verdict is « likely » and no more: the figures agree with his, and the leaves are his own letters, but a secretary's hand is not excluded by the image alone.
- « Typed » and « machine » were told apart by the face and the impression (typewriter text in the line of the letter, against a banner of a line printer, a rubber stamp, a franking mark or print).


## Part B — « hand », folders 134-1 to 162-5


Machine pre-check on the Montpellier facsimiles (PDF page = archive page + 1), not a human reading. Pages rendered at 60–110 dpi, the date's region re-rendered at 200–300 dpi where needed. Values of `hand`: his / typed (typewriter or print) / machine (computer listing, plotter or other machine-printed date on reused paper) / other / unknown.

### 134-1

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 3 | Lodève le 27.8.74 | his | photocopy of a handwritten letter « Cher Deligne »; the dateline top right is in the same hand as the body, which is his | agree | sure | on the copy only « Lodève le 27. » is clear, month and year are faint; a later marginal note along the left edge is in another hand (signed P. Deligne) and is not the date |

### 140-1

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 33 | 27-11-81 | other | red ink, written sideways at the lower right, same pen and hand as the red note « M. Grothendieck / A remplir d'urgence / Merci » and its signature; his own black-ink computation is on the upper half, another way up | agree | sure | rounded upright hand, not his |

### 162-1

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 2 | du 10.I.66 | unknown | pencil « 10.1.66 » under the struck blue-ink entry « 2 lettres à Artin (sur Atiyah–Adams) », IHÉS letterhead sheet; the pencil figures have the same shapes as the ink entries of the register | disagree → his | likely | the whole register (names, titles, strike-outs) is in one hand that matches his of the 1960s; the date is a pencil addition, struck with the entry; I read « 10.1.66 » with an arabic 1, and no « du » before it |
| 5 | du 21.9.67 | unknown | blue ink, in line with the struck entry « Grothendieck : lettre à Hartshorne du 21.9.67 », same pen and hand as the entry | disagree → his | likely | same hand as the rest of the register, which matches his |

### 146

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 58, 60 | 1979 | typed | two typewritten USTL « avis de soutenance », datelines typed: « Montpellier, le 16 mars 1979 » (p. 58), « Montpellier, le 31 mai 1979 » (p. 60) | agree | sure | nothing handwritten but the secretary's signature |
| 65 | Montpellier, 31 mai 1979 | typed | typewritten dateline of an « avis de soutenance », upside down at the foot; his ink notes over the sheet | agree | sure | |
| 72 | session de juin 1978 | typed | typewritten heading « Session de Juin 1978 » of an examination paper; his notes below | agree | sure | |
| 77 | 12 février 1982 | typed | printed letterhead « Montpellier, le », the date « 12 février 1982 » typed after it; his pencil sketches over the circular | agree | sure | |
| 131, 133 | November 1981 | typed | two typewritten « avis de soutenance », upside down, typed « Montpellier, le 25 Novembre 1981 » on both | agree | sure | the day (25) is on the leaf |

### 148

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | (29.11.83) | his | ink, in brackets, slanted in the top left corner, same pen and hand as the page of notes it heads | agree | sure | |
| 5 | 14 October 1983 | typed | typewritten dateline « Montpellier, le 14 octobre 1983 » of an « avis de soutenance » | agree | sure | |
| 9 | 18 October 1983 | typed | typewritten dateline « Montpellier, le 18 octobre 1983 » | agree | sure | |
| 7 | 20 October 1983 | typed | typewritten dateline « Montpellier, le 20 octobre 1983 » | agree | sure | |
| 21 | 10.32.40 AM 09 JUN 82 | machine | line-printer job banner « GUTS », five lines « END … 10.32.40 AM 09 JUN 82 » | agree | sure | a handwritten address block (top left) and pencil figures at the top are by hand and are not this date |
| 29 | June 1982 | machine | line-printer banner « START … 10.32.28 AM 09 JUN 82 », and a printed line « dernière mise à jour du journal 08-06-82 » | agree | sure | the day is on the leaf (9 June 1982) |
| 40 | Oct. 1983 | his | ink « Oct. 1983 » in a drawn box at the top, between the printed JCL lines; same pen and hand as the notes of the page | agree | sure | |
| 67 | 02 JUN 82 | machine | line-printer banner « 11.24.04 AM 02 JUN 82 », seen mirrored: it is the print of the other face showing through the paper | agree | sure | the date is not printed on this face; his pencil sketches are on this face |

### 150

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | déc. 81 | his | ink, top left of the first leaf (buff cover sheet), one line « déc. 81 – janv. 82 », same pen and hand as the underlined title to its right | agree | sure | the month word is cramped (« déc. » or « dec. »); the hand is not in doubt |
| 1 | janv. 82 | his | same line, same pen | agree | sure | |

### 151

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 3 | Avignon, 6 December 1990 | typed | typewritten dateline « AVIGNON le 6 décembre 1990 » of a circular with printed letterhead (Inspection académique de Vaucluse), upside down on the scan | agree | sure | photocopied circular; only the signature is by hand |
| 5 | Avignon, 6 December 1990 | typed | another copy of the same sheet, same typed dateline | agree | sure | |
| 7 | Avignon, 6 December 1990 | typed | another copy of the same sheet, same typed dateline | agree | sure | |

### 158

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 38 | Avignon, 6 December 1990 | typed | the same circular as in folder 151, typed dateline « AVIGNON le 6 décembre 1990 », upside down | agree | sure | |
| 40 | Avignon, 6 December 1990 | typed | another copy, same typed dateline | agree | sure | |

### 156-1

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | (Juin 86) | his | ink, in brackets under the title « Vers une géométrie des formes (topologiques) », same pen and hand as the page | agree | sure | the year figure is overwritten |
| 1 | (5 juin) | his | ink, in brackets at the head of the first paragraph, same hand | agree | sure | |
| 3 | 7.6. | his | ink, at the head of the slanted note in the left margin, same pen and hand as the note and the page | agree | sure | |
| 23 | (7 juin) | his | ink, in brackets at the head of the first line, same hand as the page | agree | sure | |

### 156-2

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | (Juin 86) | his | ink, in brackets top right beside the title, same hand as the page | agree | sure | |
| 1 | (6 Juin) | his | ink, in brackets after « 1. Faille topologique », same hand | agree | sure | |
| 14 | 7 Juin | his | ink, slanted in the left margin beside the heading « 2) Boucle topologique », same pen and hand | agree | sure | |

### 156-3

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | (8 Juin 86) | his | ink, in brackets on the title line « Réseaux via découpages », same hand as the page | agree | sure | |
| 21 | (9 juin) | his | ink, in brackets at the head of a new paragraph under a wavy rule, same hand | agree | sure | |

### 156-5

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | (14.6.86) | his | ink, in brackets on the title line « Sorite ensembliste », same hand as the page | agree | sure | |
| 17 | 15 juin | his | ink, underlined, top left at the head of the text, same hand | agree | sure | |
| 36 | 18 juin | his | ink, underlined, at the head of a paragraph in mid-page, same hand | agree | sure | |

### 162-5

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | (1968) | other | blue-grey ink on the buff cover: « Le Tapis de Quillen / notes d'Alexandre (1968) », a large round upright hand unlike the notes inside | agree | likely | the wording (« notes d'Alexandre ») and the letter forms both point to someone else |
| 2 | notes du 10.9.68 | his | handwritten in ink top right of the typescript's first page, « notes du 10.9.68 », underlined; small hand with the same figures and « notes du » as the heading of the manuscript p. 21 | agree | likely | the value « his » describes the handwritten date, on a typed page; on this copy I cannot tell whether the note is ink on the sheet or part of the photocopy |
| 21 | Notes du 6.9.68 | his | ink, top right, « tapis Quillen (Notes du 6.9.68) », same pen and hand as the manuscript page | agree | sure | |
| 32 | notes du 10.9.68 | his | ink top right of the typescript, « notes du 10.9.68 », same hand as on pp. 2 and 21 | agree | likely | |

### 154

Handwritten dates: looked at 100 dpi (whole page). Listing pages: all 23 looked at 50 dpi (enough to see that the only dated matter is line-printer print, not enough to re-read the figures), nine of them again at 170 dpi. Where the remark says « figures not re-read », the verdict is on the means (machine print, no handwritten date on the page), not on the reading of the date.

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | 18.1.84 | his | ink, underlined, top left corner above the first line, same pen and hand as the page | agree | sure | |
| 5 | 16 August 1982 | machine | line-printer listing, large block-letter banner and banner lines, turned a quarter; nothing handwritten | agree | sure | figures not re-read |
| 11 | 23.12.83 | his | ink, small, top left corner of the listing-paper leaf, same pen and hand as the notes | agree | sure | |
| 25 | 24.12. | his | ink, at the head of a paragraph in the left column, mid-page, same hand | agree | sure | |
| 27 | 25.12 | his | ink, underlined, at the head of a paragraph in the right column, same hand | agree | sure | |
| 43 | 31.12.83 | his | ink, top left corner, same pen and hand as the page | agree | sure | |
| 47 | 2.2.84 | his | ink, top left corner, same hand as the page | agree | sure | hand only; I did not re-read month against the record's note |
| 48 | 2.1.84 | his | ink, top left corner, same hand | agree | sure | |
| 50 | 2.1.84. | his | ink, top left corner, same hand | agree | sure | |
| 57 | 3.1.84 | his | ink, top left corner, same hand | agree | sure | |
| 64 | 3.1.84 | his | ink, top left corner above the colour sketches, same hand as the text | agree | sure | |
| 85 | 5.1.84 | his | ink, underlined, top left, same hand | agree | sure | |
| 87 | 5.1.84 | his | ink, top left, same hand | agree | sure | |
| 90 | 16 August 1982 | machine | block-letter banner « GUTS » and banner lines, upside down, line-printer print | agree | sure | figures not re-read; a short ink note of his on the page is not a date |
| 95 | 16 August 1982 | machine | block-letter banner « CRAY2 » and banner lines, upside down, line-printer print, under colour sketches | agree | sure | figures not re-read |
| 97 | 16 August 1982 | machine | block-letter banner « CRAY2 » and banner lines, line-printer print (faint or reversed: probably the other face showing through) | agree | sure | figures not re-read |
| 99 | 19 August 1982 | machine | block-letter banner « CRAY2 » and banner lines « START … », line-printer print | agree | sure | figures not re-read |
| 102 | 9 August 1982 | machine | boxed printed notices (JESNEWS) on listing paper under his colour drawings | agree | sure | figures not re-read |
| 102 | 18 August 1982 | machine | same printed notices | agree | sure | figures not re-read |
| 109 | 16 August 1982 | machine | printed « JES2 JOB STATISTICS — 16 AUG 82 JOB EXECUTION DATE », upside down at the lower right, under his colour sketches | agree | sure | date read at 170 dpi |
| 116 | 17 August 1982 | machine | block-letter banner « CRAY2 » and banner lines, line-printer print, faint | agree | sure | figures not re-read |
| 127 | 19 August 1982 | machine | printed job-log lines, upside down at the foot, under his drawings | agree | sure | figures not re-read |
| 130 | 19 August 1982 | machine | printed job-log lines at the top (« $HASP373 … STARTED », « IEF373I STEP … START 82…​.1615 »); the date is a Julian day number in the log, no handwritten date | agree | sure | the day number is at the limit of legibility at 170 dpi: I read « 82223 » (11 August) but « 82231 » (19 August) is possible — worth a look by the reader |
| 131 | 19 August 1982 | machine | the job log is seen mirrored and faint: print of the other face showing through; step lines with a Julian day (« 82231.1507 » as far as I can read) | agree | likely | the date is not printed on this face |
| 136 | 08/19/82-15:20:31 | machine | printed page header line at the top of a listing, under his colour drawings | agree | sure | figures not re-read |
| 141 | 25/8/82 | machine | printed header lines of a plotter/listing page at the top, under his pencil drawings | agree | sure | figures not re-read |
| 145 | August 1982 | machine | banner lines and notice seen mirrored (the other face showing through): « … 17 AUG 82 … », « dernière mise à jour du journal : 17-08-82 » | agree | sure | the day is legible (17 August 1982); not printed on this face |
| 150 | August 1982 | machine | banner lines seen mirrored through the paper: « … PM 19 AUG 82 … », under his ink notes | agree | sure | the day is legible (19 August 1982); not printed on this face |
| 151 | August 1982 | machine | banner « CRAY6 » printed on this face: six lines « END JOB 13 CRAY6 … 3.24.18 PM 19 AUG 82 » | agree | sure | the day is legible (19 August 1982) |
| 154 | August 1982 | machine | a printed notice seen mirrored and faint at the top right (« … sera mis en service … août 1982 »), under his ink notes | agree | likely | a date announced in a notice, not the date of the print-out |
| 155 | August 1982 | machine | listing paper with his pencil and ink drawings; a printed boxed notice begins at the lower right edge of what I rendered | agree | likely | I did not find the dated line itself at this resolution; nothing handwritten that is a date |
| 158 | August 1982 | machine | listing paper with printed boxed notices at the right, under his sketches | agree | sure | figures not re-read |
| 159 | 1.1.84 | his | ink, top left corner, same pen and hand as the page (which is crossed out) | agree | sure | |
| 160 | 16 Aug 82 | machine | printed lines upside down at the lower right, under his colour sketches | agree | sure | figures not re-read |
| 164 | 16 August 1982 | machine | block-letter banner « GUTS » and banner lines, line-printer print | agree | sure | figures not re-read |
| 166 | 16 August 1982 | machine | block-letter banner « CRAY2 » and banner lines, line-printer print | agree | sure | figures not re-read |
| 172 | 17 August 1982 | machine | block-letter banner « CRAY2 » and banner lines, line-printer print | agree | sure | figures not re-read |

### 134-2

A question of definition comes up in this folder: three dates are on typewritten pages. If `hand` says by what means the date is on the leaf (which is how the rest of the file uses it — e.g. 134-4 and 134-8, typescripts he typed himself, are « typed »), two of the records below are « typed », not « his ». If the field was meant as « his date, whoever typed it », they stand.

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 38 | Villecun 5.2.1975 | his | typewritten dateline « Villecun 5.2.1975 » on a typed transcription of the letter (« Cher Breen », pasted strips of typescript); nothing handwritten in the date | disagree → typed | sure | the only handwriting near it is a pencil « 23 bis » at the top (a page number) |
| 48 | Villecun le 17.2.1975 | his | typewritten dateline; the page is headed, typed and struck through, « Transcription d'une lettre manuscrite de A. Grothendieck »; in the place name the last letters « cun » are written over in ink, « le 17.2.1975 » is all typed | disagree → typed | sure | a typed transcription, date included; one ink correction to the place name, hand not identifiable from three letters |
| 56 | 17/19 July 1975 | his | handwritten in black ink at the top right of a typewritten English page: « Villecun 17/19 July 1975 »; the hand (V, the crossed 7s, the « ll ») matches his ink corrections further down the page and his original on p. 145 | agree | likely | a handwritten date on a typed page |
| 14 | Les Aumettes 19.2.1983 | his | handwritten in ink at the top right of the typewritten letter (« Dear … »): « Les Aumettes 19.2.1983 », same hand as the ink corrections in the typed text | agree | sure | a handwritten date on a page he typed |
| 112 | 22.2.1983 | typed | typewritten « 22.2.1983 » centred above § 13 | agree | sure | |
| 120 | November, 1982 | typed | typewritten « November, 1982 » under the typed signature block « R. Brown … Bangor »; a pencil note below it in another hand is not the date | agree | sure | the pencil foliation on the leaf reads 121 while the facsimile's page number is 120 |
| 145 | Villecun 17/19 juillet 1975 | his | ink, top right of a handwritten letter « Cher Larry », same pen and hand as the letter, which is his | agree | sure | |

### 134-3

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | 27.2.83 | his | typewritten « 27.2.83. » at the left under the typed title « Reflections on homotopical algebra »; the handwriting on the page is his ink corrections between the lines and a « 1 » top left, none of it the date | disagree → typed | sure | same typewriter and same lay-out as the dates of 134-4 and 134-8, which the file records as « typed » |

### 134-4

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | 27.3. | typed | typewritten « 27.3. » top left above § 45, typescript p. (89) | agree | sure | |
| 7 | 30.3. | typed | typewritten « 30.3. » above § 47, mid-page, typescript p. (95) | agree | sure | |
| 11 | 31.3. | typed | not on p. 11 (typescript p. 99, which opens « Let X,Y be objects of M … » and has no date). The typed « 31.3. » and the heading « 48. » are on archive p. 10 (typescript p. (98)), lower half | date not found on the page — it is on p. 10; hand typed, agree | sure | page to correct: 10, typescript p. 98 |
| 21 | 2.4. | typed | typewritten « 2.4. » above § 50, typescript p. 109 | agree | sure | |
| 36 | 3.4. | typed | typewritten « 3.4. » above § 52, typescript p. 124 | agree | sure | |
| 56 | 5.4. | typed | typewritten « 5.4. » top left above § 58, typescript p. 144 | agree | sure | |
| 80 | 7.4. | typed | typewritten date above § 65, typescript p. 168, of which the first figure is written over in ink: the « 7 » is by hand, « .4. » is typed; the section number below is corrected by hand in the same ink | agree | sure | what was typed under the « 7 » cannot be made out; the ink correction is in the manner of his other corrections on the page (likely his) |
| 92 | 9.4. | typed | not on p. 92 (typescript p. 179, which ends « We got the longed-for "key result" in the end ! »). The typed « 9.4. » and « 66. » are at the top of archive p. 93 (typescript p. 180) | date not found on the page — it is on p. 93; hand typed, agree | sure | page to correct: 93; the offset archive page / typescript page changes by one between pp. 80 and 91 |
| 68 | 6.3. | typed | typewritten « 6.3. » above § 63, typescript p. 156 | agree | sure | reads « 6.3. » as recorded |

### 134-8

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | 22.10. | typed | typewritten « 22.10. » top left, typescript p. 555; the rest of the page is masked on the facsimile | agree | sure | |
| 3 | 26.8. | typed | typewritten « 26.8. » above § 134, typescript p. 557 | agree | sure | reads « 26.8. » as recorded |
| 11 | 27.10. | typed | typewritten « 27.10. » top left above § 136, typescript p. 565 | agree | sure | |
| 16 | 27.10. | typed | typewritten « 27.10. » above § 137, lower third, typescript p. 570 | agree | sure | |
| 26 | 28.10. | typed | typewritten « 28.10. » above § 138, typescript p. 580 | agree | sure | |
| 33 | 29.10. | typed | typewritten « 29.10. » above § 139, typescript p. 587 | agree | sure | |
| 38 | 4.11. | typed | typewritten « 4.11. » top left above § 140, typescript p. 592 | agree | sure | |
| 38 | 12.11. | typed | typewritten « 12.11. » at the foot of the same page | agree | sure | |
| 42 | 25 AUG 82 | machine | line-printer banner lines « START … PM 25 AUG 82 », upside down, on listing paper; his ink diagrams over it | agree | sure | printed on the face that carries his diagrams |
| 46 | 26/ 8/ 82 | machine | printed header lines of a plotter listing at the top of the sheet, under his ink notes | agree | sure | figures not re-read at this resolution |
| 72 | 17-05-82 | machine | printed line « DERNIERE MISE A JOUR DE JOURNAL: 17-05-82 » under a « CRAY OUTPUT » banner; his ink notes written across | agree | sure | date read |

### 157-1

Page numbers: in the 157 folders the record's `page` is the pencil foliation on the leaf, which here equals the PDF page index; Montpellier's printed page number under the image is one less (record p. 105 = PDF page 105 = « 104 » in the footer). The rule « PDF page = page + 1 » does not hold for these records; I looked at the leaf that carries the pencil number.

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 105 | 11.11.90 | his | ink, above the first line of a new paragraph in mid-page, same pen and hand as the page | agree | sure | |
| 241 | 3.4 | his | ink, top right of the page, two short strokes and « 7.4 » with a crossed 7 — the same « 7.4. » that the fifth line of the page cites (« les opérations de 7.4. a) ») | agree on the hand (his); the reading is doubtful | sure for the hand, likely for the reading | I read « de 7.4 » or « au 7.4 », not « 3.4 », and it looks like a reference to a section 7.4 rather than a date — to be checked by the reader before it stays a dated leaf |
| 247 | 23 NOV 82 | machine | blank back of a listing sheet used as a divider (his pencil title and « III » at the top); the print of the other face shows through, mirrored and faint: « … 23 NOV 82 JOB EXECUTION DATE » | agree | likely | the date is not printed on this face; read through the paper at 200 dpi |
| 129 | Octobre 1985 | other | typewritten: « Octobre 1985 » is typed at the head of a typed letter on printed letterhead, stamped « COPIE », the sheet turned a quarter; no handwritten date | disagree → typed | sure | a third party's letter, but the date is typewriter, not a hand; if `other` is meant as « someone else's document », see the note on definitions under 134-2 |
| 125 | 10-4-86 | other | handwritten in ink top right, above a handwritten note on a correspondent's printed letterhead, same pen and hand as the note and its initials; a large loose hand, not his | agree | sure | |
| 108 | 15 mai 1986 | typed | typewritten testimony, turned a quarter; the date occurs in the typed text (« Le 15 mai 1986, … ») | agree | sure | the date is in the running text, not a dateline: it is the date of an event the text relates, so a terminus post quem for the typing |

### 157-2

Here the pencil foliation and Montpellier's printed page number agree with the record's `page` (PDF page = page + 1), unlike 157-1.

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 1 | 23 NOV 82 | machine | blank back of a listing sheet used as divider (his title and « V » in pencil/ink at the top right); the line-printer print of the other face shows through, faint and mirrored | agree | likely | the date is not printed on this face; figures not re-read through the paper |
| 370 | 5.11.90 | his | ink, above a new paragraph in mid-page (after a slanted stroke), same pen and hand as the page | agree | sure | |
| 405 | 9.11.90 | his | ink, top right above the first lines, same hand | agree | sure | |
| 417 | 13.11.90 | his | ink, top right beside the first lines, same hand | agree | sure | |
| 56 | 14.11.90 | his | ink, top centre-right above a bracketed note, on the title page « Le dérivateur HOT », same hand | agree | sure | |
| 96 | 15.11. | his | ink, top right corner, same hand as the page | agree | sure | |
| 139 | 16.11 | his | ink, at the right above a new paragraph in mid-page (after a slanted stroke), same hand | agree | likely | small; the figures are clear enough for the hand, I did not enlarge them |

### 157-3

Pencil foliation and Montpellier's page number agree with the record's `page` (PDF page = page + 1).

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 29 | 15 NOV 82 | machine | line-printer listing with block-letter banner and banner lines « START … » | agree | sure | figures not re-read at 80 dpi |
| 36 | 23 NOV 82 | machine | line-printer banner « GUTS », lines « START … 1.55.07 PM 23 NOV 82 », and a printed « dernière mise à jour du journal : 22-11-82 » | agree | sure | date read |
| 27 | 7 novembre 1986 | typed | typewritten closing line « à La Ribe le 7 novembre 1986 » under a handwritten initial, last page (« 4 ») of a typed letter, struck through with two pen strokes | agree | sure | |
| 37 | nov. 88 | his | handwritten in ink in the blank lower left of a photocopied magazine page: « "30 millions d'amis" / nov. 88 »; a small rounded hand with open, looped 8s | cannot tell | cannot tell at this resolution | seven words are too few; the rounded letters and the 8s do not look like his usual figures (compare his « 86 », « 90 » in these folders), so « his » is not established — I would leave it `unknown` until a reader has compared; I also cannot tell whether the note is ink on this sheet or part of the photocopy |

### 157-4

| page | written | current hand | seen on the page | verdict | confidence | remark |
|---|---|---|---|---|---|---|
| 229 | 7.9. | his | ink, second line of the page (his page number 104, not 109), after a slanted stroke: « On conclut … de 7.9. 1°, 2°, 3° »; same pen and hand as the page | agree on the hand (his); probably not a date | sure for the hand, likely for the reading | I read « de 7.9. 1°, 2°, 3° », a reference to items 1°–3° of a statement numbered 7.9 (the page itself numbers its statements 8.2, 8.3, 8.4), not « le 7.9. »; the record already calls the reading uncertain — to be checked by the reader before it stays a dated leaf. I did not look for a leaf carrying his number 109 |

### 157-5 — not done

The PDF is 272 MB, over the 250 MB limit set for this pass. One record not looked at: p. 2, « 06 NOV 82 », current hand `machine` (computer listing reused for the summary of chapter XVII).

---

### Summary

124 records in scope (folders after « 144 » in (length, string) order: 134-1 … 134-8, 140-1, 146 … 162-5). No record of kind « paper » among them. Looked at: 123. Agree: 116. Disagree: 6 (of which 2 are the `unknown` records, now with a proposal). Cannot tell: 1. Not done: 1 (157-5).

#### Disagreements

| folder | page | written | current | proposed | confidence | why |
|---|---|---|---|---|---|---|
| 134-2 | 38 | Villecun 5.2.1975 | his | typed | sure | typewritten dateline of a typed transcription of the letter |
| 134-2 | 48 | Villecun le 17.2.1975 | his | typed | sure | typewritten dateline of a page headed « Transcription d'une lettre manuscrite de A. Grothendieck »; only « cun » of the place name is inked over |
| 134-3 | 1 | 27.2.83 | his | typed | sure | typewritten, like the dates of 134-4 and 134-8 which are recorded as typed |
| 157-1 | 129 | Octobre 1985 | other | typed | sure | typewritten at the head of a third party's typed letter (copy) |
| 162-1 | 2 | du 10.I.66 | unknown | his | likely | pencil date under a struck entry of the lending register, same figures and hand as the register, which matches his; reads « 10.1.66 » |
| 162-1 | 5 | du 21.9.67 | unknown | his | likely | in line with the struck entry, same pen and hand as the register |

The first four turn on what `hand` means. They are disagreements if the field records the means by which the date stands on the leaf (the file's own practice elsewhere: 134-4, 134-8, 157-1 p. 108, 157-3 p. 27). If « his » was meant as « a date of his, typed », 134-2 pp. 38, 48 and 134-3 p. 1 are consistent with folder 5 p. 49 (« typed carbon letter », `his`) but then inconsistent with 134-4 and 134-8. One rule should be chosen for the whole file.

#### Records whose current value is `unknown`

| folder | page | written | proposal | confidence |
|---|---|---|---|---|
| 162-1 | 2 | du 10.I.66 | his | likely |
| 162-1 | 5 | du 21.9.67 | his | likely |

Both rest on the same judgment: that the lending register as a whole is in his hand (IHÉS letterhead, his letter forms and figures of the 1960s, entries naming « Grothendieck : lettre à Hartshorne » in the third person as an item lent). A reader who knows the hand should confirm on one page; the two records then follow.

#### Cannot tell

- 157-3 p. 37, « nov. 88 », current `his` (the record itself says « probably his »): a two-line ink note on a photocopied article; too little writing, and the figures do not look like his. Suggest `unknown` until compared by a reader.

#### Agreed on the hand, but something else to check

- 157-1 p. 241, « 3.4 » (`his`): I read « 7.4 », and it looks like a reference to section 7.4 (cited again five lines below), not a date.
- 157-4 p. 229, « 7.9. » (`his`): I read « On conclut … de 7.9. 1°, 2°, 3° », a reference to a statement 7.9, not a date; his page number on the leaf is 104, not 109.
- 134-4 p. 11, « 31.3. »: the typed date is on archive p. 10 (typescript p. 98), not p. 11.
- 134-4 p. 92, « 9.4. »: the typed date is on archive p. 93 (typescript p. 180), not p. 92.
- 134-4 p. 80, « 7.4. »: typed, but the « 7 » is written over in ink.
- 154 p. 130, « 19 August 1982 »: the only date I found is a Julian day in the job log, which I read « 82223 » (11 August) at the limit of legibility; « 82231 » (19 August) is possible.
- 154 p. 154, « August 1982 »: the date is one announced in a printed notice (« … août 1982 »), seen through the paper.
- Dates that are on the other face and only show through the paper (mirrored): 148 p. 67; 154 pp. 131, 145, 150, 154 (and probably 97); 157-1 p. 247; 157-2 p. 1. The value `machine` stands; the page given is the face the date is read through, not the face it is printed on.
- 162-1 p. 2: the page has « 10.1.66 » with an arabic 1 and no « du ».
- 134-1 p. 3: on the photocopy only « Lodève le 27. » is clear; month and year are faint.
- Page numbering in 157-1: the record's `page` is the pencil foliation, one more than Montpellier's printed page number (in 157-2, 157-3, 157-4 the two agree).

#### Limits of this pass

- 154: of the 23 listing pages, the printed figures were re-read on 6 (pp. 109, 130, 131, 145, 150, 151); on the others I saw at 50 dpi that the dated matter is line-printer print and that no handwritten date is on the page, and did not re-read the figures. 154 p. 155: the dated line itself not found in my render.
- Handwritten dates of 154 and 157-2 were judged at 80–100 dpi on the whole page (position, pen, continuity with the page), without an enlarged crop of each.


## Part C — skipped pages

### 2. Sampling method (redrawable)

Script: computations/issue-66-skipped/sample.py, on pop.json and sizes.json (PDF sizes from `curl -sI https://grothendieck.umontpellier.fr/<cote>.pdf`, Content-Length; 125 of the 140 folders with skips are under 80 MB).

- Strata are the reason classes of section 1, with quotas: illegible 5, unrelated 5, administrative 8, others' typescript 18, gap only 7, not classifiable 5, printed/published 3, duplicate 2, verso 2, cover/wrapper 2, blank 4 — 61 pages.
- In each stratum the pages are sorted by (cote as string, page), shuffled with Python `random.Random(66)` (one generator, strata taken in the order above), and taken in order, skipping a page when its folder's PDF is 80 MB or more or when the folder already has 3 sampled pages. No stratum needed the fallback to larger PDFs.
- Result: 61 pages in 36 folders (largest PDF 79 MB). All 61 were fetched and looked at; none is « not done ».
- Each page was rendered from Montpellier's PDF (PDF page = archive page + 1; the footer number printed on the rendered page was checked against the archive page each time) at 110 dpi, with a 220 dpi crop where the first look was not enough. The batch file was then searched for the words seen on the page.
- Caveat on the classes: they come from a keyword sort of the header prose. Several sampled « illegible », « duplicate », « printed » and « verso » pages turned out to be covers or blanks whose header sentence happened to contain the keyword; the column « recorded reason » below gives the header's own wording, which is what counts.

### 3. The sampled pages

Hands: I compared only with what the folder's header says and with the general look of his hand; « likely his » is not a settled attribution.

| cote | page | recorded reason (header) | what the page shows | anything of his missed? | confidence |
|---|---|---|---|---|---|
| 5 | 35 | « carry no mathematics of his » (typed verso) | Typed leaf numbered « 39 bis », a French analysis text (Cauchy sequence, φ(m), ψ(m)); the Greek letters and ≤ signs are inked into the typing; no marginal writing | no (the inked symbols belong to the typescript; whose pen, cannot tell) | likely |
| 5 | 37 | « carry no mathematics of his » (typed verso) | Typed leaf, EGA-style text citing (6.14.4), (6.14.1), (17.5.7); in ink: page number « – 18 – » at the head, a « t » added to « ramènent », a stroke separating « est/intègre », underlines under « sans utiliser », « intègre », « étale », the last digit of (17.5.7) rewritten; three typed words blacked out | cannot tell: ink corrections on a typed leaf, hand not identifiable from these few strokes (the number 18 and the « t » could be his or a co-author's) | cannot tell |
| 12 | 118 | skipped verso, « carry March 1968 dates » | Printed cover of Lecture Notes in Mathematics 41, Local Cohomology; rubber stamp « 20. 3. 68 1. Korrektur » top right; nothing handwritten except the archivists' 118 | no | sure |
| 12 | 138 | cover in his hand, boxed « Motifs lisses versus Isomotifs lisses » | Tan cover, the three lines boxed top right | no — carried as \section{Motifs lisses versus Isomotifs lisses} (batch-07, l. 294) | sure |
| 14 | 21 | unrelated typescript, Bourbaki n° 391 p. 14, upside down, nothing in his hand | Upside-down blue carbon typescript « n° 391 – 14 – »; no handwriting | no | sure |
| 14 | 100 | « Skipped. Typed leaves of his comments on a redaction … and a typed draft « § IV Différentielles et dérivations », with corrections and inked arrows » | Blue typed leaf: a square diagram with inked arrows, « N.B. On pose E_{i,n} = E_i/I_i^{n+1} … », « Lemme C. Supposons C et B form. simple sur A … a) … b) … »; several lines x-ed out, ink insertions (« a) », « il existe »), half the page cancelled with long diagonal strokes; pencil « 95 » top right | yes: by the header's own account this is a typed draft of his with his corrections; the mathematics (Lemme B's N.B., Lemme C a) and the cancelled b)) is not carried anywhere | sure that it is not carried; that the typing and the ink are his: likely (header says so) |
| 18 | 1 | « he has written across the head of it « Papiers donnés à Saav[edra] » — … skipped too and the inscription recorded only here » | Blank back of a typed reference list (show-through), with one pencil line at the head: « Papiers donnés à Saavedra » (the name looks written out in full) | yes: the inscription is on the page and is only in the header comment, not in the reading (no \note, no heading) | sure it is absent from the body; hand likely his |
| 31 | 72 | blank | Blank cream sheet, archivists' 72 only | no | sure |
| 33 | 20 | typed verso, Bourbaki-style draft n° 391, nothing in his hand | Typed « – 189 – n° 391 », Dynkin diagrams typed/drawn in the stencil; no handwriting | no | sure |
| 33 | 58 | typescript unrelated (English, sheaves and perfect categories) | Typed « – 26 – », definitions 5.2, 5.3 on small objects; inked § and φ symbols of the typescript; no marginalia | no | sure |
| 33 | 174 | unrelated typescript (papers in English) | Typed p. 11 of an English paper on regular local domains; one typed formula struck and replaced in ink by « y_i = x_i/x_1 » | cannot tell: one ink correction of a formula; most likely the paper's own correction, but the hand cannot be settled | cannot tell |
| 43 | 13 | blank sheet | Blank cream sheet | no | sure |
| 43 | 102 | typed leaf of an English paper on Stiefel manifolds, upside down, nothing in his hand | As described (typed p. 21) | no | sure |
| 43 | 121 | (cover; class « duplicate » is a sorting error) | Tan cover inscribed top right « Corps de classes et dualité des Courbes Algébriques » | no — carried as \section*{Corps de classes et dualité des Courbes Algébriques} (batch-07, l. 115) | sure |
| 45 | 30 | skipped without description (typed verso) | Upside-down typed leaf « – 21 – n° 246 » (half-lines, sectors) | no | sure |
| 45 | 43 | tan sheet blank but for « H^1 » top right | As described | no — carried as \subsection*{$H^1$} (batch-03, l. 168) | sure |
| 45 | 57 | typed verso, nothing in his hand | Typed « – 59 – n° 269 » (hermitian forms) | no | sure |
| 60 | 7 | typed verso (Bourbaki material) | Upside-down typed « – 55 – n° 357 » (Haar measure) | no | sure |
| 60 | 41 | typed verso, Bourbaki n° 392 | Typed « 6 – 25 – n° 392 » (exercises on factorial rings) | no | sure |
| 60 | 43 | typed verso, Bourbaki n° 392 | Typed « 6 – 24 – n° 392 » | no | sure |
| 62 | 28 | typed leaf, nothing of his mathematics | Upside-down typed « – 39 – n° 272 » (valuations) | no | sure |
| 62 | 34 | typed leaf, nothing of his mathematics | Upside-down typed « – 45 – n° 272 » | no | sure |
| 67 | 7 | unrelated typed verso (a list of plots of land) | Upside-down typed « LISTE DE TERRAINS »; two long pen strokes across the page and a few stray pen ticks; no word or figure written | no (the strokes cancel the sheet; nothing to read) | likely |
| 68 | 34 | blank | Blank cream sheet | no | sure |
| 69 | 1 | tan cover bearing only a pencilled « (34p) », « not certainly his » | As described: pencil « (34 p) » top right | cannot tell: the page count is recorded in the header only; whether it is his hand cannot be settled | cannot tell |
| 69 | 64 | pink separator sheet | Blank pink sheet | no | sure |
| 70 | 26 | « carry no mathematics » | Typed leaflet of the Section des Universités du PCF calling to demonstrate on 10 December 1977; no handwriting | no (the typed date 10 December 1977 is not his; see whether the dating of the folder uses it) | sure |
| 70 | 27 | « carry no mathematics » | Blank pink sheet | no | sure |
| 72 | 78 | (gap only in my sort; header: coloured wrapper bearing a title in his hand) | Pink sheet, one line top right, read by the transcription « Sous-espaces invariants » | no — carried as \section{Sous-espaces invariants} with a \note (batch-04, l. 814); the reading agrees with a 220 dpi crop | likely |
| 73 | 2 | cream sheet, show-through only | Blank; faint show-through | no | sure |
| 73 | 7 | cream sheet, show-through only | Blank; mirror-image show-through of the next leaf's formulas | no | sure |
| 73 | 13 | cream sheet, show-through only | Blank | no | sure |
| 74 | 36 | (no header mention) | Typed letter on USTL letterhead, « Montpellier, le 14 Juin 1977 », convening a DEUG jury; the addressee « le Professeur GROTHENDIEK » and a room number are filled in by the sender's pen; sender's signature | no (the handwriting is the sender's) | sure |
| 77 | 72 | unrelated typed verso | USTL notice of 7 December 1977 (film projection), address label to him | no | sure |
| 77 | 78 | unrelated typed verso | Upside-down « Avis de soutenance », 8 December 1977, signed by the Secrétaire général | no | sure |
| 80 | 25 | photocopy of a handwritten letter in German, autobiographical, unrelated to the mathematics | Photocopy of a double page of German handwriting, numbered « 5 » in the corner; words readable: « Spontaneität der Untersuchung », « Doch könnte ich, im selben Geist der Spontaneität, von einer beliebigen Periode meines Lebens ausgehen », « Briefwechsel mit H…ka seit 19?2 », « bis zu ihrem Tod », « weiter zurück in meine Kindheit »; one word (« betreffend ») inserted above the line in darker ink | yes, if the hand is his: the writing looks like his own hand and the content reads as his own (his life, a correspondence since the 1940s); the register (letters.json) has writer and addressee unknown. Nothing of the text is carried | likely his hand; a reader of German should confirm |
| 91 | 87 | (no header mention) | Upside-down typed « – 139 – n° 316 » (Lie algebra exercises) | no | sure |
| 91 | 122 | typed verso unrelated | Upside-down typed « – 92 – n° 371 » (exterior algebra) | no | sure |
| 98 | 9 | typed page of typescript n° 329, not by him, upside down | As described (« – 36 – ») | no | sure |
| 100 | 29 | typed letters on the odd pages | Typed letter « Paris, le 24 Février 1968 … Cher Grothendieck », signed L. Illusie; two long pen strokes across the text | no (letter registered in letters.json, p. 29; the strokes cancel the sheet) | sure |
| 117 | 18 | ruled administrative table in another hand | Ruled table turned sideways, round upright hand: « 1981 », « M. Chatowicz », « M. Auberson », « Fixe / Points », amounts | no (clearly not his hand) | sure |
| 118 | 6 | ruled administrative table in another hand | Same hand: « Séminaire d'Analyse Fonctionnelle », « Séminaire d'Analyse Convexe », amounts; his diagrams of the other side show through | no | sure |
| 120 | 1 | cover, « Topologie modérée », faint pencil « 1978 » | Pink cover: ink « Topologie modérée » over struck words, faint pencil « 1978 » and a parenthesis beneath | no — carried as \section*{Topologie modérée} with a \note describing the struck word and the pencil (batch-01, l. 102–108) | sure |
| 122 | 9 | typed leaf of Bourbaki draft n° 387, « nothing of his » | Typed « – 43 – n° 387 »; a small handwritten cross « × » in the left margin beside exercise 5) | cannot tell: one marginal cross, hand not identifiable | cannot tell |
| 122 | 11 | typed leaf of Bourbaki draft n° 387 | Typed « – 46 – n° 387 »; a faint pencil zigzag in the top right corner, no writing | no | likely |
| 122 | 24 | « the versos » | English typescript p. « –4.14– » (blow-ups, G_m action); no handwriting but the archivists' number | no | sure |
| 133 | 15 | offprint, printed, nothing in his hand | Printed page of C. R. Acad. Sc. Paris t. 278 (24 juin 1974), p. 1601 | no | sure |
| 134-8 | 61 | (no header mention; header: « The other pages of the batch (handwritten notes, listings on the backs) are left out ») | Computer listing sheet (plotter log, « 26/ 8/ 82 ») covered with handwritten mathematics in ink: « Δ^ → Ch.(Ab) », a staircase diagram with « K_{p,q} », « K_{1,0}+K_{0,1} », « K_{0,0} = 0 », « P → 𝒫 —λ_!→ Ch.(Ab) » with « λ^* » back, « λ^*(Θ[n]) = C^n… », exact sequences « 0 → h → Θ → h[1] → Θ[1] → k[2] … » | yes: a full page of handwritten mathematics, not carried (deliberately: the batch is a limited pass that transcribes p. 63 only) | sure it is not carried; hand likely his |
| 134-8 | 71 | (same) | Listing sheet (« 19 MAY 82 »), handwritten in ink: « A → M_as ⊂ M —k→ Ab_k », « A^/X ≃ (A/X)^ », « A → B », « add A → add B », « f_! f^* », « Z^(A), Z^(B) », « W_k-asphérique » | yes: handwritten mathematics, not carried (same limited pass) | sure it is not carried; hand likely his |
| 135 | 33 | « a handwritten French poem titled "Rêve", struck through … not the mathematics in hand, absent » | Blue-ink manuscript of some twenty short lines headed « Rêve » in the margin, with corrections above the line, cancelled by long diagonal strokes; words readable: « patiemment / amoureusement / je l'ai édifiée / l'image de la déesse / dans le tabernacle de mon cœur », « devant elle je me suis prosterné », « doux et implacable » | yes: a draft poem; the writing and the manner of correction look like his. Not carried (the header says so; the modern reading mentions « un poème ») | likely his hand |
| 138 | 112 | cover sheet inscribed in his hand | Yellow wrapper, one line top: « Cartes sphériques en bas degrés » | no — carried as \section{Cartes sphériques en bas degrés} (batch-06, l. 365) | sure |
| 144 | 105 | USTL administrative note, « 105 with only show-through » | Upside-down typed circular « Montpellier, le 27 septembre 1978 … Cher(e) Collègue », signed P. Molino, C. Roumieu; faint dots and an ellipse are show-through of a drawing on the other side | no. The header's description is inexact: the page is a typed circular, not show-through alone | likely |
| 144 | 111 | USTL administrative note | Typed note, Institut de Mathématiques, 26 septembre 1978, signed N. Roby | no | sure |
| 144 | 152 | unrelated verso (computer listing) | Upside-down banner page of a computer listing (« 06 NOV 82 »); archivists' pencil reads 153 on the leaf the PDF footer calls 152 | no | sure |
| 151 | 3 | administrative letter, Inspection académique de Vaucluse, 6 December 1990, upside down | As described; sender's signature only | no | sure |
| 151 | 5 | another copy of the same | As described | no | sure |
| 158 | 5 | nothing but the archivists' number | Blank cream sheet, pencil 5 | no | sure |
| 161-4 | 1 | (no header mention in my sort; header l. 10: the folder's jacket) | Folder jacket; pencil on the tab « Introduction à Géom. Alg. »; a pencil « 9 » in a rounded box at the head | no — the tab's words are carried as \section* with a \note (batch-01, l. 81–83). The boxed « 9 » is not mentioned (probably a filing number, hand not settled) | sure for the title |
| 161-5 | 3 | printed, « nothing in any hand » | Printed page (Introduction of a paper on p-divisible groups and Hodge–Tate modules) | no | sure |
| 162-5 | 53 | (no header mention) | Printed offprint page 240, « D. G. Quillen » | no | sure |
| 162-5 | 62 | « duplication only » | Faint blue carbon of an English typescript p. « – 6 – » (sphere fibrations over pro-objects) | no (whether it duplicates a transcribed leaf was not checked) | sure for the absence of handwriting |

Counts: 61 pages looked at — 51 « no » (the skip is right, or his words are in fact carried), 6 « yes », 4 « cannot tell », 0 not done.

What the sample says about the population:

- The typed versos (others' typescript, Bourbaki drafts, USTL circulars) are clean: 24 of 24 looked at carry nothing of his beyond, at most, a cancelling stroke. Two carry one small mark of an unknown pen (33 p. 174, 122 p. 9).
- Covers and wrappers: every inscribed cover in the sample (12 p. 138, 43 p. 121, 45 p. 43, 72 p. 78, 120 p. 1, 138 p. 112, 161-4 p. 1) is carried as a heading; the only cover words left out are 18 p. 1 (by declared choice) and the « (34p) » of 69 p. 1.
- Where something of his is missing, it was left out by a declared rule, not overlooked: a limited pass (134-8 batch 4: by its header, all the handwritten notes of pp. 61–80 except p. 63 are left out — 19 pages in the population, two sampled, both full of mathematics), « not the mathematics of this folder » applied to his own typed draft (14 pp. 96, 98, 100) and to his non-mathematical writing (135 p. 33, 80 pp. 21–29). No sampled page skipped as blank or illegible carried anything.
- Not seen in the sample: a verso continuing its recto, or a page called illegible that was only upside down.

### 4. Review lines — pages where something of his seems to have been skipped

- [ ] 134-8 p61 | skipped | Is this page of handwritten mathematics (complexes Ch.(Ab), λ_!, λ^*, K_{p,q}) in his hand, and should the limited pass of batch 4 be extended to the handwritten notes of pp. 61–80? | Nothing: batch 4 transcribes p. 63 only and says « the other pages of the batch (handwritten notes, listings on the backs) are left out » | A listing sheet of 26/8/82 covered in ink with diagrams and exact sequences, same manner as the folder's other notes
- [ ] 134-8 p71 | skipped | Same question for this leaf (« A → M_as ⊂ M → Ab_k », « W_k-asphérique ») | Nothing (same limited pass) | A listing sheet of 19 May 82 with a dozen handwritten formulas in ink
- [ ] 14 p100 | skipped | Is this typed leaf (Lemme B's N.B., Lemme C on algebras « form. simple sur A », with ink corrections and a cancelled part b)) his own draft, and should it — with pp. 96 and 98 — be transcribed? | Header: « Skipped. Typed leaves of his comments on a redaction about complete local rings … and a typed draft « § IV Différentielles et dérivations », with corrections and inked arrows »; no text carried | Blue typed leaf with a diagram, two lemmas, x-ed out lines, ink insertions « a) », « il existe », diagonal cancelling strokes, pencil « 95 »
- [ ] 135 p33 | skipped | Is the poem « Rêve » in his hand, and should it be carried (or at least noted in the reading)? | Header: « a handwritten French poem titled "Rêve", struck through with long diagonal strokes — not the mathematics in hand, absent » | About twenty short lines in blue ink with corrections above the line (« patiemment / amoureusement / je l'ai édifiée / l'image de la déesse / dans le tabernacle de mon cœur … »), cancelled by diagonal strokes
- [ ] 80 p25 | skipped | Is this German autobiographical text in his own hand (it reads as his own account: his life, a correspondence since the 1940s, his childhood), and if so should pp. 21, 23, 25, 29 be transcribed and the register entry « writer and addressee not named » be changed? | Header: « photocopies of a handwritten letter in German, autobiographical and unrelated to the mathematics »; letters.json: direction « other », correspondent unknown | Photocopy of a double page numbered « 5 », German handwriting that looks like his, with « Spontaneität der Untersuchung », « Periode meines Lebens », « Briefwechsel mit H…ka seit 19?2 », « bis zu ihrem Tod », « zurück in meine Kindheit »
- [ ] 18 p1 | skipped | Should his provenance line be carried in the reading (as a \note), and is the name written in full? | Only in the header comment: « Papiers donnés à Saav[edra] » | One pencil line at the head of an otherwise blank back: « Papiers donnés à Saavedra », the name apparently written out

Cannot tell — a reader may wish to look, low stakes:

- [ ] 5 p37 | skipped | Whose pen made the corrections on this typed EGA-style leaf (page number « – 18 – », « t » added to « ramènent », underlines, the 7 of (17.5.7))? | Header: pp. 33, 35, 37, 39 « carry no mathematics of his and are absent » | Typed half-page with half a dozen ink corrections
- [ ] 33 p174 | skipped | Is the ink correction « y_i = x_i/x_1 » his or the paper's author's? | Header: unrelated typescripts (papers in English) | One struck typed formula replaced in ink
- [ ] 122 p9 | skipped | Is the marginal cross beside exercise 5) his? | Header: typed leaves of Bourbaki draft n° 387 « with nothing of his » | A small « × » in the left margin
- [ ] 69 p1 | skipped | Is the pencil « (34p) » his page count for the run? | Header only: « a pencilled « (34p) » top right (a page count, not a heading, and not certainly his) » | Pencil « (34 p) » top right of a tan cover

Remarks for the coordinator (not review lines): 144 p. 105 is described in batch-06's header as « with only show-through », but it is a typed circular of 27 September 1978 (nothing of his on it). 144 p. 152: the archivists' pencil number on the leaf is 153.
