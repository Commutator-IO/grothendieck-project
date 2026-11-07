# Citation check — docs/carbon/article.bib, 7 November 2026

Every entry was checked against a canonical record (Crossref for DOIs, the HAL API for HAL documents, arXiv, the publishers' or organisations' own pages). Each in-text claim was checked against the source text or its abstract. Status: OK, FIXED (metadata or claim corrected), ADDED (new entry, verified).

## Entries already in the draft

| Key | Canonical record | Metadata | Claim in the article | Status |
|---|---|---|---|---|
| ligozat2022 | Crossref 10.3390/su14095172 | Sustainability 14(9), 5172, 2022; four authors match | LCA of AI services, hidden impacts of "AI for Green"; full life cycle (abstract) | OK |
| luccioni2023 | HAL hal-04288059; JMLR 24(253):1–15, 2023 | Matches | Training footprint of BLOOM measured (24.7 t dynamic, 50.5 t full life cycle) | OK |
| baillot2025 | Crossref 10.4000/1498x | "Introduction. Sobriété numérique", Humanités numériques 11, 2025, Baillot and Ligozat | Special issue on digital sobriety | OK |
| ligozat2024targets | Crossref 10.1101/2024.03.11.584380 (posted content, bioRxiv); HAL hal-04505199 | Nine authors match; still a preprint, no journal version found | Climate targets for higher education and research | OK (HAL id added) |
| benaben2024 | HAL hal-04738556, report, January 2024 | Five authors match; HAL lists no institution | The draft used it for "the footprint of an hour on a CPU core". The report is a method for deriving a per-core-hour factor in a computing centre; it gives no value usable for a GitHub runner, and its example grid factor is French (0.0599 kgCO2e/kWh) | FIXED: entry made @misc (no false "institution = HAL"); cited for the method only |
| morand2026 | HAL hal-04839926 v6, 24 October 2026, EMNLP 2026 | Three authors match | Training impacts keep rising; efficiency gains do not curb them (rebound) | OK (HAL version noted) |
| mariette2022 | Crossref 10.1088/2634-4505/ac84a4 | ERIS 2(3), 035008, 2022; fifteen authors (the draft had "and others") | Abstract: over a hundred French labs; average 3.6 tCO2e per lab member, 3.1 t without the indirect radiative effects of aviation | FIXED: full author list, article number; figure now quoted in the text |
| shift2018 | theshiftproject.org page dated 4 October 2018 | Title matches | Page: the sector's share "passant de 2,5 % à 3,7 % du total des émissions mondiales" since 2013; energy "en hausse de 9 % par an". The page does not itself label 3.7 % as the 2018 value | FIXED: sentence now says the 2018 report estimated a rise from 2.5 % (2013) to 3.7 % |
| shift2025 | theshiftproject.org page dated 1 October 2025 | Title matches | 920 MtCO2e a year in 2030 is for **data centres** under current trends (manufacture and construction included), not for "the sector" in general | FIXED: sentence now names data centres and the trend scenario |

## Per-query figures in the method (added after verification)

| Key | Source | Verified figures | Status |
|---|---|---|---|
| elsworth2025 | arXiv:2508.15734, 21 August 2025, Elsworth, Huang, Patterson, … Dean, Vahdat, Gomes, Manyika (12 authors) | Median Gemini Apps text prompt, May 2025: 0.24 Wh, 0.03 gCO2e (market-based), 0.26 mL water; boundary includes accelerators, host CPU and DRAM, idle machines and data-centre overhead (PUE). Tokens per prompt not given | ADDED |
| you2025epoch | Epoch AI, Gradient Updates, Josh You, 7 February 2025 | About 0.3 Wh for a typical GPT-4o query, assuming 500 output tokens; about 2.5 Wh for 10,000 input tokens and almost 40 Wh for 100,000 | ADDED |
| mistral2025 | Mistral AI news, 22 July 2025, with Carbone 4 and ADEME, reviewed by Resilio and Hubblo | Mistral Large 2. "Marginal impacts of inference" for a 400-token Le Chat response: 1.14 gCO2e, 45 mL water, 0.16 mg Sb eq; includes hardware manufacture and non-GPU electricity, excludes user terminals. Training plus 18 months of use: 20.4 ktCO2e, 281,000 m³ water | ADDED. Correction to issue #121: the per-response figure is not stated to include training |
| depaepe2024 | Crossref 10.1371/journal.pstr.0000116, PLOS Sustainability and Transformation 3(7), 2024 | 108 French labs; median 5.6 tCO2e per person (mean 6.2), about half from purchases | ADDED (supports the per-person range) |
| anthropicpricing | platform.claude.com pricing page, consulted 7 November 2026 | Opus 5.5: output $20, 5-min write $5, 1-h write $8, cache read $0.20 per MTok; Sonnet 5.5 half of each. Ratios 1 / 0.25 (0.40) / 0.01 | ADDED (corrects the cache-read weight from 0.02 to 0.01) |

## Other facts checked

- GitHub-hosted standard runner for public repositories, Linux: 4 processors, 16 GB (docs.github.com, runners reference). Stated in the text without a citation; add one if the journal wants it.
- CI run times: sample of 120 runs through the GitHub API (jobs endpoint), 14.3 h of job time against 20.2 h of wall-clock time.

## Not cited, left for the author

- A published power figure for a 4-vCPU cloud virtual machine (\todo in Method, item 5).
- Per-discipline figures from Labos 1point5 for mathematics and history (\todo).
- No source was found that reports Anthropic's energy per token or data-centre regions (\todo).

All URLs and DOIs above were resolved on 7 November 2026.
