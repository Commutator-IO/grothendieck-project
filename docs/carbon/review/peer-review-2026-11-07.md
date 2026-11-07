# Peer-review working draft — CARBON-2026-11-07

> Simulated referee report, requested by the author on his own manuscript (docs/carbon/article.tex, draft of 7 November 2026). Local only. Working draft: the author must check every number and source before relying on it. No editorial decision is made or implied.

## Intake record

- Reviewer capacity: `author_requested_reader`
- Peer-review model: `open` (pre-submission reading; the venue's own model has not been applied)
- Declared processing plan: `approved_ai_assistance` (the author asked for an AI-assisted reading)
- Intake validated with the skill's `validate_review_intake.py`: READY_FOR_LOCAL_REVIEW.
- Competence limit: data-centre engineering (power draw of specific accelerators, PUE of specific sites).

# Comments to authors

## Evidence-bounded summary

The manuscript estimates the energy use and greenhouse-gas emissions of a three-month project in which one researcher used commercial language models (Claude Opus 5.5 and Sonnet 5.5, through Claude Code) to transcribe 9,414 pages of Grothendieck's working notes, write modernised readings, check statements in Lean and draft articles. Inputs are token counts logged by the tool for 24 September to 7 November 2026 (about 6.3 of 13.1 weeks), GitHub Actions run times, and published per-query figures. Tokens are weighted by relative price into "output-equivalent tokens", multiplied by an energy-per-token range and a grid-intensity range, then extrapolated to the whole project. The headline was about 300 kgCO2e for three months (40 to 1,200 kg). The result is compared with the professional footprint of researchers working on the same corpus.

## Strengths

- The question is new and well put: the cost of one concrete scholarly use, from start to finish, rather than training cost or a per-query anecdote.
- The inputs are real logs rather than guesses, and the token table separates output, cache writes and cache reads. That separation is what lets the paper say where the cost sits.
- Ranges are given instead of point values, and the text says plainly that they are not confidence intervals.
- The per-page section already says that a machine page and a human edition are not the same product.

## Major comments

### Major comment M1: the price weights do not match the published prices of the models used

- Location: Method, item 1; Data, Table 1; Results.
- Observation: The weights are output 1, cache write 0.25, cache read 0.02. Anthropic's pricing page (checked 7 November 2026) lists, for Opus 5.5, $20/MTok output, $5 (5-minute) or $8 (1-hour) cache writes and $0.20 cache reads; Sonnet 5.5 has the same ratios at half the price. The cache-read weight is therefore 0.01, not 0.02 (cache hits on these two models are priced at 0.05 of base input, not the usual 0.1). Cache writes are 0.25 or 0.40 depending on the cache duration, which the logs may or may not record.
- Evidence or criterion: Recomputation. With 1/0.25/0.01: Opus 107.3 M, Sonnet 12.6 M, total 119.9 M output-equivalent tokens. With 1/0.25/0.02 (the draft): 204.9 M. With 1/0.40/0.02: 219.1 M. The draft's 205 M is arithmetically right for its weights; the weights are what is off.
- Why it matters: Every downstream figure scales with this total. The draft's central estimate is about 1.7 times what the published prices give.
- Requested action: Use the published ratios as the main weighting (about 120 M), and carry the alternatives (up to about 220 M) into the range. Say in the text that price includes margin and demand and is only a proxy.

### Major comment M2: the extrapolation factor (×2 to ×3) is not supported, and the activity records point lower

- Location: Data, Model usage; Results, Table 2, row "whole project".
- Observation: The measured window is 44 of 92 days, so a constant pace gives ×2.09. The draft's ×2 to ×3 assumes the unmeasured weeks were at least as heavy. The repository suggests the opposite: 321 commits before 24 September against 1,996 after; 219k lines added to transcripts/ before against 432k after; the lean/ directory received no additions before 24 September.
- Evidence or criterion: `git log` counts on the repository (7 November 2026). Activity proxies give ×1.2 (commits) to ×1.5 (transcription lines); constant time gives ×2.1.
- Why it matters: The factor multiplies the headline. ×3 has no evidence behind it.
- Requested action: Use ×1.2 to ×2.5, central ×1.5, state the proxies, and keep a \todo for a direct measure (account usage history, if any exists for the earlier weeks).

### Major comment M3: the "central estimate" is not defined

- Location: Results, Table 2, last row; Abstract.
- Observation: "Total, central estimate ≈ 1,000 kWh, ≈ 300 kg" cannot be reproduced from the stated inputs. It corresponds to about 2 mWh per token, 0.3 kg/kWh and ×2.5, none of which is stated.
- Evidence or criterion: Reproducibility of every number in a table from stated inputs.
- Why it matters: Readers will quote the central figure; it must be traceable.
- Requested action: State the central parameters (here: price weights, 2 mWh, 0.3 kg/kWh, ×1.5) and the resulting values: about 240 kWh and 72 kg for the window, about 360 kWh and 110 kg for the project.

### Major comment M4: the continuous-integration estimate uses wall-clock time and misdescribes the workload

- Location: Data, Continuous integration; Method, item 4; Table 2.
- Observation: (a) Wall-clock time per run includes queueing and does not equal runner time. In a sample of 120 runs spread over the history (every tenth run on alternate pages of the API listing), summed job time was 14.3 h against 20.2 h of wall-clock time (ratio 0.71), so about 280 runner-hours for 2,346 runs rather than 450. (b) 102 of the 120 sampled runs were "Deploy to GitHub Pages" (site build, transcript rendering, TeX compilation); 17 were "lean". "Mostly Lean builds against mathlib" does not match. (c) Benaben et al. (2024) is a method for computing a per-core-hour factor for an HPC centre, not a published value, and it is built on French data centres; it does not give a number for a GitHub runner. (d) The 45 kWh implies an unstated 100 W per runner.
- Evidence or criterion: GitHub API, `actions/runs/{id}/jobs`; GitHub documentation: a standard Linux runner for public repositories has 4 vCPUs and 16 GB.
- Why it matters: CI is small in all cases, but the paper's credibility rests on traceable inputs.
- Requested action: Use about 280 runner-hours, a stated power range per runner share (here 20 to 100 W, overhead included, as an assumption to be sourced), give 6 to 28 kWh and 1 to 11 kg, describe the workload correctly, and cite Benaben et al. for the method only. Keep the \todo for the full API timing.

### Major comment M5: the Mistral cross-check is mis-scoped and missing from the article

- Location: Method, item 5 (scope); Limits.
- Observation: The issue's cross-check uses Mistral's 1.14 gCO2e per 400-token response "including training and hardware". Mistral's page calls it the "marginal impacts of inference" for a Le Chat response; it includes hardware manufacturing and non-GPU electricity, and it does not say it includes training. The article announces that manufacturing and training are "discussed separately" but never discusses them.
- Evidence or criterion: Mistral AI, 22 July 2025, "Our contribution to a global environmental standard for AI".
- Why it matters: Applied per output-equivalent token, 1.14 g/400 tokens gives 0.34 to 0.63 t for the window, several times the energy-only central value. That gap is informative (hardware manufacturing weighs a lot) and should be in the paper.
- Requested action: Add the cross-check with the correct scope and say why it is higher.

### Major comment M6: the comparison with researchers states its ranges too narrowly

- Location: Section "Scale".
- Observation: "Between a fraction of one researcher-year and one researcher-year, a few percent of the community's own footprint". On the draft's own numbers the three months are 0.04 to 1.2 t against 2 to 5 t per researcher-year, i.e. 1 % to 60 %; the annualised pace is 0.15 to 6 t against a community of 4 to 75 t, i.e. 0.2 % to more than 100 %. "A few percent" holds only at the centre. The per-person figure is a hypothesis, while a verified figure exists: Mariette et al. (2022) report 3.6 tCO2e per lab member on average (3.1 without the non-CO2 effects of aviation), across more than a hundred French laboratories; De Paepe et al. (2024), adding purchases, report a median of 5.6 t.
- Evidence or criterion: Arithmetic from the stated ranges; Mariette et al. abstract (Crossref); De Paepe et al. (2024).
- Why it matters: A digital-humanities readership, and the ACNB's answer that prompted the article, will read this comparison closely. A range that only works at its centre will be read as advocacy.
- Requested action: Give the full ranges, anchor the per-person figure in Mariette et al., and say that the comparison is of orders of magnitude.

### Major comment M7: the per-page comparison can be read as a claim that human transcription is replaceable

- Location: Section "Scale", last paragraph.
- Observation: The text prices a human page at "several kilograms" against 30 g for a machine page. The disclaimer that follows is good, but the numbers come first and dominate. Two further points: (a) the human figure attributes a researcher's whole professional footprint (travel, buildings, purchases) to transcription, which is an allocation, not the marginal cost of transcribing; (b) the machine pages still need human checking, so the machine cost adds to the human cost rather than replacing it.
- Evidence or criterion: The issue's own instruction: the article "should not suggest that human teams are too slow or out of reach".
- Why it matters: This is the paragraph most likely to be quoted out of context.
- Requested action: State (a) and (b) explicitly, give the machine per-page figure as an upper bound (all inference is divided by transcribed pages, though part of it went to Lean and articles), and frame the human figure as an allocation that does not measure the value of the work.

## Minor comments

### Minor comment m1: grid intensity and PUE are conflated

- Location: Method, item 3.
- Observation: "0.2 to 0.4 kgCO2e/kWh, data-centre overhead included." PUE multiplies energy, not intensity.
- Evidence or criterion: Elsworth et al. (2025) count PUE and idle capacity in the energy per prompt.
- Why it matters: Double counting or omission is possible.
- Requested action: Say that the energy range is at the facility level (overhead and idle capacity included) and that the intensity is that of the grid.

### Minor comment m2: the 2030 Shift Project figure is for data centres, not "the sector"

- Location: Section 1.
- Observation: The 920 MtCO2e a year by 2030 concerns data centres worldwide, under current trends.
- Evidence or criterion: The Shift Project, report page of 1 October 2025.
- Why it matters: Misattribution of a cited figure.
- Requested action: Rephrase.

### Minor comment m3: the anchors of the 0.5 to 5 mWh range are not cited and are not per token

- Location: Method, item 2.
- Observation: Google's 0.24 Wh (May 2025) is per median prompt, token count unstated; Epoch AI's 0.3 Wh assumes GPT-4o and 500 output tokens, i.e. about 0.6 mWh per output token, and rises to about 2.5 Wh for a 10,000-token input and about 40 Wh for 100,000.
- Evidence or criterion: Elsworth et al. 2025 (arXiv:2508.15734); You 2025 (Epoch AI).
- Why it matters: The long-context figures matter here: this project's sessions run on long contexts.
- Requested action: Cite both and say how they anchor the low end.

### Minor comment m4: Haiku 5.5 appears in the project description but not in the token table

- Location: Section 2 \todo; Table 1.
- Observation: Haiku 5.5 is listed as used; no Haiku tokens are given.
- Evidence or criterion: Consistency between sections.
- Why it matters: Either the usage is negligible or it is missing.
- Requested action: Add it or say it is negligible (author).

### Minor comment m5: the laptop's energy is understated

- Location: Table 2, row "Laptop, website".
- Observation: "A few kWh": a laptop drawing 20 to 40 W for 8 h a day over 92 days uses 15 to 30 kWh. On the French grid that is still under 5 kg, but its manufacturing share is larger and excluded.
- Evidence or criterion: Arithmetic.
- Why it matters: Small, but a reader can check it.
- Requested action: Give 15 to 30 kWh and say the manufacturing share is excluded.

### Minor comment m6: water is mentioned in the issue but left without figures

- Location: Limits.
- Observation: The two published per-response water figures differ by more than a hundredfold (Google 0.26 mL per median prompt, Mistral 45 mL per 400-token response).
- Evidence or criterion: The two sources.
- Why it matters: It explains why no water figure is given.
- Requested action: Say so in Limits.

## Methods, statistics, and reproducibility

The estimate is a product of four uncertain factors (weighted tokens, energy per token, grid intensity, extrapolation). Ranges are formed by multiplying extremes, which is the right conservative choice for a first estimate, but the paper should say so. The cache-read share of the weighted total is 63 % to 83 % depending on the weights, so the claim that re-reading long contexts dominates holds under every weighting tested; it would fail only if cache reads cost well under 1 % of an output token in energy. A sensitivity sentence would make that visible. Reproducibility would gain from publishing the script that de-duplicates the usage records and the API query for CI times (as a supplement).

## Ethics, transparency, figures, tables, and citations

- The ACNB's answer is referred to without naming anyone; keep it that way.
- No figure in the draft. A chart of carbon by item with ranges, one of tokens by kind and one of the comparison would help readers see the orders of magnitude without reading the tables.
- Citations: see docs/carbon/review/citations-2026-11-07.md.
- The statement on AI use is still a \todo; the venue's policy must be checked first (the README says so).

## Limitations of this review

Numbers were recomputed from the inputs stated in the draft and in issue #121; the usage records themselves were not re-read. The CI sample is 120 runs, not the full set. Power figures for GitHub runners are assumptions, not measurements.

# Confidential comments to editor

## Reviewer disclosures

- Conflicts and editor clearance: none identified; the review was requested by the author.
- Competence limits or specialist review needed: data-centre engineering.
- Assistance or tools used and required disclosure: AI-assisted (Claude Code), at the author's request.
- Confidentiality or retention issue: none; the file stays in the author's repository.

## Editorial-process or integrity concerns

None.
