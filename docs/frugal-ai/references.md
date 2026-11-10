# References of the Inria MOOC on frugal AI (issue #116)

Course: Inria MOOC on FUN, `course-v1:inria+41033+session01`. The course page is behind the platform's login; the list below is the one Michel copied from it into a comment on #116 (sections 1.2 to 1.4 of the course's bibliography). Each entry was checked at its source on 7 November 2026: Crossref for the DOIs, DataCite for the arXiv identifiers, the publisher's or author's page otherwise. "Checked" means the title, authors and year below match the source; it does not mean the reference is cited in the books.

The figures of the books' chapters on frugal AI (#116) come from the carbon article (`docs/carbon/article.tex`) and its bibliography. Since 10 November 2026 the chapters also cite seven of the references below, each re-read at its source that day, and only for what was read there:

| Reference | Cited in | For what | Read on 10 Nov 2026 |
|---|---|---|---|
| Paris Agreement (2015), art. 2(1)(a) | *Mathématiques outillées*, « Compter ce que coûte le calcul », § Les chiffres du projet | the goal: well below 2 °C, pursuing 1.5 °C | French text in the EU Official Journal, L 282, 19 Oct 2016 (https://eur-lex.europa.eu/legal-content/FR/TXT/?uri=CELEX:22016A1019(01)); the UNFCCC PDF is a scan with no text layer |
| Millar et al. 2017 | same section | remaining budget for 1.5 °C in 2100: net cumulative CO2 after 2015 unlikely below 250 GtC, unlikely above 540 GtC, with ambitious non-CO2 mitigation | abstract on nature.com (full text paywalled, not read) |
| Rogelj et al. 2018 | same chapter, § L'effet rebond | six models; scenarios with median warming below 1.5 °C in 2100 share a rapid shift away from fossil fuels, reduced energy use and CO2 removal | abstract on nature.com (full text paywalled, not read) |
| Steffen et al. 2015 | same chapter, § Les chiffres du projet; *Archives outillées*, « Le coût d'une page lue », § Les inconnues | climate change is one of nine processes, freshwater another: what a carbon figure leaves out | abstract (OpenAlex) and the journal's summary (Crossref); science.org returns 403 to automated requests, full text not read. The list of the nine is on the Stockholm Resilience Centre page (https://www.stockholmresilience.org/research/planetary-boundaries.html) |
| Meadows 1999, *Leverage Points* | *Mathématiques outillées*, § Ne pas demander au modèle; *Archives outillées*, § Choisir ce qu'on lit | parameters are last of twelve leverage points, the goals of the system third from the top | full essay on the Donella Meadows Project site (https://donellameadows.org/archives/leverage-points-places-to-intervene-in-a-system/, dated there 19 October 1999), a better host than the third-party PDF below |
| Wan et al. 2025 (Foundation Model Transparency Index) | *Mathématiques outillées*, § Où part l'énergie; *Archives outillées*, § Les inconnues | 13 companies scored; 10 disclose none of the key information on the environmental impact of building their models; per-interaction figures judged insufficient | full text, arXiv HTML v1, section 5.1 |
| Slattery et al. 2026 (AI Risk Repository) | *Archives outillées*, § Répondre à l'objection | 1,725 risks from 74 frameworks, seven domains and 24 subdomains; environmental harm is subdomain 6.6, mentioned by 38 % of documents | full text, arXiv PDF v3 |

*Mathématiques outillées* lists the six it cites in its reading annex (`docs/livre-methodes/chapitres/annexe-lectures.tex`, « Compter ce que coûte le calcul »); *Archives outillées* has no reading annex and gives the links inline.

Kept for later reading, not cited: the UNEP *Emissions Gap Report 2025* (its pages return 403 to automated requests, so no figure could be read at source); Mora et al. 2017 and Andre et al. 2024 (deadly heat, support for climate action: no argument of the chapters rests on them); the IPCC website and the Sismique podcast (no specific passage); the general AI references of sections 1.2 and 1.3 (Konieczny & Prade, Russell & Norvig, the Hugging Face course, Jurafsky & Martin, Vaswani et al.), which belong to an introduction to the models rather than to their cost.

## 1.2 AI in general

| Reference | Link | Check (7 Nov 2026) |
|---|---|---|
| Konieczny, S. & Prade, H. (coord.), *L'Intelligence artificielle. De quoi s'agit-il vraiment ?*, GDR IA (CNRS). | https://ia.gdria.fr/ | Page answers. It says « Ouvrage coordonné par Sébastien Konieczny et Henri Prade », CC BY-NC-ND 4.0, preliminary web version of a book published by Cépaduès. The page gives no year (its metadata dates it 2020); the year 2023 of the course list was not confirmed. |
| Russell, S. & Norvig, P., *Intelligence artificielle : une approche moderne*, 4e édition, Pearson, 2021. | https://www.pearson.fr/resources/download.cfm?GCOI=27440100440640&thefile=F0221_Chap1.pdf | The link serves chapter 1 (« Introduction ») of the French edition as a PDF, titled « Intelligence artificielle : une approche moderne ». Year and edition not printed on the extract; taken from the course list. |

## 1.3 Deep learning and generative AI

| Reference | Link | Check (7 Nov 2026) |
|---|---|---|
| Hugging Face, *LLM Course*, chapter 1, n.d. | https://huggingface.co/learn/llm-course/en/chapter1/1 | Page answers (« Introduction »). |
| Jurafsky, D. & Martin, J. H., *Speech and Language Processing*, 3rd ed. draft, Stanford University. | https://web.stanford.edu/~jurafsky/slp3/ | Page answers: « 3rd ed. draft », current release dated 19 August 2026. |
| Slattery, P., Saeri, A. K., Grundy, E. A. C., Graham, J., Noetel, M., Uuk, R., Dao, J., Pour, S., Casper, S. & Thompson, N., « The AI risk repository: A meta-review, database, and taxonomy of risks from artificial intelligence », *Patterns* 7(5), 101517, 2026. | https://doi.org/10.1016/j.patter.2026.101517 (preprint https://arxiv.org/abs/2408.12622) | Crossref: Patterns 7(5), article 101517, May 2026. DataCite: arXiv 2408.12622, ten authors, first Slattery, last Thompson, linked to the Patterns DOI. |
| Vaswani, A., Shazeer, N., Parmar, N., Uszkoreit, J., Jones, L., Gomez, A. N., Kaiser, Ł. & Polosukhin, I., « Attention Is All You Need », arXiv, 2017. | https://arxiv.org/abs/1706.03762 | DataCite: eight authors, 2017. |
| Wan, A., Klyman, K., Kapoor, S., Maslej, N., Longpre, S., Xiong, B., Liang, P. & Bommasani, R., « The 2025 Foundation Model Transparency Index », arXiv, 2025. | https://arxiv.org/abs/2512.10169 | DataCite: eight authors, first Wan, last Bommasani, 2025. |

## 1.4 The environmental crisis

| Reference | Link | Check (7 Nov 2026) |
|---|---|---|
| Intergovernmental Panel on Climate Change (IPCC), website. | https://www.ipcc.ch/ | Page answers in a browser (automated requests get 403). |

### 1.4.A Carbon and climate

| Reference | Link | Check (7 Nov 2026) |
|---|---|---|
| Millar, R. J., Fuglestvedt, J. S., Friedlingstein, P., Rogelj, J., Grubb, M. J., Matthews, H. D., … & Allen, M. R., « Emission budgets and pathways consistent with limiting warming to 1.5 °C », *Nature Geoscience* 10(10), 741–747, 2017. | https://doi.org/10.1038/ngeo3031 | Crossref: matches (ten authors, last Allen). |
| Mora, C., Dousset, B., Caldwell, I. R., Powell, F. E., Geronimo, R. C., Bielecki, C. R., … & Trauernicht, C., « Global risk of deadly heat », *Nature Climate Change* 7(7), 501–506, 2017. | https://doi.org/10.1038/nclimate3322 | Crossref: matches (eighteen authors, last Trauernicht). |
| Rogelj, J., Popp, A., Calvin, K. V., Luderer, G., Emmerling, J., Gernaat, D., … & Tavoni, M., « Scenarios towards limiting global mean temperature increase below 1.5 °C », *Nature Climate Change* 8(4), 325–332, 2018. | https://doi.org/10.1038/s41558-018-0091-3 | Crossref: matches (23 authors, last Tavoni). |

### 1.4.B Analysing socio-environmental crises

| Reference | Link | Check (7 Nov 2026) |
|---|---|---|
| Andre, P., Boneva, T., Chopra, F. & Falk, A., « Globally representative evidence on the actual and perceived support for climate action », *Nature Climate Change* 14(3), 253–259, 2024. | https://doi.org/10.1038/s41558-024-01925-3 | Crossref: matches. |
| Meadows, D. H., *Leverage Points: Places to Intervene in a System*, Sustainability Institute, 1999. | https://peaceworkersus.org.hudevbooks.net/media/documents/donella-meadows-article-on-leverage-points.pdf | The PDF answers and is the essay (« Leverage Points. Places to Intervene in a System, by Donella Meadows »). The « 19, 28 » of the course list is not a volume and page; dropped. The host is a third-party copy, not the publisher. |
| Meadows, D., « The limits to growth », *Sismique*, episode 77 (podcast), November 2021. | https://www.sismique.fr/episodes/77-dennis-meadows-the-end-of-growth | Page answers: « #77 – Interview The limits to growth », Dennis Meadows, published 2 November 2021, recorded 20 September 2021, 58:33. |
| Steffen, W., Richardson, K., Rockström, J., Cornell, S. E., Fetzer, I., Bennett, E. M., … & Sörlin, S., « Planetary boundaries: Guiding human development on a changing planet », *Science* 347(6223), 1259855, 2015. | https://doi.org/10.1126/science.1259855 | Crossref: matches (eighteen authors, last Sörlin). |
| United Nations Environment Programme, *Emissions Gap Report 2025: Off Target*, 2025. | https://www.unep.org/resources/emissions-gap-report-2025 | Page answers in a browser (redirects to `/en/publications/report/emissions-gap-report-2025`; automated requests get 403). The page gives « Emissions Gap Report 2025: Off Target », sixteenth edition, author UNEP. The longer subtitle of the course list was not seen on the page. |
| United Nations Framework Convention on Climate Change, *Accord de Paris*, 2015. | https://unfccc.int/files/essential_background/convention/application/pdf/french_paris_agreement.pdf | The link of the course list (`https://unfccc.int/sites/default/files/french_paris_agreement.pdf`) returns 404. The address above serves the PDF as a download; its content was not opened. |

The `?utm_source=chatgpt.com` suffixes of the course list were removed from the links.
