import Buffalo.Topos.Part07a
import Buffalo.Topos.Part07b
import Buffalo.Topos.Part07c
import Buffalo.Topos.Part07boards

/-!
# Buffalo, topos theory, part 7 (12 July 1973)

The entries of lines 965–1114 of `docs/buffalo-topos/index.tex` (video `ORG14LNb5gE`,
0:32:47–6:09:46), the last part of the course, split into three files: `Part07a` (generating
subcategories, strictly and universally epimorphic families, the counterexamples in groups,
subtopoi of `Sh(C, τ)`), `Part07b` (the classifying topos of objects and its subtopoi at the level of
points, flat functors, `B_G` and contracted products, torsors, elementary topoi, flatness,
hypertopoi, universes), `Part07c` (properties not stable under filtered colimits, faithful
actions, topoi without points). Status of every entry: `docs/buffalo-topos/lean/Part07.json`.

Corrected entries:
* ORG14LNb5gE-13696: sets with `n` elements are not stable under filtered colimits only for
  `n ≥ 2` (`rank_not_stable`); for `n = 1` they are (`singleton_stable`).
* ORG14LNb5gE-14022: « having exactly `n` connected components » fails to be stable under
  filtered colimits for `n ≥ 2` (`components_not_stable`); for `n = 1` it is connectedness, which
  defines a subtopos (entry 13957).
-/
