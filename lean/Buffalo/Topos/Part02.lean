import Buffalo.Topos.Part02a
import Buffalo.Topos.Part02b
import Buffalo.Topos.Part02c
import Buffalo.Topos.Part02d

/-!
# Buffalo, topos theory, part 2 (18 and 25 May 1973)

The entries of lines 248–389 of `docs/buffalo-topos/index.tex` (video `URU5jgTvjhU`,
5:39:20–9:25:54), split into four files by section: `Part02a` (étale morphisms, ring and field
objects, constant sheaves, internal Hom and the subobject classifier), `Part02b` (infinite
products, connectedness, torsors, stacks, gluing), `Part02c` (irreducible closed sets, sober
spaces, fibre functors as points of the site `𝒪(X)`), `Part02d` (functors commuting with colimits,
Giraud's definitions, first examples of topoi). Status of every entry:
`docs/buffalo-topos/lean/Part02.json`.

Corrections made to the index:
* URU5jgTvjhU-28459 [def]: « not a union of two distinct closed subsets » is never satisfied
  (`isIrreducibleLiteral_false`); it now reads « two closed subsets distinct from `Z` ».
* URU5jgTvjhU-25503 [prop]: « compact » now reads « compact Hausdorff » (`stone_epi_iff`,
  `stone_prod_epi`), as for Part01 key 17712.
* URU5jgTvjhU-25307 [disc]: a counterexample to products of epimorphisms *does* exist on the line
  (`product_of_epis_not_epi`); the entry said the lecturer found none there.
-/
