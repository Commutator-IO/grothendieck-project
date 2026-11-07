import Buffalo.Topos.Part06a
import Buffalo.Topos.Part06b
import Buffalo.Topos.Part06c
import Buffalo.Topos.Part06boards

/-!
# Buffalo, topos theory, part 6 (10–12 July 1973)

The entries of lines 831–964 of `docs/buffalo-topos/index.tex` (video `4gynb9uTEE4`,
4:14:44–7:34:39, and video `ORG14LNb5gE`, 0:00:05–0:23:02), split into three files: `Part06a`
(accessible functors, objects and categories, `Set^op`, `Ind`, cardinal filtrations), `Part06b`
(strictly generating functors, finite-limit theories, finitely presented objects, Lawvere theories,
Birkhoff, pseudo-topoi and classifying topoi), `Part06c` (morphisms of sites, the classifying topos
`Ĉ`, subtopoi). Status of every entry: `docs/buffalo-topos/lean/Part06.json`.

Corrected entries:
* 4gynb9uTEE4-16076 and the second 4gynb9uTEE4-16213: stability of accessible functors under
  limits computed argumentwise holds with values in `Set` (`limit_isCardinalAccessible`,
  `limit_isAccessible`), not for an arbitrary target.
* 4gynb9uTEE4-19371: `Ind_π(C) → E` is an equivalence when `C` is stable under *colimits* with at
  most `π` arrows, not limits (`empty_not_filtered_colimit_of_punit`, `limit_of_punit_unique`).
* 4gynb9uTEE4-19433: a colimit is the colimit of the partial colimits, not a limit of partial
  limits (`isColimit_partialCoproducts`).
* 4gynb9uTEE4-21201: a small strictly generating family of `Set^op` exists iff there is no proper
  class of measurable cardinals (Isbell): not a theorem of ZFC.
* 4gynb9uTEE4-22501: `Ind(Σ₀) → S` is fully faithful if `Σ₀ ⊂ S_fp`, not only if
  (`top_not_isFinitelyPresentable`).
-/
