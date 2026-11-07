import Buffalo.Topos.Part03a
import Buffalo.Topos.Part03b
import Buffalo.Topos.Part03c

/-!
# Buffalo, topos theory, part 3 (11 May, 30 May and 4 June 1973)

The entries of lines 390–535 of `docs/buffalo-topos/index.tex` (video `URU5jgTvjhU`,
9:27:02–11:04:45, and video `PqCQM3Pcl6Q`, 0:04:34–3:22:52), split into three files: `Part03a`
(points of topoi, `B_G`, fibre functors on `Sh(X)`, 2-cells between morphisms of spaces), `Part03b`
(morphisms of topoi and the 2-category of topoi, initial and final topoi, presheaf topoi, Giraud),
`Part03c` (sober spaces, Zariski-type topologies, algebra, ordered categories, very dense subsets,
equivariant étale spaces). Status of every entry: `docs/buffalo-topos/lean/Part03.json`.

Corrected entries:
* PqCQM3Pcl6Q-1011: a fibre functor of `Top(Y)` is represented by an object of `O_Y` exactly for
  the points with a smallest open neighbourhood, not only for open points
  (`sierpinski_closed_point`, `isIso_germ_of_smallest`).
* PqCQM3Pcl6Q-1445: the category of fibre functors is `Y` ordered by specialization only for `Y`
  sober (`point_classification`; counterexample `cofiniteGenericPoint_not_iso`).
* PqCQM3Pcl6Q-6421: the localization morphism `E/X' → E` is the analogue of an étale map, of an open
  immersion only when `X'` is subterminal (`overForget_not_full`, `quotient_not_mono`).
-/
