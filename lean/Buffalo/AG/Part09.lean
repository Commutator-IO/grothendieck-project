import Buffalo.AG.Part09a
import Buffalo.AG.Part09b

/-!
# Buffalo, algebraic geometry, part 09: 10 July 1973 (from 4:22:15) – 11 July 1973 (to 6:57:40)

The entries of `docs/buffalo-ag/index.tex` lines 1191–1290, the end of the course, split by video
into `Part09a` (`vuys5SNs2eQ`, 4:22:15–5:39:27: effective descent for schemes, the radicial and
very ample cases, norms, descent and group actions) and `Part09b` (`3ULFIl_2Wis`, 5:30:39–6:57:40:
Galois descent, descent for families, the fpqc, fppf, Zariski and étale topologies, quotients), all
in the namespace `Buffalo.AG.Part09`. The status of each entry is in
`docs/buffalo-ag/lean/Part09.json`.

Main results proved here: on points, a gluing datum is a descent datum if and only if `X'' ⇉ X'`
is an equivalence relation, and it is then effective (`prop_15735`, `prop_16055`); over a
pseudo-torsor, descent data are actions of the group (`prop_20176`); a faithfully flat
quasi-compact radicial morphism is a universal homeomorphism (`prop_17754`); the canonical
topology is the topology of universally effective epimorphic sieves (`prop_23180`); `λ ↦ λ^n` has
no Zariski local section on `𝔾_m` (`cex_21857`); a morphism into `Spec B` from the spectrum of an
adically separated ring is determined by its reductions (`prop_23692`).

Not formalised (no carrier in mathlib): descent data of schemes and their effectivity, relative
ampleness and quasi-projectivity, norms of invertible sheaves, the limit argument of the finite
extension principle, Galois descent of schemes, the affine group scheme `Γ_k` and its torsors,
algebraic spaces and complex analytic spaces, quotients of schemes by finite locally free or flat
equivalence relations and of algebraic groups by subgroups.
-/
