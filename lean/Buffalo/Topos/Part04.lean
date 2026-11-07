import Buffalo.Topos.Part04a
import Buffalo.Topos.Part04b

/-!
# Buffalo, topos theory, part 4 (6, 20 and 27 June 1973)

The entries of lines 536–678 of `docs/buffalo-topos/index.tex` (video `PqCQM3Pcl6Q`,
3:23:52–8:58:56), split into two files: `Part04a` (Galois theory of coverings, `f_!` and `f^!`,
sites, sheaves on a site, the associated sheaf) and `Part04b` (exactness properties, `Cat_D`,
2-fibre products, examples of `D`, algebraic theories). Status of every entry:
`docs/buffalo-topos/lean/Part04.json`.

One entry was found imprecise: PqCQM3Pcl6Q-20146 (« a conjunction of exactness properties
`(I_λ, Σ_λ)` is one exactness property `(I, Σ)`, `I` the 2-sum »). Satisfying every `(I_λ, Σ_λ)`
implies satisfying `(I, Σ)` (`satisfiesExactness_twoSum_of_forall`), but the converse needs every
`I_μ` to admit some `D`-functor to `C` (`forall_of_satisfiesExactness_twoSum`): otherwise `(I, Σ)`
holds vacuously, as for `Set` when `D` contains the empty limit and colimit
(`no_initial_terminal_set`).
-/
