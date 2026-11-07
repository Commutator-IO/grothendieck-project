import Buffalo.Topos.Part05a
import Buffalo.Topos.Part05b
import Buffalo.Topos.Part05c
import Buffalo.Topos.Part05d
import Buffalo.Topos.Part05boards

/-!
# Buffalo, topos theory, part 5 (late June, 2 July and 10 July 1973)

The entries of lines 679–830 of `docs/buffalo-topos/index.tex` (video `PqCQM3Pcl6Q`,
9:02:23–10:12:40, and video `4gynb9uTEE4`, 0:04:18–4:11:21), split into four files: `Part05a`
(adding arrows, combining theories, generating families, additive categories), `Part05b` (strict
cogeneration, accessible functors, representability and adjoints, morphisms of theories),
`Part05c` (exactness properties, limits in `T(C)`, envelopes, the saturation `Σ'` and its calculus
of fractions), `Part05d` (the corrections of 10 July, `Setᵒᵖ`, Boolean algebras).
Status of every entry: `docs/buffalo-topos/lean/Part05.json`.

One entry was found false: 4gynb9uTEE4-648 (« strict cogeneration is transitive »; the lecturer
retracted it on 10 July), refuted in a five-element lattice (`not_transitive`). One was found
imprecise: 4gynb9uTEE4-13448 (« `Setᵒᵖ` admits a strict generator, the two-element set »), true in
the sense of SGA 4 but not in the course's sense of strict generation (`no_limit_of_bools`).
-/
