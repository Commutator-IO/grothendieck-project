import Buffalo.AG.Part06a
import Buffalo.AG.Part06c
import Buffalo.AG.Part06d

/-!
# Buffalo, algebraic geometry, part 06: 25 June 1973 (from 0:58:06) – 26 June 1973 (to 5:23:27)

The entries of `docs/buffalo-ag/index.tex` lines 770–906 (video `Oqhr-Gt66es`, 0:58:06–5:23:27),
split into `Part06a` (open and closed immersions, immersions), `Part06b` (discrete valuation rings,
reduced, integral, normal and regular schemes, surjective endomorphisms, classes of morphisms),
`Part06c` (diagonals, separated, quasi-separated and coherent morphisms) and `Part06d` (perfect and
separably closed fields, geometric reducedness and irreducibility), all in the namespace
`Buffalo.AG.Part06`. The status of each entry is in `docs/buffalo-ag/lean/Part06.json`.

Main results proved here: the equivalence of `Δ_g ∈ M`, of graphs in `M`, of kernels in `M` and of
sections of base changes in `M` for a class `M` stable under base change (`prop_10536`,
`prop_10860`), giving the equivalent forms of separated and quasi-separated morphisms
(`prop_13063`, `prop_14898`); the generators `bᵢ ⊗ 1 - 1 ⊗ bᵢ` of the diagonal ideal
(`prop_12804`); the characterisations of quasi-separated schemes by quasi-compact morphisms and
fibre products (`prop_15289`, `prop_15416`); the non-quasi-compactness of the punctured
`Spec k[t₀, t₁, …]` (`cex_15677`); the non-reducedness of `k' ⊗_k k'` for `k' = k[t]/(tᵖ - x)` and
the criterion for perfect fields (`not_isReduced_tensor`, `prop_16790`); the normalisations of the
node and the cusp (`ex_7280`, `ex_7347`).

Corrected entries: `8186` (principal ideal *domains*: `ℤ/4` is a principal ideal ring that is not
regular, `cex_8186`), `16396` (`S` must be coherent, not only quasi-separated, `cex_16396`).

Not formalised (no carrier in mathlib): the identity component of a group scheme (`6032`),
blow-ups (`7216`), Koszul complexes in general (`7990`, length one only), global dimension
(`8121`), regularity of completions and Cohen's structure theorem (`8250`, `8313`), the planes and
lines with doubled origin as glued schemes (`10987`, `14219`, `14762`), quasi-coherent
`𝒪_X`-modules and their (higher) direct images (`16474`, `16538`), and the irreducibility of
`Spec(K ⊗_k L)` over a separably closed field (`18360`).
-/
