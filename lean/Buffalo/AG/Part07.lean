import Buffalo.AG.Part07a
import Buffalo.AG.Part07b
import Buffalo.AG.Part07c

/-!
# Buffalo, algebraic geometry, part 07: 26 June 1973 (from 5:24:53) – 3 July 1973 (to 10:16:56)

The entries of `docs/buffalo-ag/index.tex` lines 907–1053 (video `Oqhr-Gt66es`, 5:24:53–10:16:56),
split by session into `Part07a` (26 June: geometric integrality and connectedness;
subschemes and coherence), `Part07b` (2 July: limits, projective and proper morphisms, valuative
criteria, integral and finite morphisms) and `Part07c` (3 July: finite, quasi-affine, radicial,
open and generalizing morphisms), all in the namespace `Buffalo.AG.Part07`. The status of each
entry is in `docs/buffalo-ag/lean/Part07.json`.

Main results proved here: `k` is algebraically closed iff `k' ⊗_k k'` is a domain for every
finite extension `k'` (`prop_19691`), and separably closed if `Spec(k' ⊗_k k')` is connected for
every finite Galois `k'` (`prop_20796`); filtered limits of rings with connected spectra (`prop_21188`) and of nonzero rings
(`prop_36375`); `(∏ ℤ)[1/2] → ∏ ℤ[1/2]` is not onto (`cex_24017`); separated quasi-finite
morphisms are quasi-affine (`prop_34060`); integral radicial surjective morphisms are universal
homeomorphisms (`prop_35012`); the generic point of the affine line is not open (`cex_36503`); the
normalization of the cusp is integral and surjective (`ex_35209`).

Not formalised (no carrier in mathlib): the projective bundle `ℙ(E)` of a quasi-coherent module,
ample and very ample invertible sheaves, the Picard group of a scheme, Chow's lemma, complex
analytic spaces, the gluing of `ℤ` copies of a curve and the normalization of the nodal curve.
-/
