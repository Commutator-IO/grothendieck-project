import Buffalo.AG.Part04d

/-!
# Buffalo, algebraic geometry, part 04: 12–18 June 1973

The entries of `docs/buffalo-ag/index.tex` lines 492–631 (video `thSz9ZHDK9o`, 1:39:49–6:59:05),
split into `Part04a` (stalks, localization, local rings, `M ↦ M^~` and products, completion),
`Part04b` (locally ringed spaces, morphisms of spectra, the functor of points), `Part04c`
(18 June: `Γ ⊣ Spec`, schemes as Zariski sheaves, sums, epimorphisms, open immersions of sheaves
and the representability criterion) and `Part04d` (gluing, lines and hyperplanes, invertible
modules, the functor `𝐏(V)` and its charts), all in the namespace `Buffalo.AG.Part04`. The status
of each entry is in `docs/buffalo-ag/lean/Part04.json`.

Corrected entry: 23835 (`M` with `M ⊗ L ≅ A` is unique up to a unique isomorphism only once the
isomorphisms `M ⊗ L ≅ A` are fixed: `prop_23835_unique`, `prop_23835_not_unique`).

Not formalised (no carrier in mathlib): the restriction of a big Zariski sheaf to the small site
of a scheme (17805), the functor `𝐏(V)` as a Zariski sheaf of invertible quotients of
quasi-coherent sheaves and its representability (24233, 24492).
-/
