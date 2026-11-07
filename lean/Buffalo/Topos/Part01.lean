import Buffalo.Topos.Part01a
import Buffalo.Topos.Part01b
import Buffalo.Topos.Part01c
import Buffalo.Topos.Part01d
import Buffalo.Topos.Part01boards

/-!
# Buffalo, topos theory, part 1 (4 April and 11 May 1973)

The entries of lines 99–247 of `docs/buffalo-topos/index.tex` (video `URU5jgTvjhU`,
0:03:26–5:34:24), split into four files by section: `Part01a` (presheaves, sheaves, limits,
the associated sheaf, quotients), `Part01b` (torsors, generators, abelian sheaves), `Part01c`
(direct and inverse images, stalks and epimorphisms), `Part01d` (algebraic structures on objects).
Status of every entry: `docs/buffalo-topos/lean/Part01.json`.

One entry was found false: URU5jgTvjhU-17712 (« for `X` compact, `Γ` sends epimorphisms to
surjections iff `X` is totally disconnected ») fails for the Sierpiński space, which is compact,
connected, and on which `Γ` preserves epimorphisms (`sierpinski_counterexample`); the entry now
reads « compact Hausdorff » (Bourbaki's « compact »).
-/
