---
name: contribute-to-mathlib
description: Proposes to Mathlib (leanprover-community/mathlib4) a general lemma that a Lean proof of this repository needed or proved — checks that the gap is real, writes it to Mathlib's conventions and style guide, compiles it against the project's pinned Mathlib without `lake build`, pushes a branch to the fork mycaule/mathlib4 and opens a draft PR, then handles CI and reviews. Use when someone asks to upstream a lemma from lean/Grothendieck/*.lean, open or fix a mathlib4 PR, improve the open PRs of issue #52, answer a review, or repair a PR's CI. Also covers bringing a merged PR back into the Lean appendix and the Findings tab.
---

# Contributing to Mathlib from this repository

The Lean proofs in `lean/Grothendieck/` (32 folders, about a thousand theorems) sometimes
need a general lemma Mathlib lacks. These make good PRs if they are presented the way Mathlib
expects. Tracking: issue #52 (one checkbox per candidate, with the PR number and its state).
PRs, titles, descriptions and commit messages are **in English**.

This skill gathers what the PRs of 10–12 October 2026 and their reviews taught. Read it whole
before the first change of a session.

## 0. What Michel does himself, always

Mathlib's AI rules (leanprover-community.github.io/contribute, read 2026-10-11) forbid
LLM-written GitHub and Zulip comments. So:

- **Never post** a PR comment, a review reply, a Zulip message, a `label` command, and never
  resolve a thread. Draft the text in the chat and let Michel post it in his own words.
- **Never change a PR's state**: draft → ready for review is Michel's, once CI is green.
- Editing a PR's **title and description** when the code changes is part of the fix, and
  allowed. So are commits on the PR's branch.
- The `LLM-generated` label is added by the bot or by Michel; it is expected.
- Michel is fine with many open PRs; do not advise him to close or merge them into fewer.

## 1. Check that the gap is real

A PR that duplicates a lemma or an open PR gets closed.

- **Mathlib master**, not the pinned version: Loogle knows master.

      curl -s -G 'https://loogle.lean-lang.org/json' --data-urlencode 'q=<name or pattern>'

  Search by name, by constants (`q=IsIso, "comp_eq_id"`), by substring. An empty answer
  proves nothing until a positive control on a neighbouring name that exists has returned it.
- **Open and closed PRs**: `gh search prs --repo leanprover-community/mathlib4 "<words>"`.
  Closed without merge often means "redone elsewhere" or "wrong approach": read the review.
  Cauchy–Binet is the example: #40473 and #44209 were closed because the reviewer
  (robin-carlier) wanted the exterior-power route, and #44757 was rewritten that way.
- Our own open PRs count too: a private helper in one PR that another PR makes public is a
  duplicate (#44760 had a private copy of #44759's `RCLike.sum_sum_norm_mul_sub_mul_sq_le`).
  Stack the PRs and use the public lemma.
- GitHub code search on mathlib4 is unreliable; prefer Loogle,
  `git show upstream/master:<file>` and `raw.githubusercontent.com`.

Say in the description what Mathlib already has: "Mathlib has X but not Y", with names checked
on Loogle. The reviewer sees at once that the search was done.

## 2. Write it the way Mathlib does

### Statement

- **As general as stays natural**: no unused hypothesis (the `unusedArguments` linter fails
  CI on an unused instance), the weakest typeclasses, the existing notions
  (`Function.Periodic`, `Set.Pairwise`, `𝓝[s] x`, `powersetCard`…) rather than a home-made
  `∀ i j, i ≠ j → …`.
- The **normal form** of the domain, the **right namespace**, the **most elementary file**
  that can hold it. A lemma that is only a step of a proof and has no use elsewhere may be
  `private`; a general one is public.
- **Attribution**: name Grothendieck upstream only where the statement really comes from a
  folder and is not standard, in one line of the PR description — « Proposition N of an
  unpublished manuscript of A. Grothendieck (Montpellier archive, cote X) » — never in a
  docstring and without page numbers. #44702 keeps its module-docstring References block
  (cote 158) by Michel's choice; do not strip existing references without asking. Never cite
  csg.igrothendieck.org.

### Style guide (leanprover-community.github.io/contribute/style.html)

Checked on every added line before pushing:

- lines of at most **100 characters** (count characters, not bytes: `awk length` is wrong on
  Unicode);
- `fun x ↦`, never `fun x =>` (`=>` stays in `match` arms), never `λ`, never `$`;
- **operators and `:=` at the end of a line**, never at the start of the next one (the first
  step of a `calc` written on its own line, `_ = …` steps, are fine);
- `by` at the end of the line, never alone on a line; 2-space proof indentation, 4-space
  continuation of a multi-line statement;
- one blank line between declarations, **no blank line inside a declaration**, no double
  blank lines;
- **comments: as few as possible.** Mathlib's linter (`docBlame`) requires a docstring on
  definitions, structures and their fields, not on theorems. Give a docstring to a definition,
  an instance carrying content, and the headline theorems (the ones the module docstring
  lists); give none to a routine lemma whose statement says it all. A docstring that restates
  the name or the statement (`/-- X is coprime to p iff … -/` over `isCoprime_X_iff`) is noise:
  vihdzp, on #44756, called such docstrings on trivial theorems "visual noise" and said AI
  has a tendency to comment all of its code. Likewise no `--` comment narrating a proof step
  that the next line shows; keep one only where a step is surprising (a workaround, a
  non-obvious choice). When a docstring is warranted it comes **before** the attributes:
  `/-- … -/` then `@[simp]` then `theorem` — a docstring after `@[simp]` is a parse error
  (it broke #44722's CI);
- no conjunction in hypotheses or conclusions (two lemmas instead);
- terminal `simp` not squeezed (do not replace a closing `simp` by its `simp?` output);
- named hypotheses: `have hp : p.Prime := Fact.out` rather than `rename_i hp`;
- `lia` for integer arithmetic, `field`, `fun_prop`, `grind` where they close the goal;
- header `Copyright (c) 2026 Michel Hua. All rights reserved.` / `Authors: Michel Hua`, then
  `module`, one block of `public import`, one of `import` (alphabetical), the `/-! # Title …
  ## Main statements -/` docstring, `public section` (`@[expose]` only with definitions);
- a new file is listed in `Mathlib.lean` at its alphabetical place; new bibliography entries
  go in `docs/references.bib`.

`scripts/stylecheck.py` (beside this file) flags most of these on the added lines of
`gh pr diff N` outputs; its "check" items (terminal `simp only`, operators in `calc`) need a
look, not a blind fix.

### Imports

Each import costs. The bot adds `large-import` beyond a few percent; the answer is a new file
rather than a heavy import in a basic one. What only proofs need is imported without `public`.
Check there is no cycle: the imported module must not already import the edited file
(`Determinant/Basic.lean` cannot import `ExteriorPower/Basis.lean`; hence
`Matrix/CauchyBinet.lean`).

## 3. Compile against the latest master

The machine has 8 GB of RAM and little disk: **one Lean process at a time** (also with the
repository's own Lean jobs), and no full build of Mathlib from source.

- **The build to use is the clone's own**: `~/Commutator/mathlib4` is a Mathlib checkout at
  upstream master with a complete build in `.lake/build` (about 8 GB). Compile a test file or a
  PR's file there:

      cd ~/Commutator/mathlib4 && lake env lean <scratchpad>/Test.lean

  Before relying on it, bring it to the latest master and fetch the matching cache:

      git fetch upstream master && git merge --ff-only upstream/master
      lake exe cache get && lake build Mathlib --no-build   # expect "All targets up-to-date"

  (`cache get` downloads thousands of files when master moved; it needs a few GB of disk.) The
  clone's `master` must stay a fast-forward of `upstream/master`: never commit on it, put work
  in worktrees (§4).
- **Never point another Lake project at this clone with a symlink** (`.lake/packages/mathlib`
  → `~/Commutator/mathlib4`). Lake compares the package's URL and revision with the manifest,
  and when they differ it *deletes the directory and clones again*, through the symlink: tested
  on a toy project, the target was emptied. The Lean project of this repository
  (`lean/`, Mathlib pinned at `v4.33.0`, toolchain v4.33.0) keeps its own copy under
  `lean/.lake/packages/mathlib`; it cannot share the build with the clone as long as the two
  revisions differ. To share one copy, bump the pin of `lean/` to a master revision (lakefile,
  manifest, toolchain) and rebuild the 32 folders, as a separate change.
- The local check misses what only CI sees (linters on the whole library, other files that
  changed after the cache): **the PR's CI is the final judge**. After pushing, wait for it with
  a background loop on `gh pr checks N --json bucket`, and read failures with
  `gh api repos/leanprover-community/mathlib4/actions/jobs/<id>/logs --allow-escape-sequences`
  piped through `sed 's/\x1b\[[0-9;]*m//g' | grep -n 'error'`.

## 4. Branches and PRs

- **Clone**: `~/Commutator/mathlib4`, remotes `origin` = the fork `mycaule/mathlib4`,
  `upstream` = leanprover-community. Never switch branches or commit in that clone (it is the
  build of §3 and agents may be using it): work in **worktrees** in the session scratchpad,
  one per PR,

      git -C ~/Commutator/mathlib4 fetch origin <branch>
      git -C ~/Commutator/mathlib4 worktree add -f <scratch>/wt-<N> -B fix/<N> origin/<branch>

  New PRs: a branch `mycaule/<topic>` from `upstream/master`.
- **Before any commit on an existing branch**, fetch it: Michel may have merged master from
  GitHub. Start from the fork's tip, never from a local copy. **No `push --force`**: one
  commit per round of fixes, pushed with `git push origin fix/<N>:<branch>`.
- **Stacked PRs** (`- [ ] depends on: #N` in the description; the bot adds
  `blocked-by-other-PR`): a fix in the lower PR is merged into each branch above it, in
  order (#44735 → #44736 → #44755; #44728 and #44759 → #44760). Say "Stacked on #N; only the
  commits after that branch are new." at the top of the description.
- **Commit**: title `feat(Dir/File): …` for new content, a plain sentence for follow-ups
  (`docstring for …`, `style: …`, `use … from #N instead of a private copy`), last line
  `Co-Authored-By: Claude …`.
- **PR**, as a draft:

      gh pr create --draft --repo leanprover-community/mathlib4 --base master \
        --head mycaule:<branch> --title "feat(Dir/File): lowercase summary" --body-file -

  Title lowercase after the colon (the title check fails otherwise). Body: the declarations
  with their statements, a paragraph of proof, what Mathlib already has, the debatable choices
  (file, imports, names) as questions for reviewers, an optional Grothendieck source line, a
  depends-on line, and:

      AI disclosure: the Lean proof was written by an AI model (Claude, Anthropic) under my
      direction. I have read and checked it and will handle the review.

  New theories or new files deserve a Zulip thread first (#mathlib); prepare the message for
  Michel.

## 5. After opening: CI and reviews

- **Red CI**: read the log, fix the cause (deprecated name on master, unused argument, missing
  import after an import cut, docstring after an attribute), push, wait again.
- **Reviews**: apply precise suggestions to the letter; when a suggestion is wrong as written,
  apply its intent and draft for Michel the reply that explains why. A reviewer asking for a
  different route (exterior powers for Cauchy–Binet, `Reedy/SimplexCategory.lean` for #44732)
  means rewriting the PR, then rewriting its title and description, saying in one line what
  an earlier version did.
- Do not answer a review about comments by adding more: when a reviewer finds docstrings
  superfluous, remove them (all of the trivial ones, not only the quoted line), and draft for
  Michel a reply only if he wants to point to the style guide's section on comments, which
  asks for docstrings on declarations worth documenting, not on every lemma.
- Improving several open PRs at once: spread the read-only review over a few agents, then
  apply and compile yourself, one PR at a time.

## 6. Back to the repository

When a PR changes or merges:

- **issue #52**: tick the box, give the PR number and state (draft, ready, merged, closed);
- **the Lean appendix** `docs/lean/article.tex`: the blue square `\mathlibpr{N}` beside each
  statement with a Mathlib PR (Michel's included); cite the authors of the known result, as
  the PR description does, in the appendix bibliography; rebuild the PDF from HEAD;
- **Findings** (`src/content/findings.ts`, `lean` field): a statement already in Mathlib is
  marked as proved there;
- after a merge, when the pinned Mathlib is bumped, replace the local proof by the Mathlib
  lemma. Bumping `lean/lakefile` / the manifest is a separate, deliberate change: it rebuilds
  Mathlib, which this machine cannot do without the cache.
