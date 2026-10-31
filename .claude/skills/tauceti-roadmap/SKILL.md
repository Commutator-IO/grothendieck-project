---
name: tauceti-roadmap
description: Writes, updates and defends a Tau Ceti roadmap pull request (TauCetiProject/TauCetiRoadmap, opened from the fork mycaule/TauCetiRoadmap) so that it passes Chris Birkbeck's AI-assisted review on the first round — the house shape of README.md, the content rules, Suggested.lean as an acceptance test, the gate and elaboration probes to run before pushing, the git discipline, and the reply to a review. Use when someone asks to create a roadmap or a roadmap PR from a folder of the fonds or a Lean appendix, to answer or repair a review (findings F01…, P1/P2/P3) on one of Michel's roadmap PRs, or to update or revise a roadmap already open or merged.
---

# Tau Ceti roadmap pull requests

A roadmap is `TauCetiRoadmap/<Name>/` with three files: `README.md` (the specification),
`Suggested.lean` (its acceptance test) and `metadata.toml` (`topic = "math.XX"`). Nothing else in
the folder, nothing outside it. The maintainer's reviewer (CBirkbeck's worker, model "fable")
re-reviews every new head: P1 (false, vacuous, unowned) and P2 (overclaim, missing hypothesis,
statable headline absent, sorry'd data, upward supplier) block; P3 (style, locator, Check) do not,
but come back every round until repaired. This skill distils the reviews of PRs #1058, #1059,
#1060, #1061, #1523 and #1685 (28 and 31 October 2026), the repository's README and CONTRIBUTING,
and the worker's rules (`prompts/sections/*.md` and `tauceti_roadmap_worker/gates.py` in
TauCetiProject/TauCetiRoadmapWorker). Models of the shape: GrothendieckTeichmuller (branch
`roadmap/grothendieck-teichmuller`, approved 31 Oct.) and GrothendieckInfinityGroupoids
(`roadmap/grothendieck-infinity-groupoids`). Roadmaps on main written by the maintainers
(DiophantineApproximationAndTranscendence, ModularCurves) are older in form: follow the rules here
where they differ.

## 0. What Michel decides

- He chooses subjects and scope, and decides when a reply is posted. Draft replies in a file of the
  scratchpad and show them; post (`gh pr comment N --repo TauCetiProject/TauCetiRoadmap
  --body-file …`) and move the label to `awaiting-review` only on his word. A comment on another
  author's PR needs his explicit go-ahead each time.
- Every edit happens in a worktree of a clone of `mycaule/TauCetiRoadmap` with `upstream` =
  TauCetiProject/TauCetiRoadmap. A worktree may share the clone's packages
  (`ln -s ../../<clone>/.lake/packages .lake/packages`) only when its `lake-manifest.json` is
  identical (`diff` it first): Lake deletes and re-clones a package whose pin differs.

## 1. The house shape (README.md)

Read GrothendieckTeichmuller's README before writing. In this order:

- [ ] `# Roadmap: <lower-case title>`, then a `**Summary.**` paragraph: what is built, on which
      carriers, and the end theorems, each with its exact hypotheses.
- [ ] `## Scope and ownership`: what is owned here, and what is left to which roadmap, by name and
      section. The only place that says "stated by roadmap X".
- [ ] `## Conventions` (not "Standing conventions"): standing hypotheses, normalisations, sign and
      composition conventions, each pinned by a two-term witness computed in a Check.
- [ ] `## Exact supplier contracts`: `**From Mathlib**`, `**From Tau Ceti**` (file and declaration
      names, checked at the pins), `**From <Roadmap>**` (sections and declarations). Write
      "Nothing is consumed from another roadmap" when true.
- [ ] `## How to read the build`: one paragraph, layer order and what each layer delivers.
- [ ] `## Layer k: <title>` with `### k.n <topic>` targets (digits only: the board reads only
      these). Each target: prose ("Define … . Prove that … (Source, Theorem 3.2, p. 41)."), a
      `*Needs:*` line naming every declaration, target and roadmap section the statement and its
      route use, and `**Checks.**` with at least three bullets per definition, each saying what is
      computed and which plausible wrong definition it excludes. Each layer ends with
      `### Examples` and `### Dependencies`.
- [ ] `## Downstream consumers`: search main and the open PRs for roadmaps that cite this one,
      under its present and former names (`git grep -w <Name> upstream/main`); "None known" was
      refused when two existed (#1059).
- [ ] `## Research context` (optional): one or two paragraphs; open problems live here only.
- [ ] `## References`: full bibliographic data, zbMATH or DOI or arXiv.

Unicode mathematics, ASCII inside code spans; no `$…$`, `\(`, `_{`, `^{` outside code; lines
wrapped at 100 characters (a 137-character line was a P3).

## 2. Content rules, with the reasons the reviews give

- **Timeless.** No process narrative ("not yet", "until the pin moves", "removed", "follow-up",
  "only so that this file compiles"), no pin hashes, no review references. A reader a year on must
  not see what was contentious (README, "Roadmaps are timeless"); the gate's `residue` scanner
  refuses "stand-in", "catalogue", "so far", "TODO".
- **Cross-roadmap citations by roadmap name and section, never PR numbers**, even for roadmaps
  still in PRs, and with the full name (`DiophantineApproximationAndTranscendence`, not
  `DiophantineApproximation`): numbers rot and the citation checker resolves names only. Resolve
  each citation at main or at the open head every round: a section cited from an open PR that
  revises a roadmap on main does not count (that roadmap is cited as on main; #1058 F01 cited a
  `GT4` that existed nowhere).
- **Legal, refereed sources with exact locators** (theorem, section, page), checked against the
  text: the reviewer reads the sources and catches a locator that states less (Waldschmidt Th. 4.1
  is for entire functions, #1059; Prop. 2.14 is for free extensions, #1060). Read only from legal
  places (arXiv, HAL, Numdam, GDZ, author pages). A paywalled work is cited by its locator alone; do
  not write "uncertified" in the README, which is a manifest status, not mathematics (#1058, last
  round). No MathOverflow, private communication, unrefereed preprint as a source; never
  csg.igrothendieck.org.
- **Open conjectures are research motivation, never deliverables**: no `def Conj : Prop`, no named
  predicate, no "consequence package", no successor that states them (IharaQuestion,
  EllipticPeriodConjecture, HomotopyHypothesis, SkeletonDetermines were all removed). Conditional
  theorems under explicit hypotheses stay.
- **Nothing deferred.** No "Roadmap for a roadmap", no "Do not implement", no "optional": every item
  lives in a layer, or Scope names the roadmap that owns it (#1058 F08, replaced by a Scope
  paragraph).
- **The edition stays out.** No Provenance section, no GitHub link to grothendieck-project, no Lean
  appendix as a source, no page-by-page folder description. At most one sentence of context with a
  Montpellier locator: "(Montpellier fonds, folder 145, p. 35, https://grothendieck.umontpellier.fr/145.pdf)".
  No quotation and no claim about what an archival page says beyond that pointer: the reviewer
  cannot read the scan and flagged it (#1060, Breen letter); the BnF answer allows only a few words
  of quotation anyway.
- **Shared material is owned by the most general roadmap**; a specialisation imports it and keeps
  only its adapters (ModularCurvesPartII's quasi-periods, DeligneWeightsAndPurity §9.7's primitive
  decomposition, SurfaceTopology's `GMap`). Search by object, not by name, on main and in the open
  PRs before stating a carrier. If this roadmap is the owner, Scope says so with a locator.
- **No duplicated owners**: never restate another roadmap's definitions in a local section to make
  the file compile, never give a declaration another roadmap's fully qualified name. If the
  supplier's object is not at the pins, the headline that needs it is "not statable" (§3).
- **Honest `*Needs:*` lines.** The dependency check reads `*Needs:*` lines, supplier contracts and
  `### Dependencies`. A supplier hidden from them is an upward edge the reviewer finds anyway
  (#1061 F03); a supplier named but unused moves the roadmap later in the merge order (#1061, last
  round). Consumers go only under `## Downstream consumers`.
- **README ↔ Lean names, both directions.** Every declaration of `Suggested.lean` is named in the
  README where its target is stated; every backticked name the README presents as its own is
  declared there, including names without a namespace or behind a word (`structure Foo`,
  `legendre`), which the gate's `readme-ids` heuristic misses. Otherwise state the fact in prose.
  Library names are written fully qualified (`TauCeti.ringKrullDim_eq_toNat_trdeg`).
- **The README's generality equals the Lean's**: same hypotheses, no unused `[CharZero K]`, no
  missing `[FiniteDimensional K H]` the supplier needs (#1061, last round).

## 3. Suggested.lean, the acceptance test

- Module docstring `<Title>: target signatures`: the roadmap is `README.md`; this file states the
  roadmap's headline theorems against the pinned Mathlib and Tau Ceti, each with `sorry`, with only
  the definitions they need; then the list of headlines stated (README target and Lean name), and
  each headline **not statable** with the carrier it lacks ("not stated: README 2.3, `ζ = σ′/σ`,
  lacking ModularCurvesPartII's `latticeSigma`"). Not the old "suggests Lean forms for particular
  milestones" wording.
- Every headline that is statable at the pins is stated; a statable headline left out is P2 (#1060:
  Corollary 8.11 was statable once a 40-line coglobular space of disks was written).
- Definitions only to make a headline statable, with real bodies on native carriers. **No sorry'd
  data**, including data built on a `sorry`'d theorem: `#print axioms` on every definition must not
  show `sorryAx` (#1060, `stdDisks`); no `Classical.choose` over an unproved `∃` (#1059,
  `quasiPeriod`). Prove the small lemmas a definition needs.
- **No padding**: delete theorems that close in one tactic, restate a definition or the library,
  mirror a Check or compute an example; the README keeps them. Exception: obligations of an instance
  the headlines need (GT's monoid laws), said so in the docstring.
- `theorem`, never `lemma`; a docstring on every declaration; `namespace TauCetiRoadmap.<Name>`;
  `/-! ## Layer k: … -/` sections in README order; no `set_option` of any kind (not even
  `autoImplicit false`: check auto-binding with the probe instead), no `#check`, `#eval`,
  `#print`, `True` placeholder, `: Prop := sorry`, admitted `example`.
- Imports: `import Mathlib`, then only the individual `TauCeti.*` modules used, each existing at the
  pinned Tau Ceti; never `Mathlib.X`, never another roadmap's module.
- Watch auto-bound implicits: `open Complex` without `open scoped Real` turned `π` into a variable
  in six statements (#1059 F01, P1).

## 4. Checks before pushing

Run all three, one Lean process at a time (8 GB of RAM), in the worktree:

1. `python3 .claude/skills/tauceti-roadmap/scripts/gate.py <Name> --clone <worktree>`: clones or
   updates the worker into `~/.cache/tauceti-roadmap/`, fetches `merge-order/ORDER.txt` from
   TauCetiProject/TauCetiRoadmapJobs with `gh`, runs the worker's `gates.run_gate` and its
   dependency check with `--movable` against `upstream/main`, then prints advisories for what the
   reviews flagged although the gate passed (PR numbers in other forms, process words, the edition,
   "uncertified", headings, Checks per target, long lines, names in both directions, consumers on
   main). The gate must print `OK`; clear every advisory or know why it is wrong.
   **"NOT IN ORDER" is a local artefact** when the roadmap is new: ORDER.txt lists the maintainers'
   roadmaps, and the board inserts ours after its last supplier. The script checks it as placed
   there; only an UPWARD or CYCLE line is real. Say so in the reply ("locally, depcheck only reports
   that the roadmap is not in the public merge-order file").
2. `lake exe cache get`, then `lake build TauCetiRoadmap.<Name>.Suggested`: `sorry` warnings only.
   Never build Mathlib: if Lake starts compiling Mathlib files, stop and fix the cache (`gate.py
   --build` refuses to build when `lake build Mathlib --no-build` fails). Tau Ceti modules may build.
3. `python3 .claude/skills/tauceti-roadmap/scripts/probe.py <worktree>/TauCetiRoadmap/<Name>/Suggested.lean --clone <worktree>`:
   one elaboration of a scratch copy (about five minutes) with the one-tactic probe of every
   sorried theorem (padding), `#print axioms` of every definition (sorry'd data) and `#check @` of
   every declaration into `signatures.txt`, flagging binders the source never declares
   (auto-bound variables); compare each signature with its README statement.

Then the adversarial pass the reviewer will run: instantiate every statement on degenerate cases
(`n = 0, 1`, zero ring, `𝔖₃`, `p = 2`, junk values of `ℕ` subtraction), test each "iff" both ways,
and recompute every sign and convention witness. Most P1s were found this way: a false uniqueness
without `IsUnit λ`, `(3, 1)` with `3 ∉ ẑˣ`, a lower bound claimed "always", the wrong correspondence
for `Λ`.

## 5. Git discipline

- New commits only, never `push --force` (the reviewer's incremental re-review diffs heads).
- Before committing, `git fetch origin <branch>`: a cloud session may have pushed to it. Put your
  commit on top (`git rebase origin/<branch>` of your unpushed commits only), then push.
- Message: `<Name>: review of <date> — <what changed, finding by finding>` (for example
  `GrothendieckTeichmuller: review of 31 Oct. — …`); other commits `<Name>: <what changed>`. Last
  line: `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- Repair every finding of the round in one commit, P3s included: a P3 left for later is carried to
  the next review and keeps the round open (#1059 rounds 3–4, #1058 round 4).
- Keep the PR description current (title, scope, sources, AI assistance naming the model, a call
  for an expert reviewer): the reviewer reads it.

## 6. Replying to a review

Draft in the scratchpad, show Michel, post on his word. Shape:

```
:robot: AI-assisted (Claude Opus 5.5); I have read it and take responsibility for it.

Answer to the review of <head, 8 characters> (<date>). All changes are in <hash>, inside
`TauCetiRoadmap/<Name>/` only. `lake build TauCetiRoadmap.<Name>.Suggested` succeeds with only
`sorry` warnings, and the worker's gate gives 0 on every check.

**F01, <short title>.** <what changed, old → new, with the target number>. <hash>
```

- One short paragraph per finding with the commit hash; "applied as proposed" when it is; the
  evidence when you dispute one (a computed instance, a source line).
- Say honestly what is only partly done ("Partly done: … come in a follow-up commit"), and never
  claim what is not yet pushed: #1060's reply said every layer had Examples when it did not, and
  needed a correction.
- No `@` mentions, no apologies ("sorry for the inconvenience"), no thanks paragraphs.

## 7. Common findings and their standard repairs

| Finding (PRs) | Repair |
|---|---|
| `set_option autoImplicit false` (1058, 1060, 1061) | delete it; run the probe |
| PR numbers as supplier names (1058, 1059, 1060, 1061) | roadmap name and section, full name |
| Old shape: bold run-in targets, `## Ordering`, no supplier contracts or consumers (all four) | §1 checklist; fold Ordering into How to read the build |
| Fewer than three Checks (1058, 1059, 1060, 1061) | add discriminating ones on the roadmap's own objects, with values |
| Statable headline absent; catalogue docstring (1058, 1059, 1060, 1061) | state it; target-signatures docstring naming what is not statable |
| Padding: one-tactic, `rfl` API, mirrored Check (1058, 1059, 1060, 1061) | delete from Lean, keep in README |
| README names not declared, Lean names not in README (1058, 1059, 1061) | prose without the name; name each declaration at its target |
| Roadmap for a roadmap, Provenance, MathOverflow, edition links (1058, 1060, 1061, 1523) | a Scope paragraph naming the owners; one Montpellier locator |
| Open conjecture as a named predicate (all six, 28 Oct.) | research context in prose; conditional theorems only |
| Supplier drift: a section or declaration that does not exist where cited (1058, 1060) | check at the pins and at main; own it here or name the real owner |
| Shared object planned twice (1059, 1061, 1523, 1685) | import from the most general owner; adapters only |
| Hidden or superfluous supplier edge (1061) | honest `*Needs:*` lines |
| Sorry'd data, `Classical.choose`, `sorryAx` in a definition (1059, 1060, 1523) | real body; prove the lemmas it uses |
| Overclaim or source stating less: "always", unit exponent, wrong locator (1058, 1059, 1060, 1061) | add the hypothesis; cite what the source states |
| "None known" consumers (1059); "uncertified" in prose, long lines (1058) | grep main; locator only; rewrap |
