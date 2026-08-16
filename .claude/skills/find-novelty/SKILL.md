---
name: find-novelty
description: Reads a folder's modernised reading and its transcriptions and proposes candidate findings — statements the folder establishes that may not stand in the published literature — each written as a claim about the literature rather than about Grothendieck, with what was searched, what part of it is the edition's own, and what would settle it. Writes them into src/content/findings.ts, which the site's Findings tab renders. Use when someone asks what is new in a folder, what these notes have that the literature does not, to look for a refinement or an unpublished result, or to re-check candidates already listed. Never asserts priority.
model: claude-opus-5
---

# Looking for what is not in the literature

**Runs on Opus 5**, like the reading it works from. The judgement here is the
same one the modernised reading makes when it names a modern theorem and
footnotes whether the manuscript could have known it — sharpened, and pointed
at the gap instead of the match. A different model at this step would be a
second reader silently disagreeing with the first about what the folder says,
in the one place where the disagreement becomes a claim about other people's
work.

## The thing this skill is for, and the thing it must not do

A folder of the fonds occasionally contains a statement that is not in the
books: a criterion under a weaker hypothesis, a construction the literature
reaches by another route, a case someone else left open. Finding those is
worth doing. It is also the single most dangerous operation in this project,
because the failure mode is not a wrong formula — it is **a false claim about
what other mathematicians did not do**, published under Grothendieck's name,
which is a claim about people rather than about mathematics.

So the rule that governs everything below:

> **A novelty is a claim about the literature, not about the manuscript.**
> The manuscript can be read. The literature can only be *searched*, never
> exhausted. Every entry is therefore provisional, and says what was searched.

Three things follow, and they are not negotiable.

**Never write a priority claim.** Not « Grothendieck first proved », not
« this predates », not « unpublished until now ». Almost nothing in this fonds
is dated, and « [vers 1963-1973] » is the archivists' guess from a verso; a
claim of precedence needs a date the folder does not have. Write instead what
is true and checkable: *not found in the sources listed*.

**Say what was searched, by name.** « Not in the standard literature » is not
a finding, it is a feeling. « Not found in Johnstone, *Stone Spaces* II.4 and
*Elephant* C1.1, nor in Isbell 1981 » is a finding, because a reader can go and
refute it. If nothing was searched, the entry says `literature: []` and its
status stays `unsearched` — which is honest, and still useful as a list of
things to check.

**Separate the manuscript's part from ours.** The modernised reading supplies
hypotheses the page leaves implicit and completes steps the page skips. Where
it did, the novelty is partly the edition's and the entry must say so in the
`ours` field. Folder 161-3's page 10 is the case to keep in mind: the converse
there is stated under a hypothesis weaker than local compactness, and it is a
genuine candidate — but the reading had to supply an inclusion the page never
writes, so what is on the page and what is in the entry are not the same
statement. An entry that hides that is claiming a novelty for a sentence
nobody wrote.

## Where it takes its material

Two files per folder, both of them ours, and in this order:

1. `transcripts/<folder>/batch-NN.fr.tex` — the record. What is actually on
   the page, apparatus and all.
2. `transcripts/<folder>/<folder>.modern.tex` — the reading. Its footnotes are
   the richest source of candidates in the project, because a footnote saying
   « c'est aujourd'hui le théorème de X » is a match, and a footnote saying
   « la page ne le vérifie pas » or « nous suppléons » is either a gap in the
   edition or a gap in the literature, and the two look alike from here.

Never work from the reading alone. A candidate always gets checked back
against the transcription: if the statement rests on an `\uncertain{}` or sits
next to an `\ill{}`, that goes in the entry, because a novelty resting on a
word nobody could read is not a novelty.

**Do not read the facsimile for this.** If a candidate turns on what the page
actually says, that is `/transcribe-grothendieck`'s work; fix the
transcription first and come back.

## What a candidate looks like

Good candidates are narrow and checkable:

- a theorem proved under a **weaker hypothesis** than the standard one;
- a **converse** the literature states only in one direction;
- a construction the books reach by a different route, where the manuscript's
  route gives something the usual one does not;
- a case the published account **leaves open** and this one settles;
- an object defined here that acquired its modern name later, *when the
  definitions actually coincide* — check that they do, in both directions.

Bad candidates, which will outnumber the good ones and should be dropped
rather than written up:

- « this is Giraud's theorem, compressed » — a match, not a novelty; it belongs
  in the reading's footnotes, where it already is;
- notation, vocabulary, or the order of an exposition;
- anything whose apparent novelty is that the manuscript is *less* general,
  *less* precise, or missing a hypothesis;
- a statement the reading had to repair to make true. The repaired statement is
  the edition's; the page's statement was wrong. Neither is a novelty.

## The entry

Entries live in `src/content/findings.ts`, typed by `Finding` in
`src/lib/types.ts`, and the site's Findings tab renders them. One object per
candidate:

| field | what it holds |
|---|---|
| `id` | stable slug, `<cote>-<short-name>`; never reused, never renumbered |
| `cote`, `pages` | the shelfmark and the pages the claim rests on |
| `kind` | `mathematical` or `codicological` — see below |
| `claim` | one sentence, English, stating what the folder establishes |
| `basis` | what in the folder supports it, in a sentence |
| `ours` | what the edition supplied, or `null` when the page carries it alone |
| `literature` | the sources actually searched, by name and section |
| `status` | `candidate` · `unsearched` · `matched` · `confirmed` |
| `settle` | the one check that would decide it |

`codicological` entries — leaves bound out of order, two manuscripts
interleaved, a sentence continued on a page that is not in the folder — are
findings in the same sense and carry less risk, because they are claims about
this object rather than about the literature. They still get a `status`: what
was checked against the facsimile, and what was not.

`status` means:

- **`unsearched`** — a candidate nobody has looked up. The honest default.
- **`candidate`** — searched in the named sources, not found there.
- **`matched`** — found in the literature. **Keep the entry**, with the
  reference. A killed candidate is the most useful thing on the page: it stops
  the next reader spending a day on it, and it is evidence the list is being
  pruned rather than grown.
- **`confirmed`** — a person has checked it. Only a person may set this. Never
  set it from a pass.

## The sequence

1. Read the folder's transcriptions and its modernised reading, whole.
2. List every place the reading names a modern theorem, supplies a hypothesis,
   completes a step, or says the page leaves something unverified. That list is
   the candidate pool, and it is mostly matches.
3. Drop the matches. For each survivor, write the claim as a single sentence
   and ask what would refute it.
4. Search — the literature, by name and section. Record what was searched even
   when it found nothing, and especially then.
5. Write the entries, `unsearched` where nothing was looked up.
6. Check every entry against the transcription for `\uncertain{}` and `\ill{}`
   under it, and against the reading for what the edition supplied.
7. `npm run lint && npx tsc -b` — the page is typed, and a malformed entry
   should fail the build rather than reach a reader.

## What not to do

- **Claim priority.** Covered above; it is the reason this skill is written
  the way it is.
- **Grow the list.** A pass that finds nothing new and marks two old entries
  `matched` has done its job well. There is no target number.
- **Write for effect.** « Remarkable », « striking », « ahead of its time » —
  all out. The entry states what was found and what was searched.
- **Let a candidate rest on an unread word.** If an `\ill{}` or an
  `\uncertain{}` carries the statement, say so in `basis` and drop the status
  to `unsearched` at best.
- **Set `confirmed`.** Only a person may, and no pass of this skill is one.
