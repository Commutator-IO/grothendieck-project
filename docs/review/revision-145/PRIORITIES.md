# #145: order of the Fable 5.2 revision pass (24 November 2026)

Counted today in the `batch-*.fr.tex` files of 164 folders: **41,854 `\uncertain` and 59,454 `\ill`**.
Revised whole by Fable 5.2 so far: 21 folders (1, 46, 62, 76, 81, 85, 86, 87, 89, 104, 115, 133,
140-1, 141, 142, 151, 152, 154, 156-2, 156-9, 161-6). Revised in part: 43 others.
The pass itself follows the rules of #145 and of `/transcribe-grothendieck` (revision on the
facsimile, `% Revised: Fable 5.2 …` line, `npm run render` and `npm run tei`).

## Which pages are already done

The registry is [`pages.json`](pages.json): one entry per folder, batch, pass and scope
(`blind`, `full`, `statements`, `flags`), seeded on 24 November 2026 from the records of this
directory and from the `% Revised:` lines of the batches. The tables below are a snapshot of
that day; the registry is what counts.

- Before a pass: `npm run revised -- --todo <cote> <pages…>` prints the pages that have no
  pass of scope `statements`, `full` or `blind`. Only those are read. `flags` does not count
  as read: on such a page only the marked words were looked at, sometimes one word.
- After a pass: add its pages to `pages.json`, in the same commit as the record.
- `npm run revised -- <cote>` lists every pass recorded for a folder.

## What to look for on each crop

The defects known in first passes of this kind, and what they mean for the pass:

1. **Two candidate readings.** Where a doubtful word has a close rival, the first reading
   turns out right in most of the places later settled on the scan (about seven in ten).
   Change it only when the page shows the other one.
2. **Omissions.** Ink on the page with nothing in the text at that place: a word at a line
   end, an insertion above the line, a margin note, a short line between two formulas.
   Look at the whole crop, not only at the marked words.
3. **Pages read in another order.** Marginalia, two columns, slips pasted on the leaf,
   arrows sending a passage elsewhere. Check that the order of the text follows the page.
4. **Pages left out.** A page of the facsimile with no `\page{}` and no note saying why.
5. **Mathematics first.** Doubts are denser per word in formulas than in prose, and a
   misread symbol changes a statement. Settle the formulas of a batch before its prose.
6. **Struck text last.** A large share of the doubts sit inside `\struck{}`. They keep their
   precise readings, but they change no statement: take them after the live text.

Expected yield, from comparable passes: about one settled doubt in seven corrects the
first reading. The rest confirm it or stay open.

## Tier 1: the pages a statement rests on

Pages cited by an open finding (`candidate`, `unsearched`) or by a Lean card, in folders not
yet revised whole. Only those pages, not the whole folder. Score = weight in the edition ×
density of marks.

| Folder | Open findings | Lean cards | Marks a page | Revised | Pages |
|---|---|---|---|---|---|
| 29 | 6 | 3 | 9.5 | 5/11 | 1–11, 120, 124–129, 141–160, 170–171, 188–216 |
| 79 | 6 | 3 | 8.4 | 0/15 | 19–20, 33, 35, 92–95, 136–140, 184–188, 242–247, 275–279 |
| 77 | 6 | 3 | 8.2 | 4/8 | 7–19, 63–125, 129–143, 155–157 |
| 126 | 4 | 4 | 23.2 | 0/2 | 4–7, 10–14, 17–23, 26–29 |
| 161-2 | 4 | 4 | 16.0 | 2/6 | 33, 39, 41–43, 48, 89–106 |
| 100 | 4 | 4 | 15.0 | 0/3 | 2–3, 20, 22–24, 30–38 |
| 15 | 6 | 0 | 13.9 | 1/12 | 58–62, 71–77, 80–81, 116–118, 140–143, 167, 175, 178 |
| 80 | 3 | 7 | 8.6 | 3/4 | 9, 20, 24, 26, 28, 39–54 |
| 16 | 5 | 3 | 8.4 | 0/3 | 4–17, 24–31, 39–43, 47–49 |
| 91 | 5 | 1 | 19.8 | 1/8 | 4–9, 15–20, 24–31, 53–58, 125–131 |
| 10 | 5 | 2 | 10.4 | 0/10 | 3–30, 32–65, 101–108, 110, 117–179, 191–197 |
| 101 | 3 | 4 | 20.5 | 1/3 | 10–34 |
| 128 | 3 | 5 | 11.7 | 0/2 | 4–29 |
| 161-3 | 4 | 3 | 7.4 | 0/3 | 9–14, 34–48, 53–54 |
| 162-5 | 6 | 0 | 3.5 | 0/4 | 2–48 |
| 6 | 5 | 0 | 8.5 | 0/4 | 33–36, 38–39, 47–56, 61 |
| 127 | 4 | 1 | 14.4 | 0/2 | 2–4, 7–10, 12, 15, 19 |
| 93 | 3 | 3 | 12.1 | 0/12 | 71–73, 100–105, 115–123, 188, 193–194, 208, 233–235 |
| 2 | 3 | 2 | 21.3 | 0/3 | 2–4, 9–15, 21, 32–37 |
| 19 | 3 | 3 | 8.1 | 0/5 | 3–11, 79–80 |

Then, in the same way: 73, 5, 11, 64, 123, 31, 43, 84, 129, 150.

## Tier 2: batches whose first pass ran on Opus 5

103 batches in 55 folders were first read by Opus 5, before Opus 5.5. In that order, with the
number of batches: 29 (11), 10 (8), 158 (5), 19 (5), 18 (4), 11, 13, 16, 161-3, 2, 31 (3
each), 159, 160, 161-2, 21, 22 (2 each), then the folders with one such batch. 151 is
already revised whole.

## Tier 3: dense folders not yet revised whole

By marks a page, for folders with at least 700 marks:

57 (27.3), 43 (25.8; 6 batches left), 58 (25.5), 33 (24.0), 101 (20.5), 91 (19.8), 34 (19.3),
23 (16.3), 161-2 (16.0), 137 (14.9), 45 (14.5), 15 (13.9), 36 (13.4), 31 (13.3), 156-7 (12.5),
7 (12.4), 93 (12.1), 156-8 (11.3), 67 (11.2), 150 (11.0), 10 (10.4), 74 (10.2), then 156-4,
156-6, 29, 149, 146, 72, 79, 77, 69, 78, 136, 12, 64, 147, 144, 84, 83.

**Folder 1** is revised whole and still has 7,683 marks (54 a page): the point « retranscribe
it whole » of #145 stays open.

## Tier 4: coverage

- **Thin pages** (fewer than 25 words, no drawing, not noted blank), to check for omissions:
  119 (17 pages), 134-2 (14), 129 (6), 144 (4), then 19, 29, 32, 43 (3 each).
- **Inventory pages against transcribed pages**, to explain one by one (blank leaves, texts
  by others summarised by rule, books edited elsewhere) or else transcribe: 119 (313 / 77),
  25 (184 / 2), 134-8 (86 / 1), 136 (375 / 247), 15 (227 / 124), 33 (180 / 91), 57 (314 / 231),
  144 (183 / 139), 14 (131 / 90), 84 (192 / 151).

## Tier 5: the rest

By decreasing density, live text before struck text.

## How to report

One file per folder in this directory, as for the folders already done: counts confirmed,
corrected, read, left; the corrections that change the mathematics, listed for
`/modernize-grothendieck` and `/find-novelty`; the places for `/review/`.
