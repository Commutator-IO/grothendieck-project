---
name: tag-grothendieck
description: Writes or refreshes a folder's modern English keywords — the \keywords{} line closing the résumé of each modernised reading, which npm run manifest extracts as the folder's tags on the archive and notebook pages. Use when someone asks to tag a folder ("tag folder 115", "add keywords", "refresh the tags", "extract modern keywords"), when a modernised reading predates the keywords convention and has no \keywords line, or when a revision of the reading has made the existing tags stale. Tags only — it edits the \keywords line and nothing else in the file; rewriting the reading itself is /modernize-grothendieck's work.
model: claude-fable-5
---

# Tagging a folder with its modern vocabulary

**Runs on Fable 5**, like the two editions — the tags are a mathematical
judgement about what the batch builds, made by the same reader that made the
modernised reading, and pinned for the same reason: comparability.

## What a tag is

Three to six terms, **in English**, naming the modern vocabulary under which
what the folder's batches construct is known today — *idempotent adjunction*,
*Isbell duality*, *free symmetric monoidal category*. They are search keys,
not prose: a reader who remembers a notion and not a shelfmark must land on
the folder by typing the notion into the archive page's search box, and the
literature that search leads into is English.

They live in exactly one place: the line

```latex
\keywords{profunctor, Isbell duality, Cauchy completion}
```

closing the résumé of each `batch-NN.modern.tex`, just before
`\end{resume}`. `npm run manifest` extracts every `\keywords{}` of the
folder's modernised readings, unions them across batches, and the archive
and notebook pages show the union as the folder's tags. **There is no tags
file**, deliberately: a tag with no modernised reading behind it would be a
claim about content nobody has read.

## The sequence

1. **Read the folder's modernised readings** —
   `transcripts/<folder>/batch-*.modern.tex`, every one. The tags describe
   the folder, so a batch you have not read can silently hold its best tag.
   If no modernised reading exists, **stop and say so**: tags come from the
   reading, and the reading comes from `/modernize-grothendieck`. Do not
   skim the transcription instead — naming modern vocabulary is an
   interpretive act, and the interpretation is the modernised reading's job.
2. **Choose the terms.** For each construction the batch actually carries
   out, ask what a survey written this year would call it, and keep the
   name under which the literature files it. Three to six per batch;
   established names over fashionable ones; the specific over the generic —
   *Picard category* earns its place, *category theory* never does (every
   folder this project touches would carry it).
3. **Write the line** — one single source line, before `\end{resume}`,
   commas between terms. Keep it on one physical line: a term wrapped
   across a line break is fragile, even though the manifest now collapses
   the whitespace. If the line exists, edit it in place; the file's
   remaining text is `/modernize-grothendieck`'s and is not touched.
4. **Propagate and check**:

   ```bash
   npm run render && npm run pdf && npm run manifest
   ```

   Then confirm `public/manifest.json` carries the folder's tags exactly as
   written, and that the archive page's search finds the folder under each
   new term.

## What not to do

- **Tag an unread folder.** No modernised reading, no tags — that is the
  design, not a gap.
- **Create a tags file, or write tags anywhere but the `\keywords{}` line.**
  One source, extracted; two sources, drifting.
- **Translate the tags into French.** The editions are French; the tags are
  English on purpose.
- **Pile on synonyms.** *Reflective subcategory* and *reflective
  localization* point the same search; pick the one the folder's own
  content argues for.
- **Let a tag outrun the pages.** The batch touching a topos-recognition
  argument earns *Giraud's theorem* only if the reading actually walks
  through it; a passing mention earns nothing.
