"""Flag Mathlib style-guide slips in a PR's added lines, or in whole Lean files.

Usage (run with python3 -I):
  gh pr diff N --repo leanprover-community/mathlib4 > diffs/N.diff   # one per PR
  python3 -I stylecheck.py diffs/                 # every *.diff in the directory
  python3 -I stylecheck.py N.diff File.lean ...   # single diffs and/or whole .lean files

For a diff only the added lines of .lean files are checked; a .lean file is checked whole.
Items marked "(check)" need a human look, not a blind fix. Exit status 1 if anything is flagged.

The rules come from the Mathlib style guide and the reviews of this repository's PRs, plus
checks adapted from Chris Birkbeck's mathlib-quality (scripts/style_checker.sh and its
reference docs; https://github.com/CBirkbeck/mathlib-quality, MIT licence, notice in
../references/mathlib-quality-LICENSE.txt). Line length is counted in codepoints, not bytes.
"""
import os
import re
import sys


def diff_lines(path):
    """Yield (file, line number, text, is_new_file) for each added line of a .lean file."""
    cur, ln, new = None, 0, False
    for raw in open(path, encoding="utf-8"):
        if raw.startswith("diff --git"):
            cur, new = None, False
            continue
        if raw.startswith("new file mode"):
            new = True
            continue
        if raw.startswith("+++ "):
            cur = raw[6:].strip() if raw[4:].startswith("b/") else None
            continue
        m = re.match(r"@@ -\d+(?:,\d+)? \+(\d+)", raw)
        if m:
            ln = int(m.group(1)) - 1
            continue
        if cur is None or not cur.endswith(".lean") or raw.startswith("-"):
            continue
        if raw.startswith("\\"):
            continue
        ln += 1
        if raw.startswith("+"):
            yield cur, ln, raw[1:].rstrip("\n"), new


def file_lines(path):
    for k, raw in enumerate(open(path, encoding="utf-8"), 1):
        yield path, k, raw.rstrip("\n"), True


RULES = [
    # (regex on code with comments removed, message)
    (r"\bfun\b[^↦]*=>", "fun => (use ↦)"),
    (r"λ", "λ (use fun x ↦)"),
    (r"(^|\s)\$(\s|$)", "$ (use <|)"),
    (r"←\S", "← without a space"),
    (r"\b(haveI|letI)\b", "haveI/letI (have/let in proofs) (check)"),
    (r"\bpush_neg\b", "push_neg is deprecated (push Not)"),
    (r"\bomega\b", "omega (lia in new code) (check)"),
    (r"\bnative_decide\b", "native_decide"),
    (r"\bsorry\b", "sorry"),
    (r"^\s*#(check|eval|print|exit|reduce|find_home|min_imports)\b", "# command left in"),
    (r"set_option\s+(trace\.|pp\.|maxHeartbeats|maxRecDepth|synthInstance\.maxHeartbeats)",
     "debug or heartbeat set_option"),
    (r"\b(refine|cases|induction|rcases|obtain)'", "primed Lean 3 tactic"),
    (r"^\s*open\s+Classical\b", "open Classical (classical tactic / open scoped Classical in)"),
    (r"\berw\b", "erw (check: rw, or a missing lemma)"),
    (r"\bshow\b.*\bfrom\s+by\b", "show … from by (show … by)"),
    (r",\s*\]", "trailing comma in a list"),
    (r":= by exact\b", ":= by exact (term mode)"),
    (r":= by rfl\s*$", ":= by rfl (:= rfl)"),
    (r"≥|(\s>\s)", "≥ or > in Lean code (use ≤, <) (check)"),
    (r"^\s*(public\s+|private\s+)?import\s+Mathlib\s*$", "import Mathlib"),
    (r"\b(theorem|lemma|def)\s+\S*(isation|ise_|fibre|colour|neighbour)", "British spelling"),
    (r"\b(theorem|lemma)\s+\S*_(ge|gt)(_|\b)", "_ge_/_gt_ in a name (check)"),
    (r"\b(theorem|lemma)\s+\S*(_aux\d|_step\d|\d+_\d+_\d+)", "numbered name"),
]


def check(lines, label):
    out = []
    added = list(lines)
    depth = 0  # nesting depth of /- … -/ comments, tracked across consecutive lines
    for i, (f, k, t, _) in enumerate(added):
        def rep(msg, f=f, k=k, t=t):
            out.append(f"  {os.path.basename(f)}:{k}: {msg}: {t.strip()[:90]}")

        code, s = "", t
        while s:
            o, c = s.find("/-"), s.find("-/")
            if depth:
                if c >= 0 and (o < 0 or c < o):
                    depth, s = depth - 1, s[c + 2:]
                elif o >= 0:
                    depth, s = depth + 1, s[o + 2:]
                else:
                    s = ""
            else:
                lc = s.find("--")
                if lc >= 0 and (o < 0 or lc < o):
                    code += s[:lc]
                    s = ""
                elif o >= 0:
                    code += s[:o]
                    depth, s = 1, s[o + 2:]
                else:
                    code += s
                    s = ""
        if len(t) > 100:
            rep(">100 chars")
        if t.rstrip() != t:
            rep("trailing ws")
        if "\t" in t:
            rep("tab")
        if t.strip() == "by":
            rep("by alone")
        if re.match(r"\s+:=", code):
            rep(":= at line start")
        if re.match(r"\s+(\+|\*|∧|∨|→|↔|=|≤|<|∣|•)\s", code) and not t.strip().startswith(("_", "·")):
            rep("operator at line start (check in calc)")
        for rx, msg in RULES:
            if re.search(rx, code):
                rep(msg)
        if re.search(r"\bsimp only \[[^\]]*\]\s*$", code):
            nxt = added[i + 1][2] if i + 1 < len(added) else ""
            ind = len(t) - len(t.lstrip())
            if nxt.strip() == "" or len(nxt) - len(nxt.lstrip()) < ind:
                rep("terminal simp only? (check)")
        if re.match(r"^\s*\(h\w* : [^)]*∧", code):
            rep("conjunction hypothesis? (check)")
        if t.lstrip().startswith("/--") and i > 0 and re.match(r"^\s*@\[.*\]\s*$", added[i - 1][2]):
            rep("docstring after attribute (parse error)")
    # blank lines inside declarations, double blank lines
    for i in range(1, len(added) - 1):
        f, k, t, _ = added[i]
        prev, nxt = added[i - 1], added[i + 1]
        if t.strip() == "" and nxt[1] == k + 1 and prev[1] == k - 1:
            if nxt[2].startswith("  ") and prev[2].startswith("  "):
                out.append(f"  {os.path.basename(f)}:{k}: blank line inside declaration?")
            if prev[2].strip() == "":
                out.append(f"  {os.path.basename(f)}:{k}: double blank line (check)")
    # header of new files
    seen = {}
    for f, k, t, new in added:
        if new and k <= 6:
            seen.setdefault(f, []).append(t)
    for f, head in seen.items():
        h = "\n".join(head)
        if "Copyright (c)" not in h:
            out.append(f"  {os.path.basename(f)}: new file without a copyright header")
        elif "Released under Apache 2.0 license as described in the file LICENSE." not in h:
            out.append(f"  {os.path.basename(f)}: header lacks the Apache 2.0 licence line")
        elif not re.search(r"^Authors: [^\n]*[^.\n]$", h, re.M) or " and " in h.split("Authors:")[-1]:
            out.append(f"  {os.path.basename(f)}: Authors line (plural, commas, no final period)")
    if out:
        print(label)
        print("\n".join(out))
    return bool(out)


def main(args):
    if not args:
        print(__doc__)
        return 2
    flagged = False
    for a in args:
        if os.path.isdir(a):
            for fn in sorted(os.listdir(a)):
                if fn.endswith(".diff"):
                    flagged |= check(diff_lines(os.path.join(a, fn)), fn[:-5])
        elif a.endswith(".lean"):
            flagged |= check(file_lines(a), a)
        else:
            flagged |= check(diff_lines(a), os.path.basename(a).removesuffix(".diff"))
    return 1 if flagged else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
