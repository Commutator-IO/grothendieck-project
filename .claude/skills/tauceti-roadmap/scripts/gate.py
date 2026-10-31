#!/usr/bin/env python3
"""The Tau Ceti roadmap gate on one roadmap folder, as the maintainer's reviewer runs it, plus the
checks its reviews kept raising that the gate does not make.

    python3 gate.py <Name> --clone <TauCetiRoadmap clone or worktree> [--folder Sub/Name]
                    [--worker DIR] [--order FILE] [--no-update] [--no-library-scan] [--build]

What it does:

1. Clones TauCetiProject/TauCetiRoadmapWorker into --worker (default
   ~/.cache/tauceti-roadmap/TauCetiRoadmapWorker), or fast-forwards it, and imports its `gates`,
   `depgraph` and `cli.depcheck_lines` (standard library only).
2. Fetches merge-order/ORDER.txt from TauCetiProject/TauCetiRoadmapJobs with `gh` (cached as
   ~/.cache/tauceti-roadmap/ORDER.txt; --order overrides it).
3. Makes sure the clone has an `upstream` remote on TauCetiProject/TauCetiRoadmap and fetches its
   main: the roadmaps on upstream/main are suppliers available to everyone, and the outside-folder
   diff is taken against it.
4. Runs `gates.run_gate` (every text scanner, metadata, stray files, dirty tree, outside-folder
   diff, source material), then the dependency check with --movable, as the reviewer does.
5. Prints advisories: what the reviews of October 2026 flagged although the gate passed.
6. With --build: `lake exe cache get`, a guard that Mathlib needs no rebuild, then
   `lake build TauCetiRoadmap.<Name>.Suggested`, which must give `sorry` warnings only.

Exit status 1 when the gate fails (the NOT IN ORDER artefact excepted, see below); advisories never
change it.

NOT IN ORDER. ORDER.txt lists the maintainers' own open roadmaps. A roadmap of ours that is new is
not in it, so the plain check prints `NOT IN ORDER: <Name>`. That line is a local artefact, not a
finding: the reviewer's board inserts the roadmap after its last supplier. The script then checks
the roadmap as placed there (`candidate`), which is what the reviewer reads, and only an UPWARD or
CYCLE line in that check is a real problem. Sibling READMEs of other open pull requests are not
available locally, so a cycle through another open pull request is not detected here.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

WORKER_URL = "https://github.com/TauCetiProject/TauCetiRoadmapWorker.git"
CONTENT_URL = "https://github.com/TauCetiProject/TauCetiRoadmap.git"
JOBS_REPO = "TauCetiProject/TauCetiRoadmapJobs"
ORDER_PATH = "merge-order/ORDER.txt"
CACHE = Path.home() / ".cache" / "tauceti-roadmap"


def run(cmd: list[str], cwd: Path | None = None, check: bool = True, timeout: int = 600) -> str:
    out = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    if check and out.returncode != 0:
        raise SystemExit(f"failed: {' '.join(cmd)}\n{out.stderr.strip()[:800]}")
    return out.stdout


def ensure_worker(path: Path, update: bool) -> None:
    if not (path / "tauceti_roadmap_worker" / "gates.py").is_file():
        path.parent.mkdir(parents=True, exist_ok=True)
        run(["git", "clone", "--quiet", "--depth", "1", WORKER_URL, str(path)])
    elif update:
        run(["git", "-C", str(path), "pull", "--quiet", "--ff-only"], check=False)
    head = run(["git", "-C", str(path), "log", "-1", "--format=%h %cs"]).strip()
    print(f"worker: {path} at {head}")


def fetch_order(explicit: str, cache: Path, update: bool) -> list[str]:
    from tauceti_roadmap_worker import depgraph
    if explicit:
        return depgraph.read_order(Path(explicit).read_text(encoding="utf-8"))
    if update or not cache.is_file():
        out = subprocess.run(["gh", "api", f"repos/{JOBS_REPO}/contents/{ORDER_PATH}",
                              "-H", "Accept: application/vnd.github.raw"], capture_output=True, text=True)
        if out.returncode == 0 and out.stdout.strip():
            cache.write_text(out.stdout, encoding="utf-8")
        elif cache.is_file():
            print(f"warning: could not fetch {JOBS_REPO}/{ORDER_PATH}; using the cached copy {cache}")
        else:
            raise SystemExit(f"cannot fetch {JOBS_REPO}/{ORDER_PATH} (gh auth?) and no cached copy; pass --order")
    order = depgraph.read_order(cache.read_text(encoding="utf-8"))
    print(f"merge order: {len(order)} roadmaps ({cache})")
    return order


def ensure_upstream(clone: Path, update: bool) -> None:
    remotes = run(["git", "-C", str(clone), "remote"]).split()
    if "upstream" not in remotes:
        run(["git", "-C", str(clone), "remote", "add", "upstream", CONTENT_URL])
        update = True
    if update:
        run(["git", "-C", str(clone), "fetch", "--quiet", "upstream", "main"])


def merged_roadmaps(clone: Path) -> set[str]:
    from tauceti_roadmap_worker import gates
    listing = run(["git", "-C", str(clone), "ls-tree", "-r", "--name-only", "upstream/main", "--",
                   "TauCetiRoadmap", "Completed"])
    return gates.roadmap_names(listing.splitlines(), ("TauCetiRoadmap", "Completed"))


# --- advisories: what the reviews flagged although the gate passed --------------------------------

def strip_code(text: str) -> str:
    text = re.sub(r"^\s*(```|~~~).*?^\s*\1", "", text, flags=re.M | re.S)
    return re.sub(r"`[^`\n]*`", "", text)


def lines_matching(text: str, pattern: str, flags: int = 0) -> list[str]:
    rx = re.compile(pattern, flags)
    return [f"{i}: {line.strip()[:110]}" for i, line in enumerate(text.splitlines(), 1) if rx.search(line)]


REQUIRED = ["## Scope and ownership", "## Conventions", "## Exact supplier contracts", "## How to read the build",
            "## Layer 0", "## Downstream consumers", "## References"]
OLD_HEADINGS = r"^##\s+(Standing conventions|Ordering|Provenance|Roadmap for a roadmap|Porting guidance|" \
               r"What Mathlib|What is missing|The build, in layers|Successor)"
PROCESS = (r"\bnot yet\b|\buntil the pin\b|\bwhen the pin\b|\bpin moves\b|\bfor now\b|\boptional(ly)?\b|\bdeferred\b|"
           r"\bfor later\b|\bfollow-up\b|\bthis pull request\b|\bthis PR\b|\bno longer\b|\bDo not implement\b|"
           r"\bwas (removed|renamed|added)\b|\bonly so that\b|\bstands? for\b")
EDITION = (r"github\.com/Commutator-IO|grothendieck-project|transcription project|Lean appendix|\bthe edition\b|"
           r"MathOverflow|mathoverflow\.net|private communication|OpenAI preprint")
HEX = r"\b(?=[0-9a-f]*[a-f])(?=[0-9a-f]*\d)[0-9a-f]{7,40}\b"
CATALOGUE = r"suggest Lean forms|particular milestones|finishes neither|is allowed in this human-owned|only so that this file"
KEYWORDS = {"theorem", "def", "structure", "class", "instance", "example", "abbrev", "sorry", "Type", "Prop", "Sort",
            "fun", "match", "with", "by", "have", "show", "from", "where", "deriving", "namespace", "section", "open",
            "variable", "noncomputable", "import", "true", "false", "True", "False", "simp", "rfl", "decide"}


def library_words(clone: Path) -> set[str]:
    """Every identifier-like token of the pinned Mathlib and Tau Ceti sources (for telling a library
    name from a name the README presents as this roadmap's own)."""
    words: set[str] = set()
    tok = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
    for root in (clone / ".lake/packages/mathlib/Mathlib", clone / ".lake/packages/TauCeti/TauCeti"):
        if not root.is_dir():
            continue
        for f in root.rglob("*.lean"):
            for w in tok.findall(f.read_text(encoding="utf-8", errors="replace")):
                words.add(w)
                if "." in w:
                    words.update(w.split("."))
    return words


def advisories(name: str, readme: str, lean: str, clone: Path, scan_library: bool) -> dict[str, list[str]]:
    from tauceti_roadmap_worker import gates
    adv: dict[str, list[str]] = {}
    prose = strip_code(readme)

    adv["pr-numbers (gate sees only `#123)`)"] = lines_matching(readme, r"(?<![\w&/])#\d{3,5}\b") + \
        [f"Suggested.lean {h}" for h in lines_matching(lean, r"(?<![\w&/])#\d{3,5}\b")]
    adv["process narrative"] = lines_matching(prose, PROCESS, re.I)
    adv["edition, Provenance, unrefereed sources"] = lines_matching(readme, EDITION, re.I) + \
        [f"Suggested.lean {h}" for h in lines_matching(lean, EDITION, re.I)]
    adv["manifest words in prose (uncertified/unverified)"] = lines_matching(prose, r"\b(un)?certified\b|\bunverified\b", re.I)
    adv["commit hashes / pins in README"] = lines_matching(prose, HEX)
    adv["old or forbidden headings"] = lines_matching(readme, OLD_HEADINGS, re.I | re.M)
    missing = [h for h in REQUIRED if not re.search("^" + re.escape(h), readme, re.M)]
    if not re.search(r"^\*\*Summary\.\*\*", readme, re.M):
        missing.insert(0, "**Summary.** paragraph")
    adv["missing house headings"] = missing

    # per layer: Examples, Dependencies; per target: Needs and three Checks
    shape: list[str] = []
    layers = re.split(r"^(?=## )", readme, flags=re.M)
    for block in layers:
        head = block.splitlines()[0] if block.strip() else ""
        if not head.startswith("## Layer"):
            continue
        for sub in ("### Examples", "### Dependencies"):
            if not re.search("^" + re.escape(sub), block, re.M):
                shape.append(f"{head[:60]}: no {sub}")
        for t in re.split(r"^(?=### )", block, flags=re.M)[1:]:
            th = t.splitlines()[0]
            if not re.match(r"### \d+\.\d+", th):
                continue
            if "*Needs:*" not in t:
                shape.append(f"{th[:60]}: no *Needs:* line")
            m = re.search(r"\*{1,2}Checks[.:]\*{1,2}(.*?)(?=^### |\Z)", t, re.S | re.M)
            n = len(re.findall(r"^\s*- ", m.group(1), re.M)) if m else 0
            if n < 3:
                shape.append(f"{th[:60]}: {n} Check(s) (a definition needs at least three)")
    adv["layer and target shape"] = shape

    long_lines, fenced = [], False
    for i, line in enumerate(readme.splitlines(), 1):
        if re.match(r"\s*(```|~~~)", line):
            fenced = not fenced
        if not fenced and len(line) > 100 and not line.lstrip().startswith("|") and "http" not in line:
            long_lines.append(f"{i}: {len(line)} characters")
    adv["README lines over 100 characters"] = long_lines

    # names: both directions
    decls = gates.lean_names(lean)
    short = {d.split(".")[-1] for d in decls}
    adv["Lean names absent from the README (name each where its target is stated)"] = sorted(
        d for d in decls if not re.search(r"\b" + re.escape(d.split(".")[-1]) + r"\b", readme))
    if scan_library:
        words = library_words(clone)
        if words:
            ids = set(re.findall(r"`([A-Za-z][A-Za-z0-9_'.]{2,})`", readme))
            suspects = []
            for i in sorted(ids):
                last = i.split(".")[-1]
                looks_lean = "_" in i or "." in i or re.search(r"[a-z][A-Z]", i)
                if not looks_lean or i in KEYWORDS or i in decls or last in short:
                    continue
                if i in words or last in words:
                    continue
                suspects.append(i)
            adv["backticked names neither in Suggested.lean nor at the pins (own name: declare it or write prose; "
                "supplier roadmap's name: say whose it is)"] = suspects
    if re.search(r"^open .*\bComplex\b", lean, re.M) and "π" in lean and not re.search(r"open scoped .*\bReal\b|Real\.pi", lean):
        adv["auto-bound π"] = ["`open Complex` without `open scoped Real`: `π` becomes an auto-bound implicit variable"]

    # Lean form
    form = []
    doc = re.search(r"/-!(.*?)-/", lean, re.S)
    if not doc or "target signatures" not in doc.group(1):
        form.append("module docstring is not '<title>: target signatures'")
    if doc and re.search(CATALOGUE, doc.group(1), re.I):
        form.append("module docstring describes a catalogue of suggested forms, not the acceptance test")
    code = gates.strip_lean_comments(lean)
    for kw, line, block in gates.lean_blocks(lean):
        if kw in ("def", "abbrev", "theorem", "structure", "class", "inductive"):
            before = lean.splitlines()[:line - 1]
            prev = "\n".join(before[-30:])
            if not re.search(r"-/\s*(@\[[^\]]*\]\s*)?(noncomputable\s+|protected\s+|private\s+)*$", prev):
                first = block.strip().splitlines()[0][:80]
                form.append(f"line {line}: no docstring on `{first}`")
    if re.search(r"^\s*lemma\b", code, re.M):
        form.append("`lemma` used: write `theorem`")
    adv["Suggested.lean form"] = form

    # consumers on main
    hits = run(["git", "-C", str(clone), "grep", "-l", "-w", name, "upstream/main", "--", "TauCetiRoadmap", "Completed"],
               check=False).split()
    others = sorted({h.split(":", 1)[1].split("/")[-2] for h in hits if h.endswith("README.md")} - {name})
    section = re.search(r"^## Downstream consumers(.*?)(?=^## |\Z)", readme, re.S | re.M)
    named = section.group(1) if section else ""
    adv["roadmaps on main naming this one, absent from Downstream consumers"] = [o for o in others if o not in named]
    return {k: v for k, v in adv.items() if v}


def build(clone: Path, name: str) -> list[str]:
    from tauceti_roadmap_worker import gates
    print("lake exe cache get …")
    subprocess.run(["lake", "exe", "cache", "get"], cwd=clone, check=False)
    guard = subprocess.run(["lake", "build", "Mathlib", "--no-build"], cwd=clone, capture_output=True, text=True)
    if guard.returncode != 0:
        return ["Mathlib is not fully cached at this pin (`lake build Mathlib --no-build` failed): not building "
                "Mathlib from source; fix the cache first"]
    module = f"TauCetiRoadmap.{name}.Suggested"
    print(f"lake build {module} …")
    text, code, failure = gates.build_output(clone, f"lake build {module}")
    return [failure] if failure else gates.build_output_problems(text, code or 0)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("name", help="the roadmap's name, e.g. GrothendieckTeichmuller")
    ap.add_argument("--clone", required=True, help="a clone or worktree of TauCetiRoadmap with the branch checked out")
    ap.add_argument("--folder", default="", help="path under TauCetiRoadmap/ when nested (default: the name)")
    ap.add_argument("--worker", default=str(CACHE / "TauCetiRoadmapWorker"))
    ap.add_argument("--order", default="", help="a merge-order file instead of the jobs repository's")
    ap.add_argument("--no-update", action="store_true", help="do not pull the worker, ORDER.txt or upstream/main")
    ap.add_argument("--no-library-scan", action="store_true", help="skip the scan of the pinned sources for names")
    ap.add_argument("--build", action="store_true", help="also run the targeted build")
    args = ap.parse_args()

    worker, clone, update = Path(args.worker).expanduser(), Path(args.clone).expanduser().resolve(), not args.no_update
    ensure_worker(worker, update)
    sys.path.insert(0, str(worker))
    from tauceti_roadmap_worker import gates
    from tauceti_roadmap_worker.cli import depcheck_lines

    CACHE.mkdir(parents=True, exist_ok=True)
    order = fetch_order(args.order, CACHE / "ORDER.txt", update)
    ensure_upstream(clone, update)
    merged = merged_roadmaps(clone)
    folder_rel = args.folder.strip("/") or args.name
    folder = clone / "TauCetiRoadmap" / folder_rel
    readme = (folder / "README.md").read_text(encoding="utf-8")
    lean = (folder / "Suggested.lean").read_text(encoding="utf-8") if (folder / "Suggested.lean").is_file() else ""

    opts = gates.GateOptions(order=None, merged=merged, tauceti_sources=gates.tauceti_sources(clone))
    opts.folder = args.folder
    result = gates.run_gate(clone, args.name, opts, base="upstream/main")

    in_order = args.name in order
    plain, _ = depcheck_lines(args.name, readme, {}, order, set(), candidate=False, movable=True, merged=merged)
    real_lines, real_problems = depcheck_lines(args.name, readme, {}, order, set(), candidate=not in_order,
                                               movable=True, merged=merged)
    result.add("depcheck", real_problems)

    if args.build:
        result.add("build", build(clone, folder_rel.replace("/", ".")))

    print()
    print(result.summary())
    for key, hits in result.details.items():
        print(f"\n[{key}] {gates.GATE_RULES.get(key, '')}")
        for h in hits[:25]:
            print(f"  {h.line}: {h.text}" if hasattr(h, "line") else f"  {h}")
    print("\n[depcheck]")
    if not in_order:
        print("  plain check: " + " | ".join(plain))
        print(f"  {args.name} is not in ORDER.txt, which lists the maintainers' open roadmaps; a NOT IN ORDER line "
              f"is a local artefact, since the board inserts the roadmap after its last supplier. Checked as placed "
              f"there:")
    for line in real_lines:
        print("  " + line)
    print("  (other authors' open pull requests are not read here: a cycle through one is not detected)")

    adv = advisories(args.name, readme, lean, clone, not args.no_library_scan)
    if adv:
        print("\nAdvisories (the gate passes these; the reviews of October 2026 did not):")
        for key, items in adv.items():
            print(f"\n- {key}")
            for item in items[:30]:
                print(f"    {item}")
            if len(items) > 30:
                print(f"    … and {len(items) - 30} more")
    return result.exit_code


if __name__ == "__main__":
    sys.exit(main())
