#!/usr/bin/env python3
"""Elaboration probes on a scratch copy of a roadmap's Suggested.lean, the ones the maintainer's
reviewer runs before a verdict:

    python3 probe.py <path/to/Suggested.lean> --clone <TauCetiRoadmap clone> [--out DIR] [--timeout S]

One `lake env lean` run (one Lean process; Mathlib is never rebuilt) on a copy that adds:

1. Errors on the original lines: the file does not elaborate.
2. For every theorem whose body is `sorry`, an `example` with the same statement closed by
   `first | rfl | simp | decide | infer_instance | norm_num | fun_prop | aesop`. An example that
   elaborates is padding (delete the theorem; the README keeps it as a Check or API bullet), unless
   it closes only through an instance whose field it is.
3. `#print axioms` of every definition, abbreviation, structure and named instance. `sorryAx` there
   is sorry'd data the gate's `sorry-data` scanner misses (a definition whose body uses a `sorry`'d
   theorem: `stdDisks` built on `norm_hemiPoint := by sorry`).
4. `#check @name` of every declaration, written to <out>/signatures.txt: compare each elaborated
   type with its README statement (lost binders, generality). A binder of the elaborated type whose
   name no binder of the source introduces is reported as auto-bound: the `{π : ℂ}` that
   `open Complex` without `open scoped Real` silently adds (a global `set_option autoImplicit
   false` in the copy would detect it too, but it changes elaboration elsewhere and gave a false
   error on a file that builds).

The real Suggested.lean never contains `set_option`, `#print axioms` or `#check` lists: they live
only in this scratch copy.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

TACTIC = "first | rfl | simp | decide | infer_instance | norm_num | fun_prop | aesop"
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*"
                  r"(?P<kw>theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+(?P<name>[^\s:({\[⦃]+)?", re.M)
STOP = re.compile(r"^(?:/--|/-!|@\[|(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|instance|"
                  r"structure|class|inductive|example|namespace|section|end|open|variable|universe|#)\b)", re.M)


def blocks(lean: str):
    """(kind, name, first line, text) of each declaration, the text running to the next command."""
    out = []
    for m in DECL.finditer(lean):
        start = m.start()
        rest = lean[m.end():]
        nxt = STOP.search(rest)
        end = m.end() + (nxt.start() if nxt else len(rest))
        out.append((m.group("kw"), m.group("name") or "", lean.count("\n", 0, start) + 1, lean[start:end]))
    return out


def example_of(text: str) -> str | None:
    """`example <signature> := by <TACTIC>` for a theorem whose body is `sorry`, else None."""
    body = re.sub(r"--[^\n]*", "", text).rstrip()
    m = re.match(r"(?s)(?:@\[[^\]]*\]\s*)?(?:(?:private|protected)\s+)*(?:theorem|lemma)\s+\S+(?P<sig>.*):=\s*(?:by\s+)?sorry\s*$",
                 body)
    return f"example{m.group('sig').rstrip()} := by\n  {TACTIC}\n" if m else None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("lean", help="the roadmap's Suggested.lean")
    ap.add_argument("--clone", required=True, help="the TauCetiRoadmap clone whose .lake holds the pinned packages")
    ap.add_argument("--out", default="", help="directory for the probe file and signatures.txt (default: a temp dir)")
    ap.add_argument("--timeout", type=int, default=3600)
    args = ap.parse_args()

    src = Path(args.lean).read_text(encoding="utf-8")
    lines = src.splitlines()
    out = Path(args.out) if args.out else Path(tempfile.mkdtemp(prefix="tauceti-probe-"))
    out.mkdir(parents=True, exist_ok=True)

    ns = re.findall(r"^namespace\s+(\S+)", src, re.M)
    last_end = max((i for i, l in enumerate(lines) if ns and re.match(rf"^end\s+{re.escape(ns[0])}\s*$", l)), default=None)
    head = lines[:last_end] if last_end is not None else lines
    tail = lines[last_end:] if last_end is not None else []
    imp = max((i for i, l in enumerate(head) if re.match(r"^\s*(public\s+)?import\b", l)), default=-1)
    body = list(head)
    unshift = lambda n: n
    binder = re.compile(r"[({⦃\[]\s*([^:()\[\]{}⦃⦄]+?)\s*:")
    declared = {w for g in binder.findall(src) for w in g.split()}

    decls = blocks(src)
    probes: dict[int, tuple[str, str]] = {}               # probe line -> (purpose, declaration)
    extra: list[str] = ["", "/-! ## Probes (scratch only) -/", ""]

    def add(text: str, purpose: str, name: str) -> None:
        probes[len(body) + len(extra) + 1] = (purpose, name)
        extra.extend(text.rstrip("\n").split("\n"))

    for kind, name, _line, text in decls:
        if kind in ("theorem", "lemma") and (ex := example_of(text)):
            add(ex, "one-tactic", name)
    for kind, name, _line, _text in decls:
        if name and kind in ("def", "abbrev", "structure", "class", "inductive", "instance"):
            add(f"#print axioms {name}", "axioms", name)
    for kind, name, _line, _text in decls:
        if name:
            add(f"#check @{name}", "check", name)
    probe = out / "Probe.lean"
    probe.write_text("\n".join(body + extra + tail) + "\n", encoding="utf-8")
    n_body = len(body)

    print(f"probe file: {probe} ({len(decls)} declarations); running lake env lean (one process) …")
    try:
        run = subprocess.run(["lake", "env", "lean", "--json", str(probe)], cwd=args.clone, capture_output=True,
                             text=True, timeout=args.timeout)
    except subprocess.TimeoutExpired:
        print("timed out")
        return 2
    (out / "lean-output.jsonl").write_text(run.stdout + run.stderr, encoding="utf-8")
    sev = {"information": "info", "warning": "warning", "error": "error"}
    msgs: list[dict] = []
    for raw in run.stdout.splitlines():
        try:
            j = json.loads(raw)
        except ValueError:
            continue
        msgs.append({"line": j["pos"]["line"], "sev": sev.get(j.get("severity"), "info"), "msg": j.get("data", "")})
    if not msgs and run.returncode != 0:
        print("lean did not run:\n" + (run.stdout + run.stderr)[-2000:])
        return 2

    def owner(line: int):
        keys = [k for k in probes if k <= line]
        return probes[max(keys)] if keys else None

    original_errors = [m for m in msgs if m["sev"] == "error" and m["line"] <= n_body]
    failed = {owner(m["line"])[1] for m in msgs if m["sev"] == "error" and m["line"] > n_body and owner(m["line"])
              and owner(m["line"])[0] == "one-tactic"}
    closes = [name for (purpose, name) in probes.values() if purpose == "one-tactic" and name not in failed]
    sorry_data, signatures, autobound = [], [], []
    for m in msgs:
        o = owner(m["line"]) if m["line"] > n_body else None
        if not o:
            continue
        if o[0] == "axioms" and "sorryAx" in m["msg"]:
            sorry_data.append(o[1])
        if o[0] == "check" and m["sev"] == "info":
            signatures.append(m["msg"].strip())
            sig = m["msg"].split(":", 1)[1] if ":" in m["msg"] else ""
            for g in binder.findall(sig):
                for w in g.split():
                    if w not in declared and "✝" not in w and not w.startswith("inst"):
                        autobound.append(f"{o[1]}: binder `{w}` introduced by no binder of the source")
    (out / "signatures.txt").write_text("\n\n".join(signatures) + "\n", encoding="utf-8")

    print("\n1. Errors on original lines (the file does not elaborate):")
    for m in original_errors[:30]:
        print(f"   line {unshift(m['line'])}: {m['msg'].splitlines()[0][:160]}")
    if not original_errors:
        print("   none")
    print("\n1b. Auto-bound variables (elaborated binders the source never declares):")
    for a in sorted(set(autobound))[:30]:
        print("   " + a)
    if not autobound:
        print("   none")
    print("\n2. Theorems closed by one tactic (padding: delete them; the README keeps them):")
    print("   " + (", ".join(closes) if closes else "none"))
    print("\n3. Definitions depending on sorryAx (sorry'd data):")
    print("   " + (", ".join(sorted(set(sorry_data))) if sorry_data else "none"))
    print(f"\n4. Elaborated signatures: {out / 'signatures.txt'} ({len(signatures)} entries); compare with the README.")
    other = [m for m in msgs if m["sev"] == "warning" and m["line"] <= n_body and "sorry" not in m["msg"]]
    if other:
        print("\nWarnings other than `sorry` on original lines (the build gate refuses them):")
        for m in other[:20]:
            print(f"   line {unshift(m['line'])}: {m['msg'].splitlines()[0][:160]}")
    return 1 if original_errors or closes or sorry_data or other or autobound else 0


if __name__ == "__main__":
    sys.exit(main())
