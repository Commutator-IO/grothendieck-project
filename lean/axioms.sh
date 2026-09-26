#!/usr/bin/env bash
# Print the axioms of every theorem in Grothendieck/*.lean and fail on any
# beyond Lean's three standard ones. Run after `lake build`, from lean/.
# The names are read from the files — `theorem <name>` inside the file's
# `namespace` — so a new proof is checked without editing a list.
set -euo pipefail
out="${TMPDIR:-/tmp}/Axioms.lean"
{
  echo 'import Grothendieck'
  for f in Grothendieck/*.lean; do
    awk '
      /^namespace / { ns[++d] = $2; next }
      /^end / && d > 0 && $2 == ns[d] { d--; next }
      /^(private )?theorem / {
        name = ($1 == "private") ? $3 : $2
        if ($1 == "private") next
        full = ""
        for (i = 1; i <= d; i++) full = full ns[i] "."
        print "#print axioms " full name
      }' "$f"
  done
} > "$out"
n=$(grep -c '^#print' "$out")
res=$(lake env lean "$out")
echo "$res"
standard='(propext|Classical\.choice|Quot\.sound)'
if [ "$(echo "$res" | grep -c "axioms")" -ne "$n" ] ||
   echo "$res" | grep -qvE "^'.+' (depends on axioms: \[$standard(, $standard)*\]|does not depend on any axioms)$"; then
  echo "::error::a theorem depends on a non-standard axiom, or was not found." >&2
  exit 1
fi
echo "$n theorems, standard axioms only."
