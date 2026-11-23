#!/usr/bin/env python3
"""Step 6 of the pipeline (novelty filter), informal side: the ten rows of the Outputs table
run through the semantic search of TheoremSearch (https://www.theoremsearch.com/docs).

    python3 docs/bridges/novelty/theoremsearch.py > /dev/null

One POST https://api.theoremsearch.com/search per output, body {"query": <description>,
"n_results": 6}, no filter on source, year or citations, citation_weight left at 0 (ranking by
similarity alone). The service embeds the query with Qwen3-Embedding-8B, retrieves candidates by
approximate nearest neighbours and reranks them by cosine similarity with the slogans of the
indexed statements. Writes theoremsearch-<date>.json next to this file (queries, slogans,
similarities and paper metadata; statement bodies are left out, their licences being those of the
source papers) and prints the six results of each query. The run quoted in the article is
theoremsearch-2026-11-23.json; the service's index changes, so a later run may differ.
"""
import datetime
import json
import os
import urllib.request

Q=[("1 quiver De Morgan","The topos of set-valued representations of a quiver satisfies the weak law of excluded middle (is De Morgan) if and only if every vertex has at most one outgoing arrow."),
("2 automata","The topos of sets with an action of the free monoid on an alphabet (automata) is De Morgan if and only if the alphabet has at most one letter."),
("3 quiver Morita","Two quivers have equivalent categories of set-valued representations if and only if the quivers are isomorphic; the essential points of the representation topos are the vertices."),
("4 cyclic quiver","The presheaf topos on the cyclic quiver with n vertices has exactly 2^n + 1 subtoposes (Grothendieck topologies)."),
("5 T_n points","The topos of right actions of the full transformation monoid T_n has n essential points and n+1 subtoposes; similar counts for partial transformations, symmetric inverse monoid, order-preserving maps and matrices over a finite field."),
("6 corners Ore","The right Ore condition for a monoid M transfers to the corner monoid eMe for an idempotent e with 1 in MeM."),
("7 matrix monoid","The topos of sets with an action of the multiplicative monoid of n by n matrices over a field is equivalent to that of m by m matrices if and only if n = m."),
("8 subspace lattice","The presheaf topos on the lattice of subspaces of a vector space determines the dimension, and the field when the dimension is at least 3."),
("9 Z/n","The topos of sets with an action of the multiplicative monoid Z/n has 2^omega(n) essential points and a Dedekind number of subtoposes, where omega(n) is the number of prime factors."),
("10 compact Hausdorff","For a compact Hausdorff space X, the topos of sheaves Sh(X) is De Morgan if and only if the ring C(X,R) of continuous real functions is Dedekind complete.")]

API = "https://api.theoremsearch.com/search"


def search(query, n=6):
    req = urllib.request.Request(API, data=json.dumps({"query": query, "n_results": n}).encode(),
                                 headers={"Content-Type": "application/json"})
    return json.load(urllib.request.urlopen(req, timeout=60))


def main():
    date = datetime.date.today().isoformat()
    runs = []
    for name, query in Q:
        r = search(query)
        keep = ("theorem_id", "slogan_id", "name", "theorem_type", "slogan", "similarity", "score", "link")
        hits = [{k: t.get(k) for k in keep} | {"paper": {k: (t.get("paper") or {}).get(k)
                 for k in ("source", "title", "year", "primary_category")}} for t in r.get("theorems", [])]
        runs.append({"output": name, "query": query, "response": {"theorems": hits}})
        print("##", name)
        for t in r.get("theorems", []):
            p = t.get("paper") or {}
            print(f"  {t['similarity']:.3f}  {(t.get('slogan') or '')[:110]}  [{p.get('title', '')[:50]} {p.get('year')}]")
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), f"theoremsearch-{date}.json")
    with open(out, "w") as f:
        json.dump({"date": date, "api": API, "n_results": 6, "runs": runs}, f, indent=1, ensure_ascii=False)


if __name__ == "__main__":
    main()
