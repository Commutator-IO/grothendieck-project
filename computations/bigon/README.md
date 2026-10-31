# Bigon-free pseudoline arrangements (folder 80)

This directory tests the problem « A dichotomy for arrangements without
bigonal pseudolines » of `docs/problems/article.tex` (folder 80, pp. 20, 24,
28) by computer. It also tests the numbering question (the Lemme of p. 28).

## What is computed

An *arrangement* is a finite family of at least three pseudolines in the
real projective plane, not all through one point. Any two of them meet
exactly once, and several may pass through one point, so non-simple
arrangements are included. Two arrangements are isomorphic when a
homeomorphism of the plane (reflections allowed) carries one onto the other.
Isomorphism classes of arrangements of n pseudolines are the same thing as
reorientation classes of rank-3 oriented matroids on n elements whose
underlying matroid is simple. Simple arrangements correspond to uniform
oriented matroids.

A pseudoline is *bigonal* when it carries exactly two vertices of the
arrangement. Three sub-arrangement types are tested:

* `II_5`: five pseudolines, no three concurrent.
* `II'_{3,2}`: five pseudolines with exactly one concurrent triple. These are
  three lines through one point and two through another, without the line
  joining the two points.
* `III_6`: the complete quadrangle. Six pseudolines with exactly four
  concurrent triples, each pseudoline lying in two of them.

`II_4` is four pseudolines in general position.

All of these conditions depend only on which pseudolines are concurrent.
They are tested on the intersection lattice. This loses nothing. The
enumeration finds exactly one class with each of these lattices: one
`II_5`, one `II'_{3,2}` and one complete quadrangle. The two five-pseudoline
types are also the only bigon-free arrangements of five pseudolines, as the
problems paper says.

**Dichotomy.** Is every bigon-free arrangement either `II_4`, or does it
contain a sub-arrangement of type `II_5`, `II'_{3,2}` or `III_6`?

**Numbering.** Can the pseudolines be numbered D_1, ..., D_n so that one of
the following holds?

* D_1..D_4 is `II_4`, and for i ≥ 5, D_i is not bigonal in K_i = {D_1..D_i}.
* D_1..D_6 is `III_6`, and the same holds for i ≥ 7.

The condition "D meets the lines already placed in at least three distinct
points" is monotone in the set already placed. So a numbering from a given
start exists iff the greedy closure of that start is the whole arrangement.
We also test a *strong* form, in which every K_i from the start on is
bigon-free as a whole. That test is a search over subsets.

## Method

The program is `enum.c`, in C, compiled by `run.py` with gcc. Python alone
was too slow for n = 9.

* **Extensions.** Level n+1 is built from one representative of each class
  at level n. For each representative the program backtracks over the new
  values chi(a,b,n) of the chirotope, in {+, 0, -}, or in {+, -} for the
  simple-only run. Two conditions prune the search:
  * the 3-term Grassmann–Plücker relations that contain a new value;
  * the matroid condition for a simple rank-3 matroid: every 4-set
    contains 0, 1 or 4 zero triples.

  These two conditions characterise chirotopes (Björner–Las
  Vergnas–Sturmfels–White–Ziegler, *Oriented Matroids*, Thm 3.6.2). Every
  arrangement of n+1 ≥ 4 pseudolines has a pseudoline whose deletion still
  has rank 3, so this process reaches every class.
* **Isomorphism.** Each extension gets a canonical form, built in four steps.
  1. Build the cell decomposition of the sphere (the double cover of the
     arrangement) from the cocircuits, with its flag graph and the three
     involutions s0, s1, s2.
  2. From a start flag, a breadth-first search orders the pseudolines by
     first appearance. The search also reorients the arrangement so that
     the start face is the all-positive tope.
  3. The relabelled chirotope, normalised up to global sign, is the code of
     that start flag.
  4. The canonical form is the least code over the start flags whose
     invariant (vertex degree, face size, degree at the other end, size of
     the other face) is maximal.

  Two chirotopes get the same form exactly when they differ by relabelling,
  reorientation and global sign.
* **Avoid mode.** This run enumerates the class 𝒜 of arrangements that
  contain no `II_5`, no `II'_{3,2}` and no `III_6`. 𝒜 is closed under
  deletion, so it can be generated level by level by extending only its own
  members. When a pseudoline is added, only the subsets that contain it are
  tested.
* `analyse.py` re-reads the bigon-free classes from the intersection lattice
  and checks the dichotomy, the numbering and the strong numbering
  independently of the C code.

### Cross-check against known counts

| n | all classes (this run) | known | simple (this run) | known |
|---|---|---|---|---|
| 3 | 1 | 1 | 1 | 1 |
| 4 | 2 | 2 | 1 | 1 |
| 5 | 4 | 4 | 1 | 1 |
| 6 | 17 | 17 | 4 | 4 |
| 7 | 143 | 143 | 11 | 11 |
| 8 | 4890 | 4890 | 135 | 135 |
| 9 | 461053 | 461053 | 4382 | 4382 |
| 10 | not run | 95052532 | 312356 | 312356 |

The known values are Finschi–Fukuda's counts of reorientation classes of
rank-3 oriented matroids, and OEIS A006248 for simple arrangements.
`run.py` asserts that the computed counts are equal to them. The sequence
"1, 1, 1, 2, 4, 11, 135, 4382" in the task that led to this computation has
an extra 2. The correct simple counts for n = 3..10 are 1, 1, 1, 4, 11,
135, 4382, 312356.

## Result

**Dichotomy: true, with no counterexample.**

* *Up to n = 9.* All 461049 bigon-free arrangements with n ≤ 9 satisfy it,
  simple and non-simple. The remaining four classes for n = 9 are I_9 and
  I_{6,2}, I_{5,3}, I_{4,4}.
* *Simple arrangements, n = 10.* All 312356 satisfy it trivially, since each
  contains `II_5`.
* *All n.* The avoid-mode enumeration gives:
  * 𝒜_4 = {II_4, I_4};
  * 𝒜_5 = {I_5, I_{2,2}};
  * 𝒜_n = {I_n}, the near-pencil, for 6 ≤ n ≤ 16.

  The only bigon-free member is `II_4`. A short induction extends this to
  every n:

  1. Let A be in 𝒜 with n+1 ≥ 7 pseudolines. Delete a pseudoline whose
     deletion keeps rank 3. What is left is in 𝒜_n = {I_n}: a pencil of
     n−1 ≥ 5 pseudolines through a point p, and a transversal t.
  2. Suppose the added pseudoline L does not pass through p. Then L meets
     the pencil in n−1 distinct points, and at most one of them lies on t.
  3. Take three pencil lines whose points on L avoid that one. Together with
     L and t they form a `II'_{3,2}`, whose only triple point is p. So
     A ∉ 𝒜.
  4. Hence L passes through p, and A = I_{n+1}.

  So every bigon-free arrangement other than `II_4` contains `II_5`,
  `II'_{3,2}` or `III_6`. This holds for every n and for pseudolines, not
  only for straight lines. The proof is the computation for n ≤ 6 together
  with this step.

**Numbering: true for n ≤ 9.** Every bigon-free arrangement with n ≤ 9,
including the non-simple ones, has a numbering of the required kind. So do
the simple arrangements with n = 10. Every one of them can be started from
`II_4`, except `III_6` itself (n = 6), which must start from `III_6`: from
any `II_4` inside it, the remaining two pseudolines are bigonal. The strong
form, with every K_i from the start on bigon-free, also holds in every case.

For the numbering, arrangements with n ≥ 10 that are not simple were not
enumerated: there are 95 million classes at n = 10.

The full output is in `results.txt`. There, the dichotomy column names the
first pattern found, scanning subsets in lexicographic order.

## How to run

```
cd computations/bigon
python3 run.py            # all n ≤ 9, simple n ≤ 9, avoid n ≤ 16, analysis: ≈ 5 min
python3 run.py --simple10 # also the simple arrangements of 10 pseudolines: ≈ 6 more min
python3 run.py --quick    # n ≤ 8 only: seconds
./out/enum all|simple|avoid NMAX out   # after compiling, one enumeration
```

The tools are Python 3 (standard library only) and gcc. The per-class files
go to `out/`, which is not versioned (45 MB for n = 9). There is one line
per bigon-free class: its multiple points, then its canonical chirotope.
The pseudolines are written in hex digits.

## Three-pencil test (Problem 14, 31 October 2026)

`three_pencil.py` tests Problem 14 of the problems paper (pp. 39–54: is a
bigon-free arrangement determined by its labelled skeleton?) on the case
that Lean leaves open. `full_of_fourth'` (`lean/Grothendieck/Folder80Maps3.lean`)
proves it when every triangle has a fourth pseudoline through none of its
vertices. A triangle without one has three multiple vertices with every other
pseudoline through one of them. So the open case is the arrangements lying in
the three pencils at the vertices of a triangle, starting with `III_6`.

For each bigon-free class of `out/all_n.txt` in that case, the script reads
the order of the points along each pseudoline from the rank-2 contraction of
the chirotope. A labelled-skeleton isomorphism is then a permutation of the
pseudolines that maps points to points and the cycle of points on each
pseudoline to the cycle on its image, up to rotation and reflection. An
arrangement isomorphism is a permutation that preserves the chirotope up to
reorientation and global sign. Two checks:

1. every automorphism of the labelled skeleton comes from an automorphism of
   the arrangement;
2. two different classes never have isomorphic labelled skeleta (compared
   among classes with the same point sizes and the same numbers of points per
   pseudoline).

**Result: no counterexample for n ≤ 9.** There are 3, 5, 22 and 102
three-pencil bigon-free classes for n = 6, 7, 8, 9 (none for n ≤ 5). Every
skeleton automorphism is realised (groups of order up to 24; `III_6` has 24,
its 𝔖₄), and none of the 904 pairs of classes compared has isomorphic
skeleta. Run `python3 three_pencil.py 9` after `run.py` (about a minute);
the output is in `three_pencil_results.txt`. This is evidence for the
statement in the open case, not a proof: n ≥ 10 is not enumerated.

## Face-width test (Problem 14, 31 October 2026)

`three_pencil_facewidth.py` tests a possible route to the three-pencil case:
if the skeleton graph G is 3-connected and its embedding in ℝP² has large
enough face-width, a uniqueness-of-embedding theorem would make every
automorphism of G, labelled or not, carry facial walks to facial walks, so
that it comes from a homeomorphism.

**The theorems (as read).** Mohar, « Face-width of embedded graphs », Math.
Slovaca 47 (1997) 35–63, read in the DML-CZ copy:

* p. 37, Prop. 3.1: fw = ½ ew(Γ), where Γ is the vertex-face (radial) graph.
* p. 40, Prop. 3.9: for a non-planar embedding, « G 3-connected and fw ≥ 3 »
  is equivalent to the embedding being polyhedral (all facial walks are
  cycles, and two faces meet in nothing, a vertex or an edge).
* p. 48, §6, reporting Robertson (in Robertson–Vitray 1990): a 3-connected
  graph embedded in a surface of genus g with fw ≥ 2g + 3 is uniquely
  embeddable in that surface. « Unique » means that every other embedding in
  that surface has the same facial walks. That forces every automorphism to
  be induced by a homeomorphism. For ℝP², g = 1, so the bound is **fw ≥ 5**.
* p. 48, Negami (1985): a 5-connected projective-planar graph other than K₆
  that contains a subdivision of K₆ has a unique embedding in ℝP². Also
  p. 48: some 4-connected triangulations of ℝP² are not uniquely embeddable.
  K₆ is excluded from Negami's statement. It is 5-connected and its
  embedding in ℝP² has fw = 3. By our own count, not read in a source, it
  has at least 720/60 = 12 equivalence classes of embeddings: 60 is the
  order of the map group of the hemi-icosahedron. So fw = 3 does not suffice in ℝP²,
  even with high connectivity.

Not read, for want of an open copy: Robertson–Vitray 1990; Mohar–Robertson–
Vitray, Discrete Math. 149 (1996); Vitray 1992 and 1993; Negami 1985 and 1988;
Mohar–Thomassen, *Graphs on Surfaces*, ch. 5.

**Method.** The script reads the 132 three-pencil classes as
`three_pencil.py` does and computes the following for each one.

* *G*: points as vertices, and segments between consecutive points as edges.
  The script checks that G is a simple graph. A pseudoline with k ≥ 3 points
  gives k distinct edges, and two points share at most one pseudoline.
* *κ(G)*: Menger, by unit-capacity max-flow on the vertex-split digraph over
  all non-adjacent pairs.
* *fw*: the double cover of the arrangement is the sphere complex of
  covectors (cocircuits, one-zero covectors, topes), obtained by composing
  cocircuits. A non-contractible closed curve meeting G only in vertices
  lifts to a path from a vertex x to −x in the radial graph of the sphere. So
  fw = min over cocircuits X of dist(X, −X)/2, and the script records a
  witness curve.
* *Checks.*
  * A second computation of fw ≤ 3 or fw ≥ 4, by crossing parity: it goes
    through all 2- and 3-point curves and their faces, and requires the same
    parity on every pseudoline.
  * τ ≤ fw, where τ is the least number of points meeting every
    pseudoline. Two non-contractible curves of ℝP² intersect, so every
    non-contractible curve meets every pseudoline.
  * Polyhedrality agrees with (κ ≥ 3 and fw ≥ 3), as Prop. 3.9 requires.
  * The label-respecting automorphisms equal those of `three_pencil.py`.
* *Automorphisms*: |Aut G| of the bare graph, against the map automorphisms
  (those that preserve the facial cycles).

**Result.**

| n | classes | κ | fw | τ | polyhedral | curve through the 3 corners | Aut G > map group |
|---|---|---|---|---|---|---|---|
| 6 | 3 | 4 (all) | 3 (all) | 3 | 3 | 2 | **3** |
| 7 | 5 | 4 | 3 | 3 | 5 | 3 | 0 |
| 8 | 22 | 4 | 3 | 3 | 22 | 11 | 0 |
| 9 | 102 | 4 | 3 (76), **4 (26)** | 3 | 102 | 44 | 0 |

* All 132 embeddings are polyhedral: G is 4-connected and fw ∈ {3, 4}. No
  class reaches the fw ≥ 5 of the uniqueness theorem.
* fw ≤ 3 fails for 26 classes at n = 9: no non-contractible curve passes
  through three points only. In all 26, the three corners carry four
  pseudolines each. 42 classes at n = 9 have that shape, and in the other
  16 a curve passes through the three corners alone, so fw = 3 there. A curve through the three corners alone exists in only 60 of the
  132 classes. Inside a triangle of the three sides, a face touches two
  corners only if no pseudoline through the third corner crosses that
  triangle.
* **The route fails at n = 6.** In all three n = 6 classes, G has
  automorphisms that come from no homeomorphism. These are 12 against 6,
  6 against 3, and, for `III_6`, 144 against 24. For `III_6`, G = K₇ − K₃:
  the four triple points are joined to everything, and the three diagonal
  points are independent. So Aut G = 𝔖₄ × 𝔖₃, while the map group is 𝔖₄,
  and G has 6 inequivalent polyhedral embeddings in ℝP². Uniqueness of the
  embedding is false there, so no theorem can supply it. The labelled
  automorphisms are all induced (0 failures, as in `three_pencil.py`). For
  `III_6` the labels are what rule out the other embeddings.
* For n = 7, 8, 9 every automorphism of the bare graph is induced. Whether
  those graphs have other, non-isomorphic embeddings in ℝP² was not
  computed.

**Proved for every n:** τ = 3, hence fw ≥ 3, for every bigon-free
three-pencil arrangement. The proof:

1. τ = 1 would put all pseudolines through one point.
2. Suppose τ = 2, with points p and q. If pq is a pseudoline, it carries
   only p and q, which is a bigon.
3. Otherwise the arrangement is a pencil P at p and a pencil Q at q. A
   triangle (a, b, c) without a fourth line has, say, a, b in P and c in Q.
   A line of Q other than c must pass through a corner p, a∩c or b∩c. It
   cannot pass through p (it would be pq), nor through a∩c or b∩c (it meets
   c only at q). So Q = {c}, and the lines of P carry only two points.

Unproved: κ ≥ 3 for every n (κ ≤ 4 as soon as there is a double point), and
any upper bound on fw for n ≥ 10.

Run `python3 three_pencil_facewidth.py 9` after `run.py` (about two
minutes). The output is in `three_pencil_facewidth_results.txt`.

## The sign obstruction (`obstruction.py`)

The problems paper now answers Problem 14 by an argument on chirotopes. An isomorphism of
labelled skeleta with permutation s keeps, along each pseudoline, the cyclic order of the
vertices up to reversal. So ψ = χ′∘s · χ is, at each pseudoline, a constant times a cut. The
argument shows that such a ψ is a reorientation, provided every pseudoline carries three
vertices. The steps are proved in Lean in `lean/Grothendieck/Folder80Signs.lean`.

The script checks the same linear algebra over 𝔽₂ on each intersection lattice of
`out/all_n.txt`. It computes the dimension of the sign functions that are balanced on the
4-cycles at every pseudoline, minus the dimension of the reorientations.

| n | lattices | obstruction 0 |
|---|---|---|
| 4 | 1 | 1 |
| 5 | 2 | 2 |
| 6 | 10 | 10 |
| 7 | 61 | 61 |
| 8 | 946 | 946 |
| 9 | 36 193 | 36 193 |

Run `python3 obstruction.py 9` after `run.py` (about three minutes).
