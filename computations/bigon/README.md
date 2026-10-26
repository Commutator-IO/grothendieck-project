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
