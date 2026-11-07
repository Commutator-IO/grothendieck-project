# Open-problems paper — peer review (working draft, 2026-10-26)

Scope: `docs/problems/article.tex` at HEAD `42f4c72` (fourteen problems, the pseudoline dichotomy proved in § 7), and its PDF. Read-only review; nothing in the article was edited.

Authorisation and handling: the author asked for this review of his own working paper, which is already public on the project site (Method tab). No confidentiality constraint applies; no venue policy yet (HAL deposit waits for the RHM referee). This is a working draft by a language model (skill `peer-review`), not a specialist's report: every point below must be checked by the author, and the mathematical points by a specialist of each field.

## 1. Summary of the paper

The note hands mathematicians fourteen statements from Grothendieck's Montpellier notes that the edition's Lean formalisation could not reach, each with source, context, what the literature search found, ideas, the Lean status and what would settle it. Fields: étale cohomology (1, 2), Hodge theory (3), group schemes (4), algebraic cycles (5), abelian schemes (6), reductive groups (7), topoi and stacks (8–11), Galois actions and moduli (12, 13), pseudoline arrangements (14). § 7 now also proves the page's pseudoline dichotomy (old Problem 14).

Strengths: every entry is tied to a folder and page; the « we » convention separates the edition's steps from the page; the limits (machine transcription, unchecked arguments, searches that report a search and not an absence) are stated up front and again in § 8; the facsimile links let a reader check the source.

## 2. Major comments

**M1. Three entries are no longer, or are barely, open problems: Problems 3, 6 and 7.**
- *Location:* Problems 3 (Ideas), 6 (Ideas), 7 (statement and Ideas).
- *Observation:* Problem 3's « Ideas » is a complete argument; I rechecked it: with $F_0$ of dimension $\le n-1$, $F_q$ of dimension $\le n-q$ and Hodge III 8.2.4 on the compact $F_q$, the $E_1$ term $H^{k-q}(F_q)(-q)$ has types in $[\max(q, k-n+q),\ \min(k,n)]$ for $q \ge 1$ and $[\max(0,k-n+1),\ \min(k,n-1)]$ for $q = 0$, all inside the box. Problem 6's « Ideas » also settles the question if its two steps hold (the composite being multiplication by $\mp\chi(\delta)$, and $\varphi\varphi(\delta) = \delta$ in dimension 2). Problem 7: the count follows from standard theory; the elements of $T$ normalising $T'$ are the $t$ with all $\alpha_i(t) = \theta(t)^{-1} = \lambda$, $\lambda^h = 1$; the image in $W$ is the set of $w$ with $w(x) \in \langle x\rangle$, of order $z\,\varphi(h)$ because the centraliser of the principal element $x$ in the adjoint group has component group $\Omega \cong P^\vee/Q^\vee$ and $x \sim x^k$ exactly for $k$ prime to $h$; lifting into $N(T')$ goes through Vinberg's conjugacy of Cartan subspaces in $\mathfrak g^{\zeta^j}$ (sketch in `outreach/mathoverflow/drafts.md`, post 7).
- *Why it matters:* a specialist will read an entry whose « Ideas » proves the statement as either a reference request or a mislabelled result; a problems paper loses credibility if its problems are exercises.
- *Requested action:* for 3, state the box as a proposition with the proof, and keep as open only the relative question of p. 119 and the $\ell$-adic form; for 6, write the two steps out with references (Mukai for $\varphi\varphi(\delta) = \delta$, the sign of the composite) and either state it as a proposition « modulo a specialist's check » or keep it open with that explicit gap; for 7, give the proof of $|N(T) \cap N(T')| = hz\varphi(h)$ and make the open question the one Grothendieck asks Kostant on p. 21: are $B$ and $B'$ in general position, and is there a distinguished orbit? (Check $B_2$ and $G_2$ before stating it.)

**M2. The figures of § 1 and the abstract are out of date or do not add up.**
- *Location:* § 1, paras 2–3; abstract.
- *Observation:* the register now holds 456 rows, 83 matched (the text says 463 and 81); 165 folders have transcriptions (the text says 164, as does the RHM article); « 203 open findings … 16 … 39 … 147 » adds up to 202: the CICM paper explains the missing one (« one finding was ill-posed as read and set aside »). The date line still says 25 October.
- *Why it matters:* a reader checking one number against the site or the companion paper will distrust the rest.
- *Requested action:* take the counts from the same source as the CICM paper (`docs/cicm/fig-counts.tex`) or say « about », add the set-aside finding, update the date.

**M3. Problem 1 uses $\ell$ for the residue characteristic.**
- *Location:* Problem 1, statement and « What is known ».
- *Observation:* in étale cohomology $\ell$ conventionally denotes a prime invertible on the scheme; here it is the characteristic of $V(\ell)$, the case where $\ell$ is *not* invertible. The MathOverflow draft uses $p$.
- *Why it matters:* the first problem of the paper invites a misreading in its first line.
- *Requested action:* use $p$ throughout Problem 1 (and Problem 2's « $r$ the residue characteristic » is fine as is).

**M4. Problem 2 omits the literature most likely to contain it.**
- *Location:* Problem 2, « What is known ».
- *Observation:* the entry says Serre's *Cohomologie galoisienne* II § 4 was not consulted. Exception (b) is about the virtual cohomological dimension of real fields, which is the subject of Scheiderer, *Real and Étale Cohomology* (LNM 1588, 1994).
- *Why it matters:* a specialist will look there first; « not consulted » reads as an invitation to do the search for us.
- *Requested action:* read Serre CG II § 4 and Scheiderer (chapters on cohomological dimension of fields with orderings) before circulating; if (b) is there, remove or narrow the problem.

**M5. Problems 4 and 6 rest on uncertain readings that have not been checked on the facsimile.**
- *Location:* Problem 4, Source (« inv. » uncertain); Problem 6, Source (« an uncertain "si" and an illegible word »).
- *Observation:* both statements may change with one word; Montpellier is offline until about 1 November.
- *Requested action:* check both on the facsimile before the paper goes to HAL or MathOverflow; until then, say in each entry that the statement is conditional on that reading (already partly done).

**M6. § 7 proves a theorem inside a problems paper without the usual apparatus.**
- *Location:* § 7, « Claim » and Steps 1–3.
- *Observation:* the proof is short and, as far as I can check, correct; but it is set in running text with « Claim », its attribution is implicit (the statement is Grothendieck's, boxed on p. 24, the proof the edition's), and Step 3's « two vertices of III₆ never cover all six sides » is asserted (true: vertices have multiplicity at most 3 and the two triple points share a side, so they cover at most five).
- *Requested action:* typeset it as a Proposition (« Grothendieck, p. 24; the proof is ours ») with a proof environment; add the one-line justification in Step 3; cite the precise statement of Sylvester–Gallai/Melchior for pseudolines (see the citation report); move the sentence « listed here as an open problem until 26 October 2026 » to a change log at the end, which the paper will need anyway as problems are removed.

**M7. Problem 4 is largely answered by Breen 1975, and the paper cites the wrong Breen.**
- *Location:* Problem 4, « Ideas » and « What would settle it »; bibliography `breen1978`.
- *Observation:* Breen, Ann. Sci. ÉNS 8 (1975), 339–352, proves $\mathcal Ext^i(G, H) = 0$ for $1 < i < 2p-2$, $G$ finite flat, $H$ smooth, under conditions that hold with $p = 3$ when 2 is invertible; it also gives $\mathcal Ext^2(\alpha_2, \mathbb G_a) \ne 0$. So the « first test » is settled (zero), the reading « si 2 inv. » is supported, and what remains is arbitrary quasi-coherent $M$ and the fppf version. Breen 1978 does not treat $\alpha_p$ (citation report § 2.1).
- *Requested action:* rewrite the entry around Breen 1975; either remove Problem 4 or narrow it to the quasi-coherent, fppf case and revisit the « tension with Illusie » sentence (Illusie's obstruction group has coefficients $t_{G_0} \otimes J$, a vector space, which Breen covers for $p \ge 3$).

**M8. Problem 12 misdescribes Pop's tripod variants.**
- *Location:* Problem 12, « What is known » and « Ideas ».
- *Observation:* Pop's variants (Invent. Math. 216, 2019) require varieties of dimension $> 1$ (Hypothesis (H)); they are not « for finite étale covers of $\mathbb P^1 \smallsetminus \{0,1,\infty\}$ ». The preprint is public.
- *Requested action:* correct the description, delete « could not be read », and rewrite « Ideas »: the dimension condition is exactly why the single-curve form is not covered, which strengthens the problem.

**M9. § 7 cites the wrong support for Sylvester–Gallai on pseudolines.**
- *Location:* § 7, Step 1.
- *Observation:* Melchior treats lines; Grünbaum 1972 is reported to *ask* the pseudoline question. The pseudoline version is Kelly–Rottenberg 1972 (Th. 3.6) and Bokowski–Pokora 2018 (Th. 1.3).
- *Requested action:* cite those two; one simple point suffices for Step 1, and a bigon-free arrangement is not a near-pencil.

**M10. Problem 1 says no global bound was found; SGA 4 prints two.**
- *Location:* Problem 1, « What is known » and « Ideas ».
- *Observation:* SGA 4 X 6.2 ($\cd_\ell X \le 2\dim X + 1$ for $X$ of finite type over $\mathbb Z$) and X 6.1 ($\cd_\ell \Spec\mathbb Z = 3$, printed); Mathew's Prop. 4.5 is a statement about residue fields, the affine-open bound being in its proof; X 5.1 needs $X$ noetherian.
- *Requested action:* see citation report § 2.4 and § 3.

## 3. Minor comments

- **m1. Unreferenced names.** Several results are named without a bibliography entry: Kostant 1959 and Springer 1974 (Problem 7), Deligne's theorem that coherent topoi have enough points (SGA 4 VI 9.0, Problem 8), Barr's theorem, Kato's $\ell$-dimension, Kleiman 1994, Charles 2013, Ramón Marí, Milne (Problem 5), Durfee–Saito, Steenbrink, Navarro Aznar, El Zein (Problem 3), Hoshi–Mochizuki (Problem 12), Looijenga, Boggi, Kato–Nakayama, Harer (Problem 13), Bose–Everett–Wismath, Robertson–Vitray, Mohar–Thomassen (Problem 14), Moerdijk's Zaragoza lectures (Problem 9), the two arXiv papers of Problem 11 (cited by number only). Either cite or drop the names.
- **m2. Bibliography hygiene.** `friedmanlaza` has no title; `illusie2023` has no venue; `pop2019` has no volume; `breen1978` has no pages; the list is no longer alphabetical (`grunbaum`, `melchior` sit before `felsnergoodman`). Details in the citation report.
- **m3. Problem 13 cites unpublished IHÉS documents** (1ILL35, 1ILL41). The IHÉS has not published the Grothendieck–Illusie fonds, so a reader cannot check them; the copy in Montpellier folder 119 can be. Keep the IHÉS references if the IHÉS agrees, and say how a reader can consult them.
- **m4. Problem 10, « Ideas ».** « We doubt that step, from memory and without having checked it » undercuts the entry. Either check the Baues remark (see citation report) and state the doubt precisely, or cut the sentence.
- **m5. Problem 9, statement.** « a "multiplicité topologique", a 2-category whose Hom-categories are discrete » is hard to parse: say what the objects are (topoi? étendues?) and whether « multiplicité » is the page's word for an étendue.
- **m6. Problem 12.** « anabelian curve » (the page's word) and « hyperbolic curve » (the literature's) should be identified once.
- **m7. Problem 6, « What would settle it ».** The real-multiplication test case (« $D \equiv 1 \bmod 8$ … the theta class is a sum of two classes of even $\chi$ ») is asserted without reference or proof; justify or remove.
- **m8. Problem 3.** The level bound $\min(i, 2n-1-i)$ needs $i \le 2n-1$; say what happens at $i \ge 2n$ (the group vanishes: the link has real dimension $2n-1$).
- **m9. Typography.** Problem 14 still says « bigon-free » and « bigonal » in two senses (pseudoline vs arrangement): define « bigon-free arrangement » once at the head of § 7 (no bigonal pseudoline).

## 4. Reproducibility and transparency

The two computations cited (`computations/kostant`, `computations/bigon`) are named but not linked: give the repository URL and commit, the command to rerun them, and the counts they produce, so a reader can rerun them. The Lean files cited by the companion paper are public; this paper cites none directly.

## 5. Ethics and rights

The paper states the rights position correctly (transcriptions not public until the heirs agree; facsimiles public; short quotations). The quotations are short. The declaration of language-model use is present and specific. No funding to declare, as stated.

## 6. Specialist review needed

Problems 1–2 (étale cohomology of fields and affine schemes), 3 (mixed Hodge theory), 6 (abelian schemes, Fourier–Mukai), 7 (Lie theory: Kostant, Springer, Vinberg), 8 (categorical logic), 13 (topology of moduli). The pseudoline proof in § 7 is elementary and can be checked by any combinatorialist.

## 7. Limits of this review

Read from the LaTeX source and the PDF only; the facsimiles were not consulted (Montpellier offline). The mathematical checks above (M1, M6, m8) are mine and unchecked by a specialist. Citation metadata and claim checks are in `citations-2026-10-26.md`.
