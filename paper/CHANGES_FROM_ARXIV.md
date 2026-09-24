# Differences from the arXiv version

The formalization follows `paper/parking.tex`, which is arXiv:2609.02820v1 with the
corrections below.  The arXiv source will be replaced by the corrected version.  The
unmodified arXiv source is `paper/parking-arxiv.tex`; its figures and bibliography file are in
`paper/arxiv/`.  Line numbers refer to the corrected file.  No statement changes its
hypotheses or its conclusion; the changes name the construction two lemmas are stated for and
add the steps that three proofs use.

## 1. Section 2, paragraph after the description of a round (line 645)

arXiv:

> The stack construction has the same law as the construction in which each particle is
> assigned its own independent walk and independent uniform variables. An instruction is never
> read until a particle is about to use it, so ...

Corrected:

> ... independent uniform variables. Distinct departures read distinct instructions, and an
> instruction is never read until a particle is about to use it, so ...

The equality of the two laws needs both facts: every departure reads an instruction no earlier
departure has read, and which instruction it reads is determined by what has already happened.
Together they make the instructions the particles read independent steps of simple random
walk.  The arXiv text gave only the second fact.

## 2. Lemma 2.3, `lem:one-particle` (lines 682-692)

arXiv:

> ... where $\widetilde\eta$ exceeds $\eta$ by one, and couple the two processes by giving
> every particle they share the same walk and the same uniform variables.

Corrected:

> ... where $\widetilde\eta$ exceeds $\eta$ by one, build both processes from the construction
> in which each particle is assigned its own walk and uniform variables, and couple them by
> giving every particle they share the same walk and the same uniform variables.

The coupling gives each particle its own walk, which the stack construction of Section 2 does
not do: adding a particle at a site changes which instruction every later departure from that
site reads.  The statement now names the construction it is made in.  Lemma 2.4
(`lem:tagged-monotonicity`) is stated in the coupling of Lemma 2.3 and so is made in the same
construction.

## 3. Proof of Lemma 2.5, `lem:transport` (lines 760-767)

arXiv:

> Summing $\E A_s(0)=S_s$ over $s<n$ gives $\E U_n(0)=\sum_{s<n}S_s$, and conditioning the
> definition of $S_t$ on $\eta(0)$ gives \eqref{eq:S-expand}.

Corrected:

> Summing $\E A_s(0)=S_s$ over $s<n$ gives $\E U_n(0)=\sum_{s<n}S_s$. In the construction in
> which each particle is assigned its own walk and uniform variables, permuting the labels of
> the $k$ particles at the origin permutes independent walks and uniform variables. This
> permutation commutes with the evolution unless two uniform variables coincide, which has
> probability zero. That construction has the same law as the stack construction, so the $k$
> particles at the origin are exchangeable conditionally on $\eta(0)=k$, and conditioning the
> definition of $S_t$ on $\eta(0)$ gives \eqref{eq:S-expand}.

The lemma asserts that the particles at the origin are exchangeable, and the arXiv proof did
not prove it.  In the stack construction the particles at the origin read different
instructions, so relabelling them is not a symmetry of each realization.  The exchangeability
is a symmetry of the other construction, and it passes to the stack construction through the
equality of the two laws.

## 4. Proof of Lemma 2.7, `lem:density-compare` (lines 823-834)

arXiv:

> Lemma~\ref{lem:one-particle}, applied successively, gives $A_t\leq\widetilde A_t$ and
> $H_t\geq\widetilde H_t$ for finitely many added particles. ...
>
> Taking expectations at the origin gives $S_t\leq\widetilde S_t$ by
> Lemma~\ref{lem:transport}.

Corrected:

> In the construction in which each particle is assigned its own walk and uniform variables,
> Lemma~\ref{lem:one-particle}, applied successively, gives $A_t\leq\widetilde A_t$ and
> $H_t\geq\widetilde H_t$ for finitely many added particles. ...
>
> That construction has the same law as the stack construction, so taking expectations at the
> origin gives $S_t\leq\widetilde S_t$ by Lemma~\ref{lem:transport}.

Lemma 2.3 compares the two processes in the construction in which each particle has its own
walk, while $S_t$ is defined through the stack construction, where $A_t$ is not a monotone
function of $\eta$.  The proof now makes the comparison in the first construction and
transfers the expectations through the equality of the two laws.

## 5. After Lemma 4.5, `lem:bernstein` (lines 1190-1193)

arXiv: the lemma cites Theorems 4.1 and 3.3 of Pinelis for both bounds, with no further text.

Corrected: the sentence

> The second bound follows from the tail bound
> $\P(|\sum_{i=1}^k\xi_i|\geq s)\leq2\exp(-s^2/(2(v+as/3)))$ for $s>0$ of
> \citet[Theorem~3.3]{Pinelis} by integrating it against $rs^{r-1}\,ds$, split at $s=3v/a$.

is added after the lemma.  Theorem 3.3 of Pinelis is a tail bound, not the moment bound of the
lemma's second part.  The moment bound follows from
$\E|S|^r=r\int_0^\infty s^{r-1}\P(|S|\geq s)\,ds$, and splitting the integral at $s=3v/a$
gives the two terms $\sqrt{rv}$ and $ra$ with a universal constant.
