/-
External input: the concentration estimate for the solution of
`v_{n+1} = (η + K v_n)⁺` that the paper quotes (`parking.tex:1387-1400`, label
`lem:u-concentration`) from Bou-Rabee and Panagiotis, Remark 3.4 there.  The
paper states the lemma and then says that it follows from that remark, so no
proof of it is given in `parking.tex` and it enters here as a hypothesis.

Assumed here.  It enters only as an explicit hypothesis of the results whose
proofs use it.
-/
import Parking.Support.Kernel

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- "Let $K$ be a finite-range, translation-invariant transition kernel on
$\Z^d$.  Let $g_n^K(z)\coloneqq\sum_{j<n}K^j(0,z)$, and let $v_0=0$ and
$v_{n+1}=(\eta+Kv_n)^+$ for i.i.d. $\eta(x)$ satisfying
$\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$.  Then there is $C<\infty$,
depending on $K$ and the law of $\eta(0)$, such that, for every $n\geq1$ and
$r\geq2$,
$(\E|v_n(0)-\E v_n(0)|^r)^{1/r}\leq C(\sqrt r\,\|g_n^K\|_2+r\|g_n^K\|_\infty)$." -/
def Parking.External.UConcentration : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (r : ℕ) (K : Parking.Site d → Parking.Site d → ℝ),
    Parking.IsLatticeKernel r K → ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
    ∀ θ : ℝ, 0 < θ → Integrable (fun z : ℝ => Real.exp (θ * |z|)) ν →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ q : ℝ, 2 ≤ q →
      (∫ η, |Parking.kSol r K η n 0
            - ∫ η', Parking.kSol r K η' n 0 ∂(LatticeProb.iidLaw d ν)| ^ q
          ∂(LatticeProb.iidLaw d ν)) ^ (1 / q)
        ≤ C * (Real.sqrt q * Parking.l2Norm (Parking.kGreen r K n)
            + q * Parking.supAbs (Parking.kGreen r K n))
-- FROZEN-STATEMENT-END
