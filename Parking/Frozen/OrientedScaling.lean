/-
Proposition 12.3 of parking.tex, frozen.  `parking.tex:3151-3159` (label
`prop:oriented-scaling`):

  "Let $d=2$, and let $\eta=(\eta(x))_{x\in\Z^2}$ have i.i.d. coordinates.
   Suppose that $\eta(0)$ is nonconstant, $\E\eta(0)=0$, and
   $\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$.  Let
   $\vec P(x,x-e_i)=1/2$ for $i=1,2$, and let $\vec u_0=0$ and
   $\vec u_{n+1}=(\eta+\vec P\vec u_n)^+$.  Then, for every $T>0$,
   $n^{-1/4}\vec u_{\lfloor nT\rfloor}(0)$ converges in distribution to a
   random variable $\mathcal U(T)$ defined in the proof.  Moreover,
   $\mathcal U(T)\stackrel d=T^{1/4}\mathcal U(1)$,
   $\mu\coloneqq\E\mathcal U(1)\in(0,\infty)$, and
   $\lim_{n\to\infty}n^{-1/4}\E\vec u_n(0)=\mu$."

The limit is defined in the paper's proof and not in its statement, so it is
asserted to exist rather than characterized; it is asserted measurable, so that
its law and its mean are those of a genuine random variable.  Convergence in distribution is
stated through bounded continuous test functions, and `μ ∈ (0,∞)` is the
integrability of `U(1)` together with the positivity of its mean.

Step 1 of the paper's proof (`parking.tex:3192-3203`) rests on two results cited from outside
the paper, the cutoff and stability estimates of the parabolic scaling limit and the binomial
local central limit theorem that converges the convolved potentials, so by standing ruling R1
the node carries `Parking.External.OrientedStoppingStability` and
`Parking.External.BinomialLocalCLT` as explicit hypotheses and nothing more.  Step 2 is the paper's own and uses only results of the
repository.
-/
import Parking.Support.Continuum
import Parking.External.OrientedStoppingStability
import Parking.External.BinomialLocalCLT
import Parking.Support.TightHappFinal

open MeasureTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.oriented_scaling
    (hStability : Parking.External.OrientedStoppingStability)
    (hBinomial : Parking.External.BinomialLocalCLT)
    (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (Uc : ℝ → Ω → ℝ) (μ : ℝ),
      (∀ T : ℝ, 0 < T → Measurable (Uc T)) ∧
      (∀ T : ℝ, 0 < T → ∀ F : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ w, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
              Parking.uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * T⌋₊ 0)
            ∂(Parking.orientedLaw 2 ν)) atTop (𝓝 (∫ ω, F (Uc T ω) ∂Q))) ∧
      (∀ T : ℝ, 0 < T → Q.map (Uc T) = Q.map fun ω => T ^ ((1 : ℝ) / 4) * Uc 1 ω) ∧
      Integrable (Uc 1) Q ∧ μ = ∫ ω, Uc 1 ω ∂Q ∧ 0 < μ ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 4) *
        Parking.meanuOriented (Parking.orientedLaw 2 ν) n) atTop (𝓝 μ)
-- FROZEN-STATEMENT-END
:= Parking.oriented_scaling_assembled hStability hBinomial ν hν
