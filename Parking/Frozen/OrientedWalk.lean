/-
Theorem 1.8 of parking.tex, frozen.  `parking.tex:363-380` (label `thm:oriented-walk`):

  "Let $\eta$ have i.i.d. integer-valued coordinates, nonconstant, of mean zero,
   with $\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$.  Then
   $\E\vec U_n(0)\asymp n^{1/4}$ for $d=2$ and $\asymp\log n$ for $d\geq3$.
   When $d=2$, the ratio $\E\vec U_n(0)/\E\vec u_n(0)$ tends to one, and there is
   $\mu\in(0,\infty)$ with $\E\vec U_n(0)\sim\mu n^{1/4}$ and
   $\vec S_t\sim(\mu/4)t^{-3/4}$."

`f ∼ g` is written as the ratio tending to one.

The proof is Steps 1 to 5 of `parking.tex:3238-3400` together with
`prop:oriented-scaling`.  Step 1 rests on the directed Bernstein inequality and the
directed concentration estimate, and `prop:oriented-scaling` rests on the cutoff and
stability estimates of the parabolic scaling limit, all three cited from outside the
paper, so by standing ruling R1 the node carries them as explicit hypotheses and nothing
more.
-/
import Parking.Support.OrientedActivity
import Parking.Frozen.OrientedScaling

open MeasureTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.oriented_walk (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration)
    (hStability : Parking.External.OrientedStoppingStability)
    (hBinomial : Parking.External.BinomialLocalCLT)
    (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) :
    (d = 2 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ Parking.meanU (Parking.orientedLaw d ν) n ∧
        Parking.meanU (Parking.orientedLaw d ν) n ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4)) ∧
    (3 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * Real.log n ≤ Parking.meanU (Parking.orientedLaw d ν) n ∧
        Parking.meanU (Parking.orientedLaw d ν) n ≤ C * Real.log n) ∧
    (d = 2 →
      Tendsto (fun n : ℕ => Parking.meanU (Parking.orientedLaw d ν) n /
        Parking.meanuOriented (Parking.orientedLaw d ν) n) atTop (𝓝 1) ∧
      ∃ μ : ℝ, 0 < μ ∧
        Tendsto (fun n : ℕ => Parking.meanU (Parking.orientedLaw d ν) n /
          (μ * (n : ℝ) ^ ((1 : ℝ) / 4))) atTop (𝓝 1) ∧
        Tendsto (fun t : ℕ => Parking.S (Parking.orientedLaw d ν) t /
          (μ / 4 * (t : ℝ) ^ (-(3 : ℝ) / 4))) atTop (𝓝 1))
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨Ω, _, Q, _, Uc, μ, _hmeas, _hweak, _hself, _hint, _hμeq, hμpos, hlim⟩ :=
    Parking.Frozen.oriented_scaling hStability hBinomial ν hν
  have hμlim : Tendsto (fun n : ℕ => Parking.meanuOriented (Parking.orientedLaw 2 ν) n /
      ((n : ℝ) ^ ((1 : ℝ) / 4))) atTop (𝓝 μ) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [show (-(1:ℝ)/4) = -((1:ℝ)/4) by ring, Real.rpow_neg hn0.le]
    ring
  exact Parking.oriented_walk_of_mean hBern hConc d hd ν hν μ hμpos hμlim
