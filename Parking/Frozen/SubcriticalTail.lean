/-
Theorem 1.1 of parking.tex, frozen.  `parking.tex:123-135`
(label `thm:subcritical-tail`):

  "Let $\eta$ have i.i.d. integer-valued coordinates, with $\E|\eta(0)|<\infty$,
   $\E\eta(0)<0$, $\P(\eta(0)>0)>0$, and suppose that $\E e^{\theta\eta(0)}<\infty$
   for some $\theta>0$.  Then there are $0<c\leq C<\infty$ such that, for every
   $t\geq1$,  $C^{-1}\exp\{-Ct^{d/(d+2)}\}\leq S_t\leq C\exp\{-ct^{d/(d+2)}\}$."

The proof at `parking.tex:2497-2502` converts the two bounds in `|R_t|` into the
two bounds in `t` by the Donsker-Varadhan estimate for the range, which the paper
cites; under R1 that estimate is carried as the explicit hypothesis
`Parking.External.DonskerVaradhanRange`.
-/
import Parking.Basic
import Parking.External.DonskerVaradhan
import Parking.Support.TailTwoSided

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.subcritical_tail
    (hDV : Parking.External.DonskerVaradhanRange)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν < 0)
    (hpos : 0 < ν (Set.Ioi 0))
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(C * (t : ℝ) ^ ((d : ℝ) / (d + 2)))) ≤ Parking.S (Parking.law d ν) t ∧
        Parking.S (Parking.law d ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / (d + 2))))
-- FROZEN-STATEMENT-END
:= by
  haveI := hprob
  exact Parking.exists_tail_bounds hDV hd hint hmean hpos hθ hexp
