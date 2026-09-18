/-
Proposition 9.2 of parking.tex, frozen.  `parking.tex:2010-2017` (label
`prop:nearest-two-hole`), in the setting of `parking.tex:1835-1866`:

  "There is $C<\infty$, depending only on $d$, such that, for every $t\geq0$
   and distinct $x,z\in\Z^d$,
   $\P(H_t(x)=H_t(z)=1)
     \leq Ch_t^2\exp\{C\log(1/h_t)(1+|x-z|)^{4-d}\}$."

Distances on the lattice are graph distances (`parking.tex:588-601`), so
`|x-z|` is the `l^1` norm of `x-z`.  The martingale moment inequality the proof
quotes enters as an explicit hypothesis.
-/
import Parking.Support.Range
import Parking.External.Bernstein
import Parking.Support.ThreePointLaw
import Parking.Support.NearestTwoHoleProof

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.nearest_two_hole (hBernstein : Parking.External.Bernstein) (d : ℕ) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 →
      ∀ (t : ℕ) (x z : Parking.Site d), x ≠ z →
        ((Parking.law d (Parking.threePointLaw p))
            {ω | Parking.H ω t x = 1 ∧ Parking.H ω t z = 1}).toReal
          ≤ C * Parking.holeProb d (Parking.threePointLaw p) t ^ 2 *
              Real.exp (C * Real.log (1 / Parking.holeProb d (Parking.threePointLaw p) t)
                * (1 + (Parking.graphNorm (x - z) : ℝ)) ^ (4 - (d : ℝ)))
-- FROZEN-STATEMENT-END
:= by
  exact Parking.nearest_two_hole_proof hBernstein d hd
