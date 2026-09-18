/-
Lemma 5.2 of parking.tex, frozen.  `parking.tex:1047-1052` (label
`lem:gamma-sum`):

  "For every $n\geq1$, $\sum_y\sup_{m\leq n}\Gamma_m(y)\leq C\kappa_d(n)$."

The constant depends only on the dimension, so it is bound before `n`.
Summability is asserted alongside the bound, so that a divergent sum cannot
satisfy the statement through the junk value of a nonsummable `tsum`.  The
supremum is over the nonempty finite set `{m : m ≤ n}`.

Version 2 carries the gradient bound `eq:green-gradient` in dimension two and
above as an explicit hypothesis.  The paper proves that bound by citing the
first-difference local central limit estimate and the Gaussian bound of
Lawler-Limic, Section 2.3, so it is an external input here; in dimension one
the gradient is computed exactly inside the proof and nothing is assumed.
-/
import Parking.Support.Walk
import Parking.Support.GammaSum
import Parking.External.GreenGradient

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.gamma_sum (d : ℕ) (hd : 1 ≤ d)
    (hgrad : 2 ≤ d → Parking.External.GreenGradient d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Summable (fun y : Parking.Site d => ⨆ m ∈ Set.Iic n, Parking.gamma d m y) ∧
        ∑' y : Parking.Site d, (⨆ m ∈ Set.Iic n, Parking.gamma d m y)
          ≤ C * Parking.kappa d n
-- FROZEN-STATEMENT-END
:= Parking.gamma_sum_of_gradient d hd hgrad
