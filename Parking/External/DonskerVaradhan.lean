/-
External input: the Donsker-Varadhan estimate for the number of distinct sites
visited by a random walk, which the paper quotes at `parking.tex:117-121` and
uses in the proof of `thm:subcritical-tail` at `parking.tex:2499-2502`.

M. D. Donsker and S. R. S. Varadhan, *On the number of distinct sites visited by
a random walk*, Comm. Pure Appl. Math. 32 (1979), 721-747, Theorem 1: for every
`a > 0` the logarithm of `E exp(-a|R_t|)` is asymptotic to `-k t^{d/(d+2)}` for a
constant `k > 0` depending on `a` and the dimension.

Assumed here.  It enters only as an explicit hypothesis of the results whose
proofs use it.  The expectation is an integral of a strictly positive function
against a probability measure, so it is positive and its logarithm is not the
junk value `Real.log 0 = 0`; the constant `k` is positive, so an integral read
as zero would make the assertion false rather than vacuous.
-/
import Parking.Support.Range

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- "By the Donsker--Varadhan estimate for the range, the logarithm of the
expectation on the right is asymptotic to $-kt^{d/(d+2)}$ for some $k>0$."
Here the expectation is $\E_0e^{-a|R_t|}$, the average over the walk from the
origin alone of `Real.exp (-(a * |R_t|))`. -/
def Parking.External.DonskerVaradhanRange : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ a : ℝ, 0 < a →
    ∃ k : ℝ, 0 < k ∧
      Filter.Tendsto
        (fun t : ℕ =>
          Real.log (∫ p, Real.exp (-(a * (Parking.rangeCard (0 : Parking.Site d) p t : ℝ)))
              ∂(Parking.walkLaw d)) / (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))
        Filter.atTop (nhds (-k))
-- FROZEN-STATEMENT-END
