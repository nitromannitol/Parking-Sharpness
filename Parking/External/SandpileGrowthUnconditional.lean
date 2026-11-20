import Parking.External.SandpileGrowthProved
import Sandpile.Support.MeanGrowthLowUnconditional

/-!
# The sandpile growth input without hypotheses

`Parking.External.SandpileGrowth`, the growth of the mean divisible sandpile odometer quoted at
`thm:BP`, holds with no hypothesis.  The divisible sandpile formalization proves the
low-dimensional limit of the mean odometer (its Theorem 1.3(i)(a)) as
`Sandpile.mean_growth_le_three_proved`, with its continuum stopping stability input proved and
without any optimal-stopping input, and `Parking.External.sandpileGrowth_of_mean_growth_le_three`
assembles the growth statement from that limit and the sealed growth theorems in dimensions
four and higher.
-/

/-- The growth of the mean divisible sandpile odometer (`thm:BP`), with no hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Parking.External.sandpileGrowth_holds : Parking.External.SandpileGrowth
-- FROZEN-STATEMENT-END
:=
  Parking.External.sandpileGrowth_of_mean_growth_le_three Sandpile.mean_growth_le_three_proved
