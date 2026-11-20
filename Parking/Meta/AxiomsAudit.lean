import Parking.MainTheorems
import Parking.MainTheoremsBernsteinProved
import Parking.MainTheoremsBernsteinConsequences
import Parking.External.LinearFieldScalingProved
import Parking.External.SpatialOdometerScalingProved
import Parking.Support.RangeConfinement
import Parking.Support.RangeUpperScaling
import Parking.MainTheoremsBerryEsseenProved
import Parking.MainTheoremsOrientedConsequences
import Parking.MainTheoremsUnconditional
import Parking.External.SpatialStoppingStabilityUnconditional
import ParkingAudit.SubcriticalTailUnconditional.Solution

/-!
# Axioms audit

Building this module prints the axiom dependencies of the eight main theorems of
`Parking/MainTheorems.lean`, of `Parking.nearest'`, Theorem 1.5 with its two heat equation
hypotheses discharged, of `Parking.nearest''`, which also derives the spatial odometer
scaling limit from the continuum stopping stability of the divisible sandpile, of the
hypothesis-free forms of the main results in `Parking/MainTheoremsUnconditional.lean` with the
three cited inputs they are proved from, and of the proof of the spatial stopping stability.
Each must report exactly the three standard foundational axioms of Mathlib: `propext`,
`Classical.choice`, `Quot.sound`.

The results the paper cites without proof are not axioms here: each is a `Prop` in
`Parking/External/` taken as an explicit hypothesis of the theorems that use it, so it
appears in the statement, not in this list.

This file is not imported by the library root; the report runs when it is built explicitly
(`lake build Parking.Meta.AxiomsAudit`), as continuous integration does on every push.
-/

#print axioms Parking.External.linearFieldScaling_holds
#print axioms Parking.External.spatialOdometerScaling_of_dsp
#print axioms Parking.subcritical_tail
#print axioms Parking.master
#print axioms Parking.growth
#print axioms Parking.trichotomy
#print axioms Parking.nearest
#print axioms Parking.nearest'
#print axioms Parking.nearest''
#print axioms Parking.nearest_counterexample
#print axioms Parking.near
#print axioms Parking.oriented_walk

#print axioms Parking.master_of_bernstein
#print axioms Parking.growth_of_bernstein
#print axioms Parking.trichotomy_of_bernstein
#print axioms Parking.nearest_of_bernstein
#print axioms Parking.nearest_heat_of_bernstein
#print axioms Parking.nearest_stability_of_bernstein
#print axioms Parking.nearest_lower_bound_of_bernstein
#print axioms Parking.near_of_bernstein
#print axioms Parking.oriented_walk_of_bernstein
#print axioms Parking.range_moment_lower_bound
#print axioms Parking.exists_lower_tail_of_confinement
#print axioms Parking.exists_tail_bounds_one
#print axioms Parking.range_moment_upper_bound_of_range_count
#print axioms Parking.subcritical_tail_of_range_count
#print axioms Parking.External.multivariateBerryEsseen
#print axioms Parking.nearest_of_proved_berry
#print axioms Parking.nearest_of_continuum_stopping
#print axioms ParkingAudit.subcritical_tail_unconditional

#print axioms Parking.External.orientedStoppingStability_of_continuumStoppingStability
#print axioms Parking.oriented_scaling_of_continuum_stopping
#print axioms Parking.oriented_walk_of_continuum_stopping
#print axioms Parking.oriented_walk_of_bernstein_and_continuum_stopping

#print axioms Parking.External.sandpileGrowth_holds
#print axioms Parking.External.orientedStoppingStability_holds
#print axioms Parking.External.spatialOdometerScaling_holds
#print axioms Parking.subcritical_tail_proved
#print axioms Parking.master_proved
#print axioms Parking.growth_proved
#print axioms Parking.trichotomy_proved
#print axioms Parking.nearest_proved
#print axioms Parking.nearest_counterexample_proved
#print axioms Parking.near_proved
#print axioms Parking.oriented_scaling_proved
#print axioms Parking.oriented_walk_proved
#print axioms Parking.External.spatialStoppingStability_of_continuumStoppingStability
#print axioms Parking.External.spatialStoppingStability_holds
