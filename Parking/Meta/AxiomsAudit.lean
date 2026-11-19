import Parking.MainTheorems
import Parking.MainTheoremsBernsteinProved
import Parking.MainTheoremsBernsteinConsequences
import Parking.External.LinearFieldScalingProved
import Parking.External.SpatialOdometerScalingProved

/-!
# Axioms audit

Building this module prints the axiom dependencies of the eight main theorems of
`Parking/MainTheorems.lean`, of `Parking.nearest'`, Theorem 1.5 with its two heat equation
hypotheses discharged, and of `Parking.nearest''`, which also derives the spatial odometer
scaling limit from the continuum stopping stability of the divisible sandpile.  Each must
report exactly the three standard foundational axioms of Mathlib: `propext`,
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
