import Parking.Unconditional.SubcriticalTail
import Parking.Unconditional.Master
import Parking.Unconditional.Growth
import Parking.Unconditional.Trichotomy
import Parking.Unconditional.Nearest
import Parking.Unconditional.NearestCounterexample
import Parking.Unconditional.Near
import Parking.Unconditional.OrientedScaling
import Parking.Unconditional.OrientedWalk

/-!
# Main results without hypotheses

Every main result of the paper holds with no cited hypothesis.  Each declaration below is the
certified statement of `Parking/Frozen/` with its cited-input binders removed and nothing else
changed:

* `Parking.subcritical_tail_proved`: Theorem 1.1;
* `Parking.master_proved`: Theorem 1.2;
* `Parking.growth_proved`: Corollary 1.3;
* `Parking.trichotomy_proved`: Theorem 1.4;
* `Parking.nearest_proved`: Theorem 1.5;
* `Parking.nearest_counterexample_proved`: Theorem 1.6;
* `Parking.near_proved`: Theorem 1.7;
* `Parking.oriented_walk_proved`: Theorem 1.8;
* `Parking.oriented_scaling_proved`: the oriented scaling limit `prop:oriented-scaling`.

The cited inputs are supplied by `Parking.External.sandpileGrowth_holds`,
`Parking.External.bernstein`, `Parking.External.spatialOdometerScaling_holds`,
`Parking.External.heatInteriorRegularity`, `Parking.External.heatCompactness`,
`Parking.External.multivariateBerryEsseen`, `Parking.External.orientedStoppingStability_holds`
and `Parking.External.stopping`; Theorem 1.1 uses the range bounds of
`Parking.subcritical_tail_of_range_count` in place of the Donsker–Varadhan limit.
-/
