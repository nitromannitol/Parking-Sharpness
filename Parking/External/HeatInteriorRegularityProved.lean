import Parking.External.HeatInteriorRegularity
import LatticeProb.Analysis.HeatParking

/-!
# Interior regularity for the heat operator, proved

Interior regularity for the heat operator `(2d)⁻¹Δ` on open subsets of positive space-time,
used in Step 3 of `parking.tex:1800-1820`, proved rather than assumed.  The statement
`Parking.External.HeatInteriorRegularity` is the shared library's
`LatticeProb.WhiteNoise.heat_interior_regularity` verbatim: a continuous weak solution agrees
on the open set with a smooth classical solution.
-/

-- FROZEN-STATEMENT-BEGIN
/-- Interior regularity for the heat operator, proved rather than assumed. -/
theorem Parking.External.heatInteriorRegularity : Parking.External.HeatInteriorRegularity
-- FROZEN-STATEMENT-END
:= fun d U hU hpos u hu hweak =>
  LatticeProb.WhiteNoise.heat_interior_regularity d U hU hpos u hu hweak
