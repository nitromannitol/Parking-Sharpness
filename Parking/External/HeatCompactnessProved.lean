import Parking.External.HeatCompactness
import LatticeProb.Analysis.HeatParking

/-!
# Compactness of classical heat solutions, proved

Local compactness of nonnegative classical solutions of the heat equation for `(2d)⁻¹Δ`, used
in Step 3 of `parking.tex:1800-1820`, proved rather than assumed.  The statement
`Parking.External.HeatCompactness` is the shared library's
`LatticeProb.WhiteNoise.heat_compactness` verbatim: a sequence of nonnegative classical
solutions with bounded integrals over the compact subsets has a subsequence converging
uniformly on compact subsets to a nonnegative classical solution.
-/

-- FROZEN-STATEMENT-BEGIN
/-- Compactness of nonnegative classical heat solutions, proved rather than assumed. -/
theorem Parking.External.heatCompactness : Parking.External.HeatCompactness
-- FROZEN-STATEMENT-END
:= fun d hd U hU f hsmooth hnonneg hheat hbound =>
  LatticeProb.WhiteNoise.heat_compactness d hd U hU f hsmooth hnonneg hheat hbound
