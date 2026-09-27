import Parking.External.HeatStrongMinimum
import LatticeProb.Analysis.HeatStrongMinimum

/-!
# The strong minimum principle, proved

The strong minimum principle for the heat operator `(2d)⁻¹Δ`, used in Step 4 of
`parking.tex:1800-1820`, proved rather than assumed.  The statement
`Parking.External.HeatStrongMinimum` is the shared library's
`LatticeProb.WhiteNoise.heat_strong_minimum` (Nirenberg 1953, Theorem 1; Evans,
*Partial Differential Equations*, Section 2.3.3, Theorem 4) verbatim.
-/

-- FROZEN-STATEMENT-BEGIN
/-- The strong minimum principle for the heat operator, proved rather than assumed. -/
theorem Parking.External.heatStrongMinimum : Parking.External.HeatStrongMinimum
-- FROZEN-STATEMENT-END
:= fun d U hU v hv hnn heq s₀ x₀ h0U hv0 τ hτ hseg =>
  LatticeProb.WhiteNoise.heat_strong_minimum d U hU v hv hnn heq s₀ x₀ h0U hv0 τ hτ hseg
