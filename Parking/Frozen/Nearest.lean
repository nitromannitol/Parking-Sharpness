/-
Theorem 1.5 of parking.tex, frozen.  `parking.tex:266-275` (label `thm:nearest`):

  "Let $d\leq3$, and let $\eta$ be i.i.d., integer-valued and nonconstant, with
   $\E\eta(0)=0$ and $\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$.  Then
   $\P(\text{the origin is closer to an unfilled hole than to an active particle
   at time }t)\to0$ as $t\to\infty$."

Distances are graph distances from the origin, in `ℕ∞`, as
`parking.tex:588-601` fixes them.

The proof at `parking.tex:1807-1833` runs through Proposition 8.3 and cites two
results from outside the paper: the sandpile growth and concentration estimates
that Proposition 8.3 itself invokes, and the critical-scale lower tail, which is
what makes the limit field positive at the origin at time one.  The node therefore
carries those inputs as explicit hypotheses and nothing more.

The hypothesis list of `prop:spatial-scaling` carries BP's Theorem 1.3(i)(b) directly
(`Parking.External.SpatialOdometerScaling`, which carries the joint space-time
equicontinuity clause itself and so also subsumes
`Parking.External.SpatialFixedTimeTightness`).  Since `thm:nearest` is proved THROUGH
`prop:spatial-scaling`, the same hypothesis appears here.
-/
import Parking.Support.NearestFromSpatial
import Parking.External.GreenNorms

open MeasureTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.nearest (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (hOdometer : Parking.External.SpatialOdometerScaling)
    (hInterior : Parking.External.HeatInteriorRegularity)
    (hMinimum : Parking.External.HeatStrongMinimum)
    (hCompact : Parking.External.HeatCompactness)
    (hLower : Parking.External.CriticalScaleLowerTail)
    (hVar : Parking.External.VarianceScale)
    (hBerry : Parking.External.MultivariateBerryEsseen)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) :
    Tendsto (fun t : ℕ => ((Parking.law d ν) {ω | Parking.HoleCloser ω t}).toReal)
      atTop (𝓝 0)
-- FROZEN-STATEMENT-END
:=
  Parking.nearest_of_spatial_scaling hGrowth hBernstein hConcentration hGreenNorms
    hOdometer hInterior hMinimum hCompact hLower hVar hBerry d hd hd3 ν hν
