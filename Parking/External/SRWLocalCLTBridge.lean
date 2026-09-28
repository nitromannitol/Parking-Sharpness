import Parking.External.SRWLocalCLT
import Sandpile.External.LocalCLT
import Sandpile.External.LocalCLTProved
import Sandpile.External.VarianceScaleProved

/-!
# Bridging the multivariate local CLT from Divisible-Sandpile-Percolation

Bridge: Parking-Sharpness's frozen `Parking.External.SRWLocalCLT` follows from
Divisible-Sandpile-Percolation's frozen `Sandpile.External.LocalCLT`.

Both statements transcribe the same display, Bou-Rabee-Panagiotis' equation (25)
(citing Lawler-Limic, Theorem 2.1.3, Eq. (2.8)), in slightly different but
equivalent dress: Sandpile's version reads the Brownian kernel at
`Sandpile.Continuum.Space d`-points `scaledSite R x`, `scaledSite R y` and the
squared distance hypothesis as `latticeDist x y ≤ C₀ * R`; Parking's version
reads the same Brownian kernel (transcribed independently as `contHeatKernel`,
with an identical normalisation) at the raw coordinatewise quotients
`fun i => (x i : ℝ) / R` and states the distance hypothesis as the squared sum
directly.  `Parking.Site d` and `Sandpile.Site d` are both `LatticeProb.Site d`,
so no site conversion is needed; `Sandpile.heatKernel_eq_srwHeat` (from
`Sandpile.External.VarianceScaleProved`, not otherwise reached by importing
just `Sandpile.External.LocalCLT`) together with `LatticeProb.srwHeat_neg`
identifies `Sandpile.heatKernel` with `LatticeProb.srwHeat` (mind the swapped
arguments `y - x` there).

`Parking.External.srwLocalCLT_of_localCLT` is this bridge, conditional on
`Sandpile.External.LocalCLT`; `Parking.External.srwLocalCLT` below discharges
that hypothesis with `Sandpile.External.localCLT`
(`Sandpile/External/LocalCLTProved.lean`), so `Parking.External.SRWLocalCLT`
is proved rather than assumed.
-/

open LatticeProb

namespace Parking.External

/-- Bridge: the Brownian kernel at Sandpile's rescaled lattice points equals Parking's
`contHeatKernel` at the raw coordinatewise quotients. -/
theorem heatKernelBM_scaledSite_eq_contHeatKernel {d : ℕ} (R t : ℝ) (x y : Sandpile.Site d) :
    Sandpile.Continuum.heatKernelBM d t
        (Sandpile.External.Lclt.scaledSite R x) (Sandpile.External.Lclt.scaledSite R y)
      = Parking.External.contHeatKernel d t
          (fun i => (x i : ℝ) / R) (fun i => (y i : ℝ) / R) := by
  have hnorm : ‖Sandpile.External.Lclt.scaledSite R x
      - Sandpile.External.Lclt.scaledSite R y‖ ^ 2
      = ∑ i, ((x i : ℝ) / R - (y i : ℝ) / R) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
    show (((x i : ℤ) : ℝ) / R - ((y i : ℤ) : ℝ) / R) ^ 2 = ((x i : ℝ) / R - (y i : ℝ) / R) ^ 2
    norm_num
  simp only [Sandpile.Continuum.heatKernelBM, Parking.External.contHeatKernel, hnorm]

/-- Discharges `Parking.External.SRWLocalCLT` from the sibling library's
`Sandpile.External.LocalCLT`, converting the rescaled-lattice-point form of the bound into
Parking's raw-coordinate form via `heatKernelBM_scaledSite_eq_contHeatKernel` and identifying
`Sandpile.heatKernel` with `LatticeProb.srwHeat`. -/
theorem srwLocalCLT_of_localCLT (hL : Sandpile.External.LocalCLT) :
    Parking.External.SRWLocalCLT := by
  intro d hd δ T C₀ hδ hδT hC₀nonneg ε hε
  obtain ⟨R₀, hR₀pos, hR₀⟩ := hL d hd δ (T + 1) C₀ hδ (by linarith) (ε / 2) (by linarith)
  refine ⟨R₀, fun R hR ℓ hℓ1 hℓ2 x y hxy hpos => ?_⟩
  have hRpos : 0 < R := lt_of_lt_of_le hR₀pos hR
  have hℓ2' : (ℓ : ℝ) ≤ (T + 1) * R ^ 2 := hℓ2.trans (by nlinarith [sq_nonneg R])
  have hC₀R : 0 ≤ C₀ * R := mul_nonneg hC₀nonneg hRpos.le
  have hdist : Sandpile.External.Lclt.latticeDist x y ≤ C₀ * R := by
    rw [Sandpile.External.Lclt.latticeDist, Real.sqrt_le_left hC₀R]
    convert hxy using 2
    push_cast
    ring
  have hheat_eq : Sandpile.heatKernel d ℓ x y = LatticeProb.srwHeat d ℓ (x - y) := by
    rw [Sandpile.heatKernel_eq_srwHeat d ℓ x y, show y - x = -(x - y) by abel,
        LatticeProb.srwHeat_neg]
  have hpos' : 0 < Sandpile.heatKernel d ℓ x y := hheat_eq ▸ hpos
  have hbound := hR₀ R hR ℓ x y hℓ1 hℓ2' hdist hpos'
  rw [hheat_eq, heatKernelBM_scaledSite_eq_contHeatKernel R ((ℓ : ℝ) / R ^ 2) x y,
      div_eq_mul_inv] at hbound
  linarith [hbound]

end Parking.External

-- FROZEN-STATEMENT-BEGIN
/-- The local central limit theorem for the simple random walk, proved rather than assumed. -/
theorem Parking.External.srwLocalCLT : Parking.External.SRWLocalCLT
-- FROZEN-STATEMENT-END
:= Parking.External.srwLocalCLT_of_localCLT Sandpile.External.localCLT
