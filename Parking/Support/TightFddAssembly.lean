/-
The finite-dimensional convergence in law (`hfdd`) of the rescaled box reward field to the
continuum noise field, at finitely many box points (`parking.tex:3192-3203`, Stage 2 of the
covariance-to-Gaussian step).

Assembles `Parking.tendsto_charFun_orientedBoxReward_linearCombination` (the discrete scalar
characteristic-function limit), `Parking.charFun_map_contZ_linearCombination` (the matching
continuum scalar characteristic-function value), and
`Parking.tendstoInDistribution_of_tendsto_charFun_linearCombination` (Cramer-Wold) into the
finite-dimensional convergence in law that `LatticeProb.tendsto_integral_of_fdd_of_equicontinuous`
consumes as its `hfdd` hypothesis.
-/
import Parking.Support.TightContFdd
import Parking.Support.TightCramerWold

open MeasureTheory LatticeProb Filter Topology

noncomputable section
namespace Parking

/-- **Finite-dimensional convergence in law of the rescaled box reward field to the continuum
noise field**, at any finite tuple of box points. This is exactly the `hfdd` hypothesis of
`LatticeProb.tendsto_integral_of_fdd_of_equicontinuous`, with `f := orientedBoxReward` and
`g := contZ (Var η(0))`. -/
theorem tendstoInDistribution_orientedBoxReward (ν : Measure ℤ) (hν : CriticalLaw ν)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure (realLaw ν)]
    [IsProbabilityMeasure (iidLaw 2 (realLaw ν))]
    (hBinomial : External.BinomialLocalCLT) (T : ℝ) {m : ℕ} (u : Fin m → Fin 2 → ℝ)
    (hu0 : ∀ l, 0 ≤ u l 0) (huT : ∀ l, u l 0 ≤ T) :
    TendstoInDistribution (fun n ω k => orientedBoxReward T n ω (u k)) atTop
      (fun ω k => contZ (∫ x : ℝ, x ^ 2 ∂(realLaw ν)) T (u k 0) (u k 1) ω)
      (fun _ : ℕ => iidLaw 2 (realLaw ν)) contNoiseLaw := by
  set σ2 : ℝ := ∫ x : ℝ, x ^ 2 ∂(realLaw ν) with hσ2def
  have hσ2 : 0 ≤ σ2 := (realLaw_sq_integral_pos ν hν).le
  have hXm : ∀ n : ℕ, Measurable (fun ω : Site 2 → ℝ => fun k => orientedBoxReward T n ω (u k)) :=
    fun n => measurable_pi_lambda _ fun k => measurable_orientedBoxReward T n (u k)
  have hZm : Measurable (fun ω : contNoiseSpace => fun k => contZ σ2 T (u k 0) (u k 1) ω) :=
    measurable_pi_lambda _ fun k => measurable_contZ σ2 T (u k 0) (u k 1)
  refine tendstoInDistribution_of_tendsto_charFun_linearCombination hXm hZm fun t => ?_
  rw [charFun_map_contZ_linearCombination T u t hσ2]
  exact tendsto_charFun_orientedBoxReward_linearCombination ν hν hBinomial T u hu0 huT t

end Parking
end
