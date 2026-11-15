import Parking.Support.CriticalLawReal
import Parking.Support.SandpileBridge
import Parking.Support.Continuum
import Sandpile.Support.MeanAInterp

/-!
# Parking and sandpile laws and rescaled odometers

The critical scenery law and the pathwise odometer agree with the corresponding
sandpile objects after the affine change from scenery to mass.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Parking

/-- The real image of a critical law satisfies the sandpile moment assumptions. -/
theorem criticalLaw_moments (ν : Measure ℤ) (hν : CriticalLaw ν) :
    IsProbabilityMeasure (ν.map (fun k : ℤ => (k : ℝ))) ∧
    ∫ z, z ∂(ν.map (fun k : ℤ => (k : ℝ))) = 0 ∧
    0 < evariance id (ν.map (fun k : ℤ => (k : ℝ))) ∧
    evariance id (ν.map (fun k : ℤ => (k : ℝ))) < ⊤ ∧
    (∃ θ₀ : ℝ, 0 < θ₀ ∧
      Integrable (fun z => Real.exp (θ₀ * |z|)) (ν.map (fun k : ℤ => (k : ℝ)))) ∧
    variance id (ν.map (fun k : ℤ => (k : ℝ))) = variance (fun k : ℤ => (k : ℝ)) ν := by
  have := hν.prob
  exact ⟨realLaw_isProbability ν, realLaw_mean ν hν, realLaw_evariance_pos ν hν,
    realLaw_evariance_lt_top ν hν, realLaw_expMoment ν hν,
    variance_id_map measurable_intCastReal.aemeasurable⟩

/-- The mass field induced by the parking law has the centered sandpile law. -/
theorem law_map_mass (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    (law d ν).map (fun w : Data d => fun y => 1 + 2 * (d : ℝ) * (w.1 y : ℝ)) =
      Sandpile.centeredMassLaw d (ν.map (fun k : ℤ => (k : ℝ))) := by
  let F : (Site d → ℝ) → Site d → ℝ := fun η y => 1 + 2 * (d : ℝ) * η y
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro y
    exact measurable_const.add (measurable_const.mul (measurable_pi_apply y))
  change (law d ν).map (F ∘ confReal) = _
  rw [← Measure.map_map hF measurable_confReal, law_map_confReal hd ν]
  unfold Sandpile.centeredMassLaw Sandpile.massLaw LatticeProb.iidLaw
  exact Measure.infinitePi_map_pi _ (fun _ => measurable_const.add (measurable_const.mul measurable_id))

/-- The odometer agrees pathwise after the affine change from scenery to mass. -/
theorem uOf_eq_sandpile_odometer (d : ℕ) (hd : 1 ≤ d) (w : Data d)
    (n : ℕ) (x : Site d) :
    uOf w n x = Sandpile.odometer (fun y => 1 + 2 * (d : ℝ) * (w.1 y : ℝ)) n x := by
  rw [Sandpile.odometer_eq_odometerOf]
  have hd0 : (2 * (d : ℝ)) ≠ 0 := by positivity
  have hs : Sandpile.scenery d (fun y => 1 + 2 * (d : ℝ) * (w.1 y : ℝ)) =
      fun y => (w.1 y : ℝ) := by
    funext y
    simp only [Sandpile.scenery]
    field_simp
    ring
  rw [hs]
  exact congrFun (u_eq_sandpile_odometerOf _ _) x

/-- The lattice-sampled parking field is the interpolated sandpile field at the mesh point. -/
theorem barDivisible_eq_sandpile_interp (d : ℕ) (hd : 1 ≤ d) (w : Data d)
    (R T : ℝ) (hR : 0 < R) (x : Fin d → ℝ) :
    barDivisible w R T x =
      Sandpile.Continuum.multilinearInterp R
        (fun y => R ^ (-(2 - (d : ℝ) / 2)) *
          Sandpile.odometer (fun z => 1 + 2 * (d : ℝ) * (w.1 z : ℝ)) ⌊T * R ^ 2⌋₊ y)
        (WithLp.toLp 2 (fun i => (⌊R * x i⌋ : ℝ) / R) : Sandpile.Continuum.Space d) := by
  rw [show (WithLp.toLp 2 (fun i => (⌊R * x i⌋ : ℝ) / R) : Sandpile.Continuum.Space d) =
      Sandpile.Support.meshPoint R (WithLp.toLp 2 x) by rfl,
    Sandpile.Support.multilinearInterp_meshPoint R (ne_of_gt hR)]
  unfold barDivisible latticePoint
  rw [uOf_eq_sandpile_odometer d hd]
  congr 1
  congr 1
  ring

end Parking
