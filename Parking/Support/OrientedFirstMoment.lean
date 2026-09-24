/- Integrability of the directed divisible process from a first scenery moment. -/
import Parking.Support.OrientedFinite
import Parking.Support.LinearFirstMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem orientedPotential_nonneg {η : Site d → ℝ} (hη : ∀ x, 0 ≤ η x) (n : ℕ) (x : Site d) :
    0 ≤ orientedPotential η n x := by
  rw [orientedPotential_eq_box]
  exact sum_nonneg fun z _ => mul_nonneg (orientedGreen_nonneg n (z - x)) (hη z)

theorem uOriented_le_abs_potential (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    uOriented η n x ≤ orientedPotential (fun z => |η z|) n x := by
  induction n generalizing x with
  | zero => simp [uOriented, orientedPotential_zero]
  | succ n ih =>
    change max 0 (η x + orientedOp (uOriented η n) x) ≤ _
    apply max_le
    · exact orientedPotential_nonneg (fun z => abs_nonneg (η z)) _ _
    · rw [orientedPotential_succ]
      exact add_le_add (le_abs_self _) (orientedOp_mono ih x)

theorem integrable_orientedPotential_iid (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (n : ℕ) (x : Site d) :
    Integrable (fun η : Site d → ℝ => orientedPotential η n x) (iidLaw d μ) := by
  simp only [orientedPotential_eq_box]
  exact integrable_linear_sum_infinitePi μ hi _ _

theorem integral_orientedPotential_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (hm : ∫ z : ℝ, z ∂μ = 0) (n : ℕ) (x : Site d) :
    (∫ η : Site d → ℝ, orientedPotential η n x ∂(iidLaw d μ)) = 0 := by
  simp only [orientedPotential_eq_box]
  exact integral_linear_sum_infinitePi μ hi hm _ _

theorem integrable_orientedPotential_abs (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (n : ℕ) (x : Site d) :
    Integrable (fun η : Site d → ℝ => orientedPotential (fun z => |η z|) n x) (iidLaw d μ) := by
  simp only [orientedPotential_eq_box]
  apply integrable_finsetSum
  intro z _
  have hz := integrable_comp_mp (measurePreserving_eval_infinitePi (fun _ : Site d => μ) z)
    (id : ℝ → ℝ) measurable_id.aestronglyMeasurable hi
  exact hz.abs.const_mul _

theorem integrable_uOriented_iid (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (n : ℕ) (x : Site d) :
    Integrable (fun η : Site d → ℝ => uOriented η n x) (iidLaw d μ) := by
  refine (integrable_orientedPotential_abs μ hi n x).mono'
    (measurable_uOriented n x).aestronglyMeasurable (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (uOriented_nonneg η n x)]
  exact uOriented_le_abs_potential η n x

end Parking
