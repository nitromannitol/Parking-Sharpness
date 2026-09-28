import Parking.Support.OrientedFinite
import Parking.Support.LinearFirstMoment

/-!
# Integrability from a first scenery moment

Integrability of the directed divisible process from a first scenery moment.
-/

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

/-- The linear potential `orientedPotential η n x` is nonnegative whenever `η` is
nonnegative everywhere, since the finite-box formula is a sum of nonnegative kernel
weights times nonnegative values. -/
theorem orientedPotential_nonneg {η : Site d → ℝ} (hη : ∀ x, 0 ≤ η x) (n : ℕ) (x : Site d) :
    0 ≤ orientedPotential η n x := by
  rw [orientedPotential_eq_box]
  exact sum_nonneg fun z _ => mul_nonneg (orientedGreen_nonneg n (z - x)) (hη z)

/-- The divisible odometer `uOriented η n x` is bounded above by the linear potential of
`|η|`, proved by induction using the max/average recursion defining `uOriented`. -/
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

/-- For an i.i.d. law `μ` with a finite first absolute moment, `η ↦ orientedPotential η n
x` is integrable, since `orientedPotential_eq_box` writes it as a finite linear
combination of coordinate evaluations (`integrable_linear_sum_infinitePi`). -/
theorem integrable_orientedPotential_iid (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (n : ℕ) (x : Site d) :
    Integrable (fun η : Site d → ℝ => orientedPotential η n x) (iidLaw d μ) := by
  simp only [orientedPotential_eq_box]
  exact integrable_linear_sum_infinitePi μ hi _ _

/-- If in addition `μ` is centered, the mean of `orientedPotential η n x` over `iidLaw d
μ` is zero, again via the finite linear-combination formula
(`integral_linear_sum_infinitePi`). -/
theorem integral_orientedPotential_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (hm : ∫ z : ℝ, z ∂μ = 0) (n : ℕ) (x : Site d) :
    (∫ η : Site d → ℝ, orientedPotential η n x ∂(iidLaw d μ)) = 0 := by
  simp only [orientedPotential_eq_box]
  exact integral_linear_sum_infinitePi μ hi hm _ _

/-- The potential of the absolute scenery, `η ↦ orientedPotential (fun z => |η z|) n x`,
is likewise integrable, since each term `|η z|` pulls back the first absolute moment of
`μ` under the measure-preserving coordinate evaluation. -/
theorem integrable_orientedPotential_abs (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (n : ℕ) (x : Site d) :
    Integrable (fun η : Site d → ℝ => orientedPotential (fun z => |η z|) n x) (iidLaw d μ) := by
  simp only [orientedPotential_eq_box]
  apply integrable_finsetSum
  intro z _
  have hz := integrable_comp_mp (measurePreserving_eval_infinitePi (fun _ : Site d => μ) z)
    (id : ℝ → ℝ) measurable_id.aestronglyMeasurable hi
  exact hz.abs.const_mul _

/-- `uOriented η n x` is integrable against `iidLaw d μ` for a first-absolute-moment
`μ`, dominated by the integrable potential of `|η|` via `uOriented_le_abs_potential`
and `integrable_orientedPotential_abs`. -/
theorem integrable_uOriented_iid (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (n : ℕ) (x : Site d) :
    Integrable (fun η : Site d → ℝ => uOriented η n x) (iidLaw d μ) := by
  refine (integrable_orientedPotential_abs μ hi n x).mono'
    (measurable_uOriented n x).aestronglyMeasurable (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (uOriented_nonneg η n x)]
  exact uOriented_le_abs_potential η n x

end Parking
