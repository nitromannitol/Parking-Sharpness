/- The conditional mean of arrivals for the directed count recursion. -/
import Parking.Support.OrientedGivenBound
import Parking.Support.OrientedInstructionIntegral
import Parking.Support.FiniteRandomCount

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb Finset
variable {d : ℕ}

theorem integral_oriented_arrivals_given (hd : 1 ≤ d) (η : Site d → ℤ)
    (n : ℕ) (y : Site d) (i : Fin d) :
    Integrable (fun σ : Site d × ℕ → Site d =>
      (arrivals σ y (y + unit i) (orientedOdometer η σ n y) : ℝ)) (orientedStackLaw d) ∧
      (∫ σ : Site d × ℕ → Site d,
        (arrivals σ y (y + unit i) (orientedOdometer η σ n y) : ℝ) ∂(orientedStackLaw d)) =
          (d : ℝ)⁻¹ * ∫ σ : Site d × ℕ → Site d, (orientedOdometer η σ n y : ℝ) ∂(orientedStackLaw d) := by
  classical
  haveI := orientedStackLaw_isProbability hd
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (orientedInstructionLaw q.1) :=
    fun q => orientedInstructionLaw_isProbability hd q.1
  have hp (j : ℕ) : (orientedStackLaw d).real {σ : Site d × ℕ → Site d | σ (y, j) = y + unit i} =
      (d : ℝ)⁻¹ := by
    change ((orientedStackLaw d) ((fun σ : Site d × ℕ → Site d => σ (y, j)) ⁻¹' {y + unit i})).toReal = _
    rw [← Measure.map_apply (measurable_pi_apply (y, j)) (measurableSet_singleton _)]
    rw [show (orientedStackLaw d).map (fun σ : Site d × ℕ → Site d => σ (y, j)) =
      orientedInstructionLaw y from Measure.infinitePi_map_eval _ (y, j)]
    exact orientedInstructionLaw_forward_mass y i
  have h := integral_random_count (orientedStackLaw d)
    (fun σ : Site d × ℕ → Site d => orientedOdometer η σ n y)
    (measurable_orientedOdometer _ _ measurable_const measurable_id n y)
    (fun j σ => σ (y, j)) (fun j => measurable_pi_apply (y, j)) (y + unit i)
    (n * ∑ z ∈ boxFinset y n, (η z).toNat) (orientedOdometer_ae_le_bound hd η n y) (d : ℝ)⁻¹
    (fun j _ => orientedOdometer_indep_stack_coord hd η n y (y, j) le_rfl) (fun j _ => hp j)
  have he : (fun σ : Site d × ℕ → Site d =>
      (arrivals σ y (y + unit i) (orientedOdometer η σ n y) : ℝ)) =
      (fun σ : Site d × ℕ → Site d =>
        (((range (orientedOdometer η σ n y)).filter fun j => σ (y, j) = y + unit i).card : ℝ)) := by
    funext σ
    unfold arrivals
    congr 1
  rw [he]
  convert h using 1 <;> congr! 5
  ext j
  simp

theorem integral_orientedArrivalCount_given (hd : 1 ≤ d) (η : Site d → ℤ) (n : ℕ) (x : Site d) :
    (∫ σ : Site d × ℕ → Site d, (orientedArrivalCount η σ n x : ℝ) ∂(orientedStackLaw d)) =
      orientedOp (fun y => ∫ σ : Site d × ℕ → Site d,
        (orientedOdometer η σ n y : ℝ) ∂(orientedStackLaw d)) x := by
  have hi (i : Fin d) := integral_oriented_arrivals_given hd η n (x - unit i) i
  simp only [sub_add_cancel] at hi
  simp only [orientedArrivalCount, Nat.cast_sum]
  rw [integral_finsetSum _ (fun i _ => (hi i).1)]
  simp only [fun i => (hi i).2, orientedOp, ← mul_sum, div_eq_inv_mul]

end Parking
