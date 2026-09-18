/- Measurability and unread-layer invariance of the directed count recursion. -/
import Parking.Support.OrientedOdometer

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_arrivals_variable (σ : Ω → Site d × ℕ → Site d) (hσ : Measurable σ)
    (v : Ω → ℕ) (hv : Measurable v) (y x : Site d) :
    Measurable fun ω => arrivals (σ ω) y x (v ω) := by
  classical
  refine measurable_of_countable_partition v hv _ (fun m ω => arrivals (σ ω) y x m)
    (fun m => ?_) (fun _ => rfl)
  simp only [arrivals, card_filter]
  apply Finset.measurable_sum
  intro j _
  exact (measurable_from_countable' fun z : Site d => if z = x then (1 : ℕ) else 0).comp
    ((measurable_pi_apply (y, j)).comp hσ)

theorem measurable_orientedOdometer (η : Ω → Site d → ℤ) (σ : Ω → Site d × ℕ → Site d)
    (hη : Measurable η) (hσ : Measurable σ) (n : ℕ) (x : Site d) :
    Measurable fun ω => orientedOdometer (η ω) (σ ω) n x := by
  induction n generalizing x with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [orientedOdometer]
    apply (measurable_from_countable' Int.toNat).comp
    apply ((measurable_pi_apply x).comp hη).add
    apply Finset.measurable_sum
    intro i _
    exact (measurable_from_countable' fun m : ℕ => (m : ℤ)).comp
      (measurable_arrivals_variable σ hσ _ (ih (x - unit i)) (x - unit i) x)

theorem orientedOdometer_update_stack (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (n : ℕ) (x : Site d) (q : Site d × ℕ) (c : Site d)
    (hq : layerHeight x ≤ layerHeight q.1) :
    orientedOdometer η (Function.update σ q c) n x = orientedOdometer η σ n x := by
  apply orientedOdometer_lower_layers n x (fun _ _ => rfl)
  intro p hp
  have hpq : p ≠ q := by rintro rfl; omega
  exact Function.update_of_ne hpq c σ

theorem orientedOdometer_update_conf (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (n : ℕ) (x y : Site d) (c : ℤ) (hy : layerHeight x < layerHeight y) :
    orientedOdometer (Function.update η y c) σ n x = orientedOdometer η σ n x := by
  apply orientedOdometer_lower_layers n x _ (fun _ _ => rfl)
  intro z hz
  have hzy : z ≠ y := by rintro rfl; omega
  exact Function.update_of_ne hzy c η

end Parking
