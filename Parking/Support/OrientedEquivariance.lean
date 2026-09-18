/- Translation equivariance of the directed odometer and error field, and the
translation invariance of the moments of the directed error. -/
import Parking.Support.OrientedOdometer
import Parking.Support.OrientedError
import Parking.Support.OrientedMeasurability
import Parking.Support.Equivariance
import Parking.Support.ActivityHoles
import Parking.Support.OrientedInvariance
import Parking.Support.OrientedParticleMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

/-- The arrival count of a translated stack. -/
theorem arrivals_shiftStack (v : Site d) (σ : Site d × ℕ → Site d) (y x : Site d) (m : ℕ) :
    arrivals (shiftStack v σ) y x m = arrivals σ (y + v) (x + v) m := by
  unfold arrivals shiftStack
  congr 1
  refine Finset.filter_congr fun j _ => ?_
  show (σ (y + v, j) - v = x) ↔ (σ (y + v, j) = x + v)
  exact sub_eq_iff_eq_add

/-- The directed odometer is translation equivariant. -/
theorem orientedOdometer_shiftData (v : Site d) (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (k : ℕ) (x : Site d) :
    orientedOdometer (shiftConf v η) (shiftStack v σ) k x = orientedOdometer η σ k (x + v) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [orientedOdometer]
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [arrivals_shiftStack]
    rw [ih]
    rw [show x - unit i + v = x + v - unit i from by abel]

/-- The directed error field is translation equivariant. -/
theorem wErrOriented_shiftData (v : Site d) (ω : Data d) (k : ℕ) (x : Site d) :
    wErrOriented (shiftConf v ω.1) (shiftStack v ω.2.1) k x
      = wErrOriented ω.1 ω.2.1 k (x + v) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [wErrOriented]
    congr 1
    · simp only [orientedOp]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ih]
      rw [show x - unit i + v = x + v - unit i from by abel]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [arrivals_shiftStack]
      rw [orientedOdometer_shiftData]
      rw [show x - unit i + v = x + v - unit i from by abel]

/-- The `r`-th moment of the directed error at a site is translation invariant. -/
theorem integral_abs_wErrOriented_rpow_shift (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {r : ℝ} (_hr : 0 ≤ r) (m : ℕ) (z : Site d) :
    ∫ ω : Data d, |wErrOriented ω.1 ω.2.1 m z| ^ r ∂(orientedLaw d ν)
      = ∫ ω : Data d, |wErrOriented ω.1 ω.2.1 m 0| ^ r ∂(orientedLaw d ν) := by
  have hm : Measurable (fun ω : Data d => |wErrOriented ω.1 ω.2.1 m z| ^ r) :=
    (measurable_abs.comp (measurable_wErrOriented m z)).pow_const r
  have h := integral_map (μ := orientedLaw d ν) (φ := shiftData (-z))
    (f := fun ω : Data d => |wErrOriented ω.1 ω.2.1 m z| ^ r)
    (measurable_shiftData _).aemeasurable hm.aestronglyMeasurable
  rw [orientedLaw_map_shiftData hd ν (-z)] at h
  have hpt : ∀ ω : Data d,
      |wErrOriented (shiftConf (-z) ω.1) (shiftStack (-z) ω.2.1) m z| ^ r
        = |wErrOriented ω.1 ω.2.1 m 0| ^ r := by
    intro ω
    rw [wErrOriented_shiftData, add_neg_cancel]
  simp only [shiftData, hpt] at h
  exact h

end Parking
end
