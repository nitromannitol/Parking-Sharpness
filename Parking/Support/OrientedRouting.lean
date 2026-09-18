/- The directed routing error and its deterministic Bellman comparison. -/
import Parking.Support.OrientedFreshness
import Parking.Support.OrientedMaximum

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

def orientedNoise (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (n : ℕ) (x : Site d) : ℝ :=
  (orientedArrivalCount η σ n x : ℝ) - orientedOp (fun y => (orientedOdometer η σ n y : ℝ)) x

def orientedError (η : Site d → ℤ) (σ : Site d × ℕ → Site d) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => orientedOp (orientedError η σ n) x + orientedNoise η σ n x

theorem measurable_orientedOp_apply {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω → Site d → ℝ) (hF : ∀ y, Measurable (fun ω => F ω y)) (x : Site d) :
    Measurable fun ω => orientedOp (F ω) x :=
  (Finset.measurable_sum _ fun i _ => hF (x - unit i)).div_const (d : ℝ)

theorem measurable_orientedNoise {Ω : Type*} [MeasurableSpace Ω]
    (η : Ω → Site d → ℤ) (σ : Ω → Site d × ℕ → Site d)
    (hη : Measurable η) (hσ : Measurable σ) (n : ℕ) (x : Site d) :
    Measurable fun ω => orientedNoise (η ω) (σ ω) n x := by
  exact ((measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
    (measurable_orientedArrivalCount η σ hη hσ n x)).sub
    (measurable_orientedOp_apply _ (fun y =>
      (measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
        (measurable_orientedOdometer η σ hη hσ n y)) x)

theorem measurable_orientedError {Ω : Type*} [MeasurableSpace Ω]
    (η : Ω → Site d → ℤ) (σ : Ω → Site d × ℕ → Site d)
    (hη : Measurable η) (hσ : Measurable σ) (n : ℕ) (x : Site d) :
    Measurable fun ω => orientedError (η ω) (σ ω) n x := by
  induction n generalizing x with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_orientedOp_apply _ ih x).add
      (measurable_orientedNoise η σ hη hσ n x)

theorem abs_orientedOp_le (f : Site d → ℝ) (x : Site d) :
    |orientedOp f x| ≤ orientedOp (fun y => |f y|) x := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [orientedOp, orientedOp, abs_div, abs_of_nonneg hd0]
  exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hd0

theorem orientedOp_fun_sub (f g : Site d → ℝ) (x : Site d) :
    orientedOp (fun y => f y - g y) x = orientedOp f x - orientedOp g x := by
  exact orientedOp_sub f g x

theorem orientedError_succ_eq (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (n : ℕ) (x : Site d) :
    orientedError η σ (n + 1) x = (orientedArrivalCount η σ n x : ℝ) -
      orientedOp (fun y => (orientedOdometer η σ n y : ℝ) - orientedError η σ n y) x := by
  change orientedOp (orientedError η σ n) x +
    ((orientedArrivalCount η σ n x : ℝ) - orientedOp (fun y => (orientedOdometer η σ n y : ℝ)) x) = _
  rw [orientedOp_fun_sub]
  ring

theorem orientedCorrected_succ (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (n : ℕ) (x : Site d) :
    (orientedOdometer η σ (n + 1) x : ℝ) - orientedError η σ (n + 1) x =
      max (-(orientedError η σ (n + 1) x)) ((η x : ℝ) +
        orientedOp (fun y => (orientedOdometer η σ n y : ℝ) - orientedError η σ n y) x) := by
  rw [orientedOdometer_succ, toNat_cast_eq_max, Int.cast_add, Int.cast_natCast,
    max_comm ((η x : ℝ) + (orientedArrivalCount η σ n x : ℝ)), orientedError_succ_eq,
    ← max_sub_sub_right]
  congr 1 <;> ring

theorem oriented_corrected_comparison (hd : 1 ≤ d) (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (n : ℕ) (x : Site d) :
    |(orientedOdometer η σ n x : ℝ) - orientedError η σ n x - uOriented (fun y => (η y : ℝ)) n x| ≤
      orientedMaxMean (orientedError η σ) n x := by
  induction n generalizing x with
  | zero =>
    simp [orientedOdometer, orientedError, uOriented, orientedMaxMean, orientedMax]
  | succ n ih =>
    rw [orientedCorrected_succ, uOriented]
    apply (abs_max_sub_max_le _ _ _ _).trans (max_le _ _)
    · rw [sub_zero, abs_neg]
      exact abs_le_orientedMaxMean hd (orientedError η σ) (n + 1) x
    · have he : ((η x : ℝ) + orientedOp
          (fun y => (orientedOdometer η σ n y : ℝ) - orientedError η σ n y) x) -
          ((η x : ℝ) + orientedOp (uOriented (fun y => (η y : ℝ)) n) x) =
          orientedOp (fun y => (orientedOdometer η σ n y : ℝ) - orientedError η σ n y -
            uOriented (fun z => (η z : ℝ)) n y) x := by
        simp only [orientedOp_fun_sub]
        ring
      rw [he]
      exact (abs_orientedOp_le _ x).trans ((orientedOp_mono ih x).trans
        (orientedOp_orientedMaxMean_le hd (orientedError η σ) n x))

theorem oriented_particle_error_comparison (hd : 1 ≤ d) (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (n : ℕ) (x : Site d) :
    |(orientedOdometer η σ n x : ℝ) - uOriented (fun y => (η y : ℝ)) n x| ≤
      2 * orientedMaxMean (orientedError η σ) n x := by
  have hc := oriented_corrected_comparison hd η σ n x
  have he := abs_le_orientedMaxMean hd (orientedError η σ) n x
  have ht := abs_add_le ((orientedOdometer η σ n x : ℝ) - orientedError η σ n x -
    uOriented (fun y => (η y : ℝ)) n x) (orientedError η σ n x)
  have hid : ((orientedOdometer η σ n x : ℝ) - orientedError η σ n x -
    uOriented (fun y => (η y : ℝ)) n x) + orientedError η σ n x =
      (orientedOdometer η σ n x : ℝ) - uOriented (fun y => (η y : ℝ)) n x := by ring
  rw [hid] at ht
  linarith

end Parking
