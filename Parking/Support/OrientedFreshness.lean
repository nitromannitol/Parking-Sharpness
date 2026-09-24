/- Independence from outgoing instructions and from scenery on higher layers. -/
import Parking.Support.OrientedOdometerMeasurable
import LatticeProb.Prob.Coordinate

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb Finset
variable {d : ℕ}

theorem orientedOdometer_indep_stack_coord (hd : 1 ≤ d) (η : Site d → ℤ)
    (n : ℕ) (x : Site d) (q : Site d × ℕ) (hq : layerHeight x ≤ layerHeight q.1) :
    IndepFun (fun σ : Site d × ℕ → Site d => orientedOdometer η σ n x)
      (fun σ => σ q) (orientedStackLaw d) := by
  haveI : ∀ p : Site d × ℕ, IsProbabilityMeasure (orientedInstructionLaw p.1) :=
    fun p => orientedInstructionLaw_isProbability hd p.1
  apply indepFun_of_update_invariant (fun p : Site d × ℕ => orientedInstructionLaw p.1)
    (0 : Site d) _ (measurable_orientedOdometer _ _ measurable_const measurable_id n x)
  intro σ
  exact orientedOdometer_update_stack η σ n x q 0 hq

def orientedArrivalCount (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (n : ℕ) (x : Site d) : ℕ :=
  ∑ i : Fin d, arrivals σ (x - unit i) x (orientedOdometer η σ n (x - unit i))

theorem orientedOdometer_succ (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (n : ℕ) (x : Site d) :
    orientedOdometer η σ (n + 1) x = (η x + (orientedArrivalCount η σ n x : ℤ)).toNat := by
  simp only [orientedOdometer, orientedArrivalCount, Nat.cast_sum]

theorem measurable_orientedArrivalCount {Ω : Type*} [MeasurableSpace Ω]
    (η : Ω → Site d → ℤ) (σ : Ω → Site d × ℕ → Site d)
    (hη : Measurable η) (hσ : Measurable σ) (n : ℕ) (x : Site d) :
    Measurable fun ω => orientedArrivalCount (η ω) (σ ω) n x := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_arrivals_variable σ hσ _
    (measurable_orientedOdometer η σ hη hσ n (x - unit i)) (x - unit i) x

theorem orientedArrivalCount_update_conf (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (n : ℕ) (x y : Site d) (c : ℤ) (hy : layerHeight x ≤ layerHeight y) :
    orientedArrivalCount (Function.update η y c) σ n x = orientedArrivalCount η σ n x := by
  unfold orientedArrivalCount
  apply sum_congr rfl
  intro i _
  rw [orientedOdometer_update_conf η σ n (x - unit i) y c (by
    rw [layerHeight_sub, layerHeight_unit]
    omega)]

theorem orientedArrivalCount_indep_conf_coord (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (σ : Site d × ℕ → Site d) (n : ℕ) (x y : Site d) (hy : layerHeight x ≤ layerHeight y) :
    IndepFun (fun η : Site d → ℤ => orientedArrivalCount η σ n x) (fun η => η y) (iidLaw d ν) := by
  apply indepFun_of_update_invariant (fun _ : Site d => ν) (0 : ℤ) _
    (measurable_orientedArrivalCount _ _ measurable_id measurable_const n x)
  intro η
  exact orientedArrivalCount_update_conf η σ n x y 0 hy

end Parking
