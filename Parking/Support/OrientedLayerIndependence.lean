import Parking.Support.OrientedFreshness
import Parking.Support.CoordinateErasure

/-!
# Independence from upper-layer stacks and scenery

Independence of directed odometers from every stack on and above a layer.
-/

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb Finset
open scoped Classical
variable {d : ℕ}

/-- The odometer values `orientedOdometer η σ n (x i)` at sites `x i` of layer height at
most `h` are independent of the instructions `σ q` with `h ≤ layerHeight q.1`, since
`orientedOdometer_lower_layers` shows the former do not depend on the erased coordinates
and `indepFun_of_erasure_invariant` upgrades that invariance to independence. -/
theorem orientedOdometers_indep_upper_stacks {ι : Type*} (hd : 1 ≤ d) (η : Site d → ℤ)
    (n : ℕ) (x : ι → Site d) (h : ℤ) (hx : ∀ i, layerHeight (x i) ≤ h) :
    IndepFun (fun σ : Site d × ℕ → Site d => fun i => orientedOdometer η σ n (x i))
      (fun σ : Site d × ℕ → Site d => fun q : {q : Site d × ℕ | h ≤ layerHeight q.1} => σ q)
      (orientedStackLaw d) := by
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (orientedInstructionLaw q.1) :=
    fun q => orientedInstructionLaw_isProbability hd q.1
  apply indepFun_of_erasure_invariant (fun q : Site d × ℕ => orientedInstructionLaw q.1)
    {q : Site d × ℕ | h ≤ layerHeight q.1} (fun _ => (0 : Site d)) _
    (measurable_pi_lambda _ fun i =>
      measurable_orientedOdometer _ _ measurable_const measurable_id n (x i))
  intro σ
  funext i
  apply orientedOdometer_lower_layers n (x i) (fun _ _ => rfl)
  intro q hq
  exact if_neg (by change ¬h ≤ layerHeight q.1; have := hx i; omega)

/-- The arrival count `orientedArrivalCount η σ n x` depends only on the scenery and stack
coordinates below the layer of `x`, since it is built from `orientedOdometer` at the `d`
predecessors `x - unit i` and from the instructions issued at those predecessors, and
`orientedOdometer_lower_layers` already gives this invariance for the odometer. -/
theorem orientedArrivalCount_lower_layers {η η' : Site d → ℤ} {σ σ' : Site d × ℕ → Site d}
    (n : ℕ) (x : Site d)
    (hη : ∀ y, layerHeight y < layerHeight x → η y = η' y)
    (hσ : ∀ q : Site d × ℕ, layerHeight q.1 < layerHeight x → σ q = σ' q) :
    orientedArrivalCount η σ n x = orientedArrivalCount η' σ' n x := by
  unfold orientedArrivalCount
  apply sum_congr rfl
  intro i _
  have hh : layerHeight (x - unit i) = layerHeight x - 1 := by
    rw [layerHeight_sub, layerHeight_unit]
  have he := orientedOdometer_lower_layers (η := η) (η' := η') (σ := σ) (σ' := σ') n (x - unit i)
    (fun y hy => hη y (by rw [hh] at hy; omega))
    (fun q hq => hσ q (by rw [hh] at hq; omega))
  rw [he]
  unfold arrivals
  apply congrArg Finset.card
  apply filter_congr
  intro j _
  rw [hσ (x - unit i, j) (by change layerHeight (x - unit i) < layerHeight x; rw [hh]; omega)]

/-- The arrival count `orientedArrivalCount η σ n x` is independent of the scenery values
`η y` at sites `y` of layer height at least that of `x`, since
`orientedArrivalCount_lower_layers` shows it does not depend on those coordinates and
`indepFun_of_erasure_invariant` upgrades that invariance to independence. -/
theorem orientedArrivals_indep_upper_conf (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (σ : Site d × ℕ → Site d) (n : ℕ) (x : Site d) :
    IndepFun (fun η : Site d → ℤ => orientedArrivalCount η σ n x)
      (fun η : Site d → ℤ => fun y : {y : Site d | layerHeight x ≤ layerHeight y} => η y)
      (iidLaw d ν) := by
  apply indepFun_of_erasure_invariant (fun _ : Site d => ν)
    {y : Site d | layerHeight x ≤ layerHeight y} (fun _ => (0 : ℤ)) _
    (measurable_orientedArrivalCount _ _ measurable_id measurable_const n x)
  intro η
  apply orientedArrivalCount_lower_layers n x _ (fun _ _ => rfl)
  intro y hy
  exact if_neg (by change ¬layerHeight x ≤ layerHeight y; omega)

end Parking
