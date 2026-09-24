/- Independence of directed odometers from every stack on and above a layer. -/
import Parking.Support.OrientedFreshness
import Parking.Support.CoordinateErasure

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb Finset
open scoped Classical
variable {d : ℕ}

theorem orientedOdometers_indep_upper_stacks {ι : Type*} (hd : 1 ≤ d) (η : Site d → ℤ)
    (n : ℕ) (x : ι → Site d) (h : ℤ) (hx : ∀ i, layerHeight (x i) ≤ h) :
    IndepFun (fun σ : Site d × ℕ → Site d => fun i => orientedOdometer η σ n (x i))
      (fun σ : Site d × ℕ → Site d => fun q : {q : Site d × ℕ | h ≤ layerHeight q.1} => σ q)
      (orientedStackLaw d) := by
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (orientedInstructionLaw q.1) :=
    fun q => orientedInstructionLaw_isProbability hd q.1
  apply indepFun_of_erasure_invariant (fun q : Site d × ℕ => orientedInstructionLaw q.1)
    {q : Site d × ℕ | h ≤ layerHeight q.1} (fun _ => (0 : Site d)) _
    (measurable_pi_lambda _ fun i => measurable_orientedOdometer _ _ measurable_const measurable_id n (x i))
  intro σ
  funext i
  apply orientedOdometer_lower_layers n (x i) (fun _ _ => rfl)
  intro q hq
  exact if_neg (by change ¬h ≤ layerHeight q.1; have := hx i; omega)

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
