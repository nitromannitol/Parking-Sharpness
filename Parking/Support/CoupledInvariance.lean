/-
The coupling input law is translation invariant: both configurations, all
priorities and each fresh table layer have invariant product laws.
-/
import Parking.Support.MatchedShift
import Parking.Support.CoupledLaw
import Parking.Support.Invariance

noncomputable section

open MeasureTheory LatticeProb
open scoped ENNReal

variable {d : ℕ}

/-- Translation of both initial configurations, their priorities and the round tables. -/
def Parking.shiftCoupledData (v : Site d) (ω : Parking.CoupledData d) : Parking.CoupledData d :=
  ((fun x => ω.1.1 (x + v), Parking.shiftRank v ω.1.2), Parking.shiftRoundNoise v ω.2)

theorem Parking.measurable_shiftRoundNoise (v : Site d) :
    Measurable (Parking.shiftRoundNoise v) := by
  apply measurable_pi_lambda
  intro t
  apply measurable_pi_lambda
  intro q
  exact (measurable_pi_apply (Parking.shiftRoundSlot v q)).comp (measurable_pi_apply t)

theorem Parking.roundNoiseLaw_map_shift (hd : 1 ≤ d) (v : Site d) :
    (Parking.roundNoiseLaw d).map (Parking.shiftRoundNoise v) = Parking.roundNoiseLaw d := by
  haveI := Parking.stepLaw_isProbability hd
  change (Measure.infinitePi fun _ : ℕ =>
    Measure.infinitePi fun _ : Parking.RoundSlot d => Parking.stepLaw d).map
    (fun (σ : Parking.RoundNoise d) t q => σ t (Parking.shiftRoundSlot v q)) = _
  have h := Measure.infinitePi_map_pi
    (fun _ : ℕ => Measure.infinitePi fun _ : Parking.RoundSlot d => Parking.stepLaw d)
    (f := fun (_ : ℕ) (τ : Parking.RoundSlot d → Fin d × Bool) (q : Parking.RoundSlot d) =>
      τ (Parking.shiftRoundSlot v q))
    (fun _ => measurable_pi_lambda _ fun q => measurable_pi_apply (Parking.shiftRoundSlot v q))
  simpa only [Parking.roundNoiseLaw, LatticeProb.infinitePi_map_comp' (Parking.stepLaw d) (Parking.shiftRoundSlot v)
    (Parking.shiftRoundSlot_injective v)] using h

theorem Parking.measurable_shiftCoupledData (v : Site d) :
    Measurable (Parking.shiftCoupledData v) := by
  have hc : Measurable (fun c : Site d → ℤ × ℤ => fun x => c (x + v)) :=
    measurable_pi_lambda _ fun x => measurable_pi_apply (x + v)
  exact (hc.prodMap (Parking.measurable_shiftRank v)).prodMap (Parking.measurable_shiftRoundNoise v)

/-- The full coupling law is translation invariant. -/
theorem Parking.coupledLaw_map_shift (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1) (v : Site d) :
    (Parking.coupledLaw d ν p).map (Parking.shiftCoupledData v) = Parking.coupledLaw d ν p := by
  haveI := Parking.resampleOne_isProbability ν hp
  haveI : IsProbabilityMeasure (Parking.resampleLaw d ν p) := by
    unfold Parking.resampleLaw LatticeProb.iidLaw
    infer_instance
  haveI := LatticeProb.rankLaw_isProbability d
  haveI := Parking.roundNoiseLaw_isProbability hd
  have hc : Measurable (fun c : Site d → ℤ × ℤ => fun x => c (x + v)) :=
    measurable_pi_lambda _ fun x => measurable_pi_apply (x + v)
  change (((Parking.resampleLaw d ν p).prod (rankLaw d)).prod (Parking.roundNoiseLaw d)).map
    (Prod.map (Prod.map (fun c : Site d → ℤ × ℤ => fun x => c (x + v)) (Parking.shiftRank v))
      (Parking.shiftRoundNoise v)) = _
  rw [← Measure.map_prod_map _ _ (hc.prodMap (Parking.measurable_shiftRank v))
    (Parking.measurable_shiftRoundNoise v),
    ← Measure.map_prod_map _ _ hc (Parking.measurable_shiftRank v),
    Parking.rankLaw_map_shiftRank, Parking.roundNoiseLaw_map_shift hd]
  rw [Parking.resampleLaw, Parking.iidLaw_map_shiftConf]
  rfl

end
