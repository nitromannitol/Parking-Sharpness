/- The directed operator half of the one-layer noise average. -/
import Parking.Support.OrientedRoute

import Parking.Support.OrientedRoute
import Parking.Support.OrientedParticleMoment
import Parking.Support.OrientedRouting

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem orientedLayerAverage_op_eq (η : Site d → ℤ)
    (σ : Site d × ℕ → Site d) (k m : ℕ) :
    (∑' z : Site d, orientedLayer d m z *
        orientedOp (fun y => (orientedOdometer η σ k y : ℝ)) z) =
      ∑' y : Site d, ∑ _j ∈ Finset.range (orientedOdometer η σ k y),
        orientedLayer d (m + 1) y := by
  have hstep : ∀ z : Site d, orientedLayer d m z *
      orientedOp (fun y => (orientedOdometer η σ k y : ℝ)) z =
      (∑ i : Fin d, orientedLayer d m z * (orientedOdometer η σ k (z - unit i) : ℝ)) / d := by
    intro z
    rw [orientedOp, ← mul_div_assoc, Finset.mul_sum]
  rw [tsum_congr hstep, tsum_div_const]
  have hsum : ∀ i : Fin d, Summable fun z : Site d =>
      orientedLayer d m z * (orientedOdometer η σ k (z - unit i) : ℝ) :=
    fun i => (summable_orientedLayer_weight m (fun z => (orientedOdometer η σ k (z - unit i) : ℝ))).congr fun z => mul_comm _ _
  rw [Summable.tsum_finsetSum (fun i _ => hsum i)]
  have hshift : ∀ i : Fin d, (∑' z : Site d,
      orientedLayer d m z * (orientedOdometer η σ k (z - unit i) : ℝ)) =
      ∑' y : Site d, orientedLayer d m (y + unit i) * (orientedOdometer η σ k y : ℝ) := by
    intro i
    have := (Equiv.subRight (unit i)).tsum_eq
      (fun y : Site d => orientedLayer d m (y + unit i) * (orientedOdometer η σ k y : ℝ))
    rw [← this]
    exact tsum_congr fun z => by simp
  rw [Finset.sum_congr rfl fun i _ => hshift i]
  have hsum2 : ∀ i : Fin d, Summable fun y : Site d =>
      orientedLayer d m (y + unit i) * (orientedOdometer η σ k y : ℝ) := by
    intro i
    rw [← (Equiv.subRight (unit i)).summable_iff]
    exact (hsum i).congr fun z => by simp
  rw [← Summable.tsum_finsetSum (fun i _ => hsum2 i)]
  rw [← tsum_div_const]
  refine tsum_congr fun y => ?_
  have hfac : (∑ i : Fin d, orientedLayer d m (y + unit i) * (orientedOdometer η σ k y : ℝ))
      = (orientedOdometer η σ k y : ℝ) * ∑ i : Fin d, orientedLayer d m (y + unit i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hfac, mul_div_assoc]
  have hsucc : (∑ i : Fin d, orientedLayer d m (y + unit i)) / (d : ℝ) =
      orientedLayer d (m + 1) y := (orientedLayer_succ m y).symm
  rw [hsucc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Parking
end
