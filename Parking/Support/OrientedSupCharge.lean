/- The quadratic variation of the directed martingale when every instruction is
read at its own horizon.

Regrouped by instruction, the directed error field of `parking.tex:3240-3250`
gives instruction `(y,j)` a horizon of its own, so the conditional variance of
its increment is `Gamma_M(y)` at that horizon and the quadratic variation is
bounded by `sum_y U_n(y) * sup_M Gamma_M(y)`.  The weights `sup_M Gamma_M(y)`
sum to at most one over any box, by the telescoping identity of
`parking.tex:3255-3262`, so the same convexity that bounds the total charge of
one round bounds this one: the weighted average of the odometer moments over the
box is below the odometer moment at the origin.
-/
import Parking.Support.OrientedChargeMoment
import Parking.Support.OrientedTelescope

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

/-- The quadratic variation of the directed martingale over the box of radius
`N`, each instruction weighted by the supremum over horizons of its layer
variance. -/
def orientedSupCharge (d : ℕ) (N n : ℕ) (z : (Site d → ℤ) × (Site d × ℕ → Site d)) : ℝ :=
  ∑ y ∈ boxFinset (0 : Site d) N,
    (⨆ m : ℕ, orientedGamma d m y) * (orientedOdometer z.1 z.2 n y : ℝ)

theorem orientedSupCharge_nonneg (hd : 1 ≤ d) (N n : ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) : 0 ≤ orientedSupCharge d N n z :=
  sum_nonneg fun y _ => mul_nonneg (orientedGammaSup_nonneg hd y) (Nat.cast_nonneg _)

/-- **The quadratic variation has the odometer's moments.**  The weights sum to
at most one over the box, so the weighted sum of the odometer moments over the
box is below the odometer moment at the origin. -/
theorem orientedSupCharge_moment (hd : 2 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (N n : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun z => orientedSupCharge d N n z ^ p)
        ((iidLaw d ν).prod (orientedStackLaw d)) ∧
      (∫ z, orientedSupCharge d N n z ^ p ∂((iidLaw d ν).prod (orientedStackLaw d))) ≤
        ∫ ω : Data d, (U ω n 0 : ℝ) ^ p ∂(orientedLaw d ν) := by
  haveI := hν.prob
  have hd1 : 1 ≤ d := by omega
  have h := integral_weighted_rpow_le ((iidLaw d ν).prod (orientedStackLaw d))
    (boxFinset (0 : Site d) N)
    (fun y => ⨆ m : ℕ, orientedGamma d m y)
    (fun y z => (orientedOdometer z.1 z.2 n y : ℝ))
    (fun y _ => orientedGammaSup_nonneg hd1 y) (fun _ _ _ => Nat.cast_nonneg _)
    (fun y _ => (measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
      (measurable_orientedOdometer _ _ measurable_fst measurable_snd n y)) hp
    (fun y _ => integrable_orientedOdometer_joint_rpow hd1 ν hν hp n y)
    (∫ ω : Data d, (U ω n 0 : ℝ) ^ p ∂(orientedLaw d ν))
    (integral_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) p)
    (fun y _ => (integral_orientedOdometer_joint_rpow hd1 ν p n y).le)
  refine ⟨h.1, h.2.trans ?_⟩
  have hw : (∑ y ∈ boxFinset (0 : Site d) N, (⨆ m : ℕ, orientedGamma d m y)) ^ p ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow
      (sum_nonneg fun y _ => orientedGammaSup_nonneg hd1 y)
      (sum_orientedGammaSup_box_le_one hd N) (by linarith : 0 ≤ p)
  exact mul_le_of_le_one_left (integral_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) p) hw

end Parking
end
