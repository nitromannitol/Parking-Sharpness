/-
The charge-weighted moment of the directed odometer: the weights are the
suprema of the directed layer variances, whose total over the box of radius `n`
is at most one (`parking.tex:3255-3262`), and translation invariance makes every
`U_n(y)` carry the moment of `U_n(0)`.
-/
import Parking.Support.OrientedTelescope
import Parking.Support.OrientedChargeMoment
import Parking.Support.WeightedMoment
import Parking.Support.OrientedMoments
import Parking.Support.OrientedParticleMoment
import Parking.Support.OrientedLaw

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem oriented_charge_weighted_moment (hd : 2 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    (∫ ω : Data d, (∑ y ∈ boxFinset (0 : Site d) n,
        (⨆ m : ℕ, orientedGamma d m y) * (U ω n y : ℝ)) ^ p ∂(orientedLaw d ν)) ^ (1 / p) ≤
      (∫ ω : Data d, (U ω n 0 : ℝ) ^ p ∂(orientedLaw d ν)) ^ (1 / p) := by
  haveI := hν.prob
  obtain ⟨θ, hθ, he⟩ := hν.expMoment
  have hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν :=
    integrable_expMax_of_expAbs hθ he
  have hM0 : 0 ≤ ∫ ω : Data d, (U ω n 0 : ℝ) ^ p ∂(orientedLaw d ν) :=
    integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) p
  have hw : ∀ y ∈ boxFinset (0 : Site d) n, 0 ≤ ⨆ m : ℕ, orientedGamma d m y :=
    fun y _ => orientedGammaSup_nonneg (by omega) y
  have hX : ∀ y ∈ boxFinset (0 : Site d) n, ∀ ω : Data d, 0 ≤ (U ω n y : ℝ) :=
    fun y _ ω => Nat.cast_nonneg _
  have hm : ∀ y ∈ boxFinset (0 : Site d) n, Measurable (fun ω : Data d => (U ω n y : ℝ)) :=
    fun y _ => (measurable_from_countable' fun m : ℕ => (m : ℝ)).comp (measurable_U n y)
  have hi : ∀ y ∈ boxFinset (0 : Site d) n,
      Integrable (fun ω : Data d => (U ω n y : ℝ) ^ p) (orientedLaw d ν) :=
    fun y _ => integrable_oriented_U_rpow (by omega) ν hθ hexp hp n y
  have hle : ∀ y ∈ boxFinset (0 : Site d) n,
      ∫ ω : Data d, (U ω n y : ℝ) ^ p ∂(orientedLaw d ν) ≤
        ∫ ω : Data d, (U ω n 0 : ℝ) ^ p ∂(orientedLaw d ν) :=
    fun y _ => le_of_eq (integral_oriented_U_rpow_shift (by omega) ν p n y)
  obtain ⟨hint, hbound⟩ := integral_weighted_rpow_le (orientedLaw d ν)
    (boxFinset (0 : Site d) n) (fun y => ⨆ m : ℕ, orientedGamma d m y)
    (fun y ω => (U ω n y : ℝ)) hw hX hm hp hi _ hM0 hle
  have hsum1 : ∑ y ∈ boxFinset (0 : Site d) n, (⨆ m : ℕ, orientedGamma d m y) ≤ 1 :=
    sum_orientedGammaSup_box_le_one (by omega) n
  have hsum0 : 0 ≤ ∑ y ∈ boxFinset (0 : Site d) n, (⨆ m : ℕ, orientedGamma d m y) :=
    sum_nonneg fun y hy => hw y hy
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpow : (∑ y ∈ boxFinset (0 : Site d) n, (⨆ m : ℕ, orientedGamma d m y)) ^ p ≤ 1 :=
    Real.rpow_le_one hsum0 hsum1 hp0.le
  have hfin : ∫ ω : Data d, (∑ y ∈ boxFinset (0 : Site d) n,
      (⨆ m : ℕ, orientedGamma d m y) * (U ω n y : ℝ)) ^ p ∂(orientedLaw d ν) ≤
      ∫ ω : Data d, (U ω n 0 : ℝ) ^ p ∂(orientedLaw d ν) := by
    refine hbound.trans ?_
    calc (∑ y ∈ boxFinset (0 : Site d) n, (⨆ m : ℕ, orientedGamma d m y)) ^ p *
          (∫ ω : Data d, (U ω n 0 : ℝ) ^ p ∂(orientedLaw d ν))
        ≤ 1 * (∫ ω : Data d, (U ω n 0 : ℝ) ^ p ∂(orientedLaw d ν)) :=
          mul_le_mul_of_nonneg_right hpow hM0
      _ = _ := one_mul _
  have hI0 : 0 ≤ ∫ ω : Data d, (∑ y ∈ boxFinset (0 : Site d) n,
      (⨆ m : ℕ, orientedGamma d m y) * (U ω n y : ℝ)) ^ p ∂(orientedLaw d ν) :=
    integral_nonneg fun ω => Real.rpow_nonneg
      (sum_nonneg fun y hy => mul_nonneg (hw y hy) (hX y hy ω)) p
  calc (∫ ω : Data d, (∑ y ∈ boxFinset (0 : Site d) n,
        (⨆ m : ℕ, orientedGamma d m y) * (U ω n y : ℝ)) ^ p ∂(orientedLaw d ν)) ^ (1 / p)
      ≤ (∫ ω : Data d, (U ω n 0 : ℝ) ^ p ∂(orientedLaw d ν)) ^ (1 / p) :=
        Real.rpow_le_rpow hI0 hfin (by positivity)

end Parking
