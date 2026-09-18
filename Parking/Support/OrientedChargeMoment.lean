/- The total directed variance charge and its particle moment bound. -/
import Parking.Support.OrientedFiniteRoute
import Parking.Support.OrientedNorm

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem sum_orientedCharge_horizons_le_one (hd : 1 ≤ d) (S : Finset (Site d)) (l : Site d → ℕ) :
    ∑ y ∈ S, orientedCharge d (l y) y ≤ 1 := by
  have hc (y : Site d) : orientedCharge d (l y) y ≤ orientedGamma d (l y + 1) y := by
    rw [orientedGamma_eq_sum]
    exact single_le_sum (fun k _ => orientedCharge_nonneg k y) (mem_range.mpr (Nat.lt_succ_self _))
  exact (sum_le_sum (fun y _ => hc y)).trans
    (sum_orientedGamma_horizons_le_one hd (S.sup (fun y => l y + 1)) S (fun y => l y + 1)
      (fun y hy => le_sup (f := fun y => l y + 1) hy))

def orientedTotalCharge (S : Finset (Site d)) (l : Site d → ℕ) (n : ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) : ℝ :=
  ∑ y ∈ S, orientedCharge d (l y) y * (orientedOdometer z.1 z.2 n y : ℝ)

theorem orientedTotalCharge_nonneg (S : Finset (Site d)) (l : Site d → ℕ) (n : ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) : 0 ≤ orientedTotalCharge S l n z :=
  sum_nonneg fun _ _ => mul_nonneg (orientedCharge_nonneg _ _) (Nat.cast_nonneg _)

theorem orientedTruncatedCharge_nonneg (S : Finset (Site d)) (m l : Site d → ℕ) (M : ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) : 0 ≤ orientedTruncatedCharge S m l M z :=
  sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (orientedCharge_nonneg _ _)

theorem orientedTruncatedCharge_le_total (S : Finset (Site d)) (m l : Site d → ℕ) (M n : ℕ)
    (hm : ∀ y ∈ S, m y ≤ n) (z : (Site d → ℤ) × (Site d × ℕ → Site d)) :
    orientedTruncatedCharge S m l M z ≤ orientedTotalCharge S l n z := by
  apply sum_le_sum
  intro y hy
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_left _ (orientedCharge_nonneg _ _)
  exact_mod_cast (min_le_right M (orientedOdometer z.1 z.2 (m y) y)).trans
    (orientedOdometer_mono_time z.1 z.2 y (hm y hy))

theorem orientedTotalCharge_moment (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (S : Finset (Site d)) (l : Site d → ℕ) (n : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun z => orientedTotalCharge S l n z ^ p) ((iidLaw d ν).prod (orientedStackLaw d)) ∧
    (∫ z, orientedTotalCharge S l n z ^ p ∂((iidLaw d ν).prod (orientedStackLaw d))) ≤
      ∫ ω : Data d, (U ω n 0 : ℝ) ^ p ∂(orientedLaw d ν) := by
  haveI := hν.prob
  have h := integral_weighted_rpow_le ((iidLaw d ν).prod (orientedStackLaw d)) S
    (fun y => orientedCharge d (l y) y) (fun y z => (orientedOdometer z.1 z.2 n y : ℝ))
    (fun y _ => orientedCharge_nonneg _ _) (fun _ _ _ => Nat.cast_nonneg _)
    (fun y _ => (measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
      (measurable_orientedOdometer _ _ measurable_fst measurable_snd n y)) hp
    (fun y _ => integrable_orientedOdometer_joint_rpow hd ν hν hp n y)
    (∫ ω : Data d, (U ω n 0 : ℝ) ^ p ∂(orientedLaw d ν))
    (integral_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) p)
    (fun y _ => (integral_orientedOdometer_joint_rpow hd ν p n y).le)
  refine ⟨h.1, h.2.trans ?_⟩
  have hw : (∑ y ∈ S, orientedCharge d (l y) y) ^ p ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow
      (sum_nonneg fun y _ => orientedCharge_nonneg _ _) (sum_orientedCharge_horizons_le_one hd S l)
      (by linarith : 0 ≤ p)
  exact mul_le_of_le_one_left (integral_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) p) hw

theorem integral_orientedTruncatedCharge_rpow_le (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (S : Finset (Site d)) (m l : Site d → ℕ) (M n : ℕ) (hm : ∀ y ∈ S, m y ≤ n)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫ z, orientedTruncatedCharge S m l M z ^ p ∂((iidLaw d ν).prod (orientedStackLaw d))) ≤
      ∫ ω : Data d, (U ω n 0 : ℝ) ^ p ∂(orientedLaw d ν) := by
  obtain ⟨hi, hb⟩ := orientedTotalCharge_moment hd ν hν S l n hp
  apply le_trans (integral_mono_of_nonneg
    (ae_of_all _ fun z => Real.rpow_nonneg (orientedTruncatedCharge_nonneg S m l M z) p) hi ?_) hb
  filter_upwards [] with z
  exact Real.rpow_le_rpow (orientedTruncatedCharge_nonneg S m l M z)
    (orientedTruncatedCharge_le_total S m l M n hm z) (by linarith)

end Parking
