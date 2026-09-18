/- Integrable directed odometers for every fixed scenery realization. -/
import Parking.Support.OrientedFreshness
import Parking.Support.WBound

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem orientedOdometer_ae_le_bound (hd : 1 ≤ d) (η : Site d → ℤ) (n : ℕ) (x : Site d) :
    ∀ᵐ σ ∂(orientedStackLaw d), orientedOdometer η σ n x ≤
      n * ∑ y ∈ boxFinset x n, (η y).toNat := by
  refine (orientedStackLaw_ae_forward hd).mono fun σ hσ => ?_
  let ω : Data d := (η, σ, fun _ => 0)
  have he := orientedOdometer_eq_U ω hσ n x
  have hb := U_le_confBox ω n x
  rw [← he] at hb
  dsimp only [confBox, ω] at hb
  exact_mod_cast hb

theorem integrable_orientedOdometer_given (hd : 1 ≤ d) (η : Site d → ℤ) (n : ℕ) (x : Site d) :
    Integrable (fun σ : Site d × ℕ → Site d => (orientedOdometer η σ n x : ℝ)) (orientedStackLaw d) := by
  haveI := orientedStackLaw_isProbability hd
  have hm : Measurable fun σ : Site d × ℕ → Site d => (orientedOdometer η σ n x : ℝ) :=
    (measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
      (measurable_orientedOdometer _ _ measurable_const measurable_id n x)
  refine (integrable_const ((n * ∑ y ∈ boxFinset x n, (η y).toNat : ℕ) : ℝ)).mono'
    hm.aestronglyMeasurable ((orientedOdometer_ae_le_bound hd η n x).mono fun σ hσ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast hσ

theorem integrable_orientedArrivals_given (hd : 1 ≤ d) (η : Site d → ℤ) (n : ℕ) (x : Site d) :
    Integrable (fun σ : Site d × ℕ → Site d => (orientedArrivalCount η σ n x : ℝ)) (orientedStackLaw d) := by
  have hdom : Integrable (fun σ : Site d × ℕ → Site d =>
      ∑ i : Fin d, (orientedOdometer η σ n (x - unit i) : ℝ)) (orientedStackLaw d) :=
    integrable_finsetSum _ (fun i _ => integrable_orientedOdometer_given hd η n (x - unit i))
  have hm : Measurable fun σ : Site d × ℕ → Site d => (orientedArrivalCount η σ n x : ℝ) :=
    (measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
      (measurable_orientedArrivalCount _ _ measurable_const measurable_id n x)
  refine hdom.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun σ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  simp only [orientedArrivalCount, Nat.cast_sum]
  apply sum_le_sum
  intro i _
  have h := card_filter_le (range (orientedOdometer η σ n (x - unit i)))
    (fun j => σ (x - unit i, j) = x)
  have hnat : arrivals σ (x - unit i) x (orientedOdometer η σ n (x - unit i)) ≤
      orientedOdometer η σ n (x - unit i) := by simpa only [arrivals, card_range] using h
  exact_mod_cast hnat

end Parking
