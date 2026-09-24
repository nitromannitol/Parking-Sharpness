/- Predictable departure counts and the moments of one directed routing instruction. -/
import Parking.Support.CoordinateFiltration
import Parking.Support.OrientedOdometerMeasurable
import Parking.Support.OrientedVariance
import Parking.Support.OrientedInstructionIntegral

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
open scoped Classical
variable {d K : ℕ}

theorem measurable_orientedOdometer_coordinateFiltration
    (b : Site d × ℕ → Site d) (q : Fin K → Site d × ℕ)
    (hq : Monotone (fun j => layerHeight (q j).1)) (j : Fin K) (n : ℕ) :
    Measurable[coordinateFiltration b q j.val]
      (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) => orientedOdometer z.1 z.2 n (q j).1) := by
  apply measurable_erasedCoordinateSpace b (remainingCoordinates q j.val) _
    (measurable_orientedOdometer _ _ measurable_fst measurable_snd n (q j).1)
  intro z
  apply orientedOdometer_lower_layers n (q j).1 (fun _ _ => rfl)
  intro c hc
  have hnot : c ∉ remainingCoordinates q j.val := by
    rintro ⟨k, hjk, hkc⟩
    have hh := hq (show j ≤ k from hjk)
    change layerHeight (q j).1 ≤ layerHeight (q k).1 at hh
    rw [hkc] at hh
    omega
  exact if_neg hnot

def orientedRouteDisc (l : ℕ) (y z : Site d) : ℝ :=
  orientedLayer d l z - orientedLayer d (l + 1) y

theorem abs_orientedRouteDisc_le (hd : 1 ≤ d) (l : ℕ) (y z : Site d) :
    |orientedRouteDisc l y z| ≤ 1 := by
  dsimp only [orientedRouteDisc]
  have h0 := orientedLayer_nonneg l z
  have h1 := orientedLayer_le_one hd l z
  have h2 := orientedLayer_nonneg (l + 1) y
  have h3 := orientedLayer_le_one hd (l + 1) y
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem integral_orientedRouteDisc (hd : 1 ≤ d) (l : ℕ) (y : Site d) :
    (∫ z, orientedRouteDisc l y z ∂(orientedInstructionLaw y)) = 0 := by
  rw [integral_orientedInstructionLaw]
  simp only [orientedRouteDisc, sum_sub_distrib, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, sub_div, orientedLayer_succ]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt hd))
  field_simp
  ring

theorem integral_orientedRouteDisc_sq (l : ℕ) (y : Site d) :
    (∫ z, orientedRouteDisc l y z ^ 2 ∂(orientedInstructionLaw y)) = orientedCharge d l y := by
  rw [integral_orientedInstructionLaw]
  rfl

end Parking
