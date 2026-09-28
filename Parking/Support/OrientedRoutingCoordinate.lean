import Parking.Support.CoordinateFiltration
import Parking.Support.OrientedOdometerMeasurable
import Parking.Support.OrientedVariance
import Parking.Support.OrientedInstructionIntegral

/-!
# Predictable departure counts and one-instruction moments

Predictable departure counts and the moments of one directed routing instruction.
-/

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
open scoped Classical
variable {d K : ℕ}

/-- The number of departures `orientedOdometer z.1 z.2 n (q j).1` at the site of the `j`-th
coordinate of an increasing sequence `q` (increasing in `layerHeight`) is measurable with
respect to the coordinate filtration up to `j`: only coordinates `k` with `layerHeight (q
k).1 ≤ layerHeight (q j).1` can influence it, and monotonicity of `q` in `layerHeight`
confines those to indices `k ≤ j`. -/
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

/-- The one-layer routing discrepancy between the layer weight of a routing instruction's
target `z` and the layer weight of its source `y` one layer earlier. -/
def orientedRouteDisc (l : ℕ) (y z : Site d) : ℝ :=
  orientedLayer d l z - orientedLayer d (l + 1) y

/-- The one-layer routing discrepancy is bounded by `1` in absolute value, since each
layer weight lies in `[0, 1]`. -/
theorem abs_orientedRouteDisc_le (hd : 1 ≤ d) (l : ℕ) (y z : Site d) :
    |orientedRouteDisc l y z| ≤ 1 := by
  dsimp only [orientedRouteDisc]
  have h0 := orientedLayer_nonneg l z
  have h1 := orientedLayer_le_one hd l z
  have h2 := orientedLayer_nonneg (l + 1) y
  have h3 := orientedLayer_le_one hd (l + 1) y
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The one-layer routing discrepancy has mean zero under the law of one directed routing
instruction from `y`, since that law averages `orientedLayer d l` over the `d` directions
in exactly the way the layer recursion `orientedLayer_succ` reconstructs
`orientedLayer d (l + 1) y`. -/
theorem integral_orientedRouteDisc (hd : 1 ≤ d) (l : ℕ) (y : Site d) :
    (∫ z, orientedRouteDisc l y z ∂(orientedInstructionLaw y)) = 0 := by
  rw [integral_orientedInstructionLaw]
  simp only [orientedRouteDisc, sum_sub_distrib, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, sub_div, orientedLayer_succ]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt hd))
  field_simp
  ring

/-- The second moment of the one-layer routing discrepancy under the law of one directed
routing instruction from `y` is the directed charge `orientedCharge d l y`, which is this
quantity's defining formula. -/
theorem integral_orientedRouteDisc_sq (l : ℕ) (y : Site d) :
    (∫ z, orientedRouteDisc l y z ^ 2 ∂(orientedInstructionLaw y)) = orientedCharge d l y := by
  rw [integral_orientedInstructionLaw]
  rfl

end Parking
