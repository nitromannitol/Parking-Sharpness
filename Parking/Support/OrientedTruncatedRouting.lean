/- The instruction sum after truncating every departure stack at a fixed index. -/
import Parking.Support.OrientedRoutingCoordinate
import Parking.Support.CoordinateMartingale
import Parking.Support.SortedEnumeration

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
open scoped Classical
variable {d : ℕ}

def orientedTruncatedRoute (S : Finset (Site d)) (m l : Site d → ℕ) (M : ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) : ℝ :=
  ∑ y ∈ S, ∑ j ∈ range M, if j < orientedOdometer z.1 z.2 (m y) y then
    orientedRouteDisc (l y) y (z.2 (y, j)) else 0

def orientedTruncatedCharge (S : Finset (Site d)) (m l : Site d → ℕ) (M : ℕ)
    (z : (Site d → ℤ) × (Site d × ℕ → Site d)) : ℝ :=
  ∑ y ∈ S, (min M (orientedOdometer z.1 z.2 (m y) y) : ℕ) * orientedCharge d (l y) y

theorem sum_range_lt_indicator (M N : ℕ) :
    (∑ j ∈ range M, if j < N then (1 : ℝ) else 0) = (min M N : ℕ) := by
  have he : (range M).filter (fun j => j < N) = range (min M N) := by
    ext j
    simp only [mem_filter, mem_range, lt_min_iff]
  rw [← sum_filter, he]
  simp

theorem exists_oriented_truncated_route_moment (hBern : External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (ν : Measure ℤ) (_ : IsProbabilityMeasure ν)
      (S : Finset (Site d)) (m l : Site d → ℕ) (M : ℕ) (r : ℝ), 2 ≤ r →
      (∫ z, |orientedTruncatedRoute S m l M z| ^ r
        ∂((iidLaw d ν).prod (orientedStackLaw d))) ^ (1 / r) ≤
        C * (Real.sqrt r * (∫ z, orientedTruncatedCharge S m l M z ^ (r / 2)
          ∂((iidLaw d ν).prod (orientedStackLaw d))) ^ (1 / r) + r) := by
  obtain ⟨C, hC, hb⟩ := exists_finite_coordinate_moment_bound hBern
  refine ⟨C, hC, fun d hd ν _ S m l M r hr => ?_⟩
  haveI : ∀ c : Site d × ℕ, IsProbabilityMeasure (orientedInstructionLaw c.1) :=
    fun c => orientedInstructionLaw_isProbability hd c.1
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  let T := S ×ˢ range M
  obtain ⟨q, hq, hcov, hsort⟩ := exists_sorted_enumeration T (fun c => layerHeight c.1)
  let b : Site d × ℕ → Site d := fun _ => 0
  let H : Fin T.card → (Site d → ℤ) × (Site d × ℕ → Site d) → ℝ :=
    fun j z => if (q j).2 < orientedOdometer z.1 z.2 (m (q j).1) (q j).1 then 1 else 0
  let g : (j : Fin T.card) → Site d → ℝ := fun j => orientedRouteDisc (l (q j).1) (q j).1
  have hH (j : Fin T.card) : Measurable[coordinateFiltration b q j.val] (H j) := by
    exact (measurable_from_countable' (fun N : ℕ => if (q j).2 < N then (1 : ℝ) else 0)).comp
      (measurable_orientedOdometer_coordinateFiltration b q hsort j (m (q j).1))
  have hHb (j : Fin T.card) (z : (Site d → ℤ) × (Site d × ℕ → Site d)) : |H j z| ≤ 1 := by
    dsimp only [H]
    split_ifs <;> norm_num
  have h := hb (Site d → ℤ) (Site d × ℕ) (fun _ => Site d) inferInstance inferInstance inferInstance
    T.card (iidLaw d ν) inferInstance (fun c => orientedInstructionLaw c.1) inferInstance b q hq H g r 1
    hH hHb (fun _ => Measurable.of_discrete) (fun j x => abs_orientedRouteDisc_le hd _ _ x)
    (fun j => integral_orientedRouteDisc hd _ _) hr zero_lt_one
  have hsum (z : (Site d → ℤ) × (Site d × ℕ → Site d)) :
      (∑ j : Fin T.card, H j z * g j (z.2 (q j))) = orientedTruncatedRoute S m l M z := by
    have he (j : Fin T.card) : H j z * g j (z.2 (q j)) =
        if (q j).2 < orientedOdometer z.1 z.2 (m (q j).1) (q j).1 then
          orientedRouteDisc (l (q j).1) (q j).1 (z.2 (q j)) else 0 := by
      dsimp only [H, g]
      split_ifs <;> simp
    simp only [he]
    rw [sum_enumeration T q hq hcov (fun c => if c.2 < orientedOdometer z.1 z.2 (m c.1) c.1 then
      orientedRouteDisc (l c.1) c.1 (z.2 c) else 0), sum_product]
    rfl
  have hsq (z : (Site d → ℤ) × (Site d × ℕ → Site d)) :
      (∑ j : Fin T.card, H j z ^ 2 * ∫ x, g j x ^ 2 ∂(orientedInstructionLaw (q j).1)) =
        orientedTruncatedCharge S m l M z := by
    have he (j : Fin T.card) : H j z ^ 2 * (∫ x, g j x ^ 2 ∂(orientedInstructionLaw (q j).1)) =
        (if (q j).2 < orientedOdometer z.1 z.2 (m (q j).1) (q j).1 then (1 : ℝ) else 0) *
          orientedCharge d (l (q j).1) (q j).1 := by
      dsimp only [H, g]
      rw [integral_orientedRouteDisc_sq]
      split_ifs <;> norm_num
    simp only [he]
    rw [sum_enumeration T q hq hcov (fun c =>
      (if c.2 < orientedOdometer z.1 z.2 (m c.1) c.1 then (1 : ℝ) else 0) *
        orientedCharge d (l c.1) c.1), sum_product]
    apply sum_congr rfl
    intro y _
    dsimp only
    rw [← sum_mul, sum_range_lt_indicator]
  simpa only [hsum, hsq, mul_one, orientedStackLaw] using h

end Parking
