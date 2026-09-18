/- Removing the stack cutoff in the directed routing martingale estimate. -/
import Parking.Support.OrientedChargeMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem exists_oriented_finite_route_moment (hBern : External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (ν : Measure ℤ), CriticalLaw ν →
      ∀ (S : Finset (Site d)) (m l : Site d → ℕ) (n : ℕ), (∀ y ∈ S, m y ≤ n) →
      ∀ r : ℝ, 2 ≤ r →
      (∫ z, |orientedFiniteRoute S m l z| ^ r ∂((iidLaw d ν).prod (orientedStackLaw d))) ^ (1 / r) ≤
        C * (Real.sqrt r * (∫ ω : Data d, (U ω n 0 : ℝ) ^ (r / 2)
          ∂(orientedLaw d ν)) ^ (1 / r) + r) := by
  obtain ⟨C, hC, hb⟩ := exists_oriented_truncated_route_moment hBern
  refine ⟨C, hC, fun d hd ν hν S m l n hm r hr => ?_⟩
  haveI := hν.prob
  let Q := (iidLaw d ν).prod (orientedStackLaw d)
  let B := C * (Real.sqrt r * (∫ ω : Data d, (U ω n 0 : ℝ) ^ (r / 2)
    ∂(orientedLaw d ν)) ^ (1 / r) + r)
  have hr0 : 0 < r := by linarith
  have hB0 : 0 ≤ B := by
    apply mul_nonneg hC.le
    exact add_nonneg (mul_nonneg (Real.sqrt_nonneg r) (Real.rpow_nonneg
      (integral_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) _)) hr0.le
  have hnorm (M : ℕ) : (∫ z, |orientedTruncatedRoute S m l M z| ^ r ∂Q) ^ (1 / r) ≤ B := by
    have h := hb d hd ν inferInstance S m l M r hr
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg r)
    exact Real.rpow_le_rpow
      (integral_nonneg fun z => Real.rpow_nonneg (orientedTruncatedCharge_nonneg S m l M z) _)
      (integral_orientedTruncatedCharge_rpow_le hd ν hν S m l M n hm (by linarith))
      (by positivity)
  have hbound (M : ℕ) : (∫ z, |orientedTruncatedRoute S m l M z| ^ r ∂Q) ≤ B ^ r := by
    have h := Real.rpow_le_rpow
      (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) r) _)
      (hnorm M) hr0.le
    rwa [← Real.rpow_mul (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) r),
      one_div, inv_mul_cancel₀ hr0.ne', Real.rpow_one] at h
  have hiF : Integrable (fun z => |orientedFiniteRoute S m l z| ^ r) Q :=
    integrable_oriented_route_rpow_of_bound hd ν hν S m n hm _ (measurable_orientedFiniteRoute S m l)
      (abs_orientedFiniteRoute_le hd S m l) (by linarith)
  have hiT (M : ℕ) : Integrable (fun z => |orientedTruncatedRoute S m l M z| ^ r) Q :=
    integrable_oriented_route_rpow_of_bound hd ν hν S m n hm _ (measurable_orientedTruncatedRoute S m l M)
      (abs_orientedTruncatedRoute_le hd S m l M) (by linarith)
  have hconv : ∀ᵐ z ∂Q, Filter.Tendsto (fun M => |orientedTruncatedRoute S m l M z| ^ r)
      Filter.atTop (nhds (|orientedFiniteRoute S m l z| ^ r)) := by
    filter_upwards [] with z
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [orientedTruncatedRoute_eventually_eq S m l z] with M hM
    rw [hM]
  have hI := integral_le_of_tendsto (fun _ _ => Real.rpow_nonneg (abs_nonneg _) r) hiF
    (fun _ => Real.rpow_nonneg (abs_nonneg _) r) hconv hiT hbound
  have h := Real.rpow_le_rpow (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) r)
    hI (by positivity : 0 ≤ 1 / r)
  rwa [← Real.rpow_mul hB0, mul_one_div, div_self hr0.ne', Real.rpow_one] at h

/-- The moment bound of `exists_oriented_finite_route_moment` in the shape the
unrolled error of `parking.tex:3240-3250` needs: the finite route sum of one
round, with the departure stacks truncated at the box of radius `n + 1`. -/
theorem exists_oriented_finiteRoute_moment_le (hBern : External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (ν : Measure ℤ), CriticalLaw ν →
      ∀ n k : ℕ, k ≤ n → ∀ r : ℝ, 2 ≤ r →
      (∫ z, |orientedFiniteRoute (boxFinset (0 : Site d) (n + 1))
          (fun _ => k) (fun _ => n - (k + 1)) z| ^ r
        ∂((iidLaw d ν).prod (orientedStackLaw d))) ^ (1 / r) ≤
        C * (Real.sqrt r * (∫ ω : Data d, (U ω n 0 : ℝ) ^ (r / 2)
          ∂(orientedLaw d ν)) ^ (1 / r) + r) := by
  obtain ⟨C, hC, hb⟩ := Parking.exists_oriented_finite_route_moment hBern
  exact ⟨C, hC, fun d hd ν hν n k hk r hr =>
    hb d hd ν hν (boxFinset (0 : Site d) (n + 1)) (fun _ => k) (fun _ => n - (k + 1)) n
      (fun y _ => hk) r hr⟩

end Parking
