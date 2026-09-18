/- The moment recursion for the directed particle odometer.

The pathwise comparison and the two displays of the directed moment estimate give
a self-referential bound on the `r`-th moment of the directed particle odometer at
the origin, in terms of the same moment of the divisible odometer.  Steps 2 and 4
of the proof of `thm:oriented-walk` (`parking.tex:3279-3342`) solve it by Young's
inequality.
-/
import Parking.Support.OrientedWStarMoment
import Parking.Support.OrientedDivisibleIntegrable
import Parking.Support.OrientedInstructionFull
import Parking.Support.OrientedError
import Parking.Support.UpperStep
import Parking.Support.OrientedMoments
import Parking.Support.NearTailSum

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem integrable_oriented_U_rpow_of_critical (hd : 1 ≤ d) (ν : Measure ℤ)
    (hν : CriticalLaw ν) {r : ℝ} (hr : 1 ≤ r) (n : ℕ) (x : Site d) :
    Integrable (fun ω : Data d => (U ω n x : ℝ) ^ r) (orientedLaw d ν) := by
  haveI := hν.prob
  obtain ⟨θ, hθ, hexp⟩ := hν.expMoment
  exact integrable_oriented_U_rpow hd ν hθ (integrable_expMax_of_expAbs hθ hexp) hr n x

/-- Cauchy-Schwarz on the probability space: the `r/2` moment at an earlier round
is at most the square root of the `r`-th moment at the later round. -/
theorem oriented_half_moment_le (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    {r : ℝ} (hr : 2 ≤ r) {m n : ℕ} (hmn : m ≤ n) :
    (∫ ω : Data d, (U ω m 0 : ℝ) ^ (r / 2) ∂(orientedLaw d ν)) ^ (1 / r)
      ≤ ((∫ ω : Data d, (U ω n 0 : ℝ) ^ r ∂(orientedLaw d ν)) ^ (1 / r)) ^ ((1 : ℝ) / 2) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (orientedLaw d ν) := orientedLaw_isProbability hd ν
  have hr0 : (0 : ℝ) < r := by linarith
  have hhalf : (1 : ℝ) ≤ r / 2 := by linarith
  have hIm : Integrable (fun ω : Data d => (U ω m 0 : ℝ) ^ (r / 2)) (orientedLaw d ν) :=
    integrable_oriented_U_rpow_of_critical hd ν hν hhalf m 0
  have hIn : Integrable (fun ω : Data d => (U ω n 0 : ℝ) ^ (r / 2)) (orientedLaw d ν) :=
    integrable_oriented_U_rpow_of_critical hd ν hν hhalf n 0
  have hIsq : Integrable (fun ω : Data d => ((U ω n 0 : ℝ) ^ (r / 2)) ^ (2 : ℕ))
      (orientedLaw d ν) := by
    refine (integrable_oriented_U_rpow_of_critical hd ν hν (by linarith) n 0).congr ?_
    filter_upwards [] with ω
    rw [rpow_sq (Nat.cast_nonneg _)]
    congr 1
    ring
  -- monotonicity in the round
  have hmono : (∫ ω : Data d, (U ω m 0 : ℝ) ^ (r / 2) ∂(orientedLaw d ν))
      ≤ ∫ ω : Data d, (U ω n 0 : ℝ) ^ (r / 2) ∂(orientedLaw d ν) := by
    refine integral_mono hIm hIn fun ω => ?_
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast U_mono_time ω 0 hmn) (by linarith)
  -- Cauchy-Schwarz
  have hcs : (∫ ω : Data d, (U ω n 0 : ℝ) ^ (r / 2) ∂(orientedLaw d ν)) ^ (2 : ℕ)
      ≤ ∫ ω : Data d, (U ω n 0 : ℝ) ^ r ∂(orientedLaw d ν) := by
    have h := sq_integral_le_integral_sq (orientedLaw d ν)
      (fun ω => (U ω n 0 : ℝ) ^ (r / 2)) hIn hIsq
    refine h.trans (le_of_eq (integral_congr_ae ?_))
    filter_upwards [] with ω
    rw [rpow_sq (Nat.cast_nonneg _)]
    congr 1
    ring
  set Im : ℝ := ∫ ω : Data d, (U ω m 0 : ℝ) ^ (r / 2) ∂(orientedLaw d ν) with hImdef
  set In : ℝ := ∫ ω : Data d, (U ω n 0 : ℝ) ^ r ∂(orientedLaw d ν) with hIndef
  set Jn : ℝ := ∫ ω : Data d, (U ω n 0 : ℝ) ^ (r / 2) ∂(orientedLaw d ν) with hJndef
  have hIm0 : 0 ≤ Im := integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hJn0 : 0 ≤ Jn := integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hIn0 : 0 ≤ In := integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hstep : Im ≤ In ^ ((1 : ℝ) / 2) := by
    have h1 : Jn ^ (2 : ℕ) ≤ In := hcs
    have h2 : Jn ≤ In ^ ((1 : ℝ) / 2) := by
      nlinarith [Real.sq_sqrt hIn0, Real.sqrt_nonneg In,
        Real.rpow_natCast (In ^ ((1 : ℝ) / 2)) 2,
        Real.rpow_natCast Jn 2,
        (by rw [← Real.rpow_natCast (In ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hIn0]; norm_num :
          (In ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = In),
        Real.rpow_nonneg hIn0 ((1 : ℝ) / 2)]
    linarith [hmono]
  calc Im ^ (1 / r) ≤ (In ^ ((1 : ℝ) / 2)) ^ (1 / r) :=
        Real.rpow_le_rpow hIm0 hstep (by positivity)
    _ = (In ^ (1 / r)) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_mul hIn0, ← Real.rpow_mul hIn0]; ring_nf
/-- **The moment recursion for the directed particle odometer.**  The pathwise
comparison, the second display of the directed moment estimate and the first
display of Step 1 give a self-referential bound on the `r`-th moment of the
directed particle odometer at the origin. -/
theorem exists_oriented_U_moment_recursion (hBern : External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 2 ≤ d → ∀ (ν : Measure ℤ), CriticalLaw ν →
      ∀ (n : ℕ) (r : ℝ), 2 ≤ r →
      (∫ ω : Data d, (U ω n 0 : ℝ) ^ r ∂(orientedLaw d ν)) ^ (1 / r)
        ≤ (∫ ω : Data d, |uOriented (confReal ω) n 0| ^ r ∂(orientedLaw d ν)) ^ (1 / r)
          + C * ((n : ℝ) + 1) ^ (1 / r) *
            (Real.sqrt r * ((∫ ω : Data d, (U ω n 0 : ℝ) ^ r ∂(orientedLaw d ν)) ^ (1 / r))
              ^ ((1 : ℝ) / 2) + r) := by
  obtain ⟨C, hC, hb⟩ := exists_oriented_wErr_moment_law hBern
  refine ⟨2 * C, by positivity, fun d hd2 ν hν n r hr => ?_⟩
  have hd : 1 ≤ d := by omega
  haveI := hν.prob
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : (1 : ℝ) ≤ r := by linarith
  set A : ℝ := (∫ ω : Data d, (U ω n 0 : ℝ) ^ r ∂(orientedLaw d ν)) ^ (1 / r) with hAdef
  have hA0 : 0 ≤ A :=
    Real.rpow_nonneg (integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) r) _
  set B : ℝ := C * (Real.sqrt r * A ^ ((1 : ℝ) / 2) + r) with hBdef
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Real.sqrt r * A ^ ((1 : ℝ) / 2) :=
      mul_nonneg (Real.sqrt_nonneg r) (Real.rpow_nonneg hA0 _)
    have : 0 ≤ Real.sqrt r * A ^ ((1 : ℝ) / 2) + r := by linarith
    exact mul_nonneg hC.le this
  -- every round up to `n` obeys the first display with the same right-hand side
  have hb' : ∀ m ≤ n,
      (∫ ω : Data d, |wErrOriented ω.1 ω.2.1 m 0| ^ r ∂(orientedLaw d ν)) ^ (1 / r) ≤ B := by
    intro m hm
    refine (hb d hd2 ν hν m r hr).trans ?_
    have hhalf := oriented_half_moment_le hd ν hν hr (m := m - 1) (n := n) (by omega)
    have := mul_le_mul_of_nonneg_left hhalf (Real.sqrt_nonneg r)
    exact mul_le_mul_of_nonneg_left (by linarith) hC.le
  -- the second display
  have hstar := wStarOriented_moment_le hd ν hν hr1 n B hB0 hb'
  -- the three integrabilities of Minkowski
  have hUabs : (fun ω : Data d => |(U ω n 0 : ℝ)| ^ r) = fun ω : Data d => (U ω n 0 : ℝ) ^ r := by
    funext ω; rw [abs_of_nonneg (Nat.cast_nonneg _)]
  have hWabs : (fun ω : Data d => |wStarOriented ω.1 ω.2.1 n 0| ^ r)
      = fun ω : Data d => wStarOriented ω.1 ω.2.1 n 0 ^ r := by
    funext ω; rw [abs_of_nonneg (wStarOriented_nonneg _ _ n 0)]
  have hIU : Integrable (fun ω : Data d => |(U ω n 0 : ℝ)| ^ r) (orientedLaw d ν) := by
    rw [hUabs]; exact integrable_oriented_U_rpow_of_critical hd ν hν hr1 n 0
  have hIu : Integrable (fun ω : Data d => |uOriented (confReal ω) n 0| ^ r)
      (orientedLaw d ν) := integrable_oriented_uOriented_rpow hd ν hν hr1 n 0
  have hIw : Integrable (fun ω : Data d => |wStarOriented ω.1 ω.2.1 n 0| ^ r)
      (orientedLaw d ν) := by
    rw [hWabs]; exact integrable_wStarOriented_rpow hd ν hν hr1 n
  have hdiff : ∀ᵐ ω ∂(orientedLaw d ν),
      |(U ω n 0 : ℝ) - uOriented (confReal ω) n 0|
        ≤ |2 * wStarOriented ω.1 ω.2.1 n 0| := by
    filter_upwards [orientedOdometer_ae_eq_U hd ν n 0] with ω hω
    have h := abs_orientedOdometer_sub_u_le hd ω.1 ω.2.1 n 0
    rw [hω] at h
    rw [abs_of_nonneg (by linarith [wStarOriented_nonneg ω.1 ω.2.1 n 0] :
      (0:ℝ) ≤ 2 * wStarOriented ω.1 ω.2.1 n 0)]
    exact h
  have hIdiff : Integrable (fun ω : Data d =>
      |(U ω n 0 : ℝ) - uOriented (confReal ω) n 0| ^ r) (orientedLaw d ν) := by
    refine (hIw.const_mul ((2 : ℝ) ^ r)).mono'
      ((((measurable_from_countable' fun m : ℕ => (m : ℝ)).comp (measurable_U n 0)).sub
        ((measurable_uOriented n 0).comp measurable_confReal)).abs.pow_const r).aestronglyMeasurable
      ?_
    filter_upwards [hdiff] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r)]
    have h1 : |(U ω n 0 : ℝ) - uOriented (confReal ω) n 0| ^ r
        ≤ |2 * wStarOriented ω.1 ω.2.1 n 0| ^ r :=
      Real.rpow_le_rpow (abs_nonneg _) hω hr0.le
    refine h1.trans (le_of_eq ?_)
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)),
      Real.mul_rpow (by norm_num) (abs_nonneg _)]
  -- Minkowski
  have hmink := rNorm_add_le (orientedLaw d ν) hr1
    (f := fun ω : Data d => (U ω n 0 : ℝ) - uOriented (confReal ω) n 0)
    (g := fun ω : Data d => uOriented (confReal ω) n 0)
    ((((measurable_from_countable' fun m : ℕ => (m : ℝ)).comp (measurable_U n 0)).sub
      ((measurable_uOriented n 0).comp measurable_confReal)).aestronglyMeasurable)
    (((measurable_uOriented n 0).comp measurable_confReal).aestronglyMeasurable)
    hIdiff hIu (by
      refine hIU.congr ?_
      filter_upwards [] with ω
      rw [sub_add_cancel])
  have hsum : rNorm (orientedLaw d ν) r
      (fun ω : Data d => ((U ω n 0 : ℝ) - uOriented (confReal ω) n 0)
        + uOriented (confReal ω) n 0) = A := by
    rw [rNorm, hAdef]
    congr 2
    funext ω
    congr 1
    rw [sub_add_cancel, abs_of_nonneg (Nat.cast_nonneg _)]
  have hdiffN : rNorm (orientedLaw d ν) r
      (fun ω : Data d => (U ω n 0 : ℝ) - uOriented (confReal ω) n 0)
      ≤ 2 * ((∫ ω : Data d, wStarOriented ω.1 ω.2.1 n 0 ^ r ∂(orientedLaw d ν)) ^ (1 / r)) := by
    have h1 := rNorm_mono (orientedLaw d ν) hr0 hdiff (by
      simpa only [hWabs] using (hIw.const_mul ((2:ℝ) ^ r)).congr (by
        filter_upwards [] with ω
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)),
          Real.mul_rpow (by norm_num) (abs_nonneg _)]))
    refine h1.trans (le_of_eq ?_)
    rw [rNorm_const_mul (orientedLaw d ν) hr0 (by norm_num : (0:ℝ) ≤ (2:ℝ)), rNorm, hWabs]
  have hstarN : rNorm (orientedLaw d ν) r (fun ω : Data d => uOriented (confReal ω) n 0)
      = (∫ ω : Data d, |uOriented (confReal ω) n 0| ^ r ∂(orientedLaw d ν)) ^ (1 / r) := rfl
  rw [hsum, hstarN] at hmink
  have hfinal : 2 * ((∫ ω : Data d, wStarOriented ω.1 ω.2.1 n 0 ^ r ∂(orientedLaw d ν)) ^ (1 / r))
      ≤ 2 * C * ((n : ℝ) + 1) ^ (1 / r) * (Real.sqrt r * A ^ ((1 : ℝ) / 2) + r) := by
    have := mul_le_mul_of_nonneg_left hstar (by norm_num : (0:ℝ) ≤ (2:ℝ))
    calc 2 * ((∫ ω : Data d, wStarOriented ω.1 ω.2.1 n 0 ^ r ∂(orientedLaw d ν)) ^ (1 / r))
        ≤ 2 * (((n : ℝ) + 1) ^ (1 / r) * B) := this
      _ = 2 * C * ((n : ℝ) + 1) ^ (1 / r) * (Real.sqrt r * A ^ ((1 : ℝ) / 2) + r) := by
          rw [hBdef]; ring
  linarith [hmink, hdiffN, hfinal]

end Parking
end
