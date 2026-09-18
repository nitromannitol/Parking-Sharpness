import Parking.Support.SpatialDifferenceTests
import Parking.Generic.TimeAverage
import Parking.Generic.LocalTimeIntegration
import Parking.Generic.MeasurableTimeDerivative

/-! Smooth time derivatives obtained by averaging the homogeneous time increments. -/

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ} (hregular : External.HeatInteriorRegularity)
    {Ω : Type*} (ω : Ω) (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ)
    (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hcont : Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (hzero : ∀ x, Uc ω 0 x = 0)
    (hmono : ∀ x, Monotone fun s => Uc ω s x)
    (hpde : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
      -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
        = (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * contOp d (fun x => ψ (p.1, x)) p.2)
          + W (fun x => ∫ s : ℝ, ψ (s, x)) ω)

include hcont hmono hpde in
/-- Averaging forward increments preserves their homogeneous weak heat
equation. Compact support and continuity justify both changes of integration order. -/
theorem weak_heat_averageIncrement_of_hpde
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ)
    (hsupp : tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2}) :
    -∫ p : ℝ × (Fin d → ℝ),
        Generic.TimeAverage.averageIncrement (fun q => Uc ω q.1 q.2) p *
          deriv (fun s => ψ (s, p.2)) p.1
      = ∫ p : ℝ × (Fin d → ℝ),
        Generic.TimeAverage.averageIncrement (fun q => Uc ω q.1 q.2) p *
          contOp d (fun x => ψ (p.1, x)) p.2 := by
  simp_rw [deriv_timeSlice (hψ.1.differentiable (by simp))]
  rw [Generic.TimeAverage.integral_averageIncrement_mul hcont (timeDeriv ψ)
      (contDiff_timeDeriv hψ.1).continuous (hasCompactSupport_timeDeriv hψ.2.1),
    Generic.TimeAverage.integral_averageIncrement_mul hcont _
      (contDiff_spaceTime_contOp hψ.1).continuous (hasCompactSupport_spaceTime_contOp hψ),
    ← integral_neg]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  by_cases hz : r = 0
  · simp [hz]
  have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hz)
  have heq := weak_heat_forwardDifference_of_hpde ω W Uc hcont hmono hpde hrpos hψ hsupp
  simp_rw [div_mul_eq_mul_div, deriv_timeSlice (hψ.1.differentiable (by simp))] at heq
  rw [integral_div, integral_div, ← neg_div] at heq
  exact (div_left_inj' hz).mp heq

include hregular hcont hzero hmono hpde in
/-- The average of the forward increments is a continuous weak heat solution,
so the corrected interior regularity input makes it smooth on the positive set. -/
theorem contDiffOn_averageIncrement_of_hpde :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (Generic.TimeAverage.averageIncrement (fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2))
      {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} := by
  obtain ⟨v, hv, heq, _⟩ := hregular d {p | 0 < Uc ω p.1 p.2}
    (isOpen_lt continuous_const hcont)
    (Generic.BackwardPositivity.positive_set_subset_positive_time hzero hmono)
    (Generic.TimeAverage.averageIncrement (fun p => Uc ω p.1 p.2))
    (Generic.TimeAverage.continuous_averageIncrement hcont)
    (fun ψ hψ hsupp => weak_heat_averageIncrement_of_hpde ω W Uc hcont hmono hpde hψ hsupp)
  exact hv.congr heq

include hregular hcont hzero hmono hpde in
/-- The continuum value has a smooth classical time derivative on its positive
set. The regularity input is applied only to continuous increments and their
continuous average; the derivative is then recovered by elementary calculus. -/
theorem exists_smooth_time_derivative_of_hpde :
    ∃ v : ℝ × (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} ∧
      ∀ p : ℝ × (Fin d → ℝ), 0 < Uc ω p.1 p.2 →
        HasDerivAt (fun s => Uc ω s p.2) (v p) p.1 := by
  have hD := (contDiffOn_forwardDifference_of_hpde hregular ω W Uc hcont hzero hmono hpde
    (h := 1) zero_lt_one).1
  simp only [div_one] at hD
  exact Generic.TimeAverage.exists_smooth_time_derivative hcont
    (isOpen_lt continuous_const hcont) hD
    (contDiffOn_averageIncrement_of_hpde hregular ω W Uc hcont hzero hmono hpde)

omit hregular ω W Uc hcont hzero hmono hpde in
/-- The smooth time derivative is a measurable field on the original sample
space and represents the distributional derivative against every admissible
test. Time monotonicity makes this representative nonnegative. -/
theorem exists_measurable_time_derivative_of_hpde
    (hregular : External.HeatInteriorRegularity)
    (Ω : Type*) [MeasurableSpace Ω] (Q : Measure Ω)
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ)
    (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hmeas : ∀ s x, Measurable fun ω => Uc ω s x)
    (hcont : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (hzero : ∀ ω x, Uc ω 0 x = 0)
    (hmono : ∀ ω x, Monotone fun s => Uc ω s x)
    (hpde : ∀ᵐ ω ∂Q, ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
      -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
        = (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * contOp d (fun x => ψ (p.1, x)) p.2)
          + W (fun x => ∫ s : ℝ, ψ (s, x)) ω) :
    ∃ v : Ω → ℝ → (Fin d → ℝ) → ℝ,
      (∀ s x, Measurable fun ω => v ω s x) ∧
      ∀ᵐ ω ∂Q,
        ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => v ω p.1 p.2)
          {p | 0 < Uc ω p.1 p.2} ∧
        (∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
          tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
          -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
            = ∫ p : ℝ × (Fin d → ℝ), v ω p.1 p.2 * ψ p) ∧
        (∀ s x, 0 < Uc ω s x → HasDerivAt (fun t => Uc ω t x) (v ω s x) s) ∧
        (∀ s x, 0 < Uc ω s x → 0 ≤ v ω s x) := by
  let v : Ω → ℝ → (Fin d → ℝ) → ℝ :=
    fun ω s x => Generic.MeasurableTimeDerivative.value (fun t => Uc ω t x) s
  refine ⟨v, fun s x => Generic.MeasurableTimeDerivative.measurable_value
    (fun t => hmeas t x) s, ?_⟩
  filter_upwards [hpde] with ω hpdeω
  obtain ⟨w, hsmooth, hderiv⟩ := exists_smooth_time_derivative_of_hpde hregular ω W Uc
    (hcont ω) (hzero ω) (hmono ω) hpdeω
  have heq : ∀ p : ℝ × (Fin d → ℝ), 0 < Uc ω p.1 p.2 → v ω p.1 p.2 = w p :=
    fun p hp => Generic.MeasurableTimeDerivative.value_eq (hderiv p hp)
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => v ω p.1 p.2)
      {p | 0 < Uc ω p.1 p.2} := hsmooth.congr heq
  have hd : ∀ s x, 0 < Uc ω s x → HasDerivAt (fun t => Uc ω t x) (v ω s x) s := by
    intro s x hs
    rw [heq (s, x) hs]
    exact hderiv (s, x) hs
  refine ⟨hv, ?_, hd, fun s x hs => (hd s x hs).nonneg_of_monotone (hmono ω x)⟩
  intro ψ hψ hsupp
  exact Generic.LocalTimeIntegration.integral_timeDerivative (hcont ω) hv.continuousOn
    (isOpen_lt continuous_const (hcont ω)) (fun p hp => hd p.1 p.2 hp)
    hψ.1 hψ.2.1 hsupp

end Parking

end
