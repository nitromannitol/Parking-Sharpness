import Parking.Support.SpatialTimeDerivative
import Parking.Support.SpaceTimeContOp
import Parking.Generic.TimeTranslationPairing
import Parking.Generic.BackwardPositivity
import Parking.External.HeatInteriorRegularity
import Mathlib.MeasureTheory.Group.Integral

/-! Backward differences of test functions for the time-difference argument. -/

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

/-- Translating a test forward in time preserves positive-time support. -/
theorem isSpaceTimeTest_translate {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : IsSpaceTimeTest ψ) {h : ℝ} (hh : 0 ≤ h) :
    IsSpaceTimeTest (fun p : ℝ × (Fin d → ℝ) => ψ (p.1 - h, p.2)) := by
  have hcomp : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin d → ℝ) => (p.1 - h, p.2)) :=
    (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
  have hcompact : HasCompactSupport (fun p : ℝ × (Fin d → ℝ) => ψ (p.1 - h, p.2)) := by
    simpa [Function.comp_def, sub_eq_add_neg, Prod.add_def] using
      hψ.2.1.comp_homeomorph (Homeomorph.addRight ((-h, 0) : ℝ × (Fin d → ℝ)))
  refine ⟨hψ.1.comp hcomp, hcompact, ?_⟩
  intro p hp
  have hmem := tsupport_comp_subset_preimage ψ hcomp.continuous hp
  have := hψ.2.2 (p.1 - h, p.2) hmem
  linarith

/-- The backward finite difference of an arbitrary test is again a test. -/
theorem isSpaceTimeTest_backwardDifference {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : IsSpaceTimeTest ψ) {h : ℝ} (hh : 0 ≤ h) :
    IsSpaceTimeTest (fun p : ℝ × (Fin d → ℝ) => ψ (p.1 - h, p.2) - ψ p) := by
  have ht := isSpaceTimeTest_translate hψ hh
  refine ⟨ht.1.sub hψ.1, ht.2.1.sub hψ.2.1, ?_⟩
  intro p hp
  rcases tsupport_sub _ _ hp with hp | hp
  · exact ht.2.2 p hp
  · exact hψ.2.2 p hp

/-- Monotonicity ensures that both parts of the backward difference remain
supported where the continuum value is positive. -/
theorem backwardDifference_supported_on_positive_set
    {u : ℝ → (Fin d → ℝ) → ℝ} (hmono : ∀ x, Monotone fun s => u s x)
    {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hsupp : tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < u p.1 p.2})
    {h : ℝ} (hh : 0 ≤ h) :
    tsupport (fun p : ℝ × (Fin d → ℝ) => ψ (p.1 - h, p.2) - ψ p) ⊆
      {p : ℝ × (Fin d → ℝ) | 0 < u p.1 p.2} := by
  intro p hp
  rcases tsupport_sub _ _ hp with hp | hp
  · have hmem := tsupport_comp_subset_preimage ψ
      ((continuous_fst.sub continuous_const).prodMk continuous_snd) hp
    exact lt_of_lt_of_le (hsupp hmem) (hmono p.2 (sub_le_self _ hh))
  · exact hsupp hp

/-- The total time integral of the backward difference vanishes, for every
spatial point and every test function. -/
theorem integral_backwardDifference_eq_zero {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : IsSpaceTimeTest ψ) (h : ℝ) (x : Fin d → ℝ) :
    (∫ s : ℝ, ψ (s - h, x) - ψ (s, x)) = 0 := by
  have hc : Continuous (fun s : ℝ => ψ (s, x)) := (contDiff_timeSlice hψ.1 x).continuous
  have hs : HasCompactSupport (fun s : ℝ => ψ (s, x)) :=
    hasCompactSupport_timeSlice hψ.2.1 x
  have hc' : Continuous (fun s : ℝ => ψ (s - h, x)) :=
    hc.comp (continuous_id.sub continuous_const)
  have hs' : HasCompactSupport (fun s : ℝ => ψ (s - h, x)) := by
    simpa [Function.comp_def, sub_eq_add_neg] using hs.comp_homeomorph (Homeomorph.addRight (-h))
  rw [integral_sub (hc'.integrable_of_hasCompactSupport hs')
    (hc.integrable_of_hasCompactSupport hs)]
  rw [integral_sub_right_eq_self (fun s : ℝ => ψ (s, x)) h, sub_self]

/-- Testing the driven equation against the backward difference of any test
removes its time-independent source. This identity precedes the change of
variables which transfers the difference from the test to the field. -/
theorem homogeneous_backwardDifference_of_hpde
    {Ω : Type*} (ω : Ω) (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ)
    (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hmono : ∀ x, Monotone fun s => Uc ω s x)
    (hpde : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
      -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
        = (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * contOp d (fun x => ψ (p.1, x)) p.2)
          + W (fun x => ∫ s : ℝ, ψ (s, x)) ω)
    (hWzero : W (fun _ => (0 : ℝ)) ω = 0)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ)
    (hsupp : tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2})
    {h : ℝ} (hh : 0 ≤ h) :
    -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 *
        deriv (fun s => ψ (s - h, p.2) - ψ (s, p.2)) p.1
      = ∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 *
        contOp d (fun x => ψ (p.1 - h, x) - ψ (p.1, x)) p.2 := by
  have heq := hpde (fun p => ψ (p.1 - h, p.2) - ψ p)
    (isSpaceTimeTest_backwardDifference hψ hh)
    (backwardDifference_supported_on_positive_set hmono hsupp hh)
  have hzero : (fun x => ∫ s : ℝ, ψ (s - h, x) - ψ (s, x)) = fun _ => (0 : ℝ) :=
    funext (integral_backwardDifference_eq_zero hψ h)
  rwa [hzero, hWzero, add_zero] at heq

/-- Every positive forward difference quotient solves the homogeneous heat
equation weakly against every test supported in the positive set. Both uses of
the driven equation retain the same sample, field, and time-independent source. -/
theorem weak_heat_forwardDifference_of_hpde
    {Ω : Type*} (ω : Ω) (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ)
    (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hcont : Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (hmono : ∀ x, Monotone fun s => Uc ω s x)
    (hpde : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
      -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
        = (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * contOp d (fun x => ψ (p.1, x)) p.2)
          + W (fun x => ∫ s : ℝ, ψ (s, x)) ω)
    {h : ℝ} (hh : 0 < h)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ)
    (hsupp : tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2}) :
    -∫ p : ℝ × (Fin d → ℝ), ((Uc ω (p.1 + h) p.2 - Uc ω p.1 p.2) / h) *
        deriv (fun s => ψ (s, p.2)) p.1
      = ∫ p : ℝ × (Fin d → ℝ), ((Uc ω (p.1 + h) p.2 - Uc ω p.1 p.2) / h) *
        contOp d (fun x => ψ (p.1, x)) p.2 := by
  have htest := isSpaceTimeTest_translate hψ hh.le
  have hsupport : tsupport (fun p : ℝ × (Fin d → ℝ) => ψ (p.1 - h, p.2)) ⊆
      {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} := by
    intro p hp
    have hm := tsupport_comp_subset_preimage ψ
      ((continuous_fst.sub continuous_const).prodMk continuous_snd) hp
    exact lt_of_lt_of_le (hsupp hm) (hmono p.2 (sub_le_self _ hh.le))
  have hshift := hpde (fun p => ψ (p.1 - h, p.2)) htest hsupport
  have hderiv (t : ℝ) (x : Fin d → ℝ) :
      deriv (fun s => ψ (s - h, x)) t = deriv (fun s => ψ (s, x)) (t - h) := by
    simpa [Function.comp_def] using (((contDiff_timeSlice hψ.1 x).differentiable (by simp) (t - h)).hasDerivAt.comp t
      ((hasDerivAt_id t).sub_const h)).deriv
  simp_rw [hderiv] at hshift
  have hnoise : (fun x => ∫ s : ℝ, ψ (s - h, x)) = fun x => ∫ s : ℝ, ψ (s, x) := by
    funext x
    exact integral_sub_right_eq_self (fun s : ℝ => ψ (s, x)) h
  rw [hnoise] at hshift
  have ht := Generic.TimeTranslationPairing.integral_translate_pairing
    (fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (fun p : ℝ × (Fin d → ℝ) => deriv (fun s => ψ (s, p.2)) p.1) h
  have hx := Generic.TimeTranslationPairing.integral_translate_pairing
    (fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (fun p : ℝ × (Fin d → ℝ) => contOp d (fun x => ψ (p.1, x)) p.2) h
  change (∫ p : ℝ × (Fin d → ℝ), Uc ω (p.1 + h) p.2 * deriv (fun s => ψ (s, p.2)) p.1) = _ at ht
  change (∫ p : ℝ × (Fin d → ℝ), Uc ω (p.1 + h) p.2 * contOp d (fun x => ψ (p.1, x)) p.2) = _ at hx
  rw [← ht, ← hx] at hshift
  have hplus : Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω (p.1 + h) p.2 :=
    hcont.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  have hbase := hpde ψ hψ hsupp
  have hdiff :
      -∫ p : ℝ × (Fin d → ℝ), (Uc ω (p.1 + h) p.2 - Uc ω p.1 p.2) *
          deriv (fun s => ψ (s, p.2)) p.1
        = ∫ p : ℝ × (Fin d → ℝ), (Uc ω (p.1 + h) p.2 - Uc ω p.1 p.2) *
          contOp d (fun x => ψ (p.1, x)) p.2 := by
    simp_rw [sub_mul]
    rw [integral_sub (integrable_mul_timeSlice_deriv hplus hψ)
        (integrable_mul_timeSlice_deriv hcont hψ),
      integral_sub (integrable_mul_spaceTime_contOp hplus hψ)
        (integrable_mul_spaceTime_contOp hcont hψ)]
    linarith
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div, integral_div, ← neg_div, hdiff]

/-- The corrected interior regularity input applies to every positive forward
time difference quotient. Its positive-domain hypothesis follows from the
initial condition and monotonicity of the same continuum field. -/
theorem contDiffOn_forwardDifference_of_hpde
    (hregular : External.HeatInteriorRegularity)
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
    {h : ℝ} (hh : 0 < h) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) =>
      (Uc ω (p.1 + h) p.2 - Uc ω p.1 p.2) / h) {p | 0 < Uc ω p.1 p.2} ∧
    ∀ p : ℝ × (Fin d → ℝ), 0 ≤ (Uc ω (p.1 + h) p.2 - Uc ω p.1 p.2) / h := by
  have hquot : Continuous (fun p : ℝ × (Fin d → ℝ) =>
      (Uc ω (p.1 + h) p.2 - Uc ω p.1 p.2) / h) :=
    ((hcont.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)).sub hcont).div_const h
  obtain ⟨v, hv, heq, _⟩ := hregular d {p | 0 < Uc ω p.1 p.2}
    (isOpen_lt continuous_const hcont)
    (Generic.BackwardPositivity.positive_set_subset_positive_time hzero hmono)
    (fun p => (Uc ω (p.1 + h) p.2 - Uc ω p.1 p.2) / h) hquot
    (fun ψ hψ hsupp => weak_heat_forwardDifference_of_hpde ω W Uc hcont hmono hpde hh hψ hsupp)
  refine ⟨hv.congr heq, fun p => div_nonneg ?_ hh.le⟩
  exact sub_nonneg.mpr (hmono p.2 (le_add_of_nonneg_right hh.le))

end Parking

end
