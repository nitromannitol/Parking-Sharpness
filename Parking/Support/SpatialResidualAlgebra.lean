/- Linearity and measurable evaluation of the weak heat residual. -/
import Parking.Support.SpatialZeroIntegralTesting
import Parking.Generic.SpaceTimeDerivativeAlgebra

open MeasureTheory Set
open Parking.Generic.SpaceTimeDerivatives
noncomputable section
namespace Parking
variable {d : ℕ}

theorem isSpaceTimeTest_sub {ψ χ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : IsSpaceTimeTest ψ) (hχ : IsSpaceTimeTest χ) :
    IsSpaceTimeTest (fun p => ψ p - χ p) := by
  refine ⟨hψ.1.sub hχ.1, hψ.2.1.sub hχ.2.1, ?_⟩
  intro p hp
  rcases (tsupport_binop_subset (fun a b : ℝ => a - b) (sub_self 0) ψ χ) hp with hp | hp
  · exact hψ.2.2 p hp
  · exact hχ.2.2 p hp

theorem spaceTime_contOp_sub {ψ χ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (p : ℝ × (Fin d → ℝ)) :
    contOp d (fun x => ψ (p.1, x) - χ (p.1, x)) p.2 =
      contOp d (fun x => ψ (p.1, x)) p.2 - contOp d (fun x => χ (p.1, x)) p.2 := by
  rw [spaceTime_contOp_eq (hψ.sub hχ), spaceTime_contOp_eq hψ, spaceTime_contOp_eq hχ]
  simp_rw [spaceDeriv_sub (hψ.differentiable (by simp)) (hχ.differentiable (by simp))]
  simp_rw [spaceDeriv_sub ((contDiff_spaceDeriv hψ _).differentiable (by simp))
    ((contDiff_spaceDeriv hχ _).differentiable (by simp))]
  rw [Finset.sum_sub_distrib, sub_div]

theorem spaceTimeResidualTest_sub {ψ χ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : IsSpaceTimeTest ψ) (hχ : IsSpaceTimeTest χ)
    (p : ℝ × (Fin d → ℝ)) :
    spaceTimeResidualTest (fun q => ψ q - χ q) p =
      spaceTimeResidualTest ψ p - spaceTimeResidualTest χ p := by
  have ht : timeDeriv (fun q => ψ q - χ q) p = timeDeriv ψ p - timeDeriv χ p := by
    simp only [timeDeriv, fderiv_fun_sub (hψ.1.differentiable (by simp) p)
      (hχ.1.differentiable (by simp) p)]
    rfl
  simp only [spaceTimeResidualTest, ht, spaceTime_contOp_sub hψ.1 hχ.1]
  ring

theorem integrable_mul_spaceTimeResidualTest {u ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hu : Continuous u) (hψ : IsSpaceTimeTest ψ) :
    Integrable (fun p => u p * spaceTimeResidualTest ψ p) := by
  apply (hu.mul (continuous_spaceTimeResidualTest hψ)).integrable_of_hasCompactSupport
  apply HasCompactSupport.mul_left
  exact HasCompactSupport.intro hψ.2.1 fun p hp =>
    spaceTimeResidualTest_eq_zero_of_notMem hψ hp

theorem integral_mul_spaceTimeResidualTest_sub {u ψ χ : ℝ × (Fin d → ℝ) → ℝ}
    (hu : Continuous u) (hψ : IsSpaceTimeTest ψ) (hχ : IsSpaceTimeTest χ) :
    (∫ p, u p * spaceTimeResidualTest (fun q => ψ q - χ q) p) =
      (∫ p, u p * spaceTimeResidualTest ψ p) - ∫ p, u p * spaceTimeResidualTest χ p := by
  simp_rw [spaceTimeResidualTest_sub hψ hχ, mul_sub]
  exact integral_sub (integrable_mul_spaceTimeResidualTest hu hψ)
    (integrable_mul_spaceTimeResidualTest hu hχ)

theorem measurable_integral_mul_spaceTimeResidualTest
    {Ω : Type*} [MeasurableSpace Ω] {u : Ω → ℝ × (Fin d → ℝ) → ℝ}
    (hu : ∀ ω, Continuous (u ω)) (hum : ∀ p, Measurable fun ω => u ω p)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ) :
    Measurable (fun ω => ∫ p, u ω p * spaceTimeResidualTest ψ p) := by
  have hj : Measurable (fun p : Ω × (ℝ × (Fin d → ℝ)) => u p.1 p.2) :=
    (measurable_uncurry_of_continuous_of_measurable hu hum).comp measurable_swap
  exact (hj.mul ((continuous_spaceTimeResidualTest hψ).measurable.comp
    measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

/-- Tests with the same time integral have the same residual on a sample where
all supported zero-time-integral tests have zero residual. -/
theorem integral_residual_eq_of_timeIntegral_eq
    {u ψ χ : ℝ × (Fin d → ℝ) → ℝ} (hu : Continuous u)
    (hzero : ∀ θ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest θ →
      tsupport θ ⊆ {p | 0 < u p} → (∀ x, (∫ s : ℝ, θ (s, x)) = 0) →
        (∫ p, u p * spaceTimeResidualTest θ p) = 0)
    (hψ : IsSpaceTimeTest ψ) (hχ : IsSpaceTimeTest χ)
    (hψs : tsupport ψ ⊆ {p | 0 < u p}) (hχs : tsupport χ ⊆ {p | 0 < u p})
    (htime : ∀ x, (∫ s : ℝ, ψ (s, x)) = ∫ s : ℝ, χ (s, x)) :
    (∫ p, u p * spaceTimeResidualTest ψ p) = ∫ p, u p * spaceTimeResidualTest χ p := by
  have hsub : tsupport (fun p => ψ p - χ p) ⊆ {p | 0 < u p} :=
    (tsupport_binop_subset (fun a b : ℝ => a - b) (sub_self 0) ψ χ).trans (union_subset hψs hχs)
  have htime0 : ∀ x, (∫ s : ℝ, (ψ (s, x) - χ (s, x))) = 0 := by
    intro x
    rw [integral_sub
      ((contDiff_timeSlice hψ.1 x).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_timeSlice hψ.2.1 x))
      ((contDiff_timeSlice hχ.1 x).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_timeSlice hχ.2.1 x)), htime, sub_self]
  have h := hzero _ (isSpaceTimeTest_sub hψ hχ) hsub htime0
  rw [integral_mul_spaceTimeResidualTest_sub hu hψ hχ] at h
  exact sub_eq_zero.mp h

end Parking
