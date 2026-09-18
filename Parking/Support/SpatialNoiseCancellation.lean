/-
Time differentiation removes the time-independent noise from the continuum weak
equation. The time derivative of a test function has the same support restriction
and integrates to zero on every spatial slice.
-/
import Parking.Support.Continuum
import Parking.Generic.TimeTest

open MeasureTheory

noncomputable section

namespace Parking

/-- Spatial white noise vanishes at the zero test function on one fixed full-measure set. -/
theorem IsSpatialWhiteNoise.ae_zero {d : ℕ} {a : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {Q : Measure Ω} {W : ((Fin d → ℝ) → ℝ) → Ω → ℝ}
    (hW : IsSpatialWhiteNoise d a Q W) :
    ∀ᵐ ω ∂Q, W (fun _ => 0) ω = 0 := by
  have hz : IsTestFun (fun _ : Fin d → ℝ => (0 : ℝ)) :=
    ⟨contDiff_const, by simp [HasCompactSupport]⟩
  filter_upwards [hW.1 (fun _ => 0) (fun _ => 0) hz hz 0 0] with ω hω
  simpa using hω

/-- Time differentiation preserves the admissibility and support of a space-time test. -/
theorem IsSpaceTimeTest.timeDeriv {d : ℕ} {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : IsSpaceTimeTest ψ) : IsSpaceTimeTest (Generic.TimeTest.timeDeriv ψ) := by
  refine ⟨Generic.TimeTest.contDiff_timeDeriv hψ.1,
    Generic.TimeTest.hasCompactSupport_timeDeriv (hψ.1.differentiable (by simp)) hψ.2.1, ?_⟩
  intro p hp
  exact hψ.2.2 p (Generic.TimeTest.tsupport_timeDeriv_subset
    (hψ.1.differentiable (by simp)) hp)

/-- Testing the continuum equation against a time derivative cancels its white-noise term.
The probability space and limiting field are the same ones as in the weak equation. -/
theorem spatial_pde_test_time_derivative {d : ℕ} {a : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hW : IsSpatialWhiteNoise d a Q W)
    (hpde : ∀ᵐ ω ∂Q, ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
      -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
        = (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * contOp d (fun x => ψ (p.1, x)) p.2)
          + W (fun x => ∫ s : ℝ, ψ (s, x)) ω) :
    ∀ᵐ ω ∂Q, ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
      -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 *
          deriv (fun s => Generic.TimeTest.timeDeriv ψ (s, p.2)) p.1
        = ∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 *
          contOp d (fun x => Generic.TimeTest.timeDeriv ψ (p.1, x)) p.2 := by
  filter_upwards [hpde, hW.ae_zero] with ω hω hzero
  intro ψ hψ hsupp
  have heq := hω (Generic.TimeTest.timeDeriv ψ) hψ.timeDeriv
    ((Generic.TimeTest.tsupport_timeDeriv_subset (hψ.1.differentiable (by simp))).trans hsupp)
  have hz : (fun x => ∫ s : ℝ, Generic.TimeTest.timeDeriv ψ (s, x)) = fun _ => 0 := by
    funext x
    exact Generic.TimeTest.integral_timeDeriv_eq_zero hψ.1 hψ.2.1 x
  simpa only [hz, hzero, add_zero] using heq

end Parking
