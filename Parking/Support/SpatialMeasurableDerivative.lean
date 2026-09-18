/-
A coordinate-measurable choice of the smooth time derivative. The choice uses
forward difference quotients, so no measurable selection of smooth representatives
is required. The strong minimum principle supplies strict positivity.
-/
import Parking.Generic.MeasurableTimeDerivative
import Parking.Generic.TimeIntegration
import Parking.Support.SpatialStrictDerivative

open MeasureTheory

noncomputable section

namespace Parking

/-- Smooth classical time derivatives on the positive set admit a measurable
representative with the weak derivative identity and strict positivity. -/
theorem exists_spatial_measurable_derivative
    (hMinimum : External.HeatStrongMinimum) {d : ℕ}
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hUcmeas : ∀ s x, Measurable fun ω => Uc ω s x)
    (hUc0 : ∀ ω x, Uc ω 0 x = 0)
    (hUccont : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (hUcmono : ∀ ω x, Monotone fun s => Uc ω s x)
    (hregular : ∀ᵐ ω ∂Q, ∃ w : ℝ × (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) w {p | 0 < Uc ω p.1 p.2} ∧
      (∀ p : ℝ × (Fin d → ℝ), 0 < Uc ω p.1 p.2 → HasDerivAt (fun s => Uc ω s p.2) (w p) p.1) ∧
      (∀ p : ℝ × (Fin d → ℝ), 0 < Uc ω p.1 p.2 → HasDerivAt (fun s => w (s, p.2))
        (contOp d (fun x => w (p.1, x)) p.2) p.1)) :
    ∃ v : Ω → ℝ → (Fin d → ℝ) → ℝ,
      (∀ s x, Measurable fun ω => v ω s x) ∧
      (∀ᵐ ω ∂Q, ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => v ω p.1 p.2)
          {p | 0 < Uc ω p.1 p.2} ∧
        (∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
          tsupport ψ ⊆ {p | 0 < Uc ω p.1 p.2} →
          -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
            = ∫ p : ℝ × (Fin d → ℝ), v ω p.1 p.2 * ψ p) ∧
        ∀ s x, 0 < Uc ω s x → 0 < v ω s x) := by
  let v : Ω → ℝ → (Fin d → ℝ) → ℝ := fun ω s x =>
    Generic.TimeDerivative.value (fun t => Uc ω t x) s
  refine ⟨v, fun s x => Generic.TimeDerivative.measurable_value (fun t => hUcmeas t x) s, ?_⟩
  filter_upwards [hregular] with ω hω
  obtain ⟨w, hw, hderiv, hheat⟩ := hω
  have heq : ∀ p : ℝ × (Fin d → ℝ), 0 < Uc ω p.1 p.2 → v ω p.1 p.2 = w p := by
    intro p hp
    exact Generic.TimeDerivative.value_eq_of_hasDerivAt (hderiv p hp)
  refine ⟨hw.congr heq, ?_, ?_⟩
  · intro ψ hψ hsupp
    have hweak := Generic.TimeTest.integral_mul_timeDeriv
      (isOpen_lt continuous_const (hUccont ω)) (hUccont ω) hw.continuousOn
      hderiv hψ.1 hψ.2.1 hsupp
    change -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 *
      Generic.TimeTest.timeDeriv ψ p = _
    rw [hweak]
    apply integral_congr_ae
    filter_upwards [] with p
    by_cases hp : p ∈ tsupport ψ
    · rw [heq p (hsupp hp)]
    · have hz : ψ p = 0 := image_eq_zero_of_notMem_tsupport hp
      simp only [hz, mul_zero]
  · intro s x hp
    rw [heq (s, x) hp]
    exact spatial_time_derivative_pos hMinimum (hUccont ω) (hUc0 ω) (hUcmono ω)
      hw hderiv hheat (s, x) hp

end Parking
