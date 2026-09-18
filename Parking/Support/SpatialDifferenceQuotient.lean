/-
Forward time differences of the continuum equation solve the homogeneous heat
 equation on the positive set. The spatial forcing cancels because translation
preserves the time integral of every test function.
-/
import Parking.Support.SpaceTimeContOp
import Parking.Generic.TimeTranslation
import Parking.Generic.MeasurableTimeDerivative
import Parking.Generic.HeatPositivity
import Parking.External.HeatInteriorRegularity

open MeasureTheory
open Parking.Generic.TimeTest
noncomputable section
namespace Parking
variable {d : ℕ}

/-- Forward translation preserves admissibility of positive-time tests. -/
theorem IsSpaceTimeTest.timeShift {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : IsSpaceTimeTest ψ) {h : ℝ} (hh : 0 ≤ h) :
    IsSpaceTimeTest (timeShift h ψ) := by
  refine ⟨contDiff_timeShift hψ.1 h, hasCompactSupport_timeShift hψ.2.1 h, ?_⟩
  intro p hp
  have ht := hψ.2.2 _ (mem_tsupport_timeShift hp)
  dsimp at ht
  linarith

/-- Subtracting translated weak equations removes a time-independent forcing.
The identity holds for every test supported in the positive set. -/
theorem spatial_difference_quotient_weak
    (u : ℝ × (Fin d → ℝ) → ℝ) (W : ((Fin d → ℝ) → ℝ) → ℝ)
    (hu : Continuous u) (hmono : ∀ x, Monotone fun s => u (s, x))
    (hpde : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ → tsupport ψ ⊆ {p | 0 < u p} →
      -∫ p, u p * deriv (fun s => ψ (s, p.2)) p.1 =
        (∫ p, u p * contOp d (fun x => ψ (p.1, x)) p.2) + W (fun x => ∫ s : ℝ, ψ (s, x)))
    {h : ℝ} (hh : 0 < h) :
    ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ → tsupport ψ ⊆ {p | 0 < u p} →
      -∫ p, ((u (p.1 + h, p.2) - u p) / h) * deriv (fun s => ψ (s, p.2)) p.1 =
        ∫ p, ((u (p.1 + h, p.2) - u p) / h) * contOp d (fun x => ψ (p.1, x)) p.2 := by
  intro ψ hψ hsupp
  have hshift : tsupport (timeShift h ψ) ⊆ {p | 0 < u p} := by
    intro p hp
    exact (hsupp (mem_tsupport_timeShift hp)).trans_le
      (hmono p.2 (sub_le_self _ hh.le))
  have heq := hpde ψ hψ hsupp
  have heqt := hpde (timeShift h ψ) (hψ.timeShift hh.le) hshift
  have hnoise : (fun x => ∫ s : ℝ, timeShift h ψ (s, x)) = fun x => ∫ s : ℝ, ψ (s, x) := by
    funext x
    exact integral_sub_right_eq_self (fun s => ψ (s, x)) h
  change -(∫ p, u p * Generic.TimeTest.timeDeriv (timeShift h ψ) p) = _ at heqt
  rw [timeDeriv_timeShift, hnoise] at heqt
  change -(∫ p, u p * Generic.TimeTest.timeDeriv ψ p) = _ at heq
  change -(∫ p, ((u (p.1 + h, p.2) - u p) / h) * Generic.TimeTest.timeDeriv ψ p) = _
  rw [integral_time_difference_quotient hu (Generic.TimeTest.contDiff_timeDeriv hψ.1).continuous
    (Generic.TimeTest.hasCompactSupport_timeDeriv (hψ.1.differentiable (by simp)) hψ.2.1),
    integral_time_difference_quotient hu (contDiff_spaceTime_contOp hψ.1).continuous
      (hasCompactSupport_spaceTime_contOp hψ), ← neg_div]
  congr 1
  change -(∫ p, u p * timeShift h (Generic.TimeTest.timeDeriv ψ) p) =
    (∫ p, u p * timeShift h (fun q => contOp d (fun x => ψ (q.1, x)) q.2) p) +
      W (fun x => ∫ s : ℝ, ψ (s, x)) at heqt
  linarith

/-- The corrected interior regularity input applies to each continuous forward
quotient. Its smooth representative is nonnegative on the positive set. -/
theorem spatial_difference_quotient_regular
    (hInterior : External.HeatInteriorRegularity)
    (u : ℝ × (Fin d → ℝ) → ℝ) (W : ((Fin d → ℝ) → ℝ) → ℝ)
    (hu : Continuous u) (hzero : ∀ x, u (0, x) = 0)
    (hmono : ∀ x, Monotone fun s => u (s, x))
    (hpde : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ → tsupport ψ ⊆ {p | 0 < u p} →
      -∫ p, u p * deriv (fun s => ψ (s, p.2)) p.1 =
        (∫ p, u p * contOp d (fun x => ψ (p.1, x)) p.2) + W (fun x => ∫ s : ℝ, ψ (s, x)))
    {h : ℝ} (hh : 0 < h) :
    ∃ v : ℝ × (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v {p | 0 < u p} ∧
      (∀ p, 0 < u p → (u (p.1 + h, p.2) - u p) / h = v p) ∧
      (∀ p, 0 < u p → 0 ≤ v p) ∧
      (∀ p, 0 < u p → HasDerivAt (fun s => v (s, p.2))
        (contOp d (fun x => v (p.1, x)) p.2) p.1) := by
  obtain ⟨v, hv, heq, hheat⟩ := hInterior d {p | 0 < u p}
    (isOpen_lt continuous_const hu) (Generic.HeatPositivity.positive_time hzero hmono)
    (fun p => (u (p.1 + h, p.2) - u p) / h)
    (continuous_time_difference_quotient hu h) (spatial_difference_quotient_weak u W hu hmono hpde hh)
  refine ⟨v, hv, heq, ?_, hheat⟩
  intro p hp
  rw [← heq p hp]
  exact Generic.TimeDerivative.forward_difference_nonneg (hmono p.2) p.1 hh

/-- Apply regularity simultaneously to all positive time increments on the one
full-measure event carrying the continuum equation, without changing its witnesses. -/
theorem spatial_difference_quotient_regular_ae
    (hInterior : External.HeatInteriorRegularity)
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hUccont : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (hUc0 : ∀ ω x, Uc ω 0 x = 0)
    (hUcmono : ∀ ω x, Monotone fun s => Uc ω s x)
    (hpde : ∀ᵐ ω ∂Q, ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
      -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
        = (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * contOp d (fun x => ψ (p.1, x)) p.2)
          + W (fun x => ∫ s : ℝ, ψ (s, x)) ω) :
    ∀ᵐ ω ∂Q, ∀ h : ℝ, 0 < h → ∃ v : ℝ × (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v {p | 0 < Uc ω p.1 p.2} ∧
      (∀ p : ℝ × (Fin d → ℝ), 0 < Uc ω p.1 p.2 → (Uc ω (p.1 + h) p.2 - Uc ω p.1 p.2) / h = v p) ∧
      (∀ p : ℝ × (Fin d → ℝ), 0 < Uc ω p.1 p.2 → 0 ≤ v p) ∧
      (∀ p : ℝ × (Fin d → ℝ), 0 < Uc ω p.1 p.2 → HasDerivAt (fun s => v (s, p.2))
        (contOp d (fun x => v (p.1, x)) p.2) p.1) := by
  filter_upwards [hpde] with ω hω
  intro h hh
  exact spatial_difference_quotient_regular hInterior (fun p => Uc ω p.1 p.2)
    (fun φ => W φ ω) (hUccont ω) (hUc0 ω) (hUcmono ω) hω hh

end Parking
