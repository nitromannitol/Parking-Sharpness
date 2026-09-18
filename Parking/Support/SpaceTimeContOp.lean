import Parking.Support.Continuum
import Parking.Generic.SpaceTimeDerivatives
import Parking.Support.SpatialTimeDerivative

open MeasureTheory

noncomputable section
namespace Parking
open Generic.SpaceTimeDerivatives
variable {d : ℕ}

/-- The spatial operator on a space-time test is a finite sum of spatial derivatives. -/
theorem spaceTime_contOp_eq {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (p : ℝ × (Fin d → ℝ)) :
    contOp d (fun x => ψ (p.1, x)) p.2 =
      (∑ i : Fin d, spaceDeriv (spaceDeriv ψ i) i p) / (2 * d) := by
  unfold contOp lap
  simp_rw [second_deriv_spaceSlice hψ p]

/-- Applying the spatial heat operator preserves smoothness in space-time. -/
theorem contDiff_spaceTime_contOp {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => contOp d (fun x => ψ (p.1, x)) p.2) := by
  simp_rw [spaceTime_contOp_eq hψ]
  exact (ContDiff.sum fun i _ => contDiff_spaceDeriv (contDiff_spaceDeriv hψ i) i).div_const _

/-- The spatial heat operator does not enlarge the space-time support. -/
theorem tsupport_spaceTime_contOp_subset {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    tsupport (fun p : ℝ × (Fin d → ℝ) => contOp d (fun x => ψ (p.1, x)) p.2) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro p hp
  by_contra hn
  have hz : ∀ i : Fin d, spaceDeriv (spaceDeriv ψ i) i p = 0 := by
    intro i
    apply image_eq_zero_of_notMem_tsupport
    exact fun h => hn ((tsupport_spaceDeriv_subset ψ i)
      ((tsupport_spaceDeriv_subset (spaceDeriv ψ i) i) h))
  exact hp (by simp [spaceTime_contOp_eq hψ p, hz])

theorem hasCompactSupport_spaceTime_contOp {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : IsSpaceTimeTest ψ) :
    HasCompactSupport (fun p : ℝ × (Fin d → ℝ) => contOp d (fun x => ψ (p.1, x)) p.2) :=
  hψ.2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_spaceTime_contOp_subset hψ.1)


/-- The spatial operator on time slices is a finite sum of second directional
derivatives of the joint space-time function. -/
theorem contOp_timeSlice_eq {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (p : ℝ × (Fin d → ℝ)) :
    contOp d (fun x => ψ (p.1, x)) p.2 =
      (∑ i : Fin d, fderiv ℝ
        (fun q => fderiv ℝ ψ q (0, Pi.single i 1)) p (0, Pi.single i 1)) / (2 * d) := by
  unfold contOp lap
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hdir : ContDiff ℝ (⊤ : ℕ∞)
      (fun q => fderiv ℝ ψ q (0, Pi.single i 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ ((0, Pi.single i 1) : ℝ × (Fin d → ℝ))).contDiff.comp
      (hψ.fderiv_right (by simp))
  have hcurve (s : ℝ) : HasDerivAt
      (fun t => (p.1, Function.update p.2 i t)) (0, Pi.single i 1) s :=
    (hasDerivAt_const s p.1).prodMk (hasDerivAt_update p.2 i s)
  have hfirst : (fun s => deriv (fun t => ψ (p.1, Function.update p.2 i t)) s) =
      fun s => fderiv ℝ ψ (p.1, Function.update p.2 i s) (0, Pi.single i 1) := by
    funext s
    exact (((hψ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s (hcurve s)).deriv
  rw [hfirst]
  simpa only [Function.update_eq_self, Function.comp_def, Prod.mk.eta] using
    (((hdir.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt (p.2 i) (hcurve (p.2 i))).deriv

/-- A continuous field times the spatial operator of a test is integrable. -/
theorem integrable_mul_spaceTime_contOp {u ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hu : Continuous u) (hψ : IsSpaceTimeTest ψ) :
    Integrable (fun p => u p * contOp d (fun x => ψ (p.1, x)) p.2) :=
  (hu.mul (contDiff_spaceTime_contOp hψ.1).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_spaceTime_contOp hψ).mul_left

/-- A continuous field times the time derivative of a test is integrable. -/
theorem integrable_mul_timeSlice_deriv {u ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hu : Continuous u) (hψ : IsSpaceTimeTest ψ) :
    Integrable (fun p => u p * deriv (fun s => ψ (s, p.2)) p.1) := by
  simp_rw [deriv_timeSlice (hψ.1.differentiable (by simp))]
  exact (hu.mul (contDiff_timeDeriv hψ.1).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_timeDeriv hψ.2.1).mul_left


end Parking
