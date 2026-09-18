/- Deterministic approximation of the signed middle term by its continuum-operator pairing. -/
import Parking.Support.SpatWWalkGrid
import Parking.Support.SpatWDivisiblePairing
import Parking.Generic.WeightedIntegral

open Set Filter Topology LatticeProb MeasureTheory
noncomputable section
namespace Parking
variable {d : ℕ}

/-- The cell coefficient is measurable because it factors through the countable lattice. -/
theorem measurable_scaledWalkTest (φ : (Fin d → ℝ) → ℝ) (R : ℝ) :
    Measurable (scaledWalkTest φ R) := by
  apply (measurable_from_countable' (fun y : Site d => R ^ 2 *
    (walkOp (fun z => φ (fun j => (z j : ℝ) / R)) y - φ (fun j => (y j : ℝ) / R)))).comp
  exact measurable_pi_lambda _ (fun i => Int.measurable_floor.comp
    (measurable_const.mul (measurable_pi_apply i)))

/-- The rescaled parking odometer is measurable in space. -/
theorem measurable_barOdometer_in_x (w : Data d) (R s : ℝ) :
    Measurable (fun x : Fin d → ℝ => barOdometer w R s x) := by
  unfold barOdometer
  apply Measurable.const_mul
  apply (measurable_from_countable' (fun y : Site d => (U w ⌊s * R ^ 2⌋₊ y : ℝ))).comp
  exact measurable_pi_lambda _ (fun i => Int.measurable_floor.comp
    (measurable_const.mul (measurable_pi_apply i)))

/-- The rescaled parking odometer is integrable on every compact ball. -/
theorem integrableOn_barOdometer (w : Data d) {R t B : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun x => barOdometer w R t x) (Metric.closedBall (0 : Fin d → ℝ) B) volume := by
  let C := max |t| B
  have hC : 0 ≤ C := (abs_nonneg t).trans (le_max_left _ _)
  let M := R ^ ((d : ℝ) / 2 - 2) * ((⌊C * R ^ 2⌋₊ : ℝ) *
      confBox w 0 ((⌈C * R⌉₊ + 1) + ⌊C * R ^ 2⌋₊))
  have hM : ∀ x ∈ Metric.closedBall (0 : Fin d → ℝ) B, |barOdometer w R t x| ≤ M := by
    intro x hx
    exact abs_barOdometer_le (p := (t, x)) (C := C) w hR hC (le_max_left _ _)
      (fun i => (norm_le_of_mem_closedBall hx i).trans (le_max_right _ _))
  refine (integrableOn_const (isCompact_closedBall (0 : Fin d → ℝ) B).measure_lt_top.ne
    (C := M)).mono' (measurable_barOdometer_in_x w R t).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  exact hM x hx

/-- A uniform coefficient error bounds the pairing error by the local odometer mass. -/
theorem abs_signedMiddle_sub_pairing_le {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ)
    {B R ε : ℝ} (hB : 0 < B) (hbound : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B)
    (hR : 1 ≤ R) (herror : ∀ x, |scaledWalkTest φ R x - contOp d φ x| ≤ ε)
    (w : Data d) :
    |signedMiddle w R φ - ∫ x, barOdometer w R 1 x * contOp d φ x| ≤
      ε * ∫ x in Metric.closedBall (0 : Fin d → ℝ) (B + 2), barOdometer w R 1 x := by
  let K := Metric.closedBall (0 : Fin d → ℝ) (B + 2)
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hu := integrableOn_barOdometer w (t := 1) (B := B + 2) hR0
  obtain ⟨M, _hM0, hM⟩ := exists_norm_le_of_hasCompactSupport (continuous_contOp hφ)
    (hasCompactSupport_contOp hφ)
  have hS : ∀ x, |scaledWalkTest φ R x| ≤ M + ε := by
    intro x
    have := abs_sub_le (scaledWalkTest φ R x) (contOp d φ x) 0
    simp only [sub_zero] at this
    linarith [herror x, hM x]
  have hf : IntegrableOn (fun x => barOdometer w R 1 x * scaledWalkTest φ R x) K volume :=
    hu.mul_bdd (measurable_scaledWalkTest φ R).aestronglyMeasurable (ae_of_all _ hS)
  have hg : IntegrableOn (fun x => barOdometer w R 1 x * contOp d φ x) K volume :=
    hu.mul_bdd (continuous_contOp hφ).measurable.aestronglyMeasurable (ae_of_all _ hM)
  have hzero : ∀ x ∉ K, scaledWalkTest φ R x = 0 := by
    intro x hx
    apply scaledWalkTest_eq_zero_of_norm_gt hbound hR
    simpa [K, Metric.mem_closedBall, dist_eq_norm] using hx
  have hcontzero : ∀ x ∉ K, contOp d φ x = 0 := by
    intro x hx
    have hKx : B + 2 < ‖x‖ := by simpa [K, Metric.mem_closedBall, dist_eq_norm] using hx
    have hnotsupp : x ∉ tsupport φ := by
      intro hs
      have hsub : tsupport φ ⊆ Metric.closedBall (0 : Fin d → ℝ) B :=
        closure_minimal (fun y hy => by simpa [Metric.mem_closedBall, dist_eq_norm] using hbound y hy)
          Metric.isClosed_closedBall
      have hb : ‖x‖ ≤ B := by simpa [Metric.mem_closedBall, dist_eq_norm] using hsub hs
      linarith
    unfold contOp
    rw [lap_eq_sum hφ.1]
    have hz : ∀ i : Fin d, partialDeriv (partialDeriv φ i) i x = 0 := fun i =>
      partialDeriv_eq_zero_of_notMem (fun hx => hnotsupp (tsupport_partialDeriv_subset φ i hx))
    simp [hz]
  have hI : (∫ x in K, barOdometer w R 1 x * scaledWalkTest φ R x) =
      ∫ x, barOdometer w R 1 x * scaledWalkTest φ R x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hzero x hx, mul_zero])
  have hJ : (∫ x in K, barOdometer w R 1 x * contOp d φ x) =
      ∫ x, barOdometer w R 1 x * contOp d φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hcontzero x hx, mul_zero])
  rw [signedMiddle_eq_integral_scaledWalkTest hB hbound hR w, ← hI, ← hJ]
  have he := Generic.WeightedIntegral.abs_pairing_sub_le hu hf hg (ae_of_all _ herror)
  have hn : ∀ x, |barOdometer w R 1 x| = barOdometer w R 1 x := by
    intro x
    apply abs_of_nonneg
    unfold barOdometer
    positivity
  simpa only [hn] using he

/-- Taylor expansion and cell integration give an arbitrarily small local-mass error. -/
theorem eventually_abs_signedMiddle_sub_pairing_le (hd : 1 ≤ d)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ)
    {B : ℝ} (hB : 0 < B) (hbound : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ w : Data d,
      |signedMiddle w R φ - ∫ x, barOdometer w R 1 x * contOp d φ x| ≤
        ε * ∫ x in Metric.closedBall (0 : Fin d → ℝ) (B + 2), barOdometer w R 1 x := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_scaledWalkTest_error_le hd hφ hε]
    with R hR he w
  exact abs_signedMiddle_sub_pairing_le hφ hB hbound hR he w
end Parking
