/-
Strict positivity of the absolute odometer discrepancy at every horizon at least two.
-/
import Parking.Support.OdometerRandomness
import Parking.Support.ParticleConfLaw

noncomputable section
namespace Parking
open MeasureTheory
variable {d : ℕ}

/-- The absolute particle/divisible discrepancy has strictly positive mean at every horizon at least two. -/
theorem integral_abs_discrepancy_pos (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n : ℕ) (hn : 2 ≤ n) :
    0 < ∫ ω, |(U ω n 0 : ℝ) - uOf ω n 0| ∂(law d ν) := by
  haveI := hν.prob
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = t + 2 := ⟨n - 2, by omega⟩
  obtain ⟨k, hk, hkν⟩ := hν.exists_positive_atom
  have hi := (integrable_U_law hd ν hν.integrable_abs (t + 2) 0).sub
    (integrable_uOf hd ν hν.integrable_abs (t + 2) 0)
  have hnn : 0 ≤ ∫ ω, |(U ω (t + 2) 0 : ℝ) - uOf ω (t + 2) 0| ∂(law d ν) :=
    integral_nonneg fun _ => abs_nonneg _
  apply lt_of_le_of_ne hnn
  intro hz
  have heq := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg
    ((U ω (t + 2) 0 : ℝ) - uOf ω (t + 2) 0)) hi.abs).mp hz.symm
  have hs : ∀ᵐ ω ∂(law d ν), (U ω (t + 2) 0 : ℝ) = uOf ω (t + 2) 0 := by
    filter_upwards [heq] with ω hω
    exact sub_eq_zero.mp (abs_eq_zero.mp hω)
  let P : (Site d → ℤ) × ℕ → Prop := fun q =>
    (q.2 : ℝ) = u (fun x => (q.1 x : ℝ)) (t + 2) 0
  have hP : MeasurableSet {q | P q} := measurableSet_eq_fun
    ((measurable_from_countable' fun k : ℕ => (k : ℝ)).comp measurable_snd)
    ((measurable_u_eval (t + 2) 0).comp (measurable_pi_lambda _ fun x =>
      measurable_intCastReal.comp ((measurable_pi_apply x).comp measurable_fst)))
  have hmap : ∀ᵐ q ∂((law d ν).map (fun ω : Data d => (ω.1, U ω (t + 2) 0))), P q :=
    (ae_map_iff (measurable_fst.prodMk (measurable_U (t + 2) 0)).aemeasurable hP).mpr hs
  rw [← map_conf_pOdometer hd ν (t + 2) 0] at hmap
  have hpM : Measurable fun ω : Parking.PData d => (ω.1, pOdometer (toPDriver ω) (t + 2) 0) :=
    measurable_fst.prodMk ((measurable_pi_apply (t + 2, 0)).comp
      (measurable_fst.comp measurable_particleObservables))
  have hp := (ae_map_iff hpM.aemeasurable hP).mp hmap
  exact not_ae_pOdometer_eq_conf hd ν k hk hkν t
    (fun η => u (fun x => (η x : ℝ)) (t + 2) 0) hp
end Parking
