/- Measurability of the directed odometer, arrival counts and error field. -/
import Parking.Support.OrientedError
import Parking.Support.OrientedOdometerMeasurable
import Parking.Support.Measurability
import Parking.Support.ActivityHoles

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem measurable_arrivals_oriented (t : ℕ) (y x : Site d) :
    Measurable fun ω : Data d => arrivals ω.2.1 y x (orientedOdometer ω.1 ω.2.1 t y) := by
  classical
  refine measurable_of_countable_partition (fun ω : Data d => orientedOdometer ω.1 ω.2.1 t y)
    (measurable_orientedOdometer (fun ω : Data d => ω.1) (fun ω : Data d => ω.2.1)
      measurable_fst (measurable_fst.comp measurable_snd) t y) _
    (fun m ω => arrivals ω.2.1 y x m) (fun m => ?_) fun _ => rfl
  have hsum : ∀ ω : Data d, arrivals ω.2.1 y x m
      = ∑ j ∈ Finset.range m, if ω.2.1 (y, j) = x then 1 else 0 := by
    intro ω; rw [arrivals, Finset.card_filter]
  simp only [hsum]
  refine Finset.measurable_sum _ fun j _ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_eq_fun ((measurable_pi_apply (y, j)).comp (measurable_fst.comp measurable_snd))
    measurable_const

theorem measurable_wErrOriented (k : ℕ) (x : Site d) :
    Measurable fun ω : Data d => wErrOriented ω.1 ω.2.1 k x := by
  classical
  induction k generalizing x with
  | zero => exact measurable_const
  | succ k ih =>
      have hcast : ∀ (t : ℕ) (y z : Site d),
          Measurable fun ω : Data d =>
            ((arrivals ω.2.1 y z (orientedOdometer ω.1 ω.2.1 t y) : ℕ) : ℝ) :=
        fun t y z => (measurable_from_countable' fun m : ℕ => (m : ℝ)).comp
          (measurable_arrivals_oriented t y z)
      have hU : ∀ (t : ℕ) (y : Site d),
          Measurable fun ω : Data d => ((orientedOdometer ω.1 ω.2.1 t y : ℕ) : ℝ) :=
        fun t y => (measurable_from_countable' fun m : ℕ => (m : ℝ)).comp
          (measurable_orientedOdometer (fun ω : Data d => ω.1) (fun ω : Data d => ω.2.1)
            measurable_fst (measurable_fst.comp measurable_snd) t y)
      have hop : Measurable fun ω : Data d => orientedOp (wErrOriented ω.1 ω.2.1 k) x := by
        have : (fun ω : Data d => orientedOp (wErrOriented ω.1 ω.2.1 k) x)
            = fun ω : Data d =>
              (∑ i : Fin d, wErrOriented ω.1 ω.2.1 k (x - unit i)) / (d : ℝ) := rfl
        rw [this]
        exact (Finset.measurable_sum _ fun i _ => ih (x - unit i)).div_const _
      have hsum : Measurable fun ω : Data d =>
          ∑ i : Fin d,
            ((arrivals ω.2.1 (x - unit i) x
                (orientedOdometer ω.1 ω.2.1 k (x - unit i)) : ℝ)
              - (orientedOdometer ω.1 ω.2.1 k (x - unit i) : ℝ) / (d : ℝ)) :=
        Finset.measurable_sum _ fun i _ =>
          (hcast k (x - unit i) x).sub ((hU k (x - unit i)).div_const _)
      exact hop.add hsum

end Parking
end
