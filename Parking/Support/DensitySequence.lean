/-
Survivor density decreases in time. A critical law has the first moment
needed to compare its expectations by pointwise monotonicity.
-/
import Parking.Frozen.Transport
import Parking.Frozen.CriticalDensity
import Parking.Support.UpperTarget

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Filter
variable {d : ℕ}

theorem survivorsFrom_antitone (D : Driver d) (x : Site d) :
    Antitone (fun t => LatticeProb.survivorsFrom D t x) := by
  intro s t hst
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hr, ha⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hr, LatticeProb.active_of_le hst ha⟩

theorem S_antitone (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) :
    Antitone (S (law d ν)) := by
  intro s t hst
  exact integral_mono ((Parking.Frozen.transport d hd ν inferInstance hint).1 t).2.1
    ((Parking.Frozen.transport d hd ν inferInstance hint).1 s).2.1
    (fun ω => Nat.cast_le.mpr (survivorsFrom_antitone (toDriver ω) 0 hst))

theorem CriticalLaw.integrable_abs {ν : Measure ℤ} (hν : CriticalLaw ν) :
    Integrable (fun k : ℤ => |(k : ℝ)|) ν := by
  obtain ⟨θ, hθ, hexp⟩ := hν.expMoment
  obtain ⟨K, _hK, hbound⟩ := rpow_le_const_mul_exp (r := (1 : ℝ)) (by norm_num) hθ
  refine Integrable.mono' (hexp.const_mul K) (measurable_from_countable' _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  have hb := hbound |(k : ℝ)| (abs_nonneg _)
  simpa only [Real.rpow_one, Real.norm_eq_abs, abs_abs] using hb
end Parking
