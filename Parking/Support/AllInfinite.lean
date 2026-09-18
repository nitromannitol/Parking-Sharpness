/-
Every odometer is infinite: Step 2 of `prop:everyone-settles`.

The origin has an infinite odometer with probability at least a fixed positive
constant, and almost surely one infinite odometer forces every odometer to be
infinite, so the event that EVERY odometer is infinite already has positive
probability.  That event is invariant under every translation of the lattice,
and the translations act ergodically on the law of the data, so its probability
is `0` or `1`; being positive, it is `1`.
-/
import Parking.Support.Ergodic
import Parking.Support.StackHits
import Parking.Support.OdometerInfinite

noncomputable section

open MeasureTheory

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- Translating the data translates the limiting odometer. -/
theorem Ulimit_shiftData (v : Site d) (ω : Data d) (x : Site d) :
    Parking.Ulimit (shiftData v ω) x = Parking.Ulimit ω (x + v) := by
  unfold Parking.Ulimit
  exact iSup_congr fun n => by rw [U_shiftData]

theorem measurableSet_Ulimit_top (x : Site d) :
    MeasurableSet {ω : Data d | Parking.Ulimit ω x = ⊤} := by
  have hset : {ω : Data d | Parking.Ulimit ω x = ⊤}
      = ⋂ M : ℕ, ⋃ n : ℕ, {ω : Data d | M ≤ Parking.U ω n x} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Ulimit_eq_top_iff]
  rw [hset]
  exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n =>
    measurableSet_le measurable_const (measurable_U n x)

theorem measurableSet_forall_Ulimit_top (d : ℕ) :
    MeasurableSet {ω : Data d | ∀ x : Site d, Parking.Ulimit ω x = ⊤} := by
  have hset : {ω : Data d | ∀ x : Site d, Parking.Ulimit ω x = ⊤}
      = ⋂ x : Site d, {ω : Data d | Parking.Ulimit ω x = ⊤} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [hset]
  exact MeasurableSet.iInter fun x => measurableSet_Ulimit_top x

/-- The event that every odometer is infinite is exactly invariant under every
translation. -/
theorem preimage_shiftData_forall_top (v : Site d) :
    shiftData (d := d) v ⁻¹' {ω : Data d | ∀ x : Site d, Parking.Ulimit ω x = ⊤}
      = {ω : Data d | ∀ x : Site d, Parking.Ulimit ω x = ⊤} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Ulimit_shiftData]
  constructor
  · intro h x
    have hx := h (x - v)
    rwa [show x - v + v = x by abel] at hx
  · intro h x
    exact h (x + v)

/-- **Every odometer is infinite.**  Step 2 of the proof of
`prop:everyone-settles` at `parking.tex:1510-1532`. -/
theorem ae_forall_Ulimit_top (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∀ᵐ ω ∂(law d ν), ∀ x : Site d, Parking.Ulimit ω x = ⊤ := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  have hAm : MeasurableSet {ω : Data d | ∀ x : Site d, Parking.Ulimit ω x = ⊤} :=
    measurableSet_forall_Ulimit_top d
  have hv : LatticeProb.unit (⟨0, hd⟩ : Fin d) ≠ (0 : Site d) := LatticeProb.unit_ne_zero _
  have herg := ergodic_shiftData hd ν hv
  have hsub : {ω : Data d | Parking.Ulimit ω 0 = ⊤}
      ≤ᵐ[law d ν] {ω : Data d | ∀ x : Site d, Parking.Ulimit ω x = ⊤} := by
    filter_upwards [ae_Ulimit_top_of_exists (d := d) hd ν] with ω hω hmem
    exact hω ⟨0, hmem⟩
  rcases herg.ae_empty_or_univ hAm (preimage_shiftData_forall_top _) with h | h
  · exfalso
    obtain ⟨a, ha, hle⟩ :=
      exists_prob_Ulimit_top hGrowth hBernstein hConcentration hGreenNorms d hd ν hν
    have h0 : (law d ν) {ω : Data d | ∀ x : Site d, Parking.Ulimit ω x = ⊤} = 0 := by
      rw [measure_congr h, measure_empty]
    have hz : (law d ν) {ω : Data d | Parking.Ulimit ω 0 = ⊤} = 0 :=
      le_antisymm (by rw [← h0]; exact measure_mono_ae hsub) bot_le
    rw [measureReal_def, hz, ENNReal.toReal_zero] at hle
    linarith
  · have hc : (law d ν) {ω : Data d | ∀ x : Site d, Parking.Ulimit ω x = ⊤}ᶜ = 0 :=
      ae_eq_univ.mp h
    exact ae_iff.mpr hc

end Parking

end
