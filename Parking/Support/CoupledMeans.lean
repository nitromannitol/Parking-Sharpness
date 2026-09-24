/-
Nonnegative marginal expectations for the common-table coupling. Both active
and hole populations at the origin have mean S at zero mean density. The
pathwise discrepancy count bound therefore gives an upper mean of 4S.
-/
import Parking.Support.CoupledLaw
import Parking.Support.CouplingTarget
import Parking.Support.DiscrepancyBalance

noncomputable section

open MeasureTheory LatticeProb
open scoped ENNReal

variable {d : ℕ}

/-- The original process observables as one measurable map. -/
def Parking.stackObservables (ω : Parking.Data d) : Parking.ProcessObservables d :=
  (fun tx => Parking.U ω tx.1 tx.2, fun tx => Parking.A ω tx.1 tx.2,
    fun tx => Parking.H ω tx.1 tx.2,
    fun ti => (LatticeProb.state (Parking.toDriver ω) ti.1).active ti.2)


theorem Parking.measurable_coupledObservables (hd : 1 ≤ d) (b : Bool) :
    Measurable (Parking.coupledObservables (d := d) b) :=
  Parking.measurable_matchedObservables ⟨0, hd⟩
    (fun ω : Parking.CoupledData d => Parking.coupledConf b ω.1.1) (fun ω => ω.1.2) Prod.snd
    ((Parking.measurable_coupledConf b).comp (measurable_fst.comp measurable_fst))
    (measurable_snd.comp measurable_fst) measurable_snd

/-- Both coupled marginals give the original expectation for every nonnegative
measurable observable of the full count history. -/
theorem Parking.lintegral_coupledObservables (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1) (b : Bool)
    (f : Parking.ProcessObservables d → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, f (Parking.coupledObservables b ω) ∂(Parking.coupledLaw d ν p) =
      ∫⁻ ω, f (Parking.stackObservables ω) ∂(Parking.law d ν) := by
  rw [← lintegral_map hf (Parking.measurable_coupledObservables hd b),
    Parking.map_coupledObservables hd ν hp b]
  exact lintegral_map hf Parking.measurable_stackObservables

/-- Both marginal active populations at the origin have mean `S_t`. -/
theorem Parking.lintegral_coupled_active (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (b : Bool) (t : ℕ) :
    ∫⁻ ω : Parking.CoupledData d,
      (Parking.matchedCount (Parking.coupledConf b ω.1.1) ω.1.2 ω.2 t 0 : ℝ≥0∞)
      ∂(Parking.coupledLaw d ν p) = ENNReal.ofReal (Parking.S (Parking.law d ν) t) := by
  have htransport := (Parking.Frozen.transport d hd ν inferInstance hint).1 t
  have h := ofReal_integral_eq_lintegral_ofReal htransport.1
    (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg (Parking.A ω t 0))
  rw [htransport.2.2] at h
  calc ∫⁻ ω : Parking.CoupledData d,
        (Parking.matchedCount (Parking.coupledConf b ω.1.1) ω.1.2 ω.2 t 0 : ℝ≥0∞)
        ∂(Parking.coupledLaw d ν p)
      = ∫⁻ ω, (Parking.A ω t 0 : ℝ≥0∞) ∂(Parking.law d ν) :=
        Parking.lintegral_coupledObservables hd ν hp b (fun O => (O.2.1 (t, 0) : ℝ≥0∞)) (by fun_prop)
    _ = _ := by simpa only [ENNReal.ofReal_natCast] using h.symm

/-- Both marginal hole populations at the origin have mean `S_t` at zero mean density. -/
theorem Parking.lintegral_coupled_holes (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν = 0)
    (b : Bool) (t : ℕ) :
    ∫⁻ ω : Parking.CoupledData d,
      ((Parking.matchedState (Parking.coupledConf b ω.1.1) ω.1.2 ω.2 t).holes 0 : ℝ≥0∞)
      ∂(Parking.coupledLaw d ν p) = ENNReal.ofReal (Parking.S (Parking.law d ν) t) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw
    infer_instance
  have hmap : (LatticeProb.iidLaw d ν).map (fun η : Site d → ℤ => η 0) = ν :=
    Measure.infinitePi_map_eval _ 0
  have hi0 : Integrable (fun η : Site d → ℤ => |(η 0 : ℝ)|) (LatticeProb.iidLaw d ν) := by
    have hi : Integrable (fun k : ℤ => |(k : ℝ)|)
        ((LatticeProb.iidLaw d ν).map (fun η : Site d → ℤ => η 0)) := by rw [hmap]; exact hint
    exact (integrable_map_measure (g := fun k : ℤ => |(k : ℝ)|)
      (f := fun η : Site d → ℤ => η 0) (μ := LatticeProb.iidLaw d ν)
      (by rw [hmap]; exact hint.aestronglyMeasurable)
      (measurable_pi_apply (0 : Site d)).aemeasurable).mp hi
  have hi : Integrable (fun ω => (Parking.H ω t 0 : ℝ)) (Parking.law d ν) :=
    Parking.integrable_H_data hd (fun v => Parking.iidLaw_map_shiftConf' ν v) hi0 t 0
  have h := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg (Parking.H ω t 0))
  rw [(Parking.mean_A_and_H_eq_S hd ν hint hmean t).2] at h
  calc ∫⁻ ω : Parking.CoupledData d,
        ((Parking.matchedState (Parking.coupledConf b ω.1.1) ω.1.2 ω.2 t).holes 0 : ℝ≥0∞)
        ∂(Parking.coupledLaw d ν p)
      = ∫⁻ ω, (Parking.H ω t 0 : ℝ≥0∞) ∂(Parking.law d ν) :=
        Parking.lintegral_coupledObservables hd ν hp b (fun O => (O.2.2.1 (t, 0) : ℝ≥0∞)) (by fun_prop)
    _ = _ := by simpa only [ENNReal.ofReal_natCast] using h.symm

/-- The mean number of live discrepancy labels is at most `4 S_t`. -/
theorem Parking.lintegral_discrepancyCount_le (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν = 0) (t : ℕ) :
    ∫⁻ ω : Parking.CoupledData d,
      ((Parking.discrepancyAt ω.1.1 (Parking.discrepancyState ω.1.1 ω.1.2 ω.2 t) t 0).card : ℝ≥0∞)
      ∂(Parking.coupledLaw d ν p) ≤ ENNReal.ofReal (4 * Parking.S (Parking.law d ν) t) := by
  have hM : ∀ b : Bool, Measurable fun ω : Parking.CoupledData d =>
      (Parking.matchedCount (Parking.coupledConf b ω.1.1) ω.1.2 ω.2 t 0 : ℝ≥0∞) := by
    intro b
    have hm := Parking.measurable_coupledObservables hd b
    change Measurable fun ω : Parking.CoupledData d =>
      ((Parking.coupledObservables b ω).2.1 (t, 0) : ℝ≥0∞)
    exact (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp
      ((measurable_pi_apply (t, (0 : Site d))).comp (measurable_fst.comp (measurable_snd.comp hm)))
  have hH : ∀ b : Bool, Measurable fun ω : Parking.CoupledData d =>
      ((Parking.matchedState (Parking.coupledConf b ω.1.1) ω.1.2 ω.2 t).holes 0 : ℝ≥0∞) := by
    intro b
    have hm := Parking.measurable_coupledObservables hd b
    change Measurable fun ω : Parking.CoupledData d =>
      ((Parking.coupledObservables b ω).2.2.1 (t, 0) : ℝ≥0∞)
    exact (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp
      ((measurable_pi_apply (t, (0 : Site d))).comp
        (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hm))))
  calc ∫⁻ ω : Parking.CoupledData d,
        ((Parking.discrepancyAt ω.1.1 (Parking.discrepancyState ω.1.1 ω.1.2 ω.2 t) t 0).card : ℝ≥0∞)
        ∂(Parking.coupledLaw d ν p)
      ≤ ∫⁻ ω : Parking.CoupledData d,
        (Parking.matchedCount (Parking.coupledConf true ω.1.1) ω.1.2 ω.2 t 0 : ℝ≥0∞) +
        ((Parking.matchedState (Parking.coupledConf true ω.1.1) ω.1.2 ω.2 t).holes 0 : ℝ≥0∞) +
        (Parking.matchedCount (Parking.coupledConf false ω.1.1) ω.1.2 ω.2 t 0 : ℝ≥0∞) +
        ((Parking.matchedState (Parking.coupledConf false ω.1.1) ω.1.2 ω.2 t).holes 0 : ℝ≥0∞)
        ∂(Parking.coupledLaw d ν p) := lintegral_mono fun ω => by
          simpa only [Nat.cast_add] using
            (Nat.cast_le (α := ℝ≥0∞)).mpr (Parking.discrepancyCount_le_four ω.1.1 ω.1.2 ω.2 t 0)
    _ = ENNReal.ofReal (Parking.S (Parking.law d ν) t) + ENNReal.ofReal (Parking.S (Parking.law d ν) t) +
        ENNReal.ofReal (Parking.S (Parking.law d ν) t) + ENNReal.ofReal (Parking.S (Parking.law d ν) t) := by
      rw [lintegral_add_left (f := fun ω : Parking.CoupledData d =>
          (Parking.matchedCount (Parking.coupledConf true ω.1.1) ω.1.2 ω.2 t 0 : ℝ≥0∞) +
          ((Parking.matchedState (Parking.coupledConf true ω.1.1) ω.1.2 ω.2 t).holes 0 : ℝ≥0∞) +
          (Parking.matchedCount (Parking.coupledConf false ω.1.1) ω.1.2 ω.2 t 0 : ℝ≥0∞))
          (((hM true).add (hH true)).add (hM false)),
        lintegral_add_left (f := fun ω : Parking.CoupledData d =>
          (Parking.matchedCount (Parking.coupledConf true ω.1.1) ω.1.2 ω.2 t 0 : ℝ≥0∞) +
          ((Parking.matchedState (Parking.coupledConf true ω.1.1) ω.1.2 ω.2 t).holes 0 : ℝ≥0∞))
          ((hM true).add (hH true)), lintegral_add_left (hM true),
        Parking.lintegral_coupled_active hd ν hp hint true,
        Parking.lintegral_coupled_active hd ν hp hint false,
        Parking.lintegral_coupled_holes hd ν hp hint hmean true,
        Parking.lintegral_coupled_holes hd ν hp hint hmean false]
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
      ring

end
