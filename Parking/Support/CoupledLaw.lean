/-
Both resampled configurations run with the same instruction tables. Each
marginal has the original joint law of all count observables, at all sites and
times. The shared directions do not alter either marginal's evolution law.
-/
import Parking.Support.MatchedLaw
import Parking.Support.Resample

noncomputable section

open MeasureTheory LatticeProb
open scoped ENNReal

variable {d : ℕ}

/-- The joint odometer, active count, hole count and activity indicators. -/
abbrev Parking.ProcessObservables (d : ℕ) :=
  (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Label d → Bool)

def Parking.matchedObservables (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) : Parking.ProcessObservables d :=
  (fun tx => (Parking.matchedState η ρ σ tx.1).departures tx.2,
   fun tx => (Parking.matchActive η (Parking.matchedState η ρ σ tx.1) tx.1 tx.2).card,
   fun tx => (Parking.matchedState η ρ σ tx.1).holes tx.2,
   fun ti => (Parking.matchedState η ρ σ ti.1).active ti.2)

def Parking.particleObservables (ω : Parking.PData d) : Parking.ProcessObservables d :=
  (fun tx => Parking.pOdometer (Parking.toPDriver ω) tx.1 tx.2,
   fun tx => Parking.pActiveCount (Parking.toPDriver ω) tx.1 tx.2,
   fun tx => Parking.pHoleCount (Parking.toPDriver ω) tx.1 tx.2,
   fun ti => (Parking.pState (Parking.toPDriver ω) ti.1).active ti.2)

theorem Parking.matchedObservables_eq (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) :
    Parking.matchedObservables η ρ σ =
      Parking.particleObservables (η, Parking.matchedMoves η ρ σ, ρ) := by
  unfold Parking.matchedObservables Parking.particleObservables Parking.pOdometer
    Parking.pActiveCount Parking.pHoleCount Parking.toPDriver
  simp only [Parking.pState_matchedMoves]
  rfl

theorem Parking.measurable_particleObservables :
    Measurable (Parking.particleObservables (d := d)) := by
  have hS := Parking.measurableState_pState (d := d)
    (Ω := Parking.PData d) Prod.fst (fun ω => ω.2.1) (fun ω => ω.2.2)
    measurable_fst (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  refine (measurable_pi_lambda _ fun tx : ℕ × Site d => (hS tx.1).2.2.2 tx.2).prodMk
    ((measurable_pi_lambda _ fun tx : ℕ × Site d => ?_).prodMk
      ((measurable_pi_lambda _ fun tx : ℕ × Site d => (hS tx.1).2.2.1 tx.2).prodMk
        (measurable_pi_lambda _ fun ti : ℕ × Label d => (hS ti.1).1 ti.2)))
  exact (measurable_from_countable' (Finset.card (α := Label d))).comp
    (Parking.measurable_matchActive Prod.fst _ measurable_fst (hS tx.1) tx.1 tx.2)

theorem Parking.measurable_matchedObservables {Ω : Type*} [MeasurableSpace Ω]
    (i₀ : Fin d) (e : Ω → Site d → ℤ) (r : Ω → Label d × ℕ → ℝ)
    (σ : Ω → Parking.RoundNoise d) (he : Measurable e) (hr : Measurable r)
    (hσ : Measurable σ) :
    Measurable fun ω => Parking.matchedObservables (e ω) (r ω) (σ ω) := by
  simp_rw [Parking.matchedObservables_eq]
  exact Parking.measurable_particleObservables.comp
    (he.prodMk ((Parking.measurable_matchedMoves i₀ e r σ he hr hσ).prodMk hr))

/-- The entire family of count observables of a marginal has the original
process law, jointly over sites and times. -/
theorem Parking.map_matchedObservables (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] :
    (((LatticeProb.iidLaw d ν).prod (LatticeProb.rankLaw d)).prod
      (Parking.roundNoiseLaw d)).map
        (fun ω => Parking.matchedObservables ω.1.1 ω.1.2 ω.2) =
      (Parking.law d ν).map (fun ω =>
        (fun tx : ℕ × Site d => Parking.U ω tx.1 tx.2,
         fun tx : ℕ × Site d => Parking.A ω tx.1 tx.2,
         fun tx : ℕ × Site d => Parking.H ω tx.1 tx.2,
         fun ti : ℕ × Label d => (LatticeProb.state (Parking.toDriver ω) ti.1).active ti.2)) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw
    infer_instance
  have hm := Parking.measurable_matchedMoves ⟨0, hd⟩
    (Ω := ((Site d → ℤ) × (Label d × ℕ → ℝ)) × Parking.RoundNoise d)
    (fun ω => ω.1.1) (fun ω => ω.1.2) Prod.snd
    (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst) measurable_snd
  have hT : Measurable fun ω : ((Site d → ℤ) × (Label d × ℕ → ℝ)) ×
      Parking.RoundNoise d => ((ω.1.1, Parking.matchedMoves ω.1.1 ω.1.2 ω.2, ω.1.2) :
        Parking.PData d) := (measurable_fst.comp measurable_fst).prodMk
      (hm.prodMk (measurable_snd.comp measurable_fst))
  simp_rw [Parking.matchedObservables_eq]
  change Measure.map (Parking.particleObservables ∘ _) _ = _
  rw [← Measure.map_map Parking.measurable_particleObservables hT,
    Parking.map_matchedData hd]
  exact (Parking.constructionsAgree' d hd ν inferInstance).symm

/-- Initial data for two configurations coupled by the same round tables. -/
abbrev Parking.CoupledData (d : ℕ) :=
  ((Site d → ℤ × ℤ) × (Label d × ℕ → ℝ)) × Parking.RoundNoise d

def Parking.coupledConf (b : Bool) (η : Site d → ℤ × ℤ) : Site d → ℤ :=
  fun x => if b then (η x).2 else (η x).1

theorem Parking.measurable_coupledConf (b : Bool) :
    Measurable (Parking.coupledConf (d := d) b) := by
  cases b <;> fun_prop [Parking.coupledConf]

def Parking.coupledLaw (d : ℕ) (ν : Measure ℤ) (p : ℝ≥0∞) :
    Measure (Parking.CoupledData d) :=
  ((Parking.resampleLaw d ν p).prod (LatticeProb.rankLaw d)).prod (Parking.roundNoiseLaw d)

theorem Parking.coupledLaw_isProbability (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1) :
    IsProbabilityMeasure (Parking.coupledLaw d ν p) := by
  haveI := Parking.resampleOne_isProbability ν hp
  haveI := LatticeProb.rankLaw_isProbability d
  haveI := Parking.roundNoiseLaw_isProbability hd
  unfold Parking.coupledLaw Parking.resampleLaw LatticeProb.iidLaw
  infer_instance

def Parking.coupledProjection (b : Bool) (ω : Parking.CoupledData d) :
    ((Site d → ℤ) × (Label d × ℕ → ℝ)) × Parking.RoundNoise d :=
  ((Parking.coupledConf b ω.1.1, ω.1.2), ω.2)

theorem Parking.measurable_coupledProjection (b : Bool) :
    Measurable (Parking.coupledProjection (d := d) b) :=
  (((Parking.measurable_coupledConf b).comp (measurable_fst.comp measurable_fst)).prodMk
    (measurable_snd.comp measurable_fst)).prodMk measurable_snd

theorem Parking.map_coupledProjection (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1) (b : Bool) :
    (Parking.coupledLaw d ν p).map (Parking.coupledProjection b) =
      (((LatticeProb.iidLaw d ν).prod (LatticeProb.rankLaw d)).prod
        (Parking.roundNoiseLaw d)) := by
  haveI := Parking.resampleOne_isProbability ν hp
  haveI : IsProbabilityMeasure (Parking.resampleLaw d ν p) := by
    unfold Parking.resampleLaw LatticeProb.iidLaw
    infer_instance
  haveI := LatticeProb.rankLaw_isProbability d
  haveI := Parking.roundNoiseLaw_isProbability hd
  have hconf : (Parking.resampleLaw d ν p).map (Parking.coupledConf b) =
      LatticeProb.iidLaw d ν := by
    cases b
    · exact Parking.resampleLaw_map_fst ν hp
    · exact Parking.resampleLaw_map_snd ν hp
  change Measure.map (Prod.map (Prod.map (Parking.coupledConf b) id) id) _ = _
  unfold Parking.coupledLaw
  rw [← Measure.map_prod_map _ _ ((Parking.measurable_coupledConf b).prodMap measurable_id)
      measurable_id, Measure.map_id,
    ← Measure.map_prod_map _ _ (Parking.measurable_coupledConf b) measurable_id,
    Measure.map_id, hconf]

def Parking.coupledState (ω : Parking.CoupledData d) (b : Bool) : ℕ → State d :=
  Parking.matchedState (Parking.coupledConf b ω.1.1) ω.1.2 ω.2

/-- The full particle driving data received by either marginal. -/
def Parking.coupledParticleData (b : Bool) (ω : Parking.CoupledData d) : Parking.PData d :=
  (Parking.coupledConf b ω.1.1,
    Parking.matchedMoves (Parking.coupledConf b ω.1.1) ω.1.2 ω.2, ω.1.2)

theorem Parking.pState_coupledParticleData (b : Bool) (ω : Parking.CoupledData d) (t : ℕ) :
    Parking.pState (Parking.toPDriver (Parking.coupledParticleData b ω)) t =
      Parking.coupledState ω b t :=
  Parking.pState_matchedMoves _ _ _ t

/-- The complete marginal driver has the ordinary particle law. The pathwise
state identity therefore transfers any measurable state event, including positions. -/
theorem Parking.map_coupledParticleData (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1) (b : Bool) :
    (Parking.coupledLaw d ν p).map (Parking.coupledParticleData b) = Parking.pDataLaw d ν := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw
    infer_instance
  have hm := Parking.measurable_matchedMoves ⟨0, hd⟩
    (Ω := ((Site d → ℤ) × (Label d × ℕ → ℝ)) × Parking.RoundNoise d)
    (fun ω => ω.1.1) (fun ω => ω.1.2) Prod.snd
    (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst) measurable_snd
  have hT : Measurable fun ω : ((Site d → ℤ) × (Label d × ℕ → ℝ)) ×
      Parking.RoundNoise d => ((ω.1.1, Parking.matchedMoves ω.1.1 ω.1.2 ω.2, ω.1.2) :
        Parking.PData d) := (measurable_fst.comp measurable_fst).prodMk
      (hm.prodMk (measurable_snd.comp measurable_fst))
  have heq : Parking.coupledParticleData b =
      (fun ω => ((ω.1.1, Parking.matchedMoves ω.1.1 ω.1.2 ω.2, ω.1.2) : Parking.PData d)) ∘
        Parking.coupledProjection b := rfl
  rw [heq, ← Measure.map_map hT (Parking.measurable_coupledProjection b),
    Parking.map_coupledProjection hd ν hp b]
  exact Parking.map_matchedData hd (LatticeProb.iidLaw d ν)

def Parking.coupledObservables (b : Bool) (ω : Parking.CoupledData d) :
    Parking.ProcessObservables d :=
  Parking.matchedObservables (Parking.coupledConf b ω.1.1) ω.1.2 ω.2

/-- Both processes have the original law for the full count history, even
though every matched pair uses a common instruction. -/
theorem Parking.map_coupledObservables (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1) (b : Bool) :
    (Parking.coupledLaw d ν p).map (Parking.coupledObservables b) =
      (Parking.law d ν).map (fun ω =>
        (fun tx : ℕ × Site d => Parking.U ω tx.1 tx.2,
         fun tx : ℕ × Site d => Parking.A ω tx.1 tx.2,
         fun tx : ℕ × Site d => Parking.H ω tx.1 tx.2,
         fun ti : ℕ × Label d => (LatticeProb.state (Parking.toDriver ω) ti.1).active ti.2)) := by
  have hm := Parking.measurable_matchedObservables ⟨0, hd⟩
    (Ω := ((Site d → ℤ) × (Label d × ℕ → ℝ)) × Parking.RoundNoise d)
    (fun ω => ω.1.1) (fun ω => ω.1.2) Prod.snd
    (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst) measurable_snd
  change Measure.map ((fun ω => Parking.matchedObservables ω.1.1 ω.1.2 ω.2) ∘
    Parking.coupledProjection b) _ = _
  rw [← Measure.map_map hm (Parking.measurable_coupledProjection b),
    Parking.map_coupledProjection hd ν hp b]
  exact Parking.map_matchedObservables hd ν

end
