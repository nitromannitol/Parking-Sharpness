/-
The joint law of the initial configuration and particle odometer.
-/
import Parking.Support.CoupledLaw

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The initial configuration and a terminal odometer have the same joint law in both constructions. -/
theorem map_conf_pOdometer (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) (x : Site d) :
    (pDataLaw d ν).map (fun ω : Parking.PData d => (ω.1, pOdometer (toPDriver ω) n x)) =
      (law d ν).map (fun ω : Data d => (ω.1, U ω n x)) := by
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  let proj : (Site d → ℤ) × ProcessObservables d → (Site d → ℤ) × ℕ :=
    fun z => (z.1, z.2.1 (n, x))
  have hp : Measurable proj := measurable_fst.prodMk
    ((measurable_pi_apply (n, x)).comp (measurable_fst.comp measurable_snd))
  have hconf := congrArg (fun μ => Measure.map proj μ) (constructionsAgree_conf d hd (iidLaw d ν))
  rw [Measure.map_map hp (measurable_fst.prodMk measurable_stackObservables),
    Measure.map_map hp (measurable_fst.prodMk measurable_pObservables)] at hconf
  haveI := stepLaw_isProbability hd
  let recode : Parking.PData d → LatticeProb.PData d :=
    fun ω => (ω.1, (fun q => stepVec (ω.2.1 q)), ω.2.2)
  have hrec : Measurable recode := measurable_fst.prodMk
    ((measurable_pi_lambda _ fun q => (measurable_from_countable' stepVec).comp
      ((measurable_pi_apply q).comp (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd))
  have hmap : (Parking.pDataLaw d ν).map recode = LatticeProb.pDataLaw d ν :=
    LatticeProb.map_pDataLaw_of_map (stepLaw d) stepVec (measurable_from_countable' _)
      map_stepLaw_stepVec ν hd
  have hobs : ∀ ω : Parking.PData d,
      pOdometer (toPDriver ω) n x = (LatticeProb.pObservables (recode ω)).1 (n, x) := by
    intro ω
    exact congrArg (fun S : State d => S.departures x) (pState_stepVec ω.1 ω.2.1 ω.2.2 n)
  calc
    (Parking.pDataLaw d ν).map (fun ω => (ω.1, pOdometer (toPDriver ω) n x))
        = (Parking.pDataLaw d ν).map (fun ω => proj ((recode ω).1,
            LatticeProb.pObservables (recode ω))) := by simp only [hobs]; rfl
    _ = ((Parking.pDataLaw d ν).map recode).map
          (fun ω : LatticeProb.PData d => proj (ω.1, LatticeProb.pObservables ω)) := by
      exact (Measure.map_map (hp.comp (measurable_fst.prodMk measurable_pObservables)) hrec).symm
    _ = (law d ν).map (fun ω : Data d => (ω.1, U ω n x)) := by
      rw [hmap]
      exact hconf.symm
end Parking
