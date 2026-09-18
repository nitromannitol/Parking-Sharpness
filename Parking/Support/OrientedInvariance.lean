/- Translation invariance of the directed particle law. -/
import Parking.Support.OrientedLaw
import Parking.Support.Invariance

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem orientedInstructionLaw_map_sub (v y : Site d) :
    (orientedInstructionLaw (y + v)).map (fun z : Site d => z - v) = orientedInstructionLaw y := by
  have hm : Measurable (fun z : Site d => z - v) := measurable_id.sub measurable_const
  simp only [orientedInstructionLaw]
  rw [Measure.map_smul, Measure.map_finset_sum' hm.aemeasurable]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [Measure.map_dirac' hm, show y + v + unit i - v = y + unit i by abel]

theorem orientedStackLaw_map_shiftStack (hd : 1 ≤ d) (v : Site d) :
    (orientedStackLaw d).map (shiftStack v) = orientedStackLaw d := by
  haveI : ∀ y : Site d, IsProbabilityMeasure (orientedInstructionLaw y) :=
    fun y => orientedInstructionLaw_isProbability hd y
  have hinj : Function.Injective fun q : Site d × ℕ => (q.1 + v, q.2) := by
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (add_right_cancel h.1) h.2
  have h1 : (orientedStackLaw d).map
      (fun σ : Site d × ℕ → Site d => fun q : Site d × ℕ => σ (q.1 + v, q.2)) =
      Measure.infinitePi fun q : Site d × ℕ => orientedInstructionLaw (q.1 + v) :=
    Measure.map_infinitePi_infinitePi_of_inj (P := fun q : Site d × ℕ => orientedInstructionLaw q.1) hinj
  have hm : Measurable (fun z : Site d => z - v) := measurable_id.sub measurable_const
  have h2 : (Measure.infinitePi fun q : Site d × ℕ => orientedInstructionLaw (q.1 + v)).map
      (fun σ : Site d × ℕ → Site d => fun q : Site d × ℕ => σ q - v) =
      Measure.infinitePi fun q : Site d × ℕ =>
        (orientedInstructionLaw (q.1 + v)).map (fun z : Site d => z - v) :=
    Measure.infinitePi_map_pi _ (f := fun _ : Site d × ℕ => fun z : Site d => z - v) (fun _ => hm)
  have hcomp : shiftStack (d := d) v =
      (fun σ : Site d × ℕ → Site d => fun q : Site d × ℕ => σ q - v) ∘
        (fun σ : Site d × ℕ → Site d => fun q : Site d × ℕ => σ (q.1 + v, q.2)) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1, h2]
  simp only [orientedInstructionLaw_map_sub, orientedStackLaw]

theorem orientedLaw_map_shiftData (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (v : Site d) : (orientedLaw d ν).map (shiftData v) = orientedLaw d ν := by
  haveI := orientedStackLaw_isProbability hd
  haveI := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  rw [orientedLaw, shiftData_eq_prodMap,
    ← Measure.map_prod_map _ _ (measurable_shiftConf v)
      ((measurable_shiftStack v).prodMap (measurable_shiftRank v)),
    iidLaw_map_shiftConf' ν v,
    ← Measure.map_prod_map _ _ (measurable_shiftStack v) (measurable_shiftRank v),
    orientedStackLaw_map_shiftStack hd v, rankLaw_map_shiftRank v]

theorem orientedLaw_map_conf (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    (orientedLaw d ν).map (Prod.fst : Data d → Site d → ℤ) = iidLaw d ν := by
  haveI := orientedStackLaw_isProbability hd
  haveI := LatticeProb.rankLaw_isProbability d
  rw [orientedLaw, Measure.map_fst_prod]
  simp

end Parking
