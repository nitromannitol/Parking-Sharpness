/-
The tagged uniform variables are almost surely pairwise distinct.

`Parking.survivalObs` no longer carries a guard, so the pairwise distinctness of
the uniform variables of the tagged realization is discharged where it is used:
in `FZ = 0`, Step 1 of `thm:subcritical`.  It needs three things, and the
realization supplies two of them almost surely.  Its own variables are pairwise
distinct (`Support/RankDistinct.lean`); they avoid any PRESCRIBED family, because
one coordinate meets a fixed real on a null set and there are countably many
pairs; and the prescribed family must itself be pairwise distinct, which is a
condition on it alone and holds for almost every prescription.
-/
import Parking.Support.RankDistinct
import Parking.Support.SubcriticalStep2

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Parking

variable {d : ℕ}

/-- A coordinate of the uniform variables meets a fixed real on a null set. -/
theorem rankLaw_eq_const_zero (d : ℕ) (a : LatticeProb.Label d × ℕ) (c : ℝ) :
    LatticeProb.rankLaw d {ρ : LatticeProb.Label d × ℕ → ℝ | ρ a = c} = 0 := by
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  have hpre : {ρ : LatticeProb.Label d × ℕ → ℝ | ρ a = c}
      = (fun ρ : LatticeProb.Label d × ℕ → ℝ => ρ a) ⁻¹' ({c} : Set ℝ) := rfl
  rw [hpre, ← Measure.map_apply (measurable_pi_apply a) (measurableSet_singleton c),
    map_rank_eval d a, unitLaw_singleton]

/-- **The uniform variables almost surely avoid a prescribed family.** -/
theorem rankLaw_ae_avoid (d : ℕ) (r : ℕ → ℝ) :
    ∀ᵐ ρ ∂(LatticeProb.rankLaw d),
      ∀ (s : ℕ) (q : LatticeProb.Label d × ℕ), r s ≠ ρ q := by
  rw [ae_all_iff]
  intro s
  rw [ae_all_iff]
  intro q
  have h0 := rankLaw_eq_const_zero d q (r s)
  rw [ae_iff]
  simpa [eq_comm] using h0

/-- The driving data almost surely avoids a prescribed family. -/
theorem ae_avoid_pDataLaw (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (r : ℕ → ℝ) :
    ∀ᵐ ω ∂(pDataLaw d ν), ∀ (s : ℕ) (q : LatticeProb.Label d × ℕ), r s ≠ ω.2.2 q := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  have hmap : (pDataLaw d ν).map (fun ω : PData d => ω.2.2) = LatticeProb.rankLaw d := by
    have h1 : (fun ω : PData d => ω.2.2) = Prod.snd ∘ Prod.snd := rfl
    rw [h1, ← Measure.map_map measurable_snd measurable_snd]
    unfold pDataLaw
    rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.map_snd_prod, measure_univ,
      one_smul]
  refine ae_of_ae_map (f := fun ω : PData d => ω.2.2)
    (p := fun ρ : LatticeProb.Label d × ℕ → ℝ =>
      ∀ (s : ℕ) (q : LatticeProb.Label d × ℕ), r s ≠ ρ q)
    (measurable_snd.comp measurable_snd).aemeasurable ?_
  rw [hmap]
  exact rankLaw_ae_avoid d r

/-- **The tagged uniform variables are almost surely pairwise distinct**, for a
prescribed family that is itself pairwise distinct. -/
theorem ae_injective_taggedRank (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {r : ℕ → ℝ} (hr : Function.Injective r) :
    ∀ᵐ ω ∂(pDataLaw d ν), Function.Injective (taggedRank r ω.2.2) := by
  filter_upwards [ae_injective_pDataLaw hd ν, ae_avoid_pDataLaw hd ν r] with ω h1 h2
  exact injective_taggedRank h1 hr fun s q => h2 s q

/-- **`FZ = 0` almost surely**, Step 1 of `thm:subcritical` under the law of the
driving data. -/
theorem ae_survivalObs_mul_holeObs (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (w : ℕ → Fin d × Bool) {r : ℕ → ℝ} (hr : Function.Injective r) (t : ℕ) :
    ∀ᵐ ω ∂(pDataLaw d ν), survivalObs w r t ω * holeObs w t ω = 0 := by
  filter_upwards [ae_injective_taggedRank hd ν hr] with ω hω
  exact survivalObs_mul_holeObs_of_injective w r t ω hω

end Parking

end
