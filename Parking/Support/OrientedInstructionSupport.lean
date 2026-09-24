/- Almost sure forward support of every directed particle instruction. -/
import Parking.Support.OrientedLaw
import Parking.Support.Exposure

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
open scoped ENNReal
variable {d : ℕ}

theorem orientedInstructionLaw_compl_forward (y : Site d) :
    orientedInstructionLaw y {z : Site d | ∃ i : Fin d, z = y + unit i}ᶜ = 0 := by
  simp only [orientedInstructionLaw, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply]
  have hz (i : Fin d) : y + unit i ∉ {z : Site d | ∃ j : Fin d, z = y + unit j}ᶜ :=
    fun h => h ⟨i, rfl⟩
  rw [sum_eq_zero (fun i _ => Set.indicator_of_notMem (hz i) _)]
  simp

theorem orientedStackLaw_ae_forward (hd : 1 ≤ d) :
    ∀ᵐ σ ∂(orientedStackLaw d), ∀ q : Site d × ℕ, ∃ i : Fin d, σ q = q.1 + unit i := by
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (orientedInstructionLaw q.1) :=
    fun q => orientedInstructionLaw_isProbability hd q.1
  rw [ae_all_iff]
  intro q
  apply ae_iff.mpr
  have hs : MeasurableSet {z : Site d | ∃ i : Fin d, z = q.1 + unit i}ᶜ :=
    (Set.to_countable _).measurableSet
  have he : {σ : Site d × ℕ → Site d | ¬∃ i : Fin d, σ q = q.1 + unit i} =
      (fun σ : Site d × ℕ → Site d => σ q) ⁻¹' {z : Site d | ∃ i : Fin d, z = q.1 + unit i}ᶜ := rfl
  rw [he, ← Measure.map_apply (measurable_pi_apply q) hs,
    show (orientedStackLaw d).map (fun σ : Site d × ℕ → Site d => σ q) = orientedInstructionLaw q.1 from
      Measure.infinitePi_map_eval _ q]
  exact orientedInstructionLaw_compl_forward q.1

theorem orientedLaw_ae_forward (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    ∀ᵐ ω ∂(orientedLaw d ν), ∀ q : Site d × ℕ, ∃ i : Fin d, ω.2.1 q = q.1 + unit i := by
  haveI := orientedStackLaw_isProbability hd
  haveI := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  have hr : ∀ᵐ r ∂((orientedStackLaw d).prod (rankLaw d)),
      ∀ q : Site d × ℕ, ∃ i : Fin d, r.1 q = q.1 + unit i :=
    (Measure.quasiMeasurePreserving_fst).ae (orientedStackLaw_ae_forward hd)
  exact (Measure.quasiMeasurePreserving_snd).ae hr

theorem orientedLaw_ae_nbr (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    ∀ᵐ ω ∂(orientedLaw d ν), ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1 := by
  refine (orientedLaw_ae_forward hd ν).mono fun ω hω q => ?_
  obtain ⟨i, hi⟩ := hω q
  rw [hi]
  exact mem_nbrFinset_add q.1 i

theorem oriented_U_succ_ae_eq_expOdometer (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (k : ℕ) (x : Site d) :
    (fun ω : Data d => U ω (k + 1) x) =ᵐ[orientedLaw d ν] fun ω : Data d => expOdometer d k ω x := by
  refine (orientedLaw_ae_nbr hd ν).mono fun ω hω => ?_
  have hpar := (parallel_of_labelOrder (D := toDriver ω) (labelOrder d) hω).2 k x
  have hcast : (U ω (k + 1) x : ℤ) =
      max 0 (ω.1 x + ∑ y ∈ nbrFinset x, (arrivals ω.2.1 y x (U ω k y) : ℤ)) := hpar
  change U ω (k + 1) x = expOdometer d k ω x
  rw [expOdometer, ← hcast]
  simp

end Parking
