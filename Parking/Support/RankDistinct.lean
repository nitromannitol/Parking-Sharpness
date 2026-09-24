/-
The uniform variables are almost surely pairwise distinct.

The arrivals at a site fill the holes there in increasing order of their uniform
variables, and the construction breaks a tie of equal variables by the labels of
the two particles.  On the set where the variables are pairwise distinct that
clause is never consulted, and the set carries the whole mass: the coordinates
are independent and their common law is atomless, so a countable union of null
sets covers the complement.
-/
import Parking.Support.Pathwise
import LatticeProb.Invariance

noncomputable section

namespace Parking

open MeasureTheory ProbabilityTheory

/-- The one-coordinate law of the uniform variables. -/
def unitLaw : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unitLaw := by
  constructor
  rw [unitLaw, Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

theorem unitLaw_singleton (x : ℝ) : unitLaw {x} = 0 := by
  have h : unitLaw {x} ≤ volume {x} := Measure.restrict_le_self {x}
  rw [Real.volume_singleton] at h
  exact nonpos_iff_eq_zero.mp h

theorem rankLaw_eq_infinitePi (d : ℕ) :
    LatticeProb.rankLaw d = Measure.infinitePi fun _ : LatticeProb.Label d × ℕ => unitLaw := rfl

/-- The coordinates of the uniform variables are independent. -/
theorem map_rank_eval (d : ℕ) (i : LatticeProb.Label d × ℕ) :
    (LatticeProb.rankLaw d).map (fun ρ : LatticeProb.Label d × ℕ → ℝ => ρ i) = unitLaw := by
  rw [rankLaw_eq_infinitePi]
  exact (measurePreserving_eval_infinitePi (fun _ : LatticeProb.Label d × ℕ => unitLaw) i).map_eq

/-- The coordinates of the uniform variables are independent. -/
theorem iIndepFun_rank (d : ℕ) :
    iIndepFun (fun (i : LatticeProb.Label d × ℕ) (ρ : LatticeProb.Label d × ℕ → ℝ) => ρ i)
      (LatticeProb.rankLaw d) := by
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : ∀ i : LatticeProb.Label d × ℕ,
      IsProbabilityMeasure ((LatticeProb.rankLaw d).map
        (fun ρ : LatticeProb.Label d × ℕ → ℝ => ρ i)) := by
    intro i
    rw [map_rank_eval d i]
    infer_instance
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun i => measurable_pi_apply i),
    Measure.map_id']
  rw [rankLaw_eq_infinitePi]
  congr 1
  funext i
  rw [← rankLaw_eq_infinitePi, map_rank_eval d i]

/-- Two distinct coordinates agree on a null set. -/
theorem rankLaw_pair_eq_zero (d : ℕ) {a b : LatticeProb.Label d × ℕ} (hab : a ≠ b) :
    LatticeProb.rankLaw d {ρ : LatticeProb.Label d × ℕ → ℝ | ρ a = ρ b} = 0 := by
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  have hdiag : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  have hind : IndepFun (fun ρ : LatticeProb.Label d × ℕ → ℝ => ρ a)
      (fun ρ : LatticeProb.Label d × ℕ → ℝ => ρ b) (LatticeProb.rankLaw d) :=
    (iIndepFun_rank d).indepFun hab
  have hmap : (LatticeProb.rankLaw d).map
        (fun ρ : LatticeProb.Label d × ℕ → ℝ => (ρ a, ρ b))
      = unitLaw.prod unitLaw := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply a).aemeasurable
      (measurable_pi_apply b).aemeasurable).mp hind, map_rank_eval d a, map_rank_eval d b]
  have hpre : {ρ : LatticeProb.Label d × ℕ → ℝ | ρ a = ρ b}
      = (fun ρ : LatticeProb.Label d × ℕ → ℝ => (ρ a, ρ b)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} := rfl
  rw [hpre, ← Measure.map_apply ((measurable_pi_apply a).prodMk (measurable_pi_apply b)) hdiag,
    hmap, Measure.prod_apply hdiag]
  have hslice : ∀ x : ℝ, (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = ({x} : Set ℝ) := by
    intro x
    ext y
    simp [eq_comm]
  simp only [hslice, unitLaw_singleton, lintegral_zero]

/-- **The uniform variables are almost surely pairwise distinct.** -/
theorem rankLaw_ae_injective (d : ℕ) :
    ∀ᵐ ρ ∂(LatticeProb.rankLaw d), Function.Injective ρ := by
  have hall : ∀ᵐ ρ ∂(LatticeProb.rankLaw d),
      ∀ a b : LatticeProb.Label d × ℕ, a ≠ b → ρ a ≠ ρ b := by
    rw [ae_all_iff]
    intro a
    rw [ae_all_iff]
    intro b
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall fun ρ hne => absurd hab hne
    · have h0 := rankLaw_pair_eq_zero d hab
      have hae : ∀ᵐ ρ ∂(LatticeProb.rankLaw d), ρ a ≠ ρ b := by
        rw [ae_iff]
        simpa using h0
      filter_upwards [hae] with ρ hρ _
      exact hρ
  filter_upwards [hall] with ρ hρ a b hab
  by_contra hne
  exact hρ a b hne hab

/-- **The driving data of the particle-driven construction almost surely has
pairwise distinct uniform variables.** -/
theorem ae_injective_pDataLaw {d : ℕ} (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] :
    ∀ᵐ ω ∂(pDataLaw d ν), Function.Injective ω.2.2 := by
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
    (measurable_snd.comp measurable_snd).aemeasurable ?_
  rw [hmap]
  exact rankLaw_ae_injective d

end Parking

end
