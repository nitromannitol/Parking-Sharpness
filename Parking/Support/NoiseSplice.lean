/-
The noise of the particle-driven construction, and revealing part of it.

The randomness of the model splits into three independent fields: the counts,
the walks of the labels and their uniform variables.  The law of the last two is
`noiseLaw`, and `pDataLaw` is the product of the law of the counts with it, so
the conditional covariance identity of `Support/CovCond.lean` splits a
covariance into the covariance of the two conditional means given the counts and
the mean of the conditional covariance given the counts, which is exactly how
Step 2 of `lem:product` (`parking.tex:2354-2357`) begins.

Revealing the walks and the uniform variables of a set of labels is `noiseComb`,
the splicing of BOTH fields along that set, and it is measure preserving for two
independent copies of the noise, so the martingale decomposition of
`Support/SpliceAvg.lean` applies to a filtration of such splicings.
-/
import Parking.Support.PairSplice
import Parking.Support.Range
import Parking.Support.Pathwise
import LatticeProb.Prob.Splice
import LatticeProb.Invariance
import Parking.Support.CovCond
import Parking.Support.RankDistinct

open MeasureTheory

noncomputable section

namespace Parking

open scoped Classical

/-- The noise of the particle-driven construction: the walks of the labels and
their uniform variables. -/
abbrev PNoise (d : ℕ) : Type := (Label d × ℕ → Fin d × Bool) × (Label d × ℕ → ℝ)

/-- The law of the noise. -/
def noiseLaw (d : ℕ) : Measure (PNoise d) := (moveLaw d).prod (LatticeProb.rankLaw d)

/-- Splicing the noise along a set of labels: the labels of `T` are read from
`ω` and every other label from the independent copy `η`. -/
def noiseComb {d : ℕ} (T : Set (Label d)) (ω η : PNoise d) : PNoise d :=
  (LatticeProb.comb {q : Label d × ℕ | q.1 ∈ T} ω.1 η.1,
    LatticeProb.comb {q : Label d × ℕ | q.1 ∈ T} ω.2 η.2)

/-- **The set where a measurable family of reals is injective is measurable.** -/
theorem measurableSet_injective_family {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {v : α → (ι → ℝ)} (hv : Measurable v) :
    MeasurableSet {ω : α | Function.Injective (v ω)} := by
  classical
  have hcoord : ∀ q : ι, Measurable fun ω : α => v ω q := fun q =>
    (measurable_pi_apply q).comp hv
  have hset : {ω : α | Function.Injective (v ω)}
      = ⋂ q : ι, ⋂ q' : ι, {ω : α | v ω q = v ω q' → q = q'} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Function.Injective]
  rw [hset]
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun q' => ?_
  by_cases hqq : q = q'
  · have huniv : {ω : α | v ω q = v ω q' → q = q'} = Set.univ := by
      ext ω; simp [hqq]
    rw [huniv]; exact MeasurableSet.univ
  · have heq : {ω : α | v ω q = v ω q' → q = q'} = {ω : α | v ω q = v ω q'}ᶜ := by
      ext ω; simp [hqq]
    rw [heq]
    exact (measurableSet_eq_fun (hcoord q) (hcoord q')).compl

/-- The set of noises whose uniform variables are pairwise distinct is measurable. -/
theorem measurableSet_injective_noise (d : ℕ) :
    MeasurableSet {b : PNoise d | Function.Injective b.2} :=
  measurableSet_injective_family (v := fun b : PNoise d => b.2) measurable_snd

/-- **The uniform variables of the noise are almost surely pairwise distinct.** -/
theorem noiseLaw_ae_injective {d : ℕ} (hd : 1 ≤ d) :
    ∀ᵐ b ∂(noiseLaw d), Function.Injective b.2 := by
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  have hmap : (noiseLaw d).map (Prod.snd : PNoise d → (Label d × ℕ → ℝ))
      = LatticeProb.rankLaw d := by
    unfold noiseLaw
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  refine ae_of_ae_map (f := (Prod.snd : PNoise d → (Label d × ℕ → ℝ)))
    measurable_snd.aemeasurable ?_
  rw [hmap]
  exact rankLaw_ae_injective d

theorem measurePreserving_noiseComb {d : ℕ} (hd : 1 ≤ d) (T : Set (Label d)) :
    MeasurePreserving (fun p : PNoise d × PNoise d => noiseComb T p.1 p.2)
      ((noiseLaw d).prod (noiseLaw d)) (noiseLaw d) := by
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    LatticeProb.uniformUnit_isProbability
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  exact measurePreserving_pairSplice (moveLaw d) (LatticeProb.rankLaw d)
    (LatticeProb.measurePreserving_comb (fun _ : Label d × ℕ => stepLaw d)
      {q : Label d × ℕ | q.1 ∈ T})
    (LatticeProb.measurePreserving_comb
      (fun _ : Label d × ℕ => MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
      {q : Label d × ℕ | q.1 ∈ T})

/-- The law of the particle-driven data is the product of the law of the counts
and the law of the noise. -/
theorem pDataLaw_eq_prod (d : ℕ) (ν : Measure ℤ) :
    pDataLaw d ν = (LatticeProb.iidLaw d ν).prod (noiseLaw d) := rfl

/-- **Splitting the counts from the particle randomness.**  The covariance under
the full law is the covariance of the two conditional means given the counts
plus the mean of the conditional covariance given the counts.  This is the
identity Step 2 of `lem:product` opens with, `parking.tex:2354-2357`. -/
theorem cov_pData_split (d : ℕ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (F Z : PData d → ℝ)
    (hFZ : Integrable (fun ω => F ω * Z ω) (pDataLaw d ν))
    (hF : Integrable F (pDataLaw d ν)) (hZ : Integrable Z (pDataLaw d ν))
    (hfz : Integrable (fun a => (∫ b, F (a, b) ∂(noiseLaw d)) * ∫ b, Z (a, b) ∂(noiseLaw d))
      (LatticeProb.iidLaw d ν)) :
    cov (pDataLaw d ν) F Z
      = cov (LatticeProb.iidLaw d ν) (fun a => ∫ b, F (a, b) ∂(noiseLaw d))
          (fun a => ∫ b, Z (a, b) ∂(noiseLaw d))
        + ∫ a, cov (noiseLaw d) (fun b => F (a, b)) (fun b => Z (a, b))
            ∂(LatticeProb.iidLaw d ν) := by
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    LatticeProb.uniformUnit_isProbability
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (noiseLaw d) := by unfold noiseLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  exact cov_prod_decomp (LatticeProb.iidLaw d ν) (noiseLaw d) F Z hFZ hF hZ hfz

/-- Reading a label of `T` from a splicing gives the first configuration. -/
theorem noiseComb_fst_of_mem {d : ℕ} {T : Set (Label d)} {ω η : PNoise d}
    {q : Label d × ℕ} (hq : q.1 ∈ T) : (noiseComb T ω η).1 q = ω.1 q := by
  simp [noiseComb, LatticeProb.comb, Set.mem_setOf_eq, hq]

/-- The same for the uniform variables. -/
theorem noiseComb_snd_of_mem {d : ℕ} {T : Set (Label d)} {ω η : PNoise d}
    {q : Label d × ℕ} (hq : q.1 ∈ T) : (noiseComb T ω η).2 q = ω.2 q := by
  simp [noiseComb, LatticeProb.comb, Set.mem_setOf_eq, hq]

theorem noiseComb_noiseComb {d : ℕ} {T T' : Set (Label d)} (hTT' : T ⊆ T')
    (b η η' : PNoise d) :
    noiseComb T (noiseComb T' b η) η' = noiseComb T b η' := by
  refine Prod.ext ?_ ?_ <;>
    · funext q
      by_cases hq : q.1 ∈ T
      · have hq' : q.1 ∈ T' := hTT' hq
        simp [noiseComb, LatticeProb.comb, Set.mem_setOf_eq, hq, hq']
      · simp [noiseComb, LatticeProb.comb, Set.mem_setOf_eq, hq]

theorem noiseComb_empty {d : ℕ} (b η : PNoise d) :
    noiseComb (∅ : Set (Label d)) b η = η := by
  refine Prod.ext ?_ ?_ <;>
    · funext q
      simp [noiseComb, LatticeProb.comb]

theorem readsParticles_noiseComb {d : ℕ} {F : PData d → ℝ} (hF : ReadsParticles F)
    (a : Site d → ℤ) (b η : PNoise d) (hb : Function.Injective b.2)
    (hc : Function.Injective (noiseComb {p : Label d | p.2 < (a p.1).toNat} b η).2) :
    F (a, noiseComb {p : Label d | p.2 < (a p.1).toNat} b η) = F (a, b) := by
  refine hF _ _ hc hb rfl ?_ ?_
  · intro q hq
    exact noiseComb_fst_of_mem (T := {p : Label d | p.2 < (a p.1).toNat}) hq
  · intro q hq
    exact noiseComb_snd_of_mem (T := {p : Label d | p.2 < (a p.1).toNat}) hq

/-- Splicing the counts along a set of sites is measure preserving. -/
theorem measurePreserving_countComb {d : ℕ} (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (S : Set (Site d)) :
    MeasurePreserving (fun p : (Site d → ℤ) × (Site d → ℤ) => LatticeProb.comb S p.1 p.2)
      ((LatticeProb.iidLaw d ν).prod (LatticeProb.iidLaw d ν)) (LatticeProb.iidLaw d ν) :=
  LatticeProb.measurePreserving_comb (fun _ : Site d => ν) S

/-- Revealing the counts and the walks and uniform variables of a set of labels:
the counts are kept and the noise is spliced. -/
def pDataComb {d : ℕ} (T : Set (Label d)) (ω η : PData d) : PData d :=
  (ω.1, noiseComb T ω.2 η.2)

theorem measurePreserving_pDataComb {d : ℕ} (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] (T : Set (Label d)) :
    MeasurePreserving (fun p : PData d × PData d => pDataComb T p.1 p.2)
      ((pDataLaw d ν).prod (pDataLaw d ν)) (pDataLaw d ν) := by
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    LatticeProb.uniformUnit_isProbability
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (noiseLaw d) := by unfold noiseLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  exact ((measurePreserving_fst (μ := LatticeProb.iidLaw d ν)
      (ν := LatticeProb.iidLaw d ν)).prod
    (measurePreserving_noiseComb hd T)).comp
    (measurePreserving_shuffle (LatticeProb.iidLaw d ν) (noiseLaw d))

/-- Reading a label outside `T` from a splicing gives the second configuration. -/
theorem noiseComb_fst_of_notMem {d : ℕ} {T : Set (Label d)} {ω η : PNoise d}
    {q : Label d × ℕ} (hq : q.1 ∉ T) : (noiseComb T ω η).1 q = η.1 q := by
  simp [noiseComb, LatticeProb.comb, Set.mem_setOf_eq, hq]

/-- The same for the uniform variables. -/
theorem noiseComb_snd_of_notMem {d : ℕ} {T : Set (Label d)} {ω η : PNoise d}
    {q : Label d × ℕ} (hq : q.1 ∉ T) : (noiseComb T ω η).2 q = η.2 q := by
  simp [noiseComb, LatticeProb.comb, Set.mem_setOf_eq, hq]

end Parking

end
