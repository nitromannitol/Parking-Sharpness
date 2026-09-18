/-
The finite-dimensional convergence in law (`hfdd`) and the equicontinuity in probability
(`htight`) of the rescaled box-reward field, read at box points through `Parking.boxToFin`,
against the everywhere-continuous noise modification `Parking.Support.TightNoiseModification`'s
`hgc`: exactly the two probabilistic hypotheses
`LatticeProb.tendsto_integral_of_fdd_of_equicontinuous'` needs, with `E := rewardBox T A` and
`K := Set.univ`.

`hfdd` transports `Parking.tendstoInDistribution_orientedBoxReward` (finite-dimensional
convergence to `contZ`) to the modification `Y` by the exact a.e. equality `hgc` supplies at
every point of `orientedBox T A`, via `MeasureTheory.TendstoInDistribution.congr`: a finite
conjunction of a.e. equalities is again an a.e. equality of the vector-valued functions
(`Filter.eventually_all`).

`htight` reads `Parking.orientedBoxReward_modulusInProbability`, stated on the metric of
`Fin 2 → ℝ`, on the metric of `rewardBox T A` instead, using that `Parking.boxToFin` does not
increase distances (`Parking.dist_boxToFin_le`): a pair of box points closer than `δ` reads as
a pair of plane points closer than `δ`.
-/
import Parking.Support.TightFddAssembly
import Parking.Support.TightHlawLift
import Parking.Support.TightNoiseModification
import Parking.Support.TightEquicont

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

variable {T A : ℝ}

/-! ### `hfdd` -/

/-- **Finite-dimensional convergence in law of the rescaled box-reward field, read at box
points, to the everywhere-continuous noise modification `Y` of `hgc`.** -/
theorem tendstoInDistribution_orientedBoxReward_boxToFin (ν : Measure ℤ) (hν : CriticalLaw ν)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure (realLaw ν)]
    [IsProbabilityMeasure (iidLaw 2 (realLaw ν))]
    (hBinomial : External.BinomialLocalCLT) (hT : 0 ≤ T) (hA : 0 ≤ A)
    {Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ}
    (hYmod : ∀ z ∈ orientedBox T A,
      contZ (∫ x : ℝ, x ^ 2 ∂(realLaw ν)) T (z 0) (z 1) =ᵐ[contNoiseLaw] Y z)
    {m : ℕ} (x : Fin m → rewardBox T A) :
    TendstoInDistribution (fun n ω k => orientedBoxReward T n ω (boxToFin T A (x k))) atTop
      (fun ω k => Y (boxToFin T A (x k)) ω) (fun _ : ℕ => iidLaw 2 (realLaw ν)) contNoiseLaw := by
  set u : Fin m → Fin 2 → ℝ := fun k => boxToFin T A (x k) with hudef
  have hu0 : ∀ l, 0 ≤ u l 0 := fun l => (Set.mem_Icc.mp (x l).1.2).1
  have huT : ∀ l, u l 0 ≤ T := fun l => (Set.mem_Icc.mp (x l).1.2).2
  have hbase := tendstoInDistribution_orientedBoxReward ν hν hBinomial T u hu0 huT
  have hpt : ∀ k : Fin m, (fun ω => contZ (∫ x : ℝ, x ^ 2 ∂(realLaw ν)) T (u k 0) (u k 1) ω)
      =ᵐ[contNoiseLaw] fun ω => Y (u k) ω :=
    fun k => hYmod (u k) (boxToFin_mem_orientedBox T hT A hA (x k))
  have hall : ∀ᵐ ω ∂contNoiseLaw,
      ∀ k : Fin m, contZ (∫ x : ℝ, x ^ 2 ∂(realLaw ν)) T (u k 0) (u k 1) ω = Y (u k) ω :=
    Filter.eventually_all.2 hpt
  have hcongr : (fun ω k => contZ (∫ x : ℝ, x ^ 2 ∂(realLaw ν)) T (u k 0) (u k 1) ω)
      =ᵐ[contNoiseLaw] fun ω k => Y (u k) ω := by
    filter_upwards [hall] with ω hω
    funext k
    exact hω k
  exact hbase.congr (fun _ => Filter.EventuallyEq.rfl) hcongr

/-! ### `htight` -/

/-- **Equicontinuity in probability of the rescaled box-reward field, read at box points.** -/
theorem htight_orientedBoxReward_boxToFin (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 8 < p) (hT : 0 ≤ T) (hA : 0 ≤ A) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      iidLaw 2 (realLaw ν) {ω : Site 2 → ℝ | ∃ z ∈ (Set.univ : Set (rewardBox T A)),
        ∃ y ∈ (Set.univ : Set (rewardBox T A)), dist z y < δ ∧
          η < |orientedBoxReward T n ω (boxToFin T A z) -
            orientedBoxReward T n ω (boxToFin T A y)|} ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hmod⟩ := orientedBoxReward_modulusInProbability ν hν p hp T A hT hA ε η hε hη
  refine ⟨δ, hδ, Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩⟩
  refine le_trans (measure_mono ?_) (hmod n hn)
  rintro ω ⟨z, -, y, -, hzy, hval⟩
  refine ⟨boxToFin T A z, boxToFin_mem_orientedBox T hT A hA z,
    boxToFin T A y, boxToFin_mem_orientedBox T hT A hA y, ?_, hval⟩
  exact lt_of_le_of_lt (dist_boxToFin_le T A z y) hzy

end Parking

end
