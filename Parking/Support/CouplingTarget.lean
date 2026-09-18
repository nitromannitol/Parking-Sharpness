/-
What Steps 1 and 2 of `lem:critical-density` (`parking.tex:1250-1319`) owe the
rest of the proof, and the reduction of the lemma to it.

The paper's Step 3 opens with the hitting sum

    ∑_{z ≠ 0} P_z(T_0 ≤ 2t) = E_0|R_{2t}| - 1 ≤ 2t ,

which `RangeHitting.lean` proves, and closes with

    4 S_t ≥ ε - (ε²/2)(E_0|R_{2t}| - 1) ≥ ε - t ε²   for every 0 ≤ ε ≤ γ .

The middle inequality is everything the coupling has to deliver: the expected
number of labels created at the origin is `ε`
(`Parking.integral_absDiff_resampleOne` at `p = ε/γ`), the expected number that
disappear by time `t` is at most `ε²/2` per pair of opposite labels
(`Parking.integral_dNeg_mul_dPos`) times the chance that a simple random walk
started at the other label's site hits the origin within `2t` steps, and by mass
transport the labels that remain are among the active particles and unfilled
holes of the two processes at the origin, of which there are `4 S_t` in the mean.

`Parking.coupling_bound` names that inequality, `Parking.quadratic_of_coupling`
turns it into the quadratic bound, and `Parking.critical_density_of_coupling`
turns the quadratic bound into both conclusions of the lemma with `c = 1/16`.
-/
import Parking.Support.ResamplePairs
import Parking.Support.RangeHitting
import Parking.Frozen.ActivityHoles
import Parking.Support.CriticalChain

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Parking

open LatticeProb

variable {d : ℕ}

/-! ### The hitting sum -/

/-- `∑_{z ≠ 0} P_z(T_0 ≤ t)`, the sum of the paper's Step 3. -/
def hitSum (d : ℕ) (t : ℕ) : ℝ≥0∞ :=
  ∑' z : Site d, (if z = 0 then 0 else (walkLaw d) {p | ∃ j ≤ t, walkPath z p j = 0})

theorem hitSum_le (hd : 1 ≤ d) (t : ℕ) : hitSum d t ≤ (t : ℝ≥0∞) :=
  tsum_hitZero_le hd t

theorem hitSum_ne_top (hd : 1 ≤ d) (t : ℕ) : hitSum d t ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top t) (hitSum_le hd t)

/-- The hitting sum in the reals, bounded by the number of steps. -/
theorem hitSum_toReal_le (hd : 1 ≤ d) (t : ℕ) : (hitSum d t).toReal ≤ (t : ℝ) := by
  have h := hitSum_le hd t
  have := ENNReal.toReal_mono (ENNReal.natCast_ne_top t) h
  simpa using this

theorem hitSum_toReal_nonneg (t : ℕ) : 0 ≤ (hitSum d t).toReal := ENNReal.toReal_nonneg


/-! ### The four-way count at the origin -/

/-- **`E A_t(0) + E H_t(0) + E Ã_t(0) + E H̃_t(0) = 4 S_t`.**  The last identity of
the paper's Step 3.  Both coupled processes carry the original law, so each of
the four means is `S_t`: the mean number of active particles at the origin is the
mean number of origin particles still active, by the mass transport principle
(`lem:transport`), and the mean numbers of active particles and of unfilled holes
at the origin differ by the mean of the configuration there
(`lem:activity-holes`), which vanishes. -/
theorem mean_A_and_H_eq_S (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν = 0) (t : ℕ) :
    ∫ ω, (A ω t 0 : ℝ) ∂(law d ν) = S (law d ν) t ∧
      ∫ ω, (H ω t 0 : ℝ) ∂(law d ν) = S (law d ν) t := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hmap : (LatticeProb.iidLaw d ν).map (fun η : Site d → ℤ => η 0) = ν := by
    show (MeasureTheory.Measure.infinitePi fun _ : Site d => ν).map
      (fun η : Site d → ℤ => η 0) = ν
    exact Measure.infinitePi_map_eval _ 0
  have hint0 : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) (LatticeProb.iidLaw d ν) := by
    refine (integrable_map_measure (g := fun k : ℤ => |(k : ℝ)|)
      (f := fun η : Site d → ℤ => η 0) (μ := LatticeProb.iidLaw d ν) ?_
      (measurable_pi_apply (0 : Site d)).aemeasurable).mp ?_
    · rw [hmap]; exact hint.aestronglyMeasurable
    · rw [hmap]; exact hint
  have hti : TranslationInvariant (LatticeProb.iidLaw d ν) :=
    fun v => iidLaw_map_shiftConf' ν v
  have hlaw : law d ν = dataLaw d (LatticeProb.iidLaw d ν) := rfl
  have hAS : ∫ ω, (A ω t 0 : ℝ) ∂(law d ν) = S (law d ν) t :=
    ((Parking.Frozen.transport d hd ν inferInstance hint).1 t).2.2
  refine ⟨hAS, ?_⟩
  have hah := Parking.Frozen.activity_holes d hd (LatticeProb.iidLaw d ν) inferInstance hti hint0 t
  have hconf : ∫ η, ((η 0 : ℤ) : ℝ) ∂(LatticeProb.iidLaw d ν) = 0 := by
    have h := integral_map (μ := LatticeProb.iidLaw d ν) (φ := fun η : Site d → ℤ => η 0)
      (f := fun k : ℤ => (k : ℝ)) (measurable_pi_apply (0 : Site d)).aemeasurable
      (measurable_from_countable' fun k : ℤ => (k : ℝ)).aestronglyMeasurable
    rw [hmap] at h
    rw [h] at hmean
    exact hmean
  rw [← hlaw] at hah
  have hdiff := hah.2.2
  rw [hconf] at hdiff
  rw [hAS] at hdiff
  linarith


/-- **The cancellation sum of Step 3.**  If the mean number of labels created at
the origin that are cancelled against a label at `z` is at most `a` times the
chance that a walk from `z` reaches the origin within `2t` steps, and no label
cancels against one at its own site, then the total is at most `2 t a`.  With
`a = ε²/2` this is the paper's `(ε²/2)(E_0|R_{2t}| - 1) ≤ t ε²`. -/
theorem tsum_cancel_le (hd : 1 ≤ d) (t : ℕ) (a : ℝ≥0∞) (canc : Site d → ℝ≥0∞)
    (h0 : canc 0 = 0)
    (h : ∀ z : Site d, z ≠ 0 →
      canc z ≤ a * (walkLaw d) {p | ∃ j ≤ 2 * t, walkPath z p j = 0}) :
    ∑' z : Site d, canc z ≤ a * (2 * (t : ℝ≥0∞)) := by
  classical
  have hterm : ∀ z : Site d, canc z
      ≤ a * (if z = 0 then 0 else (walkLaw d) {p | ∃ j ≤ 2 * t, walkPath z p j = 0}) := by
    intro z
    by_cases hz : z = 0
    · rw [hz, h0]; simp
    · rw [if_neg hz]; exact h z hz
  calc ∑' z : Site d, canc z
      ≤ ∑' z : Site d,
          a * (if z = 0 then 0 else (walkLaw d) {p | ∃ j ≤ 2 * t, walkPath z p j = 0}) :=
        ENNReal.tsum_le_tsum hterm
    _ = a * hitSum d (2 * t) := by rw [hitSum, ENNReal.tsum_mul_left]
    _ ≤ a * ((2 * t : ℕ) : ℝ≥0∞) := by
        exact mul_le_mul_right (hitSum_le hd (2 * t)) a
    _ = a * (2 * (t : ℝ≥0∞)) := by push_cast; ring

/-! ### The obligation of the coupling -/

/-- **What Steps 1 and 2 have to deliver.**  For every horizon and every size of
the resampling, the mean number of active particles and unfilled holes at the
origin in the two coupled processes is at least the mean number of labels created
at the origin minus the mean number of those that have been cancelled by an
opposite label. -/
def CouplingBound (d : ℕ) (ν : Measure ℤ) : Prop :=
  ∀ (t : ℕ) (ε : ℝ), 0 ≤ ε → ε ≤ gammaOf ν →
    ε - (ε ^ 2 / 2) * (hitSum d (2 * t)).toReal ≤ 4 * S (law d ν) t

/-- The quadratic bound `4 S_t ≥ ε - t ε²` of the paper's Step 3, from the
coupling and the hitting sum. -/
theorem quadratic_of_coupling (hd : 1 ≤ d) (ν : Measure ℤ) (hcoup : CouplingBound d ν)
    (t : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hεγ : ε ≤ gammaOf ν) :
    ε - (t : ℝ) * ε ^ 2 ≤ 4 * S (law d ν) t := by
  refine le_trans ?_ (hcoup t ε hε hεγ)
  have hle : (hitSum d (2 * t)).toReal ≤ 2 * (t : ℝ) := by
    have h := hitSum_toReal_le hd (2 * t)
    have hcast : ((2 * t : ℕ) : ℝ) = 2 * (t : ℝ) := by push_cast; ring
    rwa [hcast] at h
  have hsq : 0 ≤ ε ^ 2 / 2 := by positivity
  nlinarith [hsq, hle]

/-- **`lem:critical-density` from the coupling.**  With `γ` positive for a
nonconstant law, the quadratic bound holds for every `ε` in `[0, γ]`, and the
choice `ε = 1/(2t)` past `t = 1/(2γ)` gives both conclusions with `c = 1/16`. -/
theorem critical_density_of_coupling (hd : 1 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) (hnc : ∀ k : ℤ, ν {k} ≠ 1)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hcoup : CouplingBound d ν) :
    (∀ᶠ t : ℕ in atTop, (1 / 16 : ℝ) ≤ (t : ℝ) * S (law d ν) t) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        (1 / 16 : ℝ) * Real.log n - C ≤ meanU (law d ν) n :=
  critical_density_of_quadratic hd ν hprob hint (gammaOf_pos ν hnc hint)
    (fun t ε hε hεγ => quadratic_of_coupling hd ν hcoup t ε hε hεγ)

end Parking

end
