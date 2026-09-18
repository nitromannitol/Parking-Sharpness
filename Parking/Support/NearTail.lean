/-
Step 1 of the upper bounds of `thm:near` (`parking.tex:2914-2929`).

"Let `L = log(e/δ)`.  Take `N = ⌈C δ^{-4}L^3⌉` in dimension one,
`⌈C δ^{-2}L^3⌉` in dimension two and `⌈C δ^{-2}L^2⌉` from dimension three on.
With `C` sufficiently large, Lemma 11.1 and Proposition 11.2 give
`∑_{t ≥ N} S_t^δ ≤ C` and `E U_∞^δ(0) ≤ E U_N^δ(0) + C`."

The threshold of `prop:resolvent` at the exponent `a = c δ²` of `lem:near-tilt` is
exactly the cutoff of `eq:near-cutoff`, since `a^{-2} = c^{-2}δ^{-4}`,
`a^{-1} = c^{-1}δ^{-2}` and `log(e/a)` is comparable to `L`.  The cutoff taken here
is the first integer past that threshold, so no constant has to be chosen: every
survivor count beyond it is bounded by the corresponding term of a series whose
total is at most one.
-/
import Parking.Support.NearTailSum
import Parking.Support.NearLowerLog
import Parking.Frozen.NearTilt
import Parking.Frozen.Resolvent
import Parking.Support.SubcriticalJointBound
import Parking.Support.NearDensity
import Parking.Support.Invariance
import Parking.Support.NearTiltInterval

open MeasureTheory LatticeProb
open scoped ENNReal

noncomputable section
namespace Parking
variable {d : ℕ}

/-- **Step 1 of the upper bounds of `thm:near`** (`parking.tex:2914-2929`).  Beyond the
threshold of `prop:resolvent` at the exponent `c δ²` of `lem:near-tilt`, the survivor
counts sum to a constant. -/
theorem exists_near_tail (hd : 1 ≤ d) {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ}
    (hfam : NearFamily δ₀ ν θ M K) :
    ∃ a Ct CR δ₁ : ℝ, 0 < a ∧ 0 < Ct ∧ 0 < CR ∧ 0 < δ₁ ∧ δ₁ ≤ δ₀ ∧
      ∀ δ ∈ Set.Ioc (0 : ℝ) δ₁, ∀ N : ℕ,
        Parking.resolventThreshold d CR (a * δ ^ 2) < (N : ℝ) →
        ∀ n : ℕ, ∑ s ∈ Finset.Ico N n, Parking.S (Parking.law d (ν δ)) s ≤ Ct := by
  obtain ⟨hδ₀, hθ, hprob, hmean, hnc, hexp, hcouple⟩ := id hfam
  obtain ⟨a, Ct, ha, hCt, δt, hδt, hδtδ₀, htilt⟩ :=
    Parking.Frozen.near_tilt d hd δ₀ ν θ M K hfam
  obtain ⟨cR, CR, hcR, hCR, -, htail⟩ := Parking.Frozen.resolvent d hd
  refine ⟨a, Ct, CR, min δt (Real.sqrt a⁻¹), ha, hCt, hCR,
    lt_min hδt (Real.sqrt_pos.mpr (by positivity)), le_trans (min_le_left _ _) hδtδ₀, ?_⟩
  intro δ hδ N hN n
  have hδ0 : 0 < δ := hδ.1
  have hδt' : δ ≤ δt := le_trans hδ.2 (min_le_left _ _)
  have hδs : δ ≤ Real.sqrt a⁻¹ := le_trans hδ.2 (min_le_right _ _)
  have hane : a * δ ^ 2 ≤ 1 := by
    have h1 : δ ^ 2 ≤ a⁻¹ := by
      have := Real.sq_sqrt (le_of_lt (inv_pos.mpr ha))
      nlinarith [Real.sqrt_nonneg a⁻¹, hδ0.le]
    calc a * δ ^ 2 ≤ a * a⁻¹ := by nlinarith
      _ = 1 := mul_inv_cancel₀ (ne_of_gt ha)
  have ha2 : 0 < a * δ ^ 2 := by positivity
  obtain ⟨hsum, htot⟩ := htail (a * δ ^ 2) ha2 hane
  refine sum_Ico_le_of_tsum hCt.le (fun t => rangeExp_nonneg d _ t)
    (fun t => (htilt δ ⟨hδ0, hδt'⟩ t).2) hN hsum htot n

/-- The cutoff `N` of `eq:near-cutoff`: the first integer past the threshold of
`prop:resolvent` at the exponent of `lem:near-tilt`. -/
def nearCutoff (d : ℕ) (CR a δ : ℝ) : ℕ :=
  ⌈Parking.resolventThreshold d CR (a * δ ^ 2)⌉₊ + 1

theorem resolventThreshold_lt_nearCutoff (d : ℕ) (CR a δ : ℝ) :
    Parking.resolventThreshold d CR (a * δ ^ 2) < ((nearCutoff d CR a δ : ℕ) : ℝ) := by
  have h := Nat.le_ceil (Parking.resolventThreshold d CR (a * δ ^ 2))
  rw [nearCutoff]
  push_cast
  linarith

theorem nearCutoff_le (d : ℕ) (CR a δ : ℝ)
    (hT : 0 ≤ Parking.resolventThreshold d CR (a * δ ^ 2)) :
    ((nearCutoff d CR a δ : ℕ) : ℝ) ≤ Parking.resolventThreshold d CR (a * δ ^ 2) + 2 := by
  have h := Nat.ceil_lt_add_one hT
  rw [nearCutoff]
  push_cast
  linarith

/-- **`eq:near-tail`** (`parking.tex:2930-2933`).  A bound on every tail sum from the
cutoff on bounds the limit mean by the mean at the cutoff. -/
theorem meanUlimit_le_of_tail (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (N : ℕ) (Ctail : ℝ) (hCtail : 0 ≤ Ctail)
    (htail : ∀ n : ℕ, ∑ s ∈ Finset.Ico N n, Parking.S (Parking.law d ν) s ≤ Ctail) :
    Parking.meanUlimit (Parking.law d ν)
      ≤ ENNReal.ofReal (Parking.meanU (Parking.law d ν) N + Ctail) :=
by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hsum : ∀ n : ℕ, Parking.meanU (Parking.law d ν) n
      = ∑ s ∈ Finset.range n, Parking.S (Parking.law d ν) s := fun n =>
    meanU_eq_sum_S (μ := LatticeProb.iidLaw d ν) hd (fun v => iidLaw_map_shiftConf' ν v)
      (integrable_eval_iid (d := d) ν hint 0) n
  have hS0 : ∀ s : ℕ, 0 ≤ Parking.S (Parking.law d ν) s := fun s => S_nonneg _ s
  rw [meanUlimit_eq_iSup hd ν hint]
  refine iSup_le fun n => ENNReal.ofReal_le_ofReal ?_
  rcases le_total n N with hnN | hNn
  · have h1 : ∑ s ∈ Finset.range n, Parking.S (Parking.law d ν) s
        ≤ ∑ s ∈ Finset.range N, Parking.S (Parking.law d ν) s :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hnN)
        (fun i _ _ => hS0 i)
    rw [hsum n, hsum N]
    linarith
  · have hsplit : ∑ s ∈ Finset.range N, Parking.S (Parking.law d ν) s
        + ∑ s ∈ Finset.Ico N n, Parking.S (Parking.law d ν) s
        = ∑ s ∈ Finset.range n, Parking.S (Parking.law d ν) s := by
      simp only [Finset.range_eq_Ico]
      exact Finset.sum_Ico_consecutive _ (Nat.zero_le N) hNn
    rw [hsum n, hsum N, ← hsplit]
    have := htail n
    linarith

/-- **Step 1 of the upper bounds of `thm:near`, assembled** (`parking.tex:2914-2933`).
Beyond the cutoff the survivor counts sum to a constant, so the limit mean odometer is
the mean odometer at the cutoff up to that constant. -/
theorem exists_meanUlimit_le_cutoff (hd : 1 ≤ d) {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ}
    (hfam : NearFamily δ₀ ν θ M K) :
    ∃ a Ct CR δ₁ : ℝ, 0 < a ∧ 0 < Ct ∧ 0 < CR ∧ 0 < δ₁ ∧ δ₁ ≤ δ₀ ∧ δ₁ ≤ 1 ∧
      ∀ δ ∈ Set.Ioc (0 : ℝ) δ₁, a * δ ^ 2 ≤ 1 ∧
        Parking.meanUlimit (Parking.law d (ν δ))
          ≤ ENNReal.ofReal
              (Parking.meanU (Parking.law d (ν δ)) (nearCutoff d CR a δ) + Ct) := by
  have hfam' : NearFamily δ₀ ν θ M K := hfam
  obtain ⟨hδ₀, hθ, hprob, -, -, hexp, -⟩ := hfam
  obtain ⟨a, Ct, CR, δ₁, ha, hCt, hCR, hδ₁, hδ₁δ₀, htail⟩ := exists_near_tail hd hfam'
  refine ⟨a, Ct, CR, min δ₁ (min 1 (Real.sqrt a⁻¹)), ha, hCt, hCR,
    lt_min hδ₁ (lt_min one_pos (Real.sqrt_pos.mpr (by positivity))),
    le_trans (min_le_left _ _) hδ₁δ₀,
    le_trans (min_le_right _ _) (min_le_left _ _), fun δ hδ => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδ₁' : δ ≤ δ₁ := le_trans hδ.2 (min_le_left _ _)
  have hδ1 : δ ≤ 1 := le_trans hδ.2 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδs : δ ≤ Real.sqrt a⁻¹ :=
    le_trans hδ.2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hane : a * δ ^ 2 ≤ 1 := by
    have h1 : δ ^ 2 ≤ a⁻¹ := by
      have hsq := Real.sq_sqrt (le_of_lt (inv_pos.mpr ha))
      nlinarith [Real.sqrt_nonneg a⁻¹, hδ0.le]
    calc a * δ ^ 2 ≤ a * a⁻¹ := by nlinarith
      _ = 1 := mul_inv_cancel₀ (ne_of_gt ha)
  have hδmem : δ ∈ Set.Icc (0 : ℝ) δ₀ := ⟨hδ0.le, le_trans hδ₁' hδ₁δ₀⟩
  haveI := hprob δ hδmem
  have hint : Integrable (fun k : ℤ => |(k : ℝ)|) (ν δ) :=
    integrable_abs_of_absMoment hθ (hexp δ hδmem).1
  refine ⟨hane, meanUlimit_le_of_tail hd (ν δ) hint _ Ct hCt.le (fun n => ?_)⟩
  exact htail δ ⟨hδ0, hδ₁'⟩ (nearCutoff d CR a δ)
    (resolventThreshold_lt_nearCutoff d CR a δ) n

end Parking
end
