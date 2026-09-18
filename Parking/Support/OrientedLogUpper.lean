/- Step 4 of the oriented walk theorem: the logarithmic upper bound on the
directed particle mean at `d ≥ 3`, from the moment inequality at
`r = 2 ∨ ⌈log(n+1)⌉` and Young's inequality. -/
import Parking.Support.OrientedMeanBound
import Parking.Support.OrientedYoung
import Parking.Support.OrientedMoments
import Parking.Support.UpperTarget

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Step 4 of `thm:oriented-walk` (`parking.tex:3336-3344`): at `d ≥ 3` the
moment inequality for `U⃗_n(0)^r` with `r = 2 ∨ ⌈log(n+1)⌉`, absorbed by Young's
inequality, yields the `log(n+1)` upper bound on the mean. -/
theorem meanU_oriented_log_upper_of_moment (hd : 3 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 1 ≤ n →
      (∫ ω : Data d, (U ω n 0 : ℝ) ^ (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) ∂(orientedLaw d ν)) ^
          ((1 : ℝ) / (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ)) ≤
        C * Real.log ((n : ℝ) + 1) +
          C * (Real.sqrt ((2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) *
            (∫ ω : Data d, (U ω n 0 : ℝ) ^ (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) ∂(orientedLaw d ν)) ^
              ((1 : ℝ) / (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ))) +
            (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ))) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ n : ℕ, 1 ≤ n →
      meanU (orientedLaw d ν) n ≤ C' * Real.log ((n : ℝ) + 1) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (orientedLaw d ν) := orientedLaw_isProbability (by omega) ν
  obtain ⟨θ, hθ, he⟩ := hν.expMoment
  refine ⟨3 * (4 * C + 4 * C ^ 2 + 4 * C) + 1, by positivity, fun n hn => ?_⟩
  set L : ℝ := Real.log ((n : ℝ) + 1) + 1 with hLdef
  set r : ℝ := (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) with hrdef
  have hlog2 : Real.log 2 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n + 1))
  have hlog0 : 0 < Real.log ((n : ℝ) + 1) := lt_of_lt_of_le (Real.log_pos (by norm_num)) hlog2
  have hL1 : 1 ≤ L := by simp only [hLdef]; linarith
  have hr2 : 2 ≤ r := by
    simp only [hrdef]
    exact_mod_cast le_max_left 2 ⌈Real.log ((n : ℝ) + 1)⌉₊
  have hrL : r ≤ 2 * L := by
    simp only [hrdef, hLdef]
    have h1 : (2 : ℝ) ≤ 2 * (Real.log ((n : ℝ) + 1) + 1) := by linarith
    have h2 : ((⌈Real.log ((n : ℝ) + 1)⌉₊ : ℕ) : ℝ) ≤ 2 * (Real.log ((n : ℝ) + 1) + 1) := by
      have := Nat.ceil_lt_add_one (le_of_lt hlog0)
      linarith
    exact max_le h1 h2
  set X : ℝ := (∫ ω : Data d, (U ω n 0 : ℝ) ^ r ∂(orientedLaw d ν)) ^ ((1 : ℝ) / r) with hXdef
  have hI0 : 0 ≤ ∫ ω : Data d, (U ω n 0 : ℝ) ^ r ∂(orientedLaw d ν) :=
    integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hX0 : 0 ≤ X := Real.rpow_nonneg hI0 _
  have hstep : X ≤ C * L + C * (Real.sqrt (r * X) + r) := by
    have h1 := h n hn
    have h2 : C * Real.log ((n : ℝ) + 1) ≤ C * L := by
      simp only [hLdef]; nlinarith
    have h3 : (∫ ω : Data d, (U ω n 0 : ℝ) ^ (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ)
        ∂(orientedLaw d ν)) = ∫ ω : Data d, (U ω n 0 : ℝ) ^ r ∂(orientedLaw d ν) := by
      simp only [hrdef]
    rw [h3] at h1
    rw [hXdef]
    linarith [h1, h2]
  have habs := oriented_log_absorb hX0 hC hL1 hr2 hrL hstep
  have hle : meanU (orientedLaw d ν) n ≤ X := by
    rw [meanU]
    have h1 := integral_le_rNorm (μ := orientedLaw d ν) (r := r)
      (f := fun ω : Data d => (U ω n 0 : ℝ))
      (fun ω => Nat.cast_nonneg _) (integrable_oriented_U (d := d) (by omega) ν hν n 0)
      (by linarith) (by
        have := integrable_oriented_U_rpow (d := d) (by omega) ν hθ
          (integrable_expMax_of_expAbs hθ he) (r := r) (by linarith) n 0
        simpa only [hrdef] using this)
    rw [hXdef]
    exact h1
  have hfin : (4 * C + 4 * C ^ 2 + 4 * C) * L ≤
      (3 * (4 * C + 4 * C ^ 2 + 4 * C) + 1) * Real.log ((n : ℝ) + 1) := by
    have h4 : 0 ≤ 4 * C + 4 * C ^ 2 + 4 * C := by positivity
    have h5 : L ≤ 3 * Real.log ((n : ℝ) + 1) := by
      simp only [hLdef]
      nlinarith [hlog2, Real.log_two_gt_d9]
    nlinarith [h4, h5, hlog0]
  calc meanU (orientedLaw d ν) n ≤ X := hle
    _ ≤ (4 * C + 4 * C ^ 2 + 4 * C) * L := habs
    _ ≤ (3 * (4 * C + 4 * C ^ 2 + 4 * C) + 1) * Real.log ((n : ℝ) + 1) := hfin

end Parking
end
