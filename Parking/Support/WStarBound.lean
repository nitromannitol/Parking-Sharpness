/-
The maximal average `w^\star` as a function of the data: it is measurable, it is
bounded pathwise by the configuration over a box, and its `r`-th moment is at
most `n+1` times the largest `r`-th moment of the error at the origin.

The last is the second display of `prop:w-moment`, and its proof is the paper's:
Jensen's inequality for the walk average, the bound of a maximum over `n+1`
times by the sum of the `r`-th powers, and translation invariance.  The exchange
of the two integrals that the paper's "`\E\,\E_0`" hides is not Fubini here but
a finite decomposition: the walk after `j` steps lies in the box of radius `j`,
so the average over the walk of a function of its position is a finite
combination of the values of that function, and the outer integral passes
through the combination one term at a time.
-/
import Parking.Support.Lp
import Parking.Support.Pathwise

noncomputable section

namespace Parking

open MeasureTheory LatticeProb Finset

variable {d : ℕ}

/-! ### The maximum along the walk as a finite supremum -/

theorem wMax_eq_sup' (ω : Data d) (n : ℕ) (x : Site d) (p : ℕ → Fin d × Bool) :
    wMax ω n x p = (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun j => |wErr ω (n - j) (walkPath x p j)|) := by
  refine le_antisymm (ciSup_le fun j => ?_) (Finset.sup'_le _ _ fun j hj => ?_)
  · by_cases hj : j ∈ Finset.range (n + 1)
    · rw [ciSup_pos hj]
      exact Finset.le_sup' (fun j => |wErr ω (n - j) (walkPath x p j)|) hj
    · rw [ciSup_neg hj, Real.sSup_empty]
      refine le_trans (abs_nonneg (wErr ω (n - 0) (walkPath x p 0))) ?_
      exact Finset.le_sup' (fun j => |wErr ω (n - j) (walkPath x p j)|)
        (Finset.mem_range.mpr (Nat.succ_pos n))
  · have h1 : (⨆ _ : j ∈ Finset.range (n + 1), |wErr ω (n - j) (walkPath x p j)|)
        = |wErr ω (n - j) (walkPath x p j)| := ciSup_pos hj
    rw [← h1]
    exact le_ciSup (wMax_bdd ω n x p) j

/-! ### Measurability in the data -/

theorem measurable_wMax_prod (n : ℕ) (x : Site d) :
    Measurable fun a : Data d × (ℕ → Fin d × Bool) => wMax a.1 n x a.2 := by
  have hterm : ∀ j : ℕ, Measurable fun a : Data d × (ℕ → Fin d × Bool) =>
      |wErr a.1 (n - j) (walkPath x a.2 j)| := by
    intro j
    refine measurable_eval_var (fun a : Data d × (ℕ → Fin d × Bool) => walkPath x a.2 j)
      ((measurable_walkPath x j).comp measurable_snd)
      (fun a z => |wErr a.1 (n - j) z|) ?_
    intro z
    exact ((measurable_wErr (n - j) z).comp measurable_fst).abs
  have hsup := Finset.measurable_sup' (s := Finset.range (n + 1))
    (f := fun j (a : Data d × (ℕ → Fin d × Bool)) => |wErr a.1 (n - j) (walkPath x a.2 j)|)
    Finset.nonempty_range_add_one (fun j _ => hterm j)
  have hfun : (fun a : Data d × (ℕ → Fin d × Bool) => wMax a.1 n x a.2)
      = (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun j (a : Data d × (ℕ → Fin d × Bool)) =>
          |wErr a.1 (n - j) (walkPath x a.2 j)|) := by
    funext a
    rw [Finset.sup'_apply]
    exact wMax_eq_sup' a.1 n x a.2
  rw [hfun]
  exact hsup

theorem measurable_wStar (hd : 1 ≤ d) (n : ℕ) (x : Site d) :
    Measurable fun ω : Data d => wStar ω n x := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  exact ((measurable_wMax_prod (d := d) n x).stronglyMeasurable.integral_prod_right'
    (ν := walkLaw d)).measurable

/-! ### The pathwise bound -/

theorem wMax_le_conf (hd : 1 ≤ d) (ω : Data d) (n : ℕ) (x : Site d)
    (p : ℕ → Fin d × Bool) :
    wMax ω n x p ≤ wCoef d n * confBox ω x (3 * n) := by
  rw [wMax_eq_sup']
  refine Finset.sup'_le _ _ fun j hj => ?_
  have hjn : j ≤ n := by
    have := Finset.mem_range.mp hj; omega
  calc |wErr ω (n - j) (walkPath x p j)|
      ≤ wCoef d (n - j) * confBox ω (walkPath x p j) (2 * (n - j)) :=
        abs_wErr_le hd ω (n - j) _
    _ ≤ wCoef d n * confBox ω x (3 * n) := by
        refine mul_le_mul (wCoef_mono d (Nat.sub_le n j)) ?_
          (confBox_nonneg _ _ _) (wCoef_nonneg d n)
        refine le_trans (confBox_le_of_mem ω (walkPath_mem_box x p hjn) (2 * (n - j))) ?_
        exact confBox_mono ω x (by omega)

theorem wStar_le_conf (hd : 1 ≤ d) (ω : Data d) (n : ℕ) (x : Site d) :
    wStar ω n x ≤ wCoef d n * confBox ω x (3 * n) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  calc wStar ω n x = ∫ p, wMax ω n x p ∂(walkLaw d) := rfl
    _ ≤ ∫ _p, wCoef d n * confBox ω x (3 * n) ∂(walkLaw d) :=
        integral_mono (integrable_wMax hd ω n x) (integrable_const _)
          fun p => wMax_le_conf hd ω n x p
    _ = wCoef d n * confBox ω x (3 * n) := by
        rw [integral_const, probReal_univ, one_smul]

theorem wStar_nonneg (ω : Data d) (n : ℕ) (x : Site d) : 0 ≤ wStar ω n x :=
  integral_nonneg fun p => wMax_nonneg ω n x p

/-! ### Moments -/

theorem integrable_abs_wErr_rpow (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 1 ≤ r) (m : ℕ) (x : Site d) :
    Integrable (fun ω : Data d => |wErr ω m x| ^ r) (law d ν) := by
  have hdom : Integrable (fun ω : Data d =>
      wCoef d m ^ r * confBox ω x (2 * m) ^ r) (law d ν) :=
    (integrable_confBox_rpow hd ν hθ hexp hr x (2 * m)).const_mul _
  have hmeas : Measurable fun ω : Data d => |wErr ω m x| ^ r :=
    (measurable_rpow_const (le_trans zero_le_one hr)).comp (measurable_wErr m x).abs
  refine Integrable.mono' hdom hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r),
    ← Real.mul_rpow (wCoef_nonneg d m) (confBox_nonneg ω x (2 * m))]
  exact Real.rpow_le_rpow (abs_nonneg _) (abs_wErr_le hd ω m x) (le_trans zero_le_one hr)

theorem integrable_wStar_rpow (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) (x : Site d) :
    Integrable (fun ω : Data d => wStar ω n x ^ r) (law d ν) := by
  have hdom : Integrable (fun ω : Data d =>
      wCoef d n ^ r * confBox ω x (3 * n) ^ r) (law d ν) :=
    (integrable_confBox_rpow hd ν hθ hexp hr x (3 * n)).const_mul _
  have hmeas : Measurable fun ω : Data d => wStar ω n x ^ r :=
    (measurable_rpow_const (le_trans zero_le_one hr)).comp (measurable_wStar hd n x)
  refine Integrable.mono' hdom hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (wStar_nonneg ω n x) r),
    ← Real.mul_rpow (wCoef_nonneg d n) (confBox_nonneg ω x (3 * n))]
  exact Real.rpow_le_rpow (wStar_nonneg ω n x) (wStar_le_conf hd ω n x)
    (le_trans zero_le_one hr)

theorem integrable_U_rpow (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) (x : Site d) :
    Integrable (fun ω : Data d => ((U ω n x : ℕ) : ℝ) ^ r) (law d ν) := by
  have hdom : Integrable (fun ω : Data d =>
      (n : ℝ) ^ r * confBox ω x n ^ r) (law d ν) :=
    (integrable_confBox_rpow hd ν hθ hexp hr x n).const_mul _
  have hmeas : Measurable fun ω : Data d => ((U ω n x : ℕ) : ℝ) ^ r :=
    (measurable_from_countable' fun m : ℕ => ((m : ℝ)) ^ r).comp (measurable_U n x)
  refine Integrable.mono' hdom hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) r),
    ← Real.mul_rpow (Nat.cast_nonneg n) (confBox_nonneg ω x n)]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (U_le_confBox ω n x) (le_trans zero_le_one hr)

/-! ### Translation invariance of the moments -/

theorem integral_abs_wErr_rpow_shift (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 1 ≤ r) (m : ℕ) (z : Site d) :
    ∫ ω, |wErr ω m z| ^ r ∂(law d ν) = ∫ ω, |wErr ω m 0| ^ r ∂(law d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ν))
  have hti : TranslationInvariant (LatticeProb.iidLaw d ν) := fun w =>
    iidLaw_map_shiftConf' ν w
  have hlaw : law d ν = dataLaw d (LatticeProb.iidLaw d ν) := rfl
  have hAE : AEStronglyMeasurable (fun ω : Data d => |wErr ω m z| ^ r)
      (dataLaw d (LatticeProb.iidLaw d ν)) := by
    rw [← hlaw]
    exact (integrable_abs_wErr_rpow hd ν hθ hexp hr m z).aestronglyMeasurable
  have h := integral_comp_shiftData (μ := LatticeProb.iidLaw d ν) hd hti (-z) hAE
  rw [← hlaw] at h
  have hpt : ∀ ω : Data d, |wErr (shiftData (-z) ω) m z| ^ r = |wErr ω m 0| ^ r := by
    intro ω
    rw [wErr_shiftData, add_neg_cancel]
  simp only [hpt] at h
  exact h.symm

end Parking

end
