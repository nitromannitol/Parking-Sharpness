/-
The second display of `prop:w-moment`:

  `(E w^\star_n(0)^r)^{1/r} ≤ (n+1)^{1/r} max_{m ≤ n}(E|w_m(0)|^r)^{1/r}`.

The paper's proof is Jensen's inequality for the walk average, a union bound
over the `n+1` times, and translation invariance.  The one step the paper writes
as `\E\,\E_0` and does not comment on is the exchange of the average over the
walk with the average over the data.  It is not Fubini here: the walk after `j`
steps lies in the box of radius `j`, a finite set, so the average over the walk
of a function of the position is a finite combination of the values of that
function, with coefficients that do not depend on the data, and the average over
the data passes through the combination one term at a time.
-/
import Parking.Support.WStarBound

noncomputable section

namespace Parking

open MeasureTheory LatticeProb Finset

variable {d : ℕ}

/-! ### The average over the walk of a function of its position -/

theorem walk_indicator_sum (j : ℕ) (f : Site d → ℝ) (p : ℕ → Fin d × Bool) :
    f (walkPath (0 : Site d) p j)
      = ∑ z ∈ boxFinset (0 : Site d) j,
          Set.indicator {q | walkPath (0 : Site d) q j = z} (fun _ => f z) p := by
  classical
  have hmem : walkPath (0 : Site d) p j ∈ boxFinset (0 : Site d) j :=
    walkPath_mem_box 0 p (le_refl j)
  have hterm : ∀ z ∈ boxFinset (0 : Site d) j,
      Set.indicator {q | walkPath (0 : Site d) q j = z} (fun _ => f z) p
        = if walkPath (0 : Site d) p j = z then f z else 0 := by
    intro z _
    rw [Set.indicator_apply]
    simp only [Set.mem_setOf_eq]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq (boxFinset (0 : Site d) j) (walkPath (0 : Site d) p j) f, if_pos hmem]

theorem measurableSet_walk_fibre (j : ℕ) (z : Site d) :
    MeasurableSet {p : ℕ → Fin d × Bool | walkPath (0 : Site d) p j = z} :=
  (measurable_walkPath (0 : Site d) j) (measurableSet_singleton z)

theorem integrable_walk_comp (hd : 1 ≤ d) (j : ℕ) (f : Site d → ℝ) :
    Integrable (fun p => f (walkPath (0 : Site d) p j)) (walkLaw d) := by
  classical
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hsum : Integrable (fun p => ∑ z ∈ boxFinset (0 : Site d) j,
      Set.indicator {q | walkPath (0 : Site d) q j = z} (fun _ => f z) p) (walkLaw d) :=
    integrable_finsetSum _ fun z _ =>
      (integrable_const (f z)).indicator (measurableSet_walk_fibre j z)
  exact hsum.congr (Filter.Eventually.of_forall fun p => (walk_indicator_sum j f p).symm)

/-- **The average over the walk of a function of the position.**  The position
after `j` steps lies in the box of radius `j`, so the average is a finite
combination of the values of the function. -/
theorem integral_walk_decomp (hd : 1 ≤ d) (j : ℕ) (f : Site d → ℝ) :
    ∫ p, f (walkPath (0 : Site d) p j) ∂(walkLaw d)
      = ∑ z ∈ boxFinset (0 : Site d) j,
          (walkLaw d).real {p | walkPath (0 : Site d) p j = z} * f z := by
  classical
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  rw [integral_congr_ae (Filter.Eventually.of_forall (walk_indicator_sum j f)),
    integral_finsetSum _ fun z _ =>
      (integrable_const (f z)).indicator (measurableSet_walk_fibre j z)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [integral_indicator_const (f z) (measurableSet_walk_fibre j z), smul_eq_mul]

theorem sum_walk_prob (hd : 1 ≤ d) (j : ℕ) :
    ∑ z ∈ boxFinset (0 : Site d) j,
      (walkLaw d).real {p | walkPath (0 : Site d) p j = z} = 1 := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have h := integral_walk_decomp hd j (fun _ : Site d => (1 : ℝ))
  simp only [mul_one] at h
  rw [← h, integral_const, probReal_univ, smul_eq_mul, mul_one]

/-! ### The moment of the error along the walk -/

/-- The average over the walk of the `r`-th moment of the error at the position
after `j` steps, written as the finite combination it is. -/
def wWalkMoment (r : ℝ) (m j : ℕ) (ω : Data d) : ℝ :=
  ∑ z ∈ boxFinset (0 : Site d) j,
    (walkLaw d).real {p | walkPath (0 : Site d) p j = z} * |wErr ω m z| ^ r

theorem wWalkMoment_eq (hd : 1 ≤ d) (r : ℝ) (m j : ℕ) (ω : Data d) :
    ∫ p, |wErr ω m (walkPath (0 : Site d) p j)| ^ r ∂(walkLaw d)
      = wWalkMoment (d := d) r m j ω :=
  integral_walk_decomp hd j (fun z => |wErr ω m z| ^ r)

theorem integrable_wWalkMoment (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 1 ≤ r) (m j : ℕ) :
    Integrable (wWalkMoment (d := d) r m j) (law d ν) :=
  integrable_finsetSum _ fun z _ =>
    (integrable_abs_wErr_rpow hd ν hθ hexp hr m z).const_mul _

theorem integral_wWalkMoment (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 1 ≤ r) (m j : ℕ) :
    ∫ ω, wWalkMoment (d := d) r m j ω ∂(law d ν)
      = ∫ ω, |wErr ω m 0| ^ r ∂(law d ν) := by
  simp only [wWalkMoment]
  rw [integral_finsetSum _ fun z _ =>
    (integrable_abs_wErr_rpow hd ν hθ hexp hr m z).const_mul _]
  have hterm : ∀ z ∈ boxFinset (0 : Site d) j,
      ∫ ω, (walkLaw d).real {p | walkPath (0 : Site d) p j = z} * |wErr ω m z| ^ r
          ∂(law d ν)
        = (walkLaw d).real {p | walkPath (0 : Site d) p j = z} *
            ∫ ω, |wErr ω m 0| ^ r ∂(law d ν) := by
    intro z _
    rw [integral_const_mul, integral_abs_wErr_rpow_shift hd ν hθ hexp hr m z]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, sum_walk_prob hd j, one_mul]

/-! ### The bound on the maximum along the walk -/

theorem wMax_rpow_le (ω : Data d) (n : ℕ) {r : ℝ} (hr : 1 ≤ r)
    (p : ℕ → Fin d × Bool) :
    wMax ω n (0 : Site d) p ^ r
      ≤ ∑ j ∈ Finset.range (n + 1), |wErr ω (n - j) (walkPath (0 : Site d) p j)| ^ r := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  set T : ℝ := ∑ j ∈ Finset.range (n + 1),
    |wErr ω (n - j) (walkPath (0 : Site d) p j)| ^ r with hT
  have hT0 : 0 ≤ T :=
    Finset.sum_nonneg fun j _ => Real.rpow_nonneg (abs_nonneg _) r
  have hstep : ∀ j ∈ Finset.range (n + 1),
      |wErr ω (n - j) (walkPath (0 : Site d) p j)| ≤ T ^ (1 / r) := by
    intro j hj
    have hle : |wErr ω (n - j) (walkPath (0 : Site d) p j)| ^ r ≤ T :=
      Finset.single_le_sum
        (f := fun k => |wErr ω (n - k) (walkPath (0 : Site d) p k)| ^ r)
        (fun k _ => Real.rpow_nonneg (abs_nonneg _) r) hj
    have h1 : (|wErr ω (n - j) (walkPath (0 : Site d) p j)| ^ r) ^ (1 / r)
        ≤ T ^ (1 / r) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) r) hle (by positivity)
    rwa [← Real.rpow_mul (abs_nonneg _), mul_one_div, div_self (ne_of_gt hr0),
      Real.rpow_one] at h1
  have hmax : wMax ω n (0 : Site d) p ≤ T ^ (1 / r) := by
    rw [wMax_eq_sup']
    exact Finset.sup'_le _ _ hstep
  have h2 : wMax ω n (0 : Site d) p ^ r ≤ (T ^ (1 / r)) ^ r :=
    Real.rpow_le_rpow (wMax_nonneg ω n 0 p) hmax (le_of_lt hr0)
  rwa [← Real.rpow_mul hT0, one_div, inv_mul_cancel₀ (ne_of_gt hr0), Real.rpow_one] at h2

/-! ### The second display -/

theorem wStar_rpow_le_sum (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) (ω : Data d) :
    wStar ω n 0 ^ r
      ≤ ∑ j ∈ Finset.range (n + 1), wWalkMoment (d := d) r (n - j) j ω := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hrpow : Integrable (fun p => wMax ω n (0 : Site d) p ^ r) (walkLaw d) := by
    refine Integrable.mono' (integrable_const
        ((wCoef d n * confBox ω 0 (3 * n)) ^ r))
      (((measurable_rpow_const (le_trans zero_le_one hr)).comp
        (measurable_wMax hd ω n 0)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (wMax_nonneg ω n 0 p) r)]
    exact Real.rpow_le_rpow (wMax_nonneg ω n 0 p) (wMax_le_conf hd ω n 0 p)
      (le_trans zero_le_one hr)
  have hsumint : Integrable (fun p => ∑ j ∈ Finset.range (n + 1),
      |wErr ω (n - j) (walkPath (0 : Site d) p j)| ^ r) (walkLaw d) :=
    integrable_finsetSum _ fun j _ =>
      integrable_walk_comp hd j (fun z => |wErr ω (n - j) z| ^ r)
  calc wStar ω n 0 ^ r ≤ ∫ p, wMax ω n (0 : Site d) p ^ r ∂(walkLaw d) :=
        rpow_integral_le (fun p => wMax_nonneg ω n 0 p) (integrable_wMax hd ω n 0) hr hrpow
    _ ≤ ∫ p, (∑ j ∈ Finset.range (n + 1),
          |wErr ω (n - j) (walkPath (0 : Site d) p j)| ^ r) ∂(walkLaw d) :=
        integral_mono hrpow hsumint fun p => wMax_rpow_le ω n hr p
    _ = ∑ j ∈ Finset.range (n + 1),
          ∫ p, |wErr ω (n - j) (walkPath (0 : Site d) p j)| ^ r ∂(walkLaw d) :=
        integral_finsetSum _ fun j _ =>
          integrable_walk_comp hd j (fun z => |wErr ω (n - j) z| ^ r)
    _ = ∑ j ∈ Finset.range (n + 1), wWalkMoment (d := d) r (n - j) j ω :=
        Finset.sum_congr rfl fun j _ => wWalkMoment_eq hd r (n - j) j ω

end Parking

end
