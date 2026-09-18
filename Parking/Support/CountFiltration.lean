/-
Step 1 of `lem:product` for finitely many sites.

Revealing one count at a time splits a covariance into the covariance of the two
averages over that count and the mean of the one-site conditional covariance,
which is `Support/CovCond.lean` transported along the measure preserving map
that resamples one coordinate.  The one-site covariance is bounded by
`Support/Cov.lean`'s coupling inequality, and its mean is the covariance with
the count at that site, so an induction over the finite family of sites gives
the paper's `|Cov(f(Y), z(Y))| ≤ Σ_i Cov(f, η(x_i))`.
-/
import Parking.Support.CountSite

open MeasureTheory

noncomputable section

namespace Parking

/-- `g` is a function of the counts at the sites of `N` alone. -/
def DependsOnCounts {d : ℕ} (N : Finset (Site d)) (g : (Site d → ℤ) → ℝ) : Prop :=
  ∀ a a' : Site d → ℤ, (∀ x ∈ N, a x = a' x) → g a = g a'

/-- The average of `g` over the count at one site. -/
def avgAt {d : ℕ} (ν : Measure ℤ) (x : Site d) (g : (Site d → ℤ) → ℝ)
    (a : Site d → ℤ) : ℝ :=
  ∫ k, g (Function.update a x k) ∂ν

theorem meanF_dependsOnCounts {d : ℕ} {N : Finset (Site d)} {F : PData d → ℝ}
    (hFN : DependsOn N F) : DependsOnCounts N (meanF F) := by
  intro a a' h
  unfold meanF
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  exact hFN _ _ h (fun q _ => rfl) (fun q _ => rfl)

/-- The average over one count does not read that count. -/
theorem avgAt_update_self {d : ℕ} (ν : Measure ℤ) (x : Site d) (g : (Site d → ℤ) → ℝ)
    (a : Site d → ℤ) (k : ℤ) : avgAt ν x g (Function.update a x k) = avgAt ν x g a := by
  unfold avgAt
  simp [Function.update_idem]

/-- The average over one count is a function of the other sites of `N`. -/
theorem avgAt_dependsOnCounts {d : ℕ} {ν : Measure ℤ} {N : Finset (Site d)} {x : Site d}
    {g : (Site d → ℤ) → ℝ} (hg : DependsOnCounts (insert x N) g) :
    DependsOnCounts N (avgAt ν x g) := by
  intro a a' h
  unfold avgAt
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  refine hg _ _ fun y hy => ?_
  by_cases hyx : y = x
  · subst hyx
    simp
  · rw [Function.update_of_ne hyx, Function.update_of_ne hyx]
    exact h y ((Finset.mem_insert.mp hy).resolve_left hyx)

/-- Updating one coordinate is measurable in the new value. -/
theorem measurable_update_const {d : ℕ} (a : Site d → ℤ) (x : Site d) :
    Measurable (fun k : ℤ => Function.update a x k) := by
  refine measurable_pi_lambda _ fun y => ?_
  by_cases hy : y = x
  · subst hy
    simp only [Function.update_self]
    exact measurable_id
  · simp [Function.update_of_ne hy]

/-- The average over one count is measurable. -/
theorem measurable_avgAt {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {f : (Site d → ℤ) → ℝ} (hfm : Measurable f) (x : Site d) :
    Measurable (avgAt ν x f) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hu : MeasurePreserving (fun q : (Site d → ℤ) × ℤ => Function.update q.1 x q.2)
      ((LatticeProb.iidLaw d ν).prod ν) (LatticeProb.iidLaw d ν) :=
    LatticeProb.measurePreserving_update_infinitePi (fun _ : Site d => ν) x
  have hfu : Measurable (fun q : (Site d → ℤ) × ℤ => f (Function.update q.1 x q.2)) :=
    hfm.comp hu.measurable
  exact (hfu.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

/-- A bounded measurable functional has integrable sections in one count. -/
theorem integrable_section_update {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {f : (Site d → ℤ) → ℝ} (hfm : Measurable f) {B : ℝ} (hfb : ∀ a, |f a| ≤ B)
    (x : Site d) (a : Site d → ℤ) :
    Integrable (fun k : ℤ => f (Function.update a x k)) ν :=
  (integrable_const B).mono' (hfm.comp (measurable_update_const a x)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => by simpa [Real.norm_eq_abs] using hfb _)

/-- The average over one count inherits a bound. -/
theorem abs_avgAt_le {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {f : (Site d → ℤ) → ℝ} (hfm : Measurable f) (hfb : ∀ a, |f a| ≤ 1) (x : Site d)
    (a : Site d → ℤ) : |avgAt ν x f a| ≤ 1 := by
  unfold avgAt
  calc |∫ k, f (Function.update a x k) ∂ν| ≤ ∫ k, |f (Function.update a x k)| ∂ν :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _k : ℤ, (1 : ℝ) ∂ν :=
        integral_mono (integrable_section_update hfm hfb x a).abs (integrable_const _)
          fun k => hfb _
    _ = 1 := by simp

/-- **Revealing one count.**  The covariance is the covariance of the two
averages over that count plus the mean of the one-site conditional covariance. -/
theorem cov_split_coord {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {f z : (Site d → ℤ) → ℝ} (hfm : Measurable f) (hzm : Measurable z)
    (hfb : ∀ a, |f a| ≤ 1) (hzi : Integrable z (LatticeProb.iidLaw d ν)) (x : Site d) :
    cov (LatticeProb.iidLaw d ν) f z
      = cov (LatticeProb.iidLaw d ν) (avgAt ν x f) (avgAt ν x z)
        + ∫ a, cov ν (fun k => f (Function.update a x k))
              (fun k => z (Function.update a x k)) ∂(LatticeProb.iidLaw d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hu : MeasurePreserving (fun q : (Site d → ℤ) × ℤ => Function.update q.1 x q.2)
      ((LatticeProb.iidLaw d ν).prod ν) (LatticeProb.iidLaw d ν) :=
    LatticeProb.measurePreserving_update_infinitePi (fun _ : Site d => ν) x
  have hfu : Measurable (fun q : (Site d → ℤ) × ℤ => f (Function.update q.1 x q.2)) :=
    hfm.comp hu.measurable
  have hbnd : ∀ᵐ q ∂((LatticeProb.iidLaw d ν).prod ν),
      ‖f (Function.update q.1 x q.2)‖ ≤ 1 :=
    Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hfb _
  have hzui : Integrable (fun q : (Site d → ℤ) × ℤ => z (Function.update q.1 x q.2))
      ((LatticeProb.iidLaw d ν).prod ν) := hu.integrable_comp_of_integrable hzi
  have hfui : Integrable (fun q : (Site d → ℤ) × ℤ => f (Function.update q.1 x q.2))
      ((LatticeProb.iidLaw d ν).prod ν) :=
    (integrable_const (1 : ℝ)).mono' hfu.aestronglyMeasurable hbnd
  have hFZ : Integrable (fun q : (Site d → ℤ) × ℤ =>
      f (Function.update q.1 x q.2) * z (Function.update q.1 x q.2))
      ((LatticeProb.iidLaw d ν).prod ν) := hzui.bdd_mul hfu.aestronglyMeasurable hbnd
  have hfz : Integrable (fun a : Site d → ℤ =>
      (∫ k, f (Function.update a x k) ∂ν) * ∫ k, z (Function.update a x k) ∂ν)
      (LatticeProb.iidLaw d ν) :=
    (Integrable.integral_prod_left hzui).bdd_mul
      (measurable_avgAt hfm x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs]
        exact abs_avgAt_le hfm hfb x a)
  have hdec := cov_prod_decomp (LatticeProb.iidLaw d ν) ν
    (fun q : (Site d → ℤ) × ℤ => f (Function.update q.1 x q.2))
    (fun q : (Site d → ℤ) × ℤ => z (Function.update q.1 x q.2)) hFZ hfui hzui hfz
  rw [cov_comp_measurePreserving hu f z hfm.aestronglyMeasurable hzm.aestronglyMeasurable]
  dsimp only at hdec ⊢
  exact hdec

/-- The covariance of a constant with anything vanishes. -/
theorem cov_const_left {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : ℝ) (g : Ω → ℝ) : cov μ (fun _ => c) g = 0 := by
  unfold cov
  rw [integral_const_mul, integral_const]
  simp

/-- The count at a site is integrable. -/
theorem integrable_coord {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (y : Site d) :
    Integrable (fun a : Site d → ℤ => ((a y : ℤ) : ℝ)) (LatticeProb.iidLaw d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have heval : MeasurePreserving (fun a : Site d → ℤ => a y) (LatticeProb.iidLaw d ν) ν :=
    measurePreserving_eval_infinitePi (fun _ : Site d => ν) y
  exact heval.integrable_comp_of_integrable (integrable_cast hint)

/-- The average over the count at `x` of the count at another site is that
count. -/
theorem avgAt_coord_of_ne {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν] {x y : Site d}
    (hxy : y ≠ x) : avgAt ν x (fun a : Site d → ℤ => ((a y : ℤ) : ℝ))
      = fun a : Site d → ℤ => ((a y : ℤ) : ℝ) := by
  funext a
  unfold avgAt
  simp [Function.update_of_ne hxy]

/-- A section of a functional that is one-Lipschitz in each count is
integrable. -/
theorem integrable_section_of_lipschitz {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {z : (Site d → ℤ) → ℝ} (hzm : Measurable z)
    (hzlip : ∀ (y : Site d) (a : Site d → ℤ) (k k' : ℤ),
      |z (Function.update a y k) - z (Function.update a y k')| ≤ |(k : ℝ) - (k' : ℝ)|)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (y : Site d) (a : Site d → ℤ) :
    Integrable (fun k : ℤ => z (Function.update a y k)) ν := by
  refine Integrable.mono' (hint.add (integrable_const |z (Function.update a y 0)|))
    (hzm.comp (measurable_update_const a y)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  have h := hzlip y a k 0
  simp only [Int.cast_zero, sub_zero] at h
  have h2 : |z (Function.update a y k)|
      ≤ |z (Function.update a y k) - z (Function.update a y 0)|
        + |z (Function.update a y 0)| := by
    calc |z (Function.update a y k)|
        = |(z (Function.update a y k) - z (Function.update a y 0))
            + z (Function.update a y 0)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  simp only [Pi.add_apply, Real.norm_eq_abs]
  linarith

/-- The average over one count of an integrable functional is integrable. -/
theorem integrable_avgAt {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {z : (Site d → ℤ) → ℝ} (hzi : Integrable z (LatticeProb.iidLaw d ν)) (x : Site d) :
    Integrable (avgAt ν x z) (LatticeProb.iidLaw d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hu : MeasurePreserving (fun q : (Site d → ℤ) × ℤ => Function.update q.1 x q.2)
      ((LatticeProb.iidLaw d ν).prod ν) (LatticeProb.iidLaw d ν) :=
    LatticeProb.measurePreserving_update_infinitePi (fun _ : Site d => ν) x
  exact Integrable.integral_prod_left (hu.integrable_comp_of_integrable hzi)

/-- The average over one count is nondecreasing in each count. -/
theorem avgAt_monotone {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {f : (Site d → ℤ) → ℝ} (hfm : Measurable f) (hfb : ∀ a, |f a| ≤ 1)
    (hfmono : ∀ (y : Site d) (a : Site d → ℤ), Monotone (fun k : ℤ => f (Function.update a y k)))
    (x y : Site d) (a : Site d → ℤ) :
    Monotone (fun k : ℤ => avgAt ν x f (Function.update a y k)) := by
  by_cases hyx : y = x
  · subst hyx
    intro k k' _
    dsimp only
    rw [avgAt_update_self, avgAt_update_self]
  · intro k k' hk
    have hcomm : ∀ m : ℤ, Function.update (Function.update a y k) x m
        = Function.update (Function.update a x m) y k := fun m => Function.update_comm hyx k m a
    have hcomm' : ∀ m : ℤ, Function.update (Function.update a y k') x m
        = Function.update (Function.update a x m) y k' := fun m => Function.update_comm hyx k' m a
    simp only [avgAt]
    refine integral_mono (integrable_section_update hfm hfb x _)
      (integrable_section_update hfm hfb x _) fun m => ?_
    rw [hcomm m, hcomm' m]
    exact hfmono y (Function.update a x m) hk

/-- The average over one count is one-Lipschitz in each count. -/
theorem avgAt_lipschitz {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {z : (Site d → ℤ) → ℝ} (hzm : Measurable z)
    (hzlip : ∀ (y : Site d) (a : Site d → ℤ) (k k' : ℤ),
      |z (Function.update a y k) - z (Function.update a y k')| ≤ |(k : ℝ) - (k' : ℝ)|)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (x y : Site d) (a : Site d → ℤ) (k k' : ℤ) :
    |avgAt ν x z (Function.update a y k) - avgAt ν x z (Function.update a y k')|
      ≤ |(k : ℝ) - (k' : ℝ)| := by
  by_cases hyx : y = x
  · subst hyx
    rw [avgAt_update_self, avgAt_update_self, sub_self, abs_zero]
    exact abs_nonneg _
  · have hcomm : ∀ m : ℤ, Function.update (Function.update a y k) x m
        = Function.update (Function.update a x m) y k := fun m => Function.update_comm hyx k m a
    have hcomm' : ∀ m : ℤ, Function.update (Function.update a y k') x m
        = Function.update (Function.update a x m) y k' := fun m => Function.update_comm hyx k' m a
    simp only [avgAt]
    rw [← integral_sub (integrable_section_of_lipschitz hzm hzlip hint x _)
      (integrable_section_of_lipschitz hzm hzlip hint x _)]
    calc |∫ m, (z (Function.update (Function.update a y k) x m)
            - z (Function.update (Function.update a y k') x m)) ∂ν|
        ≤ ∫ m, |z (Function.update (Function.update a y k) x m)
            - z (Function.update (Function.update a y k') x m)| ∂ν :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _m : ℤ, |(k : ℝ) - (k' : ℝ)| ∂ν := by
          refine integral_mono ((integrable_section_of_lipschitz hzm hzlip hint x _).sub
            (integrable_section_of_lipschitz hzm hzlip hint x _)).abs
            (integrable_const _) fun m => ?_
          rw [hcomm m, hcomm' m]
          exact hzlip y (Function.update a x m) k k'
      _ = |(k : ℝ) - (k' : ℝ)| := by simp

/-- The one-site conditional covariance is integrable in the other counts. -/
theorem integrable_cov_section {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {f z : (Site d → ℤ) → ℝ} (hfm : Measurable f) (_hzm : Measurable z)
    (hfb : ∀ a, |f a| ≤ 1) (hzi : Integrable z (LatticeProb.iidLaw d ν)) (x : Site d) :
    Integrable (fun a : Site d → ℤ => cov ν (fun k => f (Function.update a x k))
        (fun k => z (Function.update a x k))) (LatticeProb.iidLaw d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hu : MeasurePreserving (fun q : (Site d → ℤ) × ℤ => Function.update q.1 x q.2)
      ((LatticeProb.iidLaw d ν).prod ν) (LatticeProb.iidLaw d ν) :=
    LatticeProb.measurePreserving_update_infinitePi (fun _ : Site d => ν) x
  have hfu : Measurable (fun q : (Site d → ℤ) × ℤ => f (Function.update q.1 x q.2)) :=
    hfm.comp hu.measurable
  have hbnd : ∀ᵐ q ∂((LatticeProb.iidLaw d ν).prod ν),
      ‖f (Function.update q.1 x q.2)‖ ≤ 1 :=
    Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hfb _
  have hzui : Integrable (fun q : (Site d → ℤ) × ℤ => z (Function.update q.1 x q.2))
      ((LatticeProb.iidLaw d ν).prod ν) := hu.integrable_comp_of_integrable hzi
  have hFZ : Integrable (fun q : (Site d → ℤ) × ℤ =>
      f (Function.update q.1 x q.2) * z (Function.update q.1 x q.2))
      ((LatticeProb.iidLaw d ν).prod ν) := hzui.bdd_mul hfu.aestronglyMeasurable hbnd
  have hfz : Integrable (fun a : Site d → ℤ =>
      (∫ k, f (Function.update a x k) ∂ν) * ∫ k, z (Function.update a x k) ∂ν)
      (LatticeProb.iidLaw d ν) :=
    (Integrable.integral_prod_left hzui).bdd_mul
      (measurable_avgAt hfm x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs]; exact abs_avgAt_le hfm hfb x a)
  exact ((Integrable.integral_prod_left hFZ).sub hfz).congr
    (Filter.Eventually.of_forall fun a => rfl)

/-- **The mean of the one-site covariances with the count is the covariance with
that count.** -/
theorem integral_cov_coord {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {f : (Site d → ℤ) → ℝ} (hfm : Measurable f) (hfb : ∀ a, |f a| ≤ 1)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (x : Site d) :
    ∫ a, cov ν (fun k => f (Function.update a x k)) (fun k : ℤ => (k : ℝ))
        ∂(LatticeProb.iidLaw d ν)
      = cov (LatticeProb.iidLaw d ν) f (fun a => ((a x : ℤ) : ℝ)) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hcoordm : Measurable (fun a : Site d → ℤ => ((a x : ℤ) : ℝ)) :=
    (measurable_int_fun (fun k : ℤ => (k : ℝ))).comp (measurable_pi_apply x)
  have hz := cov_split_coord hfm hcoordm hfb (integrable_coord hint x) x
  have h1 : avgAt ν x (fun a : Site d → ℤ => ((a x : ℤ) : ℝ))
      = fun _ : Site d → ℤ => ∫ k : ℤ, (k : ℝ) ∂ν := by
    funext a
    unfold avgAt
    simp
  rw [h1, cov_const_right, zero_add] at hz
  simp only [Function.update_self] at hz
  exact hz.symm

/-- The average over the count at `x` has the same covariance with the count at
another site. -/
theorem cov_avgAt_coord {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {f : (Site d → ℤ) → ℝ} (hfm : Measurable f) (hfb : ∀ a, |f a| ≤ 1)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {x y : Site d} (hxy : y ≠ x) :
    cov (LatticeProb.iidLaw d ν) (avgAt ν x f) (fun a => ((a y : ℤ) : ℝ))
      = cov (LatticeProb.iidLaw d ν) f (fun a => ((a y : ℤ) : ℝ)) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hcoordm : Measurable (fun a : Site d → ℤ => ((a y : ℤ) : ℝ)) :=
    (measurable_int_fun (fun k : ℤ => (k : ℝ))).comp (measurable_pi_apply y)
  have hz := cov_split_coord hfm hcoordm hfb (integrable_coord hint y) x
  rw [avgAt_coord_of_ne hxy] at hz
  have h0 : ∫ a, cov ν (fun k => f (Function.update a x k))
      (fun k => ((Function.update a x k y : ℤ) : ℝ)) ∂(LatticeProb.iidLaw d ν) = 0 := by
    have : ∀ a : Site d → ℤ, cov ν (fun k => f (Function.update a x k))
        (fun k => ((Function.update a x k y : ℤ) : ℝ)) = 0 := by
      intro a
      simp only [Function.update_of_ne hxy]
      exact cov_const_right ν _ _
    simp [this]
  rw [h0, add_zero] at hz
  exact hz.symm

/-- **Step 1 of `lem:product` for finitely many sites.**  This is the paper's
`|Cov(f(Y), z(Y))| ≤ Cov(f(Y), Y)` at `parking.tex:2345-2365`, summed over the
tilted sites. -/
theorem abs_cov_counts_le {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) :
    ∀ (N : Finset (Site d)) (f z : (Site d → ℤ) → ℝ), Measurable f → Measurable z →
      DependsOnCounts N f → DependsOnCounts N z →
      (∀ a, |f a| ≤ 1) →
      (∀ (y : Site d) (a : Site d → ℤ), Monotone (fun k : ℤ => f (Function.update a y k))) →
      (∀ (y : Site d) (a : Site d → ℤ) (k k' : ℤ),
        |z (Function.update a y k) - z (Function.update a y k')| ≤ |(k : ℝ) - (k' : ℝ)|) →
      Integrable z (LatticeProb.iidLaw d ν) →
      |cov (LatticeProb.iidLaw d ν) f z|
        ≤ ∑ x ∈ N, cov (LatticeProb.iidLaw d ν) f (fun a => ((a x : ℤ) : ℝ)) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  intro N
  induction N using Finset.induction_on with
  | empty =>
      intro f z _hfm _hzm hfN _hzN _hfb _hfmono _hzlip _hzi
      have hc : f = fun _ : Site d → ℤ => f (fun _ : Site d => (0 : ℤ)) :=
        funext fun a => hfN a _ (by simp)
      rw [hc, cov_const_left]
      simp
  | insert x N' hx ih =>
      intro f z hfm hzm hfN hzN hfb hfmono hzlip hzi
      have hsplit := cov_split_coord hfm hzm hfb hzi x
      have hcondbd : ∀ a : Site d → ℤ,
          |cov ν (fun k => f (Function.update a x k)) (fun k => z (Function.update a x k))|
            ≤ cov ν (fun k => f (Function.update a x k)) (fun k : ℤ => (k : ℝ)) := fun a =>
        abs_cov_le_cov_cast (hfmono x a) (fun k => hfb _) (fun k k' => hzlip x a k k') hint
      have hcoordm : Measurable (fun a : Site d → ℤ => ((a x : ℤ) : ℝ)) :=
        (measurable_int_fun (fun k : ℤ => (k : ℝ))).comp (measurable_pi_apply x)
      have hi1 : Integrable (fun a : Site d → ℤ =>
          cov ν (fun k => f (Function.update a x k)) (fun k => z (Function.update a x k)))
          (LatticeProb.iidLaw d ν) := integrable_cov_section hfm hzm hfb hzi x
      have hi2 : Integrable (fun a : Site d → ℤ =>
          cov ν (fun k => f (Function.update a x k)) (fun k : ℤ => (k : ℝ)))
          (LatticeProb.iidLaw d ν) := by
        have h := integrable_cov_section hfm hcoordm hfb (integrable_coord hint x) x
        simpa only [Function.update_self] using h
      have hterm : |∫ a, cov ν (fun k => f (Function.update a x k))
            (fun k => z (Function.update a x k)) ∂(LatticeProb.iidLaw d ν)|
          ≤ cov (LatticeProb.iidLaw d ν) f (fun a => ((a x : ℤ) : ℝ)) := by
        calc |∫ a, cov ν (fun k => f (Function.update a x k))
              (fun k => z (Function.update a x k)) ∂(LatticeProb.iidLaw d ν)|
            ≤ ∫ a, |cov ν (fun k => f (Function.update a x k))
                (fun k => z (Function.update a x k))| ∂(LatticeProb.iidLaw d ν) :=
              abs_integral_le_integral_abs
          _ ≤ ∫ a, cov ν (fun k => f (Function.update a x k)) (fun k : ℤ => (k : ℝ))
                ∂(LatticeProb.iidLaw d ν) := integral_mono hi1.abs hi2 hcondbd
          _ = cov (LatticeProb.iidLaw d ν) f (fun a => ((a x : ℤ) : ℝ)) :=
              integral_cov_coord hfm hfb hint x
      have hIH := ih (avgAt ν x f) (avgAt ν x z) (measurable_avgAt hfm x)
        (measurable_avgAt hzm x) (avgAt_dependsOnCounts hfN) (avgAt_dependsOnCounts hzN)
        (fun a => abs_avgAt_le hfm hfb x a)
        (fun y a => avgAt_monotone hfm hfb hfmono x y a)
        (fun y a k k' => avgAt_lipschitz hzm hzlip hint x y a k k')
        (integrable_avgAt hzi x)
      have hsum : ∑ y ∈ N', cov (LatticeProb.iidLaw d ν) (avgAt ν x f)
            (fun a => ((a y : ℤ) : ℝ))
          = ∑ y ∈ N', cov (LatticeProb.iidLaw d ν) f (fun a => ((a y : ℤ) : ℝ)) :=
        Finset.sum_congr rfl fun y hy =>
          cov_avgAt_coord hfm hfb hint (fun hc => hx (hc ▸ hy))
      rw [hsum] at hIH
      rw [Finset.sum_insert hx, hsplit]
      calc |cov (LatticeProb.iidLaw d ν) (avgAt ν x f) (avgAt ν x z)
            + ∫ a, cov ν (fun k => f (Function.update a x k))
                (fun k => z (Function.update a x k)) ∂(LatticeProb.iidLaw d ν)|
          ≤ |cov (LatticeProb.iidLaw d ν) (avgAt ν x f) (avgAt ν x z)|
            + |∫ a, cov ν (fun k => f (Function.update a x k))
                (fun k => z (Function.update a x k)) ∂(LatticeProb.iidLaw d ν)| :=
            abs_add_le _ _
        _ ≤ (∑ y ∈ N', cov (LatticeProb.iidLaw d ν) f (fun a => ((a y : ℤ) : ℝ)))
            + cov (LatticeProb.iidLaw d ν) f (fun a => ((a x : ℤ) : ℝ)) :=
            add_le_add hIH hterm
        _ = cov (LatticeProb.iidLaw d ν) f (fun a => ((a x : ℤ) : ℝ))
            + ∑ y ∈ N', cov (LatticeProb.iidLaw d ν) f (fun a => ((a y : ℤ) : ℝ)) := by
            ring

end Parking

end
