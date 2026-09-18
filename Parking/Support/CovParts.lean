/-
The comparison of Step 2 of `lem:product` (`parking.tex:2396-2412`), in the form
the model never enters.

The paper's Step 2 ends by comparing, term by term, the mean of the absolute
conditional covariances with `Cov(f(Y),Y)`.  It writes `Cov(f(Y),Y)` as a
summation by parts,

    Cov(f(Y),Y) = ∑_j (f(j)-f(j-1)) E[(Y-EY) 1{Y ≥ j}] ,

observes that every summand is nonnegative, and bounds the `j`-th expectation
below by `j P(Y=j)` for `j ≥ 1`, using `E Y ≤ 0`.

Here the summation by parts is replaced by a finite decomposition that needs no
convergence argument.  For a FINITE set `J` of integers, let

    g_J(y) = ∑_{j ∈ J} (f(j)-f(j-1)) 1{y ≥ j} .

Then `f - g_J` is nondecreasing, because its increment at `n+1` is the increment
of `f` there when `n+1 ∉ J` and zero when `n+1 ∈ J`; a nondecreasing function has
nonnegative covariance with the coordinate; and covariance is additive.  So

    Cov(f(Y),Y) ≥ Cov(g_J(Y),Y) = ∑_{j ∈ J} (f(j)-f(j-1)) Cov(1{Y ≥ j},Y)
                ≥ ∑_{j ∈ J} (f(j)-f(j-1)) j P(Y=j) ,

which is the paper's comparison, for every finite `J` of integers at least one.
-/
import Parking.Support.Cov

noncomputable section

namespace Parking

open MeasureTheory

variable {ν : Measure ℤ} [IsProbabilityMeasure ν]

/-! ### Boundedness gives integrability -/

/-- Boundedness of a function on the integers gives integrability. -/
theorem integrable_of_bdd {f : ℤ → ℝ} {B : ℝ} (hf : ∀ k : ℤ, |f k| ≤ B) :
    Integrable f ν := by
  refine Integrable.mono' (integrable_const B) (measurable_int_fun f).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  rw [Real.norm_eq_abs]
  exact hf k

omit [IsProbabilityMeasure ν] in
/-- A bounded function times the coordinate is integrable. -/
theorem integrable_bdd_mul_cast {f : ℤ → ℝ} {B : ℝ} (hf : ∀ k : ℤ, |f k| ≤ B)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) :
    Integrable (fun k : ℤ => f k * (k : ℝ)) ν := by
  refine Integrable.mono' (hint.const_mul B) (measurable_int_fun _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := hf k
  have h2 : (0 : ℝ) ≤ |(k : ℝ)| := abs_nonneg _
  have h3 : (0 : ℝ) ≤ |f k| := abs_nonneg _
  nlinarith

/-- **Chebyshev's association inequality** on one coordinate: a bounded
nondecreasing function has nonnegative covariance with the coordinate. -/
theorem cov_cast_nonneg {f : ℤ → ℝ} {B : ℝ} (hfmono : Monotone f) (hfbdd : ∀ k : ℤ, |f k| ≤ B)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) :
    0 ≤ cov ν f (fun k : ℤ => (k : ℝ)) := by
  have hcast : Integrable (fun k : ℤ => (k : ℝ)) ν := integrable_cast hint
  have hf : Integrable f ν := integrable_of_bdd hfbdd
  have hfc : Integrable (fun k : ℤ => f k * (k : ℝ)) ν := integrable_bdd_mul_cast hfbdd hint
  have q11 : Integrable (fun p : ℤ × ℤ => f p.1 * (p.1 : ℝ)) (ν.prod ν) := hfc.comp_fst ν
  have q22 : Integrable (fun p : ℤ × ℤ => f p.2 * (p.2 : ℝ)) (ν.prod ν) := hfc.comp_snd ν
  have q12 : Integrable (fun p : ℤ × ℤ => f p.1 * (p.2 : ℝ)) (ν.prod ν) := hf.mul_prod hcast
  have q21 : Integrable (fun p : ℤ × ℤ => f p.2 * (p.1 : ℝ)) (ν.prod ν) := by
    refine Integrable.congr (hcast.mul_prod hf) (Filter.Eventually.of_forall fun p => ?_)
    exact mul_comm _ _
  have hceq := two_mul_cov_eq (μ := ν) (f := f) (g := fun k : ℤ => (k : ℝ)) q11 q12 q21 q22
  have hnn : 0 ≤ ∫ p, (f p.1 - f p.2) * ((p.1 : ℝ) - (p.2 : ℝ)) ∂(ν.prod ν) := by
    refine integral_nonneg fun p => ?_
    rcases same_sign_of_monotone hfmono p.1 p.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact mul_nonneg h1 h2
    · have hmn := mul_nonneg (neg_nonneg.mpr h1) (neg_nonneg.mpr h2)
      rwa [neg_mul_neg] at hmn
  linarith [hceq, hnn]

/-! ### Covariance is additive and homogeneous in its first argument -/

omit [IsProbabilityMeasure ν] in
theorem cov_add_left {f g h : ℤ → ℝ} (hf : Integrable f ν) (hg : Integrable g ν)
    (hfh : Integrable (fun k => f k * h k) ν) (hgh : Integrable (fun k => g k * h k) ν) :
    cov ν (fun k => f k + g k) h = cov ν f h + cov ν g h := by
  unfold cov
  have h1 : ∫ k, (f k + g k) * h k ∂ν = (∫ k, f k * h k ∂ν) + ∫ k, g k * h k ∂ν := by
    rw [← integral_add hfh hgh]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => by ring)
  have h2 : ∫ k, (f k + g k) ∂ν = (∫ k, f k ∂ν) + ∫ k, g k ∂ν := integral_add hf hg
  rw [h1, h2]
  ring

omit [IsProbabilityMeasure ν] in
theorem cov_const_mul_left {f h : ℤ → ℝ} (c : ℝ) :
    cov ν (fun k => c * f k) h = c * cov ν f h := by
  unfold cov
  have h1 : ∫ k, c * f k * h k ∂ν = c * ∫ k, f k * h k ∂ν := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => by ring)
  have h2 : ∫ k, c * f k ∂ν = c * ∫ k, f k ∂ν := integral_const_mul c f
  rw [h1, h2]
  ring

omit [IsProbabilityMeasure ν] in
theorem cov_sum_left {ι : Type} (J : Finset ι) (f : ι → ℤ → ℝ) (h : ℤ → ℝ)
    (hf : ∀ i ∈ J, Integrable (f i) ν) (hfh : ∀ i ∈ J, Integrable (fun k => f i k * h k) ν) :
    cov ν (fun k => ∑ i ∈ J, f i k) h = ∑ i ∈ J, cov ν (f i) h := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [cov]
  | insert a s ha ih =>
      have hfa : Integrable (f a) ν := hf a (Finset.mem_insert_self a s)
      have hfha : Integrable (fun k => f a k * h k) ν := hfh a (Finset.mem_insert_self a s)
      have hfs : Integrable (fun k => ∑ i ∈ s, f i k) ν :=
        integrable_finsetSum s fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hfhs : Integrable (fun k => (∑ i ∈ s, f i k) * h k) ν := by
        refine Integrable.congr (integrable_finsetSum s
          (fun i hi => hfh i (Finset.mem_insert_of_mem hi))) ?_
        exact Filter.Eventually.of_forall fun k => by simp [Finset.sum_mul]
      have hkey := cov_add_left (ν := ν) (f := f a) (g := fun k => ∑ i ∈ s, f i k) (h := h)
        hfa hfs hfha hfhs
      have hrw : (fun k => ∑ i ∈ insert a s, f i k) = (fun k => f a k + ∑ i ∈ s, f i k) :=
        funext fun k => by rw [Finset.sum_insert ha]
      rw [hrw, hkey, Finset.sum_insert ha,
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hfh i (Finset.mem_insert_of_mem hi))]

/-! ### The covariance of an upper indicator with the coordinate -/

/-- The upper indicator `1{k ≥ j}`. -/
def upperInd (j : ℤ) : ℤ → ℝ := fun k => if j ≤ k then 1 else 0

theorem upperInd_bdd (j : ℤ) : ∀ k : ℤ, |upperInd j k| ≤ 1 := by
  intro k; unfold upperInd; split <;> norm_num

theorem upperInd_mono (j : ℤ) : Monotone (upperInd j) := by
  intro a b hab
  by_cases h : j ≤ a
  · have hb : j ≤ b := le_trans h hab
    simp [upperInd, h, hb]
  · simp only [upperInd, if_neg h]
    split <;> norm_num

/-- For `j ≥ 1` and a law of nonpositive mean, the covariance of `1{Y ≥ j}` with
`Y` is at least `j P(Y = j)`. -/
theorem cov_upperInd_ge {j : ℤ} (hj : 1 ≤ j) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν ≤ 0) :
    (j : ℝ) * (ν {j}).toReal ≤ cov ν (upperInd j) (fun k : ℤ => (k : ℝ)) := by
  classical
  have hP : 0 ≤ ∫ k, upperInd j k ∂ν := by
    refine integral_nonneg fun k => ?_
    unfold upperInd; split <;> norm_num
  have hPm : (∫ k, upperInd j k ∂ν) * (∫ k, (k : ℝ) ∂ν) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hP hmean
  have hind : Integrable (fun k : ℤ => (if k = j then (j : ℝ) else 0)) ν :=
    integrable_of_bdd (B := |(j : ℝ)|) (fun k => by split <;> simp [abs_nonneg])
  have hmul : Integrable (fun k : ℤ => upperInd j k * (k : ℝ)) ν :=
    integrable_bdd_mul_cast (upperInd_bdd j) hint
  have hpt : ∀ k : ℤ, (if k = j then (j : ℝ) else 0) ≤ upperInd j k * (k : ℝ) := by
    intro k
    by_cases hk : k = j
    · subst hk; simp [upperInd]
    · simp only [if_neg hk]
      unfold upperInd
      by_cases hjk : j ≤ k
      · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hj hjk
        simp only [if_pos hjk, one_mul]; linarith
      · simp [hjk]
  have hle : (∫ k, (if k = j then (j : ℝ) else 0) ∂ν)
      ≤ ∫ k, upperInd j k * (k : ℝ) ∂ν := integral_mono hind hmul hpt
  have heq : (∫ k, (if k = j then (j : ℝ) else 0) ∂ν) = (j : ℝ) * (ν {j}).toReal := by
    have hset : (fun k : ℤ => (if k = j then (j : ℝ) else 0))
        = Set.indicator ({j} : Set ℤ) (fun _ => (j : ℝ)) := by
      funext k; by_cases hk : k = j <;> simp [hk]
    rw [hset, integral_indicator (measurableSet_singleton j), setIntegral_const,
      smul_eq_mul, mul_comm, measureReal_def]
  unfold cov
  rw [← heq]
  linarith [hle, hPm]

/-! ### The term-by-term comparison -/

/-- **The comparison of Step 2 of `lem:product`.**  For a bounded nondecreasing
`f`, a law of nonpositive mean, and any finite set `J` of integers at least one,

    ∑_{j ∈ J} (f(j) - f(j-1)) j P(Y = j) ≤ Cov(f(Y), Y). -/
theorem sum_step_le_cov {f : ℤ → ℝ} {B : ℝ} (hfmono : Monotone f) (hfbdd : ∀ k : ℤ, |f k| ≤ B)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν ≤ 0)
    (J : Finset ℤ) (hJ : ∀ j ∈ J, 1 ≤ j) :
    ∑ j ∈ J, (f j - f (j - 1)) * ((j : ℝ) * (ν {j}).toReal)
      ≤ cov ν f (fun k : ℤ => (k : ℝ)) := by
  classical
  set Bg : ℝ := ∑ j ∈ J, |f j - f (j - 1)| with hBg
  set g : ℤ → ℝ := fun y => ∑ j ∈ J, (f j - f (j - 1)) * upperInd j y with hgdef
  have hgbdd : ∀ y : ℤ, |g y| ≤ Bg := by
    intro y
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    have h1 : |upperInd j y| ≤ 1 := upperInd_bdd j y
    have h2 : (0 : ℝ) ≤ |f j - f (j - 1)| := abs_nonneg _
    nlinarith
  have hdiffbdd : ∀ y : ℤ, |f y - g y| ≤ B + Bg := by
    intro y
    have h1 := hfbdd y
    have h2 := hgbdd y
    calc |f y - g y| ≤ |f y| + |g y| := abs_sub _ _
      _ ≤ B + Bg := by linarith
  have hstep : ∀ n : ℤ, g (n + 1) - g n = (if n + 1 ∈ J then f (n + 1) - f n else 0) := by
    intro n
    have hpt : ∀ j : ℤ, (f j - f (j - 1)) * upperInd j (n + 1)
        - (f j - f (j - 1)) * upperInd j n
        = if j = n + 1 then f (n + 1) - f n else 0 := by
      intro j
      by_cases hj1 : j = n + 1
      · subst hj1
        simp [upperInd]
      · by_cases hjn : j ≤ n
        · have hle : j ≤ n + 1 := by omega
          simp [upperInd, hjn, hle, hj1]
        · have h1 : ¬ j ≤ n + 1 := by omega
          simp [upperInd, hjn, h1, hj1]
    show (∑ j ∈ J, (f j - f (j - 1)) * upperInd j (n + 1))
        - ∑ j ∈ J, (f j - f (j - 1)) * upperInd j n = _
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun j _ => hpt j),
      Finset.sum_ite_eq' J (n + 1) (fun _ => f (n + 1) - f n)]
  have hmono : Monotone (fun y => f y - g y) := by
    refine monotone_int_of_le_succ fun n => ?_
    have h := hstep n
    have hf1 : f n ≤ f (n + 1) := hfmono (by omega)
    show f n - g n ≤ f (n + 1) - g (n + 1)
    by_cases hn : n + 1 ∈ J
    · rw [if_pos hn] at h; linarith
    · rw [if_neg hn] at h; linarith
  have hgint : Integrable g ν := integrable_of_bdd hgbdd
  have hdint : Integrable (fun y => f y - g y) ν := integrable_of_bdd hdiffbdd
  have hgmul : Integrable (fun k : ℤ => g k * (k : ℝ)) ν := integrable_bdd_mul_cast hgbdd hint
  have hdmul : Integrable (fun k : ℤ => (f k - g k) * (k : ℝ)) ν :=
    integrable_bdd_mul_cast hdiffbdd hint
  have hsplit : cov ν f (fun k : ℤ => (k : ℝ))
      = cov ν g (fun k : ℤ => (k : ℝ))
        + cov ν (fun y => f y - g y) (fun k : ℤ => (k : ℝ)) := by
    have hadd := cov_add_left (ν := ν) (f := g) (g := fun y => f y - g y)
      (h := fun k : ℤ => (k : ℝ)) hgint hdint hgmul hdmul
    rw [← hadd]
    congr 1
    funext y
    ring
  have hnn : 0 ≤ cov ν (fun y => f y - g y) (fun k : ℤ => (k : ℝ)) :=
    cov_cast_nonneg hmono hdiffbdd hint
  have hwbdd : ∀ j : ℤ, ∀ k : ℤ,
      |(f j - f (j - 1)) * upperInd j k| ≤ |f j - f (j - 1)| := by
    intro j k
    rw [abs_mul]
    have h1 : |upperInd j k| ≤ 1 := upperInd_bdd j k
    nlinarith [abs_nonneg (f j - f (j - 1)), abs_nonneg (upperInd j k)]
  have hgcov : cov ν g (fun k : ℤ => (k : ℝ))
      = ∑ j ∈ J, (f j - f (j - 1)) * cov ν (upperInd j) (fun k : ℤ => (k : ℝ)) := by
    rw [hgdef, cov_sum_left (ν := ν) J (fun j y => (f j - f (j - 1)) * upperInd j y)
      (fun k : ℤ => (k : ℝ))
      (fun j _ => integrable_of_bdd (hwbdd j))
      (fun j _ => integrable_bdd_mul_cast (hwbdd j) hint)]
    exact Finset.sum_congr rfl fun j _ => cov_const_mul_left _
  have hterm : ∀ j ∈ J, (f j - f (j - 1)) * ((j : ℝ) * (ν {j}).toReal)
      ≤ (f j - f (j - 1)) * cov ν (upperInd j) (fun k : ℤ => (k : ℝ)) := by
    intro j hj
    have hw : 0 ≤ f j - f (j - 1) := by
      have := hfmono (show j - 1 ≤ j by omega); linarith
    exact mul_le_mul_of_nonneg_left (cov_upperInd_ge (hJ j hj) hint hmean) hw
  calc ∑ j ∈ J, (f j - f (j - 1)) * ((j : ℝ) * (ν {j}).toReal)
      ≤ ∑ j ∈ J, (f j - f (j - 1)) * cov ν (upperInd j) (fun k : ℤ => (k : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = cov ν g (fun k : ℤ => (k : ℝ)) := hgcov.symm
    _ ≤ cov ν f (fun k : ℤ => (k : ℝ)) := by rw [hsplit]; linarith

/-- The same comparison over ALL the integers at least one.  The terms are
nonnegative and every partial sum is at most the covariance, so the series
converges and its sum obeys the same bound.  This is the form the paper's
`E|Cov(F,Z|Y)| ≤ 2 Cov(f(Y),Y)` needs, the mean of the conditional covariances
being a sum over the values of the count at the site. -/
theorem tsum_step_le_cov {f : ℤ → ℝ} {B : ℝ} (hfmono : Monotone f) (hfbdd : ∀ k : ℤ, |f k| ≤ B)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν ≤ 0) :
    Summable (fun j : ℤ => if 1 ≤ j then (f j - f (j - 1)) * ((j : ℝ) * (ν {j}).toReal) else 0) ∧
      ∑' j : ℤ, (if 1 ≤ j then (f j - f (j - 1)) * ((j : ℝ) * (ν {j}).toReal) else 0)
        ≤ cov ν f (fun k : ℤ => (k : ℝ)) := by
  classical
  have hpart : ∀ s : Finset ℤ,
      ∑ j ∈ s, (if 1 ≤ j then (f j - f (j - 1)) * ((j : ℝ) * (ν {j}).toReal) else 0)
        ≤ cov ν f (fun k : ℤ => (k : ℝ)) := by
    intro s
    have hfil : ∑ j ∈ s, (if 1 ≤ j then (f j - f (j - 1)) * ((j : ℝ) * (ν {j}).toReal) else 0)
        = ∑ j ∈ s.filter (fun j => 1 ≤ j), (f j - f (j - 1)) * ((j : ℝ) * (ν {j}).toReal) := by
      rw [Finset.sum_filter]
    rw [hfil]
    exact sum_step_le_cov hfmono hfbdd hint hmean _ fun j hj => (Finset.mem_filter.mp hj).2
  have hnn : 0 ≤ fun j : ℤ =>
      (if 1 ≤ j then (f j - f (j - 1)) * ((j : ℝ) * (ν {j}).toReal) else 0) := by
    intro j
    show (0 : ℝ) ≤ (if 1 ≤ j then (f j - f (j - 1)) * ((j : ℝ) * (ν {j}).toReal) else 0)
    by_cases hj : 1 ≤ j
    · rw [if_pos hj]
      have hw : 0 ≤ f j - f (j - 1) := by
        have := hfmono (show j - 1 ≤ j by omega); linarith
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ j)
      have := ENNReal.toReal_nonneg (a := ν {j})
      positivity
    · rw [if_neg hj]
  exact ⟨summable_of_sum_le hnn hpart,
    tsum_le_of_sum_le' (cov_cast_nonneg hfmono hfbdd hint) hpart⟩

end Parking

end
