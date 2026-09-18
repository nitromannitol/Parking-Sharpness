/-
**A maximal displacement inequality for the `d`-dimensional simple random walk, uniform in the
horizon.**  This is the "maximal-displacement tail" piece of the cutoff construction needed for
the equicontinuity clause of `prop:spatial-scaling`: the route of
`Parking.abs_u_sub_le_of_linPotential_osc` needs a global bound on the linear field's
oscillation over the WHOLE lattice, which cannot hold with high probability, because the walk
driving `Parking.stoppingSup` can in principle read the reward anywhere it can reach within its
horizon.  Bounding how far it CAN reach, with high probability, is what turns "the reward is
unbounded on the whole lattice" into "the reward the optimal stopping value actually reads is,
with high probability, bounded on a fixed compact box."

Transposed from the oriented node's `Parking/Support/TightWalkMaximal.lean` (Doob's maximal
inequality applied to the submartingale of a coordinate's squared partial sum), generalized from
the oriented model's single coordinate-difference statistic to a general dimension `d` and to
EVERY coordinate of the walk's own position, then combined by a union bound into a bound on the
walk's `Parking.graphNorm` displacement.  The per-coordinate step distribution is `Parking.stepLaw
d`/`Parking.stepVec` (this repository's own SIMPLE random walk, not the oriented one), so the
per-step variance of one fixed coordinate is `1/d` (a step touches a given coordinate with
probability `1/d`, and moves it by exactly `±1` when it does), giving a maximal inequality
`P(sup_{k≤n} |X_k(ℓ)| ≥ A) ≤ n/(d·A²)` for one coordinate `ℓ` and, after a union bound over the
`d` coordinates, `P(sup_{k≤n} graphNorm(X_k) ≥ d·A) ≤ n/A²` for the walk's own `ℓ¹` displacement.
-/
import Parking.Support.Pathwise
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ConditionalExpectation

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal ENNReal

noncomputable section

namespace Parking

variable {d : ℕ}

/-! ### One coordinate of one step, as a real-valued function of the direction -/

/-- **The `ℓ`-th coordinate of one signed step**, as a real number: `0` unless the step touches
coordinate `ℓ`, in which case `±1`. -/
def coordStep (ℓ : Fin d) (b : Fin d × Bool) : ℝ := ((stepVec b : Site d) ℓ : ℝ)

theorem stepVec_apply (b : Fin d × Bool) (j : Fin d) :
    (stepVec b : Site d) j = if j = b.1 then (if b.2 then (1 : ℤ) else -1) else 0 := by
  rcases b with ⟨i, s⟩
  cases s <;>
    (simp [stepVec, LatticeProb.unit, Pi.single_apply]
     try (split_ifs <;> ring))

theorem coordStep_eq (ℓ : Fin d) (b : Fin d × Bool) :
    coordStep ℓ b = if ℓ = b.1 then (if b.2 then (1 : ℝ) else -1) else 0 := by
  unfold coordStep
  rw [stepVec_apply]
  split_ifs <;> norm_num

theorem abs_coordStep_le (ℓ : Fin d) (b : Fin d × Bool) : |coordStep ℓ b| ≤ 1 := by
  rw [coordStep_eq]; split_ifs <;> norm_num

/-- **The mean of one coordinate's step is `0`.** -/
theorem integral_coordStep (hd : 1 ≤ d) (ℓ : Fin d) :
    ∫ b : Fin d × Bool, coordStep ℓ b ∂(stepLaw d) = 0 := by
  rw [integral_stepLaw hd]
  have hsum : (∑ b : Fin d × Bool, coordStep ℓ b) = 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Fintype.sum_bool]
    simp only [coordStep_eq]
    by_cases h : ℓ = i <;> simp [h]
  rw [hsum]; simp

/-- **The mean-square of one coordinate's step is `1/d`.** -/
theorem integral_sq_coordStep (hd : 1 ≤ d) (ℓ : Fin d) :
    ∫ b : Fin d × Bool, (coordStep ℓ b) ^ 2 ∂(stepLaw d) = 1 / d := by
  rw [integral_stepLaw hd]
  have hsum : (∑ b : Fin d × Bool, (coordStep ℓ b) ^ 2) = 2 := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single ℓ]
    · rw [Fintype.sum_bool]
      norm_num [coordStep_eq]
    · intro i _ hi
      rw [Fintype.sum_bool]
      simp [coordStep_eq, Ne.symm hi]
    · intro h; exact absurd (Finset.mem_univ ℓ) h
  rw [hsum, ← div_div]
  norm_num

/-! ### The partial sum of one coordinate along the walk -/

/-- **The partial sum of the `ℓ`-th coordinate of the first `k` steps.** -/
def coordSum (ℓ : Fin d) (k : ℕ) (p : ℕ → Fin d × Bool) : ℝ :=
  ∑ j ∈ Finset.range k, coordStep ℓ (p j)

theorem coordSum_succ (ℓ : Fin d) (k : ℕ) (p : ℕ → Fin d × Bool) :
    coordSum ℓ (k + 1) p = coordSum ℓ k p + coordStep ℓ (p k) := by
  unfold coordSum
  rw [Finset.sum_range_succ]

/-- **`Parking.coordSum` is exactly the `ℓ`-th coordinate of the walk's own position.** -/
theorem coordSum_eq_walkPath (ℓ : Fin d) (k : ℕ) (p : ℕ → Fin d × Bool) :
    coordSum ℓ k p = ((walkPath (0 : Site d) p k) ℓ : ℝ) := by
  induction k with
  | zero => simp [coordSum, walkPath]
  | succ k ih =>
      rw [coordSum_succ, ih]
      show _ = (((walkPath (0 : Site d) p k) + stepVec (p k)) ℓ : ℝ)
      unfold coordStep
      rw [Pi.add_apply]
      push_cast
      ring

theorem measurable_coordSum (hd : 1 ≤ d) (ℓ : Fin d) (k : ℕ) : Measurable (coordSum ℓ k) :=
  measurable_of_finite_dependence hd k _
    (fun p q hpq => Finset.sum_congr rfl fun j hj => by
      rw [Finset.mem_range] at hj; rw [hpq j hj])

theorem abs_coordSum_le (ℓ : Fin d) (k : ℕ) (p : ℕ → Fin d × Bool) :
    |coordSum ℓ k p| ≤ k := by
  calc |coordSum ℓ k p| ≤ ∑ j ∈ Finset.range k, |coordStep ℓ (p j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) := Finset.sum_le_sum fun j _ => abs_coordStep_le ℓ (p j)
    _ = k := by rw [Finset.sum_const, Finset.card_range]; simp

/-! ### The natural filtration of `Parking.coordSum ℓ`, and the independence of one step -/

theorem stronglyMeasurable_coordSum (hd : 1 ≤ d) (ℓ : Fin d) (k : ℕ) :
    StronglyMeasurable (coordSum ℓ k) :=
  (measurable_coordSum hd ℓ k).stronglyMeasurable

/-- **The natural filtration of `Parking.coordSum ℓ`.** -/
def coordFiltration (hd : 1 ≤ d) (ℓ : Fin d) :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Fin d × Bool)) :=
  Filtration.natural (coordSum ℓ) (stronglyMeasurable_coordSum hd ℓ)

theorem stronglyAdapted_coordFiltration (hd : 1 ≤ d) (ℓ : Fin d) :
    StronglyAdapted (coordFiltration hd ℓ) (coordSum ℓ) :=
  Filtration.stronglyAdapted_natural (stronglyMeasurable_coordSum hd ℓ)

theorem coordFiltration_le_iSup_coord (hd : 1 ≤ d) (ℓ : Fin d) (k : ℕ) :
    coordFiltration hd ℓ k ≤ ⨆ i ∈ Set.Iio k,
      MeasurableSpace.comap (fun p : ℕ → Fin d × Bool => p i) inferInstance := by
  set M : MeasurableSpace (ℕ → Fin d × Bool) :=
    ⨆ i ∈ Set.Iio k, MeasurableSpace.comap (fun p : ℕ → Fin d × Bool => p i) inferInstance
    with hMdef
  show (⨆ j ≤ k, MeasurableSpace.comap (coordSum ℓ j) inferInstance) ≤ M
  refine iSup₂_le fun j hjk => ?_
  rw [← measurable_iff_comap_le]
  show Measurable[M] (fun p => ∑ i ∈ Finset.range j, coordStep ℓ (p i))
  refine Finset.measurable_sum (Finset.range j) fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hik : i ∈ Set.Iio k := lt_of_lt_of_le hi hjk
  have heval : Measurable[M] (fun p : ℕ → Fin d × Bool => p i) := by
    rw [hMdef]
    exact measurable_iff_comap_le.mpr
      (le_biSup (fun i => MeasurableSpace.comap (fun p : ℕ → Fin d × Bool => p i) inferInstance)
        hik)
  exact (Measurable.of_discrete (f := fun b : Fin d × Bool => coordStep ℓ b)).comp heval

theorem iIndep_coord_walk (hd : 1 ≤ d) :
    iIndep (fun j : ℕ => MeasurableSpace.comap (fun p : ℕ → Fin d × Bool => p j) inferInstance)
      (walkLaw d) := by
  haveI := stepLaw_isProbability hd
  exact (iIndepFun_infinitePi (Ω := fun _ : ℕ => Fin d × Bool) (P := fun _ : ℕ => stepLaw d)
    (X := fun (_ : ℕ) (b : Fin d × Bool) => b) (fun _ => Measurable.of_discrete)).iIndep

theorem indep_coord_coordFiltration (hd : 1 ≤ d) (ℓ : Fin d) (k : ℕ) :
    Indep (MeasurableSpace.comap (fun p : ℕ → Fin d × Bool => p k) inferInstance)
      (coordFiltration hd ℓ k) (walkLaw d) := by
  have h_le : ∀ j : ℕ, MeasurableSpace.comap (fun p : ℕ → Fin d × Bool => p j) inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → Fin d × Bool)) :=
    fun j => measurable_iff_comap_le.mp (measurable_pi_apply j)
  have hST : Disjoint (Set.Iio k) ({k} : Set ℕ) := by
    simp [Set.disjoint_singleton_right]
  have h1 := indep_iSup_of_disjoint h_le (iIndep_coord_walk hd) hST
  rw [_root_.iSup_singleton] at h1
  exact indep_of_indep_of_le h1.symm le_rfl (coordFiltration_le_iSup_coord hd ℓ k)

/-! ### `Parking.coordSum ℓ` is a martingale, and its square is a submartingale -/

theorem integrable_coordSum (hd : 1 ≤ d) (ℓ : Fin d) (k : ℕ) :
    Integrable (coordSum ℓ k) (walkLaw d) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  exact Integrable.mono' (integrable_const (k : ℝ)) (measurable_coordSum hd ℓ k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact abs_coordSum_le ℓ k p)

theorem integrable_coordSum_sq (hd : 1 ≤ d) (ℓ : Fin d) (k : ℕ) :
    Integrable (fun p => (coordSum ℓ k p) ^ 2) (walkLaw d) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  refine Integrable.mono' (integrable_const ((k : ℝ) ^ 2))
    ((measurable_coordSum hd ℓ k).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc (coordSum ℓ k p) ^ 2 = |coordSum ℓ k p| ^ 2 := (sq_abs _).symm
    _ ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_coordSum_le ℓ k p) 2

/-- **The mean of one coordinate's step, read at the `k`-th direction of the walk.** -/
theorem integral_coordStep_eval (hd : 1 ≤ d) (ℓ : Fin d) (k : ℕ) :
    ∫ p : ℕ → Fin d × Bool, coordStep ℓ (p k) ∂(walkLaw d) = 0 := by
  haveI := stepLaw_isProbability hd
  have hmap : (walkLaw d).map (fun p : ℕ → Fin d × Bool => p k) = stepLaw d :=
    Measure.infinitePi_map_eval _ _
  have hmeas : Measurable (fun b : Fin d × Bool => coordStep ℓ b) := Measurable.of_discrete
  have hpull : ∫ b, coordStep ℓ b ∂((walkLaw d).map (fun p : ℕ → Fin d × Bool => p k))
      = ∫ p : ℕ → Fin d × Bool, coordStep ℓ (p k) ∂(walkLaw d) :=
    integral_map (measurable_pi_apply k).aemeasurable hmeas.aestronglyMeasurable
  have hrw : (∫ p : ℕ → Fin d × Bool, coordStep ℓ (p k) ∂(walkLaw d))
      = ∫ b, coordStep ℓ b ∂(stepLaw d) := by
    rw [← hmap]; exact hpull.symm
  rw [hrw, integral_coordStep hd ℓ]

theorem condExp_coordStep_coordFiltration (hd : 1 ≤ d) (ℓ : Fin d) (k : ℕ) :
    (walkLaw d)[fun p => coordStep ℓ (p k) | coordFiltration hd ℓ k] =ᵐ[walkLaw d] 0 := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hSM : StronglyMeasurable[MeasurableSpace.comap
      (fun p : ℕ → Fin d × Bool => p k) inferInstance] (fun p : ℕ → Fin d × Bool =>
      coordStep ℓ (p k)) := by
    have heval : Measurable[MeasurableSpace.comap (fun p : ℕ → Fin d × Bool => p k)
        inferInstance] (fun p : ℕ → Fin d × Bool => p k) :=
      measurable_iff_comap_le.mpr le_rfl
    exact ((Measurable.of_discrete (f := fun b : Fin d × Bool => coordStep ℓ b)).comp
      heval).stronglyMeasurable
  have hle₁ : MeasurableSpace.comap (fun p : ℕ → Fin d × Bool => p k) inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → Fin d × Bool)) :=
    measurable_iff_comap_le.mp (measurable_pi_apply k)
  have h := condExp_indep_eq (μ := walkLaw d) (m₁ := MeasurableSpace.comap
      (fun p : ℕ → Fin d × Bool => p k) inferInstance) (m₂ := coordFiltration hd ℓ k)
    hle₁ (Filtration.le (coordFiltration hd ℓ) k) hSM (indep_coord_coordFiltration hd ℓ k)
  filter_upwards [h] with p hp
  rw [hp]
  exact integral_coordStep_eval hd ℓ k

theorem martingale_coordSum (hd : 1 ≤ d) (ℓ : Fin d) :
    Martingale (coordSum ℓ) (coordFiltration hd ℓ) (walkLaw d) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  refine martingale_of_condExp_sub_eq_zero_nat (stronglyAdapted_coordFiltration hd ℓ)
    (integrable_coordSum hd ℓ) fun i => ?_
  have heq : (coordSum ℓ (i + 1) - coordSum ℓ i) = fun p => coordStep ℓ (p i) := by
    funext p
    simp only [Pi.sub_apply]
    show (∑ j ∈ Finset.range (i + 1), coordStep ℓ (p j))
        - (∑ j ∈ Finset.range i, coordStep ℓ (p j)) = coordStep ℓ (p i)
    rw [Finset.sum_range_succ]
    ring
  rw [heq]
  exact condExp_coordStep_coordFiltration hd ℓ i

/-- **The conditional increment of the squared partial sum is identically `1/d`**: a step
touches coordinate `ℓ` with probability `1/d`, and moves it by exactly `±1` when it does. -/
theorem condExp_sq_coordSum_sub (hd : 1 ≤ d) (ℓ : Fin d) (i : ℕ) :
    (walkLaw d)[fun p => (coordSum ℓ (i + 1) p) ^ 2 - (coordSum ℓ i p) ^ 2 |
        coordFiltration hd ℓ i] =ᵐ[walkLaw d] fun _ => 1 / (d : ℝ) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hstepMeas : Measurable (fun p : ℕ → Fin d × Bool => coordStep ℓ (p i)) :=
    (Measurable.of_discrete (f := fun b : Fin d × Bool => coordStep ℓ b)).comp
      (measurable_pi_apply i)
  have hpt : ∀ p : ℕ → Fin d × Bool, (coordSum ℓ (i + 1) p) ^ 2 - (coordSum ℓ i p) ^ 2
      = (2 * coordSum ℓ i p) * coordStep ℓ (p i) + (coordStep ℓ (p i)) ^ 2 := by
    intro p
    have hsucc : coordSum ℓ (i + 1) p = coordSum ℓ i p + coordStep ℓ (p i) := by
      show (∑ j ∈ Finset.range (i + 1), coordStep ℓ (p j))
          = (∑ j ∈ Finset.range i, coordStep ℓ (p j)) + coordStep ℓ (p i)
      rw [Finset.sum_range_succ]
    rw [hsucc]; ring
  have hbSq : ∀ b : Fin d × Bool, (coordStep ℓ b) ^ 2 = if ℓ = b.1 then (1 : ℝ) else 0 := by
    intro b; rw [coordStep_eq]; split_ifs <;> norm_num
  have hSqConst : ∀ p : ℕ → Fin d × Bool, (coordStep ℓ (p i)) ^ 2
      = if ℓ = (p i).1 then (1 : ℝ) else 0 := fun p => hbSq (p i)
  -- Split by linearity into the cross term and the pure step-square term.
  -- The cross term has conditional mean `0`, since the step is independent of the past.
  -- The step-square term has conditional mean `1/d`, by `Parking.integral_sq_coordStep`;
  -- the two conditional means therefore add up to `1/d`.
  have heq : (fun p => (coordSum ℓ (i + 1) p) ^ 2 - (coordSum ℓ i p) ^ 2)
      = (fun p => (2 * coordSum ℓ i p) * coordStep ℓ (p i))
        + fun p => (coordStep ℓ (p i)) ^ 2 := by
    funext p; rw [Pi.add_apply]; exact hpt p
  rw [heq]
  have hle : coordFiltration hd ℓ i ≤ (inferInstance : MeasurableSpace (ℕ → Fin d × Bool)) :=
    Filtration.le (coordFiltration hd ℓ) i
  have hSMf : StronglyMeasurable[coordFiltration hd ℓ i] (fun p => 2 * coordSum ℓ i p) :=
    stronglyMeasurable_const.mul (stronglyAdapted_coordFiltration hd ℓ i)
  have hfbound : ∀ᵐ p ∂(walkLaw d), ‖2 * coordSum ℓ i p‖ ≤ (2 * i : ℝ) := by
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left (abs_coordSum_le ℓ i p) (by norm_num)
  have hgint : Integrable (fun p => coordStep ℓ (p i)) (walkLaw d) :=
    Integrable.mono' (integrable_const (1 : ℝ)) hstepMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]; exact abs_coordStep_le ℓ (p i))
  have hmul := condExp_stronglyMeasurable_mul_of_bound hle hSMf hgint (2 * i) hfbound
  have hmulEq : (fun p => 2 * coordSum ℓ i p) * (fun p => coordStep ℓ (p i))
      = fun p => 2 * coordSum ℓ i p * coordStep ℓ (p i) := by
    funext p; rw [Pi.mul_apply]
  rw [hmulEq] at hmul
  have hint1 : Integrable (fun p => (2 * coordSum ℓ i p) * coordStep ℓ (p i)) (walkLaw d) := by
    refine Integrable.mono' (integrable_const (2 * i : ℝ)) ?_
      (Filter.Eventually.of_forall fun p => ?_)
    · exact (((measurable_coordSum hd ℓ i).const_mul 2).mul hstepMeas).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      have h1 : |2 * coordSum ℓ i p| ≤ (2 * i : ℝ) := by
        rw [abs_mul, abs_two]
        exact mul_le_mul_of_nonneg_left (abs_coordSum_le ℓ i p) (by norm_num)
      calc |2 * coordSum ℓ i p| * |coordStep ℓ (p i)|
          ≤ (2 * i : ℝ) * 1 :=
            mul_le_mul h1 (abs_coordStep_le ℓ (p i)) (abs_nonneg _) (by positivity)
        _ = 2 * i := mul_one _
  have hqint : Integrable (fun p => (coordStep ℓ (p i)) ^ 2) (walkLaw d) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_
      (Filter.Eventually.of_forall fun p => ?_)
    · exact (hstepMeas.pow_const 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have := coordStep_eq ℓ (p i)
      rw [this]; split_ifs <;> norm_num
  have hqconst : (walkLaw d)[fun p => (coordStep ℓ (p i)) ^ 2 | coordFiltration hd ℓ i]
      =ᵐ[walkLaw d] fun _ => 1 / (d : ℝ) := by
    have hqSM : StronglyMeasurable[MeasurableSpace.comap
        (fun p : ℕ → Fin d × Bool => p i) inferInstance] (fun p : ℕ → Fin d × Bool =>
        (coordStep ℓ (p i)) ^ 2) := by
      have heval : Measurable[MeasurableSpace.comap (fun p : ℕ → Fin d × Bool => p i)
          inferInstance] (fun p : ℕ → Fin d × Bool => p i) :=
        measurable_iff_comap_le.mpr le_rfl
      exact (((Measurable.of_discrete (f := fun b : Fin d × Bool => coordStep ℓ b)).comp
        heval).pow_const 2).stronglyMeasurable
    have hle₁ : MeasurableSpace.comap (fun p : ℕ → Fin d × Bool => p i) inferInstance ≤
        (inferInstance : MeasurableSpace (ℕ → Fin d × Bool)) :=
      measurable_iff_comap_le.mp (measurable_pi_apply i)
    have h := condExp_indep_eq (μ := walkLaw d) (m₁ := MeasurableSpace.comap
        (fun p : ℕ → Fin d × Bool => p i) inferInstance) (m₂ := coordFiltration hd ℓ i)
      hle₁ hle hqSM (indep_coord_coordFiltration hd ℓ i)
    filter_upwards [h] with p hp
    rw [hp]
    have hpull : ∫ b, (coordStep ℓ b) ^ 2 ∂((walkLaw d).map (fun p : ℕ → Fin d × Bool => p i))
        = ∫ q : ℕ → Fin d × Bool, (coordStep ℓ (q i)) ^ 2 ∂(walkLaw d) :=
      integral_map (measurable_pi_apply i).aemeasurable
        (Measurable.of_discrete (f := fun b : Fin d × Bool => (coordStep ℓ b) ^ 2)).aestronglyMeasurable
    have hmap : (walkLaw d).map (fun p : ℕ → Fin d × Bool => p i) = stepLaw d :=
      Measure.infinitePi_map_eval _ _
    rw [hmap] at hpull
    rw [← hpull, integral_sq_coordStep hd ℓ]
  have hcombine := condExp_add hint1 hqint (coordFiltration hd ℓ i)
  have hzero := condExp_coordStep_coordFiltration hd ℓ i
  filter_upwards [hcombine, hmul, hzero, hqconst] with p hp1 hp2 hp3 hp4
  rw [hp1]
  simp only [Pi.add_apply]
  rw [hp2]
  simp only [Pi.mul_apply, Pi.zero_apply] at hp3 ⊢
  rw [hp3]
  simp only [mul_zero, zero_add]
  rw [hp4]

/-- **`(Parking.coordSum ℓ)²` is a submartingale for `Parking.coordFiltration`.** -/
theorem submartingale_coordSum_sq (hd : 1 ≤ d) (ℓ : Fin d) :
    Submartingale (fun k p => (coordSum ℓ k p) ^ 2) (coordFiltration hd ℓ) (walkLaw d) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  refine submartingale_of_condExp_sub_nonneg_nat
    (fun i => ((stronglyAdapted_coordFiltration hd ℓ i)).pow 2) (integrable_coordSum_sq hd ℓ)
    fun i => ?_
  have heq : ((fun p => (coordSum ℓ (i + 1) p) ^ 2) - fun p => (coordSum ℓ i p) ^ 2)
      = fun p => (coordSum ℓ (i + 1) p) ^ 2 - (coordSum ℓ i p) ^ 2 := by
    funext p; simp only [Pi.sub_apply]
  rw [heq]
  filter_upwards [condExp_sq_coordSum_sub hd ℓ i] with p hp
  rw [hp]; positivity

/-- **`E[(coordSum ℓ n)²] ≤ n/d`.** -/
theorem integral_coordSum_sq_le (hd : 1 ≤ d) (ℓ : Fin d) (n : ℕ) :
    ∫ p, (coordSum ℓ n p) ^ 2 ∂(walkLaw d) ≤ n / d := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  induction n with
  | zero =>
    have : (fun p : ℕ → Fin d × Bool => (coordSum ℓ 0 p) ^ 2) = fun _ => (0 : ℝ) := by
      funext p; show (coordSum ℓ 0 p) ^ 2 = 0
      show (∑ _j ∈ Finset.range 0, coordStep ℓ (p _j)) ^ 2 = 0
      simp
    rw [this]; simp
  | succ i ih =>
    have htower := integral_condExp (μ := walkLaw d)
      (f := fun p => (coordSum ℓ (i + 1) p) ^ 2 - (coordSum ℓ i p) ^ 2)
      (Filtration.le (coordFiltration hd ℓ) i)
    have hrhs : (∫ p, (walkLaw d)[fun p => (coordSum ℓ (i + 1) p) ^ 2 -
        (coordSum ℓ i p) ^ 2 | coordFiltration hd ℓ i] p ∂(walkLaw d))
        = ∫ _p : ℕ → Fin d × Bool, (1 / (d : ℝ)) ∂(walkLaw d) :=
      integral_congr_ae (condExp_sq_coordSum_sub hd ℓ i)
    rw [hrhs] at htower
    rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul,
      one_mul] at htower
    have hsub : (∫ p, ((coordSum ℓ (i + 1) p) ^ 2 - (coordSum ℓ i p) ^ 2) ∂(walkLaw d))
        = (∫ p, (coordSum ℓ (i + 1) p) ^ 2 ∂(walkLaw d))
          - ∫ p, (coordSum ℓ i p) ^ 2 ∂(walkLaw d) :=
      integral_sub (integrable_coordSum_sq hd ℓ (i + 1)) (integrable_coordSum_sq hd ℓ i)
    rw [hsub] at htower
    have hstep : (∫ p, (coordSum ℓ (i + 1) p) ^ 2 ∂(walkLaw d))
        = 1 / d + ∫ p, (coordSum ℓ i p) ^ 2 ∂(walkLaw d) := by linarith
    rw [hstep]
    have hcast : ((i : ℝ) + 1) / d = 1 / d + i / d := by ring
    push_cast
    rw [hcast]
    linarith

/-- **Doob's maximal inequality for one coordinate of the walk, uniform in `n`.** The event
that the `ℓ`-th coordinate ever exits a window of half-width `A` before time `n` has probability
at most `n/(d·A²)`. -/
theorem measureReal_sup_coordSum_sq_le (hd : 1 ≤ d) (ℓ : Fin d) (n : ℕ) {A : ℝ} (hA : 0 < A) :
    (walkLaw d).real {p | ∃ k ≤ n, A ≤ |coordSum ℓ k p|} ≤ (n : ℝ) / (d * A ^ 2) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  set ε : ℝ≥0 := (A ^ 2).toNNReal with hεdef
  have hεcoe : (ε : ℝ) = A ^ 2 := by rw [hεdef, Real.coe_toNNReal]; positivity
  have hmax := maximal_ineq (ε := ε) (submartingale_coordSum_sq hd ℓ)
    (fun k => fun p => sq_nonneg (coordSum ℓ k p)) n
  have hset_eq : {ω : ℕ → Fin d × Bool | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (coordSum ℓ k ω) ^ 2}
      = {p | ∃ k ≤ n, A ≤ |coordSum ℓ k p|} := by
    ext p
    simp only [Set.mem_setOf_eq]
    rw [Finset.le_sup'_iff]
    constructor
    · rintro ⟨k, hk, hkle⟩
      rw [Finset.mem_range] at hk
      refine ⟨k, by omega, ?_⟩
      rw [hεcoe] at hkle
      nlinarith [sq_abs (coordSum ℓ k p), abs_nonneg (coordSum ℓ k p), hA.le,
        sq_nonneg (|coordSum ℓ k p| - A)]
    · rintro ⟨k, hk, hkle⟩
      refine ⟨k, by rw [Finset.mem_range]; omega, ?_⟩
      rw [hεcoe]
      nlinarith [sq_abs (coordSum ℓ k p), hkle, hA.le]
  rw [hset_eq] at hmax
  have hbound : (∫ p in {p | ∃ k ≤ n, A ≤ |coordSum ℓ k p|},
      (coordSum ℓ n p) ^ 2 ∂(walkLaw d)) ≤ (n : ℝ) / d := by
    calc (∫ p in {p | ∃ k ≤ n, A ≤ |coordSum ℓ k p|},
          (coordSum ℓ n p) ^ 2 ∂(walkLaw d))
        ≤ ∫ p, (coordSum ℓ n p) ^ 2 ∂(walkLaw d) :=
          setIntegral_le_integral (integrable_coordSum_sq hd ℓ n)
            (Filter.Eventually.of_forall fun p => sq_nonneg _)
      _ ≤ (n : ℝ) / d := integral_coordSum_sq_le hd ℓ n
  have hεpos : (0 : ℝ) < ε := by rw [hεcoe]; positivity
  have h1 : (ε : ℝ≥0∞) * (walkLaw d) {p | ∃ k ≤ n, A ≤ |coordSum ℓ k p|}
      ≤ ENNReal.ofReal ((n:ℝ) / d) := hmax.trans (ENNReal.ofReal_le_ofReal hbound)
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (n:ℝ)/d)] at h2
  rw [hεcoe] at h2
  rw [MeasureTheory.measureReal_def]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < d * A ^ 2)]
  have h3 : (d : ℝ) * (A ^ 2 * ((walkLaw d) {p | ∃ k ≤ n, A ≤ |coordSum ℓ k p|}).toReal)
      ≤ d * ((n : ℝ) / d) := mul_le_mul_of_nonneg_left h2 hdR.le
  have hn : (d : ℝ) * ((n : ℝ) / d) = n := by field_simp
  rw [hn] at h3
  nlinarith [h3]

/-! ### The union bound over every coordinate: a maximal inequality for the walk's own
displacement, in `Parking.graphNorm` -/

/-- **The walk's own `ℓ¹` displacement rarely exits a large box, uniformly in the horizon `n`.**
The event that `Parking.walkPath` from the origin ever leaves the box of `Parking.graphNorm`-radius
`d·A` before time `n` has probability at most `n/A²`: a union bound, over the `d` coordinates, of
`Parking.measureReal_sup_coordSum_sq_le`. This is the tail estimate on how far the walk travels
in `n` steps that the cutoff construction requires. -/
theorem measureReal_sup_walkPath_graphNorm_le (hd : 1 ≤ d) (n : ℕ) {A : ℝ} (hA : 0 < A) :
    (walkLaw d).real
        {p | ∃ k ≤ n, (d : ℝ) * A ≤ (graphNorm (walkPath (0 : Site d) p k) : ℝ)}
      ≤ (n : ℝ) / A ^ 2 := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  haveI hne : Nonempty (Fin d) := ⟨(⟨0, hd⟩ : Fin d)⟩
  have hsub : {p | ∃ k ≤ n, (d : ℝ) * A ≤ (graphNorm (walkPath (0 : Site d) p k) : ℝ)}
      ⊆ ⋃ ℓ : Fin d, {p | ∃ k ≤ n, A ≤ |coordSum ℓ k p|} := by
    rintro p ⟨k, hk, hkle⟩
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hcon
    have hall : ∀ ℓ : Fin d, |coordSum ℓ k p| < A := by
      intro ℓ
      rcases lt_or_ge (|coordSum ℓ k p|) A with h | h
      · exact h
      · exact absurd (⟨hk, h⟩ : k ≤ n ∧ A ≤ |coordSum ℓ k p|) (hcon ℓ k)
    have hlt : (graphNorm (walkPath (0 : Site d) p k) : ℝ) < d * A := by
      unfold graphNorm
      push_cast
      calc (∑ i : Fin d, (((walkPath (0 : Site d) p k) i).natAbs : ℝ))
          = ∑ i : Fin d, |coordSum i k p| := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [coordSum_eq_walkPath]
            exact (Nat.cast_natAbs _).trans Int.cast_abs
        _ < ∑ _i : Fin d, A := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
            (fun i _ => hall i)
        _ = d * A := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  calc (walkLaw d).real
        {p | ∃ k ≤ n, (d : ℝ) * A ≤ (graphNorm (walkPath (0 : Site d) p k) : ℝ)}
      ≤ (walkLaw d).real (⋃ ℓ : Fin d, {p | ∃ k ≤ n, A ≤ |coordSum ℓ k p|}) :=
        measureReal_mono hsub
    _ ≤ ∑ ℓ : Fin d, (walkLaw d).real {p | ∃ k ≤ n, A ≤ |coordSum ℓ k p|} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ℓ : Fin d, (n : ℝ) / (d * A ^ 2) :=
        Finset.sum_le_sum fun ℓ _ => measureReal_sup_coordSum_sq_le hd ℓ n hA
    _ = (n : ℝ) / A ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hdR : (0:ℝ) < d := by exact_mod_cast hd
        field_simp

end Parking

end
