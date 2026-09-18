/-
The piecewise bilinear interpolation of a grid field on `ℤ × ℤ`
(`parking.tex:3192-3203`).

The convergence in law of the cutoff rewards of the directed scaling limit is
formulated on the space `C(K)` of continuous functions on the box
`K = [0,T] × [-2A,2A]`, but the discrete field is only defined on the lattice
of rescaled grid points.  This module builds the bridge: the one-dimensional
hat function `hat1 t = max 0 (1 - |t|)`, the bilinear interpolation
`hatInterp V` of a grid field `V : ℤ → ℤ → ℝ` as a finite sum (the weights
have finite support), its continuity, its finite corner-set decompositions,
and the partition-of-unity identity of the hat weights.
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Int.Interval

noncomputable section
namespace Parking

open Filter Topology

/-- The one-dimensional hat function `max 0 (1 - |t|)`, the basis of the
piecewise bilinear interpolation of a grid field. -/
def hat1 (t : ℝ) : ℝ := max 0 (1 - |t|)

/-- **The hat is nonnegative.** -/
theorem hat1_nonneg (t : ℝ) : 0 ≤ hat1 t := le_max_left _ _

/-- **The hat is at most one.** -/
theorem hat1_le_one (t : ℝ) : hat1 t ≤ 1 :=
  max_le (by norm_num) (by linarith [abs_nonneg t])

/-- **The hat vanishes outside the unit interval around zero.** -/
theorem hat1_eq_zero {t : ℝ} (h : 1 ≤ |t|) : hat1 t = 0 :=
  max_eq_left (by linarith)

/-- **The hat at zero is one.** -/
@[simp] theorem hat1_zero : hat1 0 = 1 := by
  unfold hat1
  rw [abs_zero, sub_zero, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

/-- **The hat function is `1`-Lipschitz.** -/
theorem abs_hat1_sub_le (t s : ℝ) : |hat1 t - hat1 s| ≤ |t - s| := by
  have hmax : ∀ x : ℝ, max 0 x = (x + |x|) / 2 := fun x => by
    rcases lt_or_ge x 0 with h | h
    · rw [max_eq_left h.le, abs_of_neg h]
      ring
    · rw [max_eq_right h, abs_of_nonneg h]
      ring
  set a : ℝ := 1 - |t| with ha
  set b : ℝ := 1 - |s| with hb
  have h1 : |a - b| ≤ |t - s| := by
    rw [ha, hb, show (1 - |t|) - (1 - |s|) = |s| - |t| by ring, abs_sub_comm]
    exact abs_abs_sub_abs_le_abs_sub _ _
  have h2 : |(|a| - |b|)| ≤ |t - s| :=
    le_trans (abs_abs_sub_abs_le_abs_sub _ _) h1
  unfold hat1
  rw [← ha, ← hb, hmax, hmax]
  calc |((a + |a|) / 2) - ((b + |b|) / 2)|
      = |(((a - b) + (|a| - |b|)) / 2)| := by
        ring_nf
    _ ≤ (|a - b| + |(|a| - |b|)|) / 2 := by
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        gcongr
        exact abs_add_le _ _
    _ ≤ (|t - s| + |t - s|) / 2 := by
        gcongr
    _ = |t - s| := by ring

/-- **The hat function is continuous.** -/
theorem continuous_hat1 : Continuous hat1 := by
  have h : LipschitzWith 1 hat1 := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    exact abs_hat1_sub_le x y
  exact h.continuous

/-- **The support of a nonzero hat weight is inside the two floor corners.** -/
theorem hat1_ne_zero_mem_floor_pair {t : ℝ} {j : ℤ} (h : hat1 (t - (j : ℝ)) ≠ 0) :
    j = ⌊t⌋ ∨ j = ⌊t⌋ + 1 := by
  have hm : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
  have hm1 : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
  by_contra hne
  simp only [not_or] at hne
  apply h
  apply hat1_eq_zero
  rcases lt_or_ge j ⌊t⌋ with hjj | hjj
  · have hj1 : j ≤ ⌊t⌋ - 1 := by omega
    have hj1' : (j : ℝ) ≤ (⌊t⌋ : ℝ) - 1 := by
      have hcast : (j : ℝ) ≤ ((⌊t⌋ - 1 : ℤ) : ℝ) := by exact_mod_cast hj1
      push_cast at hcast
      linarith
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - (j : ℝ))]
    linarith
  · have hj2 : ⌊t⌋ + 2 ≤ j := by omega
    have hj2' : ((⌊t⌋ : ℝ) + 2) ≤ (j : ℝ) := by
      have hcast : ((⌊t⌋ + 2 : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
      push_cast at hcast
      linarith
    rw [abs_of_nonpos (by linarith : t - (j : ℝ) ≤ 0)]
    linarith

/-- **The integer translates of the hat form a partition of unity.** -/
theorem finsum_hat1 (t : ℝ) : ∑ᶠ j : ℤ, hat1 (t - (j : ℝ)) = 1 := by
  have hm : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
  have hm1 : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
  have hsupp : Function.support (fun j : ℤ => hat1 (t - (j : ℝ))) ⊆
      ({⌊t⌋, ⌊t⌋ + 1} : Finset ℤ) := by
    intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    exact hat1_ne_zero_mem_floor_pair hj
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp]
  rw [Finset.sum_pair (by omega)]
  have hv1 : hat1 (t - (⌊t⌋ : ℝ)) = 1 - (t - ⌊t⌋) := by
    unfold hat1
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - ⌊t⌋)]
    exact max_eq_right (by linarith)
  have hv2 : hat1 (t - ((⌊t⌋ + 1 : ℤ) : ℝ)) = t - ⌊t⌋ := by
    have hc : ((⌊t⌋ + 1 : ℤ) : ℝ) = (⌊t⌋ : ℝ) + 1 := by push_cast; ring
    rw [hc]
    unfold hat1
    rw [abs_of_nonpos (by linarith : t - ((⌊t⌋ : ℝ) + 1) ≤ 0)]
    rw [max_eq_right (by linarith : (0 : ℝ) ≤ 1 - -(t - ((⌊t⌋ : ℝ) + 1)))]
    ring
  rw [hv1, hv2]
  ring

/-- The piecewise bilinear interpolation of a grid field `V : ℤ → ℤ → ℝ` at
the point `u : ℝ × ℝ`: the finite sum over the integer lattice of the values
times the two-dimensional hat weights. -/
def hatInterp (V : ℤ → ℤ → ℝ) (u : ℝ × ℝ) : ℝ :=
  ∑ᶠ (m : ℤ) (j : ℤ), V m j * (hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ)))

/-- **The interpolation is a finite sum over any rectangle containing the
support of the weights.** -/
theorem hatInterp_eq_sum (V : ℤ → ℤ → ℝ) (u : ℝ × ℝ) (S₁ S₂ : Finset ℤ)
    (h₁ : ∀ m : ℤ, hat1 (u.1 - (m : ℝ)) ≠ 0 → m ∈ S₁)
    (h₂ : ∀ j : ℤ, hat1 (u.2 - (j : ℝ)) ≠ 0 → j ∈ S₂) :
    hatInterp V u =
      ∑ m ∈ S₁, ∑ j ∈ S₂, V m j * (hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ))) := by
  unfold hatInterp
  have hsupp₁ : Function.support
      (fun m : ℤ => ∑ᶠ j : ℤ, V m j * (hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ)))) ⊆
      (S₁ : Set ℤ) := by
    intro m hm
    simp only [Function.mem_support, ne_eq] at hm
    by_contra hmem
    apply hm
    have hmz : hat1 (u.1 - (m : ℝ)) = 0 := by
      by_contra hne
      exact hmem (Finset.mem_coe.mpr (h₁ m hne))
    rw [finsum_eq_finsetSum_of_support_subset _
      (s := (∅ : Finset ℤ)) (fun j hj => by
        simp only [Function.mem_support, ne_eq] at hj
        rw [hmz, zero_mul, mul_zero] at hj
        exact absurd hj (by simp))]
    rw [Finset.sum_empty]
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp₁]
  exact Finset.sum_congr rfl fun m _ =>
    finsum_eq_finsetSum_of_support_subset _ (s := S₂) (fun j hj => by
      simp only [Function.mem_support, ne_eq] at hj
      by_contra hmem
      apply hj
      have hjz : hat1 (u.2 - (j : ℝ)) = 0 := by
        by_contra hne
        exact hmem (Finset.mem_coe.mpr (h₂ j hne))
      rw [hjz, mul_zero, mul_zero])

/-- **The interpolation is the sum over the four corners of the cell** of `u`. -/
theorem hatInterp_eq_corners (V : ℤ → ℤ → ℝ) (u : ℝ × ℝ) :
    hatInterp V u =
      ∑ m ∈ ({⌊u.1⌋, ⌊u.1⌋ + 1} : Finset ℤ), ∑ j ∈ ({⌊u.2⌋, ⌊u.2⌋ + 1} : Finset ℤ),
        V m j * (hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ))) :=
  hatInterp_eq_sum V u _ _
    (fun m hm => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hat1_ne_zero_mem_floor_pair hm)
    (fun j hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hat1_ne_zero_mem_floor_pair hj)

/-- **At an integer point the interpolation is the value.** -/
theorem hatInterp_at_int (V : ℤ → ℤ → ℝ) (m j : ℤ) :
    hatInterp V ((m : ℝ), (j : ℝ)) = V m j := by
  have hint : ∀ a b : ℤ, a ≠ b → (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
    intro a b hab
    have habs : (1 : ℤ) ≤ |a - b| := Int.one_le_abs (sub_ne_zero.mpr hab)
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|a - b| : ℤ) : ℝ) := by exact_mod_cast habs
      _ = |(a : ℝ) - (b : ℝ)| := by
          rw [Int.cast_abs, Int.cast_sub]
  rw [hatInterp_eq_sum V ((m : ℝ), (j : ℝ)) {m} {j}]
  · rw [Finset.sum_singleton, Finset.sum_singleton]
    simp
  · intro m' hm'
    simp only [Finset.mem_singleton]
    by_contra hne
    exact hm' (hat1_eq_zero (hint m m' (fun h => hne h.symm)))
  · intro j' hj'
    simp only [Finset.mem_singleton]
    by_contra hne
    exact hj' (hat1_eq_zero (hint j j' (fun h => hne h.symm)))

/-- **The hat weights sum to one over any rectangle containing the support.** -/
theorem hatInterp_weight_sum (u : ℝ × ℝ) (S₁ S₂ : Finset ℤ)
    (h₁ : ∀ m : ℤ, hat1 (u.1 - (m : ℝ)) ≠ 0 → m ∈ S₁)
    (h₂ : ∀ j : ℤ, hat1 (u.2 - (j : ℝ)) ≠ 0 → j ∈ S₂) :
    ∑ m ∈ S₁, ∑ j ∈ S₂, hat1 (u.1 - (m : ℝ)) * hat1 (u.2 - (j : ℝ)) = 1 := by
  have hA : ∑ m ∈ S₁, hat1 (u.1 - (m : ℝ)) = 1 := by
    rw [← finsum_hat1 u.1]
    exact (finsum_eq_finsetSum_of_support_subset _
      (s := S₁) (fun m hm => by
        simp only [Function.mem_support, ne_eq] at hm
        exact h₁ m hm)).symm
  have hB : ∑ j ∈ S₂, hat1 (u.2 - (j : ℝ)) = 1 := by
    rw [← finsum_hat1 u.2]
    exact (finsum_eq_finsetSum_of_support_subset _
      (s := S₂) (fun j hj => by
        simp only [Function.mem_support, ne_eq] at hj
        exact h₂ j hj)).symm
  rw [← Finset.sum_mul_sum, hA, hB, mul_one]

/-- **The two-dimensional hat weight is Lipschitz with constant given by the
coordinate increments.** -/
theorem abs_hatWeight_sub_le (c : ℤ × ℤ) (u u' : ℝ × ℝ) :
    |hat1 (u.1 - (c.1 : ℝ)) * hat1 (u.2 - (c.2 : ℝ)) -
        hat1 (u'.1 - (c.1 : ℝ)) * hat1 (u'.2 - (c.2 : ℝ))| ≤
      |u.1 - u'.1| + |u.2 - u'.2| := by
  calc |hat1 (u.1 - (c.1 : ℝ)) * hat1 (u.2 - (c.2 : ℝ)) -
        hat1 (u'.1 - (c.1 : ℝ)) * hat1 (u'.2 - (c.2 : ℝ))|
      ≤ |hat1 (u.1 - (c.1 : ℝ)) * hat1 (u.2 - (c.2 : ℝ)) -
          hat1 (u'.1 - (c.1 : ℝ)) * hat1 (u.2 - (c.2 : ℝ))| +
        |hat1 (u'.1 - (c.1 : ℝ)) * hat1 (u.2 - (c.2 : ℝ)) -
          hat1 (u'.1 - (c.1 : ℝ)) * hat1 (u'.2 - (c.2 : ℝ))| := by
        rw [← sub_add_sub_cancel _ (hat1 (u'.1 - (c.1 : ℝ)) * hat1 (u.2 - (c.2 : ℝ)))]
        exact abs_add_le _ _
    _ = |hat1 (u.1 - (c.1 : ℝ)) - hat1 (u'.1 - (c.1 : ℝ))| * hat1 (u.2 - (c.2 : ℝ)) +
        hat1 (u'.1 - (c.1 : ℝ)) * |hat1 (u.2 - (c.2 : ℝ)) - hat1 (u'.2 - (c.2 : ℝ))| := by
        rw [← mul_sub_left_distrib, ← mul_sub_right_distrib, abs_mul, abs_mul,
          abs_of_nonneg (hat1_nonneg _), abs_of_nonneg (hat1_nonneg _)]
    _ ≤ |u.1 - u'.1| * 1 + 1 * |u.2 - u'.2| := by
        have e1 : (u.1 : ℝ) - (c.1 : ℝ) - (u'.1 - (c.1 : ℝ)) = u.1 - u'.1 := by
          ring
        have hw1 := abs_hat1_sub_le (u.1 - (c.1 : ℝ)) (u'.1 - (c.1 : ℝ))
        rw [e1] at hw1
        have e2 : (u.2 : ℝ) - (c.2 : ℝ) - (u'.2 - (c.2 : ℝ)) = u.2 - u'.2 := by
          ring
        have hw2 := abs_hat1_sub_le (u.2 - (c.2 : ℝ)) (u'.2 - (c.2 : ℝ))
        rw [e2] at hw2
        exact add_le_add
          (mul_le_mul hw1 (hat1_le_one _) (hat1_nonneg _) (abs_nonneg _))
          (mul_le_mul (hat1_le_one _) hw2 (abs_nonneg _) (by norm_num))
    _ = |u.1 - u'.1| + |u.2 - u'.2| := by ring

/-- **The interpolation is continuous**: near each point it is a fixed finite
sum of continuous weight functions. -/
theorem continuous_hatInterp (V : ℤ → ℤ → ℝ) : Continuous (hatInterp V) := by
  rw [continuous_iff_continuousAt]
  intro u
  set S₁ := Finset.Icc (⌊u.1⌋ - 1) (⌊u.1⌋ + 2) with hS₁
  set S₂ := Finset.Icc (⌊u.2⌋ - 1) (⌊u.2⌋ + 2) with hS₂
  set f := fun u' : ℝ × ℝ =>
    ∑ m ∈ S₁, ∑ j ∈ S₂, V m j * (hat1 (u'.1 - (m : ℝ)) * hat1 (u'.2 - (j : ℝ))) with hf
  have hcont : Continuous f := by
    apply continuous_finsetSum
    intro m _
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul
      ((continuous_hat1.comp (continuous_fst.sub continuous_const)).mul
        (continuous_hat1.comp (continuous_snd.sub continuous_const)))
  refine (hcont.continuousAt).congr ?_
  have hmem : Metric.ball u (1 / 2) ∈ 𝓝 u :=
    Metric.ball_mem_nhds u (by norm_num)
  refine Filter.eventuallyEq_of_mem hmem fun u' hu' => ?_
  have hdist : dist u' u < 1 / 2 := Metric.mem_ball.mp hu'
  have h1 : |u'.1 - u.1| < 1 / 2 := by
    have hle : dist u'.1 u.1 ≤ dist u' u := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    rw [Real.dist_eq] at hle
    exact lt_of_le_of_lt hle hdist
  have h2 : |u'.2 - u.2| < 1 / 2 := by
    have hle : dist u'.2 u.2 ≤ dist u' u := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    rw [Real.dist_eq] at hle
    exact lt_of_le_of_lt hle hdist
  have hfloor : ∀ t t' : ℝ, |t' - t| < 1 / 2 → ∀ j : ℤ, hat1 (t' - (j : ℝ)) ≠ 0 →
      j ∈ Finset.Icc (⌊t⌋ - 1) (⌊t⌋ + 2) := by
    intro t t' htt j hj
    have ht'lo : t - 1 / 2 < t' := by
      have := abs_lt.mp htt
      linarith
    have ht'hi : t' < t + 1 / 2 := by
      have := abs_lt.mp htt
      linarith
    have htfl : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
    have htfh : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
    have hlo : ⌊t⌋ - 1 ≤ ⌊t'⌋ := by
      rw [Int.le_floor]
      push_cast
      linarith
    have hhi : ⌊t'⌋ < ⌊t⌋ + 2 := by
      rw [Int.floor_lt]
      push_cast
      linarith
    obtain hje | hje := hat1_ne_zero_mem_floor_pair hj
    · rw [Finset.mem_Icc]
      omega
    · rw [Finset.mem_Icc]
      omega
  exact (hatInterp_eq_sum V u' S₁ S₂
    (fun m hm => hfloor u.1 u'.1 h1 m hm)
    (fun j hj => hfloor u.2 u'.2 h2 j hj)).symm

end Parking
end
