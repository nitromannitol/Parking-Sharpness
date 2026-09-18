/-
The piecewise multilinear interpolation of a grid field on `ℤ × Site d`
(`parking.tex:1741-1752`, BouRabeePanagiotis2026 Theorem 1.3(i)(b): "the field on the
left denotes the multilinear interpolation from `R^{-1}ℤ^d` of the values ...").

`Parking.barDivisible` and the linear membrane field `Parking.linPotential`, at a fixed
rescaling `R`, are step functions of the real space-time point `(s, x) : ℝ × (Fin d → ℝ)`:
they read only the integer time index `⌊sR²⌋` and the lattice point `latticePoint R x`, so
they are not even continuous, let alone satisfying the `ContinuousOn` hypothesis the
library's Kolmogorov modulus theorem needs.  This module builds the `(d+1)`-dimensional
bridge from the one-dimensional hat function `hat1` (dimension-independent, and used
unchanged from `Parking.Support.TightInterp`): the `d`-fold tensor product `hatProd` of
`hat1` over the space coordinates `Fin d`, and the joint time-space piecewise multilinear
interpolation `hatInterpD` of a grid field `V : ℤ → Site d → ℝ`, together with its
continuity, corner decompositions, and exact values at grid points.  This is the
`(d+1)`-dimensional generalization, for a general `d`, of the model of
`Parking.Support.TightInterp`, which has a single space index `j : ℤ`: here that index
becomes a `Fin d`-indexed family of space indices, and the two-factor bound that
`Parking.Support.TightInterp` proves by hand is replaced by a general `d`-fold
product-difference bound (`abs_prod_sub_prod_le`).
-/
import LatticeProb.Site
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Constructions
import Parking.Support.TightInterp

noncomputable section
namespace Parking

open Filter Topology Finset LatticeProb

/-! ### The one-dimensional hat function -/

/-- **Two distinct integers are at distance at least one.** -/
theorem one_le_abs_int_sub {a b : ℤ} (hab : a ≠ b) : (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
  have habs : (1 : ℤ) ≤ |a - b| := Int.one_le_abs (sub_ne_zero.mpr hab)
  calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
    _ ≤ ((|a - b| : ℤ) : ℝ) := by exact_mod_cast habs
    _ = |(a : ℝ) - (b : ℝ)| := by rw [Int.cast_abs, Int.cast_sub]

/-! ### A general `d`-fold product-difference bound -/

/-- **A product of numbers in `[0,1]` is `1`-Lipschitz in each factor, jointly**: for two
families `f, g` valued in `[0,1]` on a finite index set, the difference of the products is
bounded by the sum of the coordinatewise differences.  The two-factor case of this is
`abs_hatWeight_sub_le` of `Parking.Support.TightInterp`; this is its general
`Finset.induction_on` form, needed here because the space index ranges over `Fin d` for a
general `d`, not a single fixed coordinate. -/
theorem abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] :
    ∀ (s : Finset ι) (f g : ι → ℝ), (∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, f i ≤ 1) →
      (∀ i ∈ s, 0 ≤ g i) → (∀ i ∈ s, g i ≤ 1) →
      |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro f g _ _ _ _; simp
  | insert a s ha ih =>
      intro f g hf0 hf1 hg0 hg1
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have hPg : (0:ℝ) ≤ ∏ i ∈ s, g i :=
        Finset.prod_nonneg fun i hi => hg0 i (Finset.mem_insert_of_mem hi)
      have hPg1 : ∏ i ∈ s, g i ≤ 1 :=
        Finset.prod_le_one (fun i hi => hg0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => hg1 i (Finset.mem_insert_of_mem hi))
      have hfa0 := hf0 a (Finset.mem_insert_self a s)
      have hihs := ih f g (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hf1 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hg0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hg1 i (Finset.mem_insert_of_mem hi))
      calc |f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i|
          ≤ |f a * ∏ i ∈ s, f i - f a * ∏ i ∈ s, g i|
              + |f a * ∏ i ∈ s, g i - g a * ∏ i ∈ s, g i| := by
            rw [← sub_add_sub_cancel]; exact abs_add_le _ _
        _ = f a * |∏ i ∈ s, f i - ∏ i ∈ s, g i| + |f a - g a| * ∏ i ∈ s, g i := by
            rw [← mul_sub_left_distrib, ← mul_sub_right_distrib, abs_mul, abs_mul,
              abs_of_nonneg hfa0, abs_of_nonneg hPg]
        _ ≤ 1 * |∏ i ∈ s, f i - ∏ i ∈ s, g i| + |f a - g a| * 1 := by
            gcongr
            exact hf1 a (Finset.mem_insert_self a s)
        _ ≤ 1 * (∑ i ∈ s, |f i - g i|) + |f a - g a| * 1 := by
            gcongr
        _ = |f a - g a| + ∑ i ∈ s, |f i - g i| := by ring

/-! ### The `d`-fold tensor product of the hat function over the space coordinates -/

variable {d : ℕ}

/-- **The `d`-dimensional space weight**: the product over the coordinates `Fin d` of the
one-dimensional hat function, at a real point `x` and an integer lattice point `c`. -/
def hatProd (x : Fin d → ℝ) (c : Site d) : ℝ := ∏ i, hat1 (x i - (c i : ℝ))

/-- **The `d`-dimensional space weight is nonnegative.** -/
theorem hatProd_nonneg (x : Fin d → ℝ) (c : Site d) : 0 ≤ hatProd x c :=
  Finset.prod_nonneg fun _i _ => hat1_nonneg _

/-- **The `d`-dimensional space weight is at most one.** -/
theorem hatProd_le_one (x : Fin d → ℝ) (c : Site d) : hatProd x c ≤ 1 :=
  Finset.prod_le_one (fun _i _ => hat1_nonneg _) (fun _i _ => hat1_le_one _)

/-- **At the zero lattice point, evaluated at itself, the weight is one.** -/
@[simp] theorem hatProd_self (c : Site d) :
    hatProd (fun i => (c i : ℝ)) c = 1 := by
  unfold hatProd
  simp

/-- **A nonzero space weight forces every coordinate into its floor pair.** -/
theorem hatProd_ne_zero_mem_box {x : Fin d → ℝ} {c : Site d} (h : hatProd x c ≠ 0) (i : Fin d) :
    c i = ⌊x i⌋ ∨ c i = ⌊x i⌋ + 1 :=
  hat1_ne_zero_mem_floor_pair (Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i))

/-- **A space weight vanishes as soon as it is read at a different integer point.** -/
theorem hatProd_eq_zero_of_ne {c c' : Site d} (h : c ≠ c') :
    hatProd (fun i => (c i : ℝ)) c' = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hat1_eq_zero (one_le_abs_int_sub hi))

/-- **The `d`-dimensional space weight is `1`-Lipschitz in the `ℓ¹` sense**: the difference
at two points, at a fixed lattice site, is bounded by the sum of the coordinatewise
differences. -/
theorem abs_hatProd_sub_le (x x' : Fin d → ℝ) (c : Site d) :
    |hatProd x c - hatProd x' c| ≤ ∑ i, |x i - x' i| := by
  have hb := abs_prod_sub_prod_le (Finset.univ : Finset (Fin d))
    (fun i => hat1 (x i - (c i : ℝ))) (fun i => hat1 (x' i - (c i : ℝ)))
    (fun i _ => hat1_nonneg _) (fun i _ => hat1_le_one _)
    (fun i _ => hat1_nonneg _) (fun i _ => hat1_le_one _)
  refine hb.trans (Finset.sum_le_sum fun i _ => ?_)
  have h := abs_hat1_sub_le (x i - (c i : ℝ)) (x' i - (c i : ℝ))
  rwa [show (x i - (c i : ℝ)) - (x' i - (c i : ℝ)) = x i - x' i by ring] at h

/-- **The support of a nonzero space weight is inside the corner box.** -/
theorem support_hatProd_subset (x : Fin d → ℝ) :
    Function.support (fun c : Site d => hatProd x c) ⊆
      (Fintype.piFinset fun i : Fin d => ({⌊x i⌋, ⌊x i⌋ + 1} : Finset ℤ) : Set (Site d)) := by
  intro c hc
  simp only [Function.mem_support] at hc
  simp only [Fintype.coe_piFinset, Set.mem_pi, Set.mem_univ, Finset.mem_coe,
    Finset.mem_insert, Finset.mem_singleton, forall_true_left]
  intro i
  exact hatProd_ne_zero_mem_box hc i

/-- **The space weight has finite support, so the finsum over `Site d` is a genuine finite
sum.** -/
theorem finite_support_hatProd (x : Fin d → ℝ) :
    (Function.support (fun c : Site d => hatProd x c)).Finite :=
  Set.Finite.subset (Finset.finite_toSet _) (support_hatProd_subset x)

/-! ### The joint time-space piecewise multilinear interpolation -/

/-- **The joint time-space piecewise multilinear interpolation** of a grid field
`V : ℤ → Site d → ℝ` at a real space-time point `u : ℝ × (Fin d → ℝ)`: the finite sum, over
the integer time index and the lattice point, of the grid values times the product of the
time hat weight and the `d`-dimensional space weight. -/
def hatInterpD (V : ℤ → Site d → ℝ) (u : ℝ × (Fin d → ℝ)) : ℝ :=
  ∑ᶠ (m : ℤ) (c : Site d), V m c * (hat1 (u.1 - (m : ℝ)) * hatProd u.2 c)

/-- **The interpolation is a finite sum over any rectangle containing the support of the
weights.** -/
theorem hatInterpD_eq_sum (V : ℤ → Site d → ℝ) (u : ℝ × (Fin d → ℝ))
    (S₁ : Finset ℤ) (S₂ : Finset (Site d))
    (h₁ : ∀ m : ℤ, hat1 (u.1 - (m : ℝ)) ≠ 0 → m ∈ S₁)
    (h₂ : ∀ c : Site d, hatProd u.2 c ≠ 0 → c ∈ S₂) :
    hatInterpD V u = ∑ m ∈ S₁, ∑ c ∈ S₂, V m c * (hat1 (u.1 - (m : ℝ)) * hatProd u.2 c) := by
  unfold hatInterpD
  have hsupp₁ : Function.support
      (fun m : ℤ => ∑ᶠ c : Site d, V m c * (hat1 (u.1 - (m : ℝ)) * hatProd u.2 c)) ⊆
      (S₁ : Set ℤ) := by
    intro m hm
    simp only [Function.mem_support, ne_eq] at hm
    by_contra hmem
    apply hm
    have hmz : hat1 (u.1 - (m : ℝ)) = 0 := by
      by_contra hne
      exact hmem (Finset.mem_coe.mpr (h₁ m hne))
    rw [finsum_eq_finsetSum_of_support_subset _
      (s := (∅ : Finset (Site d))) (fun c hc => by
        simp only [Function.mem_support, ne_eq] at hc
        rw [hmz, zero_mul, mul_zero] at hc
        exact absurd hc (by simp))]
    rw [Finset.sum_empty]
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp₁]
  exact Finset.sum_congr rfl fun m _ =>
    finsum_eq_finsetSum_of_support_subset _ (s := S₂) (fun c hc => by
      simp only [Function.mem_support, ne_eq] at hc
      by_contra hmem
      apply hc
      have hcz : hatProd u.2 c = 0 := by
        by_contra hne
        exact hmem (Finset.mem_coe.mpr (h₂ c hne))
      rw [hcz, mul_zero, mul_zero])

/-- **The interpolation is the sum over the corner box** of `u`: the two nearest integer
times and the `2^d` nearest lattice points. -/
theorem hatInterpD_eq_corners (V : ℤ → Site d → ℝ) (u : ℝ × (Fin d → ℝ)) :
    hatInterpD V u =
      ∑ m ∈ ({⌊u.1⌋, ⌊u.1⌋ + 1} : Finset ℤ),
        ∑ c ∈ Fintype.piFinset fun i : Fin d => ({⌊u.2 i⌋, ⌊u.2 i⌋ + 1} : Finset ℤ),
          V m c * (hat1 (u.1 - (m : ℝ)) * hatProd u.2 c) :=
  hatInterpD_eq_sum V u _ _
    (fun m hm => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hat1_ne_zero_mem_floor_pair hm)
    (fun c hc => by
      simp only [Fintype.mem_piFinset, Finset.mem_insert, Finset.mem_singleton]
      exact hatProd_ne_zero_mem_box hc)

/-- **At an integer grid point the interpolation is the grid value.** -/
theorem hatInterpD_at_int (V : ℤ → Site d → ℝ) (m : ℤ) (c : Site d) :
    hatInterpD V ((m : ℝ), fun i => (c i : ℝ)) = V m c := by
  rw [hatInterpD_eq_sum V ((m : ℝ), fun i => (c i : ℝ)) {m} {c}]
  · rw [Finset.sum_singleton, Finset.sum_singleton]
    simp
  · intro m' hm'
    simp only [Finset.mem_singleton]
    by_contra hne
    exact hm' (hat1_eq_zero (one_le_abs_int_sub (fun h => hne h.symm)))
  · intro c' hc'
    simp only [Finset.mem_singleton]
    by_contra hne
    apply hc'
    have := hatProd_eq_zero_of_ne (c := c) (c' := c') (fun h => hne h.symm)
    simpa using this

/-- **The interpolation is continuous, jointly in space and time.** -/
theorem continuous_hatInterpD (V : ℤ → Site d → ℝ) : Continuous (hatInterpD V) := by
  rw [continuous_iff_continuousAt]
  intro u
  set S₁ := Finset.Icc (⌊u.1⌋ - 1) (⌊u.1⌋ + 2) with hS₁
  set S₂ := Fintype.piFinset fun i : Fin d => Finset.Icc (⌊u.2 i⌋ - 1) (⌊u.2 i⌋ + 2) with hS₂
  set f := fun u' : ℝ × (Fin d → ℝ) =>
    ∑ m ∈ S₁, ∑ c ∈ S₂, V m c * (hat1 (u'.1 - (m : ℝ)) * hatProd u'.2 c) with hf
  have hcont : Continuous f := by
    apply continuous_finsetSum
    intro m _
    apply continuous_finsetSum
    intro c _
    refine continuous_const.mul (Continuous.mul ?_ ?_)
    · exact continuous_hat1.comp (continuous_fst.sub continuous_const)
    · apply continuous_finsetProd
      intro i _
      exact continuous_hat1.comp
        ((continuous_apply i).comp continuous_snd |>.sub continuous_const)
  refine (hcont.continuousAt).congr ?_
  have hmem : Metric.ball u (1 / 2) ∈ 𝓝 u :=
    Metric.ball_mem_nhds u (by norm_num)
  refine Filter.eventuallyEq_of_mem hmem fun u' hu' => ?_
  have hdist : dist u' u < 1 / 2 := Metric.mem_ball.mp hu'
  have h1 : |u'.1 - u.1| < 1 / 2 := by
    have hle : dist u'.1 u.1 ≤ dist u' u := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    rw [Real.dist_eq] at hle
    exact lt_of_le_of_lt hle hdist
  have h2 : ∀ i : Fin d, |u'.2 i - u.2 i| < 1 / 2 := by
    intro i
    have hle1 : dist u'.2 u.2 ≤ dist u' u := by
      rw [Prod.dist_eq]; exact le_max_right _ _
    have hle2 : dist (u'.2 i) (u.2 i) ≤ dist u'.2 u.2 := dist_le_pi_dist u'.2 u.2 i
    have hle : dist (u'.2 i) (u.2 i) ≤ dist u' u := hle2.trans hle1
    rw [Real.dist_eq] at hle
    exact lt_of_le_of_lt hle hdist
  have hfloorT : ∀ t t' : ℝ, |t' - t| < 1 / 2 → ∀ j : ℤ, hat1 (t' - (j : ℝ)) ≠ 0 →
      j ∈ Finset.Icc (⌊t⌋ - 1) (⌊t⌋ + 2) := by
    intro t t' htt j hj
    have ht'lo : t - 1 / 2 < t' := by have := abs_lt.mp htt; linarith
    have ht'hi : t' < t + 1 / 2 := by have := abs_lt.mp htt; linarith
    have htfl : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
    have htfh : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
    have hlo : ⌊t⌋ - 1 ≤ ⌊t'⌋ := by rw [Int.le_floor]; push_cast; linarith
    have hhi : ⌊t'⌋ < ⌊t⌋ + 2 := by rw [Int.floor_lt]; push_cast; linarith
    obtain hje | hje := hat1_ne_zero_mem_floor_pair hj
    · rw [Finset.mem_Icc]; omega
    · rw [Finset.mem_Icc]; omega
  exact (hatInterpD_eq_sum V u' S₁ S₂
    (fun m hm => hfloorT u.1 u'.1 h1 m hm)
    (fun c hc => by
      rw [hS₂, Fintype.mem_piFinset]
      intro i
      exact hfloorT (u.2 i) (u'.2 i) (h2 i)
        (c i) (Finset.prod_ne_zero_iff.mp hc i (Finset.mem_univ i)))).symm

/-! ### The interpolation is a convex combination of the grid values at the corners -/

/-- **The time hat weights over the floor pair sum to one.** -/
theorem sum_hat1_floor_pair (t : ℝ) :
    ∑ j ∈ ({⌊t⌋, ⌊t⌋ + 1} : Finset ℤ), hat1 (t - (j : ℝ)) = 1 := by
  rw [Finset.sum_pair (by omega : (⌊t⌋ : ℤ) ≠ ⌊t⌋ + 1)]
  have hv1 : hat1 (t - (⌊t⌋ : ℝ)) = 1 - (t - ⌊t⌋) := by
    unfold hat1
    rw [abs_of_nonneg (by linarith [Int.floor_le t] : (0 : ℝ) ≤ t - ⌊t⌋)]
    exact max_eq_right (by linarith [Int.lt_floor_add_one t])
  have hv2 : hat1 (t - ((⌊t⌋ + 1 : ℤ) : ℝ)) = t - ⌊t⌋ := by
    have hc : ((⌊t⌋ + 1 : ℤ) : ℝ) = (⌊t⌋ : ℝ) + 1 := by push_cast; ring
    rw [hc]
    unfold hat1
    rw [abs_of_nonpos (by linarith [Int.lt_floor_add_one t] : t - ((⌊t⌋ : ℝ) + 1) ≤ 0)]
    rw [max_eq_right
      (by linarith [Int.floor_le t] : (0 : ℝ) ≤ 1 - -(t - ((⌊t⌋ : ℝ) + 1)))]
    ring
  rw [hv1, hv2]
  ring

/-- **The space weights over the corner box sum to one**: the `d`-fold tensor product of the
partition of unity, via `Finset.prod_univ_sum`. -/
theorem sum_hatProd_box (x : Fin d → ℝ) :
    ∑ c ∈ Fintype.piFinset fun i : Fin d => ({⌊x i⌋, ⌊x i⌋ + 1} : Finset ℤ), hatProd x c = 1 := by
  have hprod : (∏ i : Fin d, ∑ j ∈ ({⌊x i⌋, ⌊x i⌋ + 1} : Finset ℤ), hat1 (x i - (j : ℝ))) = 1 :=
    Finset.prod_eq_one fun i _ => sum_hat1_floor_pair (x i)
  rw [Finset.prod_univ_sum] at hprod
  exact hprod

/-- **The joint time-space weights over the corner box sum to one.** -/
theorem hatInterpD_weight_sum (u : ℝ × (Fin d → ℝ)) :
    ∑ m ∈ ({⌊u.1⌋, ⌊u.1⌋ + 1} : Finset ℤ),
      ∑ c ∈ Fintype.piFinset fun i : Fin d => ({⌊u.2 i⌋, ⌊u.2 i⌋ + 1} : Finset ℤ),
        hat1 (u.1 - (m : ℝ)) * hatProd u.2 c = 1 := by
  rw [← Finset.sum_mul_sum, sum_hat1_floor_pair u.1, sum_hatProd_box u.2, one_mul]

/-- **A weighted average, over two finite index sets, of values all within `B` of `v0`,
against nonnegative weights summing to one, stays within `B` of `v0`.**  General purpose:
no interpolation-specific content. -/
theorem abs_sum_sum_sub_le_of_forall {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a w : ι → κ → ℝ) (v0 B : ℝ)
    (hw0 : ∀ i ∈ s, ∀ j ∈ t, 0 ≤ w i j) (hsum : ∑ i ∈ s, ∑ j ∈ t, w i j = 1)
    (hB : ∀ i ∈ s, ∀ j ∈ t, |a i j - v0| ≤ B) :
    |∑ i ∈ s, ∑ j ∈ t, a i j * w i j - v0| ≤ B := by
  have heq : ∑ i ∈ s, ∑ j ∈ t, a i j * w i j - v0
      = ∑ i ∈ s, ∑ j ∈ t, (a i j - v0) * w i j := by
    have hrw : ∑ i ∈ s, ∑ j ∈ t, (a i j - v0) * w i j
        = ∑ i ∈ s, ∑ j ∈ t, a i j * w i j - v0 * ∑ i ∈ s, ∑ j ∈ t, w i j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hrw, hsum, mul_one]
  rw [heq]
  calc |∑ i ∈ s, ∑ j ∈ t, (a i j - v0) * w i j|
      ≤ ∑ i ∈ s, |∑ j ∈ t, (a i j - v0) * w i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, |(a i j - v0) * w i j| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, ∑ j ∈ t, |a i j - v0| * w i j := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
        rw [abs_mul, abs_of_nonneg (hw0 i hi j hj)]
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, B * w i j :=
        Finset.sum_le_sum fun i hi =>
          Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hB i hi j hj) (hw0 i hi j hj)
    _ = B * ∑ i ∈ s, ∑ j ∈ t, w i j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ = B := by rw [hsum, mul_one]

/-- **The interpolation stays within `B` of any value `v0` that every corner grid value is
within `B` of.**  In particular (taking `v0` to be the grid value at one corner) the
interpolated field's oscillation over a cell is controlled by the grid field's oscillation
over that cell's corners: `hatInterpD V` is a genuine weighted average of `V` at the `2^{d+1}`
corners, not merely a bounded function of them. -/
theorem abs_hatInterpD_sub_le_of_forall (V : ℤ → Site d → ℝ) (u : ℝ × (Fin d → ℝ))
    (v0 B : ℝ)
    (hB : ∀ m ∈ ({⌊u.1⌋, ⌊u.1⌋ + 1} : Finset ℤ),
      ∀ c ∈ Fintype.piFinset fun i : Fin d => ({⌊u.2 i⌋, ⌊u.2 i⌋ + 1} : Finset ℤ),
        |V m c - v0| ≤ B) :
    |hatInterpD V u - v0| ≤ B := by
  rw [hatInterpD_eq_corners]
  exact abs_sum_sum_sub_le_of_forall _ _ V (fun m c => hat1 (u.1 - (m : ℝ)) * hatProd u.2 c)
    v0 B (fun m _ c _ => mul_nonneg (hat1_nonneg _) (hatProd_nonneg _ _))
    (hatInterpD_weight_sum u) hB

end Parking
end
