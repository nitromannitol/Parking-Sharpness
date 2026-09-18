/-
The Green-function cross sums behind the covariance of the rescaled reward
field of the directed scaling limit (`parking.tex:3192-3203`).

The covariance of the grid reward field of `Parking/Support/TightKolmogorov.lean`
is a sum over pairs of layers of the cross-correlation of two layer laws, and
in dimension two the layer laws are binomial, so each cross-correlation is one
binomial coefficient mass.  This module is the exact algebra:

- `Parking.layerCross r r' w` is `∑_z p_r(z) p_{r'}(z + w)`; it is
  `binomLaw (r + r') (r' + w 0)` on the diagonal `w 0 + w 1 = r - r'` and zero
  off it.
- `Parking.greenCross l l' w` is `∑_z g_l(z) g_{l'}(z + w)`, the sum of the
  layer crosses.
- `Parking.integral_orientedPotential_mul`: the covariance of two potentials
  under the i.i.d. scenery is the variance times the Green cross sum.
- `Parking.orientedCovSum`: on the layer diagonal the Green cross sum of two
  layer points collapses to a single sum of binomial masses, the sum the local
  central limit theorem turns into the heat-kernel overlap integral.
-/
import Parking.Support.TightKolmogorov
import Parking.Support.BinomialConvolution
import Parking.Support.CriticalLawReal
import LatticeProb.Prob.CoordIntegral

open MeasureTheory LatticeProb Finset

noncomputable section
namespace Parking

/-- **The cross-correlation of two layer laws** at displacement `w`. -/
def layerCross (r r' : ℕ) (w : Site 2) : ℝ :=
  ∑' z : Site 2, orientedLayer 2 r z * orientedLayer 2 r' (z + w)

/-- The two layer laws whose product is summable against every shift: the first
factor has finite support. -/
theorem summable_layer_mul (r r' : ℕ) (w : Site 2) :
    Summable fun z : Site 2 => orientedLayer 2 r z * orientedLayer 2 r' (z + w) :=
  summable_of_ne_finset_zero (s := boxFinset 0 r) fun z hz => by
    rw [orientedLayer_eq_zero_of_notMem hz, zero_mul]

/-- The second layer law read at a displaced layer point: it is the binomial
mass on the diagonal and zero off it. -/
theorem orientedLayer_add_layerPoint (r r' : ℕ) (j : ℤ) (w : Site 2) :
    orientedLayer 2 r' (orientedLayerPoint r j + w) =
      if w 0 + w 1 = (r : ℤ) - (r' : ℤ) then binomLaw r' (j - w 0) else 0 := by
  rw [orientedLayer_two]
  have hh : layerHeight (orientedLayerPoint r j + w) = -(r : ℤ) + (w 0 + w 1) := by
    rw [layerHeight_add, layerHeight_orientedLayerPoint, layerHeight_two]
  by_cases hc : w 0 + w 1 = (r : ℤ) - (r' : ℤ)
  · rw [if_pos hc]
    have hh2 : layerHeight (orientedLayerPoint r j + w) = -(r' : ℤ) := by rw [hh]; omega
    rw [if_pos hh2]
    congr 1
    show -(orientedLayerPoint r j + w) 0 = j - w 0
    simp only [orientedLayerPoint, Pi.add_apply, Matrix.cons_val_zero]
    ring
  · rw [if_neg hc, if_neg]
    rw [hh]
    omega

/-- **The layer cross-correlation is one binomial mass**: on the diagonal
`w 0 + w 1 = r - r'` it is `binomLaw (r + r') (r' + w 0)`, and zero else. -/
theorem layerCross_eq (r r' : ℕ) (w : Site 2) :
    layerCross r r' w = if w 0 + w 1 = (r : ℤ) - (r' : ℤ)
      then binomLaw (r + r') ((r' : ℤ) + w 0) else 0 := by
  classical
  unfold layerCross
  by_cases hc : w 0 + w 1 = (r : ℤ) - (r' : ℤ)
  · rw [if_pos hc]
    have hs : Function.support
        (fun z : Site 2 => orientedLayer 2 r z * orientedLayer 2 r' (z + w)) ⊆
        Set.range (orientedLayerPoint r) := by
      intro z hz
      have hn : orientedLayer 2 r z ≠ 0 := by
        intro hn
        exact hz (by simp [hn])
      exact ⟨-z 0, orientedLayerPoint_eq (orientedLayer_height hn)⟩
    rw [← (orientedLayerPoint_injective r).tsum_eq hs]
    simp only [orientedLayer_at_layerPoint, orientedLayer_add_layerPoint, if_pos hc]
    have hsym : ∀ j : ℤ, binomLaw r j * binomLaw r' (j - w 0)
        = binomLaw r j * binomLaw r' ((r' : ℤ) + w 0 - j) := by
      intro j
      rw [← binomLaw_symm r' (j - w 0)]
      congr 2
      ring
    rw [tsum_congr hsym]
    have hconv := binomLaw_convolution r' r ((r' : ℤ) + w 0)
    rw [add_comm r' r] at hconv
    rw [hconv]
    exact tsum_eq_sum fun j hj => by
      rw [binomLaw_zero_outside hj, zero_mul]
  · rw [if_neg hc]
    have hzero : (fun z : Site 2 => orientedLayer 2 r z * orientedLayer 2 r' (z + w))
        = fun _ => (0 : ℝ) := by
      funext z
      by_cases hz : orientedLayer 2 r z = 0
      · rw [hz, zero_mul]
      · have h1 : layerHeight z = -(r : ℤ) := orientedLayer_height hz
        have h2 : layerHeight (z + w) ≠ -(r' : ℤ) := by
          rw [layerHeight_add, h1, layerHeight_two]
          omega
        have h3 : orientedLayer 2 r' (z + w) = 0 := by
          rw [orientedLayer_two, if_neg h2]
        rw [h3, mul_zero]
    rw [hzero, tsum_zero]

/-- **The Green cross sum** `∑_z g_l(z) g_{l'}(z + w)`. -/
def greenCross (l l' : ℕ) (w : Site 2) : ℝ :=
  ∑' z : Site 2, orientedGreen 2 l z * orientedGreen 2 l' (z + w)

/-- **The Green cross sum is the sum of the layer crosses.** -/
theorem greenCross_eq_sum (l l' : ℕ) (w : Site 2) :
    greenCross l l' w = ∑ r ∈ range l, ∑ r' ∈ range l', layerCross r r' w := by
  classical
  have hbody : (fun z : Site 2 => orientedGreen 2 l z * orientedGreen 2 l' (z + w))
      = fun z => ∑ r ∈ range l, ∑ r' ∈ range l',
        orientedLayer 2 r z * orientedLayer 2 r' (z + w) := by
    funext z
    rw [orientedGreen, orientedGreen, Finset.sum_mul_sum]
  unfold greenCross layerCross
  rw [hbody, Summable.tsum_finsetSum
    (f := fun r z => ∑ r' ∈ range l', orientedLayer 2 r z * orientedLayer 2 r' (z + w))
    (fun r _ => summable_sum fun r' _ => summable_layer_mul r r' w)]
  refine sum_congr rfl fun r _ => ?_
  rw [Summable.tsum_finsetSum
    (f := fun r' z => orientedLayer 2 r z * orientedLayer 2 r' (z + w))
    (fun r' _ => summable_layer_mul r r' w)]

/-- **The Green cross sum is symmetric.** -/
theorem greenCross_symm (l l' : ℕ) (w : Site 2) :
    greenCross l l' w = greenCross l' l (-w) := by
  unfold greenCross
  have h := (Equiv.addRight w).tsum_eq
    (fun z : Site 2 => orientedGreen 2 l' z * orientedGreen 2 l (z + -w))
  simp only [Equiv.coe_addRight] at h
  rw [← h]
  refine tsum_congr fun z => ?_
  rw [add_neg_cancel_right, mul_comm]

/-- **The covariance of two coordinates** of the i.i.d. scenery: the second
moment on the diagonal and zero off it, because the one-site law is centred. -/
theorem integral_eval_mul_eval_iid (ν : Measure ℤ) (hν : CriticalLaw ν)
    (z z' : Site 2) :
    ∫ η : Site 2 → ℝ, η z * η z' ∂(iidLaw 2 (realLaw ν))
      = if z = z' then ∫ x : ℝ, x ^ 2 ∂(realLaw ν) else 0 := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  by_cases hzz : z = z'
  · rw [if_pos hzz, ← hzz]
    have hpt : (fun η : Site 2 → ℝ => η z * η z) = fun η => (η z) ^ 2 := by
      ext η; ring
    rw [hpt]
    have hmap : (iidLaw 2 (realLaw ν)).map (fun η : Site 2 → ℝ => η z) = realLaw ν :=
      Measure.infinitePi_map_eval _ z
    have h1 : ∫ x : ℝ, x ^ 2 ∂(realLaw ν)
        = ∫ η : Site 2 → ℝ, (η z) ^ 2 ∂(iidLaw 2 (realLaw ν)) := by
      conv_lhs => rw [← hmap]
      exact integral_map (measurable_pi_apply z).aemeasurable
        (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
          ((iidLaw 2 (realLaw ν)).map fun η : Site 2 → ℝ => η z))
    rw [h1]
  · rw [if_neg hzz]
    have hfact := LatticeProb.integral_mul_eval (fun _ : Site 2 => realLaw ν) z' 0
      (fun η : Site 2 → ℝ => η z) (measurable_pi_apply z)
      (fun ω => Function.update_of_ne hzz (0 : ℝ) ω)
      id measurable_id
    have hpt : (fun η : Site 2 → ℝ => η z * η z')
        = fun η => (fun η : Site 2 → ℝ => η z) η * id (η z') := rfl
    rw [hpt]
    show ∫ η : Site 2 → ℝ, (fun η : Site 2 → ℝ => η z) η * id (η z')
        ∂(Measure.infinitePi fun _ : Site 2 => realLaw ν) = 0
    rw [hfact, show (∫ u : ℝ, id u ∂(realLaw ν)) = 0 from by simpa using realLaw_mean ν hν,
      mul_zero]

/-- The product of two coordinates is integrable under the i.i.d. law. -/
theorem integrable_eval_mul_eval_iid (ν : Measure ℤ) (hν : CriticalLaw ν)
    (z z' : Site 2) :
    Integrable (fun η : Site 2 → ℝ => η z * η z') (iidLaw 2 (realLaw ν)) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  have hsq : Integrable (fun x : ℝ => x ^ 2) (realLaw ν) :=
    (realLaw_memLp_two ν hν).integrable_sq
  have hev : ∀ w : Site 2, Integrable (fun η : Site 2 → ℝ => η w ^ 2)
      (iidLaw 2 (realLaw ν)) := by
    intro w
    have hmap : (iidLaw 2 (realLaw ν)).map (fun η : Site 2 → ℝ => η w) = realLaw ν :=
      Measure.infinitePi_map_eval _ w
    have h : Integrable (fun x : ℝ => x ^ 2) ((iidLaw 2 (realLaw ν)).map fun η => η w) := by
      rw [hmap]; exact hsq
    rwa [integrable_map_measure
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
        ((iidLaw 2 (realLaw ν)).map fun η => η w))
      (measurable_pi_apply w).aemeasurable] at h
  refine Integrable.mono' (((hev z).add (hev z')).div_const 2)
    (((measurable_pi_apply z).mul (measurable_pi_apply z'))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun η => ?_)
  have h2 := sq_nonneg (|η z| - |η z'|)
  have e1 : |η z| ^ 2 = η z ^ 2 := sq_abs _
  have e2 : |η z'| ^ 2 = η z' ^ 2 := sq_abs _
  show ‖η z * η z'‖ ≤ (η z ^ 2 + η z' ^ 2) / 2
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [abs_nonneg (η z), abs_nonneg (η z'), h2, e1, e2]

/-- **The covariance of two potentials** under the i.i.d. scenery is the
variance times the Green cross sum of the displacement. -/
theorem integral_orientedPotential_mul (ν : Measure ℤ) (hν : CriticalLaw ν)
    (l l' : ℕ) (a a' : Site 2) :
    ∫ η : Site 2 → ℝ, orientedPotential η l a * orientedPotential η l' a'
        ∂(iidLaw 2 (realLaw ν))
      = (∫ x : ℝ, x ^ 2 ∂(realLaw ν)) * greenCross l l' (a - a') := by
  classical
  haveI := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  have hterm : ∀ z z' : Site 2, Integrable
      (fun η : Site 2 → ℝ => (orientedGreen 2 l (z - a) * η z) *
        (orientedGreen 2 l' (z' - a') * η z')) (iidLaw 2 (realLaw ν)) := by
    intro z z'
    have hbase := (integrable_eval_mul_eval_iid ν hν z z').abs.const_mul
      |orientedGreen 2 l (z - a) * orientedGreen 2 l' (z' - a')|
    refine hbase.mono'
      ((((measurable_const.mul (measurable_pi_apply z)).mul
        (measurable_const.mul (measurable_pi_apply z')))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_eq_abs]
    show |(orientedGreen 2 l (z - a) * η z) * (orientedGreen 2 l' (z' - a') * η z')|
      ≤ |orientedGreen 2 l (z - a) * orientedGreen 2 l' (z' - a')| * |η z * η z'|
    rw [show (orientedGreen 2 l (z - a) * η z) * (orientedGreen 2 l' (z' - a') * η z')
        = (orientedGreen 2 l (z - a) * orientedGreen 2 l' (z' - a')) * (η z * η z') by ring]
    rw [abs_mul]
  have hfun : (fun η : Site 2 → ℝ => orientedPotential η l a * orientedPotential η l' a')
      = fun η => ∑ z ∈ boxFinset a l, ∑ z' ∈ boxFinset a' l',
        (orientedGreen 2 l (z - a) * η z) * (orientedGreen 2 l' (z' - a') * η z') := by
    funext η
    rw [orientedPotential_eq_box, orientedPotential_eq_box, Finset.sum_mul_sum]
  rw [hfun,
    integral_finsetSum _ fun z _ => integrable_finsetSum _ fun z' _ => hterm z z']
  rw [sum_congr rfl fun z _ => integral_finsetSum _ fun z' _ => hterm z z']
  have hval : ∀ z z' : Site 2,
      ∫ η : Site 2 → ℝ, (orientedGreen 2 l (z - a) * η z) *
          (orientedGreen 2 l' (z' - a') * η z') ∂(iidLaw 2 (realLaw ν))
        = (orientedGreen 2 l (z - a) * orientedGreen 2 l' (z' - a')) *
          if z = z' then ∫ x : ℝ, x ^ 2 ∂(realLaw ν) else 0 := by
    intro z z'
    have hpt : (fun η : Site 2 → ℝ => (orientedGreen 2 l (z - a) * η z) *
        (orientedGreen 2 l' (z' - a') * η z'))
      = fun η : Site 2 → ℝ => (orientedGreen 2 l (z - a) * orientedGreen 2 l' (z' - a')) *
        (η z * η z') := by
      ext η; ring
    rw [hpt, integral_const_mul, integral_eval_mul_eval_iid ν hν z z']
  rw [sum_congr rfl fun z _ => sum_congr rfl fun z' _ => hval z z']
  have hdiag : ∀ z ∈ boxFinset a l,
      (∑ z' ∈ boxFinset a' l', (orientedGreen 2 l (z - a) * orientedGreen 2 l' (z' - a')) *
        if z = z' then ∫ x : ℝ, x ^ 2 ∂(realLaw ν) else 0)
      = if z ∈ boxFinset a' l' then orientedGreen 2 l (z - a) * orientedGreen 2 l' (z - a') *
          ∫ x : ℝ, x ^ 2 ∂(realLaw ν) else 0 := by
    intro z _
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq (boxFinset a' l') z]
  rw [sum_congr rfl hdiag, ← Finset.sum_filter, Finset.filter_mem_eq_inter]
  -- the filtered sum is the Green cross sum
  have hsupp : ∀ z : Site 2, z ∉ boxFinset a l ∩ boxFinset a' l' →
      orientedGreen 2 l (z - a) * orientedGreen 2 l' (z - a') = 0 := by
    intro z hz
    by_cases h1 : z ∈ boxFinset a l
    · have h2 : z ∉ boxFinset a' l' := fun h2 => hz (Finset.mem_inter.mpr ⟨h1, h2⟩)
      rw [orientedGreen_sub_zero_outside (x := a') (z := z) h2, mul_zero]
    · rw [orientedGreen_sub_zero_outside (x := a) (z := z) h1, zero_mul]
  have hgreen : greenCross l l' (a - a')
      = ∑ z ∈ boxFinset a l ∩ boxFinset a' l',
        orientedGreen 2 l (z - a) * orientedGreen 2 l' (z - a') := by
    unfold greenCross
    have hre := (Equiv.addRight (-a)).tsum_eq
      (fun w : Site 2 => orientedGreen 2 l w * orientedGreen 2 l' (w + (a - a')))
    simp only [Equiv.coe_addRight] at hre
    rw [← hre, tsum_eq_sum (s := boxFinset a l ∩ boxFinset a' l') fun z hz => ?_]
    · refine sum_congr rfl fun z _ => ?_
      show orientedGreen 2 l (z + -a) * orientedGreen 2 l' (z + -a + (a - a'))
        = orientedGreen 2 l (z - a) * orientedGreen 2 l' (z - a')
      rw [show z + -a = z - a from by abel, show z - a + (a - a') = z - a' from by abel]
    · show orientedGreen 2 l (z + -a) * orientedGreen 2 l' (z + -a + (a - a')) = 0
      rw [show z + -a = z - a from by abel, show z - a + (a - a') = z - a' from by abel]
      exact hsupp z hz
  rw [hgreen, Finset.mul_sum]
  refine sum_congr rfl fun z _ => ?_
  ring

/-- **The covariance sum on the layer diagonal**: the sum of binomial masses
that the local central limit theorem turns into the heat-kernel overlap
integral. -/
def orientedCovSum (D M : ℕ) (K : ℤ) : ℝ :=
  ∑ i ∈ range M, binomLaw (2 * i + D) ((i : ℤ) + K)

/-- **The Green cross sum of two layer points collapses to the diagonal
covariance sum.**  Stated for `m ≤ m'`: the diagonal is `r - r' = m' - m`. -/
theorem greenCross_layerPoint_sub_of_le {m m' : ℕ} (hm : m ≤ m') {N : ℕ} (hm'N : m' ≤ N)
    (j j' : ℤ) :
    greenCross (N - m) (N - m') (orientedLayerPoint m j - orientedLayerPoint m' j')
      = orientedCovSum (m' - m) (N - m') (j' - j) := by
  classical
  rw [greenCross_eq_sum]
  unfold orientedCovSum
  have hw : (orientedLayerPoint m j - orientedLayerPoint m' j') 0 +
      (orientedLayerPoint m j - orientedLayerPoint m' j') 1 = (m' : ℤ) - (m : ℤ) := by
    simp only [orientedLayerPoint, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hw0 : (orientedLayerPoint m j - orientedLayerPoint m' j') 0 = j' - j := by
    simp only [orientedLayerPoint, Pi.sub_apply, Matrix.cons_val_zero]
    omega
  have hterm : ∀ r ∈ range (N - m), ∀ r' ∈ range (N - m'),
      layerCross r r' (orientedLayerPoint m j - orientedLayerPoint m' j')
      = if r = r' + (m' - m) then binomLaw (r + r') ((r' : ℤ) + (j' - j)) else 0 := by
    intro r _ r' _
    rw [layerCross_eq]
    by_cases hcond : r = r' + (m' - m)
    · rw [if_pos hcond]
      have hcr : (orientedLayerPoint m j - orientedLayerPoint m' j') 0 +
          (orientedLayerPoint m j - orientedLayerPoint m' j') 1
          = (r : ℤ) - (r' : ℤ) := by
        rw [hw, hcond]
        omega
      rw [if_pos hcr, hw0]
    · rw [if_neg hcond]
      have hcr : (orientedLayerPoint m j - orientedLayerPoint m' j') 0 +
          (orientedLayerPoint m j - orientedLayerPoint m' j') 1
          ≠ (r : ℤ) - (r' : ℤ) := by
        rw [hw]
        intro hcon
        apply hcond
        have hd : ((m' - m : ℕ) : ℤ) = (m' : ℤ) - (m : ℤ) := Nat.cast_sub hm
        have h2 : (r : ℤ) = ((r' + (m' - m) : ℕ) : ℤ) := by
          push_cast
          rw [hd]
          linarith
        exact_mod_cast h2
      rw [if_neg hcr]
  rw [sum_congr rfl fun r hr => sum_congr rfl (hterm r hr)]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun r' hr' => ?_
  have hle : r' + (m' - m) < N - m := by
    have h := mem_range.mp hr'
    omega
  rw [Finset.sum_ite_eq' (range (N - m)) (r' + (m' - m))]
  rw [if_pos (mem_range.mpr hle)]
  rw [show (r' + (m' - m)) + r' = 2 * r' + (m' - m) by omega]

/-- **The covariance of the grid reward field** is `n^{-1/2}` times the
variance times the Green cross sum of the layer-point displacement. -/
theorem integral_orientedGridReward_mul (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n N : ℕ) (m m' j j' : ℤ) :
    ∫ η : Site 2 → ℝ, orientedGridReward n N η m j * orientedGridReward n N η m' j'
        ∂(iidLaw 2 (realLaw ν))
      = (n : ℝ) ^ (-(1 : ℝ) / 2) * ((∫ x : ℝ, x ^ 2 ∂(realLaw ν)) *
        greenCross (N - m.toNat) (N - m'.toNat)
          (orientedLayerPoint m.toNat j - orientedLayerPoint m'.toNat j')) := by
  have hpt : (fun η : Site 2 → ℝ => orientedGridReward n N η m j *
      orientedGridReward n N η m' j')
    = fun η : Site 2 → ℝ => ((n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ (-(1 : ℝ) / 4)) *
      (orientedPotential η (N - m.toNat) (orientedLayerPoint m.toNat j) *
        orientedPotential η (N - m'.toNat) (orientedLayerPoint m'.toNat j')) := by
    ext η
    simp only [orientedGridReward]
    ring
  rw [hpt, integral_const_mul, integral_orientedPotential_mul ν hν]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp only [hn, Nat.cast_zero]
    rw [Real.zero_rpow (by norm_num : (-(1 : ℝ) / 4) ≠ 0), mul_zero, zero_mul,
      Real.zero_rpow (by norm_num : (-(1 : ℝ) / 2) ≠ 0), zero_mul]
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [← Real.rpow_add hn0]
    congr 1
    ring_nf
