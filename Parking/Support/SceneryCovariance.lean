import Parking.Support.LinCovarianceGlue
import Parking.Support.SpatWSceneryFdd
import Parking.Support.LinInterp
import Parking.Support.SpatWalkCLT
import Parking.Support.RangeResolvent
import Parking.Support.ErrorUnroll

/-!
# Covariances of scenery pairings

Finite weighted sums of independent centred scenery coordinates have covariance given by
an inner product of their weights.
-/

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped NNReal
open LatticeProb.Walk (sceneryBox exists_norm_le_of_hasCompactSupport
  tendsto_latticeSum_mul_rpow tsum_eq_sceneryBox_sum
  exists_norm_bound_of_hasCompactSupport mem_sceneryBox_of_ne_zero)

noncomputable section
namespace Parking

/-- The covariance of finite weighted sums of independent centred scenery. -/
theorem integral_iid_finite_sum_mul {d : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmean : ∫ x, x ∂μ = 0) (hint : Integrable (fun x : ℝ => x) μ)
    (hsq : Integrable (fun x : ℝ => x ^ 2) μ) (S : Finset (Site d)) (a b : Site d → ℝ) :
    (∫ η : Site d → ℝ, (∑ z ∈ S, a z * η z) * (∑ z ∈ S, b z * η z)
      ∂(iidLaw d μ)) = (∑ z ∈ S, a z * b z) * ∫ x, x ^ 2 ∂μ := by
  classical
  let F : (S → ℝ) → ℝ := fun ξ =>
    (∑ i : S, a i * ξ i) * (∑ i : S, b i * ξ i)
  have hF : Integrable F (Measure.pi fun _ : S => μ) :=
    integrable_sum_mul_sum_pi (fun i : S => a i) (fun i : S => b i) μ hint hsq
  have hrestrict := LatticeProb.integral_restrict d μ S F hF
  have hval := integral_sum_mul_sum_pi (ι := S) (fun i : S => a i)
    (fun i : S => b i) μ hmean hint hsq
  have hpoint : ∀ η : Site d → ℝ,
      (∑ z ∈ S, a z * η z) * (∑ z ∈ S, b z * η z) = F (S.restrict η) := by
    intro η
    dsimp only [F, Finset.restrict]
    rw [Finset.sum_coe_sort S (fun z => a z * η z),
      Finset.sum_coe_sort S (fun z => b z * η z)]
  calc
    _ = ∫ η : Site d → ℝ, F (S.restrict η) ∂(iidLaw d μ) :=
      integral_congr_ae (Eventually.of_forall hpoint)
    _ = ∫ ξ : S → ℝ, F ξ ∂(Measure.pi fun _ : S => μ) := hrestrict
    _ = _ := by
      rw [hval, Finset.sum_coe_sort S (fun z => a z * b z)]

/-- A finite bilinear form of independent scenery variables is integrable. -/
theorem integrable_iid_finite_sum_mul {d : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (hsq : Integrable (fun x : ℝ => x ^ 2) μ)
    (S : Finset (Site d)) (a b : Site d → ℝ) :
    Integrable (fun η : Site d → ℝ => (∑ z ∈ S, a z * η z) * (∑ z ∈ S, b z * η z))
      (iidLaw d μ) := by
  classical
  let F : (S → ℝ) → ℝ := fun ξ =>
    (∑ i : S, a i * ξ i) * (∑ i : S, b i * ξ i)
  have hF : Integrable F (Measure.pi fun _ : S => μ) :=
    integrable_sum_mul_sum_pi (fun i : S => a i) (fun i : S => b i) μ hint hsq
  have hmap : (iidLaw d μ).map S.restrict = Measure.pi (fun _ : S => μ) :=
    iidLaw_map_restrict d μ S
  have hm : Measurable (S.restrict : (Site d → ℝ) → S → ℝ) :=
    Measurable.of_eval fun i => measurable_pi_apply i.val
  have hFi : Integrable F ((iidLaw d μ).map S.restrict) := by rw [hmap]; exact hF
  have hcomp := (integrable_map_measure hFi.aestronglyMeasurable hm.aemeasurable).mp hFi
  convert hcomp using 1
  funext η
  dsimp only [Function.comp_def, F, Finset.restrict]
  rw [Finset.sum_coe_sort S (fun z => a z * η z),
    Finset.sum_coe_sort S (fun z => b z * η z)]

/-- The covariance of two scenery pairings at a fixed positive mesh scale. -/
theorem integral_scenePair_mul {d : ℕ} (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    {φ ψ : (Fin d → ℝ) → ℝ} {B R : ℝ} (hB : 0 < B) (hR : 1 ≤ R)
    (hφ : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B) (hψ : ∀ x, ψ x ≠ 0 → ‖x‖ ≤ B) :
    (∫ w, scenePair w R φ * scenePair w R ψ ∂(law d ν)) =
      variance (fun k : ℤ => (k : ℝ)) ν *
        ((∑' y : Site d, φ (fun j => (y j : ℝ) / R) * ψ (fun j => (y j : ℝ) / R)) *
          (1 / R) ^ d) := by
  classical
  have := hν.prob
  have : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  let S := sceneryBox d B R
  let a : Site d → ℝ := fun y => R ^ (-(d : ℝ) / 2) * φ (fun j => (y j : ℝ) / R)
  let b : Site d → ℝ := fun y => R ^ (-(d : ℝ) / 2) * ψ (fun j => (y j : ℝ) / R)
  let F : (Site d → ℝ) → ℝ := fun η => (∑ y ∈ S, a y * η y) * (∑ y ∈ S, b y * η y)
  have hmeas : Measurable F := by
    apply Measurable.mul <;> apply Finset.measurable_sum <;> intro y hy <;>
      exact measurable_const.mul (measurable_pi_apply y)
  have hpt : ∀ w : Data d, scenePair w R φ * scenePair w R ψ = F (confReal w) := by
    intro w
    rw [scenePair_eq_sceneryBox_sum hB hφ hR, scenePair_eq_sceneryBox_sum hB hψ hR]
    dsimp only [F, a, b, S]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro y hy <;> ring
  have hmap := integral_map (μ := law d ν) measurable_confReal.aemeasurable
    (hmeas.aestronglyMeasurable)
  rw [law_map_confReal hd ν] at hmap
  have hiid := integral_iid_finite_sum_mul (realLaw ν) (realLaw_mean ν hν)
    ((realLaw_memLp_two ν hν).integrable one_le_two) (realLaw_memLp_two ν hν).integrable_sq S a b
  have hp : ∀ y : Site d, a y * b y = (1 / R) ^ d *
      (φ (fun j => (y j : ℝ) / R) * ψ (fun j => (y j : ℝ) / R)) := by
    intro y
    dsimp only [a, b]
    have h := rpow_neg_half_sq (le_trans zero_le_one hR) d
    calc
      _ = (R ^ (-(d : ℝ) / 2)) ^ 2 *
          (φ (fun j => (y j : ℝ) / R) * ψ (fun j => (y j : ℝ) / R)) := by ring
      _ = _ := by rw [h]
  have hbound : ∀ x, (φ x * ψ x) ≠ 0 → ‖x‖ ≤ B := by
    intro x hx
    apply hφ x
    intro hz
    apply hx
    rw [hz, zero_mul]
  have hsum := tsum_eq_sceneryBox_sum hB hbound hR
  calc
    _ = ∫ w, F (confReal w) ∂(law d ν) := integral_congr_ae (Eventually.of_forall hpt)
    _ = ∫ η, F η ∂(iidLaw d (realLaw ν)) := hmap.symm
    _ = _ := by
      rw [hiid, ← variance_eq_integral_sq_realLaw ν hν, hsum]
      simp_rw [hp, ← Finset.mul_sum]
      ring

/-- The covariance of two scenery pairings converges to the white-noise covariance. -/
theorem tendsto_integral_scenePair_mul {d : ℕ} (hd : 1 ≤ d) (ν : Measure ℤ)
    (hν : CriticalLaw ν) {φ ψ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ)
    (hψ : IsTestFun ψ) :
    Tendsto (fun R : ℝ => ∫ w, scenePair w R φ * scenePair w R ψ ∂(law d ν)) atTop
      (𝓝 (variance (fun k : ℤ => (k : ℝ)) ν * ∫ y, φ y * ψ y)) := by
  obtain ⟨Bφ, hBφ, hbφ⟩ := exists_norm_bound_of_hasCompactSupport hφ.2
  obtain ⟨Bψ, hBψ, hbψ⟩ := exists_norm_bound_of_hasCompactSupport hψ.2
  let B := max Bφ Bψ
  have hB : 0 < B := lt_of_lt_of_le hBφ (le_max_left _ _)
  have hφB : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B := fun x hx => (hbφ x hx).trans (le_max_left _ _)
  have hψB : ∀ x, ψ x ≠ 0 → ‖x‖ ≤ B := fun x hx => (hbψ x hx).trans (le_max_right _ _)
  have ht := tendsto_latticeSum_mul_rpow (hφ.1.continuous.mul hψ.1.continuous)
    (HasCompactSupport.mul_right hφ.2)
  have ht' := ht.const_mul (variance (fun k : ℤ => (k : ℝ)) ν)
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  exact (integral_scenePair_mul hd ν hν hB hR hφB hψB).symm

/-- A scenery pairing times a finite-time linear potential is integrable. -/
theorem integrable_scenePair_mul_linPotential {d : ℕ} (hd : 1 ≤ d) (ν : Measure ℤ)
    (hν : CriticalLaw ν) {φ : (Fin d → ℝ) → ℝ} {B R : ℝ} (hB : 0 < B)
    (hR : 1 ≤ R) (hφ : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B) (n : ℕ) (x : Site d) :
    Integrable (fun w => scenePair w R φ * linPotential (confReal w) n x) (law d ν) := by
  classical
  have := hν.prob
  have : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  let S := sceneryBox d B R ∪ LatticeProb.boxFinset x n
  let a : Site d → ℝ := fun y => R ^ (-(d : ℝ) / 2) * φ (fun j => (y j : ℝ) / R)
  let b : Site d → ℝ := fun y => green d n (x - y)
  let F : (Site d → ℝ) → ℝ := fun η => (∑ y ∈ S, a y * η y) * (∑ y ∈ S, b y * η y)
  have hFi : Integrable F (iidLaw d (realLaw ν)) :=
    integrable_iid_finite_sum_mul (realLaw ν) ((realLaw_memLp_two ν hν).integrable one_le_two)
      (realLaw_memLp_two ν hν).integrable_sq S a b
  have hmap : (law d ν).map confReal = iidLaw d (realLaw ν) := law_map_confReal hd ν
  have hFi' : Integrable F ((law d ν).map confReal) := by rw [hmap]; exact hFi
  have hcomp := (integrable_map_measure hFi'.aestronglyMeasurable
    measurable_confReal.aemeasurable).mp hFi'
  have hscene (w : Data d) : scenePair w R φ = ∑ y ∈ S, a y * confReal w y := by
    rw [scenePair_eq_sceneryBox_sum hB hφ hR]
    calc
      _ = ∑ y ∈ sceneryBox d B R, a y * confReal w y := by
        apply Finset.sum_congr rfl
        intro y hy
        dsimp only [a]
        ring
      _ = ∑ y ∈ S, a y * confReal w y := by
        apply Finset.sum_subset (Finset.subset_union_left)
        intro y hy hnot
        have hzero : φ (fun j => (y j : ℝ) / R) = 0 := by
          by_contra hn
          exact hnot (mem_sceneryBox_of_ne_zero hB hφ hR hn)
        simp only [a, hzero, mul_zero, zero_mul]
  apply hcomp.congr
  filter_upwards with w
  dsimp only [Function.comp_def, F]
  rw [hscene, linPotential_eq_sum_of_boxFinset_subset (Finset.subset_union_right)]
  dsimp only [b]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- The covariance of a scenery pairing with the finite-time linear potential. -/
theorem integral_scenePair_mul_linPotential {d : ℕ} (hd : 1 ≤ d) (ν : Measure ℤ)
    (hν : CriticalLaw ν) {φ : (Fin d → ℝ) → ℝ} {B R : ℝ} (hB : 0 < B)
    (hR : 1 ≤ R) (hφ : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B) (n : ℕ) (x : Site d) :
    (∫ w, scenePair w R φ * linPotential (confReal w) n x ∂(law d ν)) =
      variance (fun k : ℤ => (k : ℝ)) ν *
        (∑ y ∈ sceneryBox d B R ∪ LatticeProb.boxFinset x n,
          (R ^ (-(d : ℝ) / 2) * φ (fun j => (y j : ℝ) / R)) * green d n (x - y)) := by
  classical
  have := hν.prob
  have : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  let S := sceneryBox d B R ∪ LatticeProb.boxFinset x n
  let a : Site d → ℝ := fun y => R ^ (-(d : ℝ) / 2) * φ (fun j => (y j : ℝ) / R)
  let b : Site d → ℝ := fun y => green d n (x - y)
  let F : (Site d → ℝ) → ℝ := fun η => (∑ y ∈ S, a y * η y) * (∑ y ∈ S, b y * η y)
  have hmeas : Measurable F := by
    apply Measurable.mul <;> apply Finset.measurable_sum <;> intro y hy <;>
      exact measurable_const.mul (measurable_pi_apply y)
  have hscene (w : Data d) : scenePair w R φ = ∑ y ∈ S, a y * confReal w y := by
    rw [scenePair_eq_sceneryBox_sum hB hφ hR]
    calc
      _ = ∑ y ∈ sceneryBox d B R, a y * confReal w y := by
        apply Finset.sum_congr rfl
        intro y hy
        dsimp only [a]
        ring
      _ = ∑ y ∈ S, a y * confReal w y := by
        apply Finset.sum_subset (Finset.subset_union_left)
        intro y hy hnot
        have hzero : φ (fun j => (y j : ℝ) / R) = 0 := by
          by_contra hn
          exact hnot (mem_sceneryBox_of_ne_zero hB hφ hR hn)
        simp only [a, hzero, mul_zero, zero_mul]
  have hpt : ∀ w : Data d, scenePair w R φ * linPotential (confReal w) n x = F (confReal w) := by
    intro w
    rw [hscene, linPotential_eq_sum_of_boxFinset_subset (Finset.subset_union_right)]
    dsimp only [F, b]
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hmap := integral_map (μ := law d ν) measurable_confReal.aemeasurable
    hmeas.aestronglyMeasurable
  rw [law_map_confReal hd ν] at hmap
  have hiid := integral_iid_finite_sum_mul (realLaw ν) (realLaw_mean ν hν)
    ((realLaw_memLp_two ν hν).integrable one_le_two) (realLaw_memLp_two ν hν).integrable_sq S a b
  calc
    _ = ∫ w, F (confReal w) ∂(law d ν) := integral_congr_ae (Eventually.of_forall hpt)
    _ = ∫ η, F η ∂(iidLaw d (realLaw ν)) := hmap.symm
    _ = _ := by
      rw [hiid, ← variance_eq_integral_sq_realLaw ν hν]
      dsimp only [S, a, b]
      ring

/-- The covariance with the interpolated field is the interpolation of the grid covariances. -/
theorem integral_scenePair_mul_linHatInterp {d : ℕ} (hd : 1 ≤ d) (ν : Measure ℤ)
    (hν : CriticalLaw ν) {φ : (Fin d → ℝ) → ℝ} {B R : ℝ} (hB : 0 < B)
    (hR : 1 ≤ R) (hφ : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B) (p : ℝ × (Fin d → ℝ)) :
    (∫ w, scenePair w R φ * linHatInterp (confReal w) R p ∂(law d ν)) =
      ∑ m ∈ ({⌊R ^ 2 * p.1⌋, ⌊R ^ 2 * p.1⌋ + 1} : Finset ℤ),
        ∑ c ∈ Fintype.piFinset (fun i : Fin d => ({⌊R * p.2 i⌋, ⌊R * p.2 i⌋ + 1} : Finset ℤ)),
          (R ^ ((d : ℝ) / 2 - 2) *
            (∫ w, scenePair w R φ * linPotential (confReal w) m.toNat c ∂(law d ν))) *
              (hat1 (R ^ 2 * p.1 - (m : ℝ)) * hatProd (fun i => R * p.2 i) c) := by
  classical
  let S : Finset ℤ := {⌊R ^ 2 * p.1⌋, ⌊R ^ 2 * p.1⌋ + 1}
  let T : Finset (Site d) := Fintype.piFinset (fun i : Fin d =>
    ({⌊R * p.2 i⌋, ⌊R * p.2 i⌋ + 1} : Finset ℤ))
  let weight : ℤ → Site d → ℝ := fun m c =>
    R ^ ((d : ℝ) / 2 - 2) * (hat1 (R ^ 2 * p.1 - (m : ℝ)) * hatProd (fun i => R * p.2 i) c)
  have hpoint (w : Data d) : scenePair w R φ * linHatInterp (confReal w) R p =
      ∑ m ∈ S, ∑ c ∈ T,
        weight m c * (scenePair w R φ * linPotential (confReal w) m.toNat c) := by
    unfold linHatInterp
    rw [hatInterpD_eq_corners]
    dsimp only [S, T, weight]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    ring
  have hi (m : ℤ) (c : Site d) : Integrable (fun w => weight m c *
      (scenePair w R φ * linPotential (confReal w) m.toNat c)) (law d ν) :=
    (integrable_scenePair_mul_linPotential hd ν hν hB hR hφ m.toNat c).const_mul _
  rw [integral_congr_ae (Eventually.of_forall hpoint)]
  rw [integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun c _ => hi m c))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [integral_finsetSum _ (fun c _ => hi m c)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [integral_const_mul]
  dsimp only [weight]
  ring

/-- Covariance commutes with multilinear interpolation of the discrete linear field. -/
theorem integral_scenePair_mul_linHatInterp_eq_hatInterpD {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure ℤ) (hν : CriticalLaw ν) {φ : (Fin d → ℝ) → ℝ} {B R : ℝ}
    (hB : 0 < B) (hR : 1 ≤ R) (hφ : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B)
    (p : ℝ × (Fin d → ℝ)) :
    (∫ w, scenePair w R φ * linHatInterp (confReal w) R p ∂(law d ν)) =
      hatInterpD (fun m c => R ^ ((d : ℝ) / 2 - 2) *
        (∫ w, scenePair w R φ * linPotential (confReal w) m.toNat c ∂(law d ν)))
        (R ^ 2 * p.1, fun i => R * p.2 i) := by
  rw [integral_scenePair_mul_linHatInterp hd ν hν hB hR hφ p, hatInterpD_eq_corners]

/-- A uniform bound on the grid covariances passes to the interpolated covariance. -/
theorem abs_integral_scenePair_mul_linHatInterp_sub_le {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure ℤ) (hν : CriticalLaw ν) {φ : (Fin d → ℝ) → ℝ} {B R : ℝ}
    (hB : 0 < B) (hR : 1 ≤ R) (hφ : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B)
    (p : ℝ × (Fin d → ℝ)) (v ε : ℝ)
    (hgrid : ∀ m ∈ ({⌊R ^ 2 * p.1⌋, ⌊R ^ 2 * p.1⌋ + 1} : Finset ℤ),
      ∀ c ∈ Fintype.piFinset (fun i : Fin d => ({⌊R * p.2 i⌋, ⌊R * p.2 i⌋ + 1} : Finset ℤ)),
        |R ^ ((d : ℝ) / 2 - 2) *
          (∫ w, scenePair w R φ * linPotential (confReal w) m.toNat c ∂(law d ν)) - v| ≤ ε) :
    |(∫ w, scenePair w R φ * linHatInterp (confReal w) R p ∂(law d ν)) - v| ≤ ε := by
  rw [integral_scenePair_mul_linHatInterp_eq_hatInterpD hd ν hν hB hR hφ p]
  exact abs_hatInterpD_sub_le_of_forall _ _ v ε hgrid

/-- The rescaled scenery--potential covariance is a Green-weighted lattice sum. -/
theorem scaled_integral_scenePair_mul_linPotential {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure ℤ) (hν : CriticalLaw ν) {φ : (Fin d → ℝ) → ℝ} {B R : ℝ}
    (hB : 0 < B) (hR : 1 ≤ R) (hφ : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B)
    (n : ℕ) (x : Site d) :
    R ^ ((d : ℝ) / 2 - 2) *
      (∫ w, scenePair w R φ * linPotential (confReal w) n x ∂(law d ν)) =
    variance (fun k : ℤ => (k : ℝ)) ν * (R ^ (-(2 : ℝ)) *
      ∑ y ∈ sceneryBox d B R ∪ LatticeProb.boxFinset x n,
        φ (fun j => (y j : ℝ) / R) * green d n (x - y)) := by
  rw [integral_scenePair_mul_linPotential hd ν hν hB hR hφ n x]
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hp : R ^ ((d : ℝ) / 2 - 2) * R ^ (-(d : ℝ) / 2) = R ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hRpos]
    congr 1
    ring
  have hs : (∑ y ∈ sceneryBox d B R ∪ LatticeProb.boxFinset x n,
      (R ^ (-(d : ℝ) / 2) * φ (fun j => (y j : ℝ) / R)) * green d n (x - y)) =
      R ^ (-(d : ℝ) / 2) * ∑ y ∈ sceneryBox d B R ∪ LatticeProb.boxFinset x n,
        φ (fun j => (y j : ℝ) / R) * green d n (x - y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [hs]
  calc
    _ = (R ^ ((d : ℝ) / 2 - 2) * R ^ (-(d : ℝ) / 2)) *
        (variance (fun k : ℤ => (k : ℝ)) ν *
          ∑ y ∈ sceneryBox d B R ∪ LatticeProb.boxFinset x n,
            φ (fun j => (y j : ℝ) / R) * green d n (x - y)) := by ring
    _ = _ := by rw [hp]; ring

/-- A finite Green-weighted sum is the sum of the corresponding heat-kernel averages. -/
theorem sum_mul_green_eq_sum_heat {d : ℕ} (S : Finset (Site d))
    (f : Site d → ℝ) (n : ℕ) (x : Site d) :
    (∑ y ∈ S, f y * green d n (x - y)) =
      ∑ k ∈ Finset.range n, ∑ y ∈ S, f y * heat d k (x - y) := by
  simp_rw [green, Finset.mul_sum]
  exact Finset.sum_comm

/-- The expectation of a bounded function of the walk equals its heat-kernel pairing. -/
theorem integral_walkPath_eq_tsum_heat {d : ℕ} (hd : 1 ≤ d) (n : ℕ)
    (f : Site d → ℝ) {C : ℝ} (hf : ∀ y, ‖f y‖ ≤ C) :
    (∫ p, f (walkPath (0 : Site d) p n) ∂(walkLaw d)) =
      ∑' y : Site d, heat d n y * f y := by
  have : NeZero d := ⟨by omega⟩
  have hwm : Measurable (walkPath (0 : Site d)) :=
    Measurable.of_eval fun j => measurable_walkPath 0 j
  have hfm : Measurable (fun X : ℕ → Site d => f (X n)) :=
    (measurable_of_countable f).comp (measurable_pi_apply n)
  calc
    _ = ∫ X, f (X n) ∂(LatticeProb.siteWalkLaw d 0) := by
      rw [← map_walkLaw_walkPath hd (0 : Site d),
        integral_map hwm.aemeasurable hfm.aestronglyMeasurable]
    _ = (LatticeProb.walkOp^[n] f) 0 :=
      LatticeProb.integral_apply_eq_walkOp_iterate d n f hf 0
    _ = _ := iterate_walkOp_apply_zero n f

/-- A finite heat-kernel pairing is a translated walk expectation. -/
theorem sum_mul_heat_eq_integral_walkPath {d : ℕ} (hd : 1 ≤ d) (n : ℕ)
    (x : Site d) (S : Finset (Site d)) (f : Site d → ℝ) {C : ℝ}
    (hf : ∀ y, ‖f y‖ ≤ C) (hS : ∀ y ∉ S, heat d n (x - y) = 0) :
    (∑ y ∈ S, f y * heat d n (x - y)) =
      ∫ p, f (x + walkPath (0 : Site d) p n) ∂(walkLaw d) := by
  have hsum := (Equiv.addLeft x).tsum_eq (fun y : Site d => heat d n (x - y) * f y)
  have heq : (∑' y : Site d, heat d n (x - y) * f y) =
      ∑' z : Site d, heat d n z * f (x + z) := by
    calc
      _ = ∑' z : Site d, heat d n (x - (x + z)) * f (x + z) := hsum.symm
      _ = _ := by
        apply tsum_congr
        intro z
        rw [show x - (x + z) = -z by abel, heat_neg]
  calc
    _ = ∑ y ∈ S, heat d n (x - y) * f y := by
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = ∑' y : Site d, heat d n (x - y) * f y := by
      symm
      apply tsum_eq_sum
      intro y hy
      rw [hS y hy, zero_mul]
    _ = _ := by
      rw [heq, ← integral_walkPath_eq_tsum_heat hd n (fun z => f (x + z))
        (fun z => hf (x + z))]

/-- A finite Green-kernel pairing is the sum of translated walk expectations. -/
theorem sum_mul_green_eq_sum_integral_walkPath {d : ℕ} (hd : 1 ≤ d)
    (n : ℕ) (x : Site d) (S : Finset (Site d)) (f : Site d → ℝ) {C : ℝ}
    (hf : ∀ y, ‖f y‖ ≤ C) (hS : LatticeProb.boxFinset x n ⊆ S) :
    (∑ y ∈ S, f y * green d n (x - y)) =
      ∑ k ∈ Finset.range n, ∫ p, f (x + walkPath (0 : Site d) p k) ∂(walkLaw d) := by
  rw [sum_mul_green_eq_sum_heat]
  apply Finset.sum_congr rfl
  intro k hk
  apply sum_mul_heat_eq_integral_walkPath hd k x S f hf
  intro y hy
  apply heat_eq_zero_of_notMem_box
  intro hm
  apply hy
  apply hS
  apply LatticeProb.mem_boxFinset_iff.mpr
  intro i
  have hi := LatticeProb.mem_boxFinset_iff.mp hm i
  simp only [Pi.sub_apply, Pi.zero_apply, sub_zero] at hi
  have hkn : (k : ℤ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
  exact (by simpa only [abs_sub_comm] using hi : |y i - x i| ≤ (k : ℤ)).trans hkn

/-- The rescaled grid covariance is a time sum of walk averages. -/
theorem scaled_integral_scenePair_mul_linPotential_eq_walk {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure ℤ) (hν : CriticalLaw ν) {φ : (Fin d → ℝ) → ℝ} (hφtest : IsTestFun φ)
    {B R : ℝ} (hB : 0 < B) (hR : 1 ≤ R)
    (hφ : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B) (n : ℕ) (x : Site d) :
    R ^ ((d : ℝ) / 2 - 2) *
      (∫ w, scenePair w R φ * linPotential (confReal w) n x ∂(law d ν)) =
    variance (fun k : ℤ => (k : ℝ)) ν * (R ^ (-(2 : ℝ)) *
      ∑ k ∈ Finset.range n, ∫ p, φ (fun i =>
        ((x i : ℝ) + (walkPath (0 : Site d) p k i : ℝ)) / R) ∂(walkLaw d)) := by
  obtain ⟨C, _, hC⟩ := exists_norm_le_of_hasCompactSupport hφtest.1.continuous hφtest.2
  rw [scaled_integral_scenePair_mul_linPotential hd ν hν hB hR hφ n x,
    sum_mul_green_eq_sum_integral_walkPath hd n x _
      (fun y => φ (fun i => (y i : ℝ) / R)) (fun y => hC _)
      Finset.subset_union_right]
  congr 3
  funext k
  apply integral_congr_ae
  filter_upwards with p
  congr 1
  funext i
  simp only [Pi.add_apply, Int.cast_add]

/-- The rescaled random walk tested at a fixed time converges to the Brownian average. -/
theorem tendsto_integral_test_spatialScaledWalk {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)) (hB : IsBrownianSpace d 0 B PB)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) (x : Fin d → ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => ∫ p, φ (x + spatialScaledSite n
      (walkPath (0 : Site d) p ⌊(n : ℝ) * a⌋₊)) ∂(walkLaw d)) atTop
      (𝓝 (∫ β, φ (x + ofBrownianSpace B (Real.toNNReal a) β) ∂PB)) := by
  let F : BoundedContinuousFunction (Fin 1 → (Fin d → ℝ)) ℝ :=
    (ofCompactSupport φ hφ.1.continuous hφ.2).compContinuous
      ⟨fun v => x + v 0, continuous_const.add (continuous_apply 0)⟩
  have h := hWalk_of_isBrownianSpace d hd hd3 ΩB PB B hB (a + 1) (by linarith)
    1 (fun _ => a) (fun _ => ⟨ha, by linarith⟩) F
  simpa [F, BoundedContinuousFunction.compContinuous_apply, ofCompactSupport] using h

end Parking
