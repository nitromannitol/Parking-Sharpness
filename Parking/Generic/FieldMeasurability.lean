/-
**Measurability of a cutoff continuous random field as a random element of the space of
bounded continuous functions.**

A continuous random field `Z : Ω' → ℝ × (Fin d → ℝ) → ℝ` with measurable point evaluations and
continuous paths, after a compactly supported space-time cutoff `χ`, is a measurable map into
`E := BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ`.  This is the CONTINUUM counterpart of the
DISCRETE statement `Parking.measurable_cutoffBC_linHatInterp`
(`Parking/Support/LinHatMeasurable.lean`), whose technique it extends.

**Route.**  The cutoff field `ω' ↦ cutoffBC χ (Z ω')` is the pointwise-in-`ω'` sup-norm limit,
as `R = 2^n → ∞`, of its hat interpolations `ω' ↦ cutoffBC χ (meshInterp (Z ω') R)` from the
meshes `R⁻²ℤ × R⁻¹ℤ^d` (`meshInterp`, below, applies `Parking.hatInterpD` to the samples of
`Z ω'` read on that mesh — the SAME rescaling `Parking.linHatInterp` uses, with the raw field
values sampled directly in place of the linear potential):

1. **Each approximant is measurable**, by exactly the finite-dependence argument of
   `Parking.measurable_cutoffBC_linHatInterp`: a fixed cutoff's compact support pins a single
   finite time-space mesh box (`meshTimeBox`), so `ω' ↦ cutoffBC χ (meshInterp (Z ω') R)`
   factors as the finite-coordinate projection onto `Z ω'`'s values at that finite set of mesh
   points (measurable, by the point-evaluation hypothesis) composed with the map from those
   finitely many samples to the cutoff interpolated field, which is LIPSCHITZ for the sup
   metrics (`measurable_cutoffBC_meshInterp`) — simpler than the discrete argument, since a
   field value is read directly, with no further `linPotential`-style box dependency.
2. **The convergence is uniform on the cutoff's compact support**, by uniform continuity of the
   path (Heine–Cantor on a compact neighbourhood of the support) combined with
   `Parking.abs_hatInterpD_sub_le_of_forall`'s convex-combination bound: the interpolated value
   stays within the corners' oscillation of the true value, and every corner of the mesh lies
   within `1/R` of the target point (`tendsto_cutoffBC_meshInterp`).
3. **Mathlib's `measurable_of_tendsto_metrizable'` needs no separability of the codomain**, so
   the (non-separable, since `ℝ × (Fin d → ℝ)` is non-compact) sup-norm space `E` is no
   obstacle: a pointwise (in `ω'`) limit, along the countably generated filter `atTop` on `ℕ`,
   of measurable maps into any pseudometrizable Borel space is itself measurable.

This module is GENERIC: it is stated for an abstract probability space and an abstract field,
and mentions no Parking-specific object.  It imports only Mathlib and
`Parking.Support.HatInterpD`, which is itself generic in content: it depends only on Mathlib,
`LatticeProb.Site` and `Parking.Support.TightInterp` (a module that imports only Mathlib).  The
main theorem applies unchanged to the field of the divisible-sandpile scaling limit.
-/
import Parking.Support.HatInterpD
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section

namespace Parking.Generic.FieldMeasurability

open Filter Topology Finset LatticeProb MeasureTheory
open scoped NNReal

variable {d : ℕ}

/-! ### The mesh hat interpolation of a continuum field -/

/-- The piecewise multilinear interpolation, at scale `R`, of the grid field `V` (read as
samples on `R⁻²ℤ × R⁻¹ℤ^d`), at the real point `p`: `Parking.hatInterpD` after the usual
`(R², R)` rescaling (the SAME rescaling `Parking.linHatInterp` uses). -/
def meshInterpV (V : ℤ → Site d → ℝ) (R : ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  Parking.hatInterpD V (R ^ 2 * p.1, fun i => R * p.2 i)

theorem continuous_meshInterpV (V : ℤ → Site d → ℝ) (R : ℝ) : Continuous (meshInterpV V R) := by
  unfold meshInterpV
  exact (Parking.continuous_hatInterpD _).comp
    ((continuous_const.mul continuous_fst).prodMk
      (continuous_pi fun i => continuous_const.mul (continuous_apply i |>.comp continuous_snd)))

/-- The mesh sample of a continuum field `f`, at scale `R`: the grid field `V m c := f
(m/R², c/R)`, `f`'s own values read on `R⁻²ℤ × R⁻¹ℤ^d`. -/
def sampleMesh (f : ℝ × (Fin d → ℝ) → ℝ) (R : ℝ) : ℤ → Site d → ℝ :=
  fun m c => f ((m : ℝ) / R ^ 2, fun i => (c i : ℝ) / R)

/-- The hat interpolation, at scale `R`, of `f`'s own samples on the mesh `R⁻²ℤ × R⁻¹ℤ^d`. -/
def meshInterp (f : ℝ × (Fin d → ℝ) → ℝ) (R : ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  meshInterpV (sampleMesh f R) R p

theorem continuous_meshInterp (f : ℝ × (Fin d → ℝ) → ℝ) (R : ℝ) :
    Continuous (meshInterp f R) :=
  continuous_meshInterpV _ R

/-- The cutoff of a continuous field by a compactly supported continuous test function, as a
bounded continuous function (the generic form of `Parking.cutoffBC`). -/
def cutoffBC (χ f : ℝ × (Fin d → ℝ) → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hf : Continuous f) : BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ :=
  ofCompactSupport (fun p => χ p * f p) (hχ.mul hf) hχc.mul_right

/-! ### A single finite mesh box serving every point of a bounded region -/

/-- A real number bounded in absolute value by `R0` has both of its floor-pair corners inside
the fixed integer window `[⌊-R0⌋, ⌊R0⌋+1]`. -/
theorem mem_meshBox_of_abs_le {t R0 : ℝ} (h : |t| ≤ R0) {j : ℤ}
    (hj : j = ⌊t⌋ ∨ j = ⌊t⌋ + 1) : j ∈ Finset.Icc (⌊-R0⌋ : ℤ) (⌊R0⌋ + 1) := by
  have hlo : -R0 ≤ t := (abs_le.mp h).1
  have hhi : t ≤ R0 := (abs_le.mp h).2
  have hfl : (⌊-R0⌋ : ℤ) ≤ ⌊t⌋ := Int.floor_mono hlo
  have hfh : ⌊t⌋ ≤ (⌊R0⌋ : ℤ) := Int.floor_mono hhi
  rw [Finset.mem_Icc]
  rcases hj with hj | hj <;> omega

/-- The finite time and space mesh window serving every point of a region bounded by `R0`. -/
def meshTimeBox (R0 : ℝ) : Finset ℤ := Finset.Icc (⌊-R0⌋ : ℤ) (⌊R0⌋ + 1)

/-- `hatInterpD` at any point of a bounded region is the SAME finite corner sum, the box
depending only on the bound `R0`, not on the point itself. -/
theorem hatInterpD_eq_sum_of_meshBound (V : ℤ → Site d → ℝ) {u : ℝ × (Fin d → ℝ)} {R0 : ℝ}
    (h1 : |u.1| ≤ R0) (h2 : ∀ i, |u.2 i| ≤ R0) :
    Parking.hatInterpD V u =
      ∑ m ∈ meshTimeBox R0, ∑ c ∈ Fintype.piFinset fun _ : Fin d => meshTimeBox R0,
          V m c * (Parking.hat1 (u.1 - (m : ℝ)) * Parking.hatProd u.2 c) := by
  refine Parking.hatInterpD_eq_sum V u _ _ (fun m hm => ?_) (fun c hc => ?_)
  · exact mem_meshBox_of_abs_le h1 (Parking.hat1_ne_zero_mem_floor_pair hm)
  · rw [Fintype.mem_piFinset]
    intro i
    exact mem_meshBox_of_abs_le (h2 i) (Parking.hatProd_ne_zero_mem_box hc i)

/-! ### A uniform bound on the rescaled compact support of a cutoff -/

/-- A bound on the rescaled compact support of `χ`: since `tsupport χ` is compact, there is
`R0 ≥ 0` with `|R² p.1| ≤ R0` and `|R p.2 i| ≤ R0` for every `p ∈ tsupport χ`. -/
theorem exists_mesh_bound (d : ℕ) (R : ℝ) (χ : ℝ × (Fin d → ℝ) → ℝ)
    (hχc : HasCompactSupport χ) :
    ∃ R0 : ℝ, 0 ≤ R0 ∧ ∀ p ∈ tsupport χ, |R ^ 2 * p.1| ≤ R0 ∧ ∀ i, |R * p.2 i| ≤ R0 := by
  obtain ⟨r, hr0, hrsub⟩ := hχc.isBounded.subset_closedBall_lt 0 ((0 : ℝ), (0 : Fin d → ℝ))
  refine ⟨(R ^ 2 + |R|) * r, by positivity, fun p hp => ?_⟩
  have hball : p ∈ Metric.closedBall ((0 : ℝ), (0 : Fin d → ℝ)) r := hrsub hp
  rw [Metric.mem_closedBall] at hball
  have h1 : |p.1| ≤ r := by
    have hle : dist p.1 (0 : ℝ) ≤ dist p ((0 : ℝ), (0 : Fin d → ℝ)) := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    have := hle.trans hball
    rwa [Real.dist_eq, sub_zero] at this
  have h2 : ∀ i, |p.2 i| ≤ r := by
    intro i
    have hle1 : dist (p.2) (0 : Fin d → ℝ) ≤ dist p ((0 : ℝ), (0 : Fin d → ℝ)) := by
      rw [Prod.dist_eq]; exact le_max_right _ _
    have hle2 : dist (p.2 i) ((0 : Fin d → ℝ) i) ≤ dist (p.2) (0 : Fin d → ℝ) :=
      dist_le_pi_dist p.2 (0 : Fin d → ℝ) i
    have := (hle2.trans hle1).trans hball
    rwa [Real.dist_eq, Pi.zero_apply, sub_zero] at this
  refine ⟨?_, fun i => ?_⟩
  · rw [abs_mul, abs_pow]
    have hR2 : (0 : ℝ) ≤ |R| ^ 2 := by positivity
    calc |R| ^ 2 * |p.1| ≤ |R| ^ 2 * r := by
          apply mul_le_mul_of_nonneg_left h1 hR2
      _ ≤ (R ^ 2 + |R|) * r := by
          have : |R| ^ 2 = R ^ 2 := sq_abs R
          nlinarith [abs_nonneg R, hr0.le]
  · rw [abs_mul]
    calc |R| * |p.2 i| ≤ |R| * r := mul_le_mul_of_nonneg_left (h2 i) (abs_nonneg R)
      _ ≤ (R ^ 2 + |R|) * r := by nlinarith [sq_nonneg R, hr0.le]

/-- The joint time-space weights, summed over the FULL mesh box `meshTimeBox R0` (not merely
the exact two corners), still sum to one, since the extra terms vanish: apply
`hatInterpD_eq_sum_of_meshBound` to the constant field `1` and compare with
`Parking.hatInterpD_eq_corners`/`Parking.hatInterpD_weight_sum`, both computing the same
`Parking.hatInterpD (fun _ _ => 1) u`. -/
theorem meshWeight_sum_eq_one {u : ℝ × (Fin d → ℝ)} {R0 : ℝ}
    (h1 : |u.1| ≤ R0) (h2 : ∀ i, |u.2 i| ≤ R0) :
    ∑ m ∈ meshTimeBox R0, ∑ c ∈ Fintype.piFinset fun _ : Fin d => meshTimeBox R0,
        Parking.hat1 (u.1 - (m : ℝ)) * Parking.hatProd u.2 c = 1 := by
  have e1 := hatInterpD_eq_sum_of_meshBound (V := fun (_ : ℤ) (_ : Site d) => (1 : ℝ)) h1 h2
  have e2 : Parking.hatInterpD (fun (_ : ℤ) (_ : Site d) => (1 : ℝ)) u = 1 := by
    rw [Parking.hatInterpD_eq_corners]
    simpa using Parking.hatInterpD_weight_sum u
  rw [e2] at e1
  simpa using e1.symm

/-! ### The interpolation is Lipschitz in the grid field, for the sup metrics -/

/-- The interpolation at a bounded point is `1`-Lipschitz (in the sup sense, with no extra
constant) in the DIFFERENCE of two grid fields, over the finite mesh box: the two-term
specialization of `Parking.abs_sum_sum_sub_le_of_forall`. -/
theorem abs_hatInterpD_sub_hatInterpD_le {V1 V2 : ℤ → Site d → ℝ} {u : ℝ × (Fin d → ℝ)}
    {R0 B : ℝ} (h1 : |u.1| ≤ R0) (h2 : ∀ i, |u.2 i| ≤ R0)
    (hB : ∀ m ∈ meshTimeBox R0, ∀ c ∈ Fintype.piFinset fun _ : Fin d => meshTimeBox R0,
      |V1 m c - V2 m c| ≤ B) :
    |Parking.hatInterpD V1 u - Parking.hatInterpD V2 u| ≤ B := by
  have heq : Parking.hatInterpD V1 u - Parking.hatInterpD V2 u
      = ∑ m ∈ meshTimeBox R0, ∑ c ∈ Fintype.piFinset fun _ : Fin d => meshTimeBox R0,
          (V1 m c - V2 m c) * (Parking.hat1 (u.1 - (m : ℝ)) * Parking.hatProd u.2 c) := by
    rw [hatInterpD_eq_sum_of_meshBound V1 h1 h2, hatInterpD_eq_sum_of_meshBound V2 h1 h2,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [heq]
  have hb := Parking.abs_sum_sum_sub_le_of_forall (meshTimeBox R0)
    (Fintype.piFinset fun _ : Fin d => meshTimeBox R0)
    (fun m c => V1 m c - V2 m c) (fun m c => Parking.hat1 (u.1 - (m : ℝ)) * Parking.hatProd u.2 c)
    0 B (fun m _ c _ => mul_nonneg (Parking.hat1_nonneg _) (Parking.hatProd_nonneg _ _))
    (meshWeight_sum_eq_one h1 h2) (fun m hm c hc => by simpa using hB m hm c hc)
  simpa using hb

/-! ### Measurability: the finite-dependence argument -/

/-- **The cutoff, rescaled, hat-interpolated MESH SAMPLE of an abstract random field is
Measurable into `E := BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ`**, given only measurable
point evaluations of the field (no continuity of the paths is needed for this step). This is
the SAME finite-dependence argument as `Parking.measurable_cutoffBC_linHatInterp`, simpler here
because a field value is read directly, with no further `linPotential`-style box dependency. -/
theorem measurable_cutoffBC_meshInterp {Ω' : Type*} [MeasurableSpace Ω']
    (Z : Ω' → ℝ × (Fin d → ℝ) → ℝ) (hmeas : ∀ p, Measurable fun ω' => Z ω' p)
    (R : ℝ) (χ : ℝ × (Fin d → ℝ) → ℝ) (hχ1 : Continuous χ) (hχ2 : HasCompactSupport χ)
    [MeasurableSpace (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ)]
    [BorelSpace (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ)] :
    Measurable (fun ω' => cutoffBC χ (meshInterp (Z ω') R) hχ1 hχ2 (continuous_meshInterp _ R)) := by
  classical
  obtain ⟨R0, _hR0nn, hbound⟩ := exists_mesh_bound d R χ hχ2
  set Tbox := meshTimeBox R0 with hTbox
  set Sbox := Fintype.piFinset fun _ : Fin d => Tbox with hSbox
  set S : Finset (ℤ × Site d) := Tbox ×ˢ Sbox with hS
  set samplePt : ℤ × Site d → ℝ × (Fin d → ℝ) :=
    fun mc => ((mc.1 : ℝ) / R ^ 2, fun i => (mc.2 i : ℝ) / R) with hsamplePt
  set π : Ω' → (S → ℝ) := fun ω' zc => Z ω' (samplePt (zc : ℤ × Site d)) with hπ
  have hπmeas : Measurable π :=
    measurable_pi_lambda _ fun zc => hmeas (samplePt (zc : ℤ × Site d))
  set extendGrid : (S → ℝ) → ℤ → Site d → ℝ :=
    fun y m c => if h : (m, c) ∈ S then y ⟨(m, c), h⟩ else 0 with hextendGrid
  set h : (S → ℝ) → BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ :=
    fun y => cutoffBC χ (meshInterpV (extendGrid y) R) hχ1 hχ2 (continuous_meshInterpV _ R)
    with hh
  -- `h` is Lipschitz for the sup metrics (the interpolation is a genuine convex combination
  -- of the grid values, so the Lipschitz constant is `Mχ` with no extra cardinality factor).
  set Mχ := ‖ofCompactSupport χ hχ1 hχ2‖ with hMχ
  have hMχnn : 0 ≤ Mχ := norm_nonneg _
  have hLip : LipschitzWith Mχ.toNNReal h := by
    refine LipschitzWith.of_dist_le_mul fun y1 y2 => ?_
    rw [Real.coe_toNNReal Mχ hMχnn]
    rw [BoundedContinuousFunction.dist_le (by positivity)]
    intro p
    by_cases hp : p ∈ tsupport χ
    · have h1 : |R ^ 2 * p.1| ≤ R0 := (hbound p hp).1
      have h2 : ∀ i, |R * p.2 i| ≤ R0 := (hbound p hp).2
      have hval1 : (h y1) p = χ p * meshInterpV (extendGrid y1) R p := rfl
      have hval2 : (h y2) p = χ p * meshInterpV (extendGrid y2) R p := rfl
      rw [Real.dist_eq, hval1, hval2]
      have hdiffgrid : ∀ m ∈ Tbox, ∀ c ∈ Sbox,
          |extendGrid y1 m c - extendGrid y2 m c| ≤ dist y1 y2 := by
        intro m hm c hc
        have hmc : (m, c) ∈ S := Finset.mem_product.mpr ⟨hm, hc⟩
        simp only [extendGrid, dif_pos hmc]
        exact dist_le_pi_dist y1 y2 ⟨(m, c), hmc⟩
      have habs : |meshInterpV (extendGrid y1) R p - meshInterpV (extendGrid y2) R p|
          ≤ dist y1 y2 :=
        abs_hatInterpD_sub_hatInterpD_le h1 h2 hdiffgrid
      have hχp : |χ p| ≤ Mχ :=
        BoundedContinuousFunction.norm_coe_le_norm (ofCompactSupport χ hχ1 hχ2) p
      calc |χ p * meshInterpV (extendGrid y1) R p - χ p * meshInterpV (extendGrid y2) R p|
          = |χ p| * |meshInterpV (extendGrid y1) R p - meshInterpV (extendGrid y2) R p| := by
            rw [← mul_sub, abs_mul]
        _ ≤ Mχ * dist y1 y2 := mul_le_mul hχp habs (abs_nonneg _) hMχnn
    · have hval1 : (h y1) p = χ p * meshInterpV (extendGrid y1) R p := rfl
      have hval2 : (h y2) p = χ p * meshInterpV (extendGrid y2) R p := rfl
      have hχ0 : χ p = 0 := image_eq_zero_of_notMem_tsupport hp
      rw [Real.dist_eq, hval1, hval2, hχ0]
      simp only [zero_mul, sub_zero, abs_zero]
      positivity
  have heq : ∀ ω' : Ω', cutoffBC χ (meshInterp (Z ω') R) hχ1 hχ2 (continuous_meshInterp _ R)
      = h (π ω') := by
    intro ω'
    refine BoundedContinuousFunction.ext fun p => ?_
    show χ p * meshInterp (Z ω') R p = χ p * meshInterpV (extendGrid (π ω')) R p
    by_cases hp : p ∈ tsupport χ
    · congr 1
      have h1 : |R ^ 2 * p.1| ≤ R0 := (hbound p hp).1
      have h2 : ∀ i, |R * p.2 i| ≤ R0 := (hbound p hp).2
      unfold meshInterp meshInterpV
      rw [hatInterpD_eq_sum_of_meshBound (V := sampleMesh (Z ω') R) h1 h2,
        hatInterpD_eq_sum_of_meshBound (V := extendGrid (π ω')) h1 h2]
      refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun c hc => ?_
      congr 2
      have hmc : (m, c) ∈ S := Finset.mem_product.mpr ⟨hm, hc⟩
      show Z ω' ((m : ℝ) / R ^ 2, fun i => (c i : ℝ) / R) = extendGrid (π ω') m c
      simp only [extendGrid, dif_pos hmc]
      rfl
    · have hχ0 : χ p = 0 := image_eq_zero_of_notMem_tsupport hp
      rw [hχ0, zero_mul, zero_mul]
  have hfun : (fun ω' => cutoffBC χ (meshInterp (Z ω') R) hχ1 hχ2 (continuous_meshInterp _ R))
      = h ∘ π := by
    funext ω'; exact heq ω'
  rw [hfun]
  exact hLip.continuous.measurable.comp hπmeas

/-! ### Convergence: the mesh interpolation converges to the true field, uniformly on a
compact cutoff support -/

/-- A corner (in the sense of `Parking.hat1_ne_zero_mem_floor_pair`) of a real number `t` is
within `1` of `t`. -/
theorem abs_corner_sub_le {t : ℝ} {j : ℤ} (hj : j = ⌊t⌋ ∨ j = ⌊t⌋ + 1) : |(j : ℝ) - t| ≤ 1 := by
  rcases hj with rfl | rfl
  · rw [abs_of_nonpos (by linarith [Int.floor_le t] : (⌊t⌋ : ℝ) - t ≤ 0)]
    linarith [Int.lt_floor_add_one t]
  · push_cast
    rw [abs_of_nonneg (by linarith [Int.lt_floor_add_one t] : (0 : ℝ) ≤ (⌊t⌋ : ℝ) + 1 - t)]
    linarith [Int.floor_le t]

/-- **The cutoff mesh interpolation of a continuous field converges, as `R = 2^n → ∞`, to the
cutoff field itself, in the sup metric on `E`.** The key quantitative step: every mesh corner
of the rescaled point `(R² p.1, R p.2)` lies within `1/R` of `p` itself, so by uniform
continuity of `f` on a compact neighbourhood of the cutoff's support (Heine–Cantor) the
interpolated value is within any prescribed `ε` of `f p`, uniformly over `p` in the support,
once `R` is large. -/
theorem tendsto_cutoffBC_meshInterp {f : ℝ × (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (χ : ℝ × (Fin d → ℝ) → ℝ) (hχ1 : Continuous χ) (hχ2 : HasCompactSupport χ) :
    Tendsto (fun n : ℕ => cutoffBC χ (meshInterp f (2 ^ n)) hχ1 hχ2 (continuous_meshInterp f _))
      atTop (𝓝 (cutoffBC χ f hχ1 hχ2 hf)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε0 := ε / 2 with hε0
  have hε00 : 0 < ε0 := by rw [hε0]; positivity
  set Mχ := ‖ofCompactSupport χ hχ1 hχ2‖ with hMχ
  set ε' := ε0 / (Mχ + 1) with hε'
  have hMχnn : 0 ≤ Mχ := norm_nonneg _
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  obtain ⟨r, hr0, hrsub⟩ := hχ2.isBounded.subset_closedBall_lt 0 ((0 : ℝ), (0 : Fin d → ℝ))
  set K' := Metric.closedBall ((0 : ℝ), (0 : Fin d → ℝ)) (r + 1) with hK'
  have hK'compact : IsCompact K' := isCompact_closedBall _ _
  have hUC : UniformContinuousOn f K' := hK'compact.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff_le.mp hUC ε' hε'0
  set δ' := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ0 one_pos
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ'0 (show (1:ℝ)/2 < 1 by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  refine lt_of_le_of_lt ?_ (show ε0 < ε by rw [hε0]; linarith)
  have hpow : ((1:ℝ)/2) ^ n ≤ ((1:ℝ)/2) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hpowδ : ((1:ℝ)/2) ^ n < δ' := lt_of_le_of_lt hpow hN
  have hReq : ((1:ℝ)/2) ^ n = 1 / (2:ℝ) ^ n := by rw [div_pow, one_pow]
  set R : ℝ := (2:ℝ) ^ n with hRdef
  have hR1 : (1:ℝ) ≤ R := one_le_pow₀ (by norm_num)
  have hR0 : (0:ℝ) < R := by linarith
  have hinvR : 1 / R < δ' := by rw [hRdef, ← hReq]; exact hpowδ
  have hinvRle : (1:ℝ) / R ≤ δ' := hinvR.le
  -- every mesh corner of the rescaled point `(R² p.1, R p.2)` lies within `1/R` of `p`
  have hcornerDist : ∀ p : ℝ × (Fin d → ℝ), ∀ m : ℤ,
      (m = ⌊R ^ 2 * p.1⌋ ∨ m = ⌊R ^ 2 * p.1⌋ + 1) → ∀ c : Site d,
      (∀ i, c i = ⌊R * p.2 i⌋ ∨ c i = ⌊R * p.2 i⌋ + 1) →
      dist ((m : ℝ) / R ^ 2, fun i => (c i : ℝ) / R) p ≤ 1 / R := by
    intro p m hm c hc
    rw [Prod.dist_eq]
    refine max_le ?_ ?_
    · rw [Real.dist_eq]
      have hcorn : |(m : ℝ) - R ^ 2 * p.1| ≤ 1 := abs_corner_sub_le hm
      have heq : (m : ℝ) / R ^ 2 - p.1 = ((m : ℝ) - R ^ 2 * p.1) / R ^ 2 := by
        field_simp
      rw [heq, abs_div, abs_of_pos (show (0:ℝ) < R ^ 2 by positivity)]
      have step1 : |(m : ℝ) - R ^ 2 * p.1| / R ^ 2 ≤ 1 / R ^ 2 := by
        gcongr
      have step2 : (1 : ℝ) / R ^ 2 ≤ 1 / R := by
        gcongr
        nlinarith [hR1]
      linarith
    · rw [dist_pi_le_iff (by positivity)]
      intro i
      rw [Real.dist_eq]
      have hcorn : |(c i : ℝ) - R * p.2 i| ≤ 1 := abs_corner_sub_le (hc i)
      have heq : (c i : ℝ) / R - p.2 i = ((c i : ℝ) - R * p.2 i) / R := by
        field_simp
      rw [heq, abs_div, abs_of_pos hR0]
      gcongr
  rw [BoundedContinuousFunction.dist_le (by positivity)]
  intro p
  have hval1 : (cutoffBC χ (meshInterp f R) hχ1 hχ2 (continuous_meshInterp f R)) p
      = χ p * meshInterp f R p := rfl
  have hval2 : (cutoffBC χ f hχ1 hχ2 hf) p = χ p * f p := rfl
  rw [hval1, hval2]
  by_cases hp : p ∈ tsupport χ
  · have hpK' : p ∈ K' := by
      have := hrsub hp
      rw [Metric.mem_closedBall] at this ⊢
      linarith
    -- every corner mesh sample is within `ε'` of `f p`
    have hcorner : ∀ m ∈ ({⌊R ^ 2 * p.1⌋, ⌊R ^ 2 * p.1⌋ + 1} : Finset ℤ),
        ∀ c ∈ Fintype.piFinset fun i : Fin d =>
          ({⌊R * p.2 i⌋, ⌊R * p.2 i⌋ + 1} : Finset ℤ),
        |sampleMesh f R m c - f p| ≤ ε' := by
      intro m hm c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      have hc' : ∀ i, c i = ⌊R * p.2 i⌋ ∨ c i = ⌊R * p.2 i⌋ + 1 := by
        rw [Fintype.mem_piFinset] at hc
        intro i
        simpa using hc i
      set x : ℝ × (Fin d → ℝ) := ((m : ℝ) / R ^ 2, fun i => (c i : ℝ) / R) with hxdef
      have hdxp : dist x p ≤ 1 / R := hcornerDist p m hm c hc'
      have hxK' : x ∈ K' := by
        rw [hK', Metric.mem_closedBall]
        have h1 : dist x ((0:ℝ), (0 : Fin d → ℝ)) ≤ dist x p + dist p ((0:ℝ), (0 : Fin d → ℝ)) :=
          dist_triangle _ _ _
        have h2 : dist p ((0:ℝ), (0 : Fin d → ℝ)) ≤ r := by
          have := hrsub hp
          rwa [Metric.mem_closedBall] at this
        have h3 : dist x p ≤ 1 := hdxp.trans (by
          rw [div_le_one hR0]; exact hR1)
        linarith
      have hdle : dist x p ≤ δ := hdxp.trans (hinvRle.trans (min_le_left _ _))
      have := hδ x hxK' p hpK' hdle
      rw [Real.dist_eq] at this
      show |f x - f p| ≤ ε'
      exact this
    have hfp : |meshInterp f R p - f p| ≤ ε' := by
      have := Parking.abs_hatInterpD_sub_le_of_forall (sampleMesh f R) (R ^ 2 * p.1, fun i => R * p.2 i)
        (f p) ε' hcorner
      exact this
    have hχp : |χ p| ≤ Mχ :=
      BoundedContinuousFunction.norm_coe_le_norm (ofCompactSupport χ hχ1 hχ2) p
    calc |χ p * meshInterp f R p - χ p * f p|
        = |χ p| * |meshInterp f R p - f p| := by rw [← mul_sub, abs_mul]
      _ ≤ Mχ * ε' := mul_le_mul hχp hfp (abs_nonneg _) hMχnn
      _ ≤ (Mχ + 1) * ε' := by
          apply mul_le_mul_of_nonneg_right (by linarith) hε'0.le
      _ = ε0 := by rw [hε']; field_simp
  · have hχ0 : χ p = 0 := image_eq_zero_of_notMem_tsupport hp
    rw [hχ0]
    simp only [zero_mul, dist_self]
    exact hε00.le

/-! ### The main theorem -/

/-- **A continuous random field with measurable point evaluations and continuous paths, cut off
by a compactly supported continuous test function, is a measurable map into
`E := BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ`.**  The cutoff field is the pointwise
(in `ω'`) sup-norm limit, as `R = 2^n → ∞`, of its measurable mesh hat interpolations
(`measurable_cutoffBC_meshInterp`, `tendsto_cutoffBC_meshInterp`), and Mathlib's
`measurable_of_tendsto_metrizable'` needs no separability of the codomain. -/
theorem measurable_cutoffBC_of_continuous_measurable {Ω' : Type*} [MeasurableSpace Ω']
    (Z : Ω' → ℝ × (Fin d → ℝ) → ℝ) (hcont : ∀ ω', Continuous (Z ω'))
    (hmeas : ∀ p, Measurable fun ω' => Z ω' p)
    (χ : ℝ × (Fin d → ℝ) → ℝ) (hχ1 : Continuous χ) (hχ2 : HasCompactSupport χ)
    [MeasurableSpace (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ)]
    [BorelSpace (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ)] :
    Measurable (fun ω' => cutoffBC χ (Z ω') hχ1 hχ2 (hcont ω')) := by
  refine measurable_of_tendsto_metrizable' (u := (atTop : Filter ℕ))
    (f := fun n ω' => cutoffBC χ (meshInterp (Z ω') (2 ^ n)) hχ1 hχ2
      (continuous_meshInterp (Z ω') (2 ^ n)))
    (fun n => measurable_cutoffBC_meshInterp Z hmeas (2 ^ n) χ hχ1 hχ2) ?_
  rw [tendsto_pi_nhds]
  intro ω'
  exact tendsto_cutoffBC_meshInterp (hcont ω') χ hχ1 hχ2

end Parking.Generic.FieldMeasurability

end
