/-
**Measurability of the cutoff, rescaled, interpolated linear field as a random element.**

Applying the library's extended continuous mapping theorem
(`Parking.Support.ExtendedMappingReal.tendsto_integral_comp_real_of_lipschitz`) requires the
law of `Parking.linHatInterp (fun y => (w.1 y : ℝ)) R` to be represented as a `Measure.map`
pushforward on `E := BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ`.  This needs
`w ↦ Parking.cutoffBC χ (Parking.linHatInterp (fun y => (w.1 y : ℝ)) R) ...` to be
MEASURABLE as a map `Parking.Data d → E`, for `E`'s Borel σ-algebra (the sup-norm topology):
`E` is NOT separable (bounded continuous functions on a non-compact space), so pointwise
measurability of each evaluation `w ↦ v(p)` is not by itself sufficient, and Mathlib has no
general fact that gives this directly.

**The construction.**  Fix a compactly supported cutoff `χ` (so `K := tsupport χ` is compact)
and a scale `R`.  Since `Parking.hatInterpD` reads a grid field only at the finitely many
corner points surrounding its argument (`Parking.hatInterpD_eq_sum`), and `K` is compact, ONE
FIXED finite box of grid points `Tbox × Sbox` (not depending on `w` or on the point `p ∈ K`,
only on `R` and `K`'s bound) serves EVERY `p ∈ K` simultaneously
(`hatInterpD_eq_sum_of_bound`, below).  Since `Parking.linPotential` at each of those finitely
many grid points reads the field `ζ` only on a further finite box
(`Parking.linPotential_eq_extendField_of_boxFinset_subset`), and the UNION of those (finitely
many) boxes is itself a single finite set `Z` of sites (`Parking.linHatBoxSites`),
`w ↦ Parking.cutoffBC χ (Parking.linHatInterp (w.1) R) ...` FACTORS as a finite-coordinate
projection `w ↦ (w.1 z)_{z ∈ Z}` (measurable, standard) composed with a map `(Z → ℝ) → E` that
is LIPSCHITZ for the sup metrics (`Parking.lipschitzWith_cutoffBC_linHatInterp_restrict`, from
the crude field-Lipschitz bound on `linPotential`,
`Parking.lipschitzWith_linPotential_extendField`, summed over the fixed finite grid box).  A
Lipschitz map is continuous, hence Borel measurable, and composing a measurable map with a
continuous one is measurable (`Parking.measurable_cutoffBC_linHatInterp`, the module's main
theorem).

The module also proves measurability of the linear membrane field `Parking.linPotential` and
its interpolated, rescaled version `Parking.linHatInterp`, as functions of the scenery
`w : Data d`, at a FIXED grid point / real space-time point.  This is needed for the
three-block scenery export `Parking.tendsto_scenePair_linHatInterp_joint_fdd_signedResidual`:
assembling the convergence of `Parking.tendsto_scenePair_linHatInterp_joint_fdd`, which is
stated as "tested against every bounded continuous `G`", into a genuine
`MeasureTheory.TendstoInDistribution` statement (via `Parking.Generic.Slutsky`) requires literal
measurability of the pre-limit random vector
`w ↦ ((scenePair w R (φ i))_i, (linHatInterp (confReal w) R (sp j))_j)`, not merely the
integral-convergence statement.

Both reduce to a FINITE sum: `Parking.linPotential_eq_sum`
(`Parking/Support/LinPotentialSum.lean`) gives
`linPotential η n x = ∑_{z ∈ boxFinset x n} η z · green d n (x-z)`, and
`Parking.hatInterpD_eq_corners` (`Parking/Support/HatInterpD.lean`) gives `hatInterpD V u`
as a finite double sum over the two nearest integer times and the `2^d` nearest lattice points
of `u`.  Composing the two turns `linHatInterp η R p`, at fixed `R, p`, into a genuine finite
combination of the coordinates `η z`, hence measurable in `η` (equivalently in `w`, via
`η := confReal w`) by the same coordinate-projection argument as `Parking.measurable_scenePair`
(`Parking/Support/SpatWSceneryFdd.lean`).
-/
import Parking.Support.HatInterpD
import Parking.Support.LinPotentialSum
import Parking.Support.LinInterp
import Parking.Support.UConcBridge
import Parking.Basic

noncomputable section

namespace Parking

open Finset LatticeProb MeasureTheory
open scoped NNReal

variable {d : ℕ}

/-! ### A single finite corner box serving every point of a bounded region -/

/-- **A real number bounded in absolute value by `R0` has both of its floor-pair corners
inside the fixed integer window `[⌊-R0⌋, ⌊R0⌋+1]`.** -/
theorem mem_boxRange_of_abs_le {t R0 : ℝ} (h : |t| ≤ R0) {j : ℤ} (hj : j = ⌊t⌋ ∨ j = ⌊t⌋ + 1) :
    j ∈ Finset.Icc (⌊-R0⌋ : ℤ) (⌊R0⌋ + 1) := by
  have hlo : -R0 ≤ t := (abs_le.mp h).1
  have hhi : t ≤ R0 := (abs_le.mp h).2
  have hfl : (⌊-R0⌋ : ℤ) ≤ ⌊t⌋ := Int.floor_mono hlo
  have hfh : ⌊t⌋ ≤ (⌊R0⌋ : ℤ) := Int.floor_mono hhi
  rw [Finset.mem_Icc]
  rcases hj with hj | hj <;> omega

/-- **`hatInterpD` at any point of a bounded region is the SAME finite corner sum**, the box
depending only on the bound `R0`, not on the point itself.  This is what lets the (varying)
corner formula `Parking.hatInterpD_eq_corners` be replaced by a SINGLE finite sum valid
uniformly over a whole compact set. -/
theorem hatInterpD_eq_sum_of_bound (V : ℤ → Site d → ℝ) {u : ℝ × (Fin d → ℝ)} {R0 : ℝ}
    (h1 : |u.1| ≤ R0) (h2 : ∀ i, |u.2 i| ≤ R0) :
    hatInterpD V u =
      ∑ m ∈ Finset.Icc (⌊-R0⌋ : ℤ) (⌊R0⌋ + 1),
        ∑ c ∈ Fintype.piFinset fun _ : Fin d => Finset.Icc (⌊-R0⌋ : ℤ) (⌊R0⌋ + 1),
          V m c * (hat1 (u.1 - (m : ℝ)) * hatProd u.2 c) := by
  refine hatInterpD_eq_sum V u _ _ (fun m hm => ?_) (fun c hc => ?_)
  · exact mem_boxRange_of_abs_le h1 (hat1_ne_zero_mem_floor_pair hm)
  · rw [Fintype.mem_piFinset]
    intro i
    exact mem_boxRange_of_abs_le (h2 i) (hatProd_ne_zero_mem_box hc i)

/-! ### The finite site box a bounded region reads -/

/-- **The finite time window and space window** serving every point of the rescaled compact
region `{(R²p.1, R•p.2) : p ∈ K}` when `K` is bounded by `R0`. -/
def linHatTimeBox (R0 : ℝ) : Finset ℤ := Finset.Icc (⌊-R0⌋ : ℤ) (⌊R0⌋ + 1)

/-- The natural-number radius bound used to build the finite site box: every grid time
index in `linHatTimeBox R0`, read as a `ℕ` horizon via `Int.toNat`, is at most this. -/
def linHatRad (R0 : ℝ) : ℕ := (⌊R0⌋ + 1).toNat

theorem toNat_mem_linHatTimeBox_le {R0 : ℝ} {m : ℤ} (hm : m ∈ linHatTimeBox R0) :
    m.toNat ≤ linHatRad R0 := by
  unfold linHatTimeBox at hm
  rw [Finset.mem_Icc] at hm
  unfold linHatRad
  omega

/-- **The finite set of sites the interpolated field reads**, over the whole time-space
corner box `linHatTimeBox R0 × (linHatTimeBox R0)^d`: the union, over every grid site `c` in
the space window, of the box of radius `linHatRad R0` about `c` (the largest box any grid
time index in the window can ask `Parking.linPotential` to read). -/
def linHatBoxSites (d : ℕ) (R0 : ℝ) : Finset (Site d) :=
  (Fintype.piFinset fun _ : Fin d => linHatTimeBox R0).biUnion
    fun c => boxFinset c (linHatRad R0)

theorem boxFinset_subset_linHatBoxSites {d : ℕ} {R0 : ℝ} {c : Site d}
    (hc : c ∈ Fintype.piFinset fun _ : Fin d => linHatTimeBox R0) :
    boxFinset c (linHatRad R0) ⊆ linHatBoxSites d R0 := by
  unfold linHatBoxSites
  exact Finset.subset_biUnion_of_mem (fun c => boxFinset c (linHatRad R0)) hc

/-! ### `linPotential` at every grid point of the corner box reads only the finite site box -/

theorem linPotential_eq_extendField_linHatBoxSites {d : ℕ} {R0 : ℝ} {m : ℤ}
    (hm : m ∈ linHatTimeBox R0) {c : Site d}
    (hc : c ∈ Fintype.piFinset fun _ : Fin d => linHatTimeBox R0) (ζ : Site d → ℤ) :
    linPotential (fun y => (ζ y : ℝ)) m.toNat c
      = linPotential (extendField (linHatBoxSites d R0)
          ((linHatBoxSites d R0).restrict (fun y => (ζ y : ℝ)))) m.toNat c :=
  linPotential_eq_extendField_of_boxFinset_subset
    ((boxFinset_mono (toNat_mem_linHatTimeBox_le hm)).trans
      (boxFinset_subset_linHatBoxSites hc)) _

/-! ### A uniform bound on the rescaled compact support of a cutoff -/

/-- **A bound on the rescaled compact support of `χ`.**  Since `tsupport χ` is compact,
there is `R0 ≥ 0` with `|R² p.1| ≤ R0` and `|R p.2 i| ≤ R0` for every `p ∈ tsupport χ`. -/
theorem exists_linHat_bound (d : ℕ) (R : ℝ) (χ : ℝ × (Fin d → ℝ) → ℝ)
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
    have hR2 : (0:ℝ) ≤ |R| ^ 2 := by positivity
    calc |R| ^ 2 * |p.1| ≤ |R| ^ 2 * r := by
          apply mul_le_mul_of_nonneg_left h1 hR2
      _ ≤ (R ^ 2 + |R|) * r := by
          have : |R| ^ 2 = R ^ 2 := sq_abs R
          nlinarith [abs_nonneg R, hr0.le]
  · rw [abs_mul]
    calc |R| * |p.2 i| ≤ |R| * r := mul_le_mul_of_nonneg_left (h2 i) (abs_nonneg R)
      _ ≤ (R ^ 2 + |R|) * r := by nlinarith [sq_nonneg R, hr0.le]

/-! ### `linHatInterp`, on the rescaled compact support of `χ`, reads only the finite box -/

/-- **On the rescaled compact support of `χ`, `linHatInterp ζ R` reads only `ζ` restricted
to the finite box `linHatBoxSites d R0`.** -/
theorem linHatInterp_eq_extendField_linHatBoxSites {d : ℕ} {R : ℝ} {χ : ℝ × (Fin d → ℝ) → ℝ}
    {R0 : ℝ} (hbound : ∀ p ∈ tsupport χ, |R ^ 2 * p.1| ≤ R0 ∧ ∀ i, |R * p.2 i| ≤ R0)
    (ζ : Site d → ℤ) {p : ℝ × (Fin d → ℝ)} (hp : p ∈ tsupport χ) :
    linHatInterp (fun y => (ζ y : ℝ)) R p
      = linHatInterp (extendField (linHatBoxSites d R0)
          ((linHatBoxSites d R0).restrict (fun y => (ζ y : ℝ)))) R p := by
  obtain ⟨h1, h2⟩ := hbound p hp
  unfold linHatInterp
  rw [hatInterpD_eq_sum_of_bound _ h1 h2, hatInterpD_eq_sum_of_bound _ h1 h2]
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun c hc => ?_
  congr 2
  exact linPotential_eq_extendField_linHatBoxSites hm hc ζ

/-! ### The Lipschitz bound on the finite-restriction map -/

/-- **The composite `y ↦ cutoffBC χ (linHatInterp (extendField Z y) R) ...` is Lipschitz**,
for the sup metrics: the cutoff, evaluated at a point of the rescaled compact support of
`χ`, is a finite sum, over the fixed finite corner box, of `linPotential`-values that are
each Lipschitz in the finite restriction by `Parking.abs_linPotential_sub_le`. -/
theorem exists_lipschitz_cutoffBC_linHatInterp (d : ℕ) (hd : 1 ≤ d) (R : ℝ)
    (χ : ℝ × (Fin d → ℝ) → ℝ) (hχ1 : Continuous χ) (hχ2 : HasCompactSupport χ)
    {R0 : ℝ} (hbound : ∀ p ∈ tsupport χ, |R ^ 2 * p.1| ≤ R0 ∧ ∀ i, |R * p.2 i| ≤ R0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y1 y2 : linHatBoxSites d R0 → ℝ,
      dist
          (cutoffBC χ (linHatInterp (extendField (linHatBoxSites d R0) y1) R) hχ1 hχ2
              (continuous_linHatInterp _ R))
          (cutoffBC χ (linHatInterp (extendField (linHatBoxSites d R0) y2) R) hχ1 hχ2
              (continuous_linHatInterp _ R))
        ≤ C * dist y1 y2 := by
  classical
  set Z := linHatBoxSites d R0 with hZ
  set Tbox := linHatTimeBox R0 with hTbox
  set Sbox := Fintype.piFinset fun _ : Fin d => Tbox with hSbox
  set Mχ := ‖ofCompactSupport χ hχ1 hχ2‖ with hMχ
  set C : ℝ := Mχ * (Tbox.card * Sbox.card) * |R ^ ((d : ℝ) / 2 - 2)| * (linHatRad R0 : ℝ)
    with hC
  have hMχnn : 0 ≤ Mχ := norm_nonneg _
  refine ⟨C, by positivity, fun y1 y2 => ?_⟩
  rw [BoundedContinuousFunction.dist_le (by positivity)]
  intro p
  rw [Real.dist_eq]
  by_cases hp : p ∈ tsupport χ
  · have h1 : |R ^ 2 * p.1| ≤ R0 := (hbound p hp).1
    have h2 : ∀ i, |R * p.2 i| ≤ R0 := (hbound p hp).2
    have hval1 : (cutoffBC χ (linHatInterp (extendField Z y1) R) hχ1 hχ2
        (continuous_linHatInterp _ R)) p = χ p * linHatInterp (extendField Z y1) R p := rfl
    have hval2 : (cutoffBC χ (linHatInterp (extendField Z y2) R) hχ1 hχ2
        (continuous_linHatInterp _ R)) p = χ p * linHatInterp (extendField Z y2) R p := rfl
    rw [hval1, hval2]
    have hexp1 : linHatInterp (extendField Z y1) R p
        = ∑ m ∈ Tbox, ∑ c ∈ Sbox,
            (R ^ ((d : ℝ) / 2 - 2) * linPotential (extendField Z y1) m.toNat c) *
              (hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c) :=
      hatInterpD_eq_sum_of_bound _ h1 h2
    have hexp2 : linHatInterp (extendField Z y2) R p
        = ∑ m ∈ Tbox, ∑ c ∈ Sbox,
            (R ^ ((d : ℝ) / 2 - 2) * linPotential (extendField Z y2) m.toNat c) *
              (hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c) :=
      hatInterpD_eq_sum_of_bound _ h1 h2
    have hdiff : ∀ z : Site d, |(extendField Z y1 z : ℝ) - extendField Z y2 z| ≤ dist y1 y2 := by
      intro z
      by_cases hz : z ∈ Z
      · show |extendField Z y1 z - extendField Z y2 z| ≤ dist y1 y2
        simp only [extendField, dif_pos hz]
        rw [← Real.dist_eq]
        exact dist_le_pi_dist y1 y2 ⟨z, hz⟩
      · simp only [extendField, dif_neg hz, sub_zero, abs_zero]
        exact dist_nonneg
    have hterm : ∀ m ∈ Tbox, ∀ c ∈ Sbox,
        |(R ^ ((d : ℝ) / 2 - 2) * linPotential (extendField Z y1) m.toNat c) *
              (hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c)
            - (R ^ ((d : ℝ) / 2 - 2) * linPotential (extendField Z y2) m.toNat c) *
              (hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c)|
          ≤ |R ^ ((d : ℝ) / 2 - 2)| * (linHatRad R0 : ℝ) * dist y1 y2 := by
      intro m hm c _hc
      have hstep : (R ^ ((d : ℝ) / 2 - 2) * linPotential (extendField Z y1) m.toNat c) *
              (hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c)
            - (R ^ ((d : ℝ) / 2 - 2) * linPotential (extendField Z y2) m.toNat c) *
              (hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c)
          = (R ^ ((d : ℝ) / 2 - 2)
              * (linPotential (extendField Z y1) m.toNat c
                  - linPotential (extendField Z y2) m.toNat c)) *
            (hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c) := by ring
      rw [hstep, abs_mul]
      have hwnn : 0 ≤ hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c :=
        mul_nonneg (hat1_nonneg _) (hatProd_nonneg _ _)
      have hwle : hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c ≤ 1 :=
        mul_le_one₀ (hat1_le_one _) (hatProd_nonneg _ _) (hatProd_le_one _ _)
      have hwabs : |hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c| ≤ 1 := by
        rw [abs_of_nonneg hwnn]; exact hwle
      have hmn : m.toNat ≤ linHatRad R0 := toNat_mem_linHatTimeBox_le hm
      have hb : |linPotential (extendField Z y1) m.toNat c - linPotential (extendField Z y2)
          m.toNat c| ≤ (m.toNat : ℝ) * dist y1 y2 :=
        abs_linPotential_sub_le hd dist_nonneg hdiff m.toNat c
      have hRnn : 0 ≤ |R ^ ((d : ℝ) / 2 - 2)| := abs_nonneg _
      calc |R ^ ((d : ℝ) / 2 - 2)
              * (linPotential (extendField Z y1) m.toNat c
                  - linPotential (extendField Z y2) m.toNat c)| *
            |hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c|
          ≤ (|R ^ ((d : ℝ) / 2 - 2)| * ((m.toNat : ℝ) * dist y1 y2)) * 1 := by
            gcongr
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left hb hRnn
        _ ≤ (|R ^ ((d : ℝ) / 2 - 2)| * ((linHatRad R0 : ℝ) * dist y1 y2)) * 1 := by
            gcongr
        _ = |R ^ ((d : ℝ) / 2 - 2)| * (linHatRad R0 : ℝ) * dist y1 y2 := by ring
    have habs : |linHatInterp (extendField Z y1) R p - linHatInterp (extendField Z y2) R p|
        ≤ (Tbox.card * Sbox.card : ℝ)
          * (|R ^ ((d : ℝ) / 2 - 2)| * (linHatRad R0 : ℝ) * dist y1 y2) := by
      rw [hexp1, hexp2, ← Finset.sum_sub_distrib]
      calc |∑ m ∈ Tbox, (∑ c ∈ Sbox,
              (R ^ ((d : ℝ) / 2 - 2) * linPotential (extendField Z y1) m.toNat c) *
                (hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c)
            - ∑ c ∈ Sbox,
              (R ^ ((d : ℝ) / 2 - 2) * linPotential (extendField Z y2) m.toNat c) *
                (hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c))|
          ≤ ∑ m ∈ Tbox, |∑ c ∈ Sbox,
              (R ^ ((d : ℝ) / 2 - 2) * linPotential (extendField Z y1) m.toNat c) *
                (hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c)
            - ∑ c ∈ Sbox,
              (R ^ ((d : ℝ) / 2 - 2) * linPotential (extendField Z y2) m.toNat c) *
                (hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _m ∈ Tbox, (Sbox.card : ℝ)
              * (|R ^ ((d : ℝ) / 2 - 2)| * (linHatRad R0 : ℝ) * dist y1 y2) := by
            refine Finset.sum_le_sum fun m hm => ?_
            rw [← Finset.sum_sub_distrib]
            calc |∑ c ∈ Sbox, ((R ^ ((d : ℝ) / 2 - 2) * linPotential (extendField Z y1) m.toNat c) *
                    (hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c)
                  - (R ^ ((d : ℝ) / 2 - 2) * linPotential (extendField Z y2) m.toNat c) *
                    (hat1 ((R ^ 2 * p.1 : ℝ) - (m : ℝ)) * hatProd (fun i => R * p.2 i) c))|
                ≤ ∑ c ∈ Sbox, |R ^ ((d : ℝ) / 2 - 2)| * (linHatRad R0 : ℝ) * dist y1 y2 :=
                  (Finset.abs_sum_le_sum_abs _ _).trans
                    (Finset.sum_le_sum fun c hc => hterm m hm c hc)
              _ = (Sbox.card : ℝ) * (|R ^ ((d : ℝ) / 2 - 2)| * (linHatRad R0 : ℝ) * dist y1 y2) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
        _ = (Tbox.card * Sbox.card : ℝ)
              * (|R ^ ((d : ℝ) / 2 - 2)| * (linHatRad R0 : ℝ) * dist y1 y2) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
    have hχp : |χ p| ≤ Mχ :=
      BoundedContinuousFunction.norm_coe_le_norm (ofCompactSupport χ hχ1 hχ2) p
    calc |χ p * linHatInterp (extendField Z y1) R p - χ p * linHatInterp (extendField Z y2) R p|
        = |χ p| * |linHatInterp (extendField Z y1) R p - linHatInterp (extendField Z y2) R p| := by
          rw [← mul_sub, abs_mul]
      _ ≤ Mχ * ((Tbox.card * Sbox.card : ℝ)
              * (|R ^ ((d : ℝ) / 2 - 2)| * (linHatRad R0 : ℝ) * dist y1 y2)) :=
          mul_le_mul hχp habs (abs_nonneg _) hMχnn
      _ = C * dist y1 y2 := by rw [hC]; ring
  · have hval1 : (cutoffBC χ (linHatInterp (extendField Z y1) R) hχ1 hχ2
        (continuous_linHatInterp _ R)) p = χ p * linHatInterp (extendField Z y1) R p := rfl
    have hval2 : (cutoffBC χ (linHatInterp (extendField Z y2) R) hχ1 hχ2
        (continuous_linHatInterp _ R)) p = χ p * linHatInterp (extendField Z y2) R p := rfl
    have hχ0 : χ p = 0 := image_eq_zero_of_notMem_tsupport hp
    rw [hval1, hval2, hχ0]
    simp
    positivity

/-! ### The finite-restriction map is Lipschitz, hence continuous -/

/-- **The map from the finite restriction to the cutoff field is Lipschitz** for the sup
metrics, hence continuous. -/
theorem lipschitzWith_cutoffBC_linHatInterp (d : ℕ) (hd : 1 ≤ d) (R : ℝ)
    (χ : ℝ × (Fin d → ℝ) → ℝ) (hχ1 : Continuous χ) (hχ2 : HasCompactSupport χ)
    {R0 : ℝ} (hbound : ∀ p ∈ tsupport χ, |R ^ 2 * p.1| ≤ R0 ∧ ∀ i, |R * p.2 i| ≤ R0) :
    ∃ K : ℝ≥0, LipschitzWith K (fun y =>
        cutoffBC χ (linHatInterp (extendField (linHatBoxSites d R0) y) R) hχ1 hχ2
          (continuous_linHatInterp _ R)) := by
  obtain ⟨C, hC0, hC⟩ := exists_lipschitz_cutoffBC_linHatInterp d hd R χ hχ1 hχ2 hbound
  refine ⟨C.toNNReal, LipschitzWith.of_dist_le_mul fun y1 y2 => ?_⟩
  rw [Real.coe_toNNReal C hC0]
  exact hC y1 y2

/-! ### The main theorem: measurability of the cutoff, rescaled, interpolated field -/

/-- **The cutoff, rescaled, interpolated linear field, as a function of the data, is
Measurable into `E := BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ`** (with `E`'s Borel
σ-algebra from the sup-norm metric).  This is the measurability the extended continuous
mapping theorem needs to represent the field's law as a genuine `Measure.map` pushforward on
`E`; see the module docstring. -/
theorem measurable_cutoffBC_linHatInterp (d : ℕ) (hd : 1 ≤ d) (R : ℝ)
    (χ : ℝ × (Fin d → ℝ) → ℝ) (hχ1 : Continuous χ) (hχ2 : HasCompactSupport χ)
    [MeasurableSpace (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ)]
    [BorelSpace (BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ)] :
    Measurable (fun w : Data d =>
      cutoffBC χ (linHatInterp (fun y => (w.1 y : ℝ)) R) hχ1 hχ2
        (continuous_linHatInterp (fun y => (w.1 y : ℝ)) R)) := by
  obtain ⟨R0, _hR0nn, hbound⟩ := exists_linHat_bound d R χ hχ2
  obtain ⟨K, hK⟩ := lipschitzWith_cutoffBC_linHatInterp d hd R χ hχ1 hχ2 hbound
  set Z := linHatBoxSites d R0 with hZ
  set π : Data d → (Z → ℝ) := fun w z => confReal w (z : Site d) with hπ
  have hπmeas : Measurable π :=
    measurable_pi_lambda _ fun z => (measurable_pi_apply (z : Site d)).comp measurable_confReal
  set h : (Z → ℝ) → BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ :=
    fun y => cutoffBC χ (linHatInterp (extendField Z y) R) hχ1 hχ2
      (continuous_linHatInterp _ R) with hh
  have hheq : ∀ w : Data d, cutoffBC χ (linHatInterp (fun y => (w.1 y : ℝ)) R)
      hχ1 hχ2 (continuous_linHatInterp (fun y => (w.1 y : ℝ)) R) = h (π w) := by
    intro w
    refine BoundedContinuousFunction.ext fun p => ?_
    show χ p * linHatInterp (fun y => (w.1 y : ℝ)) R p
        = χ p * linHatInterp (extendField Z (π w)) R p
    by_cases hp : p ∈ tsupport χ
    · congr 1
      have heq := linHatInterp_eq_extendField_linHatBoxSites hbound (fun y => w.1 y) hp
      rw [heq]
      congr 1
    · rw [image_eq_zero_of_notMem_tsupport hp, zero_mul, zero_mul]
  have : (fun w : Data d => cutoffBC χ (linHatInterp (fun y => (w.1 y : ℝ)) R) hχ1 hχ2
        (continuous_linHatInterp (fun y => (w.1 y : ℝ)) R)) = h ∘ π := by
    funext w; exact hheq w
  rw [this]
  exact hK.continuous.measurable.comp hπmeas

/-- **`linPotential` at a fixed step count and site is measurable in the scenery.** -/
theorem measurable_linPotential (n : ℕ) (x : Site d) :
    Measurable (fun w : Data d => linPotential (confReal w) n x) := by
  have heq : (fun w : Data d => linPotential (confReal w) n x) = fun w =>
      ∑ z ∈ boxFinset x n, confReal w z * green d n (x - z) :=
    funext fun w => linPotential_eq_sum (confReal w) n x
  rw [heq]
  exact Finset.measurable_sum _ fun z _ =>
    ((measurable_pi_apply z).comp measurable_confReal).mul measurable_const

/-- **`linHatInterp` at a fixed scale and space-time point is measurable in the scenery.**
No hypothesis on `R` is needed (unlike `Parking.measurable_scenePair`, which needs `1 ≤ R` for
its own box-containment argument): `linHatInterp`'s closed corner-sum form
(`Parking.hatInterpD_eq_corners`) is a finite combination for every real `R`. -/
theorem measurable_linHatInterp (R : ℝ) (p : ℝ × (Fin d → ℝ)) :
    Measurable (fun w : Data d => linHatInterp (confReal w) R p) := by
  have heq : (fun w : Data d => linHatInterp (confReal w) R p) = fun w =>
      ∑ m ∈ ({⌊R ^ 2 * p.1⌋, ⌊R ^ 2 * p.1⌋ + 1} : Finset ℤ),
        ∑ c ∈ Fintype.piFinset fun i : Fin d =>
            ({⌊R * p.2 i⌋, ⌊R * p.2 i⌋ + 1} : Finset ℤ),
          (R ^ ((d : ℝ) / 2 - 2) * linPotential (confReal w) m.toNat c)
            * (hat1 (R ^ 2 * p.1 - (m : ℝ)) * hatProd (fun i => R * p.2 i) c) := by
    funext w
    unfold linHatInterp
    exact hatInterpD_eq_corners _ _
  rw [heq]
  exact Finset.measurable_sum _ fun m _ => Finset.measurable_sum _ fun c _ =>
    (measurable_const.mul (measurable_linPotential m.toNat c)).mul measurable_const

end Parking
end
